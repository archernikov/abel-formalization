import Mathlib.Data.Set.UnionLift
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Connected.CardComponents
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.TietzeExtension

/-!
# Compact separation for Maxwell tubes

This file isolates the topological argument in Maxwell's closure comparison.  Let `B` be an
arbitrary subset of a metric space, let `radius` have compact sublevel sets, and let `defect` be
continuous.  A strict tube consists of points of `B` with bounded radius and small defect.  The
main theorem says that a uniform bound for the number of connected components of all strict tubes
also bounds the number of connected components of the zero-defect part of `closure B`.

The proof is independent of definability.  Finitely many distinct components of the limit fiber
are put in a compact radius core.  The connected-component quotient of that core is compact,
Hausdorff, and totally disconnected, so its selected points extend to a finite clopen partition.
A real-valued label for that partition extends to the ambient space by Tietze.  Compactness gives
one positive defect threshold on which the tube lies in disjoint label intervals, while closure of
`B` makes every selected interval meet the tube.
-/

open Set

namespace AbelFormalization

/-- The strict bounded tube used in the compact component argument. -/
def maxwellStrictTube {X : Type*} [TopologicalSpace X]
    (B : Set X) (radius defect : X → ℝ) (R ε : ℝ) : Set X :=
  (B ∩ {x | radius x < R}) ∩ {x | |defect x| < ε}

/-- The zero-defect locus in the closure of the limiting set. -/
def maxwellLimitFiber {X : Type*} [TopologicalSpace X]
    (B : Set X) (defect : X → ℝ) : Set X :=
  closure B ∩ {x | defect x = 0}

@[simp]
theorem mem_maxwellStrictTube {X : Type*} [TopologicalSpace X]
    {B : Set X} {radius defect : X → ℝ} {R ε : ℝ} {x : X} :
    x ∈ maxwellStrictTube B radius defect R ε ↔
      x ∈ B ∧ radius x < R ∧ |defect x| < ε := by
  simp [maxwellStrictTube, and_assoc]

@[simp]
theorem mem_maxwellLimitFiber {X : Type*} [TopologicalSpace X]
    {B : Set X} {defect : X → ℝ} {x : X} :
    x ∈ maxwellLimitFiber B defect ↔ x ∈ closure B ∧ defect x = 0 := by
  rfl

/-- Choose a representative of a connected component. -/
noncomputable def maxwellComponentRepresentative {X : Type*} [TopologicalSpace X]
    (c : ConnectedComponents X) : X :=
  Classical.choose (ConnectedComponents.surjective_coe c)

@[simp]
theorem maxwellComponentRepresentative_mk {X : Type*} [TopologicalSpace X]
    (c : ConnectedComponents X) :
    ConnectedComponents.mk (maxwellComponentRepresentative c) = c :=
  Classical.choose_spec (ConnectedComponents.surjective_coe c)

/-- A finite real-valued family admits one strict common upper bound. -/
theorem exists_strict_upperBound_fin {k : ℕ} (f : Fin k → ℝ) :
    ∃ R : ℝ, ∀ i, f i < R := by
  refine ⟨∑ i, |f i| + 1, fun i ↦ ?_⟩
  calc
    f i ≤ |f i| := le_abs_self (f i)
    _ ≤ ∑ j, |f j| :=
      Finset.single_le_sum (fun j _ ↦ abs_nonneg (f j)) (Finset.mem_univ i)
    _ < ∑ j, |f j| + 1 := by linarith

/--
On a compact space, an open neighborhood of the zero fiber of a continuous real-valued function
contains one uniform strict sublevel of its absolute value.
-/
theorem exists_pos_defect_threshold_of_compact
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (defect : X → ℝ) (hdefect : Continuous defect) {O : Set X}
    (hO : IsOpen O) (hzero : {x | defect x = 0} ⊆ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, |defect x| < ε → x ∈ O := by
  classical
  by_cases hnonempty : Oᶜ.Nonempty
  · obtain ⟨x, hx, hxmin⟩ :=
      hO.isClosed_compl.isCompact.exists_isMinOn hnonempty hdefect.abs.continuousOn
    have hdefect_ne : defect x ≠ 0 := by
      intro hxzero
      exact hx (hzero hxzero)
    refine ⟨|defect x|, abs_pos.mpr hdefect_ne, fun y hy ↦ ?_⟩
    by_contra hyO
    have hycompl : y ∈ Oᶜ := hyO
    exact (not_lt_of_ge (hxmin hycompl)) hy
  · refine ⟨1, zero_lt_one, fun x _ ↦ ?_⟩
    by_contra hxO
    exact hnonempty ⟨x, hxO⟩

/-- The separated numerical labels assigned to a finite clopen partition. -/
def maxwellPartitionLabelValue {k : ℕ} (i : Fin k) : ℝ :=
  4 * (i.val : ℝ)

/-- Disjoint open intervals around the numerical partition labels. -/
def maxwellPartitionLabelInterval {k : ℕ} (i : Fin k) : Set ℝ :=
  Ioo (maxwellPartitionLabelValue i - 1) (maxwellPartitionLabelValue i + 1)

theorem maxwellPartitionLabelValue_mem_interval {k : ℕ} (i : Fin k) :
    maxwellPartitionLabelValue i ∈ maxwellPartitionLabelInterval i := by
  simp [maxwellPartitionLabelInterval]

theorem maxwellPartitionLabelIntervals_pairwiseDisjoint {k : ℕ} :
    (Set.univ : Set (Fin k)).PairwiseDisjoint maxwellPartitionLabelInterval := by
  intro i _ j _ hij
  change Disjoint (maxwellPartitionLabelInterval i)
    (maxwellPartitionLabelInterval j)
  rw [Set.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hijle : i.val + 1 ≤ j.val := Nat.add_one_le_iff.mpr hijlt
    have hijle' : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hijle
    exact (not_lt_of_ge (show maxwellPartitionLabelValue i + 1 ≤
        maxwellPartitionLabelValue j - 1 by
          unfold maxwellPartitionLabelValue
          linarith)) (lt_trans hxj.1 hxi.2)
  · have hjile : j.val + 1 ≤ i.val := Nat.add_one_le_iff.mpr hjilt
    have hjile' : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hjile
    exact (not_lt_of_ge (show maxwellPartitionLabelValue j + 1 ≤
        maxwellPartitionLabelValue i - 1 by
          unfold maxwellPartitionLabelValue
          linarith)) (lt_trans hxi.1 hxj.2)

/--
A finite pairwise-disjoint open cover consists of clopen sets.  This elementary helper is what
turns the label intervals, after restriction to a tube, into component separators.
-/
theorem isClopen_of_finite_pairwiseDisjoint_open_cover
    {X I : Type*} [TopologicalSpace X] [Finite I]
    (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcover : ⋃ i, U i = Set.univ)
    (hUdisj : (Set.univ : Set I).PairwiseDisjoint U) (i : I) :
    IsClopen (U i) := by
  let V : Set X := ⋃ j : {j : I // j ≠ i}, U j
  apply isClopen_of_disjoint_cover_open (a := U i) (b := V)
  · intro x _
    obtain ⟨j, hj⟩ := Set.iUnion_eq_univ_iff.mp hUcover x
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
  · exact hUopen i
  · exact isOpen_iUnion fun j ↦ hUopen j
  · rw [Set.disjoint_left]
    intro x hxi hxV
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxV
    exact (Set.disjoint_left.mp
      (hUdisj (Set.mem_univ i) (Set.mem_univ j.1) (Ne.symm j.2))) hxi hxj

/--
Failure of the extended-natural cardinal bound by `N` supplies `N + 1` distinct elements.
-/
theorem exists_fin_succ_injection_of_enatCard_not_le
    {α : Type*} {N : ℕ} (h : ¬ ENat.card α ≤ (N : ℕ∞)) :
    ∃ f : Fin (N + 1) → α, Function.Injective f := by
  have hlt : (N : ℕ∞) < ENat.card α := lt_of_not_ge h
  have hsucc : (N + 1 : ℕ∞) ≤ ENat.card α := by
    rw [ENat.natCast_add_one_le_iff]
    exact hlt
  have hcard : ((N + 1 : ℕ) : Cardinal) ≤ Cardinal.mk α := by
    exact Cardinal.natCast_le_toENat.mp hsucc
  obtain ⟨f⟩ : Nonempty (Fin (N + 1) ↪ α) := by
    rw [← Cardinal.lift_mk_le']
    simpa using hcard
  exact ⟨f, f.injective⟩

/--
The finite-selected-components form of compact Maxwell separation.  Every injected family of
`N + 1` limit components forces at least `N + 1` components in one strict tube.
-/
theorem enatCard_fin_succ_le_some_maxwellStrictTube_components
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    (B : Set X) (radius defect : X → ℝ)
    (hradius : Continuous radius) (hdefect : Continuous defect)
    (hcompact : ∀ R : ℝ, IsCompact {x | radius x ≤ R}) (N : ℕ)
    (selected : Fin (N + 1) → ConnectedComponents (maxwellLimitFiber B defect))
    (hselected : Function.Injective selected) :
    ∃ R ε : ℝ, 0 < ε ∧
      (N + 1 : ℕ∞) ≤ ENat.card
        (ConnectedComponents (maxwellStrictTube B radius defect R ε)) := by
  classical
  let A : Set X := maxwellLimitFiber B defect
  let a : Fin (N + 1) → A := fun i ↦ maxwellComponentRepresentative (selected i)
  have ha_component (i : Fin (N + 1)) : ConnectedComponents.mk (a i) = selected i := by
    exact maxwellComponentRepresentative_mk (selected i)
  obtain ⟨R, hR⟩ := exists_strict_upperBound_fin (fun i ↦ radius (a i))
  let Core : Set X := {x | radius x ≤ R} ∩ closure B
  let K : Set X := Core ∩ {x | defect x = 0}
  have hCore_compact : IsCompact Core := by
    exact (hcompact R).inter_right isClosed_closure
  have hCore_closed : IsClosed Core := by
    exact (isClosed_le hradius continuous_const).inter isClosed_closure
  have hK_compact : IsCompact K := by
    exact hCore_compact.inter_right (isClosed_eq hdefect continuous_const)
  have hK_closed : IsClosed K := by
    exact hCore_closed.inter (isClosed_eq hdefect continuous_const)
  let k : Fin (N + 1) → K := fun i ↦
    ⟨a i, ⟨⟨(hR i).le, (a i).property.1⟩, (a i).property.2⟩⟩
  let inclusion : K → A := fun z ↦
    ⟨z, ⟨z.property.1.2, z.property.2⟩⟩
  have hinclusion : Continuous inclusion := by
    exact continuous_subtype_val.subtype_mk fun z ↦ ⟨z.property.1.2, z.property.2⟩
  have hk_component : Function.Injective (fun i ↦ ConnectedComponents.mk (k i)) := by
    intro i j hij
    have hmapped := congrArg hinclusion.connectedComponentsMap hij
    apply hselected
    simpa only [Continuous.connectedComponentsMap_mk, inclusion, k, ha_component] using hmapped
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK_compact
  let Z : Fin (N + 1) → Set (ConnectedComponents K) := fun i ↦ {ConnectedComponents.mk (k i)}
  let D : Fin (N + 1) → Set (ConnectedComponents K) := fun _ ↦ Set.univ
  have hZclosed : ∀ i, IsClosed (Z i) := fun i ↦ isClosed_singleton
  have hDclopen : ∀ i, IsClopen (D i) := fun i ↦ isClopen_univ
  have hZsubsetD : ∀ i, Z i ⊆ D i := fun i ↦ subset_univ _
  have hZdisj : (Set.univ : Set (Fin (N + 1))).PairwiseDisjoint Z := by
    simpa only [Z, Set.pairwiseDisjoint_singleton_iff_injOn, Set.injOn_univ] using hk_component
  obtain ⟨C, hCclopen, hZsubsetC, _hCsubsetD, hDCcover, hCdisj⟩ :=
    exists_clopen_partition_of_clopen_cover hZclosed hDclopen hZsubsetD hZdisj
  have hCcover : ⋃ i, C i = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro q
    apply hDCcover
    exact Set.mem_iUnion.mpr ⟨(0 : Fin (N + 1)), Set.mem_univ q⟩
  have hCglue (i j : Fin (N + 1)) (q : ConnectedComponents K)
      (hqi : q ∈ C i) (hqj : q ∈ C j) : i = j := by
    by_contra hij
    exact (Set.disjoint_left.mp
      (hCdisj (Set.mem_univ i) (Set.mem_univ j) hij)) hqi hqj
  let partitionIndex : ConnectedComponents K → Fin (N + 1) :=
    Set.liftCover C (fun i _ ↦ i) hCglue hCcover
  have hpartitionIndex_locallyConstant : IsLocallyConstant partitionIndex := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro i
    convert! (hCclopen i).2
    ext q
    simp [partitionIndex, Set.preimage_liftCover]
  let labelK : K → ℝ := fun z ↦
    maxwellPartitionLabelValue (partitionIndex (ConnectedComponents.mk z))
  have hlabelK_continuous : Continuous labelK := by
    exact (hpartitionIndex_locallyConstant.comp maxwellPartitionLabelValue).continuous.comp
      ConnectedComponents.continuous_coe
  have hlabelK_value (i : Fin (N + 1)) (z : K)
      (hz : ConnectedComponents.mk z ∈ C i) :
      labelK z = maxwellPartitionLabelValue i := by
    simp only [labelK, partitionIndex, Set.liftCover_of_mem hz]
  let labelKMap : C(K, ℝ) := ⟨labelK, hlabelK_continuous⟩
  obtain ⟨label, hlabel_restrict⟩ := labelKMap.exists_restrict_eq hK_closed
  have hlabel_eq (z : K) : label z = labelK z := by
    have hz := DFunLike.congr_fun hlabel_restrict z
    change label z = labelK z at hz
    exact hz
  let V : Set ℝ := ⋃ i : Fin (N + 1), maxwellPartitionLabelInterval i
  have hVopen : IsOpen V :=
    isOpen_iUnion fun i ↦ isOpen_Ioo
  let OCore : Set Core := (fun z : Core ↦ label z) ⁻¹' V
  have hOCore_open : IsOpen OCore := by
    exact hVopen.preimage (label.continuous.comp continuous_subtype_val)
  have hzero_subset_OCore : {z : Core | defect z = 0} ⊆ OCore := by
    intro z hz
    let zK : K := ⟨z, ⟨z.property, hz⟩⟩
    obtain ⟨i, hi⟩ := Set.iUnion_eq_univ_iff.mp hCcover (ConnectedComponents.mk zK)
    have hvalue : label z = maxwellPartitionLabelValue i := by
      simpa only [zK] using (hlabel_eq zK).trans (hlabelK_value i zK hi)
    change label z ∈ V
    rw [hvalue]
    exact Set.mem_iUnion.mpr ⟨i, maxwellPartitionLabelValue_mem_interval i⟩
  letI : CompactSpace Core := isCompact_iff_compactSpace.mp hCore_compact
  obtain ⟨ε, hε, hthreshold⟩ :=
    exists_pos_defect_threshold_of_compact
      (fun z : Core ↦ defect z) (hdefect.comp continuous_subtype_val)
      hOCore_open hzero_subset_OCore
  let T : Set X := maxwellStrictTube B radius defect R ε
  have hT_label (z : T) : label z ∈ V := by
    let zCore : Core :=
      ⟨z, ⟨(mem_maxwellStrictTube.mp z.property).2.1.le,
        subset_closure (mem_maxwellStrictTube.mp z.property).1⟩⟩
    exact hthreshold zCore (mem_maxwellStrictTube.mp z.property).2.2
  let U : Fin (N + 1) → Set T := fun i ↦
    (fun z : T ↦ label z) ⁻¹' maxwellPartitionLabelInterval i
  have hUopen : ∀ i, IsOpen (U i) := fun i ↦ by
    exact isOpen_Ioo.preimage (label.continuous.comp continuous_subtype_val)
  have hUcover : ⋃ i, U i = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro z
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hT_label z)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hUdisj : (Set.univ : Set (Fin (N + 1))).PairwiseDisjoint U := by
    intro i _ j _ hij
    exact Disjoint.preimage (fun z : T ↦ label z)
      (maxwellPartitionLabelIntervals_pairwiseDisjoint
        (Set.mem_univ i) (Set.mem_univ j) hij)
  have hUclopen : ∀ i, IsClopen (U i) := fun i ↦
    isClopen_of_finite_pairwiseDisjoint_open_cover U hUopen hUcover hUdisj i
  have hUnonempty : ∀ i, (U i).Nonempty := by
    intro i
    have hkC : ConnectedComponents.mk (k i) ∈ C i := by
      apply hZsubsetC i
      exact Set.mem_singleton (ConnectedComponents.mk (k i))
    have hlabel_ai : label (a i) = maxwellPartitionLabelValue i := by
      simpa only [k] using (hlabel_eq (k i)).trans (hlabelK_value i (k i) hkC)
    let W : Set X :=
      (label ⁻¹' maxwellPartitionLabelInterval i ∩ {x | radius x < R}) ∩
        {x | |defect x| < ε}
    have hWopen : IsOpen W := by
      exact ((isOpen_Ioo.preimage label.continuous).inter
        (isOpen_lt hradius continuous_const)).inter
        (isOpen_lt hdefect.abs continuous_const)
    have haW : (a i : X) ∈ W := by
      refine ⟨⟨?_, hR i⟩, ?_⟩
      · change label (a i) ∈ maxwellPartitionLabelInterval i
        rw [hlabel_ai]
        exact maxwellPartitionLabelValue_mem_interval i
      · change |defect (a i)| < ε
        rw [(a i).property.2, abs_zero]
        exact hε
    obtain ⟨b, hbW, hbB⟩ :=
      mem_closure_iff.mp (a i).property.1 W hWopen haW
    let bT : T := ⟨b, mem_maxwellStrictTube.mpr ⟨hbB, hbW.1.2, hbW.2⟩⟩
    exact ⟨bT, hbW.1.1⟩
  choose tubePoint htubePoint using hUnonempty
  have hcomponent_injective :
      Function.Injective (fun i ↦ ConnectedComponents.mk (tubePoint i)) := by
    intro i j hij
    by_contra hne
    have hcomponents : connectedComponent (tubePoint i) = connectedComponent (tubePoint j) :=
      ConnectedComponents.coe_eq_coe.mp hij
    have hjUi : tubePoint j ∈ U i := by
      apply (hUclopen i).connectedComponent_subset (htubePoint i)
      rw [hcomponents]
      exact mem_connectedComponent
    exact (Set.disjoint_left.mp
      (hUdisj (Set.mem_univ i) (Set.mem_univ j) hne)) hjUi (htubePoint j)
  refine ⟨R, ε, hε, ?_⟩
  simpa only [ENat.card_eq_coe_fintype_card, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one, T] using
    ENat.card_le_card_of_injective hcomponent_injective

/--
The compact topological core of Maxwell's closure comparison: a uniform component bound for all
strict tubes also bounds the zero-defect locus in `closure B`.
-/
theorem enatCard_connectedComponents_maxwellLimitFiber_le
    {X : Type*} [TopologicalSpace X] [T2Space X] [NormalSpace X]
    (B : Set X) (radius defect : X → ℝ)
    (hradius : Continuous radius) (hdefect : Continuous defect)
    (hcompact : ∀ R : ℝ, IsCompact {x | radius x ≤ R}) (N : ℕ)
    (htube : ∀ R ε : ℝ, 0 < ε →
      ENat.card (ConnectedComponents (maxwellStrictTube B radius defect R ε)) ≤ (N : ℕ∞)) :
    ENat.card (ConnectedComponents (maxwellLimitFiber B defect)) ≤ (N : ℕ∞) := by
  by_contra hbound
  obtain ⟨selected, hselected⟩ :=
    exists_fin_succ_injection_of_enatCard_not_le hbound
  obtain ⟨R, ε, hε, hlower⟩ :=
    enatCard_fin_succ_le_some_maxwellStrictTube_components
      B radius defect hradius hdefect hcompact N selected hselected
  have himpossible : (N + 1 : ℕ∞) ≤ (N : ℕ∞) :=
    hlower.trans (htube R ε hε)
  have : N + 1 ≤ N := ENat.natCast_le_natCast.mp himpossible
  omega

end AbelFormalization
