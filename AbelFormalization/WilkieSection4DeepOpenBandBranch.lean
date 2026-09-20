import AbelFormalization.WilkieSection4DeepFiniteClosedRefinement
import AbelFormalization.WilkieSection4DeepCommonRefinementSuccessor
import AbelFormalization.WilkieSection4LociRefinement
import AbelFormalization.WilkieSection4BadLocusExclusion
import AbelFormalization.CharbonnelOrderedSelectorGraph

/-!
# The retained open-band branch of Wilkie Section 4

This file carries the genuine cutoff/cardinality/selector argument into the
recursive deep-cell API.  The local construction keeps the two ambient band
endpoints: its outer selector regions are the bands from the lower endpoint
to the first selector and from the last selector to the upper endpoint.
Consequently every output cell is contained in the original band, while all
projected bases retain their complete recursive enrichment.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A partition of the band over one retained base.  Every top-dimensional
cell has exactly the supplied deep base; this is the invariant needed when
local constructions are flattened over a lower-dimensional deep partition. -/
structure CharbonnelFinitePartitionedDeepLocalBandCover
    (S : EuclideanSetFamily) {p : ℕ}
    (base : CharbonnelDeepEnrichedCell S p)
    (f g : RealEuclidean p → ℝ)
    (A : Set (RealEuclidean (p + 1))) where
  Index : Type
  indexFinite : Finite Index
  cell : Index → CharbonnelDeepEnrichedCell S (p + 1)
  contained : ∀ i,
    (cell i).carrier ⊆ charbonnelOpenBand base.carrier f g
  covers : ∀ z ∈ charbonnelOpenBand base.carrier f g,
    ∃ i, z ∈ (cell i).carrier
  compatible : ∀ i,
    (cell i).carrier ⊆ A ∨ Disjoint (cell i).carrier A
  cells_eq_or_disjoint : ∀ i j,
    (cell i).carrier = (cell j).carrier ∨
      Disjoint (cell i).carrier (cell j).carrier
  projectedBase_eq : ∀ i (hp : 0 < p),
    (cell i).projectedBase hp = base

/-- Over a retained base with exact finite fibres, the canonical ordered
selectors cut the ambient open band into retained graph and band cells.
The endpoint bands replace the two unbounded rays of the usual selector
partition. -/
theorem exists_charbonnelFinitePartitionedDeepLocalBandCover_of_exactFibers
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p r : ℕ} (hp : 0 < p)
    (ambientBase base : CharbonnelDeepEnrichedCell S p)
    (hbase : base.carrier ⊆ ambientBase.carrier)
    (f g : RealEuclidean p → ℝ)
    (hf : ContinuousOn f ambientBase.carrier)
    (hg : ContinuousOn g ambientBase.carrier)
    (hfg : ∀ x ∈ ambientBase.carrier, f x < g x)
    (hfGraph : charbonnelRestrictedGraph ambientBase.carrier f ∈
      charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph ambientBase.carrier g ∈
      charbonnelClosure S (p + 1))
    {A : MaxwellRelation p 1}
    (hAsub : A ⊆ charbonnelOpenBand ambientBase.carrier f g)
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hfiber : ∀ x ∈ base.carrier,
      (maxwellScalarFiber A x).Finite ∧
        (maxwellScalarFiber A x).ncard = r)
    (hescape : MaxwellScalarFiberNoEscape base.carrier A)
    (hcollision : MaxwellScalarFiberNoCollision base.carrier A) :
    Nonempty
      (CharbonnelFinitePartitionedDeepLocalBandCover
        S base f g A) := by
  classical
  let selector : Fin r → RealEuclidean p → ℝ :=
    fun i x ↦ maxwellOrderedScalarFiberEnumeration A x i
  have hfBase : ContinuousOn f base.carrier := hf.mono hbase
  have hgBase : ContinuousOn g base.carrier := hg.mono hbase
  have hfgBase : ∀ x ∈ base.carrier, f x < g x :=
    fun x hx ↦ hfg x (hbase hx)
  have hbaseMem : base.carrier ∈ charbonnelClosure S p := by
    simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using
      (base.toCell hC).carrier_mem
  have hfGraphBase : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (p + 1) :=
    charbonnelRestrictedGraph_mem_charbonnelClosure_of_subset
      hC hp hbase hbaseMem hfGraph
  have hgGraphBase : charbonnelRestrictedGraph base.carrier g ∈
      charbonnelClosure S (p + 1) :=
    charbonnelRestrictedGraph_mem_charbonnelClosure_of_subset
      hC hp hbase hbaseMem hgGraph
  have hselectorContinuous : ∀ i,
      ContinuousOn (selector i) base.carrier := by
    intro i
    exact continuousOn_maxwellOrderedScalarFiberEnumeration
      hfiber hescape hcollision i
  have hselectorOrdered : ∀ x ∈ base.carrier,
      StrictMono (fun i ↦ selector i x) := by
    intro x hx
    exact maxwellOrderedScalarFiberEnumeration_strictMono
      (hfiber x hx).1 (hfiber x hx).2
  have hselectorGraph : ∀ i,
      charbonnelRestrictedGraph base.carrier (selector i) ∈
        charbonnelClosure S (p + 1) := by
    intro i
    exact
      charbonnelRestrictedGraph_maxwellOrderedScalarFiberEnumeration_mem_charbonnelClosure
        hC hp hbaseMem hAmem hfiber i
  have hselectorLower : ∀ i x, x ∈ base.carrier →
      f x < selector i x := by
    intro i x hx
    have hmem := maxwellOrderedScalarFiberEnumeration_mem
      (hfiber x hx).1 (hfiber x hx).2 i
    have hband := hAsub hmem
    simpa [charbonnelOpenBand, selector] using hband.2.1
  have hselectorUpper : ∀ i x, x ∈ base.carrier →
      selector i x < g x := by
    intro i x hx
    have hmem := maxwellOrderedScalarFiberEnumeration_mem
      (hfiber x hx).1 (hfiber x hx).2 i
    have hband := hAsub hmem
    simpa [charbonnelOpenBand, selector] using hband.2.2
  by_cases hr : 0 < r
  · let vertical : CharbonnelOrderedSelectorRegion r →
        CharbonnelEnrichedVerticalCell S (base.toCell hC)
      | .lower => .band f (selector (charbonnelFirstSelectorIndex hr))
          hfBase (hselectorContinuous _) (hselectorLower _) hfGraphBase
            (hselectorGraph _)
      | .graph i => .graph (selector i) (hselectorContinuous i)
          (hselectorGraph i)
      | .band i => .band
          (selector (charbonnelBandLeftIndex i))
          (selector (charbonnelBandRightIndex i))
          (hselectorContinuous _) (hselectorContinuous _)
          (fun x hx ↦ hselectorOrdered x hx
            (charbonnelBandLeftIndex_lt_rightIndex i))
          (hselectorGraph _) (hselectorGraph _)
      | .upper => .band (selector (charbonnelLastSelectorIndex hr)) g
          (hselectorContinuous _) hgBase (hselectorUpper _)
            (hselectorGraph _) hgGraphBase
    let cell : CharbonnelOrderedSelectorRegion r →
        CharbonnelDeepEnrichedCell S (p + 1) :=
      fun region ↦ base.ofVertical hC hp (vertical region)
    have hcellCarrier : ∀ region,
        (cell region).carrier =
          charbonnelOrderedSelectorRegionCarrier
              base.carrier selector hr region ∩
            charbonnelOpenBand base.carrier f g := by
      intro region
      cases region with
      | lower =>
          ext z
          simp only [cell, vertical,
            CharbonnelDeepEnrichedCell.ofVertical_carrier]
          simp only [charbonnelOrderedSelectorRegionCarrier,
            charbonnelOpenBand, charbonnelLowerRayCell,
            Set.mem_ofPred_eq, Set.mem_inter_iff]
          constructor
          · rintro ⟨hx, hfy, hys⟩
            exact ⟨⟨hx, hys⟩, ⟨hx, hfy,
              lt_trans hys (hselectorUpper _ _ hx)⟩⟩
          · rintro ⟨⟨hx, hys⟩, ⟨_hx', hfy, _hyg⟩⟩
            exact ⟨hx, hfy, hys⟩
      | graph i =>
          ext z
          simp only [cell, vertical,
            CharbonnelDeepEnrichedCell.ofVertical_carrier]
          simp only [charbonnelOrderedSelectorRegionCarrier,
            charbonnelRestrictedGraph, charbonnelOpenBand,
            Set.mem_ofPred_eq, Set.mem_inter_iff]
          constructor
          · intro hz
            change realEuclideanTakeLeft z ∈ base.carrier ∧
              realEuclideanTakeRight z 0 =
                selector i (realEuclideanTakeLeft z) at hz
            obtain ⟨hx, hy⟩ := hz
            refine ⟨⟨hx, hy⟩, hx, ?_, ?_⟩
            · simpa [hy] using hselectorLower i _ hx
            · simpa [hy] using hselectorUpper i _ hx
          · intro hz
            change realEuclideanTakeLeft z ∈ base.carrier ∧
              realEuclideanTakeRight z 0 =
                selector i (realEuclideanTakeLeft z)
            exact hz.1
      | band i =>
          ext z
          simp only [cell, vertical,
            CharbonnelDeepEnrichedCell.ofVertical_carrier]
          simp only [charbonnelOrderedSelectorRegionCarrier,
            charbonnelOpenBand, Set.mem_ofPred_eq, Set.mem_inter_iff]
          constructor
          · intro hz
            change realEuclideanTakeLeft z ∈ base.carrier ∧
              selector (charbonnelBandLeftIndex i)
                  (realEuclideanTakeLeft z) < realEuclideanTakeRight z 0 ∧
              realEuclideanTakeRight z 0 <
                selector (charbonnelBandRightIndex i)
                  (realEuclideanTakeLeft z) at hz
            obtain ⟨hx, hleft, hright⟩ := hz
            refine ⟨⟨hx, hleft, hright⟩, hx, ?_, ?_⟩
            · exact lt_trans (hselectorLower _ _ hx) hleft
            · exact lt_trans hright (hselectorUpper _ _ hx)
          · intro hz
            change realEuclideanTakeLeft z ∈ base.carrier ∧
              selector (charbonnelBandLeftIndex i)
                  (realEuclideanTakeLeft z) < realEuclideanTakeRight z 0 ∧
              realEuclideanTakeRight z 0 <
                selector (charbonnelBandRightIndex i)
                  (realEuclideanTakeLeft z)
            exact hz.1
      | upper =>
          ext z
          simp only [cell, vertical,
            CharbonnelDeepEnrichedCell.ofVertical_carrier]
          simp only [charbonnelOrderedSelectorRegionCarrier,
            charbonnelOpenBand, charbonnelUpperRayCell,
            Set.mem_ofPred_eq, Set.mem_inter_iff]
          constructor
          · rintro ⟨hx, hsy, hyg⟩
            exact ⟨⟨hx, hsy⟩, ⟨hx,
              lt_trans (hselectorLower _ _ hx) hsy, hyg⟩⟩
          · rintro ⟨⟨hx, hsy⟩, ⟨_hx', _hfy, hyg⟩⟩
            exact ⟨hx, hsy, hyg⟩
    refine ⟨
      { Index := CharbonnelOrderedSelectorRegion r
        indexFinite := inferInstance
        cell := cell
        contained := ?_
        covers := ?_
        compatible := ?_
        cells_eq_or_disjoint := ?_
        projectedBase_eq := ?_ }⟩
    · intro region
      rw [hcellCarrier region]
      exact inter_subset_right
    · intro z hz
      obtain ⟨region, hregion⟩ :=
        exists_charbonnelOrderedSelectorRegion_contains hr
          (fun i ↦ selector i (realEuclideanTakeLeft z))
          (realEuclideanTakeRight z 0)
      refine ⟨region, ?_⟩
      rw [hcellCarrier region]
      refine ⟨?_, hz⟩
      cases region <;> exact ⟨hz.1, hregion⟩
    · intro region
      rw [hcellCarrier region]
      rcases charbonnelOrderedSelectorRegionCarrier_compatible
          selector hr hselectorOrdered
          (fun z hz ↦
            mem_iff_exists_maxwellOrderedScalarFiberEnumeration
              hfiber z hz)
          region with hsub | hdisjoint
      · exact Or.inl (inter_subset_left.trans hsub)
      · exact Or.inr (hdisjoint.mono inter_subset_left Subset.rfl)
    · intro left right
      rcases charbonnelOrderedSelectorRegionCarrier_eq_or_disjoint
          selector hr hselectorOrdered left right with heq | hdisjoint
      · left
        rw [hcellCarrier left, hcellCarrier right, heq]
      · right
        rw [hcellCarrier left, hcellCarrier right]
        exact hdisjoint.mono inter_subset_left inter_subset_left
    · intro region hp'
      have : hp' = hp := Subsingleton.elim _ _
      subst hp'
      exact CharbonnelDeepEnrichedCell.ofVertical_projectedBase
        hC hp base (vertical region)
  · have hrzero : r = 0 := Nat.eq_zero_of_not_pos hr
    subst r
    let vertical : CharbonnelEnrichedVerticalCell S (base.toCell hC) :=
      .band f g hfBase hgBase hfgBase hfGraphBase hgGraphBase
    let cell : CharbonnelDeepEnrichedCell S (p + 1) :=
      base.ofVertical hC hp vertical
    have hcellCarrier : cell.carrier =
        charbonnelOpenBand base.carrier f g := by
      rfl
    refine ⟨
      { Index := Unit
        indexFinite := inferInstance
        cell := fun _ ↦ cell
        contained := fun _ ↦ hcellCarrier.le
        covers := fun z hz ↦ ⟨(), hcellCarrier.symm ▸ hz⟩
        compatible := ?_
        cells_eq_or_disjoint := fun _ _ ↦ Or.inl rfl
        projectedBase_eq := ?_ }⟩
    · intro _
      right
      rw [Set.disjoint_left]
      intro z hzCell hzA
      have hzBase : realEuclideanTakeLeft z ∈ base.carrier := by
        exact (hcellCarrier ▸ hzCell).1
      obtain ⟨i, _hi⟩ :=
        (mem_iff_exists_maxwellOrderedScalarFiberEnumeration
          hfiber z hzBase).mp hzA
      exact Fin.elim0 i
    · intro _ hp'
      have : hp' = hp := Subsingleton.elim _ _
      subst hp'
      exact CharbonnelDeepEnrichedCell.ofVertical_projectedBase
        hC hp base vertical

/-! ## The bounded retained open-band branch -/

/-- The cutoff locus bounds every fibre over a nonempty open compatible
base.  This is the preliminary finite-fibre step needed before Theorem 2.2
can exclude the collision and endpoint traces. -/
theorem maxwellScalarFiber_encard_lt_cutoff_of_open_compatible_locus_deep
    {p N : ℕ} {C B : Set (RealEuclidean p)}
    {A : MaxwellRelation p 1}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty) (hBC : B ⊆ C)
    (hNempty : interior
      (closure (wilkieSection4FiberCardinalityLocus C A N)) = ∅)
    (hcompatible :
      B ⊆ closure (wilkieSection4FiberCardinalityLocus C A N) ∨
        Disjoint B
          (closure (wilkieSection4FiberCardinalityLocus C A N))) :
    ∀ x ∈ B, (maxwellScalarFiber A x).encard < (N : ℕ∞) := by
  have hdisjoint : Disjoint B
      (closure (wilkieSection4FiberCardinalityLocus C A N)) := by
    rcases hcompatible with hsubset | hdisjoint
    · have hBInterior : B ⊆ interior
          (closure (wilkieSection4FiberCardinalityLocus C A N)) :=
        interior_maximal hsubset hBopen
      obtain ⟨x, hxB⟩ := hBnonempty
      have hxEmpty : x ∈ (∅ : Set (RealEuclidean p)) := by
        rw [← hNempty]
        exact hBInterior hxB
      exact hxEmpty.elim
    · exact hdisjoint
  intro x hxB
  have hxNot : x ∉ wilkieSection4FiberCardinalityLocus C A N := by
    intro hx
    exact Set.disjoint_left.mp hdisjoint hxB (subset_closure hx)
  have hnotLe : ¬ (N : ℕ∞) ≤ (maxwellScalarFiber A x).encard := by
    intro hle
    exact hxNot
      ((mem_wilkieSection4FiberCardinalityLocus_iff_encard C A x).mpr
        ⟨hBC hxB, hle⟩)
  exact lt_of_not_ge hnotLe

/-- Projection coherence is preserved when a deep family is reindexed. -/
private theorem deepOpenBandProjectionCoherent_comp
    {S : EuclideanSetFamily} {I K : Type} :
    ∀ {n : ℕ} {cell : I → CharbonnelDeepEnrichedCell S (n + 1)},
      CharbonnelDeepCellFamilyProjectionCoherent n cell →
      (e : K → I) →
      CharbonnelDeepCellFamilyProjectionCoherent n (fun k ↦ cell (e k))
  | 0, _cell, _hcoherent, _e => trivial
  | n + 1, cell, hcoherent, e => by
      refine ⟨?_, ?_⟩
      · intro i j
        exact hcoherent.1 (e i) (e j)
      · exact deepOpenBandProjectionCoherent_comp hcoherent.2 e

/-- The genuine full-dimensional branch of Wilkie's retained successor
induction.  The ambient base is bounded, as in Wilkie's `(I)`/`(II)`
invariants.  The empty-interior premise is explicit: it is exactly what the
Charbonnel 2.1 cutoff theorem uses to make the fibres finite.  Non-open lower
base cells are delegated to the lower-dimensional branch through `hnonopen`.
-/
theorem exists_charbonnelFinitePartitionedDeepRelativeClosedDecomposition_openBand_emptyInterior
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {m : ℕ}
    (hI : CharbonnelBoundedDeepRelativeClosedDecompositionAt S m)
    (hII : CharbonnelBoundedDeepRelativeCommonRefinementAt S m)
    (base : CharbonnelDeepEnrichedCell S (m + 1))
    (hbaseBounded : Bornology.IsBounded base.carrier)
    (f g : RealEuclidean (m + 1) → ℝ)
    (hf : ContinuousOn f base.carrier)
    (hg : ContinuousOn g base.carrier)
    (hfg : ∀ x ∈ base.carrier, f x < g x)
    (hfGraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S ((m + 1) + 1))
    (hgGraph : charbonnelRestrictedGraph base.carrier g ∈
      charbonnelClosure S ((m + 1) + 1))
    {A : MaxwellRelation (m + 1) 1}
    (hAmem : A ∈ charbonnelClosure S ((m + 1) + 1))
    (hAempty : interior A = ∅)
    (hAsub : A ⊆ charbonnelOpenBand base.carrier f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A : Set (charbonnelOpenBand base.carrier f g)))
    (hnonopen : ∀ small : CharbonnelDeepEnrichedCell S (m + 1),
      small.carrier ⊆ base.carrier →
      Bornology.IsBounded small.carrier →
      ¬ IsOpen small.carrier →
      Nonempty
        (CharbonnelFinitePartitionedDeepLocalBandCover
          S small f g A)) :
    Nonempty
      (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S (charbonnelOpenBand base.carrier f g) (fun _ : Unit ↦ A)) := by
  classical
  let hp : 0 < m + 1 := by omega
  let hweak : PositiveArityWeakSetStructure (charbonnelClosure S) :=
    hC.toPositiveArityWeakSetStructure
  have hbaseMem : base.carrier ∈ charbonnelClosure S (m + 1) := by
    simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using
      (base.toCell hweak).carrier_mem
  obtain ⟨N, hN, hNempty⟩ :=
    exists_wilkieSection4_cardinalityCutoff
      hC h21 hp hbaseMem hAmem hAempty
  let loci : WilkieSection4LociIndex N → Set (RealEuclidean (m + 1)) :=
    wilkieSection4LociTarget base.carrier A f g
  let target : WilkieSection4LociIndex N → Set (RealEuclidean (m + 1)) :=
    fun j ↦ loci j ∩ base.carrier
  have htargetSub : ∀ j, target j ⊆ base.carrier :=
    fun _ ↦ inter_subset_right
  have htargetMem : ∀ j,
      target j ∈ charbonnelClosure S (m + 1) := by
    intro j
    exact hweak.ws1_inter (by omega)
      (wilkieSection4LociTarget_mem_charbonnelClosure
        hweak hp hbaseMem hAmem hfGraph hgGraph j)
      hbaseMem
  have htargetClosed : ∀ j,
      IsClosed (Subtype.val ⁻¹' target j : Set base.carrier) := by
    intro j
    exact isClosed_preimage_val_inter_right
      (wilkieSection4LociTarget_isClosed j)
  obtain ⟨fine⟩ :=
    exists_charbonnelFinitePartitionedBoundedDeepSimultaneousClosedRefinement
      hI hII base hbaseBounded target htargetSub htargetMem htargetClosed
  let carrierSetoid : Setoid fine.Index :=
    Setoid.ker (fun i ↦ (fine.cell i).carrier)
  let BaseIndex := Quotient carrierSetoid
  let representative : BaseIndex → fine.Index := Quotient.out
  let baseCell : BaseIndex → CharbonnelDeepEnrichedCell S (m + 1) :=
    fun q ↦ fine.cell (representative q)
  letI : Finite fine.Index := fine.indexFinite
  letI : Finite BaseIndex := Quotient.finite carrierSetoid
  have hbaseCellSub : ∀ q, (baseCell q).carrier ⊆ base.carrier :=
    fun q ↦ fine.contained (representative q)
  have hbaseCellBounded : ∀ q,
      Bornology.IsBounded (baseCell q).carrier :=
    fun q ↦ hbaseBounded.subset (hbaseCellSub q)
  have hlociCompatible : ∀ q j,
      (baseCell q).carrier ⊆ loci j ∨
        Disjoint (baseCell q).carrier (loci j) := by
    intro q j
    have hcompat := fine.compatible (representative q) j
    rcases hcompat with hsub | hdisjoint
    · exact Or.inl (hsub.trans inter_subset_left)
    · right
      rw [Set.disjoint_left]
      intro x hx hxlocus
      exact Set.disjoint_left.mp hdisjoint hx
        ⟨hxlocus, hbaseCellSub q hx⟩
  have hlocal : ∀ q,
      Nonempty
        (CharbonnelFinitePartitionedDeepLocalBandCover
          S (baseCell q) f g A) := by
    intro q
    by_cases hnonempty : (baseCell q).carrier.Nonempty
    · by_cases hopen : IsOpen (baseCell q).carrier
      · have hcardinalityCompatible : ∀ j, j ≤ N →
            (baseCell q).carrier ⊆
                closure (wilkieSection4FiberCardinalityLocus
                  base.carrier A j) ∨
              Disjoint (baseCell q).carrier
                (closure (wilkieSection4FiberCardinalityLocus
                  base.carrier A j)) := by
          intro j hj
          simpa [loci, wilkieSection4LociTarget] using
            hlociCompatible q
              (Sum.inl (⟨j, by omega⟩ : Fin (N + 1)))
        have hencard : ∀ x ∈ (baseCell q).carrier,
            (maxwellScalarFiber A x).encard < (N : ℕ∞) :=
          maxwellScalarFiber_encard_lt_cutoff_of_open_compatible_locus_deep
            hopen hnonempty (hbaseCellSub q) hNempty
              (hcardinalityCompatible N le_rfl)
        have hcollisionCompatible :
            (baseCell q).carrier ⊆
                wilkieSection4CollisionLocus base.carrier A ∨
              Disjoint (baseCell q).carrier
                (wilkieSection4CollisionLocus base.carrier A) := by
          simpa [loci, wilkieSection4LociTarget] using
            hlociCompatible q (Sum.inr (0 : Fin 3))
        have hlowerCompatible :
            (baseCell q).carrier ⊆
                wilkieSection4LowerEndpointLocus base.carrier A f ∨
              Disjoint (baseCell q).carrier
                (wilkieSection4LowerEndpointLocus base.carrier A f) := by
          simpa [loci, wilkieSection4LociTarget] using
            hlociCompatible q (Sum.inr (1 : Fin 3))
        have hupperCompatible :
            (baseCell q).carrier ⊆
                wilkieSection4UpperEndpointLocus base.carrier A g ∨
              Disjoint (baseCell q).carrier
                (wilkieSection4UpperEndpointLocus base.carrier A g) := by
          simpa [loci, wilkieSection4LociTarget] using
            hlociCompatible q (Sum.inr (2 : Fin 3))
        obtain ⟨hcollisionLocus, hlowerLocus, hupperLocus⟩ :=
          disjoint_wilkieSection4_badLoci_of_uniform_cardinality_of_compatible
            hweak h22 hp hopen hnonempty
              (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using
                ((baseCell q).toCell hweak).carrier_mem)
              (hbaseCellSub q) hAmem hfGraph hgGraph hencard
              hcollisionCompatible hlowerCompatible hupperCompatible
        have hescape : MaxwellScalarFiberNoEscape (baseCell q).carrier A :=
          maxwellScalarFiberNoEscape_of_relativelyClosedBand_of_disjoint_endpointLoci
            (hbaseCellSub q) hAsub hAclosed hf hg hlowerLocus hupperLocus
        have hcollision : MaxwellScalarFiberNoCollision
            (baseCell q).carrier A :=
          maxwellScalarFiberNoCollision_of_disjoint_collisionLocus
            (hbaseCellSub q) hcollisionLocus
        obtain ⟨r, _hrN, hfiber⟩ :=
          exists_exact_maxwellScalarFiber_cardinality_of_open_compatible_loci
            hN hopen hnonempty (hbaseCellSub q) hNempty
              hcardinalityCompatible hescape hcollision
        exact
          exists_charbonnelFinitePartitionedDeepLocalBandCover_of_exactFibers
            hweak hp base (baseCell q) (hbaseCellSub q) f g hf hg hfg
              hfGraph hgGraph hAsub hAmem hfiber hescape hcollision
      · exact hnonopen (baseCell q) (hbaseCellSub q)
          (hbaseCellBounded q) hopen
    · have hfiber : ∀ x ∈ (baseCell q).carrier,
          (maxwellScalarFiber A x).Finite ∧
            (maxwellScalarFiber A x).ncard = 0 := by
        intro x hx
        exact (hnonempty ⟨x, hx⟩).elim
      have hescape : MaxwellScalarFiberNoEscape (baseCell q).carrier A := by
        intro x hx
        exact (hnonempty ⟨x, hx⟩).elim
      have hcollision : MaxwellScalarFiberNoCollision
          (baseCell q).carrier A := by
        intro x hx
        exact (hnonempty ⟨x, hx⟩).elim
      exact
        exists_charbonnelFinitePartitionedDeepLocalBandCover_of_exactFibers
          hweak hp base (baseCell q) (hbaseCellSub q) f g hf hg hfg
            hfGraph hgGraph hAsub hAmem hfiber hescape hcollision
  let localCover : (q : BaseIndex) →
      CharbonnelFinitePartitionedDeepLocalBandCover
        S (baseCell q) f g A :=
    fun q ↦ Classical.choice (hlocal q)
  letI : ∀ q, Finite (localCover q).Index :=
    fun q ↦ (localCover q).indexFinite
  let Index := Σ q : BaseIndex, (localCover q).Index
  let cell : Index → CharbonnelDeepEnrichedCell S ((m + 1) + 1) :=
    fun i ↦ (localCover i.1).cell i.2
  have hrepresentativeCarrier : ∀ i : fine.Index,
      (baseCell (Quotient.mk carrierSetoid i)).carrier =
        (fine.cell i).carrier := by
    intro i
    have hq : Quotient.mk carrierSetoid
          (representative (Quotient.mk carrierSetoid i)) =
        Quotient.mk carrierSetoid i :=
      Quotient.out_eq (Quotient.mk carrierSetoid i)
    exact Quotient.exact hq
  refine ⟨
    { Index := Index
      indexFinite := inferInstance
      cell := cell
      contained := ?_
      covers := ?_
      compatible := ?_
      cells_eq_or_disjoint := ?_
      hereditary_projection_coherent := ?_ }⟩
  · rintro ⟨q, i⟩ z hz
    have hzLocal := (localCover q).contained i hz
    exact ⟨hbaseCellSub q hzLocal.1, hzLocal.2⟩
  · intro z hz
    obtain ⟨i, hxi⟩ := fine.covers (realEuclideanTakeLeft z) hz.1
    let q : BaseIndex := Quotient.mk carrierSetoid i
    have hxq : realEuclideanTakeLeft z ∈ (baseCell q).carrier := by
      rw [hrepresentativeCarrier i]
      exact hxi
    have hzLocal : z ∈ charbonnelOpenBand (baseCell q).carrier f g :=
      ⟨hxq, hz.2⟩
    obtain ⟨j, hzj⟩ := (localCover q).covers z hzLocal
    exact ⟨⟨q, j⟩, hzj⟩
  · rintro ⟨q, i⟩ _
    exact (localCover q).compatible i
  · rintro ⟨q, i⟩ ⟨r, j⟩
    change ((localCover q).cell i).carrier = ((localCover r).cell j).carrier ∨
      Disjoint ((localCover q).cell i).carrier ((localCover r).cell j).carrier
    by_cases hqr : q = r
    · subst r
      exact (localCover q).cells_eq_or_disjoint i j
    · have hbaseDisjoint :
          Disjoint (baseCell q).carrier (baseCell r).carrier := by
        rcases fine.cells_eq_or_disjoint
            (representative q) (representative r) with heq | hdisjoint
        · have hquot : q = r := by
            calc
              q = Quotient.mk carrierSetoid (representative q) :=
                (Quotient.out_eq q).symm
              _ = Quotient.mk carrierSetoid (representative r) :=
                Quotient.sound heq
              _ = r := Quotient.out_eq r
          exact False.elim (hqr hquot)
        · exact hdisjoint
      right
      rw [Set.disjoint_left]
      intro z hzi hzj
      exact Set.disjoint_left.mp hbaseDisjoint
        ((localCover q).contained i hzi).1
        ((localCover r).contained j hzj).1
  · change
      (∀ i j,
        ((cell i).projectedBase hp).carrier =
            ((cell j).projectedBase hp).carrier ∨
          Disjoint ((cell i).projectedBase hp).carrier
            ((cell j).projectedBase hp).carrier) ∧
      CharbonnelDeepCellFamilyProjectionCoherent m
        (fun i ↦ (cell i).projectedBase hp)
    constructor
    · intro i j
      simpa only [cell, (localCover i.1).projectedBase_eq i.2,
        (localCover j.1).projectedBase_eq j.2] using
        fine.cells_eq_or_disjoint
          (representative i.1) (representative j.1)
    · have hcoherent := deepOpenBandProjectionCoherent_comp
          fine.hereditary_projection_coherent
          (fun i : Index ↦ representative i.1)
      simpa only [cell, (localCover _).projectedBase_eq] using hcoherent

end AbelFormalization
