import AbelFormalization.CharbonnelSection5AnalyticReduction
import Mathlib.Topology.TietzeExtension

/-!
# Stable-component graph extraction for Charbonnel section 5.7

This file isolates the topological passage from the stable vertical intervals
of section 5.3 to the finite continuous graphs used in section 5.7.

Stability alone is not enough: one connected component of a vertical image
can contain several points of one vertical fibre.  The exact additional input
used below is the local cardinal inequality saying that an inner fibre has at
most as many points as there are stable components.  Compactness first shows
that every stable component meets every inner fibre.  The cardinal inequality
then makes each such meeting unique.  A compact closed-graph argument gives a
continuous branch in every component.

For a bounded relatively closed set in the positive half-space, the compact
set to which the argument applies is `closure S`.  Its zero branch is removed
at the end, using relative closedness, to recover finite continuous graphs for
`S` itself.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Compact labelled relations -/

/-- The part of `S` above `B` whose last coordinate lies in one fixed label. -/
def charbonnelVerticalLabelSlice {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) (B : Set (RealEuclidean n))
    (I : Set ℝ) : Set (RealEuclidean (n + 1)) :=
  S ∩ (charbonnelVerticalBaseCoordinate ⁻¹' B ∩
    charbonnelVerticalLastCoordinate ⁻¹' I)

/-- A finite continuous vertical-graph description whose `i`th graph stays
inside the prescribed label `I i`. -/
def CharbonnelFiniteContinuousVerticalGraphsAlong {n M : ℕ}
    (S : Set (RealEuclidean (n + 1))) (B : Set (RealEuclidean n))
    (I : Fin M → Set ℝ) : Prop :=
  ∃ f : Fin M → RealEuclidean n → ℝ,
    (∀ i, ContinuousOn (f i) B) ∧
    (∀ x ∈ B, charbonnelVerticalFiber S x = Set.range fun i ↦ f i x) ∧
    (∀ x ∈ B, (Set.univ : Set (Fin M)).Pairwise
      fun i j ↦ f i x ≠ f j x) ∧
    (∀ x ∈ B, ∀ i, f i x ∈ I i)

theorem CharbonnelFiniteContinuousVerticalGraphsAlong.toFiniteContinuousVerticalGraphsOn
    {n M : ℕ} {S : Set (RealEuclidean (n + 1))}
    {B : Set (RealEuclidean n)} {I : Fin M → Set ℝ}
    (h : CharbonnelFiniteContinuousVerticalGraphsAlong S B I) :
    CharbonnelFiniteContinuousVerticalGraphsOn S B := by
  obtain ⟨f, hcontinuous, hfiber, hpairwise, _hlabel⟩ := h
  exact ⟨M, f, hcontinuous, hfiber, hpairwise⟩

/-- A compact relation, cut into finitely many closed disjoint labels, is a
finite union of continuous graphs as soon as every labelled fibre is a
singleton and the labels cover every fibre.  The proof uses the projection
from each compact labelled slice as a compact-to-Hausdorff homeomorphism and
extends its last-coordinate inverse off the closed base by Tietze. -/
theorem charbonnelFiniteContinuousVerticalGraphsAlong_of_compact_closedLabels
    {n M : ℕ} {S : Set (RealEuclidean (n + 1))}
    {B : Set (RealEuclidean n)} {I : Fin M → Set ℝ}
    (hScompact : IsCompact S) (hBclosed : IsClosed B)
    (hIclosed : ∀ i, IsClosed (I i))
    (hIdisjoint : (Set.univ : Set (Fin M)).PairwiseDisjoint I)
    (hexact : ∀ x ∈ B, ∀ i, ∃! t : ℝ,
      t ∈ charbonnelVerticalFiber S x ∧ t ∈ I i)
    (hcover : ∀ x ∈ B, ∀ t ∈ charbonnelVerticalFiber S x,
      ∃ i, t ∈ I i) :
    CharbonnelFiniteContinuousVerticalGraphsAlong S B I := by
  classical
  have hsliceCompact : ∀ i, IsCompact
      (charbonnelVerticalLabelSlice S B (I i)) := by
    intro i
    exact hScompact.inter_right
      ((hBclosed.preimage continuous_charbonnelVerticalBaseCoordinate).inter
        ((hIclosed i).preimage continuous_charbonnelVerticalLastCoordinate))
  have hbranch : ∀ i : Fin M,
      ∃ f : C(RealEuclidean n, ℝ),
        ∀ x ∈ B,
          f x ∈ charbonnelVerticalFiber S x ∧ f x ∈ I i := by
    intro i
    let T : Set (RealEuclidean (n + 1)) :=
      charbonnelVerticalLabelSlice S B (I i)
    let baseMap : T → B := fun z ↦
      ⟨charbonnelVerticalBaseCoordinate z,
        z.property.2.1⟩
    have hbaseContinuous : Continuous baseMap := by
      apply Continuous.subtype_mk
      exact continuous_charbonnelVerticalBaseCoordinate.comp
        continuous_subtype_val
    have hbaseBijective : Function.Bijective baseMap := by
      constructor
      · intro z w hzw
        have hbase : charbonnelVerticalBaseCoordinate (z : RealEuclidean (n + 1)) =
            charbonnelVerticalBaseCoordinate (w : RealEuclidean (n + 1)) :=
          congrArg Subtype.val hzw
        let x : RealEuclidean n :=
          charbonnelVerticalBaseCoordinate (z : RealEuclidean (n + 1))
        have hxB : x ∈ B := z.property.2.1
        have hzFiber : charbonnelVerticalLastCoordinate
            (z : RealEuclidean (n + 1)) ∈ charbonnelVerticalFiber S x := by
          change charbonnelAppendLastCoordinate x
              (charbonnelVerticalLastCoordinate
                (z : RealEuclidean (n + 1))) ∈ S
          simpa only [x, charbonnelVerticalBaseCoordinate,
            charbonnelVerticalLastCoordinate,
            charbonnelAppendLastCoordinate_takeLeft_last] using z.property.1
        have hwFiber : charbonnelVerticalLastCoordinate
            (w : RealEuclidean (n + 1)) ∈ charbonnelVerticalFiber S x := by
          change charbonnelAppendLastCoordinate x
              (charbonnelVerticalLastCoordinate
                (w : RealEuclidean (n + 1))) ∈ S
          have hwS := w.property.1
          rw [show x = charbonnelVerticalBaseCoordinate
              (w : RealEuclidean (n + 1)) from hbase] at *
          simpa only [charbonnelVerticalBaseCoordinate,
            charbonnelVerticalLastCoordinate,
            charbonnelAppendLastCoordinate_takeLeft_last] using hwS
        have hlast : charbonnelVerticalLastCoordinate
            (z : RealEuclidean (n + 1)) =
            charbonnelVerticalLastCoordinate (w : RealEuclidean (n + 1)) :=
          (hexact x hxB i).unique
            ⟨hzFiber, z.property.2.2⟩
            ⟨hwFiber, w.property.2.2⟩
        apply Subtype.ext
        calc
          (z : RealEuclidean (n + 1)) =
              charbonnelAppendLastCoordinate
                (charbonnelVerticalBaseCoordinate
                  (z : RealEuclidean (n + 1)))
                (charbonnelVerticalLastCoordinate
                  (z : RealEuclidean (n + 1))) := by
            symm
            exact charbonnelAppendLastCoordinate_takeLeft_last
              (z : RealEuclidean (n + 1))
          _ = charbonnelAppendLastCoordinate
                (charbonnelVerticalBaseCoordinate
                  (w : RealEuclidean (n + 1)))
                (charbonnelVerticalLastCoordinate
                  (w : RealEuclidean (n + 1))) := by
            rw [hbase, hlast]
          _ = (w : RealEuclidean (n + 1)) :=
            charbonnelAppendLastCoordinate_takeLeft_last
              (w : RealEuclidean (n + 1))
      · intro x
        obtain ⟨t, ht, _htUnique⟩ := hexact x x.property i
        let z : RealEuclidean (n + 1) :=
          charbonnelAppendLastCoordinate x t
        have hzBase : charbonnelVerticalBaseCoordinate z = x := by
          simp [z, charbonnelVerticalBaseCoordinate,
            charbonnelAppendLastCoordinate]
        have hzLast : charbonnelVerticalLastCoordinate z = t := by
          simp [z, charbonnelVerticalLastCoordinate]
        refine ⟨⟨z, ?_⟩, ?_⟩
        · refine ⟨ht.1, ?_, ?_⟩
          · change charbonnelVerticalBaseCoordinate z ∈ B
            rw [hzBase]
            exact x.property
          · change charbonnelVerticalLastCoordinate z ∈ I i
            rw [hzLast]
            exact ht.2
        · apply Subtype.ext
          exact hzBase
    letI : CompactSpace T :=
      isCompact_iff_compactSpace.mp (hsliceCompact i)
    let e : T ≃ B := Equiv.ofBijective baseMap hbaseBijective
    have heContinuous : Continuous e := hbaseContinuous
    let h : T ≃ₜ B :=
      e.toHomeomorphOfContinuousClosed heContinuous
        heContinuous.isClosedMap
    let g : B → ℝ := fun x ↦
      charbonnelVerticalLastCoordinate (h.symm x : RealEuclidean (n + 1))
    have hgContinuous : Continuous g :=
      continuous_charbonnelVerticalLastCoordinate.comp
        (continuous_subtype_val.comp h.symm.continuous)
    let gMap : C(B, ℝ) := ⟨g, hgContinuous⟩
    obtain ⟨f, hf⟩ := gMap.exists_restrict_eq hBclosed
    refine ⟨f, ?_⟩
    intro x hxB
    let xb : B := ⟨x, hxB⟩
    let z : T := h.symm xb
    have hzBase : charbonnelVerticalBaseCoordinate
        (z : RealEuclidean (n + 1)) = x := by
      have happly : h z = xb := h.apply_symm_apply xb
      exact congrArg Subtype.val happly
    have hfEq : f x = charbonnelVerticalLastCoordinate
        (z : RealEuclidean (n + 1)) := by
      have hfOn := DFunLike.congr_fun hf xb
      change f x = g xb at hfOn
      exact hfOn
    constructor
    · change charbonnelAppendLastCoordinate x (f x) ∈ S
      rw [hfEq, ← hzBase]
      simpa only [charbonnelVerticalBaseCoordinate,
        charbonnelVerticalLastCoordinate,
        charbonnelAppendLastCoordinate_takeLeft_last] using z.property.1
    · rw [hfEq]
      exact z.property.2.2
  choose f hf using hbranch
  refine ⟨fun i x ↦ f i x, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (f i).continuous.continuousOn
  · intro x hxB
    ext t
    constructor
    · intro ht
      obtain ⟨i, hti⟩ := hcover x hxB t ht
      have hEq := (hexact x hxB i).unique
        ⟨ht, hti⟩ (hf i x hxB)
      exact ⟨i, hEq.symm⟩
    · rintro ⟨i, rfl⟩
      exact (hf i x hxB).1
  · intro x hxB i _hi j _hj hij
    intro hEq
    have hEq' : (f i) x = (f j) x := hEq
    exact (Set.disjoint_left.mp
      (hIdisjoint (Set.mem_univ i) (Set.mem_univ j) hij))
        (hf i x hxB).2 (by
          rw [hEq']
          exact (hf j x hxB).2)
  · intro x hxB i
    exact (hf i x hxB).2

/-! ## Stable intervals meet every inner fibre -/

/-- One explicit witness for `CharbonnelStableLocalVerticalIntervalSeparation`.
Keeping the witness bundled lets later hypotheses refer to its component
count and its fixed interval labels. -/
structure CharbonnelStableLocalVerticalIntervalWitness {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) where
  count : ℕ
  center : RealEuclidean n
  radius : ℝ
  radius_pos : 0 < radius
  label : Fin count ≃ ConnectedComponents
    (charbonnelVerticalImageOver S (Metric.closedBall center radius) : Set ℝ)
  stable : ∀ (y : RealEuclidean n) (s : ℝ), 0 < s →
    ∀ hsub : Metric.closedBall y s ⊆ Metric.closedBall center radius,
      charbonnelLocalVerticalComponentCount S y s = (count : ℕ∞) ∧
      Function.Bijective
        (charbonnelVerticalComponentInclusionMap S hsub)

def CharbonnelStableLocalVerticalIntervalWitness.innerBall
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (w : CharbonnelStableLocalVerticalIntervalWitness S) :
    Set (RealEuclidean n) :=
  Metric.closedBall w.center (w.radius / 2)

def CharbonnelStableLocalVerticalIntervalWitness.interval
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (w : CharbonnelStableLocalVerticalIntervalWitness S)
    (i : Fin w.count) : Set ℝ :=
  realConnectedComponentCarrier
    (charbonnelVerticalImageOver S
      (Metric.closedBall w.center w.radius)) (w.label i)

theorem CharbonnelStableLocalVerticalIntervalSeparation.exists_witness
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (h : CharbonnelStableLocalVerticalIntervalSeparation S) :
    Nonempty (CharbonnelStableLocalVerticalIntervalWitness S) := by
  obtain ⟨M, x, r, hr, label, hstable⟩ := h
  exact ⟨⟨M, x, r, hr, label, hstable⟩⟩

/-- Compactness upgrades stable component incidence over arbitrarily small
balls to actual incidence with the limiting point fibre. -/
theorem CharbonnelStableLocalVerticalIntervalWitness.exists_mem_fiber_interval
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (w : CharbonnelStableLocalVerticalIntervalWitness S)
    (hScompact : IsCompact S)
    {y : RealEuclidean n} (hy : y ∈ w.innerBall)
    (i : Fin w.count) :
    ∃ t : ℝ, t ∈ charbonnelVerticalFiber S y ∧ t ∈ w.interval i := by
  let Radius := {s : ℝ // 0 < s ∧ s ≤ w.radius / 2}
  let K : Radius → Set (RealEuclidean (n + 1)) := fun s ↦
    charbonnelVerticalLabelSlice S (Metric.closedBall y s) (w.interval i)
  let halfRadius : Radius :=
    ⟨w.radius / 2, by constructor <;> linarith [w.radius_pos]⟩
  letI : Nonempty Radius := ⟨halfRadius⟩
  have hsub (s : Radius) :
      Metric.closedBall y (s : ℝ) ⊆
        Metric.closedBall w.center w.radius := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    have hy' : dist y w.center ≤ w.radius / 2 :=
      Metric.mem_closedBall.mp hy
    calc
      dist z w.center ≤ dist z y + dist y w.center := dist_triangle _ _ _
      _ ≤ (s : ℝ) + w.radius / 2 := add_le_add hz hy'
      _ ≤ w.radius / 2 + w.radius / 2 :=
        by linarith [s.property.2]
      _ = w.radius := by ring
  have hKnonempty : ∀ s, (K s).Nonempty := by
    intro s
    have hbijective := (w.stable y s s.property.1 (hsub s)).2
    obtain ⟨c, hc⟩ := hbijective.2 (w.label i)
    let p := connectedComponentRepresentative
      (charbonnelVerticalImageOver S (Metric.closedBall y s)) c
    have hpCarrier : (p : ℝ) ∈ realConnectedComponentCarrier
        (charbonnelVerticalImageOver S (Metric.closedBall y s)) c := by
      exact ⟨p, mem_connectedComponent, rfl⟩
    have hpInterval : (p : ℝ) ∈ w.interval i :=
      realConnectedComponentCarrier_subset_of_inclusionMap_eq
        S (hsub s) hc hpCarrier
    obtain ⟨y', hy'Ball, hy'S⟩ := p.property
    let z : RealEuclidean (n + 1) :=
      charbonnelAppendLastCoordinate y' (p : ℝ)
    refine ⟨z, ?_⟩
    refine ⟨hy'S, ?_, ?_⟩
    · change charbonnelVerticalBaseCoordinate z ∈ Metric.closedBall y s
      simpa [z, charbonnelVerticalBaseCoordinate,
        charbonnelAppendLastCoordinate] using hy'Ball
    · change charbonnelVerticalLastCoordinate z ∈ w.interval i
      simpa [z, charbonnelVerticalLastCoordinate] using hpInterval
  have hKcompact : ∀ s, IsCompact (K s) := by
    intro s
    exact hScompact.inter_right
      ((Metric.isClosed_closedBall.preimage
          continuous_charbonnelVerticalBaseCoordinate).inter
        ((realConnectedComponentCarrier_isCompact_of_isCompact
            (charbonnelVerticalImageOver_isCompact hScompact
              Metric.isClosed_closedBall) (w.label i)).isClosed.preimage
          continuous_charbonnelVerticalLastCoordinate))
  have hKclosed : ∀ s, IsClosed (K s) := fun s ↦ (hKcompact s).isClosed
  have hKdirected : Directed (· ⊇ ·) K := by
    intro a b
    let c : Radius :=
      ⟨min (a : ℝ) (b : ℝ),
        lt_min a.property.1 b.property.1,
        (min_le_left (a : ℝ) (b : ℝ)).trans a.property.2⟩
    refine ⟨c, ?_, ?_⟩
    · intro z hz
      refine ⟨hz.1, ?_, hz.2.2⟩
      exact Metric.mem_closedBall.mpr
        ((Metric.mem_closedBall.mp hz.2.1).trans
          (min_le_left (a : ℝ) (b : ℝ)))
    · intro z hz
      refine ⟨hz.1, ?_, hz.2.2⟩
      exact Metric.mem_closedBall.mpr
        ((Metric.mem_closedBall.mp hz.2.1).trans
          (min_le_right (a : ℝ) (b : ℝ)))
  obtain ⟨z, hz⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      K hKdirected hKnonempty hKcompact hKclosed
  have hzK : ∀ s, z ∈ K s := Set.mem_iInter.mp hz
  have hbase : charbonnelVerticalBaseCoordinate z = y := by
    by_contra hne
    have hdistPos : 0 < dist (charbonnelVerticalBaseCoordinate z) y :=
      dist_pos.mpr hne
    let s : Radius :=
      ⟨min (dist (charbonnelVerticalBaseCoordinate z) y / 2)
          (w.radius / 2),
        lt_min (half_pos hdistPos) (half_pos w.radius_pos),
        min_le_right _ _⟩
    have hzBall := (hzK s).2.1
    have hle : dist (charbonnelVerticalBaseCoordinate z) y ≤ (s : ℝ) :=
      Metric.mem_closedBall.mp hzBall
    have hlt : (s : ℝ) < dist (charbonnelVerticalBaseCoordinate z) y :=
      (min_le_left _ _).trans_lt (half_lt_self hdistPos)
    exact (not_lt_of_ge hle) hlt
  refine ⟨charbonnelVerticalLastCoordinate z, ?_, ?_⟩
  · change charbonnelAppendLastCoordinate y
        (charbonnelVerticalLastCoordinate z) ∈ S
    rw [← hbase]
    simpa only [charbonnelVerticalBaseCoordinate,
      charbonnelVerticalLastCoordinate,
      charbonnelAppendLastCoordinate_takeLeft_last] using (hzK halfRadius).1
  · exact (hzK halfRadius).2.2

theorem CharbonnelStableLocalVerticalIntervalWitness.interval_isCompact
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (w : CharbonnelStableLocalVerticalIntervalWitness S)
    (hScompact : IsCompact S) (i : Fin w.count) :
    IsCompact (w.interval i) := by
  exact realConnectedComponentCarrier_isCompact_of_isCompact
    (charbonnelVerticalImageOver_isCompact hScompact
      Metric.isClosed_closedBall) (w.label i)

theorem CharbonnelStableLocalVerticalIntervalWitness.intervals_pairwiseDisjoint
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (w : CharbonnelStableLocalVerticalIntervalWitness S) :
    (Set.univ : Set (Fin w.count)).PairwiseDisjoint w.interval := by
  intro i _hi j _hj hij
  exact realConnectedComponentCarriers_pairwiseDisjoint
    (charbonnelVerticalImageOver S
      (Metric.closedBall w.center w.radius))
    (Set.mem_univ (w.label i)) (Set.mem_univ (w.label j))
    (fun h ↦ hij (w.label.injective h))

theorem CharbonnelStableLocalVerticalIntervalWitness.fiber_subset_iUnion_intervals
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (w : CharbonnelStableLocalVerticalIntervalWitness S)
    {y : RealEuclidean n} (hy : y ∈ w.innerBall)
    {t : ℝ} (ht : t ∈ charbonnelVerticalFiber S y) :
    ∃ i, t ∈ w.interval i := by
  have hyLarge : y ∈ Metric.closedBall w.center w.radius := by
    change y ∈ Metric.closedBall w.center (w.radius / 2) at hy
    rw [Metric.mem_closedBall] at hy ⊢
    linarith [w.radius_pos]
  have htLarge : t ∈ charbonnelVerticalImageOver S
      (Metric.closedBall w.center w.radius) := ⟨y, hyLarge, ht⟩
  have hunion := iUnion_realConnectedComponentCarrier_equiv
    (charbonnelVerticalImageOver S
      (Metric.closedBall w.center w.radius)) w.label
  rw [← hunion] at htLarge
  exact Set.mem_iUnion.mp htLarge

/-- On an inner ball, the cardinal upper bound by the stable component count
is exactly what turns component incidence into one point per component. -/
theorem
    CharbonnelStableLocalVerticalIntervalWitness.existsUnique_mem_fiber_interval_of_encard_le
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (w : CharbonnelStableLocalVerticalIntervalWitness S)
    (hScompact : IsCompact S)
    {y : RealEuclidean n} (hy : y ∈ w.innerBall)
    (hcard : (charbonnelVerticalFiber S y).encard ≤ (w.count : ℕ∞))
    (i : Fin w.count) :
    ∃! t : ℝ, t ∈ charbonnelVerticalFiber S y ∧ t ∈ w.interval i := by
  classical
  have hexists : ∀ j : Fin w.count, ∃ t : ℝ,
      t ∈ charbonnelVerticalFiber S y ∧ t ∈ w.interval j :=
    fun j ↦ w.exists_mem_fiber_interval hScompact hy j
  choose value hvalue using hexists
  let point : Fin w.count → charbonnelVerticalFiber S y :=
    fun j ↦ ⟨value j, (hvalue j).1⟩
  have hpointInjective : Function.Injective point := by
    intro j k hjk
    by_contra hjkne
    have hvalueEq : value j = value k := congrArg Subtype.val hjk
    exact (Set.disjoint_left.mp
      (w.intervals_pairwiseDisjoint
        (Set.mem_univ j) (Set.mem_univ k) hjkne))
      (hvalue j).2 (by
        rw [hvalueEq]
        exact (hvalue k).2)
  have hfiniteData := Set.encard_le_coe_iff_finite_ncard_le.mp hcard
  letI : Finite (charbonnelVerticalFiber S y) := hfiniteData.1
  have hcardLower : w.count ≤ Nat.card (charbonnelVerticalFiber S y) := by
    simpa only [Nat.card_fin] using
      (Nat.card_le_card_of_injective point hpointInjective)
  have hcardUpper : Nat.card (charbonnelVerticalFiber S y) ≤ w.count := by
    simpa only [Nat.card_coe_set_eq] using hfiniteData.2
  have hpointBijective : Function.Bijective point := by
    apply (Nat.bijective_iff_injective_and_card point).mpr
    refine ⟨hpointInjective, ?_⟩
    simp only [Nat.card_fin]
    exact le_antisymm hcardLower hcardUpper
  refine ⟨value i, hvalue i, ?_⟩
  intro t ht
  obtain ⟨j, hj⟩ := hpointBijective.2 ⟨t, ht.1⟩
  have hvalueEq : value j = t := congrArg Subtype.val hj
  have hji : j = i := by
    by_contra hne
    exact (Set.disjoint_left.mp
      (w.intervals_pairwiseDisjoint
        (Set.mem_univ j) (Set.mem_univ i) hne))
      (hvalue j).2 (by
        rw [hvalueEq]
        exact ht.2)
  rw [← hji]
  exact hvalueEq.symm

/-- The strongest direct graph consequence of stable interval separation:
compactness plus the inner-fibre cardinal bound produces labelled continuous
branches. -/
theorem
    CharbonnelStableLocalVerticalIntervalWitness.finiteContinuousVerticalGraphsAlong_innerBall
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (w : CharbonnelStableLocalVerticalIntervalWitness S)
    (hScompact : IsCompact S)
    (hcard : ∀ y ∈ w.innerBall,
      (charbonnelVerticalFiber S y).encard ≤ (w.count : ℕ∞)) :
    CharbonnelFiniteContinuousVerticalGraphsAlong
      S w.innerBall w.interval := by
  apply charbonnelFiniteContinuousVerticalGraphsAlong_of_compact_closedLabels
    hScompact Metric.isClosed_closedBall
  · exact fun i ↦ (w.interval_isCompact hScompact i).isClosed
  · exact w.intervals_pairwiseDisjoint
  · intro y hy i
    exact w.existsUnique_mem_fiber_interval_of_encard_le
      hScompact hy (hcard y hy) i
  · intro y hy t ht
    exact w.fiber_subset_iUnion_intervals hy ht

theorem
    CharbonnelStableLocalVerticalIntervalWitness.finiteContinuousVerticalGraphsOn_innerBall
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (w : CharbonnelStableLocalVerticalIntervalWitness S)
    (hScompact : IsCompact S)
    (hcard : ∀ y ∈ w.innerBall,
      (charbonnelVerticalFiber S y).encard ≤ (w.count : ℕ∞)) :
    CharbonnelFiniteContinuousVerticalGraphsOn S w.innerBall :=
  (w.finiteContinuousVerticalGraphsAlong_innerBall hScompact hcard)
    |>.toFiniteContinuousVerticalGraphsOn

theorem
    CharbonnelStableLocalVerticalIntervalWitness.finiteVerticalGraphChartAt_center
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (w : CharbonnelStableLocalVerticalIntervalWitness S)
    (hScompact : IsCompact S)
    (hcard : ∀ y ∈ w.innerBall,
      (charbonnelVerticalFiber S y).encard ≤ (w.count : ℕ∞)) :
    CharbonnelFiniteVerticalGraphChartAt S w.center := by
  refine ⟨w.innerBall, ?_,
    w.finiteContinuousVerticalGraphsOn_innerBall hScompact hcard⟩
  exact Metric.closedBall_mem_nhds w.center (half_pos w.radius_pos)

/-! ## Removing the zero branch over a positive trace -/

/-- Relative closedness in the positive half-space says precisely that the
positive part of the ambient closure lies back in the original set. -/
theorem
    CharbonnelRelativelyClosedInPositiveLast.closure_inter_positiveLastCoordinateLocus_subset
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : CharbonnelRelativelyClosedInPositiveLast S) :
    closure S ∩ charbonnelPositiveLastCoordinateLocus n ⊆ S := by
  have hclosed := isClosed_preimage_val.mp hS.2
  intro z hz
  apply hclosed
  refine ⟨hz.2, ?_⟩
  have hinter : charbonnelPositiveLastCoordinateLocus n ∩ S = S :=
    inter_eq_right.mpr hS.1
  simpa only [hinter] using hz.1

/-- The closure of a set in the strict positive half-space is contained in
the corresponding closed half-space. -/
theorem closure_subset_nonnegativeLast_of_subset_positiveLastCoordinateLocus
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : S ⊆ charbonnelPositiveLastCoordinateLocus n) :
    closure S ⊆ {z | 0 ≤ charbonnelVerticalLastCoordinate z} := by
  apply closure_minimal
  · intro z hz
    have hzPositive := hS hz
    change 0 < charbonnelVerticalLastCoordinate z at hzPositive
    exact le_of_lt hzPositive
  · exact isClosed_le continuous_const
      continuous_charbonnelVerticalLastCoordinate

/-- If labelled continuous graphs describe `closure S` over a nonempty part
of the positive zero trace, one label is identically zero.  Removing that
label leaves continuous graphs for `S`: all remaining closure points have
positive height, and relative closedness puts them back in `S`. -/
theorem CharbonnelFiniteContinuousVerticalGraphsAlong.remove_zero_branch_of_trace
    {n M : ℕ} {S : Set (RealEuclidean (n + 1))}
    {B : Set (RealEuclidean n)} {I : Fin M → Set ℝ}
    (hrelative : CharbonnelRelativelyClosedInPositiveLast S)
    (hBne : B.Nonempty)
    (hBtrace : B ⊆ charbonnelPositiveZeroTrace S)
    (hgraphs : CharbonnelFiniteContinuousVerticalGraphsAlong
      (closure S) B I)
    (hIdisjoint : (Set.univ : Set (Fin M)).PairwiseDisjoint I) :
    CharbonnelFiniteContinuousVerticalGraphsOn S B := by
  classical
  obtain ⟨f, hcontinuous, hfiber, hpairwise, hlabel⟩ := hgraphs
  obtain ⟨x₀, hx₀B⟩ := hBne
  have hzeroFiber : ∀ x ∈ B,
      0 ∈ charbonnelVerticalFiber (closure S) x := by
    intro x hxB
    have hxTrace := hBtrace hxB
    rw [charbonnelPositiveZeroTrace_eq_zeroSection_closure
      hrelative.1] at hxTrace
    exact hxTrace
  have hzeroRange : 0 ∈ Set.range (fun i ↦ f i x₀) := by
    rw [← hfiber x₀ hx₀B]
    exact hzeroFiber x₀ hx₀B
  obtain ⟨i₀, hi₀⟩ := hzeroRange
  have hzeroBranch : ∀ x ∈ B, f i₀ x = 0 := by
    intro x hxB
    have hzeroRangeX : 0 ∈ Set.range (fun i ↦ f i x) := by
      rw [← hfiber x hxB]
      exact hzeroFiber x hxB
    obtain ⟨j, hj⟩ := hzeroRangeX
    have hi₀Label : 0 ∈ I i₀ := by
      rw [← hi₀]
      exact hlabel x₀ hx₀B i₀
    have hjLabel : 0 ∈ I j := by
      rw [← hj]
      exact hlabel x hxB j
    have hji₀ : j = i₀ := by
      by_contra hne
      exact (Set.disjoint_left.mp
        (hIdisjoint (Set.mem_univ j) (Set.mem_univ i₀) hne))
          hjLabel hi₀Label
    simpa only [hji₀] using hj
  let Index := {i : Fin M // i ≠ i₀}
  let m := Fintype.card Index
  let e : Fin m ≃ Index := (Fintype.equivFin Index).symm
  refine ⟨m, (fun j x ↦ f (e j).1 x), ?_, ?_, ?_⟩
  · intro j
    exact hcontinuous (e j).1
  · intro x hxB
    ext t
    constructor
    · intro ht
      have htClosure : t ∈ charbonnelVerticalFiber (closure S) x :=
        subset_closure ht
      rw [hfiber x hxB] at htClosure
      obtain ⟨i, hi⟩ := htClosure
      have htPositive : 0 < t := by
        have htLocus := hrelative.1 ht
        simpa [charbonnelPositiveLastCoordinateLocus,
          charbonnelVerticalFiber] using htLocus
      have hiNe : i ≠ i₀ := by
        intro hieq
        subst i
        have := hzeroBranch x hxB
        linarith
      let ii : Index := ⟨i, hiNe⟩
      refine ⟨e.symm ii, ?_⟩
      simpa only [e.apply_symm_apply, ii] using hi
    · rintro ⟨j, rfl⟩
      have hClosure : f (e j).1 x ∈
          charbonnelVerticalFiber (closure S) x := by
        rw [hfiber x hxB]
        exact Set.mem_range_self (e j).1
      have hNonnegative : 0 ≤ f (e j).1 x := by
        have hz :=
          closure_subset_nonnegativeLast_of_subset_positiveLastCoordinateLocus
            hrelative.1 hClosure
        simpa [charbonnelVerticalLastCoordinate] using hz
      have hNonzero : f (e j).1 x ≠ 0 := by
        intro hz
        have hneBranch := hpairwise x hxB
          (Set.mem_univ (e j).1) (Set.mem_univ i₀) (e j).2
        apply hneBranch
        rw [hz, hzeroBranch x hxB]
      have hPositive : 0 < f (e j).1 x :=
        lt_of_le_of_ne hNonnegative hNonzero.symm
      apply hrelative.closure_inter_positiveLastCoordinateLocus_subset
      refine ⟨hClosure, ?_⟩
      simpa [charbonnelPositiveLastCoordinateLocus,
        charbonnelVerticalFiber] using hPositive
  · intro x hxB j _hj k _hk hjk
    apply hpairwise x hxB (Set.mem_univ (e j).1)
      (Set.mem_univ (e k).1)
    intro hval
    apply hjk
    exact e.injective (Subtype.ext hval)

/-! ## A source-shaped residual for section 5.7 -/

/-- The precise local datum still needed after stable-component graph
extraction.  The stable ball lies inside the hypothetical trace interior,
and every fibre of `closure S` over its half-radius ball has at most the
stable number of points. -/
structure CharbonnelSection57StableClosureFiberBoundWitness {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) where
  stable : CharbonnelStableLocalVerticalIntervalWitness (closure S)
  innerBall_subset_traceInterior :
    stable.innerBall ⊆ interior (charbonnelPositiveZeroTrace S)
  fiber_encard_le : ∀ y ∈ stable.innerBall,
    (charbonnelVerticalFiber (closure S) y).encard ≤
      (stable.count : ℕ∞)

/-- Source-shaped formulation of the remaining local extraction in bounded
section 5.7.  All analytic assumptions are retained so later work can prove
this statement directly from the paper's hypotheses. -/
def CharbonnelSection57StableClosureFiberBoundReduction
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n → CharbonnelPPrime C n →
    ∀ S : Set (RealEuclidean (n + 1)), S ∈ C (n + 1) →
      CharbonnelRelativelyClosedInPositiveLast S →
      Bornology.IsBounded S → interior S = ∅ →
      (interior (charbonnelPositiveZeroTrace S)).Nonempty →
        Nonempty (CharbonnelSection57StableClosureFiberBoundWitness S)

/-- A stable closure witness with the local fibre-cardinality bound supplies
the full bounded graph reduction.  Compactness comes from boundedness of
`S`; the preceding theorem removes the zero graph from `closure S`. -/
theorem charbonnelSection57BoundedGraphReduction_of_stableClosureFiberBoundReduction
    {C : EuclideanSetFamily}
    (hreduction : CharbonnelSection57StableClosureFiberBoundReduction C) :
    CharbonnelSection57BoundedGraphReduction C := by
  intro n hn hPPrime S hSmem hrelative hbounded hSempty htrace
  obtain ⟨data⟩ := hreduction hn hPPrime S hSmem hrelative
    hbounded hSempty htrace
  let w := data.stable
  have hcompact : IsCompact (closure S) := hbounded.isCompact_closure
  have hclosureGraphs : CharbonnelFiniteContinuousVerticalGraphsAlong
      (closure S) w.innerBall w.interval :=
    w.finiteContinuousVerticalGraphsAlong_innerBall hcompact
      data.fiber_encard_le
  have hcenterInner : w.center ∈ w.innerBall := by
    change w.center ∈ Metric.closedBall w.center (w.radius / 2)
    rw [Metric.mem_closedBall, dist_self]
    linarith [w.radius_pos]
  have hinnerNonempty : w.innerBall.Nonempty := ⟨w.center, hcenterInner⟩
  have hgraphs : CharbonnelFiniteContinuousVerticalGraphsOn S w.innerBall :=
    hclosureGraphs.remove_zero_branch_of_trace hrelative hinnerNonempty
      (data.innerBall_subset_traceInterior.trans interior_subset)
      w.intervals_pairwiseDisjoint
  refine ⟨w.center, data.innerBall_subset_traceInterior hcenterInner,
    w.innerBall, ?_, hgraphs⟩
  exact Metric.closedBall_mem_nhds w.center (half_pos w.radius_pos)

end AbelFormalization
