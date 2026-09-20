import AbelFormalization.CharbonnelSection5VerticalIncidence
import AbelFormalization.ProjectedZeroFirstOrderBridge
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Local vertical stability in Charbonnel section 5.3(b,c)

For a compact `S ⊆ ℝ^(n+1)`, Charbonnel first obtains a uniform bound
on the connected components of

`q(S ∩ (closedBall x r × ℝ))`.

Section 5.3(b) chooses a ball at which this bound is maximal.  It labels the
components of the corresponding vertical image by intervals `Iᵢ` and records,
for each component, the set of base points whose vertical fiber meets `Iᵢ`.
The source's section 5.3(c) descends lexicographically to a relative ball
with full base support and may lower the component count.  The conditional
algebra in this file assumes the stronger property of full support at an
ambient ball attaining the *global* maximum.  Under that stronger property,
every smaller ball meets every `Iᵢ`, and maximality forces exactly one
smaller component inside each `Iᵢ`.

This file proves all of the order, cardinal, and connected-component assembly
around the stronger hypothesis.  `CharbonnelSection53FullSupportSelection`
is false in general, even for compact semialgebraic sets with full base
projection.  The corrected source-shaped relative-ball and count-lowering
descent is developed separately.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## A maximal value for a bounded `ℕ∞`-valued family -/

/-- A nonempty family of extended natural numbers bounded by a natural number
attains a largest value.  This is the elementary order step used to choose the
integer `M` in Charbonnel 5.3(b). -/
theorem exists_maximal_enat_value_of_bounded
    {α : Type*} [Nonempty α] (f : α → ℕ∞) (N : ℕ)
    (hbound : ∀ a, f a ≤ (N : ℕ∞)) :
    ∃ (M : ℕ) (a : α),
      f a = (M : ℕ∞) ∧ ∀ b, f b ≤ (M : ℕ∞) := by
  induction N with
  | zero =>
      let a : α := Classical.choice (inferInstance : Nonempty α)
      refine ⟨0, a, ?_, ?_⟩
      · exact le_antisymm (hbound a) (by simp)
      · intro b
        exact hbound b
  | succ N ih =>
      by_cases htop : ∃ a, f a = ((N + 1 : ℕ) : ℕ∞)
      · obtain ⟨a, ha⟩ := htop
        refine ⟨N + 1, a, ha, ?_⟩
        intro b
        simpa only [Nat.succ_eq_add_one] using hbound b
      · have hbound' : ∀ a, f a ≤ (N : ℕ∞) := by
          intro a
          obtain ⟨k, hfk, hk⟩ := ENat.le_natCast_iff.mp (hbound a)
          have hkne : k ≠ N + 1 := by
            intro hkEq
            apply htop
            refine ⟨a, ?_⟩
            rw [hfk, hkEq]
          rw [hfk, ENat.natCast_le_natCast]
          omega
        exact ih hbound'

/-! ## Maximal local vertical balls -/

/-- The extended-natural component count of the vertical image over one
closed ball. -/
def charbonnelLocalVerticalComponentCount {n : ℕ}
    (S : Set (RealEuclidean (n + 1)))
    (x : RealEuclidean n) (r : ℝ) : ℕ∞ :=
  ENat.card (ConnectedComponents
    (charbonnelVerticalImageOver S (Metric.closedBall x r) : Set ℝ))

/-- A positive-radius ball attains the global maximal local vertical
component count `M`. -/
def CharbonnelMaximalLocalVerticalBall {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) (M : ℕ)
    (x : RealEuclidean n) (r : ℝ) : Prop :=
  0 < r ∧
    charbonnelLocalVerticalComponentCount S x r = (M : ℕ∞) ∧
    ∀ (y : RealEuclidean n) (s : ℝ), 0 < s →
      charbonnelLocalVerticalComponentCount S y s ≤ (M : ℕ∞)

/-- The uniform bound from 5.3(a) supplies a ball attaining a globally
maximal component count. -/
theorem CharbonnelUniformLocalVerticalComponentBound.exists_maximalLocalVerticalBall
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hbound : CharbonnelUniformLocalVerticalComponentBound S) :
    ∃ (M : ℕ) (x : RealEuclidean n) (r : ℝ),
      CharbonnelMaximalLocalVerticalBall S M x r := by
  obtain ⟨N, hN⟩ := hbound
  let f : (RealEuclidean n × {r : ℝ // 0 < r}) → ℕ∞ :=
    fun p ↦ charbonnelLocalVerticalComponentCount S p.1 p.2.1
  let p₀ : RealEuclidean n × {r : ℝ // 0 < r} :=
    (0, ⟨1, zero_lt_one⟩)
  letI : Nonempty (RealEuclidean n × {r : ℝ // 0 < r}) := ⟨p₀⟩
  have hfBound : ∀ p, f p ≤ (N : ℕ∞) := by
    intro p
    exact hN p.1 p.2.1 p.2.2
  obtain ⟨M, p, hp, hmax⟩ :=
    exists_maximal_enat_value_of_bounded f N hfBound
  refine ⟨M, p.1, p.2.1, ?_⟩
  refine ⟨p.2.2, ?_, ?_⟩
  · exact hp
  · intro y s hs
    exact hmax (y, ⟨s, hs⟩)

/-! ## Component intervals and their base supports -/

/-- The visible base coordinate of a point whose final coordinate is
distinguished. -/
def charbonnelVerticalBaseCoordinate {n : ℕ}
    (z : RealEuclidean (n + 1)) : RealEuclidean n :=
  realEuclideanTakeLeft z

/-- The distinguished final coordinate. -/
def charbonnelVerticalLastCoordinate {n : ℕ}
    (z : RealEuclidean (n + 1)) : ℝ :=
  z (Fin.last n)

theorem continuous_charbonnelVerticalBaseCoordinate {n : ℕ} :
    Continuous (@charbonnelVerticalBaseCoordinate n) := by
  change Continuous (realEuclideanTakeLeftContinuousLinearMap n 1)
  exact (realEuclideanTakeLeftContinuousLinearMap n 1).continuous

theorem continuous_charbonnelVerticalLastCoordinate {n : ℕ} :
    Continuous (@charbonnelVerticalLastCoordinate n) := by
  exact continuous_apply (Fin.last n)

/-- The vertical image over `B` is the last-coordinate image of the part of
`S` whose base coordinate lies in `B`. -/
theorem charbonnelVerticalLastCoordinate_image_restriction {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) (B : Set (RealEuclidean n)) :
    charbonnelVerticalLastCoordinate ''
        (S ∩ charbonnelVerticalBaseCoordinate ⁻¹' B) =
      charbonnelVerticalImageOver S B := by
  ext t
  constructor
  · rintro ⟨z, ⟨hzS, hzB⟩, rfl⟩
    refine ⟨charbonnelVerticalBaseCoordinate z, hzB, ?_⟩
    simpa only [charbonnelVerticalBaseCoordinate,
      charbonnelVerticalLastCoordinate,
      charbonnelAppendLastCoordinate_takeLeft_last] using hzS
  · rintro ⟨x, hxB, hxt⟩
    refine ⟨charbonnelAppendLastCoordinate x t, ?_, ?_⟩
    · refine ⟨hxt, ?_⟩
      change realEuclideanTakeLeft
        (charbonnelAppendLastCoordinate x t) ∈ B
      simpa only [charbonnelAppendLastCoordinate,
        realEuclideanTakeLeft_append] using hxB
    · exact charbonnelAppendLastCoordinate_last x t

/-- Compactness of `S` makes its vertical image over every closed base set
compact. -/
theorem charbonnelVerticalImageOver_isCompact {n : ℕ}
    {S : Set (RealEuclidean (n + 1))} (hS : IsCompact S)
    {B : Set (RealEuclidean n)} (hB : IsClosed B) :
    IsCompact (charbonnelVerticalImageOver S B) := by
  rw [← charbonnelVerticalLastCoordinate_image_restriction S B]
  exact (hS.inter_right
      (hB.preimage continuous_charbonnelVerticalBaseCoordinate)).image
    continuous_charbonnelVerticalLastCoordinate

/-- In particular, the local vertical image over a closed ball is compact. -/
theorem charbonnelLocalVerticalImage_isCompact {n : ℕ}
    {S : Set (RealEuclidean (n + 1))} (hS : IsCompact S)
    (x : RealEuclidean n) (r : ℝ) :
    IsCompact (charbonnelVerticalImageOver S (Metric.closedBall x r)) :=
  charbonnelVerticalImageOver_isCompact hS Metric.isClosed_closedBall

/-- A connected-component carrier of a compact real set is compact. -/
theorem realConnectedComponentCarrier_isCompact_of_isCompact
    {s : Set ℝ} (hs : IsCompact s) (c : ConnectedComponents s) :
    IsCompact (realConnectedComponentCarrier s c) := by
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

/-- The base points in `B` whose vertical fiber meets one fixed connected
component of the vertical image over `B`.  This is Charbonnel's set
`A_{i,x,ε}` when the component is the interval `I_{i,x,ε}`. -/
def charbonnelVerticalComponentBaseSupport {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) (B : Set (RealEuclidean n))
    (c : ConnectedComponents
      (charbonnelVerticalImageOver S B : Set ℝ)) :
    Set (RealEuclidean n) :=
  {x | x ∈ B ∧
    ∃ t ∈ realConnectedComponentCarrier
        (charbonnelVerticalImageOver S B) c,
      charbonnelAppendLastCoordinate x t ∈ S}

theorem charbonnelVerticalComponentBaseSupport_subset {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) (B : Set (RealEuclidean n))
    (c : ConnectedComponents
      (charbonnelVerticalImageOver S B : Set ℝ)) :
    charbonnelVerticalComponentBaseSupport S B c ⊆ B := by
  intro x hx
  exact hx.1

/-- A real connected-component carrier is order-convex, hence is an
interval in the precise order-topological sense used in 5.3(b). -/
theorem realConnectedComponentCarrier_ordConnected
    (s : Set ℝ) (c : ConnectedComponents s) :
    OrdConnected (realConnectedComponentCarrier s c) :=
  (isConnected_realConnectedComponentCarrier s c).isPreconnected.ordConnected

/-- Distinct connected components of a real set have disjoint carriers. -/
theorem realConnectedComponentCarriers_pairwiseDisjoint (s : Set ℝ) :
    (Set.univ : Set (ConnectedComponents s)).PairwiseDisjoint
      (realConnectedComponentCarrier s) := by
  intro c _hc d _hd hcd
  change Disjoint (realConnectedComponentCarrier s c)
    (realConnectedComponentCarrier s d)
  rw [Set.disjoint_left]
  intro t htc htd
  obtain ⟨p, hp, hpt⟩ := htc
  obtain ⟨q, hq, hqt⟩ := htd
  have hpc : (p : ConnectedComponents s) = c :=
    (ConnectedComponents.coe_eq_coe'.mpr hp).trans
      (connectedComponentRepresentative_mk s c)
  have hqd : (q : ConnectedComponents s) = d :=
    (ConnectedComponents.coe_eq_coe'.mpr hq).trans
      (connectedComponentRepresentative_mk s d)
  have hpq : p = q := by
    apply Subtype.ext
    exact hpt.trans hqt.symm
  apply hcd
  exact hpc.symm.trans
    ((congrArg (fun z : s ↦ (z : ConnectedComponents s)) hpq).trans hqd)

/-- Reindexing all connected components by an equivalence preserves their
cover of the original real set. -/
theorem iUnion_realConnectedComponentCarrier_equiv
    {I : Type*} (s : Set ℝ) (e : I ≃ ConnectedComponents s) :
    ⋃ i : I, realConnectedComponentCarrier s (e i) = s := by
  ext t
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    rw [← iUnion_realConnectedComponentCarrier s]
    exact Set.mem_iUnion.mpr ⟨e i, hi⟩
  · intro ht
    have ht' : t ∈ ⋃ c : ConnectedComponents s,
        realConnectedComponentCarrier s c := by
      rw [iUnion_realConnectedComponentCarrier s]
      exact ht
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp ht'
    exact ⟨e.symm c, by simpa using hc⟩

/-- An exact finite extended-cardinal count enumerates all connected
components by `Fin M`. -/
theorem exists_fin_equiv_connectedComponents_of_enatCard_eq
    {X : Type*} [TopologicalSpace X] {M : ℕ}
    (hcard : ENat.card (ConnectedComponents X) = (M : ℕ∞)) :
    Nonempty (Fin M ≃ ConnectedComponents X) := by
  letI : Finite (ConnectedComponents X) :=
    ENat.card_lt_top.mp (hcard.trans_lt (by simp))
  letI : Fintype (ConnectedComponents X) :=
    Fintype.ofFinite (ConnectedComponents X)
  have hcardNat : Fintype.card (ConnectedComponents X) = M := by
    simpa only [ENat.card_eq_coe_fintype_card, ENat.natCast_inj] using hcard
  let e : Fin M ≃ ConnectedComponents X :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_fin, hcardNat])
  exact ⟨e⟩

/-! ## Inclusion of vertical images and the unique component in each interval -/

theorem charbonnelVerticalImageOver_mono {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) {B C : Set (RealEuclidean n)}
    (hBC : B ⊆ C) :
    charbonnelVerticalImageOver S B ⊆ charbonnelVerticalImageOver S C := by
  rintro t ⟨x, hxB, hxt⟩
  exact ⟨x, hBC hxB, hxt⟩

/-- Inclusion of two vertical-image subtypes. -/
def charbonnelVerticalImageInclusion {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) {B C : Set (RealEuclidean n)}
    (hBC : B ⊆ C) :
    charbonnelVerticalImageOver S B → charbonnelVerticalImageOver S C :=
  fun t ↦ ⟨t.1, charbonnelVerticalImageOver_mono S hBC t.2⟩

theorem continuous_charbonnelVerticalImageInclusion {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) {B C : Set (RealEuclidean n)}
    (hBC : B ⊆ C) :
    Continuous (charbonnelVerticalImageInclusion S hBC) := by
  exact continuous_subtype_val.subtype_mk
    (fun t ↦ charbonnelVerticalImageOver_mono S hBC t.2)

/-- The map on connected components induced by inclusion of base sets. -/
def charbonnelVerticalComponentInclusionMap {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) {B C : Set (RealEuclidean n)}
    (hBC : B ⊆ C) :
    ConnectedComponents (charbonnelVerticalImageOver S B : Set ℝ) →
      ConnectedComponents (charbonnelVerticalImageOver S C : Set ℝ) :=
  (continuous_charbonnelVerticalImageInclusion S hBC).connectedComponentsMap

@[simp]
theorem charbonnelVerticalComponentInclusionMap_mk {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) {B C : Set (RealEuclidean n)}
    (hBC : B ⊆ C)
    (t : charbonnelVerticalImageOver S B) :
    charbonnelVerticalComponentInclusionMap S hBC
        (ConnectedComponents.mk t) =
      ConnectedComponents.mk (charbonnelVerticalImageInclusion S hBC t) := by
  rfl

/-- If every component over `C` has full base support, every nonempty
sub-base `B ⊆ C` meets every one of those components.  Equivalently, the
inclusion-induced map on components is surjective. -/
theorem surjective_charbonnelVerticalComponentInclusionMap_of_fullSupport
    {n : ℕ} (S : Set (RealEuclidean (n + 1)))
    {B C : Set (RealEuclidean n)} (hBC : B ⊆ C)
    (hB : B.Nonempty)
    (hfull : ∀ c : ConnectedComponents
        (charbonnelVerticalImageOver S C : Set ℝ),
      charbonnelVerticalComponentBaseSupport S C c = C) :
    Function.Surjective
      (charbonnelVerticalComponentInclusionMap S hBC) := by
  intro c
  obtain ⟨x, hxB⟩ := hB
  have hxSupport : x ∈ charbonnelVerticalComponentBaseSupport S C c := by
    rw [hfull c]
    exact hBC hxB
  obtain ⟨_hxC, t, htComponent, htS⟩ := hxSupport
  have htB : t ∈ charbonnelVerticalImageOver S B :=
    ⟨x, hxB, htS⟩
  let z : charbonnelVerticalImageOver S B := ⟨t, htB⟩
  refine ⟨ConnectedComponents.mk z, ?_⟩
  rw [charbonnelVerticalComponentInclusionMap_mk]
  obtain ⟨p, hp, hpt⟩ := htComponent
  have hzP : charbonnelVerticalImageInclusion S hBC z = p := by
    apply Subtype.ext
    exact hpt.symm
  calc
    ConnectedComponents.mk (charbonnelVerticalImageInclusion S hBC z) =
        ConnectedComponents.mk p := congrArg ConnectedComponents.mk hzP
    _ = ConnectedComponents.mk
          (connectedComponentRepresentative
            (charbonnelVerticalImageOver S C) c) :=
      ConnectedComponents.coe_eq_coe'.mpr hp
    _ = c := connectedComponentRepresentative_mk
      (charbonnelVerticalImageOver S C) c

/-- Surjectivity on components gives the lower cardinal bound for every
nonempty sub-base. -/
theorem enatCard_verticalComponents_le_of_fullSupport
    {n : ℕ} (S : Set (RealEuclidean (n + 1)))
    {B C : Set (RealEuclidean n)} (hBC : B ⊆ C)
    (hB : B.Nonempty)
    (hfull : ∀ c : ConnectedComponents
        (charbonnelVerticalImageOver S C : Set ℝ),
      charbonnelVerticalComponentBaseSupport S C c = C) :
    ENat.card (ConnectedComponents
        (charbonnelVerticalImageOver S C : Set ℝ)) ≤
      ENat.card (ConnectedComponents
        (charbonnelVerticalImageOver S B : Set ℝ)) := by
  exact ENat.card_le_card_of_injective
    (Function.injective_surjInv
      (surjective_charbonnelVerticalComponentInclusionMap_of_fullSupport
        S hBC hB hfull))

/-- A component of the smaller vertical image is contained in the carrier
of the component to which the inclusion map sends it. -/
theorem realConnectedComponentCarrier_subset_of_inclusionMap_eq
    {n : ℕ} (S : Set (RealEuclidean (n + 1)))
    {B C : Set (RealEuclidean n)} (hBC : B ⊆ C)
    {small : ConnectedComponents
      (charbonnelVerticalImageOver S B : Set ℝ)}
    {large : ConnectedComponents
      (charbonnelVerticalImageOver S C : Set ℝ)}
    (hmap : charbonnelVerticalComponentInclusionMap S hBC small = large) :
    realConnectedComponentCarrier (charbonnelVerticalImageOver S B) small ⊆
      realConnectedComponentCarrier (charbonnelVerticalImageOver S C) large := by
  intro t ht
  obtain ⟨p, hp, hpt⟩ := ht
  let repSmall := connectedComponentRepresentative
    (charbonnelVerticalImageOver S B) small
  let repLarge := connectedComponentRepresentative
    (charbonnelVerticalImageOver S C) large
  have hpImage :
      charbonnelVerticalImageInclusion S hBC p ∈
        connectedComponent
          (charbonnelVerticalImageInclusion S hBC repSmall) := by
    exact
      (continuous_charbonnelVerticalImageInclusion S hBC).image_connectedComponent_subset
        repSmall ⟨p, hp, rfl⟩
  have hcomponent :
      (charbonnelVerticalImageInclusion S hBC repSmall :
          ConnectedComponents (charbonnelVerticalImageOver S C : Set ℝ)) =
        large := by
    calc
      (charbonnelVerticalImageInclusion S hBC repSmall :
          ConnectedComponents (charbonnelVerticalImageOver S C : Set ℝ)) =
          charbonnelVerticalComponentInclusionMap S hBC
            (repSmall : ConnectedComponents
              (charbonnelVerticalImageOver S B : Set ℝ)) := by
        symm
        exact charbonnelVerticalComponentInclusionMap_mk S hBC repSmall
      _ = charbonnelVerticalComponentInclusionMap S hBC small := by
        rw [connectedComponentRepresentative_mk]
      _ = large := hmap
  have hcomponentEq :
      connectedComponent (charbonnelVerticalImageInclusion S hBC repSmall) =
        connectedComponent repLarge := by
    apply ConnectedComponents.coe_eq_coe.mp
    exact hcomponent.trans
      (connectedComponentRepresentative_mk
        (charbonnelVerticalImageOver S C) large).symm
  refine ⟨charbonnelVerticalImageInclusion S hBC p, ?_, ?_⟩
  · rwa [← hcomponentEq]
  · exact hpt

/-! ## The exact residual of the `(M,δ)` descent -/

/-- A ball attaining the global maximal component count on which every
vertical component has the whole ball as its base support.  The full-support
condition is the paper's zero-defect condition, but a zero-defect ball need
not attain the *global* maximum. -/
def CharbonnelFullSupportMaximalVerticalBall {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) (M : ℕ)
    (x : RealEuclidean n) (r : ℝ) : Prop :=
  CharbonnelMaximalLocalVerticalBall S M x r ∧
    ∀ c : ConnectedComponents
        (charbonnelVerticalImageOver S (Metric.closedBall x r) : Set ℝ),
      charbonnelVerticalComponentBaseSupport S (Metric.closedBall x r) c =
        Metric.closedBall x r

/-- A strong selection property used by the conditional stability algebra
below.  It is **false in general**, even for compact semialgebraic sets with
full compact base projection: an isolated vertical spike can create a global
maximum whose extra component has singleton base support.  Charbonnel 5.3(c)
may descend to a smaller component count; its corrected selection remains
to be formalized. -/
def CharbonnelSection53FullSupportSelection {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ∀ M : ℕ,
    (∃ (x : RealEuclidean n) (r : ℝ),
      CharbonnelMaximalLocalVerticalBall S M x r) →
    ∃ (x : RealEuclidean n) (r : ℝ),
      CharbonnelFullSupportMaximalVerticalBall S M x r

/-- Full support supplies the lower bound while maximality supplies the
upper bound, so every contained positive-radius ball has exactly `M`
vertical components. -/
theorem CharbonnelFullSupportMaximalVerticalBall.componentCount_eq
    {n : ℕ} {S : Set (RealEuclidean (n + 1))} {M : ℕ}
    {x : RealEuclidean n} {r : ℝ}
    (hfull : CharbonnelFullSupportMaximalVerticalBall S M x r)
    (y : RealEuclidean n) (s : ℝ) (hs : 0 < s)
    (hsub : Metric.closedBall y s ⊆ Metric.closedBall x r) :
    charbonnelLocalVerticalComponentCount S y s = (M : ℕ∞) := by
  apply le_antisymm
  · exact hfull.1.2.2 y s hs
  · rw [← hfull.1.2.1]
    exact enatCard_verticalComponents_le_of_fullSupport S hsub
      ⟨y, Metric.mem_closedBall_self hs.le⟩ hfull.2

/-- On every contained positive-radius ball, the component inclusion map is
bijective.  This is the exact form of "each interval `Iᵢ` contains one and
only one component". -/
theorem CharbonnelFullSupportMaximalVerticalBall.componentInclusion_bijective
    {n : ℕ} {S : Set (RealEuclidean (n + 1))} {M : ℕ}
    {x : RealEuclidean n} {r : ℝ}
    (hfull : CharbonnelFullSupportMaximalVerticalBall S M x r)
    (y : RealEuclidean n) (s : ℝ) (hs : 0 < s)
    (hsub : Metric.closedBall y s ⊆ Metric.closedBall x r) :
    Function.Bijective
      (charbonnelVerticalComponentInclusionMap S hsub) := by
  have hsurjective :=
    surjective_charbonnelVerticalComponentInclusionMap_of_fullSupport
      S hsub ⟨y, Metric.mem_closedBall_self hs.le⟩ hfull.2
  have hsmallCount :
      ENat.card (ConnectedComponents
          (charbonnelVerticalImageOver S (Metric.closedBall y s) : Set ℝ)) =
        (M : ℕ∞) :=
    hfull.componentCount_eq y s hs hsub
  have hlargeCount :
      ENat.card (ConnectedComponents
          (charbonnelVerticalImageOver S (Metric.closedBall x r) : Set ℝ)) =
        (M : ℕ∞) :=
    hfull.1.2.1
  letI : Finite (ConnectedComponents
      (charbonnelVerticalImageOver S (Metric.closedBall y s) : Set ℝ)) :=
    ENat.card_lt_top.mp (hsmallCount.trans_lt (by simp))
  letI : Finite (ConnectedComponents
      (charbonnelVerticalImageOver S (Metric.closedBall x r) : Set ℝ)) :=
    ENat.card_lt_top.mp (hlargeCount.trans_lt (by simp))
  apply (Nat.bijective_iff_surjective_and_card _).2
  refine ⟨hsurjective, ?_⟩
  have hcard := congrArg ENat.toNat
    (hsmallCount.trans hlargeCount.symm)
  simpa only [ENat.card_eq_coe_natCard, ENat.toNat_natCast] using hcard

/-! ## Stable interval separation and assembly -/

/-- The complete conclusion of 5.3(b,c), expressed using the connected
components of the large vertical image as its interval labels.  For every
contained positive-radius ball, the component count remains `M` and the
inclusion-induced map on components is a bijection. -/
def CharbonnelStableLocalVerticalIntervalSeparation {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) : Prop :=
  ∃ (M : ℕ) (x : RealEuclidean n) (r : ℝ), 0 < r ∧
    ∃ label : Fin M ≃ ConnectedComponents
        (charbonnelVerticalImageOver S (Metric.closedBall x r) : Set ℝ),
      ∀ (y : RealEuclidean n) (s : ℝ), 0 < s →
        ∀ hsub : Metric.closedBall y s ⊆ Metric.closedBall x r,
          charbonnelLocalVerticalComponentCount S y s = (M : ℕ∞) ∧
          Function.Bijective
            (charbonnelVerticalComponentInclusionMap S hsub)

/-- The uniform bound from 5.3(a), together with the stronger global-maximal
full-support selection, gives stable interval separation.  The latter is not
the source theorem and is generally false; a corrected count-lowering route
must replace this implication in the final complement proof. -/
theorem charbonnelStableLocalVerticalIntervalSeparation_of_uniformBound_of_fullSupportSelection
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hbound : CharbonnelUniformLocalVerticalComponentBound S)
    (hselection : CharbonnelSection53FullSupportSelection S) :
    CharbonnelStableLocalVerticalIntervalSeparation S := by
  obtain ⟨M, x₀, r₀, hmax⟩ := hbound.exists_maximalLocalVerticalBall
  obtain ⟨x, r, hfull⟩ := hselection M ⟨x₀, r₀, hmax⟩
  obtain ⟨label⟩ :=
    exists_fin_equiv_connectedComponents_of_enatCard_eq hfull.1.2.1
  refine ⟨M, x, r, hfull.1.1, label, ?_⟩
  intro y s hs hsub
  exact ⟨hfull.componentCount_eq y s hs hsub,
    hfull.componentInclusion_bijective y s hs hsub⟩

/-- The labels in stable interval separation are pairwise-disjoint
order-connected subsets of `ℝ` whose union is the large vertical image. -/
theorem CharbonnelStableLocalVerticalIntervalSeparation.intervalDecomposition
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hstable : CharbonnelStableLocalVerticalIntervalSeparation S) :
    ∃ (M : ℕ) (x : RealEuclidean n) (r : ℝ), 0 < r ∧
      ∃ label : Fin M ≃ ConnectedComponents
          (charbonnelVerticalImageOver S (Metric.closedBall x r) : Set ℝ),
        (∀ i, OrdConnected
          (realConnectedComponentCarrier
            (charbonnelVerticalImageOver S (Metric.closedBall x r))
            (label i))) ∧
        (Set.univ : Set (Fin M)).PairwiseDisjoint
          (fun i ↦ realConnectedComponentCarrier
            (charbonnelVerticalImageOver S (Metric.closedBall x r))
            (label i)) ∧
        ⋃ i : Fin M,
            realConnectedComponentCarrier
              (charbonnelVerticalImageOver S (Metric.closedBall x r))
              (label i) =
          charbonnelVerticalImageOver S (Metric.closedBall x r) := by
  obtain ⟨M, x, r, hr, label, _hstability⟩ := hstable
  refine ⟨M, x, r, hr, label, ?_, ?_, ?_⟩
  · intro i
    exact realConnectedComponentCarrier_ordConnected _ (label i)
  · intro i _hi j _hj hij
    exact realConnectedComponentCarriers_pairwiseDisjoint
      (charbonnelVerticalImageOver S (Metric.closedBall x r))
      (Set.mem_univ (label i)) (Set.mem_univ (label j))
      (fun h ↦ hij (label.injective h))
  · exact iUnion_realConnectedComponentCarrier_equiv
      (charbonnelVerticalImageOver S (Metric.closedBall x r)) label

/-- When `S` is compact, the labeled interval carriers in the preceding
decomposition are compact, as in the source. -/
theorem CharbonnelStableLocalVerticalIntervalSeparation.intervals_isCompact
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hstable : CharbonnelStableLocalVerticalIntervalSeparation S)
    (hS : IsCompact S) :
    ∃ (M : ℕ) (x : RealEuclidean n) (r : ℝ), 0 < r ∧
      ∃ label : Fin M ≃ ConnectedComponents
          (charbonnelVerticalImageOver S (Metric.closedBall x r) : Set ℝ),
        ∀ i, IsCompact
          (realConnectedComponentCarrier
            (charbonnelVerticalImageOver S (Metric.closedBall x r))
            (label i)) := by
  obtain ⟨M, x, r, hr, label, _hstability⟩ := hstable
  refine ⟨M, x, r, hr, label, ?_⟩
  intro i
  exact realConnectedComponentCarrier_isCompact_of_isCompact
    (charbonnelLocalVerticalImage_isCompact hS x r) (label i)

/-- For each large interval label and each contained ball there is exactly
one smaller connected component mapped to that label. -/
theorem CharbonnelStableLocalVerticalIntervalSeparation.existsUnique_component_in_interval
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hstable : CharbonnelStableLocalVerticalIntervalSeparation S) :
    ∃ (M : ℕ) (x : RealEuclidean n) (r : ℝ), 0 < r ∧
      ∃ label : Fin M ≃ ConnectedComponents
          (charbonnelVerticalImageOver S (Metric.closedBall x r) : Set ℝ),
        ∀ (y : RealEuclidean n) (s : ℝ), 0 < s →
          ∀ hsub : Metric.closedBall y s ⊆ Metric.closedBall x r,
            ∀ i : Fin M, ∃! c : ConnectedComponents
                (charbonnelVerticalImageOver S
                  (Metric.closedBall y s) : Set ℝ),
              charbonnelVerticalComponentInclusionMap S hsub c = label i ∧
                realConnectedComponentCarrier
                    (charbonnelVerticalImageOver S (Metric.closedBall y s)) c ⊆
                  realConnectedComponentCarrier
                    (charbonnelVerticalImageOver S (Metric.closedBall x r))
                    (label i) := by
  obtain ⟨M, x, r, hr, label, hstability⟩ := hstable
  refine ⟨M, x, r, hr, label, ?_⟩
  intro y s hs hsub i
  have hbijective := (hstability y s hs hsub).2
  obtain ⟨c, hc⟩ := hbijective.2 (label i)
  refine ⟨c, ⟨hc, ?_⟩, ?_⟩
  · exact realConnectedComponentCarrier_subset_of_inclusionMap_eq
      S hsub hc
  intro d hd
  exact hbijective.1 (hd.1.trans hc.symm)

/-- Stable interval separation contains the component-count conclusion
already named in the section-5 reduction. -/
theorem CharbonnelStableLocalVerticalIntervalSeparation.stableComponentCount
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hstable : CharbonnelStableLocalVerticalIntervalSeparation S) :
    CharbonnelStableLocalVerticalComponentCount S := by
  obtain ⟨M, x, r, hr, _label, hstability⟩ := hstable
  refine ⟨M, x, r, hr, ?_⟩
  intro y s hs hsub
  exact (hstability y s hs hsub).1

/-! ## Literal-zero specialization -/

/-- For the literal-zero Charbonnel closure, all of 5.3(a) and all assembly
after the `(M,δ)` descent are proved.  The only remaining premise is the
full-support selection statement from 5.3(c). -/
theorem literalZeroSet_charbonnelClosure_stableLocalVerticalIntervalSeparation
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) (n + 1))
    (hselection : CharbonnelSection53FullSupportSelection S) :
    CharbonnelStableLocalVerticalIntervalSeparation S :=
  charbonnelStableLocalVerticalIntervalSeparation_of_uniformBound_of_fullSupportSelection
    (literalZeroSet_charbonnelClosure_uniformLocalVerticalComponentBound
      hG hsmooth hUFF hS)
    hselection

/-- The corresponding existing stable-count interface. -/
theorem literalZeroSet_charbonnelClosure_stableLocalVerticalComponentCount
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) (n + 1))
    (hselection : CharbonnelSection53FullSupportSelection S) :
    CharbonnelStableLocalVerticalComponentCount S :=
  (literalZeroSet_charbonnelClosure_stableLocalVerticalIntervalSeparation
    hG hsmooth hUFF hS hselection).stableComponentCount

end AbelFormalization
