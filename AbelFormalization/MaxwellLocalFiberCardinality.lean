import AbelFormalization.MaxwellWeakSelection
import AbelFormalization.MaxwellPositiveZeroTraceSmallness
import AbelFormalization.KuratowskiUlamProduct
import AbelFormalization.ReciprocalConstraintGraph

/-!
# Maxwell--Figueiredo uniform local scalar-fiber cardinality

This file proves Figueiredo's Lemma 2.2.1 in the exact form consumed by
`MaxwellWeakSelection`.

The proof uses precisely the two earlier source inputs.

* WS5 gives one bound for the connected components of every affine section
  of the restricted relation.  A vertical section containing `N + 1`
  ordered points therefore contains a nondegenerate interval.
* Figueiredo's Theorem 2.1 turns empty interior into nullity (and also keeps
  the closure of an interiorless family member interiorless).  Fubini then
  shows that the base locus carrying `N + 1` fiber points has empty
  interior.

The remaining argument is finite: choose the last cardinality locus with
nonempty interior and take a ball in it away from the closure of the next
locus.  No complement closure, cell decomposition, definable choice, or
o-minimality conclusion is assumed.
-/

noncomputable section

open Filter Set Function MeasureTheory
open scoped MeasureTheory Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Vertical affine sections and their scalar fibers -/

/-- The affine line in flat `(x,y)` coordinates lying over `x`. -/
def maxwellScalarVerticalAffineSubspace {p : ℕ}
    (x : RealEuclidean p) :
    AffineSubspace ℝ (RealEuclidean (p + 1)) :=
  AffineSubspace.mk' (realEuclideanAppend x (0 : RealEuclidean 1))
    (realEuclideanTakeLeftContinuousLinearMap p 1).ker

@[simp]
theorem mem_maxwellScalarVerticalAffineSubspace_iff
    {p : ℕ} (x : RealEuclidean p) (z : RealEuclidean (p + 1)) :
    z ∈ maxwellScalarVerticalAffineSubspace x ↔
      realEuclideanTakeLeft z = x := by
  rw [maxwellScalarVerticalAffineSubspace, AffineSubspace.mem_mk']
  change realEuclideanTakeLeft
      (z - realEuclideanAppend x (0 : RealEuclidean 1)) = 0 ↔
    realEuclideanTakeLeft z = x
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    have hi' : z (Fin.castAdd 1 i) - x i = 0 := by
      simpa [realEuclideanTakeLeft, realEuclideanAppend] using hi
    exact sub_eq_zero.mp hi'
  · intro h
    funext i
    have hi := congrFun h i
    have hi' : z (Fin.castAdd 1 i) - x i = 0 :=
      sub_eq_zero.mpr hi
    simpa [realEuclideanTakeLeft, realEuclideanAppend] using hi'

/-- The vertical affine section of a scalar relation over one base point. -/
def maxwellScalarVerticalSection {p : ℕ}
    (R : MaxwellRelation p 1) (x : RealEuclidean p) :
    Set (RealEuclidean (p + 1)) :=
  R ∩ (maxwellScalarVerticalAffineSubspace x :
    Set (RealEuclidean (p + 1)))

/-- Projection of the vertical affine section to its unique scalar
coordinate. -/
def maxwellScalarVerticalSectionToFiber {p : ℕ}
    (R : MaxwellRelation p 1) (x : RealEuclidean p) :
    maxwellScalarVerticalSection R x → maxwellScalarFiber R x :=
  fun z ↦ ⟨realEuclideanTakeRight z.1 0, by
    have hx : realEuclideanTakeLeft z.1 = x :=
      (mem_maxwellScalarVerticalAffineSubspace_iff x z.1).mp z.2.2
    have hy : realEuclideanTakeRight z.1 =
        (fun _ : Fin 1 ↦ realEuclideanTakeRight z.1 0) := by
      funext i
      rw [show i = 0 from Fin.eq_zero i]
    change realEuclideanAppend x
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z.1 0) ∈ R
    have hcanonical : realEuclideanAppend x
        (fun _ : Fin 1 ↦ realEuclideanTakeRight z.1 0) = z.1 := by
      calc
        _ = realEuclideanAppend (realEuclideanTakeLeft z.1)
              (realEuclideanTakeRight z.1) := by rw [hx, hy]
        _ = z.1 := realEuclideanAppend_take z.1
    rw [hcanonical]
    exact z.2.1⟩

theorem continuous_maxwellScalarVerticalSectionToFiber
    {p : ℕ} (R : MaxwellRelation p 1) (x : RealEuclidean p) :
    Continuous (maxwellScalarVerticalSectionToFiber R x) := by
  apply Continuous.subtype_mk
  change Continuous
    (fun z : maxwellScalarVerticalSection R x ↦
      z.1 (Fin.natAdd p (0 : Fin 1)))
  exact (continuous_apply (Fin.natAdd p (0 : Fin 1))).comp
    continuous_subtype_val

theorem surjective_maxwellScalarVerticalSectionToFiber
    {p : ℕ} (R : MaxwellRelation p 1) (x : RealEuclidean p) :
    Function.Surjective (maxwellScalarVerticalSectionToFiber R x) := by
  rintro ⟨y, hy⟩
  let yv : RealEuclidean 1 := fun _ ↦ y
  refine ⟨⟨realEuclideanAppend x yv, hy, ?_⟩, ?_⟩
  · exact (mem_maxwellScalarVerticalAffineSubspace_iff x _).mpr
      (realEuclideanTakeLeft_append x yv)
  · apply Subtype.ext
    change realEuclideanTakeRight (realEuclideanAppend x yv) 0 = y
    simp [yv]

/-- WS5, applied to the relation itself and to its vertical affine lines,
gives one component bound for all scalar fibers. -/
theorem exists_maxwellScalarFiber_component_bound_of_ws5
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {p : ℕ} (hp : 0 < p) {R : MaxwellRelation p 1}
    (hR : R ∈ C (p + 1)) :
    ∃ N : ℕ, ∀ x : RealEuclidean p,
      ENat.card (ConnectedComponents (maxwellScalarFiber R x)) ≤ N := by
  obtain ⟨N, hN⟩ := hC.ws5_affineSections (by omega) hR
  refine ⟨N, ?_⟩
  intro x
  exact
    (enatCard_connectedComponents_le_of_continuous_surjective
      (continuous_maxwellScalarVerticalSectionToFiber R x)
      (surjective_maxwellScalarVerticalSectionToFiber R x)).trans
      (hN (maxwellScalarVerticalAffineSubspace x))

/-! ## Ordered points, component collisions, and interval fibers -/

/-- Any injected finite subset of a scalar fiber can be sorted increasingly,
giving the positive-increment witness used in the source formula. -/
theorem exists_maxwellOrderedScalarFiberWitness_of_fin_succ_injection
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (f : Fin (k + 1) → maxwellScalarFiber R x)
    (hf : Function.Injective f) :
    ∃ y : ℝ, MaxwellOrderedScalarFiberWitness R k x y := by
  let scalar : Fin (k + 1) → ℝ := fun i ↦ (f i : ℝ)
  have hscalar : Function.Injective scalar := by
    intro i j hij
    apply hf
    exact Subtype.ext hij
  let T : Set ℝ := Set.range scalar
  have hTfinite : T.Finite := Set.finite_range scalar
  let s : Finset ℝ := hTfinite.toFinset
  have hsCard : s.card = k + 1 := by
    change hTfinite.toFinset.card = k + 1
    rw [← Set.ncard_eq_toFinset_card T hTfinite,
      Set.ncard_range_of_injective hscalar]
    simp
  let values : RealEuclidean (k + 1) :=
    fun i ↦ s.orderEmbOfFin hsCard i
  refine ⟨values 0, values, rfl, ?_, ?_⟩
  · intro i
    exact (s.orderEmbOfFin hsCard).strictMono Fin.castSucc_lt_succ
  · intro i
    have hi : s.orderEmbOfFin hsCard i ∈ s :=
      s.orderEmbOfFin_mem hsCard i
    have hiT : s.orderEmbOfFin hsCard i ∈ T :=
      (Set.Finite.mem_toFinset hTfinite).mp hi
    obtain ⟨j, hj⟩ := hiT
    have hfj : scalar j ∈ maxwellScalarFiber R x := (f j).property
    rw [hj] at hfj
    exact hfj

/-- `N + 1` ordered points in a scalar fiber with at most `N` connected
components force a nondegenerate interval in that fiber. -/
theorem exists_interval_subset_maxwellScalarFiber_of_orderedWitness
    {p N : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hcomponents :
      ENat.card (ConnectedComponents (maxwellScalarFiber R x)) ≤ N)
    {y : ℝ} (hwitness :
      MaxwellOrderedScalarFiberWitness R N x y) :
    ∃ a b : ℝ, a < b ∧ Set.Icc a b ⊆ maxwellScalarFiber R x := by
  obtain ⟨values, _hzero, hstep, hvalues⟩ := hwitness
  have hmono : StrictMono values :=
    Fin.strictMono_iff_lt_succ.mpr hstep
  let point : Fin (N + 1) → maxwellScalarFiber R x :=
    fun i ↦ ⟨values i, hvalues i⟩
  let component : Fin (N + 1) →
      ConnectedComponents (maxwellScalarFiber R x) :=
    fun i ↦ ConnectedComponents.mk (point i)
  have hnotInjective : ¬ Function.Injective component := by
    intro hinjective
    exact
      (not_enatCard_connectedComponents_le_of_fin_succ_injection
        component hinjective) hcomponents
  obtain ⟨i, j, hijComponent, hij⟩ :=
    Function.not_injective_iff.mp hnotInjective
  have hinterval : ∀ {i j : Fin (N + 1)}, i < j →
      component i = component j →
      ∃ a b : ℝ, a < b ∧
        Set.Icc a b ⊆ maxwellScalarFiber R x := by
    intro i j hijOrder hijSame
    let K : Set ℝ :=
      Subtype.val '' connectedComponent (point j)
    have hKpreconnected : IsPreconnected K :=
      isPreconnected_connectedComponent.image _
        continuous_subtype_val.continuousOn
    have hipoint : point i ∈ connectedComponent (point j) := by
      apply ConnectedComponents.coe_eq_coe'.mp
      simpa [component] using hijSame
    have hiK : values i ∈ K := ⟨point i, hipoint, rfl⟩
    have hjK : values j ∈ K :=
      ⟨point j, mem_connectedComponent, rfl⟩
    refine ⟨values i, values j, hmono hijOrder, ?_⟩
    intro t ht
    obtain ⟨z, _hz, rfl⟩ :=
      hKpreconnected.Icc_subset hiK hjK ht
    exact z.property
  rcases lt_or_gt_of_ne hij with hijOrder | hjiOrder
  · exact hinterval hijOrder hijComponent
  · exact hinterval hjiOrder hijComponent.symm

/-- Measure-theoretic form of the preceding component collision. -/
theorem maxwellScalarFiber_volume_ne_zero_of_orderedWitness
    {p N : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hcomponents :
      ENat.card (ConnectedComponents (maxwellScalarFiber R x)) ≤ N)
    {y : ℝ} (hwitness :
      MaxwellOrderedScalarFiberWitness R N x y) :
    (volume : Measure ℝ) (maxwellScalarFiber R x) ≠ 0 := by
  obtain ⟨a, b, hab, hIcc⟩ :=
    exists_interval_subset_maxwellScalarFiber_of_orderedWitness
      hcomponents hwitness
  have hIccVolume : (volume : Measure ℝ) (Set.Icc a b) ≠ 0 := by
    rw [Real.volume_Icc, ENNReal.ofReal_ne_zero_iff]
    exact sub_pos.mpr hab
  intro hfiberZero
  exact hIccVolume (measure_mono_null hIcc hfiberZero)

/-! ## Cardinality loci -/

/-- Base points in `B` whose scalar fiber contains at least `r` points.
For positive `r`, the definition uses the ordered positive-increment formula
from `MaxwellWeakSelection`; the zero locus is simply `B`. -/
def maxwellScalarFiberCardinalityAtLeast {p : ℕ}
    (B : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    ℕ → Set (RealEuclidean p)
  | 0 => B
  | k + 1 =>
      {x | x ∈ B ∧
        ∃ y : ℝ, MaxwellOrderedScalarFiberWitness R k x y}

@[simp]
theorem mem_maxwellScalarFiberCardinalityAtLeast_zero_iff
    {p : ℕ} (B : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (x : RealEuclidean p) :
    x ∈ maxwellScalarFiberCardinalityAtLeast B R 0 ↔ x ∈ B :=
  Iff.rfl

@[simp]
theorem mem_maxwellScalarFiberCardinalityAtLeast_succ_iff
    {p k : ℕ} (B : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) (x : RealEuclidean p) :
    x ∈ maxwellScalarFiberCardinalityAtLeast B R (k + 1) ↔
      x ∈ B ∧
        ∃ y : ℝ, MaxwellOrderedScalarFiberWitness R k x y :=
  Iff.rfl

/-- Semantic cardinal form of the ordered positive-increment formula. -/
theorem mem_maxwellScalarFiberCardinalityAtLeast_iff_encard
    {p r : ℕ} (B : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) (x : RealEuclidean p) :
    x ∈ maxwellScalarFiberCardinalityAtLeast B R r ↔
      x ∈ B ∧ (r : ℕ∞) ≤ (maxwellScalarFiber R x).encard := by
  cases r with
  | zero => simp
  | succ k =>
      rw [mem_maxwellScalarFiberCardinalityAtLeast_succ_iff]
      constructor
      · rintro ⟨hxB, y, values, hzero, hstep, hvalues⟩
        let f : Fin (k + 1) → maxwellScalarFiber R x :=
          fun i ↦ ⟨values i, hvalues i⟩
        have hf : Function.Injective f := by
          intro i j hij
          apply (Fin.strictMono_iff_lt_succ.mpr hstep).injective
          exact congrArg Subtype.val hij
        have hcard := ENat.card_le_card_of_injective hf
        refine ⟨hxB, ?_⟩
        simpa only [ENat.card_eq_coe_fintype_card, Fintype.card_fin,
          ENat.card_coe_set_eq] using hcard
      · rintro ⟨hxB, hlower⟩
        have hnotUpper :
            ¬ (maxwellScalarFiber R x).encard ≤ (k : ℕ∞) := by
          intro hupper
          have himpossible : (k + 1 : ℕ∞) ≤ (k : ℕ∞) :=
            hlower.trans hupper
          have : k + 1 ≤ k :=
            ENat.natCast_le_natCast.mp himpossible
          omega
        obtain ⟨f, hf⟩ :=
          exists_fin_succ_injection_of_enatCard_not_le hnotUpper
        obtain ⟨y, hy⟩ :=
          exists_maxwellOrderedScalarFiberWitness_of_fin_succ_injection
            f hf
        exact ⟨hxB, y, hy⟩

/-- The positive-cardinality locus is the visible projection of the ordered
selection graph. -/
theorem maxwellScalarFiberCardinalityAtLeast_succ_eq_projection
    {p k : ℕ} (B : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) :
    maxwellScalarFiberCardinalityAtLeast B R (k + 1) =
      realEuclideanExistentialProjection
        (maxwellOrderedScalarSelectionGraph B R k) := by
  ext x
  rw [mem_maxwellScalarFiberCardinalityAtLeast_succ_iff]
  constructor
  · rintro ⟨hxB, y, hy⟩
    exact ⟨fun _ : Fin 1 ↦ y,
      (realEuclideanAppend_mem_maxwellOrderedScalarSelectionGraph_iff
        B R x y).mpr ⟨hxB, hy⟩⟩
  · rintro ⟨yv, hyv⟩
    have hyvConst : yv = (fun _ : Fin 1 ↦ yv 0) := by
      funext i
      rw [show i = 0 from Fin.eq_zero i]
    rw [hyvConst] at hyv
    have hgraph :=
      (realEuclideanAppend_mem_maxwellOrderedScalarSelectionGraph_iff
        B R x (yv 0)).mp hyv
    exact ⟨hgraph.1, ⟨yv 0, hgraph.2⟩⟩

/-- Every finite-cardinality locus is again a Charbonnel-closure member. -/
theorem maxwellScalarFiberCardinalityAtLeast_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p r : ℕ} (hp : 0 < p)
    {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hB : B ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellScalarFiberCardinalityAtLeast B R r ∈
      charbonnelClosure S p := by
  cases r with
  | zero => exact hB
  | succ k =>
      rw [maxwellScalarFiberCardinalityAtLeast_succ_eq_projection]
      exact charbonnelClosure_projection hp
        (maxwellOrderedScalarSelectionGraph_mem_charbonnelClosure
          hC hp hB hR)

/-! ## The Fubini step -/

/-- Under WS5 and WS6, the locus carrying one point more than the uniform
component bound has empty interior.  This category form is the precise
statement needed by Wilkie's nested-modulus argument: WS6 makes the
interiorless relation meagre, Kuratowski--Ulam selects a meagre scalar
fiber, and `N + 1` ordered points would force that fiber to contain an
interval. -/
theorem exists_component_bound_and_interior_atLeast_succ_eq_empty_of_category
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hinterior : interior R = ∅) :
    ∃ N : ℕ,
      (∀ x : RealEuclidean p,
        ENat.card (ConnectedComponents (maxwellScalarFiber R x)) ≤ N) ∧
      interior (maxwellScalarFiberCardinalityAtLeast B R (N + 1)) = ∅ := by
  obtain ⟨N, hcomponents⟩ :=
    exists_maxwellScalarFiber_component_bound_of_ws5 hC hp hR
  refine ⟨N, hcomponents, Set.not_nonempty_iff_eq_empty.mp ?_⟩
  intro hlocus
  have hRmeagre : IsMeagre R :=
    hC.isMeagre_of_interior_eq_empty (by omega) hR hinterior
  let E : (RealEuclidean p × ℝ) ≃L[ℝ] RealEuclidean (p + 1) :=
    realEuclideanAppendScalarContinuousLinearEquiv p
  let D : Set (RealEuclidean p × ℝ) := E ⁻¹' R
  have hDmeagre : IsMeagre D :=
    hRmeagre.preimage_of_isOpenMap E.continuous E.toHomeomorph.isOpenMap
  have hgood : ∀ᶠ x in residual (RealEuclidean p),
      IsMeagre (maxwellScalarFiber R x) := by
    have hsections :=
      IsMeagre.eventually_isMeagre_productFiber hDmeagre
    filter_upwards [hsections] with x hx
    change IsMeagre {y : ℝ | E (x, y) ∈ R} at hx
    change IsMeagre
      {y : ℝ | realEuclideanAppendScalar x y ∈ R} at hx
    simpa only [maxwellScalarFiber, realEuclideanAppendScalar] using hx
  obtain ⟨x, hxLocus, hxMeagre⟩ :=
    (dense_of_mem_residual hgood).inter_open_nonempty
      (interior (maxwellScalarFiberCardinalityAtLeast B R (N + 1)))
      isOpen_interior hlocus
  obtain ⟨_hxB, y, hyOrdered⟩ :=
    (mem_maxwellScalarFiberCardinalityAtLeast_succ_iff B R x).mp
      (interior_subset hxLocus)
  obtain ⟨a, b, hab, hinterval⟩ :=
    exists_interval_subset_maxwellScalarFiber_of_orderedWitness
      (hcomponents x) hyOrdered
  have hIooMeagre : IsMeagre (Set.Ioo a b) :=
    hxMeagre.mono (fun t ht ↦ hinterval ⟨ht.1.le, ht.2.le⟩)
  exact not_isMeagre_of_isOpen isOpen_Ioo
    (Set.nonempty_Ioo.mpr hab) hIooMeagre

/-- Under WS5 and Theorem 2.1, the locus carrying one point more than the
WS5 component bound has empty interior. -/
theorem exists_component_bound_and_interior_atLeast_succ_eq_empty
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hinterior : interior R = ∅) :
    ∃ N : ℕ,
      (∀ x : RealEuclidean p,
        ENat.card (ConnectedComponents (maxwellScalarFiber R x)) ≤ N) ∧
      interior (maxwellScalarFiberCardinalityAtLeast B R (N + 1)) = ∅ := by
  obtain ⟨N, hcomponents⟩ :=
    exists_maxwellScalarFiber_component_bound_of_ws5 hC hp hR
  have hRnull : (volume : Measure (RealEuclidean (p + 1))) R = 0 :=
    (h21 (by omega) hR).1.mp hinterior
  have hclosureInterior : interior (closure R) = ∅ :=
    (h21 (by omega) hR).2.1.mp hRnull
  have hclosureNull :
      (volume : Measure (RealEuclidean (p + 1))) (closure R) = 0 :=
    (h21 (by omega) hR).2.2.mp hclosureInterior
  let T : Set (RealEuclidean p × ℝ) :=
    maxwellScalarRelationProductCoordinates (closure R)
  have hTnull : (volume : Measure (RealEuclidean p × ℝ)) T = 0 :=
    maxwellScalarRelationProductCoordinates_volume_eq_zero hclosureNull
  have hTmeasurable : MeasurableSet T := by
    exact (maxwellScalarRelationProductEquiv p).measurableEmbedding
      |>.measurableSet_image' isClosed_closure.measurableSet
  have hbaseNull : (volume : Measure (RealEuclidean p))
      (maxwellScalarFiberCardinalityAtLeast B R (N + 1)) = 0 := by
    apply volume_base_eq_zero_of_prod_eq_zero_of_sections_ne_zero
      hTmeasurable _ hTnull
    intro x hx
    obtain ⟨_hxB, y, hy⟩ :=
      (mem_maxwellScalarFiberCardinalityAtLeast_succ_iff
        B R x).mp hx
    have hfiberNonzero :=
      maxwellScalarFiber_volume_ne_zero_of_orderedWitness
        (hcomponents x) hy
    have hclosureFiberNonzero :
        (volume : Measure ℝ) (maxwellScalarFiber (closure R) x) ≠ 0 := by
      intro hzero
      apply hfiberNonzero
      apply measure_mono_null _ hzero
      intro z hz
      exact subset_closure hz
    have hsection : Prod.mk x ⁻¹' T =
        maxwellScalarFiber (closure R) x := by
      ext z
      exact mem_maxwellScalarRelationProductCoordinates_iff (closure R) x z
    rwa [hsection]
  exact ⟨N, hcomponents,
    (volume : Measure (RealEuclidean p)).interior_eq_empty_of_null
      hbaseNull⟩

/-! ## Finite maximality and the local constant-cardinality ball -/

/-- A finite sequence whose first member has interior and whose last member
does not has a last adjacent `nonempty/empty` transition.  No monotonicity is
needed for this elementary finite step. -/
theorem exists_index_interior_nonempty_next_eq_empty
    {X : Type*} [TopologicalSpace X] (A : ℕ → Set X)
    {N : ℕ} (hzero : (interior (A 0)).Nonempty)
    (hfinal : interior (A (N + 1)) = ∅) :
    ∃ k : ℕ, k ≤ N ∧ (interior (A k)).Nonempty ∧
      interior (A (k + 1)) = ∅ := by
  induction N with
  | zero =>
      exact ⟨0, le_rfl, hzero, hfinal⟩
  | succ N ih =>
      by_cases hprevious : (interior (A (N + 1))).Nonempty
      · exact ⟨N + 1, by omega, hprevious, hfinal⟩
      · obtain ⟨k, hk, hkInterior, hkNext⟩ :=
          ih (not_nonempty_iff_eq_empty.mp hprevious)
        exact ⟨k, by omega, hkInterior, hkNext⟩

/-- Restricting a relation does not alter a scalar fiber over a retained
base point. -/
theorem maxwellScalarFiber_restrict_eq_of_mem
    {p : ℕ} (R : MaxwellRelation p 1)
    (B : Set (RealEuclidean p)) {x : RealEuclidean p} (hx : x ∈ B) :
    maxwellScalarFiber (maxwellRelationRestrict R B) x =
      maxwellScalarFiber R x := by
  ext y
  simp [maxwellScalarFiber, maxwellRelationRestrict, hx]

/-- Figueiredo's Lemma 2.2.1 from WS5, WS6, and closure-interior
regularity.  The category argument above replaces the nullity/Fubini part
of the traditional proof. -/
theorem maxwellLocalConstantScalarFiberCardinality_of_closureInteriorRegularity
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S)) :
    MaxwellLocalConstantScalarFiberCardinality
      (charbonnelClosure S) := by
  intro p hp B R hBopen hBnonempty hBmem hRmem hfull hinterior
  let A : MaxwellRelation p 1 := maxwellRelationRestrict R B
  have hAmem : A ∈ charbonnelClosure S (p + 1) :=
    maxwellRelationRestrict_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hBmem hRmem
  obtain ⟨N, _hcomponents, hlastEmpty⟩ :=
    exists_component_bound_and_interior_atLeast_succ_eq_empty_of_category
      hC hp (B := B) hAmem hinterior
  let locus : ℕ → Set (RealEuclidean p) :=
    maxwellScalarFiberCardinalityAtLeast B A
  have hlocusZero : locus 0 = B := rfl
  have hzeroInterior : (interior (locus 0)).Nonempty := by
    rw [hlocusZero, hBopen.interior_eq]
    exact hBnonempty
  obtain ⟨k, _hkN, hkInterior, hkNextEmpty⟩ :=
    exists_index_interior_nonempty_next_eq_empty locus
      hzeroInterior hlastEmpty
  have hlocusMem : ∀ r : ℕ, locus r ∈ charbonnelClosure S p := by
    intro r
    exact maxwellScalarFiberCardinalityAtLeast_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hBmem hAmem
  have hkNextClosureEmpty : interior (closure (locus (k + 1))) = ∅ := by
    exact hregularity hp (hlocusMem (k + 1)) hkNextEmpty
  obtain ⟨x₀, ε, hε, hball⟩ :=
    exists_ball_subset_diff_of_open_nonempty_of_closed_interior_empty
      isOpen_interior hkInterior isClosed_closure hkNextClosureEmpty
  let U : Set (RealEuclidean p) := Metric.ball x₀ ε
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUnonempty : U.Nonempty := ⟨x₀, Metric.mem_ball_self hε⟩
  have hUsubsetLocus : U ⊆ locus k := by
    intro x hx
    exact interior_subset (hball hx).1
  have hUsubsetB : U ⊆ B := by
    intro x hx
    exact
      ((mem_maxwellScalarFiberCardinalityAtLeast_iff_encard
        B A x).mp (hUsubsetLocus hx)).1
  have hUmem : U ∈ charbonnelClosure S p :=
    hC.ws2_polynomialSign hp
      (polynomialSignConstructible_ball x₀ hε)
  have hfiberCard : ∀ x ∈ U,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = k := by
    intro x hxU
    have hxLocus : x ∈ locus k := hUsubsetLocus hxU
    have hxNotNext : x ∉ locus (k + 1) := by
      intro hxNext
      exact (hball hxU).2 (subset_closure hxNext)
    have hlower : (k : ℕ∞) ≤ (maxwellScalarFiber A x).encard :=
      ((mem_maxwellScalarFiberCardinalityAtLeast_iff_encard
        B A x).mp hxLocus).2
    have hnotSucc :
        ¬ (k + 1 : ℕ∞) ≤ (maxwellScalarFiber A x).encard := by
      intro hsucc
      apply hxNotNext
      exact
        (mem_maxwellScalarFiberCardinalityAtLeast_iff_encard
          B A x).mpr ⟨hUsubsetB hxU, hsucc⟩
    have hupper : (maxwellScalarFiber A x).encard ≤ (k : ℕ∞) := by
      by_contra hnotUpper
      have hlt : (k : ℕ∞) < (maxwellScalarFiber A x).encard :=
        lt_of_not_ge hnotUpper
      have hsucc : (k + 1 : ℕ∞) ≤
          (maxwellScalarFiber A x).encard := by
        rw [ENat.natCast_add_one_le_iff]
        exact hlt
      exact hnotSucc hsucc
    have hcard : (maxwellScalarFiber A x).encard = (k : ℕ∞) :=
      le_antisymm hupper hlower
    have hfiniteA : (maxwellScalarFiber A x).Finite :=
      Set.finite_of_encard_eq_coe hcard
    have hncardA : (maxwellScalarFiber A x).ncard = k := by
      rw [Set.ncard_def, hcard]
      simp
    rw [maxwellScalarFiber_restrict_eq_of_mem R B (hUsubsetB hxU)] at hfiniteA
    rw [maxwellScalarFiber_restrict_eq_of_mem R B (hUsubsetB hxU)] at hncardA
    exact ⟨hfiniteA, hncardA⟩
  have hkPositive : 0 < k := by
    by_contra hk
    have hkZero : k = 0 := Nat.eq_zero_of_not_pos hk
    obtain ⟨x, hxU⟩ := hUnonempty
    obtain ⟨yv, hyv⟩ := hfull x (hUsubsetB hxU)
    have hyConst : yv = (fun _ : Fin 1 ↦ yv 0) := by
      funext i
      rw [show i = 0 from Fin.eq_zero i]
    have hscalarNonempty : (maxwellScalarFiber R x).Nonempty := by
      refine ⟨yv 0, ?_⟩
      change realEuclideanAppend x (fun _ : Fin 1 ↦ yv 0) ∈ R
      rw [← hyConst]
      exact hyv
    have hzeroCard := (hfiberCard x hxU).2
    rw [hkZero] at hzeroCard
    have hempty : maxwellScalarFiber R x = ∅ :=
      (Set.ncard_eq_zero (hs := (hfiberCard x hxU).1)).mp hzeroCard
    exact hscalarNonempty.ne_empty hempty
  obtain ⟨j, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkPositive)
  refine ⟨j, U, hUopen, hUnonempty, hUsubsetB, hUmem, ?_⟩
  intro x hx
  simpa using hfiberCard x hx

/-- Theorem 2.1 implies the closure regularity needed by the category form
of Figueiredo's Lemma 2.2.1. -/
theorem maxwellLocalConstantScalarFiberCardinality_of_theorem21
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S)) :
    MaxwellLocalConstantScalarFiberCardinality
      (charbonnelClosure S) := by
  have hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S) := by
    intro d hd T hT hTInterior
    exact (h21 hd hT).2.1.mp ((h21 hd hT).1.mp hTInterior)
  unfold MaxwellLocalConstantScalarFiberCardinality
  intro p hp B R hBopen hBnonempty hBmem hRmem hfull hinterior
  exact maxwellLocalConstantScalarFiberCardinality_of_closureInteriorRegularity
    (S := S) hC hregularity hp hBopen hBnonempty hBmem hRmem hfull
      hinterior

/-! ## Literal-zero/Abel-family adapters -/

/-- The currently isolated Maxwell closure/nullity dimension package and
UFF discharge Lemma 2.2.1 for the literal-zero Charbonnel closure. -/
theorem literalZeroSet_charbonnelClosure_maxwellLocalConstantScalarFiberCardinality
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hMaxwell : MaxwellClosureNullityDimensionInduction
      (charbonnelClosure (literalZeroSetFamily G))) :
    MaxwellLocalConstantScalarFiberCardinality
      (charbonnelClosure (literalZeroSetFamily G)) := by
  let hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  let h21 : CharbonnelTheorem21
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_theorem21_of_maxwellDimensionInduction
      hG hsmooth hUFF hMaxwell
  unfold MaxwellLocalConstantScalarFiberCardinality
  intro p hp B R hBopen hBnonempty hBmem hRmem hfull hinterior
  exact maxwellLocalConstantScalarFiberCardinality_of_theorem21
    (S := literalZeroSetFamily G) hC h21
    (p := p) (B := B) (R := R) hp hBopen hBnonempty
      hBmem hRmem hfull hinterior

/-- Adapter from the two stronger geometric premises already isolated in the
project: Maxwell's meagre finite-selection step and Charbonnel's connected
compact positive-volume step. -/
theorem literalZeroSet_charbonnelClosure_maxwellLocalConstantScalarFiberCardinality_of_steps
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure (literalZeroSetFamily G)))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G))) :
    MaxwellLocalConstantScalarFiberCardinality
      (charbonnelClosure (literalZeroSetFamily G)) := by
  let hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  let h21 : CharbonnelTheorem21
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_theorem21_of_meagreSelection_and_analyticStep
      hG hsmooth hUFF hselection hanalytic
  unfold MaxwellLocalConstantScalarFiberCardinality
  intro p hp B R hBopen hBnonempty hBmem hRmem hfull hinterior
  exact maxwellLocalConstantScalarFiberCardinality_of_theorem21
    (S := literalZeroSetFamily G) hC h21
    (p := p) (B := B) (R := R) hp hBopen hBnonempty
      hBmem hRmem hfull hinterior

end AbelFormalization
