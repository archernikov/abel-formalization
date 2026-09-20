import AbelFormalization.CharbonnelAffineSectionRankInduction
import AbelFormalization.CharbonnelFiniteLocallyClosedReduction

/-!
# Maxwell--Servi closure-interior regularity

This file separates the already formalized parts of Maxwell's Lemma 2.7
(cited as Servi 3.5.9) from its remaining geometric step.

There are three layers.

* A closed lift gives a countable exhaustion of its projection by compact,
  hence closed, sets.  Thus the semi-closed theorem supplies the `F_sigma`
  input used in Maxwell's proof.
* The WS5 rank induction gives one finite bound for the connected components
  of every affine section.
* What remains is the Maxwell finite-selection argument: if `A` has empty
  interior while `closure A` has interior, then for every `N` one affine
  section of `A` has `N + 1` distinct connected components.

The last item is exposed below as `MaxwellInteriorGapComponentSelection`.
It is not a consequence of elementary topology or of the component bound
for one isolated set.  In the source it uses the semi-closed weak-structure
uniformity together with Fubini.  All cardinal and family-level consequences
of that missing geometric statement are proved here.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## The `F_sigma` consequence of a closed lift -/

/-- A presentation as a countable union of closed sets.  This elementary
topological predicate is the ordinary real-topological `F_sigma` condition
needed in Maxwell's argument. -/
def IsCountableUnionOfClosedSets
    {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ F : ℕ → Set X, (∀ m, IsClosed (F m)) ∧ A = ⋃ m, F m

/-- The compact visible projection of the radius-`m` part of a closed lift. -/
def maxwellClosedLiftProjectionTruncation
    {n q : ℕ} (T : Set (RealEuclidean (n + q))) (m : ℕ) :
    Set (RealEuclidean n) :=
  realEuclideanExistentialProjection (charbonnelCompactTruncation T m)

/-- A truncated closed-lift projection is exactly the image under the
continuous visible-coordinate projection. -/
theorem maxwellClosedLiftProjectionTruncation_eq_image
    {n q : ℕ} (T : Set (RealEuclidean (n + q))) (m : ℕ) :
    maxwellClosedLiftProjectionTruncation T m =
      realEuclideanTakeLeft '' charbonnelCompactTruncation T m := by
  ext x
  constructor
  · rintro ⟨y, hxy⟩
    refine ⟨realEuclideanAppend x y, hxy, ?_⟩
    exact realEuclideanTakeLeft_append x y
  · rintro ⟨v, hv, rfl⟩
    refine ⟨realEuclideanTakeRight v, ?_⟩
    rw [realEuclideanAppend_take]
    exact hv

/-- Every truncation of the projection of a closed lift is compact. -/
theorem maxwellClosedLiftProjectionTruncation_isCompact
    {n q : ℕ} {T : Set (RealEuclidean (n + q))}
    (hT : IsClosed T) (m : ℕ) :
    IsCompact (maxwellClosedLiftProjectionTruncation T m) := by
  rw [maxwellClosedLiftProjectionTruncation_eq_image]
  change IsCompact
    ((realEuclideanTakeLeftContinuousLinearMap n q) ''
      charbonnelCompactTruncation T m)
  exact (charbonnelCompactTruncation_isCompact hT m).image
    (realEuclideanTakeLeftContinuousLinearMap n q).continuous

/-- The compact truncated projections exhaust the whole projection. -/
theorem iUnion_maxwellClosedLiftProjectionTruncation
    {n q : ℕ} (T : Set (RealEuclidean (n + q))) :
    ⋃ m : ℕ, maxwellClosedLiftProjectionTruncation T m =
      realEuclideanExistentialProjection T := by
  unfold maxwellClosedLiftProjectionTruncation
  rw [
    ← realEuclideanExistentialProjection_iUnion,
    iUnion_charbonnelCompactTruncation]

/-- The projection of a closed Euclidean set is `F_sigma`. -/
theorem realEuclideanExistentialProjection_isCountableUnionOfClosedSets
    {n q : ℕ} {T : Set (RealEuclidean (n + q))}
    (hT : IsClosed T) :
    IsCountableUnionOfClosedSets
      (realEuclideanExistentialProjection T) := by
  refine ⟨maxwellClosedLiftProjectionTruncation T, ?_, ?_⟩
  · intro m
    exact (maxwellClosedLiftProjectionTruncation_isCompact hT m).isClosed
  · exact (iUnion_maxwellClosedLiftProjectionTruncation T).symm

/-- The family-level closed-lift clause supplies an `F_sigma` presentation
for each positive-arity member. -/
theorem isCountableUnionOfClosedSets_of_closedLift
    {C : EuclideanSetFamily}
    (hclosedLift : ∀ {n : ℕ}, 0 < n →
      ∀ {A : Set (RealEuclidean n)}, A ∈ C n →
        ∃ (q : ℕ) (T : Set (RealEuclidean (n + q))),
          IsClosed T ∧ A = realEuclideanExistentialProjection T)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ C n) :
    IsCountableUnionOfClosedSets A := by
  obtain ⟨q, T, hTClosed, hprojection⟩ := hclosedLift hn hA
  rw [hprojection]
  exact realEuclideanExistentialProjection_isCountableUnionOfClosedSets hTClosed

/-- An `F_sigma` set with empty interior is meagre.  This is the Baire-side
observation used before Maxwell's finite-selection/Fubini step. -/
theorem IsCountableUnionOfClosedSets.isMeagre_of_interior_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsCountableUnionOfClosedSets A)
    (hinterior : interior A = ∅) :
    IsMeagre A := by
  obtain ⟨F, hFClosed, hAUnion⟩ := hA
  rw [hAUnion]
  apply isMeagre_iUnion
  intro m
  apply ((hFClosed m).isNowhereDense_iff.mpr ?_).isMeagre
  apply interior_eq_empty_of_subset
    (show F m ⊆ ⋃ i, F i from subset_iUnion F m)
  simpa only [hAUnion] using hinterior

/-- Every member of the literal-zero Charbonnel closure is `F_sigma`, by
the already proved semi-closed theorem. -/
theorem literalZeroSet_charbonnelClosure_isCountableUnionOfClosedSets
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ} (_hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure (literalZeroSetFamily G) n) :
    IsCountableUnionOfClosedSets A := by
  obtain ⟨q, T, hTClosed, _hTMem, hprojection⟩ :=
    literalZeroSet_charbonnelClosure_semiClosed hG hsmooth hA
  rw [hprojection]
  exact realEuclideanExistentialProjection_isCountableUnionOfClosedSets hTClosed

/-- The WS6 closed-lift field of an o-minimal weak structure supplies the
same `F_sigma` conclusion without any further set-family closure property. -/
theorem PositiveArityOMinimalWeakSetStructure.isCountableUnionOfClosedSets
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ C n) :
    IsCountableUnionOfClosedSets A := by
  obtain ⟨q, T, hTClosed, _hTMem, hprojection⟩ :=
    hC.ws6_closedLift hn hA
  rw [hprojection]
  exact realEuclideanExistentialProjection_isCountableUnionOfClosedSets hTClosed

/-- Consequently, an empty-interior member of a positive-arity o-minimal
weak structure is meagre. -/
theorem PositiveArityOMinimalWeakSetStructure.isMeagre_of_interior_eq_empty
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ C n) (hinterior : interior A = ∅) :
    IsMeagre A :=
  (hC.isCountableUnionOfClosedSets hn hA).isMeagre_of_interior_eq_empty
    hinterior

/-! ## The exact remaining Maxwell finite-selection statement -/

/-- One set has a finite uniform bound on the component counts of all its
affine sections. -/
def MaxwellFiniteAffineSectionComponentBound
    {n : ℕ} (A : Set (RealEuclidean n)) : Prop :=
  ∃ N : ℕ, ∀ V : AffineSubspace ℝ (RealEuclidean n),
    ENat.card (ConnectedComponents
      ((A ∩ (V : Set (RealEuclidean n))) : Set (RealEuclidean n))) ≤
        (N : ℕ∞)

/-- Component-explosion form of Maxwell's missing geometric step: an
interior gap forces failure of every finite affine-section bound. -/
def MaxwellInteriorGapComponentExplosion
    {n : ℕ} (A : Set (RealEuclidean n)) : Prop :=
  interior A = ∅ → interior (closure A) ≠ ∅ →
    ∀ N : ℕ, ∃ V : AffineSubspace ℝ (RealEuclidean n),
      ¬ ENat.card (ConnectedComponents
        ((A ∩ (V : Set (RealEuclidean n))) : Set (RealEuclidean n))) ≤
          (N : ℕ∞)

/-- Finite-selection form of the same missing Maxwell step.  The selected
components all lie in one affine section, which may depend on `N`. -/
def MaxwellInteriorGapComponentSelection
    {n : ℕ} (A : Set (RealEuclidean n)) : Prop :=
  interior A = ∅ → interior (closure A) ≠ ∅ →
    ∀ N : ℕ, ∃ (V : AffineSubspace ℝ (RealEuclidean n))
      (selected : Fin (N + 1) → ConnectedComponents
        ((A ∩ (V : Set (RealEuclidean n))) : Set (RealEuclidean n))),
        Function.Injective selected

/-- The category-shaped form closest to the generalized Maxwell proof:
a meagre member dense in an open set forces arbitrarily many components in
one affine section.  Semi-closedness turns empty interior into meagreness,
so this is a weaker premise than `MaxwellInteriorGapComponentSelection` in
the setting used below. -/
def MaxwellMeagreClosureComponentSelection
    {n : ℕ} (A : Set (RealEuclidean n)) : Prop :=
  IsMeagre A → interior (closure A) ≠ ∅ →
    ∀ N : ℕ, ∃ (V : AffineSubspace ℝ (RealEuclidean n))
      (selected : Fin (N + 1) → ConnectedComponents
        ((A ∩ (V : Set (RealEuclidean n))) : Set (RealEuclidean n))),
        Function.Injective selected

/-- For an `F_sigma` set, the meagre-selection statement supplies the
empty-interior-selection statement. -/
theorem maxwellInteriorGapComponentSelection_of_countableUnionClosed
    {n : ℕ} {A : Set (RealEuclidean n)}
    (hF : IsCountableUnionOfClosedSets A)
    (hselection : MaxwellMeagreClosureComponentSelection A) :
    MaxwellInteriorGapComponentSelection A := by
  intro hinterior hclosure N
  exact hselection
    (hF.isMeagre_of_interior_eq_empty hinterior) hclosure N

/-- An injection of `N + 1` components contradicts a component bound by
`N`. -/
theorem not_enatCard_connectedComponents_le_of_fin_succ_injection
    {X : Type*} [TopologicalSpace X] {A : Set X} {N : ℕ}
    (selected : Fin (N + 1) → ConnectedComponents A)
    (hselected : Function.Injective selected) :
    ¬ ENat.card (ConnectedComponents A) ≤ (N : ℕ∞) := by
  intro hupper
  have hlower :
      (N + 1 : ℕ∞) ≤ ENat.card (ConnectedComponents A) := by
    simpa only [ENat.card_eq_coe_fintype_card, Fintype.card_fin,
      Nat.cast_add, Nat.cast_one] using
        ENat.card_le_card_of_injective hselected
  have himpossible : (N + 1 : ℕ∞) ≤ (N : ℕ∞) :=
    hlower.trans hupper
  have : N + 1 ≤ N := ENat.natCast_le_natCast.mp himpossible
  omega

/-- The component-explosion and finite-selection formulations are
equivalent. -/
theorem maxwellInteriorGapComponentSelection_iff_explosion
    {n : ℕ} {A : Set (RealEuclidean n)} :
    MaxwellInteriorGapComponentSelection A ↔
      MaxwellInteriorGapComponentExplosion A := by
  constructor
  · intro hselection hinterior hclosure N
    obtain ⟨V, selected, hselected⟩ :=
      hselection hinterior hclosure N
    exact ⟨V,
      not_enatCard_connectedComponents_le_of_fin_succ_injection
        selected hselected⟩
  · intro hexplosion hinterior hclosure N
    obtain ⟨V, hV⟩ := hexplosion hinterior hclosure N
    obtain ⟨selected, hselected⟩ :=
      exists_fin_succ_injection_of_enatCard_not_le hV
    exact ⟨V, selected, hselected⟩

/-- A finite WS5-style bound and Maxwell finite selection rule out an
interior gap. -/
theorem interior_closure_eq_empty_of_maxwellComponentSelection
    {n : ℕ} {A : Set (RealEuclidean n)}
    (hbound : MaxwellFiniteAffineSectionComponentBound A)
    (hselection : MaxwellInteriorGapComponentSelection A)
    (hinterior : interior A = ∅) :
    interior (closure A) = ∅ := by
  classical
  by_contra hclosure
  obtain ⟨N, hN⟩ := hbound
  obtain ⟨V, selected, hselected⟩ :=
    hselection hinterior hclosure N
  exact
    (not_enatCard_connectedComponents_le_of_fin_succ_injection
      selected hselected) (hN V)

/-- Under a finite affine-section bound, Maxwell finite selection is
logically equivalent to closure preserving empty interior.  This theorem
makes explicit that the selection statement is precisely the unproved
geometric content, rather than a consequence already hidden in WS5. -/
theorem maxwellInteriorGapComponentSelection_iff_closureInteriorRegularity
    {n : ℕ} {A : Set (RealEuclidean n)}
    (hbound : MaxwellFiniteAffineSectionComponentBound A) :
    MaxwellInteriorGapComponentSelection A ↔
      (interior A = ∅ → interior (closure A) = ∅) := by
  constructor
  · intro hselection
    exact interior_closure_eq_empty_of_maxwellComponentSelection
      hbound hselection
  · intro hregularity hinterior hclosure _N
    exact False.elim (hclosure (hregularity hinterior))

/-! ## Family-level and literal-zero assembly -/

/-- Maxwell's finite-selection statement uniformly for all positive-arity
members of a Euclidean set family. -/
def HasMaxwellInteriorGapComponentSelection
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n →
    ∀ {A : Set (RealEuclidean n)}, A ∈ C n →
      MaxwellInteriorGapComponentSelection A

/-- The weaker, source-shaped family premise: meagre members which are
dense in an open set exhibit affine sections with arbitrarily many selected
components. -/
def HasMaxwellMeagreClosureComponentSelection
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n →
    ∀ {A : Set (RealEuclidean n)}, A ∈ C n →
      MaxwellMeagreClosureComponentSelection A

/-- The WS5 field of an o-minimal weak structure gives the set-level finite
affine-section bound. -/
theorem PositiveArityOMinimalWeakSetStructure.maxwellFiniteAffineSectionComponentBound
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ C n) :
    MaxwellFiniteAffineSectionComponentBound A := by
  exact hC.ws5_affineSections hn hA

/-- WS5 plus the exact Maxwell finite-selection step gives the
Maxwell--Servi closure-interior regularity interface. -/
theorem charbonnelClosureInteriorRegularity_of_ws5_and_maxwellComponentSelection
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hselection : HasMaxwellInteriorGapComponentSelection C) :
    CharbonnelClosureInteriorRegularity C := by
  intro n hn A hA hinterior
  exact interior_closure_eq_empty_of_maxwellComponentSelection
    (hC.maxwellFiniteAffineSectionComponentBound hn hA)
    (hselection hn hA) hinterior

/-- The source-shaped assembly uses WS6 for the `F_sigma`/meagre reduction,
WS5 for the finite upper bound, and only the meagre finite-selection step as
its remaining Maxwell premise. -/
theorem charbonnelClosureInteriorRegularity_of_ws5_ws6_and_maxwellMeagreSelection
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hselection : HasMaxwellMeagreClosureComponentSelection C) :
    CharbonnelClosureInteriorRegularity C := by
  intro n hn A hA hinterior
  apply interior_closure_eq_empty_of_maxwellComponentSelection
    (hC.maxwellFiniteAffineSectionComponentBound hn hA)
  · exact maxwellInteriorGapComponentSelection_of_countableUnionClosed
      (hC.isCountableUnionOfClosedSets hn hA)
      (hselection hn hA)
  · exact hinterior

/-- Direct specialization to the literal-zero Charbonnel closure.  The
already proved numeric description-rank induction discharges the entire
WS5 side; only Maxwell's finite-selection/Fubini step remains as a premise. -/
theorem literalZeroSet_charbonnelClosure_closureInteriorRegularity_of_maxwellComponentSelection
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hselection : HasMaxwellInteriorGapComponentSelection
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelClosureInteriorRegularity
      (charbonnelClosure (literalZeroSetFamily G)) := by
  intro n hn A hA hinterior
  exact interior_closure_eq_empty_of_maxwellComponentSelection
    (literalZeroSet_charbonnelClosure_ws5_affineSections
      hG hsmooth hUFF hn hA)
    (hselection hn hA) hinterior

/-- Literal-zero specialization with the weaker meagre-selection premise.
The proved semi-closed theorem supplies the `F_sigma` reduction and the
description-rank theorem supplies WS5. -/
theorem literalZeroSet_charbonnelClosure_closureInteriorRegularity_of_maxwellMeagreSelection
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelClosureInteriorRegularity
      (charbonnelClosure (literalZeroSetFamily G)) := by
  intro n hn A hA hinterior
  apply interior_closure_eq_empty_of_maxwellComponentSelection
    (literalZeroSet_charbonnelClosure_ws5_affineSections
      hG hsmooth hUFF hn hA)
  · exact maxwellInteriorGapComponentSelection_of_countableUnionClosed
      (literalZeroSet_charbonnelClosure_isCountableUnionOfClosedSets
        hG hsmooth hn hA)
      (hselection hn hA)
  · exact hinterior

end AbelFormalization
