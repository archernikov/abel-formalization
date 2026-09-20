import AbelFormalization.CharbonnelApproximationTraceSmallness
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Elementary inputs to Charbonnel section 5

Two inputs to the measure induction in Charbonnel's section 5 are elementary
consequences of the weak-structure axioms.

* Integral closed-ball truncations remain in the Charbonnel closure generated
  by literal zero sets.  The ambient norm on `RealEuclidean d = Fin d → ℝ` is
  the sup norm, so its closed ball is the finite intersection of the
  polynomial inequalities `xᵢ² ≤ m²`.
* In arity one, WS5 gives finitely many connected components.  A finite
  point-and-open-interval decomposition with empty interior contains only
  finitely many points; hence it has zero Lebesgue measure.  This proves the
  base assertion `P'_1`.

No analytic approximation theorem or complement closure is used here.
-/

noncomputable section

open Set MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Finite polynomial-sign intersections -/

/-- Polynomial-sign constructible sets are closed under intersections indexed
by a finite ordinal. -/
theorem polynomialSignConstructible_iInter_fin
    {d k : ℕ} (s : Fin k → Set (RealEuclidean d))
    (hs : ∀ i, PolynomialSignConstructible d (s i)) :
    PolynomialSignConstructible d (⋂ i, s i) := by
  induction k with
  | zero =>
      simpa using polynomialSignConstructible_univ d
  | succ k ih =>
      rw [show (⋂ i : Fin (k + 1), s i) =
          s 0 ∩ ⋂ j : Fin k, s j.succ by
        ext x
        simp only [mem_iInter, mem_inter_iff]
        constructor
        · intro hx
          exact ⟨hx 0, fun j ↦ hx j.succ⟩
        · rintro ⟨hzero, hsucc⟩ i
          exact Fin.cases hzero (fun j ↦ hsucc j) i]
      exact .inter (hs 0) (ih (fun j ↦ s j.succ) (fun j ↦ hs j.succ))

/-! ## Polynomial presentation of the sup-norm closed ball -/

/-- The polynomial `m² - xᵢ²` cutting out the `i`th coordinate slab of an
integral sup-norm ball. -/
def charbonnelClosedBallCoordinatePolynomial
    (d m : ℕ) (i : Fin d) : MvPolynomial (Fin d) ℝ :=
  MvPolynomial.C ((m : ℝ) ^ 2) - MvPolynomial.X i ^ 2

@[simp]
theorem charbonnelClosedBallCoordinatePolynomial_eval
    {d m : ℕ} (i : Fin d) (x : RealEuclidean d) :
    MvPolynomial.eval x (charbonnelClosedBallCoordinatePolynomial d m i) =
      (m : ℝ) ^ 2 - (x i) ^ 2 := by
  simp [charbonnelClosedBallCoordinatePolynomial]

/-- One closed coordinate slab is a finite union of a polynomial zero set and
a strict polynomial positivity set. -/
theorem polynomialSignConstructible_closedBallCoordinate
    {d m : ℕ} (i : Fin d) :
    PolynomialSignConstructible d
      {x : RealEuclidean d |
        0 ≤ MvPolynomial.eval x
          (charbonnelClosedBallCoordinatePolynomial d m i)} := by
  let P := charbonnelClosedBallCoordinatePolynomial d m i
  rw [show {x : RealEuclidean d | 0 ≤ MvPolynomial.eval x P} =
      {x | MvPolynomial.eval x P = 0} ∪
        {x | 0 < MvPolynomial.eval x P} by
    ext x
    simp only [mem_ofPred_eq, mem_union]
    constructor
    · intro hx
      rcases hx.eq_or_lt with hx | hx
      · exact Or.inl hx.symm
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact hx.symm.le
      · exact hx.le]
  exact .union (.zero P) (.pos P)

/-- A closed ball about zero in `RealEuclidean d` is polynomial-sign
constructible.  Recall that this function space carries the sup norm. -/
theorem polynomialSignConstructible_closedBall_zero
    (d m : ℕ) :
    PolynomialSignConstructible d
      (Metric.closedBall (0 : RealEuclidean d) (m : ℝ)) := by
  have hconstraints : PolynomialSignConstructible d
      (⋂ i : Fin d,
        {x : RealEuclidean d |
          0 ≤ MvPolynomial.eval x
            (charbonnelClosedBallCoordinatePolynomial d m i)}) :=
    polynomialSignConstructible_iInter_fin _
      (fun i ↦ polynomialSignConstructible_closedBallCoordinate i)
  convert hconstraints using 1
  rw [closedBall_pi (0 : RealEuclidean d)
    (Nat.cast_nonneg m)]
  ext x
  simp only [mem_iInter, mem_pi, mem_univ, true_implies, mem_ofPred_eq,
    Metric.mem_closedBall, Pi.zero_apply, Real.dist_eq, sub_zero,
    charbonnelClosedBallCoordinatePolynomial_eval]
  constructor
  · intro hx i
    rw [sub_nonneg]
    rw [sq_le_sq]
    simpa using hx i
  · intro hx i
    have hsq : (x i) ^ 2 ≤ (m : ℝ) ^ 2 := by
      simpa only [sub_nonneg] using hx i
    exact abs_le_of_sq_le_sq hsq (Nat.cast_nonneg m)

/-- Integral closed-ball truncations of literal-zero Charbonnel sets stay in
the same Charbonnel closure. -/
theorem literalZeroSet_charbonnelClosure_compactTruncationMembership
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    CharbonnelCompactTruncationMembership
      (charbonnelClosure (literalZeroSetFamily G)) := by
  intro d hd S hS m
  have hball : Metric.closedBall (0 : RealEuclidean d) (m : ℝ) ∈
      charbonnelClosure (literalZeroSetFamily G) d :=
    ((polynomialSignConstructible_closedBall_zero d m).isProjectedZeroSet hG)
      |>.mem_literalZeroSet_charbonnelClosure hd
  let hbase : ClosedPositiveArityDescriptionBase (literalZeroSetFamily G) :=
    literalZeroSetFamily_closedDescriptionBase hG hsmooth
  exact hbase.charbonnelClosure_inter hS hball

/-! ## Empty-interior unary decompositions are finite -/

/-- A unary piece contained in an empty-interior set is finite.  Every
non-point unary piece is open, so containment forces it to be empty. -/
theorem unaryPiece_carrier_finite_of_subset_interior_eq_empty
    (piece : UnaryPiece) {s : Set ℝ}
    (hsubset : piece.carrier ⊆ s) (hempty : interior s = ∅) :
    piece.carrier.Finite := by
  cases piece with
  | point a =>
      exact finite_singleton a
  | bounded a b =>
      change (Ioo a b).Finite
      have hinside : Ioo a b ⊆ interior s :=
        isOpen_Ioo.subset_interior_iff.mpr hsubset
      have heq : Ioo a b = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        have : x ∈ interior s := hinside hx
        rw [hempty] at this
        exact this
      rw [heq]
      exact finite_empty
  | leftRay b =>
      change (Iio b).Finite
      have hinside : Iio b ⊆ interior s :=
        isOpen_Iio.subset_interior_iff.mpr hsubset
      have heq : Iio b = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        have : x ∈ interior s := hinside hx
        rw [hempty] at this
        exact this
      rw [heq]
      exact finite_empty
  | rightRay a =>
      change (Ioi a).Finite
      have hinside : Ioi a ⊆ interior s :=
        isOpen_Ioi.subset_interior_iff.mpr hsubset
      have heq : Ioi a = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        have : x ∈ interior s := hinside hx
        rw [hempty] at this
        exact this
      rw [heq]
      exact finite_empty
  | whole =>
      change (Set.univ : Set ℝ).Finite
      have hinside : (Set.univ : Set ℝ) ⊆ interior s :=
        isOpen_univ.subset_interior_iff.mpr hsubset
      have heq : (Set.univ : Set ℝ) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        have : x ∈ interior s := hinside hx
        rw [hempty] at this
        exact this
      rw [heq]
      exact finite_empty

/-- An empty-interior set admitting a finite unary-piece decomposition is
finite. -/
theorem UnaryPieceDecomposable.finite_of_interior_eq_empty
    {s : Set ℝ} (hs : UnaryPieceDecomposable s)
    (hempty : interior s = ∅) : s.Finite := by
  obtain ⟨k, piece, hpieces⟩ := hs
  rw [hpieces]
  apply Set.finite_iUnion
  intro i
  apply unaryPiece_carrier_finite_of_subset_interior_eq_empty
    (piece i) (s := s) _ hempty
  rw [hpieces]
  exact subset_iUnion (fun j ↦ (piece j).carrier) i

/-! ## WS5 proves the one-dimensional base case -/

/-- Evaluation at the unique coordinate as a continuous linear equivalence. -/
def realEuclideanOneEquivReal : RealEuclidean 1 ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ

theorem realEuclideanOneCoordinateImage_eq_equivImage
    (s : Set (RealEuclidean 1)) :
    realEuclideanOneCoordinateImage s = realEuclideanOneEquivReal '' s := by
  ext x
  simp only [realEuclideanOneCoordinateImage, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨v, hv, hvx⟩
    exact ⟨v, hv, by
      simpa [realEuclideanOneEquivReal] using hvx⟩
  · rintro ⟨v, hv, hvx⟩
    exact ⟨v, hv, by
      simpa [realEuclideanOneEquivReal] using hvx⟩

/-- WS5 in arity one gives a unary-piece decomposition after applying the
unique coordinate equivalence. -/
theorem PositiveArityOMinimalWeakSetStructure.coordinateImage_unaryPieceDecomposable
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {s : Set (RealEuclidean 1)} (hs : s ∈ C 1) :
    UnaryPieceDecomposable (realEuclideanOneCoordinateImage s) := by
  obtain ⟨N, hN⟩ := hC.ws5_affineSections (n := 1) (by omega) hs
  have hcard : ENat.card (ConnectedComponents s) ≤ N := by
    have h := hN (⊤ : AffineSubspace ℝ (RealEuclidean 1))
    rw [AffineSubspace.top_coe, inter_univ] at h
    exact h
  have hcoordCard :
      ENat.card
        (ConnectedComponents (realEuclideanOneCoordinateImage s)) ≤ N :=
    (enatCard_connectedComponents_le_of_continuous_surjective
      (continuous_realEuclideanOneToCoordinateImage s)
      (surjective_realEuclideanOneToCoordinateImage s)).trans hcard
  exact unaryPieceDecomposable_of_enatCard_connectedComponents_le
    (realEuclideanOneCoordinateImage s) N hcoordCard

/-- The one-dimensional assertion `P'_1` follows from WS5. -/
theorem PositiveArityOMinimalWeakSetStructure.charbonnelPPrime_one
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C) :
    CharbonnelPPrime C 1 := by
  intro s _hsClosed hs
  constructor
  · intro hnull
    exact (volume : Measure (RealEuclidean 1)).interior_eq_empty_of_null hnull
  · intro hempty
    have hcoordEmpty :
        interior (realEuclideanOneCoordinateImage s) = ∅ := by
      rw [realEuclideanOneCoordinateImage_eq_equivImage]
      change interior (realEuclideanOneEquivReal.toHomeomorph '' s) = ∅
      rw [← realEuclideanOneEquivReal.toHomeomorph.image_interior]
      simp [hempty]
    have hcoordFinite :
        (realEuclideanOneCoordinateImage s).Finite :=
      (hC.coordinateImage_unaryPieceDecomposable hs)
        |>.finite_of_interior_eq_empty hcoordEmpty
    have himageFinite : (realEuclideanOneEquivReal '' s).Finite := by
      rwa [← realEuclideanOneCoordinateImage_eq_equivImage]
    have hsFinite : s.Finite :=
      himageFinite.of_finite_image realEuclideanOneEquivReal.injective.injOn
    exact hsFinite.measure_zero volume

/-! ## Assembly with the remaining section 5 inputs -/

/-- For the Charbonnel closure generated by literal zero sets, the elementary
membership and one-dimensional inputs reduce approximation-trace smallness
to the geometric analytic step, finite locally closed decomposition, and the
closed-lift witnesses from Charbonnel section 5. -/
theorem literalZeroSet_charbonnelClosure_approximationTraceSmallness_of_section5
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hdecomp : ∀ {n : ℕ}, 0 < n →
      CharbonnelFiniteLocallyClosedDecomposition
        (charbonnelClosure (literalZeroSetFamily G)) n)
    (hwitness : HasCharbonnelClosureNullityWitnesses
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelApproximationTraceSmallness
      (charbonnelClosure (literalZeroSetFamily G)) :=
  charbonnelApproximationTraceSmallness_of_section5Induction
    (literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth)
    (literalZeroSet_charbonnelClosure_compactTruncationMembership hG hsmooth)
    hC.charbonnelPPrime_one hanalytic hdecomp hwitness

end AbelFormalization
