import AbelFormalization.ClosedZeroSetCharbonnelBridge
import AbelFormalization.ProjectedZeroComplementCriterion
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The algebraic part of the Maxwell closure-rank step

Maxwell's Claim 1.9, as used in Servi's Lemma 3.3.10, replaces a closure
node over a set `B ⊆ ℝⁿ` by

`(B × ℝ^(n²+n+2)) ∩ Eₙ`,

where `Eₙ` is one fixed semialgebraic thickening.  This file formalizes the
universal integer polynomial defining the affine-system parameter, proves
that all affine subspaces occur as its zero fibres, constructs `Eₙ` by
polynomial sign conditions, and proves that the replacement has rank at most
`rank B + 3`.  It is consequently strictly below the closure node, whose
rank is `rank B + 4`.

The geometric component estimate of Maxwell's Claim 1.9 is not asserted
here.  In particular, the rank calculation alone does not prove that taking
topological closure preserves the affine-section component bound.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-! ## A universal integer polynomial for affine systems -/

/-- The matrix and right-hand-side parameters for a square affine system in
`n` variables: `n²` matrix entries followed by `n` constants. -/
abbrev maxwellAffineParameterCount (n : ℕ) : ℕ := n * n + n

/-- The visible coordinate `x_j` in a block `(x,M,b,t)`, where `t` is an
optional trailing block. -/
def maxwellAffineXIndex (n tail : ℕ) (j : Fin n) :
    Fin (n + (maxwellAffineParameterCount n + tail)) :=
  Fin.castAdd (maxwellAffineParameterCount n + tail) j

/-- The matrix parameter `M_ij` in a block `(x,M,b,t)`. -/
def maxwellAffineMatrixIndex (n tail : ℕ) (i j : Fin n) :
    Fin (n + (maxwellAffineParameterCount n + tail)) :=
  Fin.natAdd n
    (Fin.castAdd tail (Fin.castAdd n (finProdFinEquiv (i, j))))

/-- The right-hand-side parameter `b_i` in a block `(x,M,b,t)`. -/
def maxwellAffineConstantIndex (n tail : ℕ) (i : Fin n) :
    Fin (n + (maxwellAffineParameterCount n + tail)) :=
  Fin.natAdd n (Fin.castAdd tail (Fin.natAdd (n * n) i))

/-- Row `i` of the universal affine system, over an arbitrary coefficient
ring.  In particular, the specialization to `ℤ` has integer coefficients. -/
def maxwellAffineRowPolynomial (R : Type) [CommRing R]
    (n tail : ℕ) (i : Fin n) :
    MvPolynomial (Fin (n + (maxwellAffineParameterCount n + tail))) R :=
  (∑ j : Fin n,
      MvPolynomial.X (maxwellAffineMatrixIndex n tail i j) *
        MvPolynomial.X (maxwellAffineXIndex n tail j)) -
    MvPolynomial.X (maxwellAffineConstantIndex n tail i)

/-- One universal polynomial cuts out the whole affine system: it is the sum
of the squares of its row equations. -/
def maxwellUniversalAffinePolynomial (R : Type) [CommRing R]
    (n tail : ℕ) :
    MvPolynomial (Fin (n + (maxwellAffineParameterCount n + tail))) R :=
  ∑ i : Fin n, (maxwellAffineRowPolynomial R n tail i) ^ 2

/-- The universal polynomial really is obtained from an integer polynomial
by coefficient extension to `ℝ`. -/
theorem maxwellUniversalAffinePolynomial_map_int (n tail : ℕ) :
    MvPolynomial.map (Int.castRingHom ℝ)
        (maxwellUniversalAffinePolynomial ℤ n tail) =
      maxwellUniversalAffinePolynomial ℝ n tail := by
  simp [maxwellUniversalAffinePolynomial, maxwellAffineRowPolynomial]

@[simp]
theorem maxwellAffineRowPolynomial_eval_append
    {n tail : ℕ} (i : Fin n) (x : RealEuclidean n)
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (t : RealEuclidean tail) :
    MvPolynomial.eval
        (realEuclideanAppend x
          (realEuclideanAppend (realEuclideanAppend M b) t))
        (maxwellAffineRowPolynomial ℝ n tail i) =
      flatSquareMatrixMulVec M x i - b i := by
  classical
  let v : RealEuclidean
      (n + (maxwellAffineParameterCount n + tail)) :=
    realEuclideanAppend x
      (realEuclideanAppend (realEuclideanAppend M b) t)
  change (MvPolynomial.eval v)
      ((∑ j : Fin n,
          MvPolynomial.X (maxwellAffineMatrixIndex n tail i j) *
            MvPolynomial.X (maxwellAffineXIndex n tail j)) -
        MvPolynomial.X (maxwellAffineConstantIndex n tail i)) =
    (∑ j, flatSquareMatrixEntry M i j * x j) - b i
  rw [map_sub, map_sum]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _hj
    simp [v, maxwellAffineMatrixIndex, maxwellAffineXIndex,
      maxwellAffineParameterCount, flatSquareMatrixEntry]
  · simp [v, maxwellAffineConstantIndex, maxwellAffineParameterCount]

@[simp]
theorem maxwellUniversalAffinePolynomial_eval_append
    {n tail : ℕ} (x : RealEuclidean n)
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (t : RealEuclidean tail) :
    MvPolynomial.eval
        (realEuclideanAppend x
          (realEuclideanAppend (realEuclideanAppend M b) t))
        (maxwellUniversalAffinePolynomial ℝ n tail) =
      ∑ i : Fin n, (flatSquareMatrixMulVec M x i - b i) ^ 2 := by
  classical
  change (MvPolynomial.eval
      (realEuclideanAppend x
        (realEuclideanAppend (realEuclideanAppend M b) t)))
      (∑ i : Fin n, (maxwellAffineRowPolynomial ℝ n tail i) ^ 2) = _
  rw [map_sum]
  simp only [MvPolynomial.eval_pow]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [maxwellAffineRowPolynomial_eval_append]

theorem maxwellUniversalAffinePolynomial_eval_eq_zero_iff
    {n tail : ℕ} (x : RealEuclidean n)
    (M : FlatSquareMatrix n) (b : RealEuclidean n)
    (t : RealEuclidean tail) :
    MvPolynomial.eval
        (realEuclideanAppend x
          (realEuclideanAppend (realEuclideanAppend M b) t))
        (maxwellUniversalAffinePolynomial ℝ n tail) = 0 ↔
      flatSquareMatrixMulVec M x = b := by
  rw [maxwellUniversalAffinePolynomial_eval_append]
  rw [Finset.sum_sq_eq_zero_iff]
  constructor
  · intro h
    funext i
    have hi := h i (Finset.mem_univ i)
    exact sub_eq_zero.mp hi
  · intro h i _hi
    exact sub_eq_zero.mpr (congrFun h i)

/-- Every affine subspace in positive arity is a zero fibre of the fixed
universal integer polynomial (after extension of coefficients to `ℝ`). -/
theorem exists_maxwellUniversalAffinePolynomial_fiber_eq_affineSubspace
    {n : ℕ} (hn : 0 < n)
    (V : AffineSubspace ℝ (RealEuclidean n)) :
    ∃ (M : FlatSquareMatrix n) (b : RealEuclidean n),
      {x : RealEuclidean n |
          MvPolynomial.eval
            (realEuclideanAppend x (realEuclideanAppend M b))
            (maxwellUniversalAffinePolynomial ℝ n 0) = 0} =
        (V : Set (RealEuclidean n)) := by
  obtain ⟨M, b, hV⟩ := exists_flatSquareMatrix_eq_affineSubspace hn V
  refine ⟨M, b, ?_⟩
  rw [← hV]
  ext x
  simp only [Set.mem_ofPred_eq]
  simpa using
    (maxwellUniversalAffinePolynomial_eval_eq_zero_iff
      x M b (fun i : Fin 0 ↦ Fin.elim0 i))

/-! ## The fixed semialgebraic thickening -/

/-- The coordinate occupied by the radius `R` in `(x,M,b,R,ε)`. -/
def maxwellRadiusIndex (n : ℕ) :
    Fin (n + (maxwellAffineParameterCount n + 2)) :=
  Fin.natAdd n
    (Fin.natAdd (maxwellAffineParameterCount n) (0 : Fin 2))

/-- The coordinate occupied by `ε` in `(x,M,b,R,ε)`. -/
def maxwellEpsilonIndex (n : ℕ) :
    Fin (n + (maxwellAffineParameterCount n + 2)) :=
  Fin.natAdd n
    (Fin.natAdd (maxwellAffineParameterCount n) (1 : Fin 2))

/-- The squared Euclidean norm of the visible `x` block. -/
def maxwellVisibleNormSqPolynomial (n : ℕ) :
    MvPolynomial (Fin (n + (maxwellAffineParameterCount n + 2))) ℝ :=
  ∑ j : Fin n, MvPolynomial.X (maxwellAffineXIndex n 2 j) ^ 2

/-- `ε² - p(x,M,b)`, the upper half of `|p| < ε²`. -/
def maxwellThickeningUpperPolynomial (n : ℕ) :
    MvPolynomial (Fin (n + (maxwellAffineParameterCount n + 2))) ℝ :=
  MvPolynomial.X (maxwellEpsilonIndex n) ^ 2 -
    maxwellUniversalAffinePolynomial ℝ n 2

/-- `ε² + p(x,M,b)`, the lower half of `|p| < ε²`. -/
def maxwellThickeningLowerPolynomial (n : ℕ) :
    MvPolynomial (Fin (n + (maxwellAffineParameterCount n + 2))) ℝ :=
  MvPolynomial.X (maxwellEpsilonIndex n) ^ 2 +
    maxwellUniversalAffinePolynomial ℝ n 2

/-- `R² - ‖x‖²`, the bounded-ball condition in Maxwell's thickening. -/
def maxwellThickeningBallPolynomial (n : ℕ) :
    MvPolynomial (Fin (n + (maxwellAffineParameterCount n + 2))) ℝ :=
  MvPolynomial.X (maxwellRadiusIndex n) ^ 2 -
    maxwellVisibleNormSqPolynomial n

/-- Maxwell's fixed semialgebraic thickening, written without absolute value
as three strict polynomial inequalities. -/
def maxwellThickening (n : ℕ) :
    Set (RealEuclidean (n + (maxwellAffineParameterCount n + 2))) :=
  {v | 0 < MvPolynomial.eval v (maxwellThickeningUpperPolynomial n)} ∩
    {v | 0 < MvPolynomial.eval v (maxwellThickeningLowerPolynomial n)} ∩
      {v | 0 < MvPolynomial.eval v (maxwellThickeningBallPolynomial n)}

theorem polynomialSignConstructible_maxwellThickening (n : ℕ) :
    PolynomialSignConstructible
      (n + (maxwellAffineParameterCount n + 2)) (maxwellThickening n) := by
  exact .inter
    (.inter
      (.pos (maxwellThickeningUpperPolynomial n))
      (.pos (maxwellThickeningLowerPolynomial n))
    )
    (.pos (maxwellThickeningBallPolynomial n))

/-- The fixed thickening is a projected zero set for every geometric family. -/
theorem isProjectedZeroSet_maxwellThickening
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) (n : ℕ) :
    IsProjectedZeroSet G (maxwellThickening n) :=
  (polynomialSignConstructible_maxwellThickening n).isProjectedZeroSet hG

/-- The thickening has a rank-one description over the literal zero-set
base. -/
theorem exists_rank_one_description_maxwellThickening
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) (n : ℕ) :
    ∃ description : CharbonnelDescription (literalZeroSetFamily G)
        (n + (maxwellAffineParameterCount n + 2)),
      description.carrier = maxwellThickening n ∧ description.rank = 1 := by
  exact
    (isProjectedZeroSet_maxwellThickening hG n).exists_rank_one_literalZero_description
      (by omega)

/-! ## The strict rank drop below a closure node -/

/-- A rank-zero description of a whole positive-dimensional coordinate
space, represented as the zero set of the zero polynomial. -/
theorem exists_rank_zero_univ_literalZero_description
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {k : ℕ} (hk : 0 < k) :
    ∃ description : CharbonnelDescription (literalZeroSetFamily G) k,
      description.carrier = Set.univ ∧ description.rank = 0 := by
  have hmem : (Set.univ : Set (RealEuclidean k)) ∈
      literalZeroSetFamily G k := by
    simpa using literalZeroSet_polynomial_mem hG
      (0 : MvPolynomial (Fin k) ℝ)
  exact ⟨.base hk Set.univ hmem, rfl, rfl⟩

/-- The exact algebraic replacement used in the closure case of Servi
3.3.10.  Its carrier is `(B × ℝ^(n²+n+2)) ∩ Eₙ`, and its rank is strictly
smaller than the closure node over `B`.

This theorem is the rank half of the Maxwell step.  The comparison of
affine-section component counts between `closure B` and this carrier is the
remaining geometric content of Maxwell's Claim 1.9. -/
theorem exists_maxwellClosureReplacement
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ}
    (inner : CharbonnelDescription (literalZeroSetFamily G) n) :
    ∃ replacement : CharbonnelDescription (literalZeroSetFamily G)
        (n + (maxwellAffineParameterCount n + 2)),
      replacement.carrier =
          realEuclideanSetProduct inner.carrier Set.univ ∩
            maxwellThickening n ∧
        replacement.rank <
          (CharbonnelDescription.topologicalClosure inner).rank := by
  obtain ⟨whole, hwholeCarrier, hwholeRank⟩ :=
    exists_rank_zero_univ_literalZero_description hG
      (k := maxwellAffineParameterCount n + 2) (by omega)
  obtain ⟨cylinder, hcylinderCarrier, hcylinderRank⟩ :=
    literalZeroSetFamily_exists_product_description hG hsmooth inner whole
  obtain ⟨thickening, hthickeningCarrier, hthickeningRank⟩ :=
    exists_rank_one_description_maxwellThickening hG n
  obtain ⟨replacement, hreplacementCarrier, hreplacementRank⟩ :=
    literalZeroSetFamily_exists_inter_description
      hG hsmooth cylinder thickening
  refine ⟨replacement, ?_, ?_⟩
  · rw [hreplacementCarrier, hcylinderCarrier, hwholeCarrier,
      hthickeningCarrier]
  · simp only [CharbonnelDescription.rank_topologicalClosure]
    omega

end AbelFormalization
