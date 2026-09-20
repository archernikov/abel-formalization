import AbelFormalization.JacobianBasis
import AbelFormalization.LionRegularCodimensionOne
import AbelFormalization.SurjectiveJacobianRank

/-!
# Rectangular Jacobian minors for smooth geometric families

This file isolates the first rectangular rank-locus bridge needed beyond the
codimension-one part of the Lion finiteness argument.  For a map
`g : ℝ^a → ℝ^b`, its standard Jacobian is a `b × a` matrix.  Surjectivity of
the derivative is equivalent to one of its maximal column minors being
nonzero.  When the coordinate functions of `g` lie in a geometric family
closed under coordinate differentiation, every such minor lies in the family.

These are pointwise rank-locus facts.  They do not provide a stratification of
singular fibers or a component bound uniform in the target; those are separate
global steps in the uniform-fiber-finiteness argument.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The standard rectangular Jacobian of a map between coordinate real
spaces.  Rows are output coordinates and columns are source coordinates. -/
def standardRectangularJacobian {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (x : RealEuclidean a) :
    Matrix (Fin b) (Fin a) ℝ :=
  fun i j ↦ fderiv ℝ (fun y ↦ g y i) x
    ((Pi.basisFun ℝ (Fin a)) j)

/-- A maximal column minor of the standard rectangular Jacobian, regarded as
a scalar-valued function on the source. -/
def standardJacobianColumnMinor {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (cols : Fin b ↪ Fin a) :
    RealEuclideanFunction a :=
  fun x ↦ ((standardRectangularJacobian g x).submatrix id cols).det

/-- A matrix with finitely many rows induces a surjection onto its codomain
exactly when one full-row-size column minor is nonzero. -/
theorem matrix_mulVecLin_surjective_iff_exists_column_minor_ne_zero
    {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℝ) :
    Function.Surjective A.mulVecLin ↔
      ∃ cols : Fin b ↪ Fin a, (A.submatrix id cols).det ≠ 0 := by
  classical
  constructor
  · intro hsurj
    exact exists_column_minor_of_rank_eq A
      (matrix_rank_eq_of_mulVecLin_surjective A hsurj)
  · rintro ⟨cols, hcols⟩
    have hminorRank : (A.submatrix id cols).rank = b := by
      simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero hcols
    have hlower : b ≤ A.rank := by
      calc
        b = (A.submatrix id cols).rank := hminorRank.symm
        _ ≤ A.rank := Matrix.rank_submatrix_le A id cols
    have hrank : A.rank = b :=
      le_antisymm
        (by simpa only [Fintype.card_fin] using Matrix.rank_le_card_height A)
        hlower
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hrank, Module.finrank_pi, Fintype.card_fin]

/-- In standard source coordinates, the Fréchet derivative is multiplication
by the standard rectangular Jacobian. -/
theorem fderiv_eq_standardRectangularJacobian_mulVec
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {x : RealEuclidean a} (hg : DifferentiableAt ℝ g x)
    (v : RealEuclidean a) :
    fderiv ℝ g x v = (standardRectangularJacobian g x).mulVec v := by
  let H : Fin b → RealEuclideanFunction a := fun i y ↦ g y i
  let B : Module.Basis (Fin a) ℝ (RealEuclidean a) :=
    Pi.basisFun ℝ (Fin a)
  have hcoordinates : ∀ i, DifferentiableAt ℝ (H i) x := by
    intro i
    exact differentiableAt_pi.mp hg i
  have hfderiv : fderiv ℝ g x = constraintFDeriv H x := by
    change fderiv ℝ (fun y i ↦ H i y) x = constraintFDeriv H x
    simpa only [constraintFDeriv] using fderiv_pi hcoordinates
  have hv : (∑ j, v j • B j) = v := by
    simpa only [B, Pi.basisFun_repr] using B.sum_repr v
  have hmatrix :
      constraintFDeriv H x (∑ j, v j • B j) =
        (standardRectangularJacobian g x).mulVec v := by
    ext i
    simp [constraintFDeriv, standardRectangularJacobian, H, B,
      Matrix.mulVec, dotProduct, mul_comm]
  calc
    fderiv ℝ g x v = constraintFDeriv H x v :=
      congrArg (fun L : RealEuclidean a →L[ℝ] RealEuclidean b ↦ L v) hfderiv
    _ = constraintFDeriv H x (∑ j, v j • B j) :=
      congrArg (constraintFDeriv H x) hv.symm
    _ = (standardRectangularJacobian g x).mulVec v := hmatrix

/-- Pointwise surjectivity of a differentiable rectangular map is detected by
one nonzero maximal coordinate minor. -/
theorem fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {x : RealEuclidean a} (hg : DifferentiableAt ℝ g x) :
    Function.Surjective (fderiv ℝ g x) ↔
      ∃ cols : Fin b ↪ Fin a, standardJacobianColumnMinor g cols x ≠ 0 := by
  let A := standardRectangularJacobian g x
  have hfactor : ∀ v : RealEuclidean a,
      fderiv ℝ g x v = A.mulVec v := by
    intro v
    exact fderiv_eq_standardRectangularJacobian_mulVec hg v
  constructor
  · intro hsurj
    have hmatrix : Function.Surjective A.mulVecLin :=
      matrix_mulVecLin_surjective_of_factorization A (fderiv ℝ g x)
        (fun v : RealEuclidean a ↦ v) hsurj hfactor
    simpa only [A, standardJacobianColumnMinor] using
      (matrix_mulVecLin_surjective_iff_exists_column_minor_ne_zero A).mp hmatrix
  · intro hminor
    have hmatrix : Function.Surjective A.mulVecLin :=
      (matrix_mulVecLin_surjective_iff_exists_column_minor_ne_zero A).mpr (by
        simpa only [A, standardJacobianColumnMinor] using hminor)
    intro y
    obtain ⟨v, hv⟩ := hmatrix y
    refine ⟨v, ?_⟩
    exact (hfactor v).trans hv

/-- Every maximal rectangular Jacobian minor belongs to a geometric family
closed under coordinate differentiation. -/
theorem IsGeometricFunctionFamily.standardJacobianColumnMinor_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) (cols : Fin b ↪ Fin a) :
    standardJacobianColumnMinor g cols ∈ G a := by
  let M : Matrix (Fin b) (Fin b) (RealEuclideanFunction a) :=
    fun i j x ↦ fderiv ℝ (fun y ↦ g y i) x
      ((Pi.basisFun ℝ (Fin a)) (cols j))
  have hM : ∀ i j, M i j ∈ G a := by
    intro i j
    simpa only [M, Pi.basisFun_apply] using
      hderiv a (fun y ↦ g y i) (hg i) (cols j)
  have hdet : Matrix.det M ∈ G a := hG.matrix_det_mem M hM
  convert hdet using 1
  funext x
  change Matrix.det
      ((Pi.evalRingHom (fun _ : RealEuclidean a ↦ ℝ) x).mapMatrix M) =
    (Pi.evalRingHom (fun _ : RealEuclidean a ↦ ℝ) x) (Matrix.det M)
  exact ((Pi.evalRingHom (fun _ : RealEuclidean a ↦ ℝ) x).map_det M).symm

/-- For a tuple in an everywhere-smooth family, the pointwise regular-rank
condition is exactly the nonvanishing of one of the family-valued maximal
Jacobian minors. -/
theorem IsEverywhereSmoothFunctionFamily.fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) (x : RealEuclidean a) :
    Function.Surjective (fderiv ℝ g x) ↔
      ∃ cols : Fin b ↪ Fin a, standardJacobianColumnMinor g cols x ≠ 0 := by
  have hgSmooth : ContDiff ℝ ∞ g := by
    rw [contDiff_pi]
    intro i
    exact hsmooth a (fun y ↦ g y i) (hg i)
  exact AbelFormalization.fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
    ((hgSmooth.differentiable (by simp)).differentiableAt)

end AbelFormalization
