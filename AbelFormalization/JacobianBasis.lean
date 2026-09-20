import AbelFormalization.ConstraintSurjectivity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Basis.Basic

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Directional Jacobian in a genuine basis of the source. -/
def constraintJacobianInBasis {n : ℕ} (H : Fin n → E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (x : E) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ fderiv ℝ (H i) x (basis j)

theorem constraintFDeriv_sum_basis_eq_mulVec
    {n : ℕ} (H : Fin n → E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (x : E) (v : Fin n → ℝ) :
    constraintFDeriv H x (∑ j, v j • basis j) =
      (constraintJacobianInBasis H basis x).mulVec v := by
  ext i
  simp [constraintFDeriv, constraintJacobianInBasis,
    Matrix.mulVec, dotProduct, mul_comm]

/-- A square derivative is surjective exactly when its Jacobian determinant
in any source basis is nonzero. -/
theorem constraintJacobianInBasis_det_ne_zero_iff_surjective
    {n : ℕ} (H : Fin n → E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (x : E) :
    (constraintJacobianInBasis H basis x).det ≠ 0 ↔
      (constraintFDeriv H x).range = ⊤ := by
  constructor
  · intro hdet
    have hmatrixSurj : Function.Surjective
        (constraintJacobianInBasis H basis x).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((constraintJacobianInBasis H basis x).isUnit_iff_isUnit_det.mpr
          (isUnit_iff_ne_zero.mpr hdet))
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨v, hv⟩ := hmatrixSurj y
    refine ⟨∑ j, v j • basis j, ?_⟩
    exact (constraintFDeriv_sum_basis_eq_mulVec H basis x v).trans hv
  · intro hsurj
    have hLsurj : Function.Surjective (constraintFDeriv H x) :=
      LinearMap.range_eq_top.mp hsurj
    have hmatrixSurj : Function.Surjective
        (constraintJacobianInBasis H basis x).mulVec := by
      intro y
      obtain ⟨e, he⟩ := hLsurj y
      refine ⟨basis.repr e, ?_⟩
      rw [← constraintFDeriv_sum_basis_eq_mulVec H basis x]
      simpa only [basis.sum_repr] using he
    have hunit : IsUnit (constraintJacobianInBasis H basis x) :=
      Matrix.mulVec_surjective_iff_isUnit.mp hmatrixSurj
    exact isUnit_iff_ne_zero.mp
      ((constraintJacobianInBasis H basis x).isUnit_iff_isUnit_det.mp hunit)

end AbelFormalization
