import AbelFormalization.CofactorTangent
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem constraintFDeriv_surjective_of_criticalDeterminant_ne_zero
    {r : ℕ} (H : Fin r → E → ℝ) (χ : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E)
    (hdet : criticalDeterminant H χ basis x ≠ 0) :
    (constraintFDeriv H x).range = ⊤ := by
  have hmatrixDet : (criticalJacobianMatrix H χ basis x).det ≠ 0 := by
    exact hdet
  have hmatrixSurj : Function.Surjective
      (criticalJacobianMatrix H χ basis x).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((criticalJacobianMatrix H χ basis x).isUnit_iff_isUnit_det.mpr
        (isUnit_iff_ne_zero.mpr hmatrixDet))
  rw [LinearMap.range_eq_top]
  intro y
  let y' : Fin (r + 1) → ℝ :=
    fun i ↦ Fin.lastCases 0 (fun j ↦ y j) i
  obtain ⟨v, hv⟩ := hmatrixSurj y'
  refine ⟨∑ j, v j • basis j, ?_⟩
  ext i
  change fderiv ℝ (H i) x (∑ j, v j • basis j) = y i
  rw [map_sum]
  simp_rw [map_smul, smul_eq_mul]
  have hi := congrFun hv i.castSucc
  simpa [Matrix.mulVec, dotProduct, criticalJacobianMatrix, y', mul_comm] using hi

end AbelFormalization
