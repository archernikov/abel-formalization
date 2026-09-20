import AbelFormalization.ExponentialLogComparisonJacobian

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_exponentialGraphComparison_of_ne_zero
    (g : E → ℝ) {x : E} {Y : ℝ} (hg : DifferentiableAt ℝ g x)
    (hY : Y ≠ 0) :
    fderiv ℝ (exponentialGraphComparison g) (x, Y) =
      Y⁻¹ • ContinuousLinearMap.snd ℝ E ℝ -
        (fderiv ℝ g x).comp (ContinuousLinearMap.fst ℝ E ℝ) := by
  have hsnd : HasFDerivAt (fun p : E × ℝ ↦ p.2)
      (ContinuousLinearMap.snd ℝ E ℝ) (x, Y) :=
    (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
  have hlog : HasFDerivAt (fun p : E × ℝ ↦ Real.log p.2)
      (Y⁻¹ • ContinuousLinearMap.snd ℝ E ℝ) (x, Y) :=
    hsnd.log hY
  have hgcomp : HasFDerivAt (fun p : E × ℝ ↦ g p.1)
      ((fderiv ℝ g x).comp (ContinuousLinearMap.fst ℝ E ℝ)) (x, Y) :=
    hg.hasFDerivAt.comp (x, Y)
      (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt
  change fderiv ℝ (fun p : E × ℝ ↦ Real.log p.2 - g p.1) (x, Y) = _
  exact (hlog.sub hgcomp).fderiv

theorem constraintJacobianInBasis_logComparison_eq_updateRow_of_ne_zero
    {n : ℕ} (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E} {Y : ℝ}
    (hg : DifferentiableAt ℝ g x) (hY : Y ≠ 0) :
    constraintJacobianInBasis (exponentialLogComparisonTuple Ftilde g)
        (graphProductBasis basis) (x, Y) =
      (exponentialAdjunctionJacobianMatrix Ftilde g basis (x, Y)).updateRow
        (Fin.last n)
        (Y⁻¹ • exponentialAdjunctionJacobianMatrix Ftilde g basis
          (x, Y) (Fin.last n)) := by
  ext i j
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · rw [Matrix.updateRow_self]
    refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · rw [constraintJacobianInBasis, exponentialLogComparisonTuple,
        functionTupleSnoc_last, graphProductBasis_last,
        fderiv_exponentialGraphComparison_of_ne_zero g hg hY]
      simp [exponentialAdjunctionJacobianMatrix]
    · rw [constraintJacobianInBasis, exponentialLogComparisonTuple,
        functionTupleSnoc_last, graphProductBasis_castSucc,
        fderiv_exponentialGraphComparison_of_ne_zero g hg hY]
      simp [exponentialAdjunctionJacobianMatrix]
      field_simp
  · rw [Matrix.updateRow_ne (Fin.castSucc_ne_last k)]
    refine Fin.lastCases ?_ (fun l ↦ ?_) j <;>
      simp [constraintJacobianInBasis, exponentialLogComparisonTuple,
        exponentialAdjunctionJacobianMatrix, graphProductBasis]

theorem exponentialLogComparisonJacobian_eq_inv_mul_adjunctionJacobian_of_ne_zero
    {n : ℕ} (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E} {Y : ℝ}
    (hg : DifferentiableAt ℝ g x) (hY : Y ≠ 0) :
    exponentialLogComparisonJacobian Ftilde g basis (x, Y) =
      Y⁻¹ * exponentialAdjunctionJacobian Ftilde g basis (x, Y) := by
  rw [exponentialLogComparisonJacobian_eq_det_constraintJacobian,
    constraintJacobianInBasis_logComparison_eq_updateRow_of_ne_zero
      Ftilde g basis hg hY,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  rfl

theorem exponentialLogComparisonJacobian_ne_zero_of_ne_zero
    {n : ℕ} (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E} {Y : ℝ}
    (hg : DifferentiableAt ℝ g x) (hY : Y ≠ 0)
    (hJ : exponentialAdjunctionJacobian Ftilde g basis (x, Y) ≠ 0) :
    exponentialLogComparisonJacobian Ftilde g basis (x, Y) ≠ 0 := by
  rw [exponentialLogComparisonJacobian_eq_inv_mul_adjunctionJacobian_of_ne_zero
    Ftilde g basis hg hY]
  exact mul_ne_zero (inv_ne_zero hY) hJ

end AbelFormalization
