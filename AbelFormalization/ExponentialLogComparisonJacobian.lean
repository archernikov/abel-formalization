import AbelFormalization.ExponentialGraphJacobianFormula
import AbelFormalization.ExponentialAdjunctionJacobian

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_exponentialGraphComparison_at_graph
    (g : E → ℝ) {x : E} (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (exponentialGraphComparison g) (x, Real.exp (g x)) =
      (Real.exp (g x))⁻¹ • ContinuousLinearMap.snd ℝ E ℝ -
        (fderiv ℝ g x).comp (ContinuousLinearMap.fst ℝ E ℝ) := by
  have hsnd : HasFDerivAt (fun p : E × ℝ ↦ p.2)
      (ContinuousLinearMap.snd ℝ E ℝ) (x, Real.exp (g x)) :=
    (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
  have hlog : HasFDerivAt (fun p : E × ℝ ↦ Real.log p.2)
      ((Real.exp (g x))⁻¹ • ContinuousLinearMap.snd ℝ E ℝ)
      (x, Real.exp (g x)) := hsnd.log (Real.exp_ne_zero (g x))
  have hgcomp : HasFDerivAt (fun p : E × ℝ ↦ g p.1)
      ((fderiv ℝ g x).comp (ContinuousLinearMap.fst ℝ E ℝ))
      (x, Real.exp (g x)) :=
    hg.hasFDerivAt.comp (x, Real.exp (g x))
      (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt
  change fderiv ℝ (fun p : E × ℝ ↦ Real.log p.2 - g p.1)
      (x, Real.exp (g x)) = _
  exact (hlog.sub hgcomp).fderiv

theorem fderiv_exponentialGraphComparison_eq_inv_smul_graphEquation
    (g : E → ℝ) {x : E} (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (exponentialGraphComparison g) (x, Real.exp (g x)) =
      (Real.exp (g x))⁻¹ •
        fderiv ℝ (fun p : E × ℝ ↦ p.2 - Real.exp (g p.1))
          (x, Real.exp (g x)) := by
  rw [fderiv_exponentialGraphComparison_at_graph g hg,
    fderiv_exponentialGraphEquation_at_graph g hg]
  apply ContinuousLinearMap.ext
  intro v
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  change (Real.exp (g x))⁻¹ * v.2 - fderiv ℝ g x v.1 =
    (Real.exp (g x))⁻¹ *
      (v.2 - Real.exp (g x) * fderiv ℝ g x v.1)
  field_simp


/-- Scalar equations consisting of `F̃ = 0` and the logarithmic comparison
`log Y - g = 0`. -/
def exponentialLogComparisonTuple {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ) :
    Fin (n + 1) → E × ℝ → ℝ :=
  functionTupleSnoc (fun i p ↦ Ftilde p i) (exponentialGraphComparison g)

/-- Jacobian determinant of `F̃ = 0, log Y - g = 0`. -/
def exponentialLogComparisonJacobian {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (p : E × ℝ) : ℝ :=
  criticalDeterminant (fun i q ↦ Ftilde q i)
    (exponentialGraphComparison g) (graphProductBasis basis) p

theorem exponentialLogComparisonJacobian_eq_det_constraintJacobian {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (p : E × ℝ) :
    exponentialLogComparisonJacobian Ftilde g basis p =
      (constraintJacobianInBasis (exponentialLogComparisonTuple Ftilde g)
        (graphProductBasis basis) p).det := by
  rfl

theorem constraintJacobianInBasis_logComparison_eq_updateRow {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hg : DifferentiableAt ℝ g x) :
    constraintJacobianInBasis (exponentialLogComparisonTuple Ftilde g)
        (graphProductBasis basis) (x, Real.exp (g x)) =
      (constraintJacobianInBasis (exponentialGraphLiftTuple Ftilde g)
        (graphProductBasis basis) (x, Real.exp (g x))).updateRow
          (Fin.last n)
          ((Real.exp (g x))⁻¹ •
            constraintJacobianInBasis (exponentialGraphLiftTuple Ftilde g)
              (graphProductBasis basis) (x, Real.exp (g x)) (Fin.last n)) := by
  ext i j
  refine Fin.lastCases ?_ (fun h ↦ ?_) i
  · rw [Matrix.updateRow_self]
    simp [constraintJacobianInBasis, exponentialLogComparisonTuple,
      exponentialGraphLiftTuple]
    change fderiv ℝ (exponentialGraphComparison g) (x, Real.exp (g x))
        (graphProductBasis basis j) =
      ((Real.exp (g x))⁻¹ •
        fderiv ℝ (fun p : E × ℝ ↦ p.2 - Real.exp (g p.1))
          (x, Real.exp (g x))) (graphProductBasis basis j)
    rw [fderiv_exponentialGraphComparison_eq_inv_smul_graphEquation g hg]
  · have hne : h.castSucc ≠ Fin.last n := Fin.castSucc_ne_last h
    rw [Matrix.updateRow_ne hne]
    simp [constraintJacobianInBasis, exponentialLogComparisonTuple,
      exponentialGraphLiftTuple]


theorem exponentialLogComparisonJacobian_eq_inv_mul_graphJacobian {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hg : DifferentiableAt ℝ g x) :
    exponentialLogComparisonJacobian Ftilde g basis
        (x, Real.exp (g x)) =
      (Real.exp (g x))⁻¹ *
        exponentialGraphJacobian Ftilde g basis (x, Real.exp (g x)) := by
  rw [exponentialLogComparisonJacobian_eq_det_constraintJacobian,
    constraintJacobianInBasis_logComparison_eq_updateRow Ftilde g basis hg,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    exponentialGraphJacobian_eq_det_constraintJacobian]

/-- This is the manuscript's displayed identity
`det D(F̃, log Y - g) = J / Y` on the exponential graph. -/
theorem exponentialLogComparisonJacobian_eq_inv_mul_adjunctionJacobian
    {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hg : DifferentiableAt ℝ g x) :
    exponentialLogComparisonJacobian Ftilde g basis
        (x, Real.exp (g x)) =
      (Real.exp (g x))⁻¹ *
        exponentialAdjunctionJacobian Ftilde g basis
          (x, Real.exp (g x)) := by
  rw [exponentialLogComparisonJacobian_eq_inv_mul_graphJacobian
    Ftilde g basis hg,
    exponentialAdjunctionJacobian_on_graph Ftilde g basis hg]


theorem exponentialLogComparisonJacobian_ne_zero_iff {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hg : DifferentiableAt ℝ g x) :
    exponentialLogComparisonJacobian Ftilde g basis
        (x, Real.exp (g x)) ≠ 0 ↔
      exponentialGraphJacobian Ftilde g basis (x, Real.exp (g x)) ≠ 0 := by
  rw [exponentialLogComparisonJacobian_eq_inv_mul_graphJacobian
    Ftilde g basis hg]
  exact mul_ne_zero_iff_left (inv_ne_zero (Real.exp_ne_zero (g x)))

/-- Original regularity makes the logarithmic comparison transverse on the
lifted exponential graph. -/
theorem exponentialLogComparisonJacobian_ne_zero_of_mem_regularZeroSet
    {n : ℕ} {Omega : Set E}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, Real.exp (g x)))
    (hg : DifferentiableAt ℝ g x)
    (hx : x ∈ regularZeroSet Omega
      (exponentialGraphSubstitution Ftilde g)) :
    exponentialLogComparisonJacobian Ftilde g basis
        (x, Real.exp (g x)) ≠ 0 := by
  rw [exponentialLogComparisonJacobian_ne_zero_iff Ftilde g basis hg]
  exact exponentialGraphJacobian_ne_zero_of_mem_regularZeroSet
    Ftilde g basis hF hg hx

end AbelFormalization
