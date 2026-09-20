import AbelFormalization.ExponentialGraphJacobianFormula

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The manuscript's lower-level Jacobian matrix on the whole enlarged
space: its bottom row uses the independent coordinate `Y`. -/
def exponentialAdjunctionJacobianMatrix {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (p : E × ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j ↦ Fin.lastCases
    (Fin.lastCases 1
      (fun k ↦ -p.2 * fderiv ℝ g p.1 (basis k)) j)
    (fun h ↦ Fin.lastCases
      (fderiv ℝ (fun q ↦ Ftilde q h) p (0, 1))
      (fun k ↦ fderiv ℝ (fun q ↦ Ftilde q h) p (basis k, 0)) j) i

/-- The global determinant `J(x,Y)` used to define the open curve `V`. -/
def exponentialAdjunctionJacobian {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (p : E × ℝ) : ℝ :=
  (exponentialAdjunctionJacobianMatrix Ftilde g basis p).det

@[simp]
theorem exponentialAdjunctionJacobianMatrix_on_graph {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (x : E) :
    exponentialAdjunctionJacobianMatrix Ftilde g basis
        (x, Real.exp (g x)) =
      paperExponentialGraphJacobianMatrix Ftilde g basis x := by
  rfl

/-- On `Y = exp(g(x))`, the lower-level manuscript determinant is exactly
the derivative determinant of the exponential graph equation. -/
theorem exponentialAdjunctionJacobian_on_graph {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hg : DifferentiableAt ℝ g x) :
    exponentialAdjunctionJacobian Ftilde g basis (x, Real.exp (g x)) =
      exponentialGraphJacobian Ftilde g basis (x, Real.exp (g x)) := by
  rw [exponentialAdjunctionJacobian,
    exponentialAdjunctionJacobianMatrix_on_graph,
    ← exponentialGraphJacobian_eq_det_paperMatrix Ftilde g basis hg]

theorem exponentialAdjunctionJacobian_ne_zero_of_mem_regularZeroSet
    {n : ℕ} {Omega : Set E}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, Real.exp (g x)))
    (hg : DifferentiableAt ℝ g x)
    (hx : x ∈ regularZeroSet Omega
      (exponentialGraphSubstitution Ftilde g)) :
    exponentialAdjunctionJacobian Ftilde g basis
        (x, Real.exp (g x)) ≠ 0 := by
  rw [exponentialAdjunctionJacobian_on_graph Ftilde g basis hg]
  exact exponentialGraphJacobian_ne_zero_of_mem_regularZeroSet
    Ftilde g basis hF hg hx

end AbelFormalization
