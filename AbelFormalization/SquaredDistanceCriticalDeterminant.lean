import AbelFormalization.CofactorTangent
import AbelFormalization.SquaredDistanceDifferentiation

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem criticalDeterminant_algebraicSquaredDistance_basis {r : ℕ}
    (H : Fin r → E → ℝ) (rho : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (center : Fin (r + 1) → ℝ) (x : E) :
    criticalDeterminant H
        (algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) center)
        basis x =
      ∑ i, 2 * (basis.equivFun x i - center i) *
        basis.equivFun (criticalCofactorTangent H rho basis x) i := by
  rw [criticalDeterminant_eq_fderiv_criticalCofactorTangent_of_aux
    H rho
      (algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) center)
      basis x]
  exact fderiv_algebraicSquaredDistance_basis_apply basis center x
    (criticalCofactorTangent H rho basis x)

theorem mem_constrainedCriticalSet_algebraicSquaredDistance_basis_iff
    {r : ℕ} {M : Set E}
    (H : Fin r → E → ℝ) (rho : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (center : Fin (r + 1) → ℝ) (x : M) :
    x ∈ constrainedCriticalSet M H
        (algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) center)
        basis ↔
      ∑ i, 2 * (basis.equivFun x i - center i) *
        basis.equivFun (criticalCofactorTangent H rho basis x) i = 0 := by
  change criticalDeterminant H
        (algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) center)
        basis x = 0 ↔ _
  rw [criticalDeterminant_algebraicSquaredDistance_basis
    H rho basis center x]

end AbelFormalization
