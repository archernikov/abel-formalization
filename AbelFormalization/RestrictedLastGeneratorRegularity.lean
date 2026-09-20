import AbelFormalization.RestrictedExponentialGraph
import AbelFormalization.RestrictedSystemLastGeneratorLift

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Pointwise recovery on the exponential graph identifies the abstract
substitution with the original scalar tuple. -/
theorem restrictedExponentialGraphSubstitution_eq_constraintMap_of_eval
    {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (F : Fin n → RestrictedSource m p a → ℝ)
    (g : RestrictedSource m p a → ℝ)
    (heval : ∀ x i,
      H i (restrictedSourceAppendAuxOne x (Real.exp (g x))) = F i x) :
    restrictedExponentialGraphSubstitution H g = constraintMap F := by
  funext x i
  exact heval x i

/-- The system lift supplied by an expression tower recovers the original
system after abstract exponential-graph substitution. -/
theorem RestrictedExpressionTower.restrictedLastGeneratorSystemLift_substitution
    {m p a ell n : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (i : Fin ell)
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (F : Fin n → RestrictedSource m p a → ℝ)
    (heval : ∀ x k,
      H k (restrictedSourceAppendAuxOne x (T.generator i x)) = F k x) :
    restrictedExponentialGraphSubstitution H (T.exponent i) =
      constraintMap F := by
  apply restrictedExponentialGraphSubstitution_eq_constraintMap_of_eval
  intro x k
  exact heval x k

/-- With a differentiable lower-level lift, the original regular zeros are
exactly the zeros of the logarithmic comparison on the concrete restricted
open curve. -/
def restrictedRegularZeroSetEquivComparisonZeroOfEval
    {m p a n : ℕ}
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (F : Fin n → RestrictedSource m p a → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (g : RestrictedSource m p a → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (heval : ∀ x i,
      H i (restrictedSourceAppendAuxOne x (Real.exp (g x))) = F i x)
    (hH : ∀ x, DifferentiableAt ℝ (restrictedSystemProductForm H)
      (x, Real.exp (g x)))
    (hg : Differentiable ℝ g) :
    regularZeroSet (restrictedBaseOpenDomain D R) (constraintMap F) ≃
      {y : RestrictedSource m p (a + 1) |
        y ∈ restrictedExponentialAdjunctionCurve H D R
          (restrictedExponentialAdjunctionJacobian H g basis) ∧
        restrictedExponentialGraphComparison g y = 0} := by
  rw [← restrictedExponentialGraphSubstitution_eq_constraintMap_of_eval
    H F g heval]
  exact restrictedRegularZeroSetEquivComparisonZero H D R g basis hH hg

end AbelFormalization
