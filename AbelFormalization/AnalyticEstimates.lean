import AbelFormalization.HigherDerivatives
import AbelFormalization.LowerDerivativeBounds
import AbelFormalization.InverseEstimates
import AbelFormalization.ComplexEstimates

/-!
# The full analytic-estimates lemma

`AnalyticEstimates` groups every conclusion of the manuscript's estimates lemma.
The inverse inequalities hold on one common tail. For each fixed disk radius,
one threshold and one constant work for every sufficiently large real center;
the selected complex extensions agree on all pairwise overlaps.

`IsAbel.analytic_estimates` proves this entire property from the stated Abel
function hypotheses. This lemma is an analytic input to the proposed main
theorem, and is distinct from the unproved o-minimality conclusion.
-/

namespace AbelFormalization

open Set Filter Asymptotics
open scoped Topology

/-- All conclusions of the analytic-estimates lemma, with the manuscript's
quantifier order and a compatible family of complex extensions for each radius. -/
structure AnalyticEstimates (A : ℝ → ℝ) : Prop where
  /-- The first scaled derivative tends to zero. -/
  first_scaled_derivative_tends_to_zero :
    Tendsto (fun x : ℝ => x * deriv A x) atTop (𝓝 0)
  /-- The derivative scaled by the power `3/2` tends to infinity. -/
  three_halves_scaled_derivative_tends_to_infinity :
    Tendsto (fun x : ℝ => x ^ (3 / 2 : ℝ) * deriv A x) atTop atTop
  /-- The Abel function has logarithmic Big-O growth. -/
  logarithmic_growth : A =O[atTop] Real.log
  /-- Every fixed positive-order derivative tends to zero. -/
  positive_derivatives_tend_to_zero :
    ∀ r : ℕ, 1 ≤ r → Tendsto (iteratedDeriv r A) atTop (𝓝 0)
  /-- All inverse derivative inequalities hold simultaneously on one tail. -/
  inverse_bounds : ∀ᶠ s : ℝ in atTop,
    inverse A s < deriv (inverse A) s ∧
      deriv (inverse A) s ≤ (inverse A s) ^ (3 / 2 : ℝ) ∧
      deriv (inverse A) (s - 2) <
        deriv (fun t => Real.log (Real.log (inverse A t))) s ∧
      inverse A (s - 2) < deriv (inverse A) (s - 2)
  /-- One threshold and one logarithmic bound work at every center for each
  fixed radius. The same chosen extensions are compatible on intersections. -/
  compatible_complex_extensions : ∀ M : ℝ, 0 < M →
    ∃ (xM K : ℝ) (F : ℝ → ℂ → ℂ),
      1 < xM ∧ 0 < K ∧
      (∀ x : ℝ, xM < x →
        AnalyticOnNhd ℂ (F x) (Metric.ball (x : ℂ) M) ∧
        (∀ y ∈ Metric.ball x M, F x (y : ℂ) = (A y : ℂ)) ∧
        ∀ z ∈ Metric.ball (x : ℂ) M, ‖F x z‖ ≤ K * Real.log x) ∧
      ∀ x y : ℝ, xM < x → xM < y →
        Set.EqOn (F x) (F y) (Metric.ball (x : ℂ) M ∩ Metric.ball (y : ℂ) M)

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- The two sets of inverse estimates share one eventual threshold. -/
theorem eventually_full_inverse_estimates : ∀ᶠ s : ℝ in atTop,
    inverse A s < deriv (inverse A) s ∧
      deriv (inverse A) s ≤ (inverse A s) ^ (3 / 2 : ℝ) ∧
      deriv (inverse A) (s - 2) <
        deriv (fun t => Real.log (Real.log (inverse A t))) s ∧
      inverse A (s - 2) < deriv (inverse A) (s - 2) := by
  filter_upwards [hA.eventually_inverse_lt_deriv,
    hA.eventually_inverse_deriv_le_rpow_three_halves,
    hA.eventually_logLog_inverse_deriv_estimates] with s hs₁ hs₂ hs₃
  exact ⟨hs₁, hs₂, hs₃.1, hs₃.2⟩

/-- The complete analytic-estimates lemma, proved from `IsAbel`. -/
theorem analytic_estimates : AnalyticEstimates A where
  first_scaled_derivative_tends_to_zero := hA.tendsto_mul_deriv_atTop
  three_halves_scaled_derivative_tends_to_infinity :=
    hA.tendsto_rpow_three_halves_mul_deriv_atTop
  logarithmic_growth := hA.isBigO_log_atTop
  positive_derivatives_tend_to_zero := hA.tendsto_iteratedDeriv_atTop
  inverse_bounds := hA.eventually_full_inverse_estimates
  compatible_complex_extensions M hM :=
    hA.exists_compatible_bounded_complex_extensions (M := M) hM

end IsAbel

end AbelFormalization
