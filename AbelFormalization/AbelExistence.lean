import AbelFormalization.AbelLocalDensity
import AbelFormalization.AbelQuadraticDefectBound
import AbelFormalization.AbelLocalDensityAssembly
import AbelFormalization.AbelExistenceFromDensity

/-!
# Existence of the Abel function in the manuscript

This construction has no Abel-function or invariant-density existence premise.
The logarithmic density defect is analytic and vanishes to second order at zero.
Its convergent orbit sum produces a local positive density, inverse iteration
extends that density globally, and a normalized analytic primitive gives exactly
the four hypotheses bundled in `IsAbel`.
-/

noncomputable section

namespace AbelFormalization

/-- A positive analytic invariant density exists for `exp x - 1` on `(0,∞)`. -/
theorem exists_analytic_invariant_density :
    ∃ b : ℝ → ℝ, AnalyticOnNhd ℝ b (Set.Ioi 0) ∧
      (∀ x > 0, 0 < b x) ∧ (∀ x > 0, b (E x) * Real.exp x = b x) := by
  obtain ⟨R, hR, C, hC, ha, hbound⟩ :=
    exists_quadratic_bound_of_analytic_zero logDensityDefect_analyticAt_zero
      logDensityDefect_zero logDensityDefect_deriv_zero
  obtain ⟨ε, hε, b, hb, hbpos, hinv⟩ :=
    exists_local_density_of_log_defect hR hC ha hbound
      (fun x hx _ => logDensityDefect_ofReal_re hx)
  exact exists_global_density_of_local hε hb hbpos hinv

/-- The required Abel function exists, with precisely the draft's hypotheses. -/
theorem exists_isAbel : ∃ A : ℝ → ℝ, IsAbel A := by
  obtain ⟨b, hb, hbpos, hinv⟩ := exists_analytic_invariant_density
  exact exists_isAbel_of_analytic_density hb hbpos hinv

end AbelFormalization
