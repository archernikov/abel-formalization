import AbelFormalization.InverseRegularity
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Derivative recurrence and iterated-logarithm estimates for the inverse

This proves the derivative recurrence and the strict iterated-logarithm
inequalities in the analytic-input lemma. All conclusions follow from `IsAbel`.
-/

namespace AbelFormalization

open Set Filter
open scoped Topology

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- Differentiating the inverse Abel recurrence. -/
theorem inverse_deriv_add_one (s : ℝ) :
    deriv (inverse A) (s + 1) =
      Real.exp (inverse A s) * deriv (inverse A) s := by
  calc
    deriv (inverse A) (s + 1) = deriv (fun t => inverse A (t + 1)) s :=
      (deriv_comp_add_const (inverse A) 1 s).symm
    _ = Real.exp (inverse A s) * deriv (inverse A) s := by
      rw [show (fun t => inverse A (t + 1)) =
          (fun t => Real.exp (inverse A t) - 1) from funext hA.inverse_add_one]
      exact (((hA.inverse_hasDerivAt s).differentiableAt.hasDerivAt).exp.sub_const 1).deriv

/-- The derivative of the double logarithm on positive Abel times. -/
theorem deriv_logLog_inverse {s : ℝ} (hs : 0 < s) :
    deriv (fun t => Real.log (Real.log (inverse A t))) s =
      deriv (inverse A) s / (inverse A s * Real.log (inverse A s)) := by
  have h := (((hA.inverse_hasDerivAt s).differentiableAt.hasDerivAt).log
    (ne_of_gt (hA.inverse_pos s))).log
      (ne_of_gt (Real.log_pos (hA.one_lt_inverse hs)))
  simpa only [div_div] using h.deriv

/-- The middle comparison from the manuscript, valid already for `s > 0`. -/
theorem inverse_deriv_ratio_lt_logLog_deriv {s : ℝ} (hs : 0 < s) :
    deriv (inverse A) (s - 1) / inverse A (s - 1) <
      deriv (fun t => Real.log (Real.log (inverse A t))) s := by
  have hv : inverse A s = Real.exp (inverse A (s - 1)) - 1 := by
    simpa only [sub_add_cancel] using hA.inverse_add_one (s - 1)
  have hd : deriv (inverse A) s =
      Real.exp (inverse A (s - 1)) * deriv (inverse A) (s - 1) := by
    simpa only [sub_add_cancel] using hA.inverse_deriv_add_one (s - 1)
  have hl : 0 < Real.log (inverse A s) := Real.log_pos (hA.one_lt_inverse hs)
  have hlog : Real.log (inverse A s) < inverse A (s - 1) := by
    calc
      Real.log (inverse A s) < Real.log (Real.exp (inverse A (s - 1))) :=
        Real.log_lt_log (hA.inverse_pos s) (by rw [hv]; linarith)
      _ = inverse A (s - 1) := Real.log_exp _
  have hratio : deriv (inverse A) (s - 1) < deriv (inverse A) s / inverse A s := by
    apply (lt_div_iff₀ (hA.inverse_pos s)).mpr
    rw [hv, hd]
    nlinarith [hA.inverse_deriv_pos (s - 1)]
  rw [hA.deriv_logLog_inverse hs]
  calc
    deriv (inverse A) (s - 1) / inverse A (s - 1) <
        deriv (inverse A) (s - 1) / Real.log (inverse A s) :=
      div_lt_div_of_pos_left (hA.inverse_deriv_pos (s - 1)) hl hlog
    _ < (deriv (inverse A) s / inverse A s) / Real.log (inverse A s) :=
      div_lt_div_of_pos_right hratio hl
    _ = deriv (inverse A) s / (inverse A s * Real.log (inverse A s)) :=
      div_div _ _ _

/-- A previous inverse derivative is strictly smaller than the next logarithmic
derivative. This comparison needs no restriction on `s`. -/
theorem inverse_deriv_sub_two_lt_ratio (s : ℝ) :
    deriv (inverse A) (s - 2) <
      deriv (inverse A) (s - 1) / inverse A (s - 1) := by
  have hshift : s - 2 + 1 = s - 1 := by ring
  have hv : inverse A (s - 1) = Real.exp (inverse A (s - 2)) - 1 := by
    simpa only [hshift] using hA.inverse_add_one (s - 2)
  have hd : deriv (inverse A) (s - 1) =
      Real.exp (inverse A (s - 2)) * deriv (inverse A) (s - 2) := by
    simpa only [hshift] using hA.inverse_deriv_add_one (s - 2)
  apply (lt_div_iff₀ (hA.inverse_pos (s - 1))).mpr
  rw [hv, hd]
  nlinarith [hA.inverse_deriv_pos (s - 2)]

/-- The first double-logarithm inequality holds for every positive Abel time. -/
theorem inverse_deriv_sub_two_lt_logLog_deriv {s : ℝ} (hs : 0 < s) :
    deriv (inverse A) (s - 2) <
      deriv (fun t => Real.log (Real.log (inverse A t))) s :=
  (hA.inverse_deriv_sub_two_lt_ratio s).trans (hA.inverse_deriv_ratio_lt_logLog_deriv hs)

/-- Both strict inequalities from the iterated-logarithm part of the analytic
input lemma, on one common tail. -/
theorem eventually_logLog_inverse_deriv_estimates :
    ∀ᶠ s : ℝ in atTop,
      deriv (inverse A) (s - 2) <
          deriv (fun t => Real.log (Real.log (inverse A t))) s ∧
        inverse A (s - 2) < deriv (inverse A) (s - 2) := by
  obtain ⟨r, hr⟩ := eventually_atTop.mp hA.eventually_inverse_lt_deriv
  filter_upwards [eventually_gt_atTop (max (r + 2) 0)] with s hs
  have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs
  have hsr : r ≤ s - 2 := by have := le_max_left (r + 2) 0; linarith
  exact ⟨hA.inverse_deriv_sub_two_lt_logLog_deriv hs0, hr (s - 2) hsr⟩

end IsAbel

end AbelFormalization
