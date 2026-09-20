import AbelFormalization.AbelDensityExtension
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries

/-!
# Summing the logarithmic defect of an Abel density

The density is obtained by exponentiating a normally convergent series along
the contracting logarithmic orbit.  The quadratic defect and inverse-linear
orbit estimates make the majorant a convergent square-reciprocal series.
-/

noncomputable section

namespace AbelFormalization

open Set Filter Function
open scoped Topology

def logDensitySum (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, h (complexL^[n] z)

def densityFromLogDefect (h : ℂ → ℂ) (x : ℝ) : ℝ :=
  Real.exp (logDensitySum h (x : ℂ)).re / x ^ 2

theorem summable_square_reciprocal_majorant (K : ℝ) :
    Summable (fun n : ℕ => K / ((n : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  simpa only [Nat.cast_add, Nat.cast_one, mul_one_div] using h.mul_left K

theorem summable_logDensityTerms_of_bound {h : ℂ → ℂ} {z : ℂ} {K : ℝ}
    (hbound : ∀ n : ℕ, ‖h (complexL^[n] z)‖ ≤ K / ((n : ℝ) + 1) ^ 2) :
    Summable (fun n : ℕ => h (complexL^[n] z)) :=
  (summable_square_reciprocal_majorant K).of_norm_bounded hbound

theorem analyticOnNhd_logDensitySum_of_bound {h : ℂ → ℂ} {s : Set ℂ} {K : ℝ}
    (hs : IsOpen s)
    (ha : ∀ n : ℕ, AnalyticOnNhd ℂ (fun z => h (complexL^[n] z)) s)
    (hbound : ∀ n : ℕ, ∀ z ∈ s, ‖h (complexL^[n] z)‖ ≤ K / ((n : ℝ) + 1) ^ 2) :
    AnalyticOnNhd ℂ (logDensitySum h) s := by
  have hu : SummableUniformlyOn (fun n : ℕ => fun z => h (complexL^[n] z)) s :=
    ⟨_, hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
      (tendstoUniformlyOn_tsum (summable_square_reciprocal_majorant K) hbound)⟩
  exact (hu.hasSumUniformlyOn.hasSumLocallyUniformlyOn.summableLocallyUniformlyOn
    |>.differentiableOn hs (fun n z hz => (ha n z hz).differentiableAt)).analyticOnNhd hs

theorem densityFromLogDefect_pos (h : ℂ → ℂ) {x : ℝ} (hx : 0 < x) :
    0 < densityFromLogDefect h x :=
  div_pos (Real.exp_pos _) (sq_pos_of_pos hx)

theorem analyticAt_densityFromLogDefect {h : ℂ → ℂ} {x : ℝ} (hx : 0 < x)
    (ha : AnalyticAt ℂ (logDensitySum h) (x : ℂ)) :
    AnalyticAt ℝ (densityFromLogDefect h) x := by
  exact ha.re_ofReal.rexp.div (analyticAt_id.pow 2) (pow_ne_zero _ (ne_of_gt hx))

theorem densityFromLogDefect_invariant {h : ℂ → ℂ} {x : ℝ} (hx : 0 < x)
    (hs : Summable (fun n : ℕ => h (complexL^[n] (x : ℂ))))
    (he : (h (x : ℂ)).re = Real.log (x ^ 2 / ((1 + x) * (L x) ^ 2))) :
    densityFromLogDefect h (L x) / (1 + x) = densityFromLogDefect h x := by
  have hsum : logDensitySum h (x : ℂ) = h (x : ℂ) + logDensitySum h (L x : ℂ) := by
    rw [logDensitySum, hs.tsum_eq_zero_add]
    simp only [Function.iterate_zero, id_eq, logDensitySum,
      Function.iterate_succ_apply, complexL_ofReal (by linarith : 0 ≤ 1 + x)]
  have hp : 0 < x ^ 2 / ((1 + x) * (L x) ^ 2) :=
    div_pos (sq_pos_of_pos hx) (mul_pos (by linarith) (sq_pos_of_pos (L_pos hx)))
  unfold densityFromLogDefect
  rw [hsum, Complex.add_re, he, Real.exp_add, Real.exp_log hp]
  have hadd : 1 + x ≠ 0 := by linarith
  field_simp [ne_of_gt hx, ne_of_gt (L_pos hx), hadd]

end AbelFormalization
