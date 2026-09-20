import AbelFormalization.ComplexLog
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# A local analytic Abel density for `log (1 + x)`

This file constructs the density on a complex attracting petal.  The real
restriction is the local datum used to extend the density to all positive
reals.
-/

noncomputable section

namespace AbelFormalization

open Set Filter Asymptotics Complex Function
open scoped Topology

/-- The analytic quotient `(log (1+z) - z) / z²`, with its removable
singularity filled in at zero.  Iterated divided slopes let us obtain the
filled-in function without making a choice of value at the origin. -/
def logQuadraticTail : ℂ → ℂ :=
  (Function.swap dslope (0 : ℂ))^[2] complexL

theorem logQuadraticTail_zero : logQuadraticTail 0 = -(1 : ℂ) / 2 := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    .ofScalars ℂ (fun n => -(-1 : ℂ) ^ n / n)
  have hp : HasFPowerSeriesAt complexL p 0 := by
    change HasFPowerSeriesAt (fun z : ℂ => Complex.log (1 + z)) p 0
    simpa only [p] using hasFPowerSeriesAt_clog_one_add
  change (Function.swap dslope (0 : ℂ))^[2] complexL 0 = _
  rw [← (hp.has_fpower_series_iterate_dslope_fslope 2).coeff_zero 1,
    ← FormalMultilinearSeries.coeff]
  simp [p]

theorem complexL_eq_add_sq_mul_logQuadraticTail (z : ℂ) :
    complexL z = z + z ^ 2 * logQuadraticTail z := by
  by_cases hz : z = 0
  · simp [hz, complexL]
  · simp only [logQuadraticTail, Function.iterate_succ_apply', Function.iterate_zero_apply,
      dslope_of_ne _ hz, slope, sub_zero, smul_eq_mul, vsub_eq_sub]
    have hderiv : deriv complexL 0 = 1 := by
      simpa using (complexL_hasDerivAt (z := 0) (by norm_num)).deriv
    simp only [Function.swap, dslope_same, hderiv, complexL, sub_zero]
    field_simp
    simp

theorem logQuadraticTail_analyticAt {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ logQuadraticTail z := by
  have hL : DifferentiableOn ℂ complexL (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa [Metric.mem_ball] using hw
    have hre : -‖w‖ ≤ w.re := neg_le_of_abs_le (abs_re_le_norm w)
    exact (complexL_analyticAt (by
      simp only [add_re, one_re]
      linarith)).differentiableAt.differentiableWithinAt
  have h0 : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds 0 one_pos
  have h1 : DifferentiableOn ℂ (dslope complexL 0) (Metric.ball (0 : ℂ) 1) :=
    (Complex.differentiableOn_dslope h0).2 hL
  have h2 : DifferentiableOn ℂ logQuadraticTail (Metric.ball (0 : ℂ) 1) := by
    change DifferentiableOn ℂ (dslope (dslope complexL 0) 0) _
    exact (Complex.differentiableOn_dslope h0).2 h1
  exact h2.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball] using hz))

/-- The multiplicative correction between the model density `z⁻²` and its
pullback by `complexL`.  The factorized definition fills its removable
singularity at zero. -/
def densityRatio (z : ℂ) : ℂ :=
  ((1 + z) * (1 + z * logQuadraticTail z) ^ 2)⁻¹

@[simp]
theorem densityRatio_zero : densityRatio 0 = 1 := by
  simp [densityRatio]

theorem densityRatio_analyticAt_zero : AnalyticAt ℂ densityRatio 0 := by
  have hg : AnalyticAt ℂ logQuadraticTail 0 :=
    logQuadraticTail_analyticAt (by norm_num)
  change AnalyticAt ℂ (fun z : ℂ =>
    ((1 + z) * (1 + z * logQuadraticTail z) ^ 2)⁻¹) 0
  exact ((analyticAt_const.add analyticAt_id).mul
    ((analyticAt_const.add (analyticAt_id.mul hg)).pow 2)).inv (by norm_num)

theorem densityRatio_deriv_zero : deriv densityRatio 0 = 0 := by
  have hg : DifferentiableAt ℂ logQuadraticTail 0 :=
    (logQuadraticTail_analyticAt (by norm_num)).differentiableAt
  have hv : DifferentiableAt ℂ (fun z : ℂ => z * logQuadraticTail z) 0 :=
    differentiableAt_id.mul hg
  have hu : DifferentiableAt ℂ (fun z : ℂ => 1 + z * logQuadraticTail z) 0 :=
    (differentiableAt_const (c := (1 : ℂ))).add hv
  have hp : DifferentiableAt ℂ (fun z : ℂ =>
      (1 + z * logQuadraticTail z) ^ 2) 0 := hu.pow 2
  have ha : DifferentiableAt ℂ (fun z : ℂ => 1 + z) 0 :=
    (differentiableAt_const (c := (1 : ℂ))).add differentiableAt_id
  have hd : DifferentiableAt ℂ (fun z : ℂ =>
      (1 + z) * (1 + z * logQuadraticTail z) ^ 2) 0 := ha.mul hp
  have hvd : deriv (fun z : ℂ => z * logQuadraticTail z) 0 = -(1 : ℂ) / 2 := by
    change deriv (fun z : ℂ => id z * logQuadraticTail z) 0 = _
    rw [deriv_fun_mul differentiableAt_id hg]
    simp [logQuadraticTail_zero]
  have hud : deriv (fun z : ℂ => 1 + z * logQuadraticTail z) 0 = -(1 : ℂ) / 2 := by
    simpa only [deriv_const_add] using hvd
  have hpd : deriv (fun z : ℂ => (1 + z * logQuadraticTail z) ^ 2) 0 = -1 := by
    rw [deriv_fun_pow hu 2, hud]
    norm_num
  have hdd : deriv (fun z : ℂ =>
      (1 + z) * (1 + z * logQuadraticTail z) ^ 2) 0 = 0 := by
    rw [deriv_fun_mul ha hp, hpd]
    norm_num
  unfold densityRatio
  rw [deriv_fun_inv'' hd (by norm_num), hdd]
  norm_num

/-- The additive logarithmic defect whose orbit sum corrects `x⁻²` to an
invariant density. -/
def logDensityDefect (z : ℂ) : ℂ := Complex.log (densityRatio z)

@[simp]
theorem logDensityDefect_zero : logDensityDefect 0 = 0 := by
  simp [logDensityDefect]

theorem logDensityDefect_analyticAt_zero : AnalyticAt ℂ logDensityDefect 0 := by
  change AnalyticAt ℂ (fun z => Complex.log (densityRatio z)) 0
  exact densityRatio_analyticAt_zero.clog (by simpa using one_mem_slitPlane)

theorem logDensityDefect_deriv_zero : deriv logDensityDefect 0 = 0 := by
  have hq : DifferentiableAt ℂ densityRatio 0 :=
    densityRatio_analyticAt_zero.differentiableAt
  have hslit : densityRatio 0 ∈ slitPlane := by simpa using one_mem_slitPlane
  have h := Complex.deriv_log_comp_eq_logDeriv hq hslit
  rw [show (Complex.log ∘ densityRatio) = logDensityDefect by rfl,
    logDeriv, Pi.div_apply, densityRatio_deriv_zero] at h
  simpa using h

theorem densityRatio_ofReal {x : ℝ} (hx : 0 < x) :
    densityRatio (x : ℂ) =
      (x ^ 2 / ((1 + x) * (L x) ^ 2) : ℝ) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hL0 : L x ≠ 0 := (L_pos hx).ne'
  have hfac := complexL_eq_add_sq_mul_logQuadraticTail (x : ℂ)
  rw [complexL_ofReal (by linarith : 0 ≤ 1 + x)] at hfac
  have hu : 1 + (x : ℂ) * logQuadraticTail (x : ℂ) = ((L x / x : ℝ) : ℂ) := by
    calc
      1 + (x : ℂ) * logQuadraticTail (x : ℂ) =
          (x : ℂ)⁻¹ * ((x : ℂ) + (x : ℂ) ^ 2 * logQuadraticTail (x : ℂ)) := by
            field_simp
            <;> ring
      _ = (x : ℂ)⁻¹ * (L x : ℂ) := by rw [← hfac]
      _ = ((L x / x : ℝ) : ℂ) := by
        push_cast [div_eq_mul_inv]
        ring
  rw [densityRatio, hu]
  norm_cast
  field_simp [hx.ne', hL0, show 1 + x ≠ 0 by linarith]
  <;> ring

/-- On the positive real axis the complex logarithmic defect is the real
logarithm of the density correction ratio. -/
theorem logDensityDefect_ofReal_re {x : ℝ} (hx : 0 < x) :
    (logDensityDefect (x : ℂ)).re =
      Real.log (x ^ 2 / ((1 + x) * (L x) ^ 2)) := by
  rw [logDensityDefect, densityRatio_ofReal hx, Complex.log_ofReal_re]

end AbelFormalization
