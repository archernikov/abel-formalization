import AbelFormalization.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Set Filter MeasureTheory
open scoped Interval Topology

namespace AbelFormalization

noncomputable section

private def primitiveSeries (p : FormalMultilinearSeries ℝ ℝ ℝ) (c : ℝ) :
    FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ fun
    | 0 => c
    | n + 1 => p.coeff n / (n + 1 : ℝ)

private theorem primitiveSeries_radius (p : FormalMultilinearSeries ℝ ℝ ℝ) (c : ℝ) :
    p.radius ≤ (primitiveSeries p c).radius := by
  calc
    p.radius ≤ (primitiveSeries p c).shift.radius := by
      apply FormalMultilinearSeries.radius_le_of_le
      intro n
      rw [FormalMultilinearSeries.shift, ContinuousMultilinearMap.curryRight_norm]
      rw [FormalMultilinearSeries.norm_apply_eq_norm_coef,
        FormalMultilinearSeries.norm_apply_eq_norm_coef]
      simp only [primitiveSeries, FormalMultilinearSeries.coeff_ofScalars, norm_div]
      apply div_le_self (norm_nonneg _)
      rw [Real.norm_of_nonneg (by positivity)]
      norm_num
    _ = (primitiveSeries p c).radius := FormalMultilinearSeries.radius_shift _

private theorem primitiveSeries_derivSeries_eq
    (p : FormalMultilinearSeries ℝ ℝ ℝ) (c : ℝ) :
    (ContinuousLinearMap.apply ℝ ℝ 1).compFormalMultilinearSeries
        (primitiveSeries p c).derivSeries = p := by
  ext n
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply']
  have hcoeff : ((primitiveSeries p c).derivSeries.coeff n) 1 = p.coeff n := by
    rw [FormalMultilinearSeries.derivSeries_coeff_one]
    simp only [primitiveSeries, FormalMultilinearSeries.coeff_ofScalars]
    rw [nsmul_eq_mul]
    field_simp
    push_cast
    ring
  rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  simp [hcoeff]

private def densityPrimitive (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, b t

private theorem densityPrimitive_hasDerivAt
    {b : ℝ → ℝ} (hb : AnalyticOnNhd ℝ b (Set.Ioi 0))
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (densityPrimitive b) (b x) x := by
  apply intervalIntegral.integral_hasDerivAt_right
  · apply (hb.continuousOn.mono ?_).intervalIntegrable
    intro y hy
    rw [Set.mem_uIcc] at hy
    rcases hy with hy | hy
    · exact zero_lt_one.trans_le hy.1
    · exact hx.trans_le hy.1
  · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hb.continuousOn x hx
  · exact (hb x hx).continuousAt

private theorem primitiveSeries_deriv_hasFPowerSeriesAt
    (p : FormalMultilinearSeries ℝ ℝ ℝ) (c : ℝ) (hp : 0 < p.radius) :
    HasFPowerSeriesAt (deriv (primitiveSeries p c).sum) p 0 := by
  have hqpos : 0 < (primitiveSeries p c).radius :=
    hp.trans_le (primitiveSeries_radius p c)
  have hq := (primitiveSeries p c).hasFPowerSeriesOnBall hqpos
  have hmap := (ContinuousLinearMap.apply ℝ ℝ 1).comp_hasFPowerSeriesOnBall hq.fderiv
  rw [primitiveSeries_derivSeries_eq] at hmap
  convert hmap.hasFPowerSeriesAt using 1
  funext z
  exact fderiv_apply_one_eq_deriv

private theorem primitiveSeries_sum_zero
    (p : FormalMultilinearSeries ℝ ℝ ℝ) (c : ℝ) :
    (primitiveSeries p c).sum 0 = c := by
  change FormalMultilinearSeries.ofScalarsSum
    (fun | 0 => c | n + 1 => p.coeff n / (n + 1 : ℝ)) 0 = c
  simp

private theorem densityPrimitive_analyticAt
    {b : ℝ → ℝ} (hb : AnalyticOnNhd ℝ b (Set.Ioi 0))
    {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℝ (densityPrimitive b) x := by
  obtain ⟨p, hp⟩ := hb x hx
  have hppos : 0 < p.radius := by
    obtain ⟨r, hpr⟩ := hp
    exact hpr.r_pos.trans_le hpr.r_le
  let q := primitiveSeries p (densityPrimitive b x)
  have hqpos : 0 < q.radius := hppos.trans_le (primitiveSeries_radius p _)
  have hGanalytic : AnalyticAt ℝ (fun y => q.sum (y - x)) x := by
    simpa [q] using ((q.hasFPowerSeriesOnBall hqpos).analyticAt.comp_sub x)
  have hGderiv : HasFPowerSeriesAt (fun y => deriv q.sum (y - x)) p x := by
    simpa [q] using
      ((primitiveSeries_deriv_hasFPowerSeriesAt p (densityPrimitive b x) hppos).comp_sub x)
  have hderiv_unique :
      ∀ᶠ y in 𝓝 x, b y = deriv q.sum (y - x) := by
    filter_upwards [hp.eventually_hasSum_sub, hGderiv.eventually_hasSum_sub]
      with y hb' hG'
    exact hb'.unique hG'
  have hpos : ∀ᶠ y in 𝓝 x, 0 < y :=
    (isOpen_Ioi : IsOpen (Ioi (0 : ℝ))).mem_nhds hx
  have hFdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (densityPrimitive b) y := by
    filter_upwards [hpos] with y hy
    exact (densityPrimitive_hasDerivAt hb hy).differentiableAt
  have hGdiff : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun z => q.sum (z - x)) y := by
    filter_upwards [hGanalytic.eventually_analyticAt] with y hy
    exact hy.differentiableAt
  have hderiv_eq :
      ∀ᶠ y in 𝓝 x,
        deriv (densityPrimitive b) y = deriv (fun z => q.sum (z - x)) y := by
    filter_upwards [hpos, hderiv_unique] with y hy huniq
    rw [(densityPrimitive_hasDerivAt hb hy).deriv, deriv_comp_sub_const]
    exact huniq
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp
    (hFdiff.and (hGdiff.and hderiv_eq))
  have hcenter : densityPrimitive b x = q.sum (x - x) := by
    simp only [sub_self]
    simpa [q] using (primitiveSeries_sum_zero p (densityPrimitive b x)).symm
  have heqOn : Set.EqOn (densityPrimitive b) (fun y => q.sum (y - x)) (Metric.ball x δ) := by
    apply Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball x δ).isPreconnected
    · intro y hy
      exact (hlocal hy).1.differentiableWithinAt
    · intro y hy
      exact (hlocal hy).2.1.differentiableWithinAt
    · intro y hy
      exact (hlocal hy).2.2
    · exact Metric.mem_ball_self hδ
    · exact hcenter
  apply hGanalytic.congr
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  exact (heqOn hy).symm

private theorem densityPrimitive_analyticOnNhd
    {b : ℝ → ℝ} (hb : AnalyticOnNhd ℝ b (Set.Ioi 0)) :
    AnalyticOnNhd ℝ (densityPrimitive b) (Set.Ioi 0) :=
  fun _ hx => densityPrimitive_analyticAt hb hx

/-- A positive analytic density satisfying the Jacobian invariance equation
produces a normalized Abel function by integration. -/
theorem exists_isAbel_of_analytic_density
    {b : ℝ → ℝ}
    (hb : AnalyticOnNhd ℝ b (Set.Ioi 0))
    (hbpos : ∀ x > 0, 0 < b x)
    (hE : ∀ x > 0, b (E x) * Real.exp x = b x) :
    ∃ A : ℝ → ℝ, IsAbel A := by
  let F := densityPrimitive b
  have hFanalytic : AnalyticOnNhd ℝ F (Set.Ioi 0) :=
    densityPrimitive_analyticOnNhd hb
  have hFderiv : ∀ x > 0, deriv F x = b x := by
    intro x hx
    exact (densityPrimitive_hasDerivAt hb hx).deriv
  have hFstrict : StrictMonoOn F (Set.Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) hFanalytic.continuousOn
    intro x hx
    rw [hFderiv x (interior_subset hx)]
    exact hbpos x (interior_subset hx)
  let c := F (E 1)
  have hc : 0 < c := by
    have hlt := hFstrict (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (E_pos zero_lt_one) (lt_E zero_lt_one)
    simpa [c, F, densityPrimitive] using hlt
  let D := fun x => F (E x) - F x
  have hDderiv : ∀ x > 0, HasDerivAt D 0 x := by
    intro x hx
    have hcomp := (densityPrimitive_hasDerivAt hb (E_pos hx)).comp x
      (show HasDerivAt E (Real.exp x) x by
        change HasDerivAt (fun y : ℝ => Real.exp y - 1) (Real.exp x) x
        exact (Real.hasDerivAt_exp x).sub_const 1)
    have hsub := hcomp.sub (densityPrimitive_hasDerivAt hb hx)
    change HasDerivAt (densityPrimitive b ∘ E - densityPrimitive b) 0 x
    simpa only [hE x hx, sub_self] using hsub
  have hDdiff : DifferentiableOn ℝ D (Set.Ioi 0) := by
    intro x hx
    exact (hDderiv x hx).differentiableAt.differentiableWithinAt
  have hDconst : ∀ x > 0, D x = D 1 := by
    intro x hx
    exact (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).is_const_of_deriv_eq_zero
      (convex_Ioi (0 : ℝ)).isPreconnected hDdiff
      (fun y hy => (hDderiv y hy).deriv) hx
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
  refine ⟨fun x => F x / c, ?_⟩
  refine
    { analytic := hFanalytic.div_const
      deriv_pos := ?_
      normalized := ?_
      abel := ?_ }
  · intro x hx
    rw [((densityPrimitive_hasDerivAt hb hx).div_const c).deriv]
    exact div_pos (hbpos x hx) hc
  · simp [F, densityPrimitive]
  · intro x hx
    have hdiff : F (E x) - F x = c := by
      simpa [D, c, F, densityPrimitive] using hDconst x hx
    apply (div_eq_iff hc.ne').2
    rw [add_mul, div_mul_cancel₀ _ hc.ne', one_mul]
    linarith

end

end AbelFormalization
