import AbelFormalization.AbelDensitySeries
import AbelFormalization.AbelLogBounds

/-!
# A local density from the quadratic logarithmic defect

The complex logarithm of the density ratio vanishes to second order at zero.
Summing it along logarithmic iterates gives an analytic positive density.
-/

noncomputable section

namespace AbelFormalization

open Set Function

private theorem norm_bounds_half_ball {x : ℝ} (hx : 0 < x) {z : ℂ}
    (hz : z ∈ Metric.ball (x : ℂ) (x / 2)) :
    0 < ‖z‖ ∧ ‖z‖ < 3 * x / 2 := by
  have hdist : ‖z - (x : ℂ)‖ < x / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hnorm : ‖(x : ℂ)‖ = x := by simp [abs_of_pos hx]
  constructor
  · apply norm_pos_iff.mpr
    intro he
    rw [he, zero_sub, norm_neg, hnorm] at hdist
    linarith
  · calc
      ‖z‖ ≤ ‖z - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_le_norm_sub_add _ _
      _ < x / 2 + x := by rw [hnorm]; linarith
      _ = 3 * x / 2 := by ring

/-- The local analytic estimate needed to construct the Abel density. -/
theorem exists_local_density_of_log_defect {h : ℂ → ℂ} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (ha : AnalyticOnNhd ℂ h {z | 0 < ‖z‖ ∧ ‖z‖ < R})
    (hbound : ∀ z, 0 < ‖z‖ → ‖z‖ < R → ‖h z‖ ≤ C * ‖z‖ ^ 2)
    (hreal : ∀ x : ℝ, 0 < x → x < R →
      (h (x : ℂ)).re = Real.log (x ^ 2 / ((1 + x) * (L x) ^ 2))) :
    ∃ ε > 0, ∃ b : ℝ → ℝ, AnalyticOnNhd ℝ b (Ioo 0 ε) ∧
      (∀ x ∈ Ioo 0 ε, 0 < b x) ∧
      (∀ x ∈ Ioo 0 ε, b (L x) / (1 + x) = b x) := by
  let ε := min 1 (R / 2)
  have hε : 0 < ε := lt_min zero_lt_one (half_pos hR)
  have hdata (x : ℝ) (hx : x ∈ Ioo 0 ε) :
      AnalyticAt ℂ (logDensitySum h) (x : ℂ) ∧
      Summable (fun n : ℕ => h (complexL^[n] (x : ℂ))) := by
    have hx1 : x ≤ 1 := hx.2.le.trans (min_le_left _ _)
    have hxR : 3 * x / 2 < R := by
      have ht : x < R / 2 := hx.2.trans_le (min_le_right _ _)
      linarith
    let D := Metric.ball (x : ℂ) (x / 2)
    have hD : (x : ℂ) ∈ D := Metric.mem_ball_self (half_pos hx.1)
    have horbit (n : ℕ) (z : ℂ) (hz : z ∈ D) :
        0 < ‖complexL^[n] z‖ ∧ ‖complexL^[n] z‖ < R ∧
          ‖complexL^[n] z‖ ≤ 6 / ((n : ℝ) + 1) := by
      have hn := norm_bounds_half_ball (L_iterate_pos hx.1 n)
        (complexL_iterate_mapsTo_half_ball hx.1 n hz)
      refine ⟨hn.1, ?_, ?_⟩
      · have hle : 3 * L^[n] x / 2 ≤ 3 * x / 2 := by
          have := L_iterate_le_self hx.1 n
          linarith
        exact hn.2.trans (hle.trans_lt hxR)
      · calc
          ‖complexL^[n] z‖ ≤ 3 * L^[n] x / 2 := hn.2.le
          _ ≤ 3 * (4 / ((n : ℝ) + 1)) / 2 := by
            have := L_iterate_le_four_div hx.1 hx1 n
            linarith
          _ = 6 / ((n : ℝ) + 1) := by ring
    have hmajor (n : ℕ) (z : ℂ) (hz : z ∈ D) :
        ‖h (complexL^[n] z)‖ ≤ (36 * C) / ((n : ℝ) + 1) ^ 2 := by
      have hn := horbit n z hz
      calc
        ‖h (complexL^[n] z)‖ ≤ C * ‖complexL^[n] z‖ ^ 2 :=
          hbound _ hn.1 hn.2.1
        _ ≤ C * (6 / ((n : ℝ) + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn.2.2 _) hC
        _ = (36 * C) / ((n : ℝ) + 1) ^ 2 := by rw [div_pow]; ring
    have han (n : ℕ) : AnalyticOnNhd ℂ (fun z => h (complexL^[n] z)) D := by
      intro z hz
      exact (ha _ ⟨(horbit n z hz).1, (horbit n z hz).2.1⟩).comp
        (complexL_iterate_analyticOnNhd_half_ball hx.1 n z hz)
    exact ⟨analyticOnNhd_logDensitySum_of_bound Metric.isOpen_ball han hmajor _ hD,
      summable_logDensityTerms_of_bound (fun n => hmajor n _ hD)⟩
  refine ⟨ε, hε, densityFromLogDefect h, ?_, ?_, ?_⟩
  · intro x hx
    exact analyticAt_densityFromLogDefect hx.1 (hdata x hx).1
  · intro x hx
    exact densityFromLogDefect_pos h hx.1
  · intro x hx
    apply densityFromLogDefect_invariant hx.1 (hdata x hx).2
    apply hreal x hx.1
    exact (hx.2.trans_le (min_le_right _ _)).trans (by linarith)

end AbelFormalization
