import AbelFormalization.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Quantitative contraction by the principal logarithm

The complex version of `L` maps a disk about a sufficiently positive real
center into a smaller disk. The explicit bound remains valid for the first,
possibly large, disk in the construction of the paper's holomorphic extensions.
-/

noncomputable section

namespace AbelFormalization

open Set Complex

/-- The principal complex logarithmic inverse of the dynamics. -/
def complexL (z : ℂ) : ℂ := Complex.log (1 + z)

theorem complexL_ofReal {x : ℝ} (hx : 0 ≤ 1 + x) :
    complexL (x : ℂ) = (L x : ℂ) := by
  simp only [complexL, L, Complex.ofReal_log hx, Complex.ofReal_add,
    Complex.ofReal_one]

private theorem one_add_re_lower_bound {c r : ℝ} {z : ℂ}
    (hz : z ∈ Metric.ball (c : ℂ) r) :
    1 + c - r < (1 + z).re := by
  have h := Complex.re_le_norm ((c : ℂ) - z)
  have hn : ‖(c : ℂ) - z‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz
  simp only [sub_re, ofReal_re, add_re, one_re] at *
  linarith

theorem complexL_hasDerivAt {z : ℂ} (hz : 0 < (1 + z).re) :
    HasDerivAt complexL (1 + z)⁻¹ z := by
  change HasDerivAt (fun w : ℂ => Complex.log (1 + w)) (1 + z)⁻¹ z
  simpa only [one_div, id_eq] using
    ((hasDerivAt_id z).const_add 1).clog (Or.inl hz)

theorem complexL_analyticAt {z : ℂ} (hz : 0 < (1 + z).re) :
    AnalyticAt ℂ complexL z :=
  (analyticAt_const.add analyticAt_id).clog (Or.inl hz)

/-- The derivative estimate on a disk gives the precise logarithmic
contraction factor `1 / (1 + c - r)`. -/
theorem norm_complexL_sub_le {c r : ℝ} (hr : 0 < r) (hc : r < 1 + c)
    {z : ℂ} (hz : z ∈ Metric.ball (c : ℂ) r) :
    ‖complexL z - complexL (c : ℂ)‖ ≤ ‖z - (c : ℂ)‖ / (1 + c - r) := by
  have hd : 0 < 1 + c - r := sub_pos.mpr hc
  have hder : ∀ w ∈ Metric.ball (c : ℂ) r,
      HasDerivWithinAt complexL (1 + w)⁻¹ (Metric.ball (c : ℂ) r) w := by
    intro w hw
    exact (complexL_hasDerivAt (hd.trans (one_add_re_lower_bound hw))).hasDerivWithinAt
  have hbound : ∀ w ∈ Metric.ball (c : ℂ) r, ‖(1 + w)⁻¹‖ ≤ (1 + c - r)⁻¹ := by
    intro w hw
    rw [norm_inv]
    have hl := (one_add_re_lower_bound hw).le.trans (Complex.re_le_norm _)
    exact (inv_le_inv₀ (hd.trans_le hl) hd).mpr hl
  have h := (convex_ball (c : ℂ) r).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (Metric.mem_ball_self hr) hz
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem complexL_mapsTo_ball {c r : ℝ} (hr : 0 < r) (hc : r < 1 + c) :
    MapsTo complexL (Metric.ball (c : ℂ) r)
      (Metric.ball (complexL (c : ℂ)) (r / (1 + c - r))) := by
  intro z hz
  apply (Metric.mem_ball).mpr
  rw [dist_eq_norm]
  exact (norm_complexL_sub_le hr hc hz).trans_lt
    ((div_lt_div_iff_of_pos_right (sub_pos.mpr hc)).mpr
      (by simpa only [Metric.mem_ball, dist_eq_norm] using hz))

theorem complexL_analyticOnNhd_ball {c r : ℝ} (hc : r < 1 + c) :
    AnalyticOnNhd ℂ complexL (Metric.ball (c : ℂ) r) := by
  intro z hz
  exact complexL_analyticAt ((sub_pos.mpr hc).trans (one_add_re_lower_bound hz))

end AbelFormalization
