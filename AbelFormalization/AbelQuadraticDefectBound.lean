import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Bounding the vanishing logarithmic density defect

A holomorphic function whose value and first derivative vanish at zero is
bounded by a constant times the squared norm in a neighbourhood of zero.
This is the local estimate used in the Abel density series.
-/

noncomputable section

namespace AbelFormalization

open Set Filter
open scoped Topology

theorem exists_quadratic_bound_of_analytic_zero {h : ℂ → ℂ}
    (ha : AnalyticAt ℂ h 0) (h0 : h 0 = 0) (hd0 : deriv h 0 = 0) :
    ∃ R > 0, ∃ C ≥ 0,
      AnalyticOnNhd ℂ h {z | 0 < ‖z‖ ∧ ‖z‖ < R} ∧
      (∀ z, 0 < ‖z‖ → ‖z‖ < R → ‖h z‖ ≤ C * ‖z‖ ^ 2) := by
  let q : ℂ → ℂ := dslope (dslope h 0) 0
  have hqa : AnalyticAt ℂ q 0 := by
    obtain ⟨p, hp⟩ := ha
    exact ⟨p.fslope.fslope,
      hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope⟩
  have hfactor (z : ℂ) : h z = z ^ 2 * q z := by
    have hfirst : z * dslope h 0 z = h z := by
      simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope_of_zero h0 z
    have hsecond : z * q z = dslope h 0 z := by
      simpa only [sub_zero, smul_eq_mul] using
        sub_smul_dslope_of_zero (f := dslope h 0) (a := (0 : ℂ))
          (by simpa only [dslope_same] using hd0) z
    rw [← hfirst, ← hsecond]
    ring
  let C := ‖q 0‖ + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hqbound : ∀ᶠ z in 𝓝 (0 : ℂ), ‖q z‖ < C :=
    hqa.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [C]; linarith))
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp
    (ha.eventually_analyticAt.and hqbound)
  refine ⟨R, hR, C, hC, ?_, ?_⟩
  · intro z hz
    exact (hball (by simpa only [dist_zero_right] using hz.2)).1
  · intro z _ hz
    have hqz : ‖q z‖ ≤ C :=
      (hball (by simpa only [dist_zero_right] using hz)).2.le
    rw [hfactor, norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right hqz (sq_nonneg _)

end AbelFormalization
