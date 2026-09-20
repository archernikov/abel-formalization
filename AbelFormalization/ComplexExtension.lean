import AbelFormalization.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Complex.Basic

/-!
# Local complex extensions of real analytic functions

We complexify the scalar coefficients of a real power series. Their norms,
and hence their radius of convergence, are preserved. This supplies the local
holomorphic extensions needed before the compact-interval construction in the
paper's analytic-input lemma.
-/

noncomputable section

namespace AbelFormalization

open Filter Set FormalMultilinearSeries
open scoped Topology

/-- A real analytic function has a local complex analytic extension. -/
theorem exists_complex_extension_of_analyticAt {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F (x : ℂ) ∧
      ∀ᶠ y : ℝ in 𝓝 x, F (y : ℂ) = (f y : ℂ) := by
  obtain ⟨p, r, hr⟩ := hf
  let q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => (p.coeff n : ℂ))
  have hrad : p.radius ≤ q.radius := by
    apply FormalMultilinearSeries.radius_le_of_le
    intro n
    simp [q]
  have hq : 0 < q.radius := (hr.r_pos.trans_le hr.r_le).trans_le hrad
  refine ⟨fun z => q.sum (z - (x : ℂ)), ?_, ?_⟩
  · simpa only [zero_add] using
      (q.hasFPowerSeriesOnBall hq).analyticAt.comp_sub (x : ℂ)
  · filter_upwards [hr.eventually_hasSum_sub] with y hy
    have hs := Complex.hasSum_ofReal.mpr hy
    change q.sum ((y : ℂ) - (x : ℂ)) = (f y : ℂ)
    rw [FormalMultilinearSeries.sum]
    convert hs.tsum_eq using 1
    apply tsum_congr
    intro n
    simp [q, smul_eq_mul,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow, mul_comm]

/-- A disk version, with analyticity at every point and agreement on its real
diameter. The disk radius and the extension are both constructed from `hf`. -/
theorem exists_complex_extension_on_ball_of_analyticAt {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (Metric.ball (x : ℂ) r) ∧
        ∀ y : ℝ, y ∈ Metric.ball x r → F (y : ℂ) = (f y : ℂ) := by
  obtain ⟨F, hF, he⟩ := exists_complex_extension_of_analyticAt hf
  obtain ⟨r₁, hr₁, h₁⟩ := Metric.eventually_nhds_iff.mp hF.eventually_analyticAt
  obtain ⟨r₂, hr₂, h₂⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, F, ?_, ?_⟩
  · intro z hz
    exact h₁ (lt_of_lt_of_le hz (min_le_left r₁ r₂))
  · intro y hy
    exact h₂ (lt_of_lt_of_le hy (min_le_right r₁ r₂))

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem exists_complex_extension {x : ℝ} (hx : 0 < x) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ F (Metric.ball (x : ℂ) r) ∧
        ∀ y : ℝ, y ∈ Metric.ball x r → F (y : ℂ) = (A y : ℂ) :=
  exists_complex_extension_on_ball_of_analyticAt (hA.analytic x hx)

end IsAbel

end AbelFormalization
