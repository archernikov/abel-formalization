import AbelFormalization.CentralIdentity
import AbelFormalization.CentralCoefficientBounds
import AbelFormalization.HermiteScaling

/-! # Substituting the exponential scale into the central coefficients

The original and central contour constructions may use different complex
extensions and different contour radii.  Analytic uniqueness and Hermite
scaling identify their coefficients.  Substitution of the central zero-scale
jet then gives the exact signed-Stirling plus scale-remainder identity.
-/

noncomputable section

open Set Filter Metric Polynomial
open scoped Topology

namespace AbelFormalization

/-- A radius inequality places the entire rescaled closed disk inside the
open target disk. -/
theorem exp_neg_mul_mem_ball {u R ρ : ℝ} (hscale : Real.exp (-u) * R < ρ)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    (Real.exp (-u) : ℂ) * z ∈ ball (0 : ℂ) ρ := by
  have hzn : ‖z‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hz
  rw [mem_ball, dist_zero_right, norm_mul,
    Complex.norm_of_nonneg (Real.exp_pos (-u)).le]
  exact (mul_le_mul_of_nonneg_left hzn (Real.exp_pos (-u)).le).trans_lt hscale

theorem centralComplexFunction_rescale_analyticOnNhd {F : ℂ → ℂ} {u R ρ : ℝ}
    (hH : AnalyticOnNhd ℂ (centralComplexFunction F (u : ℂ)) (closedBall (0 : ℂ) ρ))
    (hscale : Real.exp (-u) * R < ρ) :
    AnalyticOnNhd ℂ (fun z : ℂ =>
      centralComplexFunction F (u : ℂ) ((Real.exp (-u) : ℂ) * z))
      (closedBall (0 : ℂ) R) := by
  intro z hz
  exact (hH _ (ball_subset_closedBall (exp_neg_mul_mem_ball hscale hz))).fun_comp
    (f := fun z : ℂ => (Real.exp (-u) : ℂ) * z)
    (analyticAt_const.fun_mul analyticAt_id)

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)
include hA

/-- The normalized coefficients of the original Hermite interpolant are the
central coefficients at the actual exponential scale, multiplied by its
corresponding power. Local real agreement of each complex branch is explicit. -/
theorem centralCoefficient_rescale {ι : Type*} [Fintype ι]
    (δ : ι → ℂ) (m : ι → ℕ) {F G : ℂ → ℂ} {u R ρ : ℝ}
    (hu : 0 < u) (hR : 0 < R)
    (hF : AnalyticAt ℂ F (u : ℂ)) (hG : AnalyticAt ℂ G (E u : ℂ))
    (heF : (fun y : ℝ => F (y : ℂ)) =ᶠ[𝓝 u] fun y => (A y : ℂ))
    (heG : (fun y : ℝ => G (y : ℂ)) =ᶠ[𝓝 (E u)] fun y => (A y : ℂ))
    (hGshift : AnalyticOnNhd ℂ (fun z : ℂ => G ((E u : ℂ) + z))
      (closedBall (0 : ℂ) R))
    (hH : AnalyticOnNhd ℂ (centralComplexFunction F (u : ℂ)) (closedBall (0 : ℂ) ρ))
    (hscale : Real.exp (-u) * R < ρ)
    (hδ : ∀ i, δ i ∈ ball (0 : ℂ) R) (hd : 0 < totalMultiplicity m) (r : ℕ) :
    normalizedCoeff (hermiteContourPolynomial (fun z : ℂ => G ((E u : ℂ) + z))
      (nodePolynomial δ m) R) r =
      (Real.exp (-u) : ℂ) ^ r *
        centralCoefficient F m ρ (u : ℂ) (Real.exp (-u) : ℂ) δ r := by
  have hρ : 0 < ρ := (mul_pos (Real.exp_pos (-u)) hR).trans hscale
  have hq : (Real.exp (-u) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (-u)
  have hright := centralComplexFunction_rescale_analyticOnNhd hH hscale
  have heq := hA.centralComplexFunction_rescale_eqOn hu hF hG heF heG
    (U := ball (0 : ℂ) R) (convex_ball (0 : ℂ) R).isPreconnected (mem_ball_self hR)
    (hGshift.mono ball_subset_closedBall) (hright.mono ball_subset_closedBall)
  have hlocal : ∀ i, (fun z : ℂ => G ((E u : ℂ) + z)) =ᶠ[𝓝 (δ i)]
      fun z => centralComplexFunction F (u : ℂ) ((Real.exp (-u) : ℂ) * z) := by
    intro i
    exact heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds (hδ i))
  have hqδ : ∀ i, (Real.exp (-u) : ℂ) * δ i ∈ ball (0 : ℂ) ρ :=
    fun i => exp_neg_mul_mem_ball hscale (ball_subset_closedBall (hδ i))
  exact hermiteContour_normalizedCoeff_scale δ m hq hR hρ hGshift hH hδ hqδ hd hlocal r

/-- The exact central Hermite coefficient identity from the manuscript. The
remainder is the analytic divided difference in the independent scale; the
specialization `q = exp(-u)` is made only in this identity. -/
theorem normalizedHermiteCoeff_stirling_remainder {ι : Type*} [Fintype ι]
    (δ : ι → ℂ) (m : ι → ℕ) {F G : ℂ → ℂ} {u R : ℝ}
    (hu : 0 < u) (hR : 0 < R)
    (hF : AnalyticAt ℂ F (u : ℂ)) (hG : AnalyticAt ℂ G (E u : ℂ))
    (heF : (fun y : ℝ => F (y : ℂ)) =ᶠ[𝓝 u] fun y => (A y : ℂ))
    (heG : (fun y : ℝ => G (y : ℂ)) =ᶠ[𝓝 (E u)] fun y => (A y : ℂ))
    (hGshift : AnalyticOnNhd ℂ (fun z : ℂ => G ((E u : ℂ) + z))
      (closedBall (0 : ℂ) R))
    (hH : AnalyticOnNhd ℂ (centralComplexFunction F (u : ℂ))
      (closedBall (0 : ℂ) (1 / 4)))
    (hscale : Real.exp (-u) * R < 1 / 4)
    (hδ : ∀ i, δ i ∈ ball (0 : ℂ) R)
    {r : ℕ} (hr : 1 ≤ r) (hrd : r < totalMultiplicity m) :
    normalizedCoeff (hermiteContourPolynomial (fun z : ℂ => G ((E u : ℂ) + z))
      (nodePolynomial δ m) R) r =
      (Real.exp (-u) : ℂ) ^ r *
        ((∑ j ∈ Finset.range (r + 1), (signedStirling r j : ℂ) *
          ((iteratedDeriv j A u : ℝ) : ℂ)) +
          (Real.exp (-u) : ℂ) *
            centralRemainder F m (1 / 4) (u : ℂ) (Real.exp (-u) : ℂ) δ r) := by
  rw [hA.centralCoefficient_rescale δ m hu hR hF hG heF heG hGshift hH hscale hδ
    ((Nat.zero_le r).trans_lt hrd) r]
  rw [centralRemainder_identity F m (1 / 4) (u : ℂ) (Real.exp (-u) : ℂ) δ r]
  rw [hA.centralCoefficient_zero_scale_stirling m (by norm_num) hu hF heF hH δ hr hrd]

end IsAbel
end AbelFormalization
