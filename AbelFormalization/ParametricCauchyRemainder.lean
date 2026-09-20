import AbelFormalization.HermiteContour
import AbelFormalization.AnalyticCircleParameter

/-! # A Cauchy remainder with independent complex parameters

The contour representation of the first divided difference is holomorphic
jointly in all parameters and the difference variable. We express
multivariate holomorphy by complex Fréchet differentiability.
-/

noncomputable section

namespace AbelFormalization

open Set Metric Polynomial

/-- The Cauchy quotient for the polynomial `X` is a first-order remainder. -/
theorem hermiteContourQuotient_X_identity {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) ρ))
    {q : ℂ} (hq : q ∈ ball (0 : ℂ) ρ) :
    f q = f 0 + q * hermiteContourQuotient f X ρ q := by
  have hX : ∀ ζ ∈ sphere (0 : ℂ) ρ, (X : ℂ[X]).eval ζ ≠ 0 := by
    intro ζ hζ
    simp only [eval_X]
    intro he
    have hn : ‖ζ‖ = ρ := by simpa using hζ
    rw [he, norm_zero] at hn
    linarith
  have hd : 0 < (X : ℂ[X]).natDegree := by simp
  have hdeg : (hermiteContourPolynomial f X ρ).natDegree = 0 := by
    have h := hermiteContourPolynomial_natDegree_lt f X ρ hd
    simpa only [natDegree_X, Nat.lt_one_iff] using h
  have hP := eq_C_of_natDegree_eq_zero hdeg
  have h0 := hermiteContour_remainder hρ hf hX hd (mem_ball_self hρ)
  rw [hP] at h0
  simp only [eval_C, eval_X, zero_mul, sub_eq_zero] at h0
  have hq' := hermiteContour_remainder hρ hf hX hd hq
  rw [hP] at hq'
  simp only [eval_C, eval_X, ← h0] at hq'
  linear_combination hq'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]

/-- An explicit remainder with a fixed contour, including at zero scale. -/
def parameterCauchyRemainder (f : E × ℂ → ℂ) (ρ : ℝ) (p : E) (q : ℂ) : ℂ :=
  hermiteContourQuotient (fun ζ => f (p, ζ)) X ρ q

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E] in
theorem parameterCauchyRemainder_identity {f : E × ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) {p : E}
    (hf : AnalyticOnNhd ℂ (fun ζ => f (p, ζ)) (closedBall (0 : ℂ) ρ))
    {q : ℂ} (hq : q ∈ ball (0 : ℂ) ρ) :
    f (p, q) = f (p, 0) + q * parameterCauchyRemainder f ρ p q :=
  hermiteContourQuotient_X_identity hρ hf hq

/-- Joint holomorphy in all independent parameters and in the scale variable. -/
theorem differentiableOn_parameterCauchyRemainder {f : E × ℂ → ℂ} {U : Set E}
    {ρ : ℝ} (hU : IsOpen U) (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (U ×ˢ closedBall (0 : ℂ) ρ)) :
    DifferentiableOn ℂ (fun p : E × ℂ => parameterCauchyRemainder f ρ p.1 p.2)
      (U ×ˢ ball (0 : ℂ) ρ) := by
  have ha : AnalyticOnNhd ℂ
      (fun v : (E × ℂ) × ℂ => f (v.1.1, v.2) / (v.2 * (v.2 - v.1.2)))
      ((U ×ˢ ball (0 : ℂ) ρ) ×ˢ sphere (0 : ℂ) ρ) := by
    intro v hv
    have hfst : AnalyticAt ℂ (fun w : (E × ℂ) × ℂ => w.1.1) v :=
      analyticAt_fst.comp (f := fun w : (E × ℂ) × ℂ => w.1) analyticAt_fst
    have hsnd : AnalyticAt ℂ (fun w : (E × ℂ) × ℂ => w.1.2) v :=
      analyticAt_snd.comp (f := fun w : (E × ℂ) × ℂ => w.1) analyticAt_fst
    have hnum := (hf (v.1.1, v.2) ⟨hv.1.1, sphere_subset_closedBall hv.2⟩).comp
      (f := fun w : (E × ℂ) × ℂ => (w.1.1, w.2)) (hfst.prod analyticAt_snd)
    have hζ : v.2 ≠ 0 := by
      intro he
      have hn : ‖v.2‖ = ρ := by simpa using hv.2
      rw [he, norm_zero] at hn
      linarith
    exact hnum.div (analyticAt_snd.mul (analyticAt_snd.sub hsnd))
      (mul_ne_zero hζ (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hv.2 hv.1.2)))
  have h := differentiableOn_circleIntegral_of_analyticOnNhd
    (hU.prod isOpen_ball) hρ.le ha
  simpa only [parameterCauchyRemainder, hermiteContourQuotient, eval_X] using
    (h.const_mul cauchyNormalization : DifferentiableOn ℂ
      (fun p : E × ℂ => cauchyNormalization *
        ∮ ζ in C(0, ρ), f (p.1, ζ) / (ζ * (ζ - p.2)))
      (U ×ˢ ball (0 : ℂ) ρ))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E] in
/-- A fixed contour gives a uniform remainder bound on its inner half disk. -/
theorem norm_parameterCauchyRemainder_le {f : E × ℂ → ℂ} {ρ S : ℝ}
    (hρ : 0 < ρ) (hS : 0 ≤ S) {p : E}
    (hf : ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖f (p, ζ)‖ ≤ S)
    {q : ℂ} (hq : ‖q‖ ≤ ρ / 2) :
    ‖parameterCauchyRemainder f ρ p q‖ ≤ 2 * S / ρ := by
  have hb : ∀ ζ ∈ sphere (0 : ℂ) ρ,
      ‖f (p, ζ) / (ζ * (ζ - q))‖ ≤ S / (ρ * (ρ / 2)) := by
    intro ζ hζ
    have hn : ‖ζ‖ = ρ := by simpa using hζ
    have hgap : ρ / 2 ≤ ‖ζ - q‖ := by
      have ht := norm_sub_norm_le ζ q
      rw [hn] at ht
      linarith
    have hden : ρ * (ρ / 2) ≤ ‖ζ * (ζ - q)‖ := by
      rw [norm_mul, hn]
      exact mul_le_mul_of_nonneg_left hgap hρ.le
    rw [norm_div]
    exact div_le_div₀ hS (hf ζ hζ)
      (mul_pos hρ (half_pos hρ)) hden
  have h := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ.le hb
  have he : ρ * (S / (ρ * (ρ / 2))) = 2 * S / ρ := by
    field_simp
  simpa only [parameterCauchyRemainder, hermiteContourQuotient, cauchyNormalization,
    eval_X, smul_eq_mul, he] using h

end AbelFormalization
