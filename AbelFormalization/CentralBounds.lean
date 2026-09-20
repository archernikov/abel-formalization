import AbelFormalization.CentralJet

/-!
# Uniform complex bounds for the central interpolation function

The center and the interpolation argument vary independently. A fixed
half-strip for the center and a fixed disk for the argument suffice for
joint analyticity and a uniform polynomial bound of degree one.
-/

noncomputable section

namespace AbelFormalization

open Set Metric

theorem norm_complexL_lt_one {η : ℂ} (hη : ‖η‖ < 1 / 2) :
    ‖complexL η‖ < 1 := by
  have h := norm_complexL_sub_le (c := 0) (r := 1 / 2)
    (by norm_num) (by norm_num) (z := η) (by simpa using hη)
  have hbound : ‖complexL η‖ ≤ 2 * ‖η‖ := by
    norm_num [complexL, div_eq_mul_inv] at h ⊢
    simpa [mul_comm] using h
  linarith

theorem central_argument_mem_strip {X : ℝ} {u η : ℂ}
    (hu : u ∈ rightHalfStrip (X + 1) 1) (hη : ‖η‖ < 1 / 2) :
    u + complexL η ∈ rightHalfStrip X 2 := by
  have hn := norm_complexL_lt_one hη
  have hre := (Complex.abs_re_le_norm (complexL η)).trans_lt hn
  have him := (Complex.abs_im_le_norm (complexL η)).trans_lt hn
  constructor
  · simp only [Complex.add_re]
    have hl := (abs_lt.mp hre).1
    linarith [hu.1]
  · simp only [Complex.add_im]
    exact (abs_add_le _ _).trans_lt (by linarith [hu.2])

theorem centralComplexFunction_joint_analyticOnNhd {X : ℝ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F (rightHalfStrip X 2)) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => centralComplexFunction F p.1 p.2)
      (rightHalfStrip (X + 1) 1 ×ˢ ball 0 (1 / 2)) := by
  intro p hp
  have hη : ‖p.2‖ < 1 / 2 := by simpa using hp.2
  have hpos : 0 < (1 + p.2).re := by
    have h := (Complex.abs_re_le_norm p.2).trans_lt hη
    simp only [Complex.add_re, Complex.one_re]
    have hl := (abs_lt.mp h).1
    linarith
  have hinner : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1 + complexL p.2) p :=
    analyticAt_fst.add ((complexL_analyticAt hpos).comp analyticAt_snd)
  have hb := hF _ (central_argument_mem_strip hp.1 hη)
  have hc := hb.comp (f := fun p : ℂ × ℂ => p.1 + complexL p.2) hinner
  exact analyticAt_const.add hc

theorem centralComplexFunction_norm_le {X K : ℝ} {F : ℂ → ℂ}
    (hX : 1 < X) (hK : 0 < K)
    (hF : ∀ z ∈ rightHalfStrip X 2, ‖F z‖ ≤ K * Real.log z.re)
    {u η : ℂ} (hu : u ∈ rightHalfStrip (X + 1) 1) (hη : ‖η‖ < 1 / 2) :
    ‖centralComplexFunction F u η‖ ≤ (1 + K) * (1 + u.re) := by
  have hz := central_argument_mem_strip hu hη
  have hpos : 0 < (u + complexL η).re := lt_trans (by linarith) hz.1
  have hlog := Real.log_le_sub_one_of_pos hpos
  have hre := (Complex.re_le_norm (complexL η)).trans_lt (norm_complexL_lt_one hη)
  have hlog' : Real.log (u + complexL η).re ≤ u.re := by
    simp only [Complex.add_re] at hlog ⊢
    linarith
  calc
    ‖centralComplexFunction F u η‖ ≤ 1 + ‖F (u + complexL η)‖ := by
      simpa [centralComplexFunction] using norm_add_le (1 : ℂ) (F (u + complexL η))
    _ ≤ 1 + K * Real.log (u + complexL η).re := add_le_add le_rfl (hF _ hz)
    _ ≤ 1 + K * u.re := add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog' hK.le)
    _ ≤ (1 + K) * (1 + u.re) := by nlinarith [hu.1]

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)
include hA

/-- Uniform joint complex analyticity and a polynomial bound for the
auxiliary function in a fixed strip and disk. -/
theorem exists_bounded_centralComplexFunction :
    ∃ u₀ K : ℝ, ∃ F : ℂ → ℂ, 0 < u₀ ∧ 0 < K ∧
      AnalyticOnNhd ℂ F (rightHalfStrip u₀ 1) ∧
      (∀ u : ℝ, u₀ < u → F (u : ℂ) = (A u : ℂ)) ∧
      AnalyticOnNhd ℂ (fun p : ℂ × ℂ => centralComplexFunction F p.1 p.2)
        (rightHalfStrip u₀ 1 ×ˢ ball 0 (1 / 2)) ∧
      ∀ u ∈ rightHalfStrip u₀ 1, ∀ η : ℂ, ‖η‖ < 1 / 2 →
        ‖centralComplexFunction F u η‖ ≤ K * (1 + u.re) := by
  obtain ⟨X, K, F, hX, hK, hF, he, hb⟩ :=
    hA.exists_bounded_complex_strip (M := 2) (by norm_num)
  refine ⟨X + 1, 1 + K, F, by linarith, by linarith, ?_, ?_,
    centralComplexFunction_joint_analyticOnNhd hF, ?_⟩
  · intro u hu
    exact hF u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · intro u hu
    exact he u (by linarith)
  · intro u hu η hη
    exact centralComplexFunction_norm_le hX hK hb hu hη

end IsAbel
end AbelFormalization
