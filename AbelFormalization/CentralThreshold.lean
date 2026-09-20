import AbelFormalization.CentralBounds

/-! # One threshold for every central interpolation constraint -/

namespace AbelFormalization

open Filter
open scoped Topology

/-- A common real threshold simultaneously puts the center in its analytic
strip, the original argument in its extension range, and the exponential
scale inside both required disks. All inequalities persist above it. -/
theorem exists_central_threshold (X U B : ℝ) {ε : ℝ} (hε : 0 < ε) (_hB : 0 < B) :
    ∃ u₀ : ℝ, 0 < u₀ ∧ U < u₀ ∧
      ∀ u : ℝ, u₀ ≤ u →
        0 < u ∧ U < u ∧ X < E u ∧ Real.exp (-u) < ε ∧
          Real.exp (-u) * (B + 1) < 1 / 4 := by
  have he : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hscaled : Tendsto (fun u : ℝ => Real.exp (-u) * (B + 1)) atTop (𝓝 0) := by
    simpa using he.mul_const (B + 1)
  have htail : ∀ᶠ u : ℝ in atTop,
      0 < u ∧ U < u ∧ X < E u ∧ Real.exp (-u) < ε ∧
        Real.exp (-u) * (B + 1) < 1 / 4 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop U,
      eventually_gt_atTop X, he.eventually (gt_mem_nhds hε),
      hscaled.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with u hu hU hX he hscale
    exact ⟨hu, hU, hX.trans (lt_E hu), he, hscale⟩
  obtain ⟨u₀, hu₀⟩ := eventually_atTop.mp htail
  exact ⟨u₀, (hu₀ u₀ le_rfl).1, (hu₀ u₀ le_rfl).2.1, hu₀⟩

end AbelFormalization
