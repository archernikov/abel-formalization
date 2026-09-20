import AbelFormalization.CommonStripHermiteAnalytic
import AbelFormalization.CentralCoefficientBounds

noncomputable section

set_option autoImplicit false

open Set Filter Metric Polynomial
open scoped Topology

namespace AbelFormalization

variable {ι : Type*} [Fintype ι]

private theorem commonStrip_ball_subset
    {X B x : ℝ} (hx : X + B + 3 < x) :
    ball (x : ℂ) (B + 2) ⊆ rightHalfStrip X (B + 2) := by
  intro z hz
  have hn : ‖z - (x : ℂ)‖ < B + 2 := by
    simpa only [mem_ball, dist_eq_norm] using hz
  have hre : |z.re - x| < B + 2 := by
    have h := (Complex.abs_re_le_norm (z - (x : ℂ))).trans_lt hn
    simpa only [Complex.sub_re, Complex.ofReal_re] using h
  have him : |z.im| < B + 2 := by
    have h := (Complex.abs_im_le_norm (z - (x : ℂ))).trans_lt hn
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using h
  exact ⟨by linarith [(abs_lt.mp hre).1], him⟩

private theorem commonStrip_real_mem
    {X B x y : ℝ} (hx : X + B + 3 < x)
    (hy : y ∈ ball x (B + 2)) : X < y := by
  have hd : |y - x| < B + 2 := by
    simpa only [mem_ball, Real.dist_eq] using hy
  linarith [(abs_lt.mp hd).1]

private theorem commonStrip_log_bound
    {X B K x : ℝ} (hX : 1 < X) (hB : 0 < B) (hK : 0 < K)
    (hx : X + B + 3 < x) {z : ℂ}
    (hz : z ∈ ball (x : ℂ) (B + 2))
    {t : ℝ} (hb : t <= K * Real.log z.re) :
    t <= (2 * K) * Real.log x := by
  have hn : ‖z - (x : ℂ)‖ < B + 2 := by
    simpa only [mem_ball, dist_eq_norm] using hz
  have hre : |z.re - x| < B + 2 := by
    have h := (Complex.abs_re_le_norm (z - (x : ℂ))).trans_lt hn
    simpa only [Complex.sub_re, Complex.ofReal_re] using h
  have hzpos : 0 < z.re := by
    linarith [(abs_lt.mp hre).1]
  have hxpos : 0 < x := by linarith
  have hzlt : z.re < 2 * x := by
    have hu := (abs_lt.mp hre).2
    linarith
  have hlogz : Real.log z.re <= Real.log (2 * x) :=
    Real.log_le_log hzpos hzlt.le
  have hlogmul : Real.log (2 * x) = Real.log 2 + Real.log x := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hxpos)]
  have hlog2 : Real.log 2 <= Real.log x :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogs : Real.log z.re <= 2 * Real.log x := by
    rw [hlogmul] at hlogz
    linarith
  calc
    t <= K * Real.log z.re := hb
    _ <= K * (2 * Real.log x) :=
      mul_le_mul_of_nonneg_left hlogs hK.le
    _ = (2 * K) * Real.log x := by ring

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- A uniform Abel--Hermite family can be chosen from one common complex
extension. The fixed extension is exposed for joint center/node analyticity. -/
theorem exists_commonStrip_abelHermiteFamily
    {B : ℝ} (hB : 0 < B) (m : ι → ℕ)
    (hd : 0 < totalMultiplicity m) :
    ∃ X K K0 : ℝ, ∃ F : ℂ → ℂ,
      1 < X ∧
      AnalyticOnNhd ℂ F (rightHalfStrip X (B + 2)) ∧
      (∀ x : ℝ, X < x → F (x : ℂ) = (A x : ℂ)) ∧
      AbelHermiteFamilySpec A B m (X + B + 3) K K0 (fun _ => F) := by
  obtain ⟨X, K, F, hX, hK, hF, hreal, hbound⟩ :=
    hA.exists_bounded_complex_strip (M := B + 2) (by linarith)
  obtain ⟨D, hD, hcoeff⟩ :=
    exists_uniform_hermiteContour_coeff_bounds B m hB.le
  let X0 : ℝ := X + B + 3
  let K' : ℝ := 2 * K
  have hX0 : 1 < X0 := by dsimp [X0]; linarith
  have hK' : 0 < K' := by dsimp [K']; positivity
  have hball : ∀ x : ℝ, X0 < x →
      ball (x : ℂ) (B + 2) ⊆ rightHalfStrip X (B + 2) := by
    intro x hx
    exact commonStrip_ball_subset (by simpa only [X0] using hx)
  have hbranchAnalytic : ∀ x : ℝ, X0 < x →
      AnalyticOnNhd ℂ F (ball (x : ℂ) (B + 2)) := by
    intro x hx
    exact hF.mono (hball x hx)
  have hbranchReal : ∀ x : ℝ, X0 < x →
      ∀ y : ℝ, y ∈ ball x (B + 2) → F (y : ℂ) = (A y : ℂ) := by
    intro x hx y hy
    exact hreal y (commonStrip_real_mem (by simpa only [X0] using hx) hy)
  have hbranchBound : ∀ x : ℝ, X0 < x →
      ∀ z ∈ ball (x : ℂ) (B + 2), ‖F z‖ <= K' * Real.log x := by
    intro x hx z hz
    exact commonStrip_log_bound hX hB hK
      (by simpa only [X0] using hx) hz
      (hbound z (hball x hx hz))
  have hshiftMem : ∀ x : ℝ, ∀ z ∈ closedBall (0 : ℂ) (B + 1),
      (x : ℂ) + z ∈ ball (x : ℂ) (B + 2) := by
    intro x z hz
    have hn : ‖z‖ <= B + 1 := by
      simpa only [mem_closedBall, dist_zero_right] using hz
    have hn' : ‖z‖ < B + 2 := by linarith
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using hn'
  have hshift : ∀ x : ℝ, X0 < x →
      AnalyticOnNhd ℂ (shiftedAbelExtension (fun _ : ℝ => F) x)
        (closedBall (0 : ℂ) (B + 1)) := by
    intro x hx z hz
    exact (hbranchAnalytic x hx _ (hshiftMem x z hz)).fun_comp
      (f := fun w : ℂ => (x : ℂ) + w)
      (analyticAt_const.fun_add analyticAt_id)
  have hshiftReal : ∀ x : ℝ, X0 < x → ∀ t : ℝ, |t| <= B + 1 →
      shiftedAbelExtension (fun _ : ℝ => F) x (t : ℂ) =
        (A (x + t) : ℂ) := by
    intro x hx t ht
    have hmem : x + t ∈ ball x (B + 2) := by
      have hdist : dist (x + t) x = |t| := by
        rw [Real.dist_eq]
        congr 1
        ring
      rw [mem_ball, hdist]
      linarith
    simpa only [shiftedAbelExtension, Complex.ofReal_add] using
      hbranchReal x hx (x + t) hmem
  have hshiftBound : ∀ x : ℝ, X0 < x →
      ∀ z ∈ closedBall (0 : ℂ) (B + 1),
        ‖shiftedAbelExtension (fun _ : ℝ => F) x z‖ <=
          K' * Real.log x := by
    intro x hx z hz
    exact hbranchBound x hx _ (hshiftMem x z hz)
  have hnodes : ∀ δ ∈ hermiteNodeNeighborhood (ι := ι) B,
      ∀ i, δ i ∈ ball (0 : ℂ) (B + 1) := by
    intro δ hδ i
    have hi : ‖δ i‖ < B + 1 / 4 := hδ i
    have hi' : ‖δ i‖ < B + 1 := by linarith
    simpa only [mem_ball, dist_zero_right] using hi'
  have hdegree : ∀ x δ,
      (abelHermitePolynomial (fun _ : ℝ => F) B m x δ).natDegree <
        totalMultiplicity m := by
    intro x δ
    simpa only [abelHermitePolynomial, nodePolynomial_natDegree] using
      hermiteContourPolynomial_natDegree_lt
        (shiftedAbelExtension (fun _ : ℝ => F) x)
        (nodePolynomial δ m) (B + 1)
        (by simpa only [nodePolynomial_natDegree] using hd)
  have hjets : ∀ x, X0 < x → ∀ δ ∈ hermiteNodeNeighborhood B,
      ∀ (ξ : ℂ) (r : ℕ), r < nodeMultiplicity δ m ξ →
        iteratedDeriv r (shiftedAbelExtension (fun _ : ℝ => F) x) ξ =
          iteratedDeriv r
            (fun z => (abelHermitePolynomial
              (fun _ : ℝ => F) B m x δ).eval z) ξ := by
    intro x hx δ hδ ξ r hr
    exact hermiteContour_interpolates_combined δ m
      (by linarith : 0 < B + 1) (hshift x hx)
      (hnodes δ hδ) hd hr
  refine ⟨X, K', D * K', F, hX, hF, hreal, ?_⟩
  refine {
    threshold_gt_one := hX0
    extensionConstant_pos := hK'
    coefficientConstant_pos := mul_pos hD hK'
    neighborhood_open := isOpen_hermiteNodeNeighborhood hB
    neighborhood_bounded := isBounded_hermiteNodeNeighborhood hB
    neighborhood_contains := closed_nodes_subset_hermiteNodeNeighborhood B
    branch_analytic := hbranchAnalytic
    branch_realAgreement := hbranchReal
    branch_bound := hbranchBound
    branch_compatible := ?_
    shifted_analytic := hshift
    shifted_realAgreement := hshiftReal
    shifted_bound := hshiftBound
    coefficient_analytic := ?_
    coefficient_bound := ?_
    degree_bound := ?_
    normalized_expansion := ?_
    combined_jets := hjets
    combined_jets_explicit := ?_
    constant_coefficient := ?_ }
  · intro x y hx hy z hz
    rfl
  · intro x hx j hj δ hδ
    exact analyticAt_normalizedHermiteCoeff_nodes
      (B + 1) (by linarith) m j hj
      (shiftedAbelExtension (fun _ : ℝ => F) x)
      ((hshift x hx).continuousOn.mono sphere_subset_closedBall)
      δ (fun _ hz => nodePolynomial_eval_ne_zero_on_sphere
        δ m (hnodes δ hδ) hz)
  · intro x hx δ hδ j hj
    have hx1 : 1 < x := hX0.trans hx
    have hS : 0 <= K' * Real.log x :=
      mul_nonneg hK'.le (Real.log_nonneg hx1.le)
    have hb := (hcoeff δ
      (shiftedAbelExtension (fun _ : ℝ => F) x)
      (K' * Real.log x)
      (fun i => (hδ i).le) hS
      (fun z hz => hshiftBound x hx z
        (by simpa only [mem_closedBall, dist_zero_right] using hz.le))
      j hj).2
    have hlog : Real.log x <= 1 + x :=
      (Real.log_le_self (by linarith)).trans (by linarith)
    calc
      _ <= D * (K' * Real.log x) := hb
      _ = (D * K') * Real.log x := by ring
      _ <= (D * K') * (1 + x) :=
        mul_le_mul_of_nonneg_left hlog (mul_pos hD hK').le
  · intro x _ δ _
    exact hermiteContour_node_degree_lt
      (shiftedAbelExtension (fun _ : ℝ => F) x) δ m (B + 1)
  · intro x _ δ _ z
    exact polynomial_eval_normalized _ (hdegree x δ) z
  · intro x hx δ hδ ξ r hr
    rw [hjets x hx δ hδ ξ r hr]
    exact polynomial_iteratedDeriv_normalized _ (hdegree x δ)
      (hr.trans_le (nodeMultiplicity_le_totalMultiplicity δ m ξ)) ξ
  · intro x hx δ hδ i hi hmi
    have hc := hermiteContour_coeff_zero δ m
      (by linarith : 0 < B + 1) (hshift x hx)
      (hnodes δ hδ) hd hi hmi
    have hzero := hshiftReal x hx 0 (by
      simp only [abs_zero]
      linarith)
    simpa only [abelHermiteCoeff, normalizedCoeff, Nat.factorial_zero,
      Nat.cast_one, one_mul, abelHermitePolynomial, hc,
      Complex.ofReal_zero, add_zero] using hzero

end IsAbel
end AbelFormalization
