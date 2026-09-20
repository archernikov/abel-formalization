import AbelFormalization.AnalyticContourFamily
import AbelFormalization.HermiteFamilyAnalytic
import AbelFormalization.CentralCoefficientBounds

/-! # Joint analyticity of the central coefficients

The center, scale, and every node are independent complex parameters. A
Banach-valued analytic contour family is combined with the analytic Hermite
kernel, then composed with the polynomial map sending the nodes to their
scaled values. This includes scale zero and colliding nodes.
-/

noncomputable section

open Set Filter Metric Polynomial
open scoped Topology

namespace AbelFormalization

variable {ι : Type*} [Fintype ι]

/-- Full analyticity in the independent center, scale, and nodes, under the
exact contour nonvanishing condition. -/
theorem centralCoefficient_analyticAt_joint
    {F : ℂ → ℂ} {U : Set ℂ} {ρ : ℝ} (hU : IsOpen U) (hρ : 0 ≤ ρ)
    (hH : AnalyticOnNhd ℂ (fun v : ℂ × ℂ => centralComplexFunction F v.1 v.2)
      (U ×ˢ sphere (0 : ℂ) ρ))
    (m : ι → ℕ) {r : ℕ} (hr : r < totalMultiplicity m)
    {u q : ℂ} {δ : ι → ℂ} (hu : u ∈ U)
    (hQ : ∀ z ∈ sphere (0 : ℂ) ρ,
      (nodePolynomial (fun i => q * δ i) m).eval z ≠ 0) :
    AnalyticAt ℂ (fun v : ℂ × (ℂ × (ι → ℂ)) =>
      centralCoefficient F m ρ v.1 v.2.1 v.2.2 r) (u, q, δ) := by
  let H : ℂ × ℂ → ℂ := fun v => centralComplexFunction F v.1 v.2
  let G := contourFamily H ρ
  have hG : AnalyticAt ℂ G u := analyticOnNhd_contourFamily hU hH u hu
  have he : ∀ᶠ v in 𝓝 u, ∀ z : sphere (0 : ℂ) ρ, G v z = H (v, z) := by
    filter_upwards [hU.mem_nhds hu] with v hv
    exact fun z => contourFamily_apply hH.continuousOn hv z
  have hc := analyticAt_hermiteContourCoeff_family hρ m r H G hG he
    (fun i => q * δ i) hQ
  have hn := analyticAt_const.fun_mul hc
    (f := fun _ : ℂ × (ι → ℂ) => (r.factorial : ℂ))
  have hqmap : AnalyticAt ℂ (fun v : ℂ × (ℂ × (ι → ℂ)) => v.2.1) (u, q, δ) :=
    analyticAt_fst.fun_comp (f := fun v : ℂ × (ℂ × (ι → ℂ)) => v.2) analyticAt_snd
  have hδmap : AnalyticAt ℂ (fun v : ℂ × (ℂ × (ι → ℂ)) => v.2.2) (u, q, δ) :=
    analyticAt_snd.fun_comp (f := fun v : ℂ × (ℂ × (ι → ℂ)) => v.2) analyticAt_snd
  have hscaled : AnalyticAt ℂ
      (fun v : ℂ × (ℂ × (ι → ℂ)) => fun i => v.2.1 * v.2.2 i) (u, q, δ) := by
    apply AnalyticAt.pi
    intro i
    have hproj : AnalyticAt ℂ (fun v : ℂ × (ℂ × (ι → ℂ)) => v.2.2 i) (u, q, δ) :=
      ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt δ).fun_comp
        (f := fun v : ℂ × (ℂ × (ι → ℂ)) => v.2.2) hδmap
    exact hqmap.fun_mul hproj
  have ha := hn.fun_comp
    (f := fun v : ℂ × (ℂ × (ι → ℂ)) => (v.1, fun i => v.2.1 * v.2.2 i))
    (analyticAt_fst.prod hscaled)
  apply ha.congr
  filter_upwards with v
  dsimp only [centralCoefficient, normalizedCoeff, H]
  rw [hermiteContourPolynomial_coeff _ _ ρ
    (by simpa only [nodePolynomial_natDegree] using hr)]

/-- The same joint theorem with `(center, nodes)` grouped as the parameter and
scale as the final variable, suitable for a parametric Cauchy remainder. -/
theorem centralCoefficient_analyticAt_parametric
    {F : ℂ → ℂ} {U : Set ℂ} {ρ : ℝ} (hU : IsOpen U) (hρ : 0 ≤ ρ)
    (hH : AnalyticOnNhd ℂ (fun v : ℂ × ℂ => centralComplexFunction F v.1 v.2)
      (U ×ˢ sphere (0 : ℂ) ρ))
    (m : ι → ℕ) {r : ℕ} (hr : r < totalMultiplicity m)
    {u q : ℂ} {δ : ι → ℂ} (hu : u ∈ U)
    (hQ : ∀ z ∈ sphere (0 : ℂ) ρ,
      (nodePolynomial (fun i => q * δ i) m).eval z ≠ 0) :
    AnalyticAt ℂ (fun v : (ℂ × (ι → ℂ)) × ℂ =>
      centralCoefficient F m ρ v.1.1 v.2 v.1.2 r) ((u, δ), q) := by
  have hfst : AnalyticAt ℂ (fun v : (ℂ × (ι → ℂ)) × ℂ => v.1.1) ((u, δ), q) :=
    analyticAt_fst.fun_comp (f := fun v : (ℂ × (ι → ℂ)) × ℂ => v.1) analyticAt_fst
  have hnodes : AnalyticAt ℂ (fun v : (ℂ × (ι → ℂ)) × ℂ => v.1.2) ((u, δ), q) :=
    analyticAt_snd.fun_comp (f := fun v : (ℂ × (ι → ℂ)) × ℂ => v.1) analyticAt_fst
  exact (centralCoefficient_analyticAt_joint hU hρ hH m hr hu hQ).fun_comp
    (f := fun v : (ℂ × (ι → ℂ)) × ℂ => (v.1.1, v.2, v.1.2))
    (hfst.prod (analyticAt_snd.prod hnodes))

/-- On the uniform strip and scale disk, all independent central parameters
are analytic at every allowed node tuple, including coincident nodes. -/
theorem centralCoefficient_analyticAt_uniform
    {F : ℂ → ℂ} {X B : ℝ} (hB : 0 < B)
    (hH : AnalyticOnNhd ℂ (fun v : ℂ × ℂ => centralComplexFunction F v.1 v.2)
      (rightHalfStrip X 1 ×ˢ ball (0 : ℂ) (1 / 2)))
    (m : ι → ℕ) {r : ℕ} (hr : r < totalMultiplicity m)
    {u q : ℂ} {δ : ι → ℂ} (hu : u ∈ rightHalfStrip X 1)
    (hq : ‖q‖ < centralScaleRadius B) (hδ : ∀ i, ‖δ i‖ ≤ B + 1 / 4) :
    AnalyticAt ℂ (fun v : (ℂ × (ι → ℂ)) × ℂ =>
      centralCoefficient F m (1 / 4) v.1.1 v.2 v.1.2 r) ((u, δ), q) := by
  have hHcircle : AnalyticOnNhd ℂ
      (fun v : ℂ × ℂ => centralComplexFunction F v.1 v.2)
      (rightHalfStrip X 1 ×ˢ sphere (0 : ℂ) (1 / 4)) := by
    apply hH.mono
    intro v hv
    refine ⟨hv.1, ?_⟩
    have hn : ‖v.2‖ = 1 / 4 := by simpa using hv.2
    simpa [mem_ball, dist_zero_right, hn] using (by norm_num : (1 / 4 : ℝ) < 1 / 2)
  apply centralCoefficient_analyticAt_parametric (isOpen_rightHalfStrip X 1)
    (by norm_num) hHcircle m hr hu
  intro z hz
  apply nodePolynomial_ne_zero_of_radius_gap m (by norm_num : (1 / 8 : ℝ) < 1 / 4)
    (fun i => (norm_central_scaled_node_lt hB hq (hδ i)).le)
  simpa only [mem_sphere, dist_zero_right] using hz

/-- A domain form exposing the full joint power-series analyticity. -/
theorem centralCoefficient_analyticOnNhd_joint
    {F : ℂ → ℂ} {X B : ℝ} (hB : 0 < B)
    (hH : AnalyticOnNhd ℂ (fun v : ℂ × ℂ => centralComplexFunction F v.1 v.2)
      (rightHalfStrip X 1 ×ˢ ball (0 : ℂ) (1 / 2)))
    (m : ι → ℕ) {r : ℕ} (hr : r < totalMultiplicity m) :
    AnalyticOnNhd ℂ (fun v : (ℂ × (ι → ℂ)) × ℂ =>
      centralCoefficient F m (1 / 4) v.1.1 v.2 v.1.2 r)
      ((rightHalfStrip X 1 ×ˢ {δ : ι → ℂ | ∀ i, ‖δ i‖ ≤ B + 1 / 4}) ×ˢ
        ball (0 : ℂ) (centralScaleRadius B)) := by
  intro v hv
  exact centralCoefficient_analyticAt_uniform hB hH m hr hv.1.1
    (by simpa using hv.2) hv.1.2

end AbelFormalization
