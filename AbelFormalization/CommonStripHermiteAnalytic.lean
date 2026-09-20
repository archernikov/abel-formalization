import AbelFormalization.AbelHermiteFamily
import AbelFormalization.AnalyticContourFamily
import AbelFormalization.ComplexStrip
import AbelFormalization.HermiteFamilyAnalytic

/-!
# Joint Hermite-coefficient analyticity from one common strip extension

Using one fixed complex extension makes the moving interpolation center an
ordinary analytic parameter.  The contour family then varies analytically in
that center, while the existing Hermite kernel handles all nodes jointly.
-/

noncomputable section

set_option autoImplicit false

open Set Filter Metric Polynomial
open scoped Topology

namespace AbelFormalization

variable {ι : Type*} [Fintype ι]

/-- Joint analyticity in a moving center and every Hermite node, for one
fixed complex analytic extension. -/
theorem normalizedHermiteCoeff_analyticAt_joint_center_nodes
    {F : ℂ → ℂ} {U : Set ℂ} {R : ℝ}
    (hU : IsOpen U) (hR : 0 ≤ R)
    (hF : AnalyticOnNhd ℂ (fun v : ℂ × ℂ => F (v.1 + v.2))
      (U ×ˢ sphere (0 : ℂ) R))
    (m : ι → ℕ) {r : ℕ} (hr : r < totalMultiplicity m)
    {x : ℂ} {δ : ι → ℂ} (hx : x ∈ U)
    (hQ : ∀ z ∈ sphere (0 : ℂ) R,
      (nodePolynomial δ m).eval z ≠ 0) :
    AnalyticAt ℂ (fun v : ℂ × (ι → ℂ) =>
      normalizedCoeff
        (hermiteContourPolynomial
          (fun z => F (v.1 + z)) (nodePolynomial v.2 m) R) r)
      (x, δ) := by
  let H : ℂ × ℂ → ℂ := fun v => F (v.1 + v.2)
  let G := contourFamily H R
  have hG : AnalyticAt ℂ G x :=
    analyticOnNhd_contourFamily hU hF x hx
  have he : ∀ᶠ v in 𝓝 x, ∀ z : sphere (0 : ℂ) R,
      G v z = H (v, z) := by
    filter_upwards [hU.mem_nhds hx] with v hv
    exact fun z => contourFamily_apply hF.continuousOn hv z
  have hc := analyticAt_hermiteContourCoeff_family hR m r H G hG he δ hQ
  have hn := analyticAt_const.fun_mul hc
    (f := fun _ : ℂ × (ι → ℂ) => (r.factorial : ℂ))
  apply hn.congr
  filter_upwards with v
  dsimp only [normalizedCoeff, H]
  rw [hermiteContourPolynomial_coeff _ _ R
    (by simpa only [nodePolynomial_natDegree] using hr)]

/-- A fixed extension on a wide strip gives joint center/node analyticity on
the narrower strip whose translated interpolation contour stays inside it. -/
theorem normalizedHermiteCoeff_analyticAt_commonStrip
    {F : ℂ → ℂ} {X B : ℝ} (hB : 0 < B)
    (hF : AnalyticOnNhd ℂ F (rightHalfStrip X (B + 2)))
    (m : ι → ℕ) {r : ℕ} (hr : r < totalMultiplicity m)
    {x : ℂ} (hx : x ∈ rightHalfStrip (X + B + 1) 1)
    {δ : ι → ℂ} (hδ : δ ∈ hermiteNodeNeighborhood B) :
    AnalyticAt ℂ (fun v : ℂ × (ι → ℂ) =>
      normalizedCoeff
        (hermiteContourPolynomial
          (fun z => F (v.1 + z)) (nodePolynomial v.2 m) (B + 1)) r)
      (x, δ) := by
  have hshift : AnalyticOnNhd ℂ
      (fun v : ℂ × ℂ => F (v.1 + v.2))
      (rightHalfStrip (X + B + 1) 1 ×ˢ sphere (0 : ℂ) (B + 1)) := by
    intro v hv
    have hzNorm : ‖v.2‖ = B + 1 := by
      simpa only [mem_sphere, dist_zero_right] using hv.2
    have hzRe : |v.2.re| ≤ B + 1 := by
      exact (Complex.abs_re_le_norm v.2).trans_eq hzNorm
    have hzIm : |v.2.im| ≤ B + 1 := by
      exact (Complex.abs_im_le_norm v.2).trans_eq hzNorm
    have hsum : v.1 + v.2 ∈ rightHalfStrip X (B + 2) := by
      constructor
      · simp only [Complex.add_re]
        have hl := (abs_le.mp hzRe).1
        linarith [hv.1.1]
      · simp only [Complex.add_im]
        exact (abs_add_le _ _).trans_lt (by linarith [hv.1.2])
    exact (hF _ hsum).comp
      (f := fun v : ℂ × ℂ => v.1 + v.2)
      (analyticAt_fst.add analyticAt_snd)
  apply normalizedHermiteCoeff_analyticAt_joint_center_nodes
    (isOpen_rightHalfStrip (X + B + 1) 1)
    (by linarith) hshift m hr hx
  intro z hz
  apply nodePolynomial_eval_ne_zero_on_sphere δ m
  · intro i
    have hi : ‖δ i‖ < B + 1 / 4 := hδ i
    have hi' : ‖δ i‖ < B + 1 := by linarith
    simpa only [mem_ball, dist_zero_right] using hi'
  · exact hz

end AbelFormalization
