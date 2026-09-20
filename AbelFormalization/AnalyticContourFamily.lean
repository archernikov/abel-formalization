import AbelFormalization.ContourFunctional
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Analytic families with values in continuous functions on a circle

A jointly continuous family of scalar holomorphic functions on a compact
circle gives an analytic map into the Banach space of continuous circle
functions. The proof uses a Banach-valued Cauchy integral and verifies its
representation by applying continuous evaluation functionals.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace AbelFormalization

/-- A family restricted to a circle, with zero as the default at parameters
where the restriction is not continuous. -/
def contourFamily (F : ℂ × ℂ → ℂ) (R : ℝ) (u : ℂ) : C(sphere (0 : ℂ) R, ℂ) :=
  ContinuousMap.mkD (fun ζ => F (u, ζ)) 0

/-- On its continuous parameter domain, the bundled family has the original
pointwise values. -/
theorem contourFamily_apply {F : ℂ × ℂ → ℂ} {U : Set ℂ} {R : ℝ}
    (hF : ContinuousOn F (U ×ˢ sphere (0 : ℂ) R)) {u : ℂ} (hu : u ∈ U)
    (ζ : sphere (0 : ℂ) R) : contourFamily F R u ζ = F (u, ζ) := by
  apply ContinuousMap.mkD_apply_of_continuous
  exact hF.comp_continuous (continuous_const.prodMk continuous_subtype_val)
    (fun ζ => ⟨hu, ζ.property⟩)

/-- Joint continuity gives continuity in the uniform norm on the compact
circle. -/
theorem continuousOn_contourFamily {F : ℂ × ℂ → ℂ} {U : Set ℂ} {R : ℝ}
    (hF : ContinuousOn F (U ×ˢ sphere (0 : ℂ) R)) :
    ContinuousOn (contourFamily F R) U := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  have hc : ContinuousOn (fun v : ℂ × sphere (0 : ℂ) R => F (v.1, v.2))
      (U ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun v hv => ⟨hv.1, v.2.property⟩)
  apply hc.congr
  intro v hv
  exact contourFamily_apply hF hv.1 v.2

/-- Continuous evaluation commutes with a Banach-valued circle integral. -/
theorem circleIntegral_continuousMap_apply {R : ℝ}
    {f : ℂ → C(sphere (0 : ℂ) R, ℂ)} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) (ζ : sphere (0 : ℂ) R) :
    (∮ t in C(c, r), f t) ζ = ∮ t in C(c, r), f t ζ := by
  have h := (ContinuousMap.evalCLM (R := ℂ) ζ).intervalIntegral_comp_comm hf.out
  simpa only [circleIntegral, ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply] using h.symm

/-- Scalar holomorphy in the parameter, together with joint continuity,
upgrades to actual Banach-valued analyticity. -/
theorem analyticOnNhd_contourFamily_of_fibers
    {F : ℂ × ℂ → ℂ} {U : Set ℂ} {R : ℝ}
    (hU : IsOpen U) (hF : ContinuousOn F (U ×ˢ sphere (0 : ℂ) R))
    (hfiber : ∀ ζ : sphere (0 : ℂ) R, AnalyticOnNhd ℂ (fun u => F (u, ζ)) U) :
    AnalyticOnNhd ℂ (contourFamily F R) U := by
  intro p hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p hp
  have hρ : 0 < ε / 2 := half_pos hε
  have hsub : closedBall p (ε / 2) ⊆ U := by
    intro u hu
    apply hball
    exact lt_of_le_of_lt (mem_closedBall.mp hu) (by linarith)
  have hc : ContinuousOn (contourFamily F R) U := continuousOn_contourFamily hF
  have hi : CircleIntegrable (contourFamily F R) p (ε / 2) :=
    (hc.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable hρ.le
  have hnorm : AnalyticAt ℂ
      (fun u => (2 * Real.pi * I : ℂ)⁻¹ •
        ∮ t in C(p, ε / 2), (t - u)⁻¹ • contourFamily F R t) p :=
    (hasFPowerSeriesOn_cauchy_integral (R := ⟨ε / 2, hρ.le⟩) hi hρ).analyticAt
  apply hnorm.congr
  filter_upwards [ball_mem_nhds p hρ] with u hu
  ext ζ
  have hnot : u ∉ sphere p |ε / 2| := by
    rw [abs_of_pos hρ]
    intro hs
    exact (ne_of_lt (mem_ball.mp hu)) (mem_sphere.mp hs)
  have hiKernel : CircleIntegrable
      (fun t => (t - u)⁻¹ • contourFamily F R t) p (ε / 2) := by
    simpa only [zpow_neg_one] using hi.sub_zpow_smul (-1) hnot
  have heval : AnalyticOnNhd ℂ (fun t => contourFamily F R t ζ) U :=
    (hfiber ζ).congr hU (fun t ht => (contourFamily_apply hF ht ζ).symm)
  change (2 * Real.pi * I : ℂ)⁻¹ •
    (∮ t in C(p, ε / 2), (t - u)⁻¹ • contourFamily F R t) ζ = _
  rw [circleIntegral_continuousMap_apply hiKernel]
  simpa only [ContinuousMap.smul_apply] using
    Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      countable_empty hu (heval.continuousOn.mono hsub)
      (fun t ht => (heval t (hsub (ball_subset_closedBall ht.1))).differentiableAt)

/-- A jointly analytic scalar family on a parameter domain times a compact
circle is analytic as a map into the Banach space of continuous circle
functions. -/
theorem analyticOnNhd_contourFamily {F : ℂ × ℂ → ℂ} {U : Set ℂ} {R : ℝ}
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F (U ×ˢ sphere (0 : ℂ) R)) :
    AnalyticOnNhd ℂ (contourFamily F R) U := by
  apply analyticOnNhd_contourFamily_of_fibers hU hF.continuousOn
  intro ζ u hu
  exact (hF (u, ζ) ⟨hu, ζ.property⟩).comp (f := fun v : ℂ => (v, (ζ : ℂ)))
    (analyticAt_id.prod analyticAt_const)

end AbelFormalization
