import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Complex parameters in contour integrals

On a proper parameter space, continuity of the partial derivative supplies the
local compact bounds needed to differentiate a finite interval integral. Joint
analyticity near a fixed circle provides these hypotheses for a contour
integral. The multivariate conclusion is complex Fréchet differentiability;
for one complex parameter it also gives `AnalyticOnNhd`.
-/

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology Interval

namespace AbelFormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]

/-- Differentiation under a finite interval integral using joint continuity of
the integrand and its parameter derivative. -/
theorem hasFDerivAt_intervalIntegral_of_continuousOn
    {U : Set E} {a b : ℝ} {F : E × ℝ → ℂ} {D : E × ℝ → E →L[ℂ] ℂ}
    (hU : IsOpen U) (hF : ContinuousOn F (U ×ˢ uIcc a b))
    (hD : ContinuousOn D (U ×ˢ uIcc a b))
    (hd : ∀ p ∈ U, ∀ t ∈ uIcc a b, HasFDerivAt (fun q => F (q, t)) (D (p, t)) p)
    {p : E} (hp : p ∈ U) :
    HasFDerivAt (fun q => ∫ t in a..b, F (q, t)) (∫ t in a..b, D (p, t)) p := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU p hp
  have hsub : closedBall p (ε / 2) ⊆ U := by
    intro q hq
    apply hball
    exact lt_of_le_of_lt (mem_closedBall.mp hq) (by linarith)
  have hcF (q : E) (hq : q ∈ U) :
      ContinuousOn (fun t => F (q, t)) (uIcc a b) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨hq, ht⟩)
  have hcD (q : E) (hq : q ∈ U) :
      ContinuousOn (fun t => D (q, t)) (uIcc a b) :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨hq, ht⟩)
  have hK : IsCompact (closedBall p (ε / 2) ×ˢ uIcc a b) :=
    (isCompact_closedBall p (ε / 2)).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (hD.mono (Set.prod_mono hsub Subset.rfl))
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := closedBall p (ε / 2)) (bound := fun _ => C)
    (closedBall_mem_nhds p (half_pos hε))
  · filter_upwards [hU.mem_nhds hp] with q hq
    exact (hcF q hq).intervalIntegrable.aestronglyMeasurable_restrict_uIoc
  · exact (hcF p hp).intervalIntegrable
  · exact (hcD p hp).intervalIntegrable.aestronglyMeasurable_restrict_uIoc
  · exact Filter.Eventually.of_forall fun t ht q hq =>
      hC (q, t) ⟨hq, uIoc_subset_uIcc ht⟩
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t ht q hq =>
      hd q (hsub hq) t (uIoc_subset_uIcc ht)

/-- The partial derivative in the parameter of a jointly analytic integrand. -/
def circleParameterDerivative (F : E × ℂ → ℂ) (p : E) (ζ : ℂ) : E →L[ℂ] ℂ :=
  (fderiv ℂ F (p, ζ)).comp (ContinuousLinearMap.inl ℂ E ℂ)

/-- A contour integral of a jointly analytic family has a complex Fréchet
derivative, obtained by integrating the parameter derivative. -/
theorem hasFDerivAt_circleIntegral_of_analyticOnNhd
    {U : Set E} {F : E × ℂ → ℂ} {R : ℝ}
    (hU : IsOpen U) (hR : 0 ≤ R)
    (hF : AnalyticOnNhd ℂ F (U ×ˢ sphere (0 : ℂ) R))
    {p : E} (hp : p ∈ U) :
    HasFDerivAt (fun q => ∮ ζ in C(0, R), F (q, ζ))
      (∮ ζ in C(0, R), circleParameterDerivative F p ζ) p := by
  let Ψ : E × ℝ → E × ℂ := fun v => (v.1, circleMap 0 R v.2)
  have hΨ : Continuous Ψ := continuous_fst.prodMk
    ((continuous_circleMap 0 R).comp continuous_snd)
  have hm : MapsTo Ψ (U ×ˢ uIcc 0 (2 * Real.pi)) (U ×ˢ sphere (0 : ℂ) R) :=
    fun v hv => ⟨hv.1, circleMap_mem_sphere 0 hR v.2⟩
  have hweight : Continuous (fun v : E × ℝ => deriv (circleMap 0 R) v.2) := by
    simp only [deriv_circleMap]
    fun_prop
  unfold circleIntegral
  apply hasFDerivAt_intervalIntegral_of_continuousOn
    (F := fun v => deriv (circleMap 0 R) v.2 • F (v.1, circleMap 0 R v.2))
    (D := fun v => deriv (circleMap 0 R) v.2 •
      circleParameterDerivative F v.1 (circleMap 0 R v.2)) hU
  · exact hweight.continuousOn.smul (hF.continuousOn.comp hΨ.continuousOn hm)
  · exact hweight.continuousOn.smul
      ((hF.fderiv.continuousOn.comp hΨ.continuousOn hm).clm_comp continuousOn_const)
  · intro q hq t _
    exact (((hF (q, circleMap 0 R t)
      ⟨hq, circleMap_mem_sphere 0 hR t⟩).differentiableAt.hasFDerivAt).comp q
        (hasFDerivAt_prodMk_left (𝕜 := ℂ) q (circleMap 0 R t))).const_smul
          (deriv (circleMap 0 R) t)
  · exact hp

/-- Contour integrals are holomorphic in any proper complex parameter space. -/
theorem differentiableOn_circleIntegral_of_analyticOnNhd
    {U : Set E} {F : E × ℂ → ℂ} {R : ℝ}
    (hU : IsOpen U) (hR : 0 ≤ R)
    (hF : AnalyticOnNhd ℂ F (U ×ˢ sphere (0 : ℂ) R)) :
    DifferentiableOn ℂ (fun p => ∮ ζ in C(0, R), F (p, ζ)) U :=
  fun _ hp =>
    (hasFDerivAt_circleIntegral_of_analyticOnNhd hU hR hF hp).differentiableAt.differentiableWithinAt

/-- In one complex parameter, contour-integral holomorphy yields an analytic
power series at each point of the open parameter domain. -/
theorem analyticOnNhd_circleIntegral_of_analyticOnNhd
    {U : Set ℂ} {F : ℂ × ℂ → ℂ} {R : ℝ}
    (hU : IsOpen U) (hR : 0 ≤ R)
    (hF : AnalyticOnNhd ℂ F (U ×ˢ sphere (0 : ℂ) R)) :
    AnalyticOnNhd ℂ (fun p => ∮ ζ in C(0, R), F (p, ζ)) U :=
  (differentiableOn_circleIntegral_of_analyticOnNhd hU hR hF).analyticOnNhd hU

end AbelFormalization
