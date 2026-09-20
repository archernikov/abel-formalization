import AbelFormalization.CentralJet

/-! # Complex rescaling identity for central interpolation

The Abel equation first supplies a real germ identity. Analytic uniqueness
extends it to a complex germ and then to every common connected domain.
-/

noncomputable section

namespace AbelFormalization

open Set Filter Metric
open scoped Topology

/-- Agreement of complex analytic functions on a real neighborhood determines
their complex germs. -/
theorem analytic_eventuallyEq_of_real_eventuallyEq {F G : ℂ → ℂ} {a : ℝ}
    (hF : AnalyticAt ℂ F (a : ℂ)) (hG : AnalyticAt ℂ G (a : ℂ))
    (he : (fun t : ℝ => F (t : ℂ)) =ᶠ[𝓝 a] fun t => G (t : ℂ)) :
    F =ᶠ[𝓝 (a : ℂ)] G := by
  rcases hF.eventually_eq_or_eventually_ne hG with h | h
  · exact h
  · have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] a) (𝓝[≠] (a : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [eventually_mem_nhdsWithin] with t ht
      simpa using ht
    obtain ⟨t, heq, hne⟩ := ((he.filter_mono nhdsWithin_le_nhds).and (ht.eventually h)).exists
    exact (hne heq).elim

/-- The central complex function restricts to the central real germ whenever
the underlying extension has the corresponding real germ. -/
theorem centralComplexFunction_real_eventuallyEq {A : ℝ → ℝ} {F : ℂ → ℂ} {u : ℝ}
    (he : (fun y : ℝ => F (y : ℂ)) =ᶠ[𝓝 u] fun y => (A y : ℂ)) :
    (fun η : ℝ => centralComplexFunction F (u : ℂ) (η : ℂ)) =ᶠ[𝓝 0]
      fun η => (centralRealFunction A u η : ℂ) := by
  have hc : Tendsto (fun η : ℝ => u + L η) (𝓝 0) (𝓝 u) := by
    have h : ContinuousAt (fun η : ℝ => u + L η) 0 :=
      continuousAt_const.add analyticAt_L_zero.continuousAt
    simpa [L] using h.tendsto
  filter_upwards [hc.eventually he,
    isOpen_Ioi.mem_nhds (by norm_num : (-1 : ℝ) < 0)] with η hη hη1
  change -1 < η at hη1
  dsimp [centralComplexFunction, centralRealFunction]
  rw [complexL_ofReal (by linarith : 0 ≤ 1 + η), ← Complex.ofReal_add, hη]
  simp

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)
include hA

/-- The Abel equation identifies the rescaled complex central function with
the original function near the center. The two complex extensions may differ. -/
theorem centralComplexFunction_rescale_eventuallyEq {F G : ℂ → ℂ} {u : ℝ}
    (hu : 0 < u) (hF : AnalyticAt ℂ F (u : ℂ))
    (hG : AnalyticAt ℂ G (E u : ℂ))
    (heF : (fun y : ℝ => F (y : ℂ)) =ᶠ[𝓝 u] fun y => (A y : ℂ))
    (heG : (fun y : ℝ => G (y : ℂ)) =ᶠ[𝓝 (E u)] fun y => (A y : ℂ)) :
    (fun z : ℂ => G ((E u : ℂ) + z)) =ᶠ[𝓝 0]
      fun z => centralComplexFunction F (u : ℂ) ((Real.exp (-u) : ℂ) * z) := by
  have hleft : AnalyticAt ℂ (fun z : ℂ => G ((E u : ℂ) + z)) 0 := by
    have hg : AnalyticAt ℂ G ((E u : ℂ) + 0) := by simpa using hG
    exact hg.comp (f := fun z : ℂ => (E u : ℂ) + z)
      (analyticAt_const.add analyticAt_id)
  have hright : AnalyticAt ℂ (fun z : ℂ =>
      centralComplexFunction F (u : ℂ) ((Real.exp (-u) : ℂ) * z)) 0 := by
    have hh : AnalyticAt ℂ (centralComplexFunction F (u : ℂ))
        ((Real.exp (-u) : ℂ) * 0) := by
      simpa using centralComplexFunction_analyticAt hF
    exact hh.comp (f := fun z : ℂ => (Real.exp (-u) : ℂ) * z)
      (analyticAt_const.mul analyticAt_id)
  apply analytic_eventuallyEq_of_real_eventuallyEq (a := 0)
    (by simpa using hleft) (by simpa using hright)
  have hshift : Tendsto (fun z : ℝ => E u + z) (𝓝 0) (𝓝 (E u)) := by
    have hc : ContinuousAt (fun z : ℝ => E u + z) 0 := by fun_prop
    simpa only [add_zero] using hc.tendsto
  have hscale : Tendsto (fun z : ℝ => Real.exp (-u) * z) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun z : ℝ => Real.exp (-u) * z) 0 := by fun_prop
    simpa only [mul_zero] using hc.tendsto
  filter_upwards [hshift.eventually heG,
    hscale.eventually (centralComplexFunction_real_eventuallyEq heF),
    hscale.eventually (hA.centralRealFunction_eventually_eq hu)] with z hz hzc hzr
  have hex : Real.exp u * (Real.exp (-u) * z) = z := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  simp only [hex] at hzr
  simpa only [Complex.ofReal_add, Complex.ofReal_mul] using
    hz.trans ((congrArg (fun x : ℝ => (x : ℂ)) hzr).symm.trans hzc.symm)

/-- On a common connected domain, the rescaling identity holds everywhere.
In applications this domain is the disk containing all interpolation nodes. -/
theorem centralComplexFunction_rescale_eqOn {F G : ℂ → ℂ} {u : ℝ}
    (hu : 0 < u) (hF : AnalyticAt ℂ F (u : ℂ))
    (hG : AnalyticAt ℂ G (E u : ℂ))
    (heF : (fun y : ℝ => F (y : ℂ)) =ᶠ[𝓝 u] fun y => (A y : ℂ))
    (heG : (fun y : ℝ => G (y : ℂ)) =ᶠ[𝓝 (E u)] fun y => (A y : ℂ))
    {U : Set ℂ} (hU : IsPreconnected U) (h0 : (0 : ℂ) ∈ U)
    (hleft : AnalyticOnNhd ℂ (fun z : ℂ => G ((E u : ℂ) + z)) U)
    (hright : AnalyticOnNhd ℂ (fun z : ℂ =>
      centralComplexFunction F (u : ℂ) ((Real.exp (-u) : ℂ) * z)) U) :
    EqOn (fun z : ℂ => G ((E u : ℂ) + z))
      (fun z : ℂ => centralComplexFunction F (u : ℂ) ((Real.exp (-u) : ℂ) * z)) U := by
  exact hleft.eqOn_of_preconnected_of_frequently_eq hright hU h0
    ((hA.centralComplexFunction_rescale_eventuallyEq hu hF hG heF heG).filter_mono
      nhdsWithin_le_nhds).frequently

end IsAbel
end AbelFormalization
