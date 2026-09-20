import AbelFormalization.ComplexJets
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# Central jets in the scaled Hermite construction

At zero interpolation scale, the auxiliary function is
`1 + A(u + log(1 + η))`. Its jets are the signed-Stirling combinations
appearing in the central interpolation identity.
-/

noncomputable section

namespace AbelFormalization

open Set Filter
open scoped Topology

/-- Scalar substitution commutes with iterated scalar derivatives, including
the case of the zero scalar and without a global smoothness assumption. -/
theorem iteratedDeriv_comp_mul_exact (f : ℝ → ℝ) (c : ℝ) (r : ℕ) :
    iteratedDeriv r (fun x => f (c * x)) =
      fun x => c ^ r * iteratedDeriv r f (c * x) := by
  induction r with
  | zero => simp
  | succ r ih =>
      funext x
      rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left]
      simp only [smul_eq_mul, ← iteratedDeriv_succ, pow_succ]
      ring

/-- The real auxiliary function used before passing to independent complex
parameters in the Hermite construction. -/
def centralRealFunction (A : ℝ → ℝ) (u : ℝ) (η : ℝ) : ℝ :=
  1 + A (u + L η)

/-- The auxiliary function with independent complex input. -/
def centralComplexFunction (F : ℂ → ℂ) (u η : ℂ) : ℂ :=
  1 + F (u + complexL η)

theorem centralComplexFunction_analyticAt {F : ℂ → ℂ} {u : ℂ}
    (hF : AnalyticAt ℂ F u) : AnalyticAt ℂ (centralComplexFunction F u) 0 := by
  have hbase : AnalyticAt ℂ F (u + complexL 0) := by simpa [complexL] using hF
  have hinner : AnalyticAt ℂ (fun η => u + complexL η) 0 :=
    analyticAt_const.add (complexL_analyticAt (by norm_num))
  have hcomp := hbase.comp (f := fun η : ℂ => u + complexL η) hinner
  exact analyticAt_const.add hcomp

theorem analyticAt_L_zero : AnalyticAt ℝ L 0 := by
  unfold L
  apply (analyticAt_const.add analyticAt_id).log
  norm_num

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)
include hA

theorem centralRealFunction_eventually_eq {u : ℝ} (hu : 0 < u) :
    centralRealFunction A u =ᶠ[𝓝 0] fun η => A (E u + Real.exp u * η) := by
  have hcont : ContinuousAt (fun η => u + L η) 0 :=
    continuousAt_const.add analyticAt_L_zero.continuousAt
  have hpos : ∀ᶠ η : ℝ in 𝓝 0, 0 < u + L η := by
    apply hcont.eventually
    simpa [L] using (lt_mem_nhds hu)
  filter_upwards [hpos, isOpen_Ioi.mem_nhds (by norm_num : (-1 : ℝ) < 0)] with η hη hη1
  change -1 < η at hη1
  have hex : E (u + L η) = E u + Real.exp u * η := by
    unfold E L
    rw [Real.exp_add, Real.exp_log (by linarith : 0 < 1 + η)]
    ring
  change 1 + A (u + L η) = _
  rw [← hex, hA.abel _ hη]
  ring

theorem centralRealFunction_analyticAt {u : ℝ} (hu : 0 < u) :
    AnalyticAt ℝ (centralRealFunction A u) 0 := by
  have hbase : AnalyticAt ℝ A (u + L 0) := by simpa [L] using hA.analytic u hu
  have hinner : AnalyticAt ℝ (fun η => u + L η) 0 :=
    analyticAt_const.add analyticAt_L_zero
  have hcomp := hbase.comp (f := fun η : ℝ => u + L η) hinner
  exact analyticAt_const.add hcomp

/-- The real central jet is exactly the normalized transport polynomial. -/
theorem centralRealFunction_iteratedDeriv {u : ℝ} (hu : 0 < u)
    (r : ℕ) (hr : 1 ≤ r) :
    iteratedDeriv r (centralRealFunction A u) 0 =
      ∑ j ∈ Finset.range (r + 1), (signedStirling r j : ℝ) * iteratedDeriv j A u := by
  rw [(hA.centralRealFunction_eventually_eq hu).iteratedDeriv_eq r]
  have hmul := congrFun (iteratedDeriv_comp_mul_exact
    (fun z => A (E u + z)) (Real.exp u) r) 0
  simp only [mul_zero, iteratedDeriv_comp_const_add, add_zero] at hmul
  rw [hmul, ← Real.exp_nat_mul]
  have h := hA.iteratedDeriv_transport_normalized r hr u hu
  rw [polynomialJet_descPochhammer] at h
  exact h

/-- At zero scale, the complex auxiliary function has precisely the
signed-Stirling jet used in the manuscript's central interpolation formula. -/
theorem centralComplexFunction_iteratedDeriv {u : ℝ} (hu : 0 < u)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F (u : ℂ))
    (he : (fun y : ℝ => F (y : ℂ)) =ᶠ[𝓝 u] fun y => (A y : ℂ))
    (r : ℕ) (hr : 1 ≤ r) :
    iteratedDeriv r (centralComplexFunction F (u : ℂ)) 0 =
      ∑ j ∈ Finset.range (r + 1), (signedStirling r j : ℂ) *
        ((iteratedDeriv j A u : ℝ) : ℂ) := by
  have hc : Tendsto (fun η : ℝ => u + L η) (𝓝 0) (𝓝 u) := by
    have h : ContinuousAt (fun η : ℝ => u + L η) 0 :=
      continuousAt_const.add analyticAt_L_zero.continuousAt
    simpa [L] using h.tendsto
  have he' : (fun η : ℝ => centralComplexFunction F (u : ℂ) (η : ℂ))
      =ᶠ[𝓝 0] fun η => (centralRealFunction A u η : ℂ) := by
    filter_upwards [hc.eventually he,
      isOpen_Ioi.mem_nhds (by norm_num : (-1 : ℝ) < 0)] with η hη hη1
    change -1 < η at hη1
    dsimp [centralComplexFunction, centralRealFunction]
    rw [complexL_ofReal (by linarith : 0 ≤ 1 + η), ← Complex.ofReal_add, hη]
    simp
  have h := iteratedDeriv_complex_extension (hA.centralRealFunction_analyticAt hu)
    (centralComplexFunction_analyticAt hF) he' r
  simp only [Complex.ofReal_zero] at h
  rw [h, hA.centralRealFunction_iteratedDeriv hu r hr]
  push_cast
  rfl

end IsAbel
end AbelFormalization
