import AbelFormalization.ComplexStrip
import AbelFormalization.Stirling
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Agreement of real and complex jets

A holomorphic extension agrees with every real derivative of the original
analytic function along its real diameter. This identifies the jets appearing
in contour interpolation with the real jets in the manuscript.
-/

namespace AbelFormalization

open Set Filter
open scoped Topology

theorem deriv_complex_extension {f : ℝ → ℝ} {F : ℂ → ℂ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hF : DifferentiableAt ℂ F (x : ℂ))
    (he : (fun y : ℝ => F (y : ℂ)) =ᶠ[𝓝 x] fun y => (f y : ℂ)) :
    deriv F (x : ℂ) = ((deriv f x : ℝ) : ℂ) := by
  exact hF.hasDerivAt.comp_ofReal.unique
    (hf.hasDerivAt.ofReal_comp.congr_of_eventuallyEq he)

/-- All complex derivatives of an extension restrict to the real derivatives. -/
theorem iteratedDeriv_complex_extension {f : ℝ → ℝ} {F : ℂ → ℂ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hF : AnalyticAt ℂ F (x : ℂ))
    (he : (fun y : ℝ => F (y : ℂ)) =ᶠ[𝓝 x] fun y => (f y : ℂ)) (r : ℕ) :
    iteratedDeriv r F (x : ℂ) = ((iteratedDeriv r f x : ℝ) : ℂ) := by
  induction r generalizing f F x with
  | zero => exact he.eq_of_nhds
  | succ r ih =>
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      apply ih hf.deriv hF.deriv
      filter_upwards [hf.eventually_analyticAt,
        Complex.continuous_ofReal.continuousAt.eventually hF.eventually_analyticAt,
        he.eventually_nhds] with y hy hY heY
      exact deriv_complex_extension hy.differentiableAt hY.differentiableAt heY

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)
include hA

/-- Any complex extension agreeing with the Abel function locally has the
prescribed real jet at a positive real point. -/
theorem complex_extension_jets {F : ℂ → ℂ} {x : ℝ} (hx : 0 < x)
    (hF : AnalyticAt ℂ F (x : ℂ))
    (he : (fun y : ℝ => F (y : ℂ)) =ᶠ[𝓝 x] fun y => (A y : ℂ)) (r : ℕ) :
    iteratedDeriv r F (x : ℂ) = ((iteratedDeriv r A x : ℝ) : ℂ) :=
  iteratedDeriv_complex_extension (hA.analytic x hx) hF he r

/-- The common extension on a right half-strip has the original Abel jets at
every real point of the tail. -/
theorem complex_strip_jets {F : ℂ → ℂ} {X M : ℝ} (hX : 0 < X) (hM : 0 < M)
    (hF : AnalyticOnNhd ℂ F (rightHalfStrip X M))
    (he : ∀ y : ℝ, X < y → F (y : ℂ) = (A y : ℂ))
    {x : ℝ} (hx : X < x) (r : ℕ) :
    iteratedDeriv r F (x : ℂ) = ((iteratedDeriv r A x : ℝ) : ℂ) := by
  apply hA.complex_extension_jets (hX.trans hx)
  · apply hF
    simpa only [rightHalfStrip, mem_ofPred_eq, Complex.ofReal_re,
      Complex.ofReal_im, abs_zero] using And.intro hx hM
  · filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact he y hy

end IsAbel
end AbelFormalization
