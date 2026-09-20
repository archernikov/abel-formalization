import AbelFormalization.Statement
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.Constructions

/-!
# Initial analytic consequences

The named generator is analytic at every real point, and differentiating the
Abel equation gives the first-order derivative recurrence.
-/

namespace AbelFormalization

open Filter Set
open scoped Topology

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem differentiableAt {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ A x :=
  differentiableAt_of_deriv_ne_zero (ne_of_gt (hA.deriv_pos x hx))

theorem analyticAt_C0 (x : ℝ) : AnalyticAt ℝ (C0 A) x := by
  have hp : 0 < 1 + x ^ 2 := by positivity
  have hid : AnalyticAt ℝ (fun y : ℝ => y) x := analyticAt_id
  have hc : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) x := analyticAt_const
  have hg : AnalyticAt ℝ (fun y : ℝ => 1 + y ^ 2) x := hc.add (hid.pow 2)
  exact (hA.analytic _ hp).comp (f := fun y : ℝ => 1 + y ^ 2) hg

theorem deriv_abel {x : ℝ} (hx : 0 < x) :
    deriv A (E x) * Real.exp x = deriv A x := by
  have hE : HasDerivAt E (Real.exp x) x := (Real.hasDerivAt_exp x).sub_const 1
  have hleft : HasDerivAt (fun u => A (E u))
      (deriv A (E x) * Real.exp x) x :=
    (hA.differentiableAt (E_pos hx)).hasDerivAt.comp x hE
  have hright : HasDerivAt (fun u => A u + 1) (deriv A x) x :=
    (hA.differentiableAt hx).hasDerivAt.add_const 1
  have heq : (fun u => A (E u)) =ᶠ[𝓝 x] (fun u => A u + 1) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
    exact hA.abel u hu
  exact hleft.unique (hright.congr_of_eventuallyEq heq)

end IsAbel

end AbelFormalization
