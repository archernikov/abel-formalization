import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Contour integration as a continuous linear functional

Continuous functions on a compact circle form a Banach space. Extending them by
zero off the circle makes the usual circle integral available; the extension's
values off the circle have no effect on the integral.
-/

noncomputable section

namespace AbelFormalization

open Set Metric

/-- A continuous function on the circle, extended by zero away from the circle. -/
def sphereFunctionExtension (R : ℝ) (g : C(sphere (0 : ℂ) R, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ sphere (0 : ℂ) R then g ⟨z, hz⟩ else 0

@[simp]
theorem sphereFunctionExtension_of_mem (R : ℝ) (g : C(sphere (0 : ℂ) R, ℂ))
    (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) :
    sphereFunctionExtension R g z = g ⟨z, hz⟩ := by
  simp only [sphereFunctionExtension, dite_eq_left hz]

theorem continuousOn_sphereFunctionExtension (R : ℝ) (g : C(sphere (0 : ℂ) R, ℂ)) :
    ContinuousOn (sphereFunctionExtension R g) (sphere (0 : ℂ) R) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert g.continuous using 1
  ext z
  exact sphereFunctionExtension_of_mem R g z z.property

private def contourIntegralLinearMap (R : ℝ) (hR : 0 ≤ R) :
    C(sphere (0 : ℂ) R, ℂ) →ₗ[ℂ] ℂ where
  toFun g := ∮ z in C(0, R), sphereFunctionExtension R g z
  map_add' g h := by
    calc
      _ = ∮ z in C(0, R), sphereFunctionExtension R g z + sphereFunctionExtension R h z := by
        apply circleIntegral.integral_congr hR
        intro z hz
        simp only [sphereFunctionExtension_of_mem R _ z hz, ContinuousMap.add_apply]
      _ = _ := circleIntegral.integral_add
        ((continuousOn_sphereFunctionExtension R g).circleIntegrable hR)
        ((continuousOn_sphereFunctionExtension R h).circleIntegrable hR)
  map_smul' c g := by
    calc
      _ = ∮ z in C(0, R), c • sphereFunctionExtension R g z := by
        apply circleIntegral.integral_congr hR
        intro z hz
        simp only [sphereFunctionExtension_of_mem R _ z hz, ContinuousMap.smul_apply]
      _ = _ := circleIntegral.integral_smul c _ 0 R

/-- Integration around the circle is a bounded complex-linear functional on
the Banach space of continuous functions on that circle. -/
def contourIntegralCLM (R : ℝ) (hR : 0 ≤ R) : C(sphere (0 : ℂ) R, ℂ) →L[ℂ] ℂ :=
  (contourIntegralLinearMap R hR).mkContinuous (2 * Real.pi * R) fun g => by
    apply circleIntegral.norm_integral_le_of_norm_le_const hR
    intro z hz
    rw [sphereFunctionExtension_of_mem R g z hz]
    exact g.norm_coe_le_norm ⟨z, hz⟩

@[simp]
theorem contourIntegralCLM_apply (R : ℝ) (hR : 0 ≤ R) (g : C(sphere (0 : ℂ) R, ℂ)) :
    contourIntegralCLM R hR g = ∮ z in C(0, R), sphereFunctionExtension R g z := rfl

/-- Any total function agreeing with the continuous circle function has the same
circle integral. -/
theorem contourIntegralCLM_eq_circleIntegral (R : ℝ) (hR : 0 ≤ R)
    (g : C(sphere (0 : ℂ) R, ℂ)) (f : ℂ → ℂ)
    (h : ∀ z : sphere (0 : ℂ) R, g z = f z) :
    contourIntegralCLM R hR g = ∮ z in C(0, R), f z := by
  apply circleIntegral.integral_congr hR
  intro z hz
  rw [sphereFunctionExtension_of_mem R g z hz]
  exact h ⟨z, hz⟩

end AbelFormalization
