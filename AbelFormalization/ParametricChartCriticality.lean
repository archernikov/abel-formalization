import AbelFormalization.ParametricSubmersionLinear
import Mathlib.LinearAlgebra.Determinant

/-!
# Criticality of a parameter projection

A local parametrization of the zero set of a joint submersion has derivative
range equal to the kernel of the joint derivative.  In such a chart,
regularity of the fixed-parameter equation is equivalent to regularity of the
projection to parameter space.  Thus every degenerate fixed-parameter zero is
a critical point of that projection, in the determinant sense used by Sard's
theorem.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem chartProjection_fderiv_range_eq
    (Phi : X × Y → Z) (gamma : Y → X × Y) (y : Y)
    (hgamma : DifferentiableAt ℝ gamma y)
    (hdgamma : (fderiv ℝ gamma y).range =
      (fderiv ℝ Phi (gamma y)).ker) :
    (fderiv ℝ (fun t => (gamma t).2) y).range =
      (sndOnKernel (fderiv ℝ Phi (gamma y))).range := by
  rw [fderiv.snd hgamma]
  exact range_eq_top_comp_of_range_eq_ker
    (fderiv ℝ Phi (gamma y)) (fderiv ℝ gamma y) hdgamma

theorem fixedParameter_regular_iff_chartProjection_regular
    (Phi : X × Y → Z) (gamma : Y → X × Y) (y : Y)
    (hgamma : DifferentiableAt ℝ gamma y)
    (hdgamma : (fderiv ℝ gamma y).range =
      (fderiv ℝ Phi (gamma y)).ker)
    (hPhiSurj : (fderiv ℝ Phi (gamma y)).range = ⊤) :
    (fstPartial (fderiv ℝ Phi (gamma y))).range = ⊤ ↔
      (fderiv ℝ (fun t => (gamma t).2) y).range = ⊤ := by
  rw [chartProjection_fderiv_range_eq Phi gamma y hgamma hdgamma]
  exact fstPartial_range_eq_top_iff_sndOnKernel_range_eq_top
    (fderiv ℝ Phi (gamma y)) hPhiSurj

theorem continuousLinearMap_det_eq_zero_of_range_ne_top
    [FiniteDimensional ℝ Y] (L : Y →L[ℝ] Y)
    (hL : L.range ≠ ⊤) : L.det = 0 := by
  by_contra hdet
  have hker : L.ker = ⊥ := by
    apply not_ne_iff.mp
    intro hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  have hrange : L.range = ⊤ :=
    (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank rfl).mp hker
  exact hL hrange

theorem chartProjection_det_eq_zero_of_fixedParameter_not_regular
    [FiniteDimensional ℝ Y]
    (Phi : X × Y → Z) (gamma : Y → X × Y) (y : Y)
    (hgamma : DifferentiableAt ℝ gamma y)
    (hdgamma : (fderiv ℝ gamma y).range =
      (fderiv ℝ Phi (gamma y)).ker)
    (hPhiSurj : (fderiv ℝ Phi (gamma y)).range = ⊤)
    (hfixed : (fstPartial (fderiv ℝ Phi (gamma y))).range ≠ ⊤) :
    (fderiv ℝ (fun t => (gamma t).2) y).det = 0 := by
  apply continuousLinearMap_det_eq_zero_of_range_ne_top
  intro hprojection
  exact hfixed ((fixedParameter_regular_iff_chartProjection_regular
    Phi gamma y hgamma hdgamma hPhiSurj).mpr hprojection)

end AbelFormalization
