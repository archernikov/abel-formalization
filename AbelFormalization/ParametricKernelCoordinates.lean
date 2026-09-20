import AbelFormalization.ParametricChartCriticality

/-!
# Kernel coordinates for a parametric submersion

If a surjective derivative has source `X × Y`, target `Z`, and
`finrank X = finrank Z`, rank-nullity identifies the dimension of its kernel
with the parameter dimension.  This file records that calculation and fixes
a continuous linear equivalence from parameter space to the kernel.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

theorem finrank_ker_eq_parameter_of_surjective
    (L : (X × Y) →L[ℝ] Z)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hL : L.range = ⊤) :
    Module.finrank ℝ L.ker = Module.finrank ℝ Y := by
  have h := L.finrank_range_add_finrank_ker
  rw [hL, finrank_top, Module.finrank_prod, hdim] at h
  omega

def parameterKernelEquiv
    (L : (X × Y) →L[ℝ] Z)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hL : L.range = ⊤) : Y ≃L[ℝ] L.ker :=
  ContinuousLinearEquiv.ofFinrankEq
    (finrank_ker_eq_parameter_of_surjective L hdim hL).symm

theorem range_eq_ker_of_chart_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : (X × Y) →L[ℝ] Z)
    (A : (X × Y) →L[ℝ] (Z × V))
    (d : Y →L[ℝ] (X × Y))
    (q : Y ≃L[ℝ] V)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hL : L.range = ⊤)
    (hfst : (ContinuousLinearMap.fst ℝ Z V).comp A = L)
    (hcomp : A.comp d =
      (0 : Y →L[ℝ] Z).prod (q : Y →L[ℝ] V)) :
    d.range = L.ker := by
  have hcomp_apply : ∀ u : Y, A (d u) = (0, q u) := by
    intro u
    have hu := congrArg
      (fun T : Y →L[ℝ] (Z × V) => T u) hcomp
    simpa using hu
  have hd_injective : Function.Injective d := by
    intro u v huv
    apply q.injective
    have hAuv : A (d u) = A (d v) := congrArg A huv
    simpa [hcomp_apply] using congrArg Prod.snd hAuv
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro w ⟨u, rfl⟩
    change L (d u) = 0
    have hfst_apply := congrArg
      (fun T : (X × Y) →L[ℝ] Z => T (d u)) hfst
    simpa [hcomp_apply] using hfst_apply.symm
  · rw [LinearMap.finrank_range_of_inj hd_injective,
      finrank_ker_eq_parameter_of_surjective L hdim hL]

end AbelFormalization
