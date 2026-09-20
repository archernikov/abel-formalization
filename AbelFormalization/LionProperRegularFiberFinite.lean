import AbelFormalization.LionUniformPreimageReduction
import AbelFormalization.RegularZeroBasics
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.DiscreteSubset

/-!
# Pointwise finiteness of proper regular fibers

A proper square `C¹` map has a finite full fiber at every regular target
value. Properness makes the full fiber compact. The inverse function theorem
isolates each point of that fiber, and a compact discrete set is finite.

This is a pointwise statement. Its cardinal can still grow without bound as
the regular target approaches a critical value.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- A surjective derivative of a square Euclidean `C¹` map gives an open
source neighborhood on which the map is injective. -/
private theorem exists_open_injective_patch_of_surjective_fderiv
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) {x : RealEuclidean n}
    (hsurj : Function.Surjective (fderiv ℝ F x)) :
    ∃ U : Set (RealEuclidean n), IsOpen U ∧ x ∈ U ∧ InjOn F U := by
  let D : RealEuclidean n →L[ℝ] RealEuclidean n := fderiv ℝ F x
  have hinj : Function.Injective D :=
    continuousLinearMap_injective_of_surjective_of_finrank_eq D rfl hsurj
  have hker : D.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrange : D.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  let e : RealEuclidean n ≃L[ℝ] RealEuclidean n :=
    ContinuousLinearEquiv.ofBijective D hker hrange
  have heD : (e : RealEuclidean n →L[ℝ] RealEuclidean n) = D :=
    ContinuousLinearEquiv.coe_ofBijective D hker hrange
  have hderiv : HasFDerivAt F
      (e : RealEuclidean n →L[ℝ] RealEuclidean n) x := by
    rw [heD]
    exact hF.contDiffAt.differentiableAt_one.hasFDerivAt
  let chart : OpenPartialHomeomorph (RealEuclidean n) (RealEuclidean n) :=
    hF.contDiffAt.toOpenPartialHomeomorph F hderiv (by norm_num)
  refine ⟨chart.source, chart.open_source, ?_, ?_⟩
  · exact hF.contDiffAt.mem_toOpenPartialHomeomorph_source hderiv (by norm_num)
  · exact chart.injOn

/-- A proper square `C¹` map has a finite full preimage at every regular
target value, including a regular target with an empty fiber. -/
theorem finite_fullFiber_of_proper_regular_target
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) (hproper : IsProperMap F)
    {u : RealEuclidean n} (hregular : IsRegularTargetValue F u) :
    (F ⁻¹' {u}).Finite := by
  have hcompact : IsCompact (F ⁻¹' {u}) :=
    hproper.isCompact_preimage isCompact_singleton
  have hdiscrete : IsDiscrete (F ⁻¹' {u}) := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro x hx
    have hxvalue : F x = u := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx
    obtain ⟨U, hUopen, hxU, hUinj⟩ :=
      exists_open_injective_patch_of_surjective_fderiv hF
        (hregular x hxvalue)
    refine ⟨U, hUopen, ?_⟩
    ext y
    constructor
    · rintro ⟨hyU, hyfiber⟩
      have hyvalue : F y = u := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hyfiber
      have hyx : y = x := hUinj hyU hxU (hyvalue.trans hxvalue.symm)
      simpa only [Set.mem_singleton_iff] using hyx
    · intro hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨hxU, hx⟩
  exact hcompact.finite hdiscrete

/-- Properness supplies pointwise full-fiber finiteness at every regular
target without an extra finiteness hypothesis. -/
theorem forall_regular_target_finite_fullFiber_of_proper
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) (hproper : IsProperMap F) :
    ∀ u : RealEuclidean n, IsRegularTargetValue F u →
      (F ⁻¹' {u}).Finite := by
  intro u hregular
  exact finite_fullFiber_of_proper_regular_target hF hproper hregular

/-- The manuscript's smooth regular fiber is finite over a regular target
for a proper square `C¹` map. -/
theorem finite_smoothRegularFiber_of_proper_regular_target
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) (hproper : IsProperMap F)
    {u : RealEuclidean n} (hregular : IsRegularTargetValue F u) :
    (smoothRegularFiber F u).Finite := by
  rw [smoothRegularFiber_eq_preimage_of_isRegularTargetValue F hF u hregular]
  exact finite_fullFiber_of_proper_regular_target hF hproper hregular

end AbelFormalization
