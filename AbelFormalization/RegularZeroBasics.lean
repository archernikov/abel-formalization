import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.DiscreteSubset

/-!
# Basic topology of regular zeros

For a square smooth map between finite-dimensional real normed spaces, every
zero with surjective derivative is isolated.  This is the local differential
fact used both in the restricted-analytic base case and in the definition of
the regular fibers appearing in the final o-minimality criterion.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Zeros in an open domain at which the Fréchet derivative is surjective. -/
def regularZeroSet
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Omega : Set E) (f : E → F) : Set E :=
  {x | x ∈ Omega ∧ f x = 0 ∧ Function.Surjective (fderiv ℝ f x)}

/-- In equal finite dimensions, surjectivity of a continuous linear map also
gives injectivity. -/
theorem continuousLinearMap_injective_of_surjective_of_finrank_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (D : E →L[ℝ] F) (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hD : Function.Surjective D) : Function.Injective D :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hD

/-- Every regular zero of a `C¹` square map has an open neighborhood in
which it is the only regular zero (indeed, the only zero). -/
theorem exists_isOpen_inter_regularZeroSet_eq_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Omega : Set E} (hOmega : IsOpen Omega)
    {f : E → E} (hf : ContDiffOn ℝ 1 f Omega)
    {x : E} (hx : x ∈ regularZeroSet Omega f) :
    ∃ U : Set E, IsOpen U ∧ U ∩ regularZeroSet Omega f = {x} := by
  have hfxOmega : x ∈ Omega := hx.1
  have hfxzero : f x = 0 := hx.2.1
  have hsurj : Function.Surjective (fderiv ℝ f x) := hx.2.2
  have hcont : ContDiffAt ℝ 1 f x :=
    hf.contDiffAt (hOmega.mem_nhds hfxOmega)
  let D : E →L[ℝ] E := fderiv ℝ f x
  have hinj : Function.Injective D :=
    continuousLinearMap_injective_of_surjective_of_finrank_eq D rfl hsurj
  have hker : D.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrange : D.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective D hker hrange
  have heD : (e : E →L[ℝ] E) = D :=
    ContinuousLinearEquiv.coe_ofBijective D hker hrange
  have hderiv : HasFDerivAt f (e : E →L[ℝ] E) x := by
    rw [heD]
    exact hcont.differentiableAt_one.hasFDerivAt
  let invchart := hcont.toOpenPartialHomeomorph f hderiv (by norm_num)
  have hxsource : x ∈ invchart.source := by
    exact hcont.mem_toOpenPartialHomeomorph_source hderiv (by norm_num)
  refine ⟨invchart.source, invchart.open_source, ?_⟩
  ext y
  constructor
  · rintro ⟨hysource, hy⟩
    have hfy : f y = f x := by rw [hy.2.1, hfxzero]
    have hyx : y = x := invchart.toPartialEquiv.injOn hysource hxsource hfy
    simpa [hyx]
  · intro hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨hxsource, hx⟩

/-- The regular-zero set of a `C¹` square map on an open set is discrete. -/
theorem isDiscrete_regularZeroSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Omega : Set E} (hOmega : IsOpen Omega)
    {f : E → E} (hf : ContDiffOn ℝ 1 f Omega) :
    IsDiscrete (regularZeroSet Omega f) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  exact exists_isOpen_inter_regularZeroSet_eq_singleton hOmega hf hx

end AbelFormalization
