import AbelFormalization.ComponentZeroFiniteness
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A parametrized arc in `M` with nonvanishing velocity on its interior. -/
def RegularArcIn (M : Set E) (x y : E) : Prop :=
  ∃ a b : ℝ, ∃ γ v : ℝ → E,
    a < b ∧ γ a = x ∧ γ b = y ∧
      ContinuousOn γ (Icc a b) ∧ MapsTo γ (Icc a b) M ∧
        ∀ t ∈ Ioo a b, HasDerivAt γ (v t) t ∧ v t ≠ 0

/-- A linear functional nonzero on a generator of a one-dimensional kernel
is nonzero on every nonzero vector in that kernel. -/
theorem continuousLinearMap_ne_zero_on_kernelLine
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (k : E →L[ℝ] ℝ) (τ v : E)
    (hker : L.ker = ℝ ∙ τ) (hkτ : k τ ≠ 0)
    (hvker : v ∈ L.ker) (hv : v ≠ 0) :
    k v ≠ 0 := by
  rw [hker] at hvker
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hvker
  intro hkv
  rw [← hc, map_smul, smul_eq_mul] at hkv
  have hc0 : c = 0 := (mul_eq_zero.mp hkv).resolve_right hkτ
  apply hv
  rw [← hc, hc0, zero_smul]

/-- Along an interior point of an arc contained in a constraint locus, the
arc velocity lies in the kernel of the simultaneous constraint derivative. -/
theorem regularArc_velocity_mem_constraintKernel
    {r : ℕ} {M : Set E} (H : Fin r → E → ℝ)
    (hMzero : ∀ x : M, ∀ i, H i x = 0)
    {a b t : ℝ} {γ v : ℝ → E}
    (ht : t ∈ Ioo a b) (hγM : MapsTo γ (Icc a b) M)
    (hγ : HasDerivAt γ (v t) t)
    (hH : ∀ i, HasStrictFDerivAt (H i)
      (fderiv ℝ (H i) (γ t)) (γ t)) :
    v t ∈ (constraintFDeriv H (γ t)).ker := by
  rw [LinearMap.mem_ker]
  ext i
  have hcomp : HasDerivAt (H i ∘ γ)
      (fderiv ℝ (H i) (γ t) (v t)) t :=
    (hH i).hasFDerivAt.comp_hasDerivAt t hγ
  have heq : (H i ∘ γ) =ᶠ[𝓝 t] (fun _ ↦ 0) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact hMzero ⟨γ s, hγM hs⟩ i
  have hzero : HasDerivAt (H i ∘ γ) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq
  have := hcomp.unique hzero
  simpa [constraintFDeriv] using this

/-- Rolle's theorem prevents two zeros in one component when every pair of
distinct points in that component can be joined by a regular arc and the
differential is nonzero on the tangent line. -/
theorem eq_of_mem_connectedComponent_of_regularArcs
    {r : ℕ} {M : Set E} (H : Fin r → E → ℝ) (h : E → ℝ)
    (τ : M → E)
    (hMzero : ∀ x : M, ∀ i, H i x = 0)
    (hArc : ∀ x y : M, y ∈ connectedComponent x → x ≠ y →
      RegularArcIn M x y)
    (hH : ∀ x : M, ∀ i, HasStrictFDerivAt (H i)
      (fderiv ℝ (H i) x) x)
    (hh : ∀ x : M, HasStrictFDerivAt h (fderiv ℝ h x) x)
    (hker : ∀ x : M, (constraintFDeriv H x).ker = ℝ ∙ τ x)
    (hhτ : ∀ x : M, fderiv ℝ h x (τ x) ≠ 0)
    (x y : M) (hx : h x = 0) (hy : h y = 0)
    (hcomponent : y ∈ connectedComponent x) :
    x = y := by
  by_contra hxy
  obtain ⟨a, b, γ, v, hab, hγa, hγb, hγcont, hγM, hγder⟩ :=
    hArc x y hcomponent hxy
  have hhcont : ContinuousOn h M := by
    intro z hz
    exact (hh ⟨z, hz⟩).continuousAt.continuousWithinAt
  have hcompcont : ContinuousOn (h ∘ γ) (Icc a b) :=
    hhcont.comp hγcont hγM
  have hend : (h ∘ γ) a = (h ∘ γ) b := by
    simp only [Function.comp_apply, hγa, hγb, hx, hy]
  let d : ℝ → ℝ := fun t ↦ fderiv ℝ h (γ t) (v t)
  have hcompder : ∀ t ∈ Ioo a b, HasDerivAt (h ∘ γ) (d t) t := by
    intro t ht
    have htIcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
    exact (hh ⟨γ t, hγM htIcc⟩).hasFDerivAt.comp_hasDerivAt t
      (hγder t ht).1
  obtain ⟨t, ht, hdt⟩ := exists_hasDerivAt_eq_zero hab hcompcont hend hcompder
  have htIcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
  let z : M := ⟨γ t, hγM htIcc⟩
  have hvker : v t ∈ (constraintFDeriv H (γ t)).ker :=
    regularArc_velocity_mem_constraintKernel H hMzero ht hγM
      (hγder t ht).1 (hH z)
  have hdnz : d t ≠ 0 := by
    apply continuousLinearMap_ne_zero_on_kernelLine
      (constraintFDeriv H (γ t)) (fderiv ℝ h (γ t)) (τ z) (v t)
      (hker z) (hhτ z) hvker (hγder t ht).2
  exact hdnz hdt

/-- Quantitative Rolle reduction: the zero set of the last coordinate on a
regular one-dimensional constraint locus has at most one point in each
connected component.  Hence its cardinality is bounded by the component
count of the partial fiber.  This is Lion's Lemma 5 in the form used by the
induction in Theorem 7'. -/
theorem enatCard_zeroSet_le_connectedComponents_of_regularArcs
    {r : ℕ} {M : Set E} (H : Fin r → E → ℝ) (h : E → ℝ)
    (τ : M → E)
    (hMzero : ∀ x : M, ∀ i, H i x = 0)
    (hArc : ∀ x y : M, y ∈ connectedComponent x → x ≠ y →
      RegularArcIn M x y)
    (hH : ∀ x : M, ∀ i, HasStrictFDerivAt (H i)
      (fderiv ℝ (H i) x) x)
    (hh : ∀ x : M, HasStrictFDerivAt h (fderiv ℝ h x) x)
    (hker : ∀ x : M, (constraintFDeriv H x).ker = ℝ ∙ τ x)
    (hhτ : ∀ x : M, fderiv ℝ h x (τ x) ≠ 0) :
    ENat.card {x : M | h x = 0} ≤
      ENat.card (ConnectedComponents M) := by
  apply enatCard_le_connectedComponents_of_component_unique
  intro x y hcomponent
  apply Subtype.ext
  exact eq_of_mem_connectedComponent_of_regularArcs
    H h τ hMzero hArc hH hh hker hhτ x y x.property y.property
      (ConnectedComponents.coe_eq_coe'.mp hcomponent.symm)

/-- The zero set of `h` on `M` is finite under the regular-arc hypotheses
used in the manuscript's Rolle argument. -/
theorem finite_zeroSet_of_finite_components_of_regularArcs
    {r : ℕ} {M : Set E} [Finite (ConnectedComponents M)]
    (H : Fin r → E → ℝ) (h : E → ℝ) (τ : M → E)
    (hMzero : ∀ x : M, ∀ i, H i x = 0)
    (hArc : ∀ x y : M, y ∈ connectedComponent x → x ≠ y →
      RegularArcIn M x y)
    (hH : ∀ x : M, ∀ i, HasStrictFDerivAt (H i)
      (fderiv ℝ (H i) x) x)
    (hh : ∀ x : M, HasStrictFDerivAt h (fderiv ℝ h x) x)
    (hker : ∀ x : M, (constraintFDeriv H x).ker = ℝ ∙ τ x)
    (hhτ : ∀ x : M, fderiv ℝ h x (τ x) ≠ 0) :
    ({x : M | h x = 0} : Set M).Finite := by
  apply Set.Finite.of_finite_connectedComponents_of_component_unique
  intro x y hcomponent
  apply Subtype.ext
  exact eq_of_mem_connectedComponent_of_regularArcs
    H h τ hMzero hArc hH hh hker hhτ x y x.property y.property hcomponent

end AbelFormalization
