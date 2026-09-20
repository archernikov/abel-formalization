import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The differential contradiction in Wilkie's Theorem 2.8

This standalone, mathlib-only module isolates the final step of Wilkie's
regular-fiber exceptional-value argument.  Its finite-set theorem makes the
two unformalized source inputs explicit: unary tameness of the exceptional
set and a differentiable selection of singular witnesses on an open set.
Neither input is asserted here.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wilkie28MathlibOnly

set_option autoImplicit false

/-- A surjective linear map, together with a tangent vector in its kernel on
which one more functional takes value one, makes the augmented map
surjective. -/
theorem augmented_surjective_of_kernel_value_one
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (D : E →L[ℝ] K) (q : E →L[ℝ] ℝ)
    (hD : Function.Surjective D) (v : E)
    (hDv : D v = 0) (hqv : q v = 1) :
    Function.Surjective (fun w : E ↦ (D w, q w)) := by
  rintro ⟨y, z⟩
  obtain ⟨w, hw⟩ := hD y
  refine ⟨w + (z - q w) • v, ?_⟩
  apply Prod.ext
  · simp [map_add, map_smul, hDv, hw]
  · simp [map_add, map_smul, hqv, smul_eq_mul]

/-- The unary values at which the augmented derivative is not surjective,
with the first component fixed at a regular-fiber target. -/
def exceptionalParameterSet
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (F : E → K) (f : E → ℝ) (a : K) : Set ℝ :=
  {t | ∃ x : E, F x = a ∧ f x = t ∧
    ¬ Function.Surjective
      (fun v : E ↦ (fderiv ℝ F x v, fderiv ℝ f x v))}

/-- The composite analytic selection input obtained in the source from weak
selection and almost-everywhere smoothness.  The selected witnesses are
singular for the augmented derivative on a nonempty open domain. -/
def SmoothSingularWitnessSelection
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (F : E → K) (f : E → ℝ) (a : K) : Prop :=
  (interior (exceptionalParameterSet F f a)).Nonempty →
    ∃ (U : Set ℝ) (φ : ℝ → E),
      IsOpen U ∧ U.Nonempty ∧
      (∀ t ∈ U, F (φ t) = a) ∧
      (∀ t ∈ U, f (φ t) = t) ∧
      (∀ t ∈ U, ¬ Function.Surjective
        (fun v : E ↦
          (fderiv ℝ F (φ t) v, fderiv ℝ f (φ t) v))) ∧
      (∀ t ∈ U, DifferentiableAt ℝ φ t)

/-- A differentiable section of the equations `F (φ t) = a` and
`f (φ t) = t` gives a kernel vector with `df`-value one.  Therefore the
augmented derivative is surjective at every point of that section lying on a
regular fiber. -/
theorem augmented_surjective_along_differentiable_section
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (F : E → K) (f : E → ℝ) (a : K)
    {U : Set ℝ} (hUopen : IsOpen U) (φ : ℝ → E)
    (hFsection : ∀ t ∈ U, F (φ t) = a)
    (hfsection : ∀ t ∈ U, f (φ t) = t)
    {t : ℝ} (ht : t ∈ U)
    (hφdiff : DifferentiableAt ℝ φ t)
    (hFdiff : DifferentiableAt ℝ F (φ t))
    (hfdiff : DifferentiableAt ℝ f (φ t))
    (hregular : Function.Surjective (fderiv ℝ F (φ t))) :
    Function.Surjective
      (fun v : E ↦ (fderiv ℝ F (φ t) v, fderiv ℝ f (φ t) v)) := by
  have hUnhds : U ∈ 𝓝 t := hUopen.mem_nhds ht
  have hFeq : (F ∘ φ) =ᶠ[𝓝 t] (fun _ ↦ a) := by
    filter_upwards [hUnhds] with s hs
    exact hFsection s hs
  have hfeq : (f ∘ φ) =ᶠ[𝓝 t] (fun s ↦ s) := by
    filter_upwards [hUnhds] with s hs
    exact hfsection s hs
  have hFconst : HasDerivAt (F ∘ φ) (0 : K) t :=
    (hasDerivAt_const t a).congr_of_eventuallyEq hFeq
  have hfid : HasDerivAt (f ∘ φ) (1 : ℝ) t :=
    (hasDerivAt_id t).congr_of_eventuallyEq hfeq
  have hφderiv : HasDerivAt φ (deriv φ t) t := hφdiff.hasDerivAt
  have hDzero : fderiv ℝ F (φ t) (deriv φ t) = 0 :=
    ((hFdiff.hasFDerivAt).comp_hasDerivAt t hφderiv).unique hFconst
  have hqone : fderiv ℝ f (φ t) (deriv φ t) = 1 :=
    ((hfdiff.hasFDerivAt).comp_hasDerivAt t hφderiv).unique hfid
  exact augmented_surjective_of_kernel_value_one
    (fderiv ℝ F (φ t)) (fderiv ℝ f (φ t))
    hregular (deriv φ t) hDzero hqone

/-- The precise final implication of Wilkie 2.8.  Unary tameness is the
WS5 consequence after derivative closure has placed the exceptional set in
the weak family.  The selection premise is the combined conclusion of weak
selection (2.3) and the smooth-selector remark (2.5). -/
theorem exceptionalParameterSet_finite_of_tameness_and_smooth_selection
    {E K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (F : E → K) (f : E → ℝ) (a : K)
    (hFdiff : ∀ x : E, DifferentiableAt ℝ F x)
    (hfdiff : ∀ x : E, DifferentiableAt ℝ f x)
    (hregular : ∀ x : E, F x = a →
      Function.Surjective (fderiv ℝ F x))
    (htame : interior (exceptionalParameterSet F f a) = ∅ →
      (exceptionalParameterSet F f a).Finite)
    (hselection : SmoothSingularWitnessSelection F f a) :
    (exceptionalParameterSet F f a).Finite := by
  apply htame
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨U, φ, hUopen, ⟨s, hs⟩, hFsection, hfsection,
    hsingular, hφdiff⟩ := hselection ⟨t, ht⟩
  have haug := augmented_surjective_along_differentiable_section
    F f a hUopen φ hFsection hfsection hs
    (hφdiff s hs) (hFdiff (φ s)) (hfdiff (φ s))
    (hregular (φ s) (hFsection s hs))
  exact hsingular s hs haug

end Wilkie28MathlibOnly
