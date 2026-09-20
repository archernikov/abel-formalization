import AbelFormalization.LocalConstraintFiber
import AbelFormalization.CriticalComponentFiniteness

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The simultaneous value of a finite family of scalar constraints. -/
def constraintMap {r : ℕ} (H : Fin r → E → ℝ) : E → Fin r → ℝ :=
  fun x i ↦ H i x

/-- The product derivative of a finite family of scalar constraints. -/
def constraintFDeriv {r : ℕ} (H : Fin r → E → ℝ) (x : E) :
    E →L[ℝ] (Fin r → ℝ) :=
  ContinuousLinearMap.pi (fun i ↦ fderiv ℝ (H i) x)

theorem hasStrictFDerivAt_constraintMap {r : ℕ}
    (H : Fin r → E → ℝ) (x : E)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x) :
    HasStrictFDerivAt (constraintMap H) (constraintFDeriv H x) x := by
  exact hasStrictFDerivAt_pi.mpr hH

variable [CompleteSpace E]

/-- Independent differentials make the local constraint fiber stay in one
connected component of a locally matching constraint locus. -/
theorem localConstraintFiber_of_surjectiveDerivative
    {r : ℕ} {M : Set E} (H : Fin r → E → ℝ) (x : M)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hsurj : (constraintFDeriv H x).range = ⊤)
    (hlocalConstraint : ∃ V ∈ 𝓝 (x : E),
      V ∩ {y | ∀ i, H i y = H i x} ⊆ M) :
    ∃ U ∈ 𝓝 (x : E),
      ∀ y ∈ U, (∀ i, H i y = H i x) →
        ∃ hyM : y ∈ M,
          (⟨y, hyM⟩ : M) ∈ connectedComponent x := by
  have hf := hasStrictFDerivAt_constraintMap H (x : E) hH
  have hlocalMap : ∃ V ∈ 𝓝 (x : E),
      V ∩ {y | constraintMap H y = constraintMap H x} ⊆ M := by
    obtain ⟨V, hV, hVM⟩ := hlocalConstraint
    refine ⟨V, hV, ?_⟩
    intro y hy
    exact hVM ⟨hy.1, fun i ↦ congrFun hy.2 i⟩
  obtain ⟨U, hU, hcomponent⟩ :=
    HasStrictFDerivAt.exists_local_level_connectedComponent
      hf hsurj x.property hlocalMap
  refine ⟨U, hU, ?_⟩
  intro y hyU hyLevel
  apply hcomponent y hyU
  exact funext hyLevel

/-- In the finite-critical-system argument, local connectedness of the
constraint fibers follows from the implicit function theorem. -/
theorem finite_connectedComponents_of_finite_regularCriticalSystem_of_surjectiveConstraint
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : ℕ} {M Omega : Set E} (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E) (G : E → F)
    (hρcont : Continuous ρ)
    (hcompact : ∀ R : ℝ, IsCompact {x : M | ρ (x : E) ≤ R})
    (hregularFinite : (regularZeroSet Omega G).Finite)
    (hcriticalRegular : ∀ x : M,
      x ∈ constrainedCriticalSet M H ρ basis →
        (x : E) ∈ regularZeroSet Omega G)
    (hlocalConstraint : ∀ x : M, ∃ V ∈ 𝓝 (x : E),
      V ∩ {y | ∀ i, H i y = H i x} ⊆ M)
    (hsurj : ∀ x : M, (constraintFDeriv H x).range = ⊤)
    (hH : ∀ x : M, ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hρ : ∀ x : M, HasStrictFDerivAt ρ (fderiv ℝ ρ x) x) :
    Finite (ConnectedComponents M) := by
  apply finite_connectedComponents_of_finite_regularCriticalSystem
    H ρ basis G hρcont hcompact hregularFinite hcriticalRegular
  · intro x
    exact localConstraintFiber_of_surjectiveDerivative H x
      (hH x) (hsurj x) (hlocalConstraint x)
  · exact hH
  · exact hρ

end AbelFormalization
