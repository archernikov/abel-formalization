import AbelFormalization.RolleComponentUniqueness

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The complete geometric conclusion of the exponential-adjunction
argument after its Morse and regular-arc inputs have been supplied. -/
theorem finite_comparisonZeroSet_of_finite_regularCriticalSystem
    {r : ℕ} {M Omega : Set E}
    (H : Fin r → E → ℝ) (ρ K h : E → ℝ)
    (basis : Fin (r + 1) → E) (τ : M → E)
    (hρcont : Continuous ρ)
    (hcompact : ∀ R : ℝ, IsCompact {x : M | ρ (x : E) ≤ R})
    (hregularFinite :
      (regularZeroSet Omega (criticalSystemMap H K)).Finite)
    (hOmega : ∀ x : M, (x : E) ∈ Omega)
    (hMzero : ∀ x : M, ∀ i, H i x = 0)
    (hKcritical : ∀ x : M,
      K x = criticalDeterminant H ρ basis x)
    (hlocalConstraint : ∀ x : M, ∃ V ∈ 𝓝 (x : E),
      V ∩ {y | ∀ i, H i y = H i x} ⊆ M)
    (hsurj : ∀ x : M, (constraintFDeriv H x).range = ⊤)
    (hH : ∀ x : M, ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hK : ∀ x : M, HasStrictFDerivAt K (fderiv ℝ K x) x)
    (hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ))
    (hker : ∀ x : M, (constraintFDeriv H x).ker = ℝ ∙ τ x)
    (hKτ : ∀ x : M, x ∈ constrainedCriticalSet M H ρ basis →
      fderiv ℝ K x (τ x) ≠ 0)
    (hρ : ∀ x : M, HasStrictFDerivAt ρ (fderiv ℝ ρ x) x)
    (hArc : ∀ x y : M, y ∈ connectedComponent x → x ≠ y →
      RegularArcIn M x y)
    (hh : ∀ x : M, HasStrictFDerivAt h (fderiv ℝ h x) x)
    (hhτ : ∀ x : M, fderiv ℝ h x (τ x) ≠ 0) :
    ({x : M | h x = 0} : Set M).Finite := by
  letI : Finite (ConnectedComponents M) :=
    finite_connectedComponents_of_finite_regularCriticalSystem_of_tangent
      H ρ K basis τ hρcont hcompact hregularFinite hOmega hMzero
      hKcritical hlocalConstraint hsurj hH hK hdim hker hKτ hρ
  exact finite_zeroSet_of_finite_components_of_regularArcs
    H h τ hMzero hArc hH hh hker hhτ

/-- An injective lift into a finite zero set makes the original set finite. -/
theorem Set.Finite.of_injective_lift_to_finite
    {X Y : Type*} {Z : Set X} {W : Set Y} (lift : X → Y)
    (hW : W.Finite) (hlift : MapsTo lift Z W)
    (hinj : Set.InjOn lift Z) :
    Z.Finite := by
  apply Set.Finite.of_finite_image (f := lift)
  · exact hW.subset fun y ⟨x, hx, hxy⟩ ↦ hxy ▸ hlift hx
  · exact hinj

/-- Final lift form: regular zeros in the original system are finite once
their canonical lifts are comparison-function zeros on the closed curve. -/
theorem finite_of_injective_lift_to_comparisonZeroSet
    {X : Type*} {Z : Set X}
    {r : ℕ} {M Omega : Set E}
    (H : Fin r → E → ℝ) (ρ K h : E → ℝ)
    (basis : Fin (r + 1) → E) (τ : M → E)
    (lift : X → M)
    (hρcont : Continuous ρ)
    (hcompact : ∀ R : ℝ, IsCompact {x : M | ρ (x : E) ≤ R})
    (hregularFinite :
      (regularZeroSet Omega (criticalSystemMap H K)).Finite)
    (hOmega : ∀ x : M, (x : E) ∈ Omega)
    (hMzero : ∀ x : M, ∀ i, H i x = 0)
    (hKcritical : ∀ x : M,
      K x = criticalDeterminant H ρ basis x)
    (hlocalConstraint : ∀ x : M, ∃ V ∈ 𝓝 (x : E),
      V ∩ {y | ∀ i, H i y = H i x} ⊆ M)
    (hsurj : ∀ x : M, (constraintFDeriv H x).range = ⊤)
    (hH : ∀ x : M, ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hK : ∀ x : M, HasStrictFDerivAt K (fderiv ℝ K x) x)
    (hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ))
    (hker : ∀ x : M, (constraintFDeriv H x).ker = ℝ ∙ τ x)
    (hKτ : ∀ x : M, x ∈ constrainedCriticalSet M H ρ basis →
      fderiv ℝ K x (τ x) ≠ 0)
    (hρ : ∀ x : M, HasStrictFDerivAt ρ (fderiv ℝ ρ x) x)
    (hArc : ∀ x y : M, y ∈ connectedComponent x → x ≠ y →
      RegularArcIn M x y)
    (hh : ∀ x : M, HasStrictFDerivAt h (fderiv ℝ h x) x)
    (hhτ : ∀ x : M, fderiv ℝ h x (τ x) ≠ 0)
    (hlift : ∀ x ∈ Z, h (lift x : E) = 0)
    (hinj : Set.InjOn lift Z) :
    Z.Finite := by
  apply Set.Finite.of_injective_lift_to_finite lift
    (finite_comparisonZeroSet_of_finite_regularCriticalSystem
      H ρ K h basis τ hρcont hcompact hregularFinite hOmega hMzero
      hKcritical hlocalConstraint hsurj hH hK hdim hker hKτ hρ hArc hh hhτ)
  · intro x hx
    exact hlift x hx
  · exact hinj

end AbelFormalization
