import AbelFormalization.ConstraintSurjectivity

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Determinant-only form of regularity for the square critical system. -/
theorem criticalSystemFDeriv_surjective_of_cofactor_determinants
    {r : ℕ} (H : Fin r → E → ℝ) (ρ χ K : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E)
    (hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ))
    (hχdet : criticalDeterminant H χ basis x ≠ 0)
    (hKdet : criticalDeterminant H K basis x ≠ 0) :
    Function.Surjective (criticalSystemFDeriv H K x) := by
  apply criticalSystemFDeriv_surjective_of_ker_eq_span H K x
    (criticalCofactorTangent H ρ basis x) hdim
  · exact
      constraintFDeriv_ker_eq_span_criticalCofactorTangent_of_det_ne_zero
        H ρ χ basis x hdim
          (constraintFDeriv_surjective_of_criticalDeterminant_ne_zero
            H χ basis x hχdet) hχdet
  · rw [← criticalDeterminant_eq_fderiv_criticalCofactorTangent_of_aux
      H ρ K basis x]
    exact hKdet

/-- A zero of the constraints and critical equation is regular when the
distinguished Jacobian and the appended critical Jacobian are nonzero. -/
theorem mem_regularZeroSet_criticalSystemMap_of_cofactor_determinants
    {r : ℕ} {Omega : Set E}
    (H : Fin r → E → ℝ) (ρ χ K : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E)
    (hxOmega : x ∈ Omega)
    (hHx : ∀ i, H i x = 0) (hKx : K x = 0)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hK : HasStrictFDerivAt K (fderiv ℝ K x) x)
    (hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ))
    (hχdet : criticalDeterminant H χ basis x ≠ 0)
    (hKdet : criticalDeterminant H K basis x ≠ 0) :
    x ∈ regularZeroSet Omega (criticalSystemMap H K) := by
  refine ⟨hxOmega, ?_, ?_⟩
  · ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [criticalSystemMap_apply_last]
      exact hKx
    · rw [criticalSystemMap_apply_castSucc]
      exact hHx j
  · rw [(hasStrictFDerivAt_criticalSystemMap H K x hH hK).hasFDerivAt.fderiv]
    exact criticalSystemFDeriv_surjective_of_cofactor_determinants
      H ρ χ K basis x hdim hχdet hKdet

/-- The finite-component Morse conclusion with the tangent hypotheses
replaced by the three determinant tests appearing in the manuscript. -/
theorem finite_connectedComponents_of_finite_regularCriticalSystem_of_cofactor
    {r : ℕ} {M Omega : Set E}
    (H : Fin r → E → ℝ) (ρ χ K : E → ℝ)
    (basis : Fin (r + 1) → E)
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
    (hH : ∀ x : M, ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hK : ∀ x : M, HasStrictFDerivAt K (fderiv ℝ K x) x)
    (hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ))
    (hχdet : ∀ x : M, criticalDeterminant H χ basis x ≠ 0)
    (hKdet : ∀ x : M, x ∈ constrainedCriticalSet M H ρ basis →
      criticalDeterminant H K basis x ≠ 0)
    (hρ : ∀ x : M, HasStrictFDerivAt ρ (fderiv ℝ ρ x) x) :
    Finite (ConnectedComponents M) := by
  apply finite_connectedComponents_of_finite_regularCriticalSystem_of_tangent
    H ρ K basis (fun x ↦ criticalCofactorTangent H ρ basis x)
    hρcont hcompact hregularFinite hOmega hMzero hKcritical
    hlocalConstraint
      (fun x ↦ constraintFDeriv_surjective_of_criticalDeterminant_ne_zero
        H χ basis x (hχdet x)) hH hK hdim
  · intro x
    exact constraintFDeriv_ker_eq_span_criticalCofactorTangent_of_det_ne_zero
      H ρ χ basis x hdim
        (constraintFDeriv_surjective_of_criticalDeterminant_ne_zero
          H χ basis x (hχdet x)) (hχdet x)
  · intro x hx
    rw [← criticalDeterminant_eq_fderiv_criticalCofactorTangent_of_aux
      H ρ K basis x]
    exact hKdet x hx
  · exact hρ

/-- The comparison-zero conclusion with every tangent nonvanishing input
stated as a determinant nonvanishing condition. -/
theorem finite_comparisonZeroSet_of_finite_regularCriticalSystem_of_cofactor
    {r : ℕ} {M Omega : Set E}
    (H : Fin r → E → ℝ) (ρ χ K h : E → ℝ)
    (basis : Fin (r + 1) → E)
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
    (hH : ∀ x : M, ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hK : ∀ x : M, HasStrictFDerivAt K (fderiv ℝ K x) x)
    (hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ))
    (hχdet : ∀ x : M, criticalDeterminant H χ basis x ≠ 0)
    (hKdet : ∀ x : M, x ∈ constrainedCriticalSet M H ρ basis →
      criticalDeterminant H K basis x ≠ 0)
    (hρ : ∀ x : M, HasStrictFDerivAt ρ (fderiv ℝ ρ x) x)
    (hArc : ∀ x y : M, y ∈ connectedComponent x → x ≠ y →
      RegularArcIn M x y)
    (hh : ∀ x : M, HasStrictFDerivAt h (fderiv ℝ h x) x)
    (hhdet : ∀ x : M, criticalDeterminant H h basis x ≠ 0) :
    ({x : M | h x = 0} : Set M).Finite := by
  apply finite_comparisonZeroSet_of_finite_regularCriticalSystem
    H ρ K h basis (fun x ↦ criticalCofactorTangent H ρ basis x)
    hρcont hcompact hregularFinite hOmega hMzero hKcritical
    hlocalConstraint
      (fun x ↦ constraintFDeriv_surjective_of_criticalDeterminant_ne_zero
        H χ basis x (hχdet x)) hH hK hdim
  · intro x
    exact constraintFDeriv_ker_eq_span_criticalCofactorTangent_of_det_ne_zero
      H ρ χ basis x hdim
        (constraintFDeriv_surjective_of_criticalDeterminant_ne_zero
          H χ basis x (hχdet x)) (hχdet x)
  · intro x hx
    rw [← criticalDeterminant_eq_fderiv_criticalCofactorTangent_of_aux
      H ρ K basis x]
    exact hKdet x hx
  · exact hρ
  · exact hArc
  · exact hh
  · intro x
    rw [← criticalDeterminant_eq_fderiv_criticalCofactorTangent_of_aux
      H ρ h basis x]
    exact hhdet x

end AbelFormalization
