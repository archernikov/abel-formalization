import AbelFormalization.RestrictedComparisonTransversality

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finite_comparisonZeroSet_of_finite_components_of_cofactor
    {r : ℕ} {M : Set E}
    (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (hfinite : Finite (ConnectedComponents M))
    (hMzero : ∀ x : M, ∀ i, H i x = 0)
    (hArc : ∀ x y : M, y ∈ connectedComponent x → x ≠ y →
      RegularArcIn M x y)
    (hH : ∀ x : M, ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hh : ∀ x : M, HasStrictFDerivAt h (fderiv ℝ h x) x)
    (hdet : ∀ x : M, criticalDeterminant H h basis x ≠ 0) :
    ({x : M | h x = 0} : Set M).Finite := by
  letI : Finite (ConnectedComponents M) := hfinite
  have hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ) := by
    simpa using Module.finrank_eq_card_basis basis
  let τ : M → E := fun x ↦ criticalCofactorTangent H h basis x
  apply finite_zeroSet_of_finite_components_of_regularArcs
    H h τ hMzero hArc hH hh
  · intro x
    apply constraintFDeriv_ker_eq_span_criticalCofactorTangent_of_det_ne_zero
      H h h basis x hdim
    · exact constraintFDeriv_surjective_of_criticalDeterminant_ne_zero
        H h basis x (hdet x)
    · exact hdet x
  · intro x
    rw [← criticalDeterminant_eq_fderiv_criticalCofactorTangent
      H h basis x]
    exact hdet x

end AbelFormalization
