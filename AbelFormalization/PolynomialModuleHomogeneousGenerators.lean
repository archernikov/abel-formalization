import AbelFormalization.PolynomialModuleLeadingDivision
import AbelFormalization.PolynomialModuleHomogeneous

set_option autoImplicit false

/-!
# Actual finite homogeneous generator lifting

The original polynomial submodule is assumed closed under its actual shifted
weighted coefficient projections. The
proved projection theorem supplies homogeneous representatives of each
actual leading term, and the cancellation theorem proves generation.
Neither homogeneous generation nor a Hilbert identity is an assumption.
-/

noncomputable section

namespace AbelFormalization

variable {K : Type*} [Field K] {n r : ℕ}

/-- A homogeneous actual polynomial submodule over a field has finitely
many actual homogeneous generators. This holds for every natural variable
grade and integer component shift; positivity is unnecessary here. -/
theorem exists_finite_homogeneous_polynomialModule_generators
    (m : MonomialOrder (Fin n)) (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K))
    (hN : IsWeightedPolynomialModuleHomogeneous weight shift N) :
    ∃ S : Finset (Fin r → MvPolynomial (Fin n) K),
      (∀ Q ∈ S, Q ∈ N ∧ ∃ degree : ℤ,
        Q ∈ weightedPolynomialModulePiece weight shift degree) ∧
      Submodule.span (MvPolynomial (Fin n) K) (S : Set _) = N := by
  apply exists_finite_polynomialModule_generators_of_leading_witnesses m N
    (fun Q => ∃ degree : ℤ, Q ∈ weightedPolynomialModulePiece weight shift degree)
  intro t ht
  obtain ⟨P, hPN, hP⟩ := ht
  obtain ⟨Q, hQN, hQdegree, hQlead⟩ :=
    exists_homogeneous_polynomialModuleLeadingTerm m weight shift N hN hPN hP
  exact ⟨Q, hQN, ⟨shiftedModuleMonomialDegree weight shift t, hQdegree⟩, hQlead⟩

/-- A specified finite cover of the actual leading upper family lifts to
actual generators with exactly the corresponding weighted degrees. The
term-degree data are retained for the later uniform bound argument. -/
theorem exists_homogeneous_polynomialModule_generators_from_leadingCover
    (m : MonomialOrder (Fin n)) (weight : Fin n → ℕ) (shift : Fin r → ℤ)
    (N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K))
    (hN : IsWeightedPolynomialModuleHomogeneous weight shift N)
    (s : Finset (Fin r × (Fin n →₀ ℕ)))
    (hwitness : ∀ t ∈ s, ∃ P ∈ N, IsPolynomialModuleLeadingTerm m P t)
    (hcover : ∀ P ∈ N, ∀ t, IsPolynomialModuleLeadingTerm m P t →
      ∃ u ∈ s, u.1 = t.1 ∧ u.2 ≤ t.2) :
    ∃ G : {t // t ∈ s} → (Fin r → MvPolynomial (Fin n) K),
      (∀ t, G t ∈ N ∧ G t ∈ weightedPolynomialModulePiece weight shift
        (shiftedModuleMonomialDegree weight shift t.val) ∧
          IsPolynomialModuleLeadingTerm m (G t) t.val) ∧
      Submodule.span (MvPolynomial (Fin n) K) (Set.range G) = N := by
  apply exists_polynomialModule_generators_from_leadingCover m N s
    (fun t Q => Q ∈ weightedPolynomialModulePiece weight shift
      (shiftedModuleMonomialDegree weight shift t)) ?_ hcover
  intro t ht
  obtain ⟨P, hPN, hP⟩ := hwitness t ht
  exact exists_homogeneous_polynomialModuleLeadingTerm m weight shift N hN hPN hP

end AbelFormalization
