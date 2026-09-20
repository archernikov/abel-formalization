import AbelFormalization.MonomialUpperFamilyGeneratorBounds
import AbelFormalization.PolynomialModuleHilbert
import AbelFormalization.PolynomialModuleHomogeneousGenerators

set_option autoImplicit false

/-!
# Uniform homogeneous generator degrees from actual weighted Hilbert data

The degree bound is chosen from the finite family
of possible actual leading upper families before the original submodule is
chosen. The actual Hilbert correspondence puts each homogeneous submodule
in that finite family, and actual cancellation lifts the selected finite
leading cover to homogeneous generators of exactly those degrees.
-/

noncomputable section

namespace AbelFormalization

variable {K : Type*} [Field K] {n r : ℕ}

/-- One degree bound works for every actual homogeneous polynomial
submodule having the specified weighted-piece dimensions. The generators
have actual leading indices in a finite cover, and their precise shifted
weighted degrees are retained. -/
theorem exists_uniform_homogeneous_polynomialModule_generator_degree
    (m : MonomialOrder (Fin n)) (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ) (h : ℤ → ℕ) :
    ∃ D : ℕ,
      ∀ N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K),
        IsWeightedPolynomialModuleHomogeneous weight shift N →
        (∀ degree : ℤ, Module.finrank K
          ((N.restrictScalars K ⊓ weightedPolynomialModulePiece weight shift degree) :
            Submodule K (Fin r → MvPolynomial (Fin n) K)) = h degree) →
        ∃ s : Finset (Fin r × (Fin n →₀ ℕ)),
          ∃ G : {t // t ∈ s} → (Fin r → MvPolynomial (Fin n) K),
            (∀ t, G t ∈ N ∧
              G t ∈ weightedPolynomialModulePiece weight shift
                (shiftedModuleMonomialDegree weight shift t.val) ∧
              IsPolynomialModuleLeadingTerm m (G t) t.val ∧
              shiftedModuleMonomialDegree weight shift t.val ≤ (D : ℤ)) ∧
            Submodule.span (MvPolynomial (Fin n) K) (Set.range G) = N := by
  obtain ⟨D, hD⟩ := monomialUpperFamily_fixed_weightedCounts_cover_degree_bound
    weight hweight shift h
  refine ⟨D, ?_⟩
  intro N hN hdim
  have hcount : ∀ degree, monomialUpperFamilyWeightedDegreeCount weight shift
      (polynomialModuleLeadingUpperFamily m N) degree = h degree := by
    intro degree
    exact (finrank_polynomialModule_weightedPiece_eq_leadingCount
      m weight hweight shift N hN degree).symm.trans (hdim degree)
  obtain ⟨s, hsmem, hscover, hsdegree⟩ := hD (polynomialModuleLeadingUpperFamily m N) hcount
  have hwitness : ∀ t ∈ s, ∃ P ∈ N, IsPolynomialModuleLeadingTerm m P t := by
    intro t ht
    exact (mem_polynomialModuleLeadingUpperFamily m N t.1 t.2).mp (hsmem t ht)
  have hcover : ∀ P ∈ N, ∀ t, IsPolynomialModuleLeadingTerm m P t →
      ∃ u ∈ s, u.1 = t.1 ∧ u.2 ≤ t.2 := by
    intro P hPN t hP
    exact hscover t.1 t.2
      ((mem_polynomialModuleLeadingUpperFamily m N t.1 t.2).mpr ⟨P, hPN, hP⟩)
  obtain ⟨G, hG, hspan⟩ :=
    exists_homogeneous_polynomialModule_generators_from_leadingCover
      m weight shift N hN s hwitness hcover
  exact ⟨s, G, fun t => ⟨(hG t).1, (hG t).2.1, (hG t).2.2,
    hsdegree t.val t.property⟩, hspan⟩

/-- The same uniform bound stated directly as a finite set of actual
homogeneous generators, without retaining their term indices. -/
theorem exists_uniform_finite_homogeneous_polynomialModule_generators
    (m : MonomialOrder (Fin n)) (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ) (h : ℤ → ℕ) :
    ∃ D : ℕ,
      ∀ N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K),
        IsWeightedPolynomialModuleHomogeneous weight shift N →
        (∀ degree : ℤ, Module.finrank K
          ((N.restrictScalars K ⊓ weightedPolynomialModulePiece weight shift degree) :
            Submodule K (Fin r → MvPolynomial (Fin n) K)) = h degree) →
        ∃ S : Finset (Fin r → MvPolynomial (Fin n) K),
          (∀ P ∈ S, P ∈ N ∧ ∃ degree : ℤ,
            degree ≤ (D : ℤ) ∧ P ∈ weightedPolynomialModulePiece weight shift degree) ∧
          Submodule.span (MvPolynomial (Fin n) K) (S : Set _) = N := by
  classical
  obtain ⟨D, hD⟩ := exists_uniform_homogeneous_polynomialModule_generator_degree
    (K := K) m weight hweight shift h
  refine ⟨D, ?_⟩
  intro N hN hdim
  obtain ⟨s, G, hG, hspan⟩ := hD N hN hdim
  let S : Finset (Fin r → MvPolynomial (Fin n) K) := Finset.univ.image G
  refine ⟨S, ?_, ?_⟩
  · intro P hPS
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hPS
    exact ⟨(hG t).1, shiftedModuleMonomialDegree weight shift t.val,
      (hG t).2.2.2, (hG t).2.1⟩
  · have hS : (S : Set (Fin r → MvPolynomial (Fin n) K)) = Set.range G := by
      simp only [S, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [hS]
    exact hspan

end AbelFormalization
