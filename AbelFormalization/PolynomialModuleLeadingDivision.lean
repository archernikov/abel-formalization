import AbelFormalization.PolynomialModuleLeadingSubmodule

set_option autoImplicit false

/-!
# Actual generator lifting by leading-term cancellation

An explicit well-founded induction on the actual leading term proves that
a set of reducers generates the original module
when its leading terms divide all actual leading terms. Dickson's finite
upper-set generators then select a finite family of original witnesses.
No generation, division solvability, or Hilbert-preservation conclusion is
assumed. A witness-property wrapper allows the separate actual homogeneous
projection theorem to select homogeneous generators.
-/

noncomputable section

namespace AbelFormalization

variable {K : Type*} [Field K] {n r : ℕ}

/-- A submodule containing a reducer at each actual leading index contains
the entire original submodule. Cancellation is performed on actual vectors
and induction uses the proved well-founded leading-term order. -/
theorem polynomialModule_le_of_matching_leading_reducers
    (m : MonomialOrder (Fin n))
    (N T : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K))
    (hTN : T ≤ N)
    (hcover : ∀ P ∈ N, ∀ t, IsPolynomialModuleLeadingTerm m P t →
      ∃ Q ∈ T, IsPolynomialModuleLeadingTerm m Q t) : N ≤ T := by
  classical
  have hall : ∀ P : {P : Fin r → MvPolynomial (Fin n) K // P ≠ 0},
      P.val ∈ N → P.val ∈ T := by
    intro P
    induction P using (polynomialModuleLeadingTerm_wellFounded m).induction with
    | h P ih =>
      intro hPN
      let t := polynomialModuleLeadingTerm m P.val P.property
      have hP : IsPolynomialModuleLeadingTerm m P.val t :=
        polynomialModuleLeadingTerm_spec m P.val P.property
      obtain ⟨Q, hQT, hQ⟩ := hcover P.val hPN t hP
      let c : K := (P.val t.1).coeff t.2 / (Q t.1).coeff t.2
      let R : Fin r → MvPolynomial (Fin n) K := P.val - c • Q
      have hcQT : c • Q ∈ T := (T.restrictScalars K).smul_mem c hQT
      have hRN : R ∈ N := N.sub_mem hPN (hTN hcQT)
      have hRT : R ∈ T := by
        by_cases hR : R = 0
        · simpa only [hR] using T.zero_mem
        · apply ih ⟨R, hR⟩ ?_ hRN
          exact polynomialModule_sub_scaled_terms_lt hP hQ
            (polynomialModuleLeadingTerm_spec m R hR).1
      have hrecover : P.val = R + c • Q := by
        dsimp only [R]
        abel
      rw [hrecover]
      exact T.add_mem hRT hcQT
  intro P hPN
  by_cases hP : P = 0
  · simpa only [hP] using T.zero_mem
  · exact hall ⟨P, hP⟩ hPN

/-- Actual leading-term divisibility suffices for a selected set of module
vectors to generate the original polynomial submodule. -/
theorem polynomialModule_span_eq_of_leading_divisibility
    (m : MonomialOrder (Fin n))
    (N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K))
    (S : Set (Fin r → MvPolynomial (Fin n) K)) (hS : S ⊆ N)
    (hcover : ∀ P ∈ N, ∀ t, IsPolynomialModuleLeadingTerm m P t →
      ∃ Q ∈ S, ∃ u, IsPolynomialModuleLeadingTerm m Q u ∧
        u.1 = t.1 ∧ u.2 ≤ t.2) :
    Submodule.span (MvPolynomial (Fin n) K) S = N := by
  have hspan : Submodule.span (MvPolynomial (Fin n) K) S ≤ N :=
    Submodule.span_le.mpr hS
  apply le_antisymm hspan
  apply polynomialModule_le_of_matching_leading_reducers m N _ hspan
  intro P hPN t hP
  obtain ⟨Q, hQS, u, hQ, hucomp, hule⟩ := hcover P hPN t hP
  refine ⟨(MvPolynomial.monomial (t.2 - u.2) (1 : K)) • Q,
    (Submodule.span (MvPolynomial (Fin n) K) S).smul_mem _ (Submodule.subset_span hQS), ?_⟩
  simpa only [polynomialModuleTermTranslate, hucomp, tsub_add_cancel_of_le hule] using
    hQ.monomial_smul (t.2 - u.2)

/-- Lifting a specified finite leading cover preserves a property indexed by
its actual leading terms. This version retains the degree of every chosen
term, which is needed for subsequent uniform degree bounds. -/
theorem exists_polynomialModule_generators_from_leadingCover
    (m : MonomialOrder (Fin n))
    (N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K))
    (s : Finset (Fin r × (Fin n →₀ ℕ)))
    (H : (Fin r × (Fin n →₀ ℕ)) → (Fin r → MvPolynomial (Fin n) K) → Prop)
    (hwitness : ∀ t ∈ s, ∃ Q ∈ N, H t Q ∧ IsPolynomialModuleLeadingTerm m Q t)
    (hcover : ∀ P ∈ N, ∀ t, IsPolynomialModuleLeadingTerm m P t →
      ∃ u ∈ s, u.1 = t.1 ∧ u.2 ≤ t.2) :
    ∃ G : {t // t ∈ s} → (Fin r → MvPolynomial (Fin n) K),
      (∀ t, G t ∈ N ∧ H t.val (G t) ∧ IsPolynomialModuleLeadingTerm m (G t) t.val) ∧
      Submodule.span (MvPolynomial (Fin n) K) (Set.range G) = N := by
  classical
  choose G hGN hGH hGlead using fun t : {t // t ∈ s} => hwitness t.val t.property
  refine ⟨G, fun t => ⟨hGN t, hGH t, hGlead t⟩, ?_⟩
  apply polynomialModule_span_eq_of_leading_divisibility m N (Set.range G)
  · rintro Q ⟨t, rfl⟩
    exact hGN t
  · intro P hPN t hP
    obtain ⟨u, hus, hucomp, hule⟩ := hcover P hPN t hP
    exact ⟨G ⟨u, hus⟩, ⟨⟨u, hus⟩, rfl⟩, u, hGlead ⟨u, hus⟩, hucomp, hule⟩

/-- Select finitely many actual leading witnesses from the finite Dickson
generators of each leading exponent upper set. The optional property is
preserved by selecting witnesses with that property, not by assuming that
they already generate the module. -/
theorem exists_finite_polynomialModule_leading_representatives
    (m : MonomialOrder (Fin n))
    (N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K))
    (H : (Fin r → MvPolynomial (Fin n) K) → Prop)
    (hH : ∀ t, (∃ P ∈ N, IsPolynomialModuleLeadingTerm m P t) →
      ∃ Q ∈ N, H Q ∧ IsPolynomialModuleLeadingTerm m Q t) :
    ∃ S : Finset (Fin r → MvPolynomial (Fin n) K),
      (∀ Q ∈ S, Q ∈ N ∧ H Q) ∧
      ∀ P ∈ N, ∀ t, IsPolynomialModuleLeadingTerm m P t →
        ∃ Q ∈ S, ∃ u, IsPolynomialModuleLeadingTerm m Q u ∧
          u.1 = t.1 ∧ u.2 ≤ t.2 := by
  classical
  choose s hs using fun k : Fin r =>
    monomialUpperSet_exists_finset_generators (polynomialModuleLeadingUpperFamily m N k)
  let A := Σ k : Fin r, {x : Fin n → ℕ // x ∈ s k}
  have hwitness (a : A) : ∃ Q ∈ N, H Q ∧
      IsPolynomialModuleLeadingTerm m Q (a.1, Finsupp.equivFunOnFinite.symm a.2.val) := by
    apply hH
    apply (mem_polynomialModuleLeadingUpperFamily m N a.1 _).mp
    exact (hs a.1 a.2.val).mpr ⟨a.2.val, a.2.property, le_rfl⟩
  choose Q hQN hQH hQlead using hwitness
  let S : Finset (Fin r → MvPolynomial (Fin n) K) := Finset.univ.image Q
  refine ⟨S, ?_, ?_⟩
  · intro P hPS
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hPS
    exact ⟨hQN a, hQH a⟩
  · intro P hPN t hP
    have ht : (t.2 : Fin n → ℕ) ∈ polynomialModuleLeadingUpperFamily m N t.1 :=
      (mem_polynomialModuleLeadingUpperFamily m N t.1 t.2).mpr ⟨P, hPN, hP⟩
    obtain ⟨x, hxs, hxt⟩ := (hs t.1 (t.2 : Fin n → ℕ)).mp ht
    let a : A := ⟨t.1, ⟨x, hxs⟩⟩
    refine ⟨Q a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩,
      (t.1, Finsupp.equivFunOnFinite.symm x), hQlead a, rfl, ?_⟩
    exact hxt

/-- The selected finite leading witnesses generate by actual cancellation,
while retaining any property supplied by the witness selection theorem. -/
theorem exists_finite_polynomialModule_generators_of_leading_witnesses
    (m : MonomialOrder (Fin n))
    (N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K))
    (H : (Fin r → MvPolynomial (Fin n) K) → Prop)
    (hH : ∀ t, (∃ P ∈ N, IsPolynomialModuleLeadingTerm m P t) →
      ∃ Q ∈ N, H Q ∧ IsPolynomialModuleLeadingTerm m Q t) :
    ∃ S : Finset (Fin r → MvPolynomial (Fin n) K),
      (∀ Q ∈ S, Q ∈ N ∧ H Q) ∧
      Submodule.span (MvPolynomial (Fin n) K) (S : Set _) = N := by
  obtain ⟨S, hS, hcover⟩ := exists_finite_polynomialModule_leading_representatives m N H hH
  exact ⟨S, hS, polynomialModule_span_eq_of_leading_divisibility m N S
    (fun Q hQ => (hS Q hQ).1) hcover⟩

/-- Every actual finite free polynomial submodule over a field has a finite
family of original vectors generating it, proved here by leading-term
cancellation and Dickson's lemma. -/
theorem exists_finite_polynomialModule_generators (m : MonomialOrder (Fin n))
    (N : Submodule (MvPolynomial (Fin n) K) (Fin r → MvPolynomial (Fin n) K)) :
    ∃ S : Finset (Fin r → MvPolynomial (Fin n) K),
      (∀ Q ∈ S, Q ∈ N) ∧ Submodule.span (MvPolynomial (Fin n) K) (S : Set _) = N := by
  obtain ⟨S, hS, hspan⟩ := exists_finite_polynomialModule_generators_of_leading_witnesses
    m N (fun _ => True) (by
      intro t ht
      obtain ⟨P, hPN, hP⟩ := ht
      exact ⟨P, hPN, trivial, hP⟩)
  exact ⟨S, fun Q hQ => (hS Q hQ).1, hspan⟩

end AbelFormalization
