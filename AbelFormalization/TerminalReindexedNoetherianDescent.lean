import AbelFormalization.TerminalReindexedSandwichRecurrence
import AbelFormalization.TerminalReindexedPrincipalQuotientIteration

set_option autoImplicit false

/-!
# Noetherian descent for the reindexed terminal Stirling iteration

This module closes the induction on the Krull-dimension bound.  In positive
dimension we first stabilize after localization away from the minimal primes,
contract the stable ideal, and clear one denominator.  The two resulting
sandwiches, for an iterate and its Stirling image, persist along the tail.
After reducing coefficients modulo that denominator, the induction hypothesis
gives a fixed quotient iterate.  Saturation of the localization contraction
then lifts fixedness back to the source.  Fixedness is permanent because every
term of the iteration is homogeneous for the full terminal multigrading.
-/

noncomputable section

namespace AbelFormalization

universe u w

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Homogeneity of the localization contraction -/

/-- The contraction of a localized terminal iterate is homogeneous for the
terminal multigrading.  This is the homogeneity input used both to propagate
the denominator sandwich and to commute initial formation with the principal
coefficient quotient. -/
theorem terminalReindexedLocalizationContraction_multiHomogeneous
    {B : Type u} [CommRing B] {h n : ℕ}
    (d : Fin h → ℕ) (Time : Type w)
    (S : Submonoid B)
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j : ℕ) :
    let φ := MvPolynomial.map (algebraMap B (Localization S))
    let sourceJ := (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).toRingEquiv
    let I_j := lexicographicInitialIdealIteration
      (terminalReindexedMultiDegree d Time e) sourceJ Q j
    let L := I_j.map φ
    let K := L.comap φ
    K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i))) := by
  let φ : MvPolynomial (Fin n) B →+*
      MvPolynomial (Fin n) (Localization S) :=
    MvPolynomial.map (algebraMap B (Localization S))
  let sourceJ := (terminalReindexedGlobalStirlingEquiv
    (R := B) d Time e).toRingEquiv
  let localizedJ := (terminalReindexedGlobalStirlingEquiv
    (R := Localization S) d Time e).toRingEquiv
  let I_j := lexicographicInitialIdealIteration
    (terminalReindexedMultiDegree d Time e) sourceJ Q j
  let L := I_j.map φ
  let K := L.comap φ
  have hL : L.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule (Localization S)
        (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i))) := by
    rw [show L = lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e) localizedJ
        (Q.map φ) j by
      simpa only [L, I_j, φ, sourceJ, localizedJ] using
        terminalReindexedLexicographicInitialIdealIteration_map_localization
          (B := B) d Time S e Q j]
    exact lexicographicInitialIdealIteration_isHomogeneous
      (terminalReindexedMultiDegree d Time e) localizedJ (Q.map φ) j
  simpa only [K, L, φ] using
    mvPolynomial_ideal_comap_isHomogeneous
      (algebraMap B (Localization S))
      (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i)) L hL

/-! ## Dimension zero -/

/-- Dimension zero reduces to the global Artinian theorem. -/
theorem exists_terminalReindexedLexicographicInitialIdealIteration_stabilizes_of_krullDimLE_zero
    {B : Type u} [CommRing B] [IsNoetherianRing B] [Ring.KrullDimLE 0 B]
    {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)
    (monomialOrder : MonomialOrder (Fin n))
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ)))) :
    let multiDegree := terminalReindexedMultiDegree d Time e
    let J := (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).toRingEquiv
    ∃ j₀ : ℕ,
      (lexicographicInitialIdealIteration multiDegree J Q j₀).map
          J.toRingHom =
        lexicographicInitialIdealIteration multiDegree J Q j₀ ∧
      ∀ j, j₀ ≤ j →
        lexicographicInitialIdealIteration multiDegree J Q j =
          lexicographicInitialIdealIteration multiDegree J Q j₀ := by
  let _ : IsArtinianRing B :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact exists_terminalReindexedLexicographicInitialIdealIteration_stabilizes_global
    (B := B) d Time monomialOrder e Q hQ

/-! ## Successor dimension -/

/-- The positive-dimensional step.  The induction input is deliberately
stated only for principal quotients of `B`, and asks only for one quotient
iterate fixed by the quotient terminal automorphism.  The localization,
sandwich recurrence, lifting, and permanence conclusions are all proved in
this theorem. -/
theorem exists_terminalReindexedLexicographicInitialIdealIteration_stabilizes_of_krullDimLE_succ
    {B : Type u} [CommRing B] [IsNoetherianRing B]
    (krullDim : ℕ) [Ring.KrullDimLE (krullDim + 1) B]
    {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)
    (monomialOrder : MonomialOrder (Fin n))
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ))))
    (hquotient :
      ∀ (b : B),
        Ring.KrullDimLE krullDim (B ⧸ Ideal.span {b}) →
        ∀ Qbar : Ideal
            (MvPolynomial (Fin n) (B ⧸ Ideal.span {b})),
          Qbar.IsHomogeneous
              (MvPolynomial.weightedHomogeneousSubmodule
                (B ⧸ Ideal.span {b})
                (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ))) →
          ∃ j₂ : ℕ,
            (lexicographicInitialIdealIteration
                (terminalReindexedMultiDegree d Time e)
                (terminalReindexedGlobalStirlingEquiv
                  (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv
                Qbar j₂).map
                (terminalReindexedGlobalStirlingEquiv
                  (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv.toRingHom =
              lexicographicInitialIdealIteration
                (terminalReindexedMultiDegree d Time e)
                (terminalReindexedGlobalStirlingEquiv
                  (R := B ⧸ Ideal.span {b}) d Time e).toRingEquiv
                Qbar j₂) :
    let multiDegree := terminalReindexedMultiDegree d Time e
    let J := (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).toRingEquiv
    ∃ j₀ : ℕ,
      (lexicographicInitialIdealIteration multiDegree J Q j₀).map
          J.toRingHom =
        lexicographicInitialIdealIteration multiDegree J Q j₀ ∧
      ∀ j, j₀ ≤ j →
        lexicographicInitialIdealIteration multiDegree J Q j =
          lexicographicInitialIdealIteration multiDegree J Q j₀ := by
  let S : Submonoid B := minimalPrimeAvoidanceSubmonoid B
  obtain ⟨j₁, hlocalizedFixed, _hlocalizedStable⟩ :=
    exists_terminalReindexedMinimalPrimeLocalizationIteration_stabilizes
      (B := B) d Time monomialOrder e Q hQ
  let φ : MvPolynomial (Fin n) B →+*
      MvPolynomial (Fin n) (Localization S) :=
    MvPolynomial.map (algebraMap B (Localization S))
  let sourceJ := (terminalReindexedGlobalStirlingEquiv
    (R := B) d Time e).toRingEquiv
  let I := lexicographicInitialIdealIteration
    (terminalReindexedMultiDegree d Time e) sourceJ Q
  let L : Ideal (MvPolynomial (Fin n) (Localization S)) :=
    (I j₁).map φ
  let K : Ideal (MvPolynomial (Fin n) B) := L.comap φ
  have hcontraction :
      K.FG ∧ K.map φ = L ∧ K.map sourceJ.toRingHom = K ∧
        ∃ b : S,
          Ideal.span {MvPolynomial.C (b : B)} * K ≤ I j₁ ∧
            I j₁ ≤ K := by
    simpa only [K, L, I, φ, sourceJ] using
      terminalReindexedIteration_localizationContraction_sandwich
        (B := B) d Time S e Q j₁ hlocalizedFixed
  obtain ⟨_hKfg, _hKmap, hKinv, b, hbaseLower, hbaseUpper⟩ :=
    hcontraction
  have hKhom : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i))) := by
    simpa only [K, L, I, φ, sourceJ] using
      terminalReindexedLocalizationContraction_multiHomogeneous
        (B := B) d Time S e Q j₁
  have hKsat : ∀ P : MvPolynomial (Fin n) B,
      MvPolynomial.C (b : B) * P ∈ K → P ∈ K := by
    intro P hP
    exact (mvPolynomial_C_mul_mem_localizationContraction_iff
      S L b P).mp (by simpa only [K] using hP)
  have hsourceSandwich : TerminalReindexedTailSandwich
      d Time e Q j₁ (b : B) K :=
    terminalReindexedLexicographicInitialIdealIteration_shifted_sandwich
      d Time e (b : B) K Q j₁ hKhom hKinv
        hbaseLower hbaseUpper
  have hmappedSandwich : TerminalReindexedMappedTailSandwich
      d Time e Q j₁ (b : B) K :=
    terminalReindexedLexicographicInitialIdealIteration_shifted_map_sandwich
      d Time e (b : B) K Q j₁ hKhom hKinv
        hbaseLower hbaseUpper
  have hbAvoids : ∀ p ∈ minimalPrimes B, (b : B) ∉ p := by
    simpa only [S, mem_minimalPrimeAvoidanceSubmonoid] using b.property
  have hquotientDim :
      Ring.KrullDimLE krullDim (B ⧸ Ideal.span {(b : B)}) :=
    Ring.KrullDimLE.quotient_span_singleton_of_avoids_minimalPrimes
      krullDim hbAvoids
  let Qbar : Ideal
      (MvPolynomial (Fin n) (B ⧸ Ideal.span {(b : B)})) :=
    terminalReindexedPrincipalQuotientSeed d Time e Q j₁ (b : B)
  have hQbar : Qbar.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule
        (B ⧸ Ideal.span {(b : B)})
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ))) := by
    simpa only [Qbar] using
      terminalReindexedPrincipalQuotientSeed_ordinaryHomogeneous
        (B := B) d Time e Q hQ j₁ (b : B)
  obtain ⟨j₂, hquotientFixed⟩ :=
    hquotient (b : B) hquotientDim Qbar hQbar
  let j₀ : ℕ := j₁ + 1 + j₂
  have hfixed : (I j₀).map sourceJ.toRingHom = I j₀ := by
    simpa only [I, sourceJ, Qbar, j₀] using
      terminalReindexedPrincipalQuotient_fixed_of_sandwich
        (B := B) d Time e Q j₁ (b : B) K hKhom hKsat
          hsourceSandwich hmappedSandwich j₂ hquotientFixed
  have hpermanent : ∀ k : ℕ, I (j₀ + k) = I j₀ := by
    simpa only [I, sourceJ] using
      lexicographicInitialIdealIteration_permanent_of_map_fixed
        (terminalReindexedMultiDegree d Time e) sourceJ Q j₀ hfixed
  refine ⟨j₀, ?_, ?_⟩
  · simpa only [I, sourceJ] using hfixed
  · intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    simpa only [I, sourceJ] using hpermanent k

/-! ## Full induction -/

/-- The reindexed terminal signed-Stirling lexicographic-initial iteration
stabilizes permanently over every Noetherian coefficient ring with a finite
upper bound on Krull dimension. -/
theorem exists_terminalReindexedLexicographicInitialIdealIteration_stabilizes_of_krullDimLE
    (krullDim : ℕ)
    {B : Type u} [CommRing B] [IsNoetherianRing B]
    [Ring.KrullDimLE krullDim B]
    {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)
    (monomialOrder : MonomialOrder (Fin n))
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ)))) :
    let multiDegree := terminalReindexedMultiDegree d Time e
    let J := (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).toRingEquiv
    ∃ j₀ : ℕ,
      (lexicographicInitialIdealIteration multiDegree J Q j₀).map
          J.toRingHom =
        lexicographicInitialIdealIteration multiDegree J Q j₀ ∧
      ∀ j, j₀ ≤ j →
        lexicographicInitialIdealIteration multiDegree J Q j =
          lexicographicInitialIdealIteration multiDegree J Q j₀ := by
  induction krullDim generalizing B with
  | zero =>
      exact
        exists_terminalReindexedLexicographicInitialIdealIteration_stabilizes_of_krullDimLE_zero
          (B := B) d Time monomialOrder e Q hQ
  | succ krullDim ih =>
      apply
        exists_terminalReindexedLexicographicInitialIdealIteration_stabilizes_of_krullDimLE_succ
          (B := B) krullDim d Time monomialOrder e Q hQ
      intro b hdim Qbar hQbar
      let _ : Ring.KrullDimLE krullDim
          (B ⧸ Ideal.span {b}) := hdim
      obtain ⟨j₂, hfixed, _hpermanent⟩ :=
        ih (B := B ⧸ Ideal.span {b}) Qbar hQbar
      exact ⟨j₂, hfixed⟩

end AbelFormalization
