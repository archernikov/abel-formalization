import AbelFormalization.LexicographicInitialIdealLocalizationReverse
import AbelFormalization.MinimalPrimeLocalization
import AbelFormalization.RankOneIdealIterationBaseChange
import AbelFormalization.TerminalReindexedGlobalArtinianDescent

set_option autoImplicit false

/-!
# Localization of the terminal Stirling ideal iteration

Full lexicographic initial formation and the signed-Stirling automorphism both
commute with coefficient localization.  Hence every recursive ideal iterate
commutes with localization.  When the localized coefficient ring is
Artinian, the concrete global Artinian theorem supplies a localized stopping
index for the original iteration.
-/

noncomputable section

namespace AbelFormalization

universe u w

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {B : Type u} [CommRing B]
variable {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)

/-- Every terminal signed-Stirling initial-ideal iterate commutes with
localization of the coefficient ring. -/
theorem terminalReindexedLexicographicInitialIdealIteration_map_localization
    (S : Submonoid B)
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j : ℕ) :
    (lexicographicInitialIdealIteration
      (terminalReindexedMultiDegree d Time e)
      (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingEquiv Q j).map
        (MvPolynomial.map (algebraMap B (Localization S))) =
      lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e)
        (terminalReindexedGlobalStirlingEquiv
          (R := Localization S) d Time e).toRingEquiv
        (Q.map (MvPolynomial.map (algebraMap B (Localization S)))) j := by
  apply lexicographicInitialIdealIteration_map
    (terminalReindexedMultiDegree d Time e)
    (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).toRingEquiv
    (terminalReindexedGlobalStirlingEquiv
      (R := Localization S) d Time e).toRingEquiv
    (MvPolynomial.map (algebraMap B (Localization S)))
  · simpa using
      map_comp_terminalReindexedGlobalStirlingEquiv d Time e
        (algebraMap B (Localization S))
  · intro I
    exact lexicographicInitialIdeal_map_localization S
      (terminalReindexedMultiDegree d Time e) I

/-- If a coefficient localization is Artinian, the localized images of the
original terminal iteration stabilize permanently at a localized ideal fixed
by the localized Stirling automorphism. -/
theorem exists_terminalReindexedLocalizationIteration_stabilizes
    (S : Submonoid B) [IsArtinianRing (Localization S)]
    (monomialOrder : MonomialOrder (Fin n))
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ)))) :
    ∃ j₀ : ℕ,
      let sourceJ := (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingEquiv
      let localizedJ := (terminalReindexedGlobalStirlingEquiv
        (R := Localization S) d Time e).toRingEquiv
      let φ := MvPolynomial.map (algebraMap B (Localization S))
      ((lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) sourceJ Q j₀).map φ).map
          localizedJ.toRingHom =
        (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) sourceJ Q j₀).map φ ∧
      ∀ j, j₀ ≤ j →
        (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) sourceJ Q j).map φ =
        (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) sourceJ Q j₀).map φ := by
  let sourceJ := (terminalReindexedGlobalStirlingEquiv
    (R := B) d Time e).toRingEquiv
  let localizedJ := (terminalReindexedGlobalStirlingEquiv
    (R := Localization S) d Time e).toRingEquiv
  let φ : MvPolynomial (Fin n) B →+*
      MvPolynomial (Fin n) (Localization S) :=
    MvPolynomial.map (algebraMap B (Localization S))
  let Qloc := Q.map φ
  have hQloc : Qloc.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule (Localization S)
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ))) := by
    exact mvPolynomial_ideal_map_isHomogeneous
      (algebraMap B (Localization S))
      (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ)) Q hQ
  obtain ⟨j₀, hfixed, hstable⟩ :=
    exists_terminalReindexedLexicographicInitialIdealIteration_stabilizes_global
      (B := Localization S) d Time monomialOrder e Qloc hQloc
  have hbase (j : ℕ) :
      (lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e) sourceJ Q j).map φ =
      lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d Time e) localizedJ Qloc j := by
    exact terminalReindexedLexicographicInitialIdealIteration_map_localization
      (B := B) d Time S e Q j
  refine ⟨j₀, ?_, ?_⟩
  · calc
      ((lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) sourceJ Q j₀).map φ).map
          localizedJ.toRingHom =
        (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) localizedJ Qloc j₀).map
            localizedJ.toRingHom := by rw [hbase j₀]
      _ = lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) localizedJ Qloc j₀ := hfixed
      _ = (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) sourceJ Q j₀).map φ :=
        (hbase j₀).symm
  · intro j hj
    calc
      (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) sourceJ Q j).map φ =
        lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) localizedJ Qloc j := hbase j
      _ = lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) localizedJ Qloc j₀ :=
        hstable j hj
      _ = (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) sourceJ Q j₀).map φ :=
        (hbase j₀).symm

/-- The localization away from all minimal primes is Artinian, so the
localized terminal iteration always stabilizes over a Noetherian coefficient
ring. -/
theorem exists_terminalReindexedMinimalPrimeLocalizationIteration_stabilizes
    [IsNoetherianRing B]
    (monomialOrder : MonomialOrder (Fin n))
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ)))) :
    let S := minimalPrimeAvoidanceSubmonoid B
    ∃ j₀ : ℕ,
      let sourceJ := (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingEquiv
      let localizedJ := (terminalReindexedGlobalStirlingEquiv
        (R := Localization S) d Time e).toRingEquiv
      let φ := MvPolynomial.map (algebraMap B (Localization S))
      ((lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) sourceJ Q j₀).map φ).map
          localizedJ.toRingHom =
        (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) sourceJ Q j₀).map φ ∧
      ∀ j, j₀ ≤ j →
        (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) sourceJ Q j).map φ =
        (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e) sourceJ Q j₀).map φ := by
  let S := minimalPrimeAvoidanceSubmonoid B
  let _ : IsArtinianRing (Localization S) :=
    minimalPrimeAvoidanceLocalization_isArtinianRing
      (B := B) (T := Localization S)
  exact exists_terminalReindexedLocalizationIteration_stabilizes
    (B := B) d Time S monomialOrder e Q hQ

end AbelFormalization
