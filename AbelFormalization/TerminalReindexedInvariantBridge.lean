import AbelFormalization.HomogeneousCentralIteration
import AbelFormalization.TerminalReindexedNoetherianDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Reindexed descent and natural terminal invariants

The Noetherian descent theorem is stated after choosing an enumeration

`e : Fin n ≃ CentralPolynomialIndex (Fin h) d Time`,

whereas homogeneous central iteration uses the natural block/time variable
type.  This file proves the exact change-of-variables identity for full
lexicographic initial ideals, conjugates both ideal iterations, and transports
the fixed stabilized ideal back to the natural presentation.

The final theorem exposes all data needed by terminal elimination: exact
fixedness under the natural terminal Stirling automorphism, closure under the
actual `TerminalMultidegree` components, the public forward-invariance
predicate, and permanent stabilization of the natural-index iteration.
-/

noncomputable section

namespace AbelFormalization

universe u v w z

open scoped BigOperators

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Graded equivalences between two polynomial presentations -/

/-- A graded algebra equivalence between two polynomial variable types
commutes with the corresponding weighted homogeneous components. -/
theorem weightedHomogeneousComponent_algEquiv_between
    {R : Type u} {σ : Type v} {τ : Type w} {M : Type z}
    [CommRing R] [AddCommMonoid M] [DecidableEq M]
    (sourceWeight : σ → M) (targetWeight : τ → M)
    (E : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R)
    (hE : ∀ {P : MvPolynomial σ R} {degree : M},
      P.IsWeightedHomogeneous sourceWeight degree →
        (E P).IsWeightedHomogeneous targetWeight degree)
    (degree : M) (P : MvPolynomial σ R) :
    E (MvPolynomial.weightedHomogeneousComponent sourceWeight degree P) =
      MvPolynomial.weightedHomogeneousComponent targetWeight degree (E P) := by
  classical
  have hsum :
      (∑ other ∈ P.support.image (Finsupp.weight sourceWeight),
        MvPolynomial.weightedHomogeneousComponent
          sourceWeight other P) = P :=
    sum_weightedHomogeneousComponent_support sourceWeight P
  calc
    E (MvPolynomial.weightedHomogeneousComponent sourceWeight degree P) =
        E (MvPolynomial.weightedHomogeneousComponent sourceWeight degree
          (∑ other ∈ P.support.image (Finsupp.weight sourceWeight),
            MvPolynomial.weightedHomogeneousComponent
              sourceWeight other P)) := by
      rw [hsum]
    _ = MvPolynomial.weightedHomogeneousComponent targetWeight degree
        (E (∑ other ∈ P.support.image (Finsupp.weight sourceWeight),
          MvPolynomial.weightedHomogeneousComponent
            sourceWeight other P)) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro other hother
      have hsource :
          (MvPolynomial.weightedHomogeneousComponent sourceWeight other P).IsWeightedHomogeneous
            sourceWeight other :=
        MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
          other P
      have htarget := hE hsource
      by_cases hdegree : degree = other
      · subst other
        rw [hsource.weightedHomogeneousComponent_same,
          htarget.weightedHomogeneousComponent_same]
      · rw [hsource.weightedHomogeneousComponent_ne degree hdegree,
          map_zero,
          htarget.weightedHomogeneousComponent_ne degree hdegree]
    _ = MvPolynomial.weightedHomogeneousComponent targetWeight degree
        (E P) := by
      rw [hsum]

/-- A lexicographically graded equivalence between different polynomial
presentations commutes with the least-weight form. -/
theorem lexicographicInitialForm_algEquiv_between
    {R : Type u} {σ : Type v} {τ : Type w} [CommRing R] {k : ℕ}
    (sourceWeight : σ → Fin k → ℤ)
    (targetWeight : τ → Fin k → ℤ)
    (E : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R)
    (hE : ∀ {P : MvPolynomial σ R}
        {degree : Lex (Fin k → ℤ)},
      P.IsWeightedHomogeneous (fun i ↦ toLex (sourceWeight i)) degree →
        (E P).IsWeightedHomogeneous
          (fun i ↦ toLex (targetWeight i)) degree)
    (P : MvPolynomial σ R) :
    E (lexicographicInitialForm sourceWeight P) =
      lexicographicInitialForm targetWeight (E P) := by
  classical
  by_cases hP : P = 0
  · subst P
    simp
  let sourceLex : σ → Lex (Fin k → ℤ) :=
    fun i ↦ toLex (sourceWeight i)
  let targetLex : τ → Lex (Fin k → ℤ) :=
    fun i ↦ toLex (targetWeight i)
  let beta : Lex (Fin k → ℤ) :=
    lexicographicMinimumWeight sourceWeight P
  have hcomponent :
      E (MvPolynomial.weightedHomogeneousComponent sourceLex beta P) =
        MvPolynomial.weightedHomogeneousComponent targetLex beta (E P) :=
    weightedHomogeneousComponent_algEquiv_between
      sourceLex targetLex E hE beta P
  have hsourceComponent :
      MvPolynomial.weightedHomogeneousComponent sourceLex beta P ≠ 0 := by
    change lexicographicInitialForm sourceWeight P ≠ 0
    exact lexicographicInitialForm_ne_zero sourceWeight hP
  have htargetComponent :
      MvPolynomial.weightedHomogeneousComponent targetLex beta (E P) ≠ 0 := by
    intro hzero
    apply hsourceComponent
    apply E.injective
    rw [map_zero, hcomponent, hzero]
  have hbound : ∀ d ∈ (E P).support,
      beta ≤ Finsupp.weight targetLex d := by
    intro d hd
    by_contra hnot
    have hlt : Finsupp.weight targetLex d < beta := lt_of_not_ge hnot
    let gamma : Lex (Fin k → ℤ) := Finsupp.weight targetLex d
    have htargetGamma :
        MvPolynomial.weightedHomogeneousComponent
            targetLex gamma (E P) ≠ 0 := by
      intro hzero
      have hcoeff := congrArg
        (fun Q : MvPolynomial τ R ↦ Q.coeff d) hzero
      rw [MvPolynomial.coeff_weightedHomogeneousComponent,
        if_pos rfl, MvPolynomial.coeff_zero] at hcoeff
      exact (MvPolynomial.mem_support_iff.mp hd) hcoeff
    have hgammaComponent :
        E (MvPolynomial.weightedHomogeneousComponent sourceLex gamma P) =
          MvPolynomial.weightedHomogeneousComponent
            targetLex gamma (E P) :=
      weightedHomogeneousComponent_algEquiv_between
        sourceLex targetLex E hE gamma P
    have hsourceGamma :
        MvPolynomial.weightedHomogeneousComponent sourceLex gamma P ≠ 0 := by
      intro hzero
      apply htargetGamma
      rw [← hgammaComponent, hzero, map_zero]
    obtain ⟨m, hm⟩ :=
      MvPolynomial.support_nonempty.mpr hsourceGamma
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hm
    have hmSupport : m ∈ P.support := (Finset.mem_filter.mp hm).1
    have hmWeight : Finsupp.weight sourceLex m = gamma :=
      (Finset.mem_filter.mp hm).2
    have hminimum :=
      lexicographicMinimumWeight_le sourceWeight P hmSupport
    change beta ≤ Finsupp.weight sourceLex m at hminimum
    rw [hmWeight] at hminimum
    exact (not_lt_of_ge hminimum) hlt
  have hminimum : lexicographicMinimumWeight targetWeight (E P) = beta :=
    lexicographicMinimumWeight_eq_of_component_ne_zero
      targetWeight (E P) beta hbound htargetComponent
  change
    E (MvPolynomial.weightedHomogeneousComponent sourceLex beta P) =
      MvPolynomial.weightedHomogeneousComponent targetLex
        (lexicographicMinimumWeight targetWeight (E P)) (E P)
  rw [hcomponent, hminimum]

/-- Full lexicographic initial ideals commute with a graded equivalence
between different polynomial presentations. -/
theorem lexicographicInitialIdeal_map_algEquiv_between
    {R : Type u} {σ : Type v} {τ : Type w} [CommRing R] {k : ℕ}
    (sourceWeight : σ → Fin k → ℤ)
    (targetWeight : τ → Fin k → ℤ)
    (E : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R)
    (hE : ∀ {P : MvPolynomial σ R}
        {degree : Lex (Fin k → ℤ)},
      P.IsWeightedHomogeneous (fun i ↦ toLex (sourceWeight i)) degree →
        (E P).IsWeightedHomogeneous
          (fun i ↦ toLex (targetWeight i)) degree)
    (I : Ideal (MvPolynomial σ R)) :
    (lexicographicInitialIdeal sourceWeight I).map E.toRingHom =
      lexicographicInitialIdeal targetWeight (I.map E.toRingHom) := by
  apply le_antisymm
  · change
      (Ideal.span
        (lexicographicInitialForm sourceWeight ''
          (I : Set (MvPolynomial σ R)))).map E.toRingHom ≤ _
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
    change E (lexicographicInitialForm sourceWeight P) ∈ _
    rw [lexicographicInitialForm_algEquiv_between
      sourceWeight targetWeight E hE]
    exact lexicographicInitialForm_mem_initialIdeal targetWeight _
      (Ideal.mem_map_of_mem E.toRingHom hP)
  · change Ideal.span
        (lexicographicInitialForm targetWeight ''
          (I.map E.toRingHom : Set (MvPolynomial τ R))) ≤ _
    apply Ideal.span_le.mpr
    rintro _ ⟨Q, hQ, rfl⟩
    have hpre : E.symm Q ∈ I :=
      (Ideal.symm_apply_mem_of_equiv_iff
        (I := I) (f := E.toRingEquiv) (y := Q)).2 hQ
    have hform := lexicographicInitialForm_algEquiv_between
      sourceWeight targetWeight E hE (E.symm Q)
    rw [E.apply_symm_apply] at hform
    rw [← hform]
    exact Ideal.mem_map_of_mem E.toRingHom
      (lexicographicInitialForm_mem_initialIdeal
        sourceWeight I hpre)

/-- Mapping through a graded equivalence between polynomial presentations
preserves homogeneous ideals. -/
theorem ideal_map_algEquiv_isHomogeneous_between
    {R : Type u} {σ : Type v} {τ : Type w} {M : Type z}
    [CommRing R] [AddCommMonoid M] [DecidableEq M]
    (sourceWeight : σ → M) (targetWeight : τ → M)
    (E : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R)
    (hE : ∀ {P : MvPolynomial σ R} {degree : M},
      P.IsWeightedHomogeneous sourceWeight degree →
        (E P).IsWeightedHomogeneous targetWeight degree)
    (I : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R sourceWeight)) :
    (I.map E.toRingHom).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R targetWeight) := by
  let sourceGrade :=
    MvPolynomial.weightedHomogeneousSubmodule R sourceWeight
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists sourceGrade I).mp hI
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
  obtain ⟨degree, hdegree⟩ := P.property
  exact ⟨degree, hE hdegree⟩

/-- The same homogeneous-ideal transport only needs a ring homomorphism,
provided homogeneous polynomials of every degree are preserved. -/
theorem ideal_map_ringHom_isHomogeneous_between
    {R : Type u} {σ : Type v} {τ : Type w} {M : Type z}
    [CommRing R] [AddCommMonoid M] [DecidableEq M]
    (sourceWeight : σ → M) (targetWeight : τ → M)
    (F : MvPolynomial σ R →+* MvPolynomial τ R)
    (hF : ∀ {P : MvPolynomial σ R} {degree : M},
      P.IsWeightedHomogeneous sourceWeight degree →
        (F P).IsWeightedHomogeneous targetWeight degree)
    (I : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R sourceWeight)) :
    (I.map F).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R targetWeight) := by
  let sourceGrade :=
    MvPolynomial.weightedHomogeneousSubmodule R sourceWeight
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists sourceGrade I).mp hI
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
  obtain ⟨degree, hdegree⟩ := P.property
  exact ⟨degree, hF hdegree⟩

/-! ## Exact transport through the terminal finite reindexing -/

variable {R : Type u} [CommRing R]
variable {h n : ℕ} (d : Fin h → ℕ) (Time : Type v)

/-- Renaming the finite presentation to the natural terminal presentation
preserves the encoded lexicographic terminal degree. -/
theorem terminalReindexedRenameEquiv_preserves_lexHomogeneous
    (e : TerminalFiniteReindex (n := n) d Time)
    {P : MvPolynomial (Fin n) R} {degree : Lex (Fin h → ℤ)}
    (hP : P.IsWeightedHomogeneous
      (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i)) degree) :
    (terminalReindexedRenameEquiv (R := R) d Time e P).IsWeightedHomogeneous
        (fun x ↦ toLex (signedTerminalWeight d Time x)) degree := by
  change (MvPolynomial.renameEquiv R e P).IsWeightedHomogeneous _ degree
  apply weightedHomogeneous_renameEquiv (R := R) e
    (fun x ↦ toLex (signedTerminalWeight d Time x))
  have hweight :
      (fun i ↦ toLex (signedTerminalWeight d Time (e i))) =
        (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i)) := by
    funext i
    apply congrArg toLex
    funext b
    rfl
  change P.IsWeightedHomogeneous
    (fun i ↦ toLex (signedTerminalWeight d Time (e i))) degree
  rw [hweight]
  exact hP

/-- The least terminal-weight form itself commutes with the chosen finite
enumeration. -/
theorem terminalReindexedRenameEquiv_lexicographicInitialForm
    (e : TerminalFiniteReindex (n := n) d Time)
    (P : MvPolynomial (Fin n) R) :
    terminalReindexedRenameEquiv (R := R) d Time e
        (lexicographicInitialForm
          (terminalReindexedMultiDegree d Time e) P) =
      lexicographicInitialForm (signedTerminalWeight d Time)
        (terminalReindexedRenameEquiv (R := R) d Time e P) := by
  exact lexicographicInitialForm_algEquiv_between
    (terminalReindexedMultiDegree d Time e)
    (signedTerminalWeight d Time)
    (terminalReindexedRenameEquiv (R := R) d Time e)
    (fun hP ↦
      terminalReindexedRenameEquiv_preserves_lexHomogeneous
        d Time e hP) P

/-- Full terminal initial formation is unchanged by passing between the
finite enumeration and the natural block/time presentation. -/
theorem terminalReindexedRenameEquiv_lexicographicInitialIdeal
    (e : TerminalFiniteReindex (n := n) d Time)
    (I : Ideal (MvPolynomial (Fin n) R)) :
    (lexicographicInitialIdeal
        (terminalReindexedMultiDegree d Time e) I).map
          (terminalReindexedRenameEquiv (R := R) d Time e).toRingHom =
      lexicographicInitialIdeal (signedTerminalWeight d Time)
        (I.map
          (terminalReindexedRenameEquiv (R := R) d Time e).toRingHom) := by
  exact lexicographicInitialIdeal_map_algEquiv_between
    (terminalReindexedMultiDegree d Time e)
    (signedTerminalWeight d Time)
    (terminalReindexedRenameEquiv (R := R) d Time e)
    (fun hP ↦
      terminalReindexedRenameEquiv_preserves_lexHomogeneous
        d Time e hP) I

/-- Ring-homomorphism conjugacy built into the definition of the reindexed
terminal Stirling equivalence. -/
@[simp]
theorem terminalReindexedRenameEquiv_globalStirling_apply
    (e : TerminalFiniteReindex (n := n) d Time)
    (P : MvPolynomial (Fin n) R) :
    terminalReindexedRenameEquiv (R := R) d Time e
        (terminalReindexedGlobalStirlingEquiv
          (R := R) d Time e P) =
      terminalGlobalStirlingEquiv R (Fin h) d Time
        (terminalReindexedRenameEquiv (R := R) d Time e P) := by
  simp [terminalReindexedGlobalStirlingEquiv]

/-- Ring-homomorphism conjugacy built into the definition of the reindexed
terminal Stirling equivalence. -/
theorem terminalReindexedRenameEquiv_comp_globalStirling
    (e : TerminalFiniteReindex (n := n) d Time) :
    (terminalReindexedRenameEquiv (R := R) d Time e).toRingHom.comp
        (terminalReindexedGlobalStirlingEquiv
          (R := R) d Time e).toRingHom =
      (terminalGlobalStirlingEquiv R (Fin h) d Time).toRingHom.comp
        (terminalReindexedRenameEquiv (R := R) d Time e).toRingHom := by
  apply RingHom.ext
  intro P
  exact terminalReindexedRenameEquiv_globalStirling_apply d Time e P

/-- Ideal maps by the two conjugate terminal automorphisms commute with the
finite-to-natural rename. -/
theorem terminalReindexedRenameEquiv_ideal_map_globalStirling
    (e : TerminalFiniteReindex (n := n) d Time)
    (I : Ideal (MvPolynomial (Fin n) R)) :
    (I.map (terminalReindexedGlobalStirlingEquiv
        (R := R) d Time e).toRingHom).map
          (terminalReindexedRenameEquiv (R := R) d Time e).toRingHom =
      (I.map (terminalReindexedRenameEquiv
        (R := R) d Time e).toRingHom).map
          (terminalGlobalStirlingEquiv R (Fin h) d Time).toRingHom := by
  rw [Ideal.map_map, Ideal.map_map,
    terminalReindexedRenameEquiv_comp_globalStirling]

/-- The natural-index initial-ideal sequence is exactly the renamed
finite-index sequence at every step. -/
theorem terminalReindexedRenameEquiv_initialIteration
    (e : TerminalFiniteReindex (n := n) d (Fin 1 ⊕ Time))
    (Q : Ideal (MvPolynomial (Fin n) R)) (j : ℕ) :
    (lexicographicInitialIdealIteration
        (terminalReindexedMultiDegree d (Fin 1 ⊕ Time) e)
        (terminalReindexedGlobalStirlingEquiv
          (R := R) d (Fin 1 ⊕ Time) e).toRingEquiv Q j).map
      (terminalReindexedRenameEquiv
        (R := R) d (Fin 1 ⊕ Time) e).toRingHom =
    homogeneousTerminalInitialIteration R d Time
      (Q.map (terminalReindexedRenameEquiv
        (R := R) d (Fin 1 ⊕ Time) e).toRingHom) j := by
  induction j with
  | zero =>
      simpa only [lexicographicInitialIdealIteration_zero,
        homogeneousTerminalInitialIteration_zero] using
        terminalReindexedRenameEquiv_lexicographicInitialIdeal
          d (Fin 1 ⊕ Time) e Q
  | succ j ih =>
      rw [lexicographicInitialIdealIteration_succ,
        homogeneousTerminalInitialIteration_succ,
        terminalReindexedRenameEquiv_lexicographicInitialIdeal,
        terminalReindexedRenameEquiv_ideal_map_globalStirling, ih]

/-! ## Terminal invariants after renaming -/

/-- The lexicographic weight of a natural terminal monomial is the injective
encoding of its actual natural terminal multidegree. -/
theorem terminalGlobalLexWeight_eq_terminalMultidegreeToLex
    (m : CentralPolynomialIndex (Fin h) d Time →₀ ℕ) :
    Finsupp.weight
        (fun x ↦ toLex (signedTerminalWeight d Time x)) m =
      terminalMultidegreeToLex
        (Finsupp.weight (terminalGlobalWeight (Fin h) d Time) m) := by
  classical
  induction m using Finsupp.induction with
  | zero =>
      change toLex (fun _ : Fin h ↦ (0 : ℤ)) =
        toLex (fun _ : Fin h ↦ (0 : ℤ))
      rfl
  | @single_add x c m hx hc ih =>
      simp [Finsupp.weight_single, ih, signedTerminalWeight,
        terminalMultidegreeToLex, terminalMultidegreeCast,
        Nat.cast_add, Nat.cast_mul] <;>
        rfl

/-- An actual natural terminal component is the corresponding component for
the injective lexicographic encoding of terminal multidegrees. -/
theorem terminalGlobalComponent_eq_lexComponent
    (degree : TerminalMultidegree (Fin h))
    (P : CentralPolynomial R (Fin h) d Time) :
    terminalGlobalComponent R (Fin h) d Time degree P =
      MvPolynomial.weightedHomogeneousComponent
        (fun x ↦ toLex (signedTerminalWeight d Time x))
        (terminalMultidegreeToLex degree) P := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [terminalGlobalComponent_coeff,
    MvPolynomial.coeff_weightedHomogeneousComponent,
    terminalGlobalLexWeight_eq_terminalMultidegreeToLex]
  by_cases hm :
      Finsupp.weight (terminalGlobalWeight (Fin h) d Time) m = degree
  · simp [hm]
  · have hlex :
        terminalMultidegreeToLex
            (Finsupp.weight (terminalGlobalWeight (Fin h) d Time) m) ≠
          terminalMultidegreeToLex degree :=
      fun h => hm (terminalMultidegreeToLex_injective h)
    simp [hm, hlex]

/-- Renaming the finite component at an encoded terminal degree gives the
actual natural terminal component at that degree. -/
theorem terminalReindexedRenameEquiv_terminalGlobalComponent
    (e : TerminalFiniteReindex (n := n) d Time)
    (degree : TerminalMultidegree (Fin h))
    (P : MvPolynomial (Fin n) R) :
    terminalReindexedRenameEquiv (R := R) d Time e
        (MvPolynomial.weightedHomogeneousComponent
          (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i))
          (terminalMultidegreeToLex degree) P) =
      terminalGlobalComponent R (Fin h) d Time degree
        (terminalReindexedRenameEquiv (R := R) d Time e P) := by
  calc
    terminalReindexedRenameEquiv (R := R) d Time e
        (MvPolynomial.weightedHomogeneousComponent
          (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i))
          (terminalMultidegreeToLex degree) P) =
      MvPolynomial.weightedHomogeneousComponent
        (fun x ↦ toLex (signedTerminalWeight d Time x))
        (terminalMultidegreeToLex degree)
        (terminalReindexedRenameEquiv (R := R) d Time e P) :=
      weightedHomogeneousComponent_algEquiv_between
        (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i))
        (fun x ↦ toLex (signedTerminalWeight d Time x))
        (terminalReindexedRenameEquiv (R := R) d Time e)
        (fun hP ↦
          terminalReindexedRenameEquiv_preserves_lexHomogeneous
            d Time e hP)
        (terminalMultidegreeToLex degree) P
    _ = terminalGlobalComponent R (Fin h) d Time degree
        (terminalReindexedRenameEquiv (R := R) d Time e P) :=
      (terminalGlobalComponent_eq_lexComponent
        d Time degree
        (terminalReindexedRenameEquiv (R := R) d Time e P)).symm

/-- A reindexed ideal homogeneous for the encoded lexicographic grading
becomes an ideal closed under every actual terminal component after renaming. -/
theorem terminalReindexedRename_isTerminalMultigradedIdeal
    (e : TerminalFiniteReindex (n := n) d Time)
    (I : Ideal (MvPolynomial (Fin n) R))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i)))) :
    IsTerminalMultigradedIdeal R (Fin h) d Time
      (I.map (terminalReindexedRenameEquiv
        (R := R) d Time e).toRingHom) := by
  have hrename :
      (I.map (terminalReindexedRenameEquiv
        (R := R) d Time e).toRingHom).IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule R
            (fun x ↦ toLex (signedTerminalWeight d Time x))) :=
    ideal_map_algEquiv_isHomogeneous_between
      (fun i ↦ toLex (terminalReindexedMultiDegree d Time e i))
      (fun x ↦ toLex (signedTerminalWeight d Time x))
      (terminalReindexedRenameEquiv (R := R) d Time e)
      (fun hP ↦
        terminalReindexedRenameEquiv_preserves_lexHomogeneous
          d Time e hP) I hI
  intro P hP degree
  rw [terminalGlobalComponent_eq_lexComponent]
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem R
    (fun x ↦ toLex (signedTerminalWeight d Time x))
    hrename hP (terminalMultidegreeToLex degree)

/-- Exact fixedness is transported from the reindexed terminal automorphism
to the natural terminal automorphism. -/
theorem terminalReindexedRename_map_globalStirling_eq_of_fixed
    (e : TerminalFiniteReindex (n := n) d Time)
    (I : Ideal (MvPolynomial (Fin n) R))
    (hfixed : I.map (terminalReindexedGlobalStirlingEquiv
      (R := R) d Time e).toRingHom = I) :
    (I.map (terminalReindexedRenameEquiv
      (R := R) d Time e).toRingHom).map
        (terminalGlobalStirlingEquiv R (Fin h) d Time).toRingHom =
      I.map (terminalReindexedRenameEquiv
        (R := R) d Time e).toRingHom := by
  rw [← terminalReindexedRenameEquiv_ideal_map_globalStirling,
    hfixed]

/-- Reindexed fixedness therefore supplies the public natural forward
Stirling-invariance predicate. -/
theorem terminalReindexedRename_isTerminalGlobalStirlingInvariant
    (e : TerminalFiniteReindex (n := n) d Time)
    (I : Ideal (MvPolynomial (Fin n) R))
    (hfixed : I.map (terminalReindexedGlobalStirlingEquiv
      (R := R) d Time e).toRingHom = I) :
    IsTerminalGlobalStirlingInvariant R (Fin h) d Time
      (I.map (terminalReindexedRenameEquiv
        (R := R) d Time e).toRingHom) := by
  intro P hP
  rw [← terminalReindexedRename_map_globalStirling_eq_of_fixed
    d Time e I hfixed]
  exact Ideal.mem_map_of_mem
    (terminalGlobalStirlingEquiv R (Fin h) d Time).toRingHom hP

/-! ## Terminal invariants after setting the homogenizing variable to one -/

/-- Direct variable images for homogeneous central dehomogenization.  The
homogenizing variable goes to one, and all genuine central variables are
retained. -/
def homogeneousCentralDirectDehomogenizationVariable :
    CentralPolynomialIndex (Fin h) d (Fin 1 ⊕ Time) →
      CentralPolynomial R (Fin h) d Time
  | Sum.inl derivative => MvPolynomial.X (Sum.inl derivative)
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr t) => MvPolynomial.X (Sum.inr t)

/-- The direct evaluation presentation of homogeneous central
dehomogenization. -/
def homogeneousCentralDirectDehomogenization :
    CentralPolynomial R (Fin h) d (Fin 1 ⊕ Time) →+*
      CentralPolynomial R (Fin h) d Time :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (homogeneousCentralDirectDehomogenizationVariable
      (R := R) d Time)

/-- The direct evaluation presentation agrees exactly with the reassociated
dehomogenization map used by homogeneous central iteration. -/
theorem homogeneousCentralDirectDehomogenization_eq :
    homogeneousCentralDirectDehomogenization (R := R) d Time =
      homogeneousCentralDehomogenization R d Time := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [homogeneousCentralDirectDehomogenization]
  · intro x
    rcases x with ⟨b, i⟩ | (H | t)
    · simp [homogeneousCentralDirectDehomogenization,
        homogeneousCentralDirectDehomogenizationVariable]
    · simp [homogeneousCentralDirectDehomogenization,
        homogeneousCentralDirectDehomogenizationVariable]
    · simp [homogeneousCentralDirectDehomogenization,
        homogeneousCentralDirectDehomogenizationVariable]

/-- Setting `H = 1` preserves every genuine terminal multidegree because
`H`, like every time variable, has terminal degree zero. -/
theorem homogeneousCentralDehomogenization_preserves_terminalHomogeneous
    {P : CentralPolynomial R (Fin h) d (Fin 1 ⊕ Time)}
    {degree : TerminalMultidegree (Fin h)}
    (hP : P.IsWeightedHomogeneous
      (terminalGlobalWeight (Fin h) d (Fin 1 ⊕ Time)) degree) :
    (homogeneousCentralDehomogenization R d Time P).IsWeightedHomogeneous
        (terminalGlobalWeight (Fin h) d Time) degree := by
  rw [← homogeneousCentralDirectDehomogenization_eq (R := R) d Time]
  change
    (MvPolynomial.eval₂ MvPolynomial.C
      (homogeneousCentralDirectDehomogenizationVariable
        (R := R) d Time) P).IsWeightedHomogeneous
          (terminalGlobalWeight (Fin h) d Time) degree
  apply weightedHomogeneous_eval₂ hP
  · intro r
    exact MvPolynomial.isWeightedHomogeneous_C
      (terminalGlobalWeight (Fin h) d Time) r
  · intro x
    rcases x with ⟨b, i⟩ | (H | t)
    · simpa [homogeneousCentralDirectDehomogenizationVariable] using
        (MvPolynomial.isWeightedHomogeneous_X R
          (terminalGlobalWeight (Fin h) d Time)
          (Sum.inl ⟨b, i⟩))
    · simpa [homogeneousCentralDirectDehomogenizationVariable] using
        (MvPolynomial.isWeightedHomogeneous_one R
          (terminalGlobalWeight (Fin h) d Time))
    · simpa [homogeneousCentralDirectDehomogenizationVariable] using
        (MvPolynomial.isWeightedHomogeneous_X R
          (terminalGlobalWeight (Fin h) d Time)
          (Sum.inr t))

/-- Closure under all actual terminal components descends through `H = 1`. -/
theorem homogeneousCentralDehomogenization_isTerminalMultigradedIdeal
    (I : Ideal
      (CentralPolynomial R (Fin h) d (Fin 1 ⊕ Time)))
    (hI : IsTerminalMultigradedIdeal R (Fin h) d
      (Fin 1 ⊕ Time) I) :
    IsTerminalMultigradedIdeal R (Fin h) d Time
      (homogeneousCentralDehomogenizeIdeal R d Time I) := by
  have hsource : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (terminalGlobalWeight (Fin h) d (Fin 1 ⊕ Time))) := by
    intro degree P hP
    rw [← DirectSum.Decomposition.decompose'_eq]
    rw [MvPolynomial.weightedDecomposition.decompose'_apply]
    exact hI P hP degree
  have htarget :
      (homogeneousCentralDehomogenizeIdeal R d Time I).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule R
          (terminalGlobalWeight (Fin h) d Time)) := by
    simpa only [homogeneousCentralDehomogenizeIdeal] using
      ideal_map_ringHom_isHomogeneous_between
        (terminalGlobalWeight (Fin h) d (Fin 1 ⊕ Time))
        (terminalGlobalWeight (Fin h) d Time)
        (homogeneousCentralDehomogenization R d Time)
        (fun hP ↦
          homogeneousCentralDehomogenization_preserves_terminalHomogeneous
            d Time hP) I hsource
  intro P hP degree
  change MvPolynomial.weightedHomogeneousComponent
    (terminalGlobalWeight (Fin h) d Time) degree P ∈
      homogeneousCentralDehomogenizeIdeal R d Time I
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem R
    (terminalGlobalWeight (Fin h) d Time) htarget hP degree

/-- Exact Stirling fixedness descends through the dehomogenization commuting
square. -/
theorem homogeneousCentralDehomogenization_map_globalStirling_eq_of_fixed
    (I : Ideal
      (CentralPolynomial R (Fin h) d (Fin 1 ⊕ Time)))
    (hfixed : I.map
      (terminalGlobalStirlingEquiv R (Fin h) d
        (Fin 1 ⊕ Time)).toRingHom = I) :
    (homogeneousCentralDehomogenizeIdeal R d Time I).map
        (terminalGlobalStirlingEquiv R (Fin h) d Time).toRingHom =
      homogeneousCentralDehomogenizeIdeal R d Time I := by
  change
    (I.map (homogeneousCentralDehomogenization R d Time)).map
        (terminalGlobalStirlingEquiv R (Fin h) d Time).toRingHom =
      I.map (homogeneousCentralDehomogenization R d Time)
  calc
    (I.map (homogeneousCentralDehomogenization R d Time)).map
        (terminalGlobalStirlingEquiv R (Fin h) d Time).toRingHom =
      (I.map (terminalGlobalStirlingEquiv R (Fin h) d
        (Fin 1 ⊕ Time)).toRingHom).map
          (homogeneousCentralDehomogenization R d Time) := by
      rw [Ideal.map_map, Ideal.map_map,
        homogeneousCentralDehomogenization_comp_terminalGlobalStirling]
    _ = I.map (homogeneousCentralDehomogenization R d Time) := by
      rw [hfixed]

/-- The public forward Stirling-invariance predicate descends through
`H = 1`; exact source fixedness is more than enough. -/
theorem homogeneousCentralDehomogenization_isTerminalGlobalStirlingInvariant
    (I : Ideal
      (CentralPolynomial R (Fin h) d (Fin 1 ⊕ Time)))
    (hfixed : I.map
      (terminalGlobalStirlingEquiv R (Fin h) d
        (Fin 1 ⊕ Time)).toRingHom = I) :
    IsTerminalGlobalStirlingInvariant R (Fin h) d Time
      (homogeneousCentralDehomogenizeIdeal R d Time I) := by
  intro P hP
  rw [←
    homogeneousCentralDehomogenization_map_globalStirling_eq_of_fixed
      d Time I hfixed]
  exact Ideal.mem_map_of_mem
    (terminalGlobalStirlingEquiv R (Fin h) d Time).toRingHom hP

/-! ## Ordinary-homogeneity input for Noetherian descent -/

/-- Casting a natural-valued monomial weight to integers commutes with its
finite-support sum, for an arbitrary variable type. -/
theorem finsupp_weight_natCast_general
    {σ : Type v} (weight : σ → ℕ) (m : σ →₀ ℕ) :
    Finsupp.weight (fun i ↦ (weight i : ℤ)) m =
      (Finsupp.weight weight m : ℤ) := by
  classical
  induction m using Finsupp.induction with
  | zero => simp
  | @single_add i a m hi ha ih =>
      simp [map_add, Finsupp.weight_single, ih,
        Nat.cast_add, Nat.cast_mul]

/-- Ordinary homogeneity for the natural total-degree grading implies
ordinary homogeneity for the integer grading used by Noetherian descent. -/
theorem ideal_isHomogeneous_one_int_of_one_nat
    {σ : Type v} (I : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ : σ ↦ (1 : ℕ)))) :
    I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ : σ ↦ (1 : ℤ))) := by
  let natGrade := MvPolynomial.weightedHomogeneousSubmodule R
    (fun _ : σ ↦ (1 : ℕ))
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists natGrade I).mp hI
  rw [hS]
  apply Ideal.homogeneous_span
  rintro _ ⟨P, hP, rfl⟩
  obtain ⟨degree, hdegree⟩ := P.property
  refine ⟨(degree : ℤ), ?_⟩
  intro m hm
  calc
    Finsupp.weight (fun _ : σ ↦ (1 : ℤ)) m =
        (Finsupp.weight (fun _ : σ ↦ (1 : ℕ)) m : ℤ) := by
      simpa using
        (finsupp_weight_natCast_general (fun _ : σ ↦ (1 : ℕ)) m)
    _ = (degree : ℤ) :=
      congrArg (fun q : ℕ ↦ (q : ℤ)) (hdegree hm)

/-- Pulling a naturally presented ordinarily homogeneous ideal back through
the finite enumeration gives exactly the integer-homogeneity hypothesis of
the maintained descent theorem. -/
theorem terminalReindexedRenameEquiv_symm_map_isOrdinaryHomogeneous
    (e : TerminalFiniteReindex (n := n) d Time)
    (K : Ideal (CentralPolynomial R (Fin h) d Time))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ)))) :
    (K.map (terminalReindexedRenameEquiv
      (R := R) d Time e).symm.toRingHom).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule R
          (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ))) := by
  have hKint := ideal_isHomogeneous_one_int_of_one_nat K hK
  refine ideal_map_algEquiv_isHomogeneous_between
    (fun _ : CentralPolynomialIndex (Fin h) d Time ↦ (1 : ℤ))
    (fun i : Fin n ↦ (terminalReindexedOrdinaryDegree n i : ℤ))
    (terminalReindexedRenameEquiv (R := R) d Time e).symm ?_ K hKint
  intro P degree hP
  change
    ((terminalReindexedRenameEquiv (R := R) d Time e).symm P).IsWeightedHomogeneous
        (fun i : Fin n ↦ (terminalReindexedOrdinaryDegree n i : ℤ)) degree
  change (MvPolynomial.renameEquiv R e.symm P).IsWeightedHomogeneous _ degree
  apply weightedHomogeneous_renameEquiv (R := R) e.symm
    (fun i : Fin n ↦ (terminalReindexedOrdinaryDegree n i : ℤ))
  change P.IsWeightedHomogeneous
    (fun _ : CentralPolynomialIndex (Fin h) d Time ↦ (1 : ℤ)) degree
  exact hP

/-! ## Natural stabilized endpoint -/

/-- Noetherian stabilization in finite coordinates transports to permanent
stabilization in the natural block/time presentation.  The stabilized ideal
is fixed by the natural terminal Stirling automorphism and satisfies both
terminal invariant predicates consumed by elimination. -/
theorem exists_homogeneousTerminalInitialIteration_stabilizes_with_invariants
    (krullDim : ℕ) [IsNoetherianRing R]
    [Ring.KrullDimLE krullDim R]
    (monomialOrder : MonomialOrder (Fin n))
    (e : TerminalFiniteReindex (n := n) d (Fin 1 ⊕ Time))
    (K : Ideal (CentralPolynomial R (Fin h) d (Fin 1 ⊕ Time)))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ)))) :
    ∃ j₀ : ℕ,
      let Kstable := homogeneousTerminalInitialIteration R d Time K j₀
      Kstable.map
          (terminalGlobalStirlingEquiv R (Fin h) d
            (Fin 1 ⊕ Time)).toRingHom =
        Kstable ∧
      IsTerminalMultigradedIdeal R (Fin h) d (Fin 1 ⊕ Time) Kstable ∧
      IsTerminalGlobalStirlingInvariant R (Fin h) d
        (Fin 1 ⊕ Time) Kstable ∧
      ∀ j, j₀ ≤ j →
        homogeneousTerminalInitialIteration R d Time K j = Kstable := by
  let E := terminalReindexedRenameEquiv (R := R) d (Fin 1 ⊕ Time) e
  let Jfin := (terminalReindexedGlobalStirlingEquiv
    (R := R) d (Fin 1 ⊕ Time) e).toRingEquiv
  let Q : Ideal (MvPolynomial (Fin n) R) := K.map E.symm.toRingHom
  let I : ℕ → Ideal (MvPolynomial (Fin n) R) :=
    lexicographicInitialIdealIteration
      (terminalReindexedMultiDegree d (Fin 1 ⊕ Time) e) Jfin Q
  have hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ))) := by
    simpa only [Q, E] using
      terminalReindexedRenameEquiv_symm_map_isOrdinaryHomogeneous
        d (Fin 1 ⊕ Time) e K hK
  obtain ⟨j₀, hfixed, hpermanent⟩ :=
    exists_terminalReindexedLexicographicInitialIdealIteration_stabilizes_of_krullDimLE
      krullDim d (Fin 1 ⊕ Time) monomialOrder e Q hQ
  have hseed : Q.map E.toRingHom = K := by
    change (K.map E.symm.toRingHom).map E.toRingHom = K
    rw [Ideal.map_map]
    have hcomp : E.toRingHom.comp E.symm.toRingHom = RingHom.id _ := by
      apply RingHom.ext
      intro P
      simp
    rw [hcomp, Ideal.map_id]
  have hiteration (j : ℕ) :
      (I j).map E.toRingHom =
        homogeneousTerminalInitialIteration R d Time K j := by
    calc
      (I j).map E.toRingHom =
          homogeneousTerminalInitialIteration R d Time
            (Q.map E.toRingHom) j := by
        simpa only [I, Jfin, E] using
          terminalReindexedRenameEquiv_initialIteration
            d Time e Q j
      _ = homogeneousTerminalInitialIteration R d Time K j := by
        rw [hseed]
  have hfixedNatural :
      (homogeneousTerminalInitialIteration R d Time K j₀).map
          (terminalGlobalStirlingEquiv R (Fin h) d
            (Fin 1 ⊕ Time)).toRingHom =
        homogeneousTerminalInitialIteration R d Time K j₀ := by
    calc
      (homogeneousTerminalInitialIteration R d Time K j₀).map
          (terminalGlobalStirlingEquiv R (Fin h) d
            (Fin 1 ⊕ Time)).toRingHom =
        ((I j₀).map E.toRingHom).map
          (terminalGlobalStirlingEquiv R (Fin h) d
            (Fin 1 ⊕ Time)).toRingHom :=
        congrArg
          (fun L => L.map
            (terminalGlobalStirlingEquiv R (Fin h) d
              (Fin 1 ⊕ Time)).toRingHom)
          (hiteration j₀).symm
      _ = (I j₀).map E.toRingHom := by
        exact terminalReindexedRename_map_globalStirling_eq_of_fixed
          d (Fin 1 ⊕ Time) e (I j₀)
            (by simpa only [I, Jfin] using hfixed)
      _ = homogeneousTerminalInitialIteration R d Time K j₀ :=
        hiteration j₀
  have hmulti : IsTerminalMultigradedIdeal R (Fin h) d (Fin 1 ⊕ Time)
      (homogeneousTerminalInitialIteration R d Time K j₀) := by
    have hI : (I j₀).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule R
          (fun i ↦ toLex
            (terminalReindexedMultiDegree d (Fin 1 ⊕ Time) e i))) := by
      simpa only [I] using
        lexicographicInitialIdealIteration_isHomogeneous
          (terminalReindexedMultiDegree d (Fin 1 ⊕ Time) e) Jfin Q j₀
    have hrename := terminalReindexedRename_isTerminalMultigradedIdeal
      d (Fin 1 ⊕ Time) e (I j₀) hI
    rwa [hiteration j₀] at hrename
  have hinvariant : IsTerminalGlobalStirlingInvariant R (Fin h) d
      (Fin 1 ⊕ Time)
      (homogeneousTerminalInitialIteration R d Time K j₀) := by
    have hrename :=
      terminalReindexedRename_isTerminalGlobalStirlingInvariant
        d (Fin 1 ⊕ Time) e (I j₀)
          (by simpa only [I, Jfin] using hfixed)
    rwa [hiteration j₀] at hrename
  refine ⟨j₀, hfixedNatural, hmulti, hinvariant, ?_⟩
  intro j hj
  calc
    homogeneousTerminalInitialIteration R d Time K j =
        (I j).map E.toRingHom := (hiteration j).symm
    _ = (I j₀).map E.toRingHom := by
      exact congrArg
        (fun L : Ideal (MvPolynomial (Fin n) R) => L.map E.toRingHom)
        (by simpa only [I] using hpermanent j hj)
    _ = homogeneousTerminalInitialIteration R d Time K j₀ :=
      hiteration j₀

/-- The same stabilized endpoint after setting `H = 1`.  This is the form
consumed by terminal elimination in the original central polynomial ring. -/
theorem exists_homogeneousTerminalInitialIteration_stabilizes_with_dehomogenized_invariants
    (krullDim : ℕ) [IsNoetherianRing R]
    [Ring.KrullDimLE krullDim R]
    (monomialOrder : MonomialOrder (Fin n))
    (e : TerminalFiniteReindex (n := n) d (Fin 1 ⊕ Time))
    (K : Ideal (CentralPolynomial R (Fin h) d (Fin 1 ⊕ Time)))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ)))) :
    ∃ j₀ : ℕ,
      let Kstable := homogeneousTerminalInitialIteration R d Time K j₀
      let Kdehom := homogeneousCentralDehomogenizeIdeal R d Time Kstable
      Kstable.map
          (terminalGlobalStirlingEquiv R (Fin h) d
            (Fin 1 ⊕ Time)).toRingHom =
        Kstable ∧
      IsTerminalMultigradedIdeal R (Fin h) d (Fin 1 ⊕ Time) Kstable ∧
      IsTerminalGlobalStirlingInvariant R (Fin h) d
        (Fin 1 ⊕ Time) Kstable ∧
      (∀ j, j₀ ≤ j →
        homogeneousTerminalInitialIteration R d Time K j = Kstable) ∧
      Kdehom.map
          (terminalGlobalStirlingEquiv R (Fin h) d Time).toRingHom =
        Kdehom ∧
      IsTerminalMultigradedIdeal R (Fin h) d Time Kdehom ∧
      IsTerminalGlobalStirlingInvariant R (Fin h) d Time Kdehom := by
  obtain ⟨j₀, hfixed, hmulti, hinvariant, hpermanent⟩ :=
    exists_homogeneousTerminalInitialIteration_stabilizes_with_invariants
      d Time krullDim monomialOrder e K hK
  refine ⟨j₀, hfixed, hmulti, hinvariant, hpermanent, ?_, ?_, ?_⟩
  · exact
      homogeneousCentralDehomogenization_map_globalStirling_eq_of_fixed
        d Time (homogeneousTerminalInitialIteration R d Time K j₀) hfixed
  · exact homogeneousCentralDehomogenization_isTerminalMultigradedIdeal
      d Time (homogeneousTerminalInitialIteration R d Time K j₀) hmulti
  · exact
      homogeneousCentralDehomogenization_isTerminalGlobalStirlingInvariant
        d Time (homogeneousTerminalInitialIteration R d Time K j₀) hfixed

end AbelFormalization
