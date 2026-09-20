import AbelFormalization.TerminalReindexedArtinianDescent
import AbelFormalization.TerminalStirlingBaseChange
import AbelFormalization.LexicographicInitialIdealProductBaseChange
import AbelFormalization.RankOneIdealGlobalArtinianDescent

set_option autoImplicit false

/-!
# Global Artinian descent for the terminal Stirling automorphism

The local terminal descent theorem requires a nilpotent maximal coefficient
ideal.  An arbitrary commutative Artinian ring is instead decomposed into its
finitely many canonical Artinian local factors.  This file equips every
factor with the concrete reindexed terminal Stirling descent data, uses the
product base-change theorem for full lexicographic initials, and uses
Stirling naturality for the mapped-ideal square.  The global factorwise
stabilization theorem then recombines the local endpoints.
-/

noncomputable section

namespace AbelFormalization

universe u v w z

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Homogeneous ideals under coefficient maps -/

/-- Mapping coefficients sends a weighted-homogeneous polynomial to a
weighted-homogeneous polynomial of the same degree.  Injectivity of the
coefficient map is not needed. -/
theorem mvPolynomial_map_isWeightedHomogeneous
    {R : Type u} {S : Type v} {sigma : Type w} {M : Type z}
    [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
    (f : R →+* S) (weight : sigma → M) {degree : M}
    {P : MvPolynomial sigma R}
    (hP : P.IsWeightedHomogeneous weight degree) :
    (MvPolynomial.map f P).IsWeightedHomogeneous weight degree := by
  intro m hm
  apply hP
  intro hcoeff
  apply hm
  rw [MvPolynomial.coeff_map, hcoeff, map_zero]

/-- Coefficient extension preserves homogeneous ideals for every weighted
polynomial grading. -/
theorem mvPolynomial_ideal_map_isHomogeneous
    {R : Type u} {S : Type v} {sigma : Type w} {M : Type z}
    [CommRing R] [CommRing S] [AddCommMonoid M] [DecidableEq M]
    (f : R →+* S) (weight : sigma → M)
    (I : Ideal (MvPolynomial sigma R))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R weight)) :
    (I.map (MvPolynomial.map f)).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule S weight) := by
  let sourceGrade := MvPolynomial.weightedHomogeneousSubmodule R weight
  obtain ⟨T, hT⟩ :=
    (Ideal.IsHomogeneous.iff_exists sourceGrade I).mp hI
  rw [hT, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
  obtain ⟨degree, hdegree⟩ := P.property
  exact ⟨degree, mvPolynomial_map_isWeightedHomogeneous
    f weight hdegree⟩

/-! ## The concrete terminal grading and local datum -/

/-- Ordinary total degree on the finite reindexing. -/
abbrev terminalReindexedOrdinaryDegree (n : ℕ) : Fin n → ℕ :=
  fun _ ↦ 1

/-- The genuine terminal multidegree transported to the finite
reindexing. -/
abbrev terminalReindexedMultiDegree
    {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)
    (e : TerminalFiniteReindex (n := n) d Time) :
    Fin n → Fin h → ℤ :=
  fun i b ↦ ((terminalGlobalWeight (Fin h) d Time (e i)) b : ℤ)

theorem terminalReindexedOrdinaryDegree_pos (n : ℕ) :
    ∀ i : Fin n, 0 < terminalReindexedOrdinaryDegree n i := by
  intro i
  simp [terminalReindexedOrdinaryDegree]

/-- All local hypotheses used by rank-one Artinian descent, specialized to
the reindexed terminal Stirling automorphism. -/
noncomputable def terminalReindexedRankOneLocalInitialDescentData
    {C : Type u} [CommRing C]
    {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) C))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule C
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ)))) :
    RankOneLocalInitialDescentData C
      (terminalReindexedOrdinaryDegree n)
      (terminalReindexedMultiDegree d Time e)
      (terminalReindexedOrdinaryDegree_pos n) Q := by
  let Jalg := terminalReindexedGlobalStirlingEquiv (R := C) d Time e
  let J := Jalg.toRingEquiv
  let Jmodule := terminalReindexedGlobalStirlingModuleEquiv
    (R := C) d Time e
  refine
    { J := J
      Jmodule := Jmodule
      Q_ordinaryHomogeneous := hQ
      map_ordinaryHomogeneous := ?_
      map_degreeLength := ?_
      map_window := ?_
      triangular := ?_
      map_windowPart := ?_ }
  · intro I hI
    let grade := MvPolynomial.weightedHomogeneousSubmodule C
      (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ))
    obtain ⟨T, hT⟩ := (Ideal.IsHomogeneous.iff_exists grade I).mp hI
    rw [hT, Ideal.map_span]
    apply Ideal.homogeneous_span
    rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
    obtain ⟨degree, hdegree⟩ := P.property
    have hdegreeWeighted :
        (P : MvPolynomial (Fin n) C).IsWeightedHomogeneous
          (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ)) degree :=
      (MvPolynomial.mem_weightedHomogeneousSubmodule C
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ)) degree P).mp
          hdegree
    have hdegree' : (P : MvPolynomial (Fin n) C).IsWeightedHomogeneous
        (fun _ : Fin n ↦ (1 : ℤ)) degree := by
      simpa only [terminalReindexedOrdinaryDegree, Nat.cast_one] using
        hdegreeWeighted
    have himage :=
      terminalReindexedGlobalStirlingEquiv_isWeightedHomogeneous_int
        (B := C) d Time e hdegree'
    refine ⟨degree, ?_⟩
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    change (Jalg (P : MvPolynomial (Fin n) C)).IsWeightedHomogeneous
      (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ)) degree
    simpa only [terminalReindexedOrdinaryDegree, Nat.cast_one] using himage
  · intro I hI degree
    have hlength :=
      terminalReindexed_artinianPolynomialSubmoduleDegree_length
        (B := C) d Time e degree I
    simpa only [J, Jalg] using congrArg ENat.toNat hlength
  · intro D
    exact terminalReindexedGlobalStirlingModuleEquiv_map_window
      (R := C) d Time e D
  · intro D
    exact terminalReindexedGlobalStirlingModuleEquiv_isWindowWeightTriangular
      (R := C) d Time e D
  · intro D I
    exact terminalReindexed_polynomialWindowOrderedWeightPart_map
      (B := C) d Time e D I

@[simp]
theorem terminalReindexedRankOneLocalInitialDescentData_J
    {C : Type u} [CommRing C]
    {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) C))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule C
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ)))) :
    (terminalReindexedRankOneLocalInitialDescentData d Time e Q hQ).J =
      (terminalReindexedGlobalStirlingEquiv
        (R := C) d Time e).toRingEquiv :=
  rfl

/-! ## Canonical-factor data -/

variable {B : Type u} [CommRing B] [IsArtinianRing B]
variable {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)

/-- Ordinary homogeneity descends to each canonical Artinian local factor. -/
theorem artinianLocalFactorPolynomialIdealEquiv_ordinaryHomogeneous
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ))))
    (m : MaximalSpectrum B) :
    (artinianLocalFactorPolynomialIdealEquiv B (Fin n) Q m).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule
        (artinianLocalFactor B m)
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ))) := by
  rw [artinianLocalFactorPolynomialIdealEquiv_apply_eq_map]
  exact mvPolynomial_ideal_map_isHomogeneous
    (artinianLocalFactorCoefficientHom B m)
    (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ)) Q hQ

/-- The complete factorwise datum for the terminal automorphism over an
arbitrary commutative Artinian coefficient ring. -/
noncomputable def terminalReindexedRankOneGlobalArtinianDescentData
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i ↦ (terminalReindexedOrdinaryDegree n i : ℤ)))) :
    RankOneGlobalArtinianDescentData B
      (terminalReindexedOrdinaryDegree n)
      (terminalReindexedMultiDegree d Time e)
      (terminalReindexedOrdinaryDegree_pos n)
      (terminalReindexedGlobalStirlingEquiv
        (R := B) d Time e).toRingEquiv Q where
  factorData m :=
    terminalReindexedRankOneLocalInitialDescentData d Time e
      (artinianLocalFactorPolynomialIdealEquiv B (Fin n) Q m)
      (artinianLocalFactorPolynomialIdealEquiv_ordinaryHomogeneous
        d Time e Q hQ m)
  initial_factor I m :=
    artinianLocalFactorPolynomialIdealEquiv_lexicographicInitialIdeal
      B (terminalReindexedMultiDegree d Time e) I m
  map_factor I m := by
    simpa only [terminalReindexedRankOneLocalInitialDescentData_J] using
      artinianLocalFactorPolynomialIdealEquiv_map_terminalStirling
        B d Time e I m

/-! ## Global endpoint -/

/-- Over every commutative Artinian coefficient ring, the recursive full
lexicographic-initial iteration attached to the reindexed terminal Stirling
automorphism stabilizes permanently at an ideal fixed by that automorphism. -/
theorem exists_terminalReindexedLexicographicInitialIdealIteration_stabilizes_global
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
  let ordinaryDegree := terminalReindexedOrdinaryDegree n
  let multiDegree := terminalReindexedMultiDegree d Time e
  let hpositive := terminalReindexedOrdinaryDegree_pos n
  let J := (terminalReindexedGlobalStirlingEquiv
    (R := B) d Time e).toRingEquiv
  let data := terminalReindexedRankOneGlobalArtinianDescentData
    (B := B) d Time e Q hQ
  exact RankOneGlobalArtinianDescentData.exists_iteration_stabilizes
    ordinaryDegree multiDegree hpositive J Q data monomialOrder

end AbelFormalization
