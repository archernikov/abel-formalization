import AbelFormalization.RankOneIdealArtinianDescent
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Maps

set_option autoImplicit false

/-!
# Global Artinian descent by local-factor decomposition

An arbitrary commutative Artinian ring need not contain a nilpotent maximal
ideal.  Mathlib instead decomposes it as the finite product of the quotients
by sufficiently large powers of all maximal ideals.  Every such quotient has
an explicit nilpotent maximal ideal, so the local-factor theorem from
`RankOneIdealArtinianDescent` applies to it.

This file supplies three bridges:

* polynomial rings commute with finite products of coefficient rings;
* ideals over the Artinian coefficient ring are therefore identified with
  tuples of ideals over the canonical local factors;
* finitely many factorwise stabilization indices can be replaced by their
  maximum and recombined through that ideal equivalence.

The final theorem keeps two factor-transport facts as fields of its input
data: full lexicographic initial formation and the polynomial automorphism
must commute with passage to each factor.  The first uses the central
idempotents of the Artinian product decomposition; it is stronger than the
corresponding statement for an arbitrary quotient map.
-/

noncomputable section

namespace AbelFormalization

open scoped Pointwise

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Polynomial rings over finite products -/

/-- A multivariate polynomial ring over a finite product of rings is the
finite product of the corresponding multivariate polynomial rings. -/
noncomputable def mvPolynomialPiRingEquiv
    {ι σ : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] :
    MvPolynomial σ (∀ i, R i) ≃+* ∀ i, MvPolynomial σ (R i) :=
  .ofBijective
    (RingHom.pi fun i =>
      MvPolynomial.map (Pi.evalRingHom R i))
    ⟨by
      intro p q hpq
      apply MvPolynomial.ext
      intro d
      funext i
      have hi := congrArg (fun f => (f i).coeff d) hpq
      simpa only [RingHom.pi_apply, MvPolynomial.coeff_map,
        Pi.evalRingHom_apply] using hi,
    by
      classical
      intro p
      let support : Set (σ →₀ ℕ) :=
        Function.support (fun d i => (p i).coeff d)
      have support_finite : support.Finite :=
        (Set.finite_iUnion fun i => (p i).support.finite_toSet).subset
          (by
            intro d hd
            simp only [support, Function.mem_support] at hd
            have : ∃ i, (p i).coeff d ≠ 0 := by
              by_contra h
              apply hd
              funext i
              exact not_ne_iff.mp (not_exists.mp h i)
            obtain ⟨i, hi⟩ := this
            exact Set.mem_iUnion.mpr
              ⟨i, MvPolynomial.mem_support_iff.mpr hi⟩)
      let q : MvPolynomial σ (∀ i, R i) :=
        AddMonoidAlgebra.ofCoeff <|
          Finsupp.ofSupportFinite (fun d i => (p i).coeff d) support_finite
      refine ⟨q, ?_⟩
      funext i
      apply MvPolynomial.ext
      intro d
      simp only [RingHom.pi_apply, MvPolynomial.coeff_map, q,
        AddMonoidAlgebra.coeff_ofCoeff, Finsupp.ofSupportFinite_coe,
        Pi.evalRingHom_apply]⟩

@[simp]
theorem mvPolynomialPiRingEquiv_apply
    {ι σ : Type*} [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)]
    (p : MvPolynomial σ (∀ i, R i)) (i : ι) :
    mvPolynomialPiRingEquiv R p i =
      MvPolynomial.map (Pi.evalRingHom R i) p :=
  rfl

/-! ## Canonical local factors of an Artinian ring -/

variable (B : Type*) [CommRing B] [IsArtinianRing B]

/-- A chosen exponent killing the nilradical of an Artinian ring. -/
noncomputable def artinianNilradicalExponent : ℕ :=
  Classical.choose (IsArtinianRing.isNilpotent_nilradical (R := B))

theorem artinianNilradical_pow_exponent_eq_bot :
    nilradical B ^ artinianNilradicalExponent B = ⊥ := by
  simpa only [artinianNilradicalExponent, Ideal.zero_eq_bot] using
    (Classical.choose_spec
      (IsArtinianRing.isNilpotent_nilradical (R := B)))

/-- We use the successor of the chosen exponent so that every maximal-ideal
power occurring in the factors has a positive exponent. -/
theorem artinianNilradical_pow_succ_exponent_eq_bot :
    nilradical B ^ (artinianNilradicalExponent B + 1) = ⊥ := by
  rw [pow_succ, artinianNilradical_pow_exponent_eq_bot, Ideal.bot_mul]

/-- The canonical factor belonging to a maximal ideal. -/
abbrev artinianLocalFactor (m : MaximalSpectrum B) :=
  B ⧸ m.asIdeal ^ (artinianNilradicalExponent B + 1)

/-- The image of `m` in the quotient by its chosen positive power. -/
def artinianLocalFactorMaximalIdeal (m : MaximalSpectrum B) :
    Ideal (artinianLocalFactor B m) :=
  m.asIdeal.map
    (Ideal.Quotient.mk
      (m.asIdeal ^ (artinianNilradicalExponent B + 1)))

noncomputable instance artinianLocalFactorMaximalIdeal_isMaximal
    (m : MaximalSpectrum B) :
    (artinianLocalFactorMaximalIdeal B m).IsMaximal := by
  letI : m.asIdeal.IsMaximal := m.isMaximal
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := Ideal.Quotient.mk
      (m.asIdeal ^ (artinianNilradicalExponent B + 1)))
    Ideal.Quotient.mk_surjective
  rw [Ideal.mk_ker]
  exact Ideal.pow_le_self (Nat.add_one_ne_zero _)

/-- The maximal ideal of each factor is nilpotent with the same positive
exponent used to define that factor. -/
theorem artinianLocalFactorMaximalIdeal_pow_eq_bot
    (m : MaximalSpectrum B) :
    artinianLocalFactorMaximalIdeal B m ^
        (artinianNilradicalExponent B + 1) = ⊥ := by
  change
    (m.asIdeal.map
      (Ideal.Quotient.mk
        (m.asIdeal ^ (artinianNilradicalExponent B + 1)))) ^
        (artinianNilradicalExponent B + 1) = ⊥
  rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

/-- The Artinian ring itself as the finite product of its canonical local
factors.  This is `quotNilradicalPowEquivPi` after replacing the zero
nilradical power by the bottom ideal. -/
noncomputable def artinianLocalFactorEquiv :
    B ≃+* ∀ m : MaximalSpectrum B, artinianLocalFactor B m :=
  (((AlgEquiv.quotientBot B B).symm).trans
      ((Ideal.quotientEquivAlgOfEq B
        (artinianNilradical_pow_succ_exponent_eq_bot B).symm).trans
        (IsArtinianRing.quotNilradicalPowEquivPi B
          (artinianNilradicalExponent B + 1)))).toRingEquiv

/-- Apply the coefficient decomposition and then commute multivariate
polynomials with the finite product. -/
noncomputable def artinianLocalFactorPolynomialEquiv (σ : Type*) :
    MvPolynomial σ B ≃+*
      ∀ m : MaximalSpectrum B,
        MvPolynomial σ (artinianLocalFactor B m) :=
  (MvPolynomial.mapEquiv σ
      (artinianLocalFactorEquiv B)).trans
    (mvPolynomialPiRingEquiv
      (fun m : MaximalSpectrum B => artinianLocalFactor B m))

/-- Ideals over an Artinian coefficient ring are exactly tuples of ideals
over its canonical local factors. -/
noncomputable def artinianLocalFactorPolynomialIdealEquiv (σ : Type*) :
    Ideal (MvPolynomial σ B) ≃o
      ∀ m : MaximalSpectrum B,
        Ideal (MvPolynomial σ (artinianLocalFactor B m)) :=
  ((artinianLocalFactorPolynomialEquiv B σ).idealComapOrderIso.symm).trans
    (Ideal.piOrderIso
      (ι := MaximalSpectrum B)
      (R := fun m => MvPolynomial σ (artinianLocalFactor B m)))

/-! ## Finite recombination of stabilization indices -/

/-- If an ideal sequence and its endomorphism are identified factorwise,
and every factor sequence eventually stabilizes at a fixed point, then one
common index works before decomposition. -/
theorem exists_idealSequence_stabilizes_of_finite_factorwise
    {A : Type*} [Semiring A]
    {ι : Type*} [Finite ι]
    {Aι : ι → Type*} [∀ i, Semiring (Aι i)]
    (factor : Ideal A ≃o ∀ i, Ideal (Aι i))
    (globalMap : Ideal A → Ideal A)
    (factorMap : ∀ i, Ideal (Aι i) → Ideal (Aι i))
    (sequence : ℕ → Ideal A)
    (factorSequence : ∀ i, ℕ → Ideal (Aι i))
    (hmap : ∀ (I : Ideal A) i,
      factor (globalMap I) i = factorMap i (factor I i))
    (hsequence : ∀ j i, factor (sequence j) i = factorSequence i j)
    (hfactor : ∀ i, ∃ j₀ : ℕ,
      factorMap i (factorSequence i j₀) = factorSequence i j₀ ∧
        ∀ j, j₀ ≤ j → factorSequence i j = factorSequence i j₀) :
    ∃ j₀ : ℕ,
      globalMap (sequence j₀) = sequence j₀ ∧
        ∀ j, j₀ ≤ j → sequence j = sequence j₀ := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  choose stop hfixed hstable using hfactor
  let j₀ := Finset.univ.sup stop
  have hstop (i : ι) : stop i ≤ j₀ :=
    Finset.le_sup (f := stop) (Finset.mem_univ i)
  refine ⟨j₀, ?_, ?_⟩
  · apply factor.injective
    funext i
    calc
      factor (globalMap (sequence j₀)) i =
          factorMap i (factor (sequence j₀) i) := hmap _ i
      _ = factorMap i (factorSequence i j₀) := by
        rw [hsequence j₀ i]
      _ = factorMap i (factorSequence i (stop i)) := by
        rw [hstable i j₀ (hstop i)]
      _ = factorSequence i (stop i) := hfixed i
      _ = factorSequence i j₀ := (hstable i j₀ (hstop i)).symm
      _ = factor (sequence j₀) i := (hsequence j₀ i).symm
  · intro j hj
    apply factor.injective
    funext i
    calc
      factor (sequence j) i = factorSequence i j := hsequence j i
      _ = factorSequence i (stop i) :=
        hstable i j ((hstop i).trans hj)
      _ = factorSequence i j₀ := (hstable i j₀ (hstop i)).symm
      _ = factor (sequence j₀) i := (hsequence j₀ i).symm

/-! ## Factorwise rank-one descent data -/

/-- All local hypotheses about a concrete polynomial automorphism that are
consumed by `exists_lexicographicInitialIdealIteration_stabilizes_of_isArtinianRing`.
The coefficient ring is a parameter so that one such datum can be supplied
for every canonical Artinian local factor. -/
structure RankOneLocalInitialDescentData
    (C : Type*) [CommRing C]
    {n h : ℕ}
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i)
    (Q : Ideal (MvPolynomial (Fin n) C)) where
  /-- The polynomial-ring automorphism on this factor. -/
  J : MvPolynomial (Fin n) C ≃+* MvPolynomial (Fin n) C
  /-- Its coefficient-linear realization on the rank-one polynomial
  module. -/
  Jmodule : artinianFreePolynomialModule C n 1 ≃ₗ[C]
    artinianFreePolynomialModule C n 1
  /-- The initial ideal from which the local iteration starts is ordinary
  homogeneous. -/
  Q_ordinaryHomogeneous : Q.IsHomogeneous
    (MvPolynomial.weightedHomogeneousSubmodule C
      (fun i => (ordinaryDegree i : ℤ)))
  /-- Applying `J` preserves ordinary homogeneity. -/
  map_ordinaryHomogeneous : ∀ I : Ideal (MvPolynomial (Fin n) C),
    I.IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule C
          (fun i => (ordinaryDegree i : ℤ))) →
      (I.map J.toRingHom).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule C
          (fun i => (ordinaryDegree i : ℤ)))
  /-- Applying `J` preserves the length of every ordinary degree slice. -/
  map_degreeLength : ∀ (I : Ideal (MvPolynomial (Fin n) C)),
    I.IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule C
          (fun i => (ordinaryDegree i : ℤ))) →
    ∀ degree : ℤ,
      (Module.length C
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule (I.map J.toRingHom))
          ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat =
        (Module.length C
          (artinianPolynomialSubmoduleDegree
            (rankOnePolynomialIdealSubmodule I)
            ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat
  /-- The rank-one realization preserves every bounded ordinary window. -/
  map_window : ∀ D : ℤ,
    ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).windowModule
        C hpositive D).map Jmodule.toLinearMap =
      (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).windowModule
        C hpositive D
  /-- The realization is strictly lower triangular in lexicographic
  weight on every bounded window. -/
  triangular : ∀ D : ℤ,
    (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).IsWindowWeightTriangular
      hpositive D Jmodule
  /-- Mapping an ideal by `J` agrees on the ordered bounded part with the
  conjugated rank-one realization. -/
  map_windowPart : ∀ (D : ℤ) (I : Ideal (MvPolynomial (Fin n) C)),
    (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).polynomialWindowOrderedWeightPart
        hpositive D
        (rankOnePolynomialIdealSubmodule (I.map J.toRingHom)) =
      ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).polynomialWindowOrderedWeightPart
        hpositive D
        (rankOnePolynomialIdealSubmodule I)).map
          ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).windowOrderedWeightConjugate
            hpositive D Jmodule
              (map_window D)).toLinearMap

/-- Factorwise data together with the two identities needed to transport
the global recursive ideal sequence to the canonical Artinian factors. -/
structure RankOneGlobalArtinianDescentData
    (B : Type*) [CommRing B] [IsArtinianRing B]
    {n h : ℕ}
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) where
  /-- Concrete local descent data on each canonical factor. -/
  factorData : ∀ m : MaximalSpectrum B,
    RankOneLocalInitialDescentData
      (artinianLocalFactor B m)
      ordinaryDegree multiDegree hpositive
      (artinianLocalFactorPolynomialIdealEquiv B (Fin n) Q m)
  /-- Full lexicographic initial formation commutes with projection to each
  local factor. -/
  initial_factor : ∀ (I : Ideal (MvPolynomial (Fin n) B))
      (m : MaximalSpectrum B),
    artinianLocalFactorPolynomialIdealEquiv B (Fin n)
        (lexicographicInitialIdeal multiDegree I) m =
      lexicographicInitialIdeal multiDegree
        (artinianLocalFactorPolynomialIdealEquiv B (Fin n) I m)
  /-- The global polynomial automorphism becomes the specified factor
  automorphism after projection. -/
  map_factor : ∀ (I : Ideal (MvPolynomial (Fin n) B))
      (m : MaximalSpectrum B),
    artinianLocalFactorPolynomialIdealEquiv B (Fin n)
        (I.map J.toRingHom) m =
      (artinianLocalFactorPolynomialIdealEquiv B (Fin n) I m).map
        (factorData m).J.toRingHom

namespace RankOneGlobalArtinianDescentData

variable {B : Type*} [CommRing B] [IsArtinianRing B]
variable {n h : ℕ}
variable (ordinaryDegree : Fin n → ℕ)
variable (multiDegree : Fin n → Fin h → ℤ)
variable (hpositive : ∀ i, 0 < ordinaryDegree i)
variable (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
variable (Q : Ideal (MvPolynomial (Fin n) B))
variable (data : RankOneGlobalArtinianDescentData B
  ordinaryDegree multiDegree hpositive J Q)

/-- The global recursive initial-ideal sequence projects to the recursive
sequence associated with the corresponding factor automorphism. -/
theorem iteration_factor : ∀ (j : ℕ) (m : MaximalSpectrum B),
    artinianLocalFactorPolynomialIdealEquiv B (Fin n)
        (lexicographicInitialIdealIteration multiDegree J Q j) m =
      lexicographicInitialIdealIteration multiDegree
        (data.factorData m).J
        (artinianLocalFactorPolynomialIdealEquiv B (Fin n) Q m) j := by
  intro j
  induction j with
  | zero =>
      intro m
      simpa only [lexicographicInitialIdealIteration_zero] using
        data.initial_factor Q m
  | succ j ih =>
      intro m
      let Ij := lexicographicInitialIdealIteration multiDegree J Q j
      calc
        artinianLocalFactorPolynomialIdealEquiv B (Fin n)
            (lexicographicInitialIdealIteration multiDegree J Q (j + 1)) m =
          artinianLocalFactorPolynomialIdealEquiv B (Fin n)
            (lexicographicInitialIdeal multiDegree
              (Ij.map J.toRingHom)) m := by
                rfl
        _ = lexicographicInitialIdeal multiDegree
            (artinianLocalFactorPolynomialIdealEquiv B (Fin n)
              (Ij.map J.toRingHom) m) :=
          data.initial_factor (Ij.map J.toRingHom) m
        _ = lexicographicInitialIdeal multiDegree
            ((artinianLocalFactorPolynomialIdealEquiv B (Fin n) Ij m).map
              (data.factorData m).J.toRingHom) := by
          rw [data.map_factor Ij m]
        _ = lexicographicInitialIdeal multiDegree
            ((lexicographicInitialIdealIteration multiDegree
                (data.factorData m).J
                (artinianLocalFactorPolynomialIdealEquiv B (Fin n) Q m) j).map
              (data.factorData m).J.toRingHom) := by
          rw [ih m]
        _ = lexicographicInitialIdealIteration multiDegree
            (data.factorData m).J
            (artinianLocalFactorPolynomialIdealEquiv B (Fin n) Q m)
            (j + 1) := by
          rfl

/-- The existing Artinian-local theorem applies to every canonical factor,
because its displayed maximal ideal is nilpotent. -/
theorem local_stabilizes
    (monomialOrder : MonomialOrder (Fin n))
    (m : MaximalSpectrum B) :
    ∃ j₀ : ℕ,
      (lexicographicInitialIdealIteration multiDegree
          (data.factorData m).J
          (artinianLocalFactorPolynomialIdealEquiv B (Fin n) Q m) j₀).map
          (data.factorData m).J.toRingHom =
        lexicographicInitialIdealIteration multiDegree
          (data.factorData m).J
          (artinianLocalFactorPolynomialIdealEquiv B (Fin n) Q m) j₀ ∧
      ∀ j, j₀ ≤ j →
        lexicographicInitialIdealIteration multiDegree
            (data.factorData m).J
            (artinianLocalFactorPolynomialIdealEquiv B (Fin n) Q m) j =
          lexicographicInitialIdealIteration multiDegree
            (data.factorData m).J
            (artinianLocalFactorPolynomialIdealEquiv B (Fin n) Q m) j₀ := by
  let L := data.factorData m
  simpa only [L] using
    exists_lexicographicInitialIdealIteration_stabilizes_of_isArtinianRing
      monomialOrder (artinianLocalFactorMaximalIdeal B m)
      (artinianLocalFactorMaximalIdeal_pow_eq_bot B m)
      ordinaryDegree multiDegree hpositive L.J L.Jmodule
      (artinianLocalFactorPolynomialIdealEquiv B (Fin n) Q m)
      L.Q_ordinaryHomogeneous L.map_ordinaryHomogeneous L.map_degreeLength
      L.map_window L.triangular L.map_windowPart

include data

/-- Global Artinian stabilization.  No maximal ideal of `B` is assumed
nilpotent: the proof applies local descent to every canonical factor, takes
the maximum of the finitely many local stopping indices, and recombines the
factor ideals through `artinianLocalFactorPolynomialIdealEquiv`. -/
theorem exists_iteration_stabilizes
    (monomialOrder : MonomialOrder (Fin n)) :
    ∃ j₀ : ℕ,
      (lexicographicInitialIdealIteration multiDegree J Q j₀).map
          J.toRingHom =
        lexicographicInitialIdealIteration multiDegree J Q j₀ ∧
      ∀ j, j₀ ≤ j →
        lexicographicInitialIdealIteration multiDegree J Q j =
          lexicographicInitialIdealIteration multiDegree J Q j₀ := by
  let factor := artinianLocalFactorPolynomialIdealEquiv B (Fin n)
  let factorSequence := fun (m : MaximalSpectrum B) =>
    lexicographicInitialIdealIteration multiDegree
      (data.factorData m).J (factor Q m)
  refine exists_idealSequence_stabilizes_of_finite_factorwise
    factor
    (fun I => I.map J.toRingHom)
    (fun m I => I.map (data.factorData m).J.toRingHom)
    (lexicographicInitialIdealIteration multiDegree J Q)
    factorSequence
    ?_ ?_ ?_
  · intro I m
    simpa only [factor] using data.map_factor I m
  · intro j m
    simpa only [factor, factorSequence] using
      iteration_factor ordinaryDegree multiDegree hpositive J Q data j m
  · intro m
    simpa only [factor, factorSequence] using
      local_stabilizes ordinaryDegree multiDegree hpositive J Q data
        monomialOrder m

end RankOneGlobalArtinianDescentData

end AbelFormalization
