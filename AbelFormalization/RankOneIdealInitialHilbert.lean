import AbelFormalization.RankOneLexicographicWindowCompatibility

set_option autoImplicit false

/-!
# Ordinary Hilbert lengths of rank-one lexicographic initial ideals

The ordinary-degree slice is embedded in the finite ordered product of
lexicographic weight pieces.  Fixed-degree rank-one compatibility identifies
the embedded slice of the lexicographic initial ideal with the finite-weight
initial submodule of the original embedded slice.  The exact-sequence theorem
`finiteWeightInitial_length` then proves equality of their module lengths.

Artinian or Noetherian hypotheses are not needed for this equality.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n h : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- If an injective realization identifies one submodule with the
finite-weight initial of another, the original two submodules have equal
length. -/
theorem submodule_length_eq_of_map_eq_finiteWeightInitial
    {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {m : ℕ} {M : Fin m → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (embedding : V →ₗ[R] (∀ i, M i))
    (embedding_injective : Function.Injective embedding)
    (source target : Submodule R V)
    (hcompat : target.map embedding =
      finiteWeightInitial (source.map embedding)) :
    Module.length R target = Module.length R source := by
  calc
    Module.length R target = Module.length R (target.map embedding) :=
      (Submodule.equivMapOfInjective embedding embedding_injective
        target).length_eq
    _ = Module.length R (finiteWeightInitial (source.map embedding)) := by
      rw [hcompat]
    _ = Module.length R (source.map embedding) :=
      finiteWeightInitial_length (source.map embedding)
    _ = Module.length R source :=
      (Submodule.equivMapOfInjective embedding embedding_injective
        source).length_eq.symm

/-- Taking the full lexicographic initial ideal preserves the actual
coefficient-module length of every ordinary weighted degree slice. -/
theorem rankOne_lexicographicInitialIdeal_degree_length
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (degree : ℕ) :
    Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule
            (lexicographicInitialIdeal multiDegree I))
          ordinaryDegree (fun _ : Fin 1 => 0) (degree : ℤ)) =
      Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule I)
          ordinaryDegree (fun _ : Fin 1 => 0) (degree : ℤ)) := by
  let G := rankOnePolynomialGradedLexData ordinaryDegree multiDegree
  let sourceInitial := artinianPolynomialSubmoduleDegree
    (rankOnePolynomialIdealSubmodule
      (lexicographicInitialIdeal multiDegree I))
    G.ordinaryDegree G.ordinaryShift (degree : ℤ)
  let source := artinianPolynomialSubmoduleDegree
    (rankOnePolynomialIdealSubmodule I)
    G.ordinaryDegree G.ordinaryShift (degree : ℤ)
  let embedding := G.ordinaryDegreeOrderedWeightEmbedding
    (B := B) hpositive (degree : ℤ) (degree : ℤ) le_rfl
  have embedding_injective : Function.Injective embedding :=
    G.ordinaryDegreeOrderedWeightEmbedding_injective
      (B := B) hpositive (degree : ℤ) (degree : ℤ) le_rfl
  have hcompat : sourceInitial.map embedding =
      finiteWeightInitial (source.map embedding) := by
    simpa only [sourceInitial, source, embedding,
      PolynomialGradedLexData.rankOnePolynomialDegreeOrderedWeightPart]
      using
        (rankOnePolynomialDegreeOrderedWeightPart_lexicographicInitialIdeal
          ordinaryDegree multiDegree hpositive (degree : ℤ)
            degree le_rfl I hI)
  change Module.length B sourceInitial = Module.length B source
  exact submodule_length_eq_of_map_eq_finiteWeightInitial
    embedding embedding_injective source sourceInitial hcompat

/-- A negative ordinary degree has no rank-one monomials when the module
shift is zero. -/
theorem rankOne_ordinaryPolynomialModulePiece_eq_bot_of_neg
    (ordinaryDegree : Fin n → ℕ) {degree : ℤ} (hdegree : degree < 0) :
    artinianPolynomialModulePiece (B := B)
        ordinaryDegree (fun _ : Fin 1 => 0) degree = ⊥ := by
  apply le_antisymm
  · intro P hP
    rw [Submodule.mem_bot]
    funext k
    apply MvPolynomial.ext
    intro d
    by_contra hcoeff
    have hterm :=
      (mem_artinianPolynomialModuleSupported _ _).mp hP k d hcoeff
    have hweight : (Finsupp.weight ordinaryDegree d : ℤ) = degree := by
      simpa [artinianPolynomialDegreeTerms,
        artinianPolynomialTermDegree] using hterm
    have hnonneg : 0 ≤ degree := by
      rw [← hweight]
      exact Int.natCast_nonneg _
    exact (not_lt_of_ge hnonneg) hdegree
  · exact bot_le

/-- Consequently every submodule cut out inside a negative rank-one degree
piece is zero. -/
theorem rankOne_artinianPolynomialSubmoduleDegree_eq_bot_of_neg
    (ordinaryDegree : Fin n → ℕ)
    (I : Ideal (MvPolynomial (Fin n) B))
    {degree : ℤ} (hdegree : degree < 0) :
    artinianPolynomialSubmoduleDegree
        (rankOnePolynomialIdealSubmodule I)
        ordinaryDegree (fun _ : Fin 1 => 0) degree = ⊥ := by
  apply bot_unique
  intro P hP
  rw [Submodule.mem_bot]
  apply Subtype.ext
  have hPbot : (P : artinianFreePolynomialModule B n 1) ∈
      (⊥ : Submodule B (artinianFreePolynomialModule B n 1)) := by
    rw [← rankOne_ordinaryPolynomialModulePiece_eq_bot_of_neg
      ordinaryDegree hdegree]
    exact P.property
  rw [Submodule.mem_bot] at hPbot
  exact hPbot

/-- Integer-indexed form of degree-length preservation.  Negative slices
are zero, while a nonnegative integer slice is the corresponding natural
weighted degree. -/
theorem rankOne_lexicographicInitialIdeal_degree_length_int
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (degree : ℤ) :
    Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule
            (lexicographicInitialIdeal multiDegree I))
          ordinaryDegree (fun _ : Fin 1 => 0) degree) =
      Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule I)
          ordinaryDegree (fun _ : Fin 1 => 0) degree) := by
  by_cases hdegree : 0 ≤ degree
  · have hcast : (degree.toNat : ℤ) = degree :=
      Int.toNat_of_nonneg hdegree
    rw [← hcast]
    exact rankOne_lexicographicInitialIdeal_degree_length
      ordinaryDegree multiDegree hpositive I hI degree.toNat
  · have hneg : degree < 0 := lt_of_not_ge hdegree
    rw [rankOne_artinianPolynomialSubmoduleDegree_eq_bot_of_neg
        ordinaryDegree (lexicographicInitialIdeal multiDegree I) hneg,
      rankOne_artinianPolynomialSubmoduleDegree_eq_bot_of_neg
        ordinaryDegree I hneg]

/-- The natural-number-valued degree length used by the uniform Artinian
generator bound is therefore unchanged by lexicographic initial formation. -/
theorem rankOne_lexicographicInitialIdeal_degree_length_toNat
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (degree : ℕ) :
    (Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule
            (lexicographicInitialIdeal multiDegree I))
          ordinaryDegree (fun _ : Fin 1 => 0) (degree : ℤ))).toNat =
      (Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule I)
          ordinaryDegree (fun _ : Fin 1 => 0) (degree : ℤ))).toNat := by
  rw [rankOne_lexicographicInitialIdeal_degree_length
    ordinaryDegree multiDegree hpositive I hI degree]

/-- Natural-valued module length equality for every integer-indexed
ordinary slice. -/
theorem rankOne_lexicographicInitialIdeal_degree_length_int_toNat
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (degree : ℤ) :
    (Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule
            (lexicographicInitialIdeal multiDegree I))
          ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat =
      (Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule I)
          ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat := by
  rw [rankOne_lexicographicInitialIdeal_degree_length_int
    ordinaryDegree multiDegree hpositive I hI degree]

/-- Pointwise preservation of a prescribed ordinary Hilbert-length
function. -/
theorem rankOne_lexicographicInitialIdeal_hilbertLength
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (hilbertLength : ℕ → ℕ)
    (hLength : ∀ degree : ℕ,
      (Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule I)
          ordinaryDegree (fun _ : Fin 1 => 0) (degree : ℤ))).toNat =
        hilbertLength degree) :
    ∀ degree : ℕ,
      (Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule
            (lexicographicInitialIdeal multiDegree I))
          ordinaryDegree (fun _ : Fin 1 => 0) (degree : ℤ))).toNat =
        hilbertLength degree := by
  intro degree
  rw [rankOne_lexicographicInitialIdeal_degree_length_toNat
    ordinaryDegree multiDegree hpositive I hI degree]
  exact hLength degree

/-- Integer-indexed Hilbert-length transport in the exact form consumed by
the uniform Artinian bounded-generation theorem. -/
theorem rankOne_lexicographicInitialIdeal_hilbertLength_int
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (hilbertLength : ℤ → ℕ)
    (hLength : ∀ degree,
      (Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule I)
          ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat =
        hilbertLength degree) :
    ∀ degree,
      (Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOnePolynomialIdealSubmodule
            (lexicographicInitialIdeal multiDegree I))
          ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat =
        hilbertLength degree := by
  intro degree
  rw [rankOne_lexicographicInitialIdeal_degree_length_int_toNat
    ordinaryDegree multiDegree hpositive I hI degree]
  exact hLength degree

end AbelFormalization
