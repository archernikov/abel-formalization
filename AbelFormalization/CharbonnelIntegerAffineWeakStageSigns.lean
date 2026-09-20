import AbelFormalization.CharbonnelIntegerAffineSectionReplacement
import AbelFormalization.CharbonnelWeakStructure

/-!
# Integer-affine sign cuts at one weak-structure stage

Wilkie 3.13 applies WS1 and WS2 inside the earlier weak structure `J`:
if `B` is a member of `J`, then the exact hyperplane cut and both strict
sign cuts are also members of `J`. They consequently have rank-zero *base*
descriptions when the description language is instantiated with `J`.
This is not a strict-rank theorem for an arbitrary description over a fixed
generator family.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- The visible polynomial for the displayed integer-affine form. -/
def integerAffineSliceLinearPolynomial {n : ℕ}
    (coeff : Fin n → ℤ) (constant : ℤ) :
    MvPolynomial (Fin n) ℝ :=
  (∑ j : Fin n,
      MvPolynomial.C (coeff j : ℝ) * MvPolynomial.X j) +
    MvPolynomial.C (constant : ℝ)

theorem integerAffineSliceLinearPolynomial_eval
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (x : RealEuclidean n) :
    MvPolynomial.eval x
      (integerAffineSliceLinearPolynomial coeff constant) =
      integerAffineSliceLinearForm coeff constant x := by
  classical
  simp only [integerAffineSliceLinearPolynomial,
    integerAffineSliceLinearForm, map_add, map_sum, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- All three cells are polynomial-sign constructible, even for a zero
coefficient row. -/
theorem polynomialSignConstructible_integerAffineSliceHyperplane
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ) :
    PolynomialSignConstructible n
      (integerAffineSliceHyperplane coeff constant) := by
  simpa [integerAffineSliceHyperplane,
    integerAffineSliceLinearPolynomial_eval] using
    (PolynomialSignConstructible.zero
      (integerAffineSliceLinearPolynomial coeff constant))

theorem polynomialSignConstructible_integerAffineSlicePositiveSide
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ) :
    PolynomialSignConstructible n
      (integerAffineSlicePositiveSide coeff constant) := by
  simpa [integerAffineSlicePositiveSide,
    integerAffineSliceLinearPolynomial_eval] using
    (PolynomialSignConstructible.pos
      (integerAffineSliceLinearPolynomial coeff constant))

theorem polynomialSignConstructible_integerAffineSliceNegativeSide
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ) :
    PolynomialSignConstructible n
      (integerAffineSliceNegativeSide coeff constant) := by
  simpa [integerAffineSliceNegativeSide,
    integerAffineSliceLinearPolynomial_eval] using
    (PolynomialSignConstructible.neg
      (integerAffineSliceLinearPolynomial coeff constant))

/-- WS1--WS2 give exactly the three earlier-stage representatives used
in Wilkie 3.13. Their rank is zero relative to that earlier weak family
because each is a literal base member of it. -/
theorem PositiveArityWeakSetStructure.exists_rank_zero_integerAffineSlice_threeCuts
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    {n : ℕ} (hn : 0 < n)
    (B : Set (RealEuclidean n)) (hB : B ∈ S n)
    (coeff : Fin n → ℤ) (constant : ℤ) :
    ∃ exactCut positiveCut negativeCut : CharbonnelDescription S n,
      exactCut.carrier =
          B ∩ integerAffineSliceHyperplane coeff constant ∧
        exactCut.rank = 0 ∧
        positiveCut.carrier =
          B ∩ integerAffineSlicePositiveSide coeff constant ∧
        positiveCut.rank = 0 ∧
        negativeCut.carrier =
          B ∩ integerAffineSliceNegativeSide coeff constant ∧
        negativeCut.rank = 0 := by
  have hH : integerAffineSliceHyperplane coeff constant ∈ S n :=
    hS.ws2_polynomialSign hn
      (polynomialSignConstructible_integerAffineSliceHyperplane
        coeff constant)
  have hP : integerAffineSlicePositiveSide coeff constant ∈ S n :=
    hS.ws2_polynomialSign hn
      (polynomialSignConstructible_integerAffineSlicePositiveSide
        coeff constant)
  have hN : integerAffineSliceNegativeSide coeff constant ∈ S n :=
    hS.ws2_polynomialSign hn
      (polynomialSignConstructible_integerAffineSliceNegativeSide
        coeff constant)
  obtain ⟨exactCut, hexactCarrier, hexactRank⟩ :=
    hS.exists_rank_zero_inter_description hn hB hH
  obtain ⟨positiveCut, hpositiveCarrier, hpositiveRank⟩ :=
    hS.exists_rank_zero_inter_description hn hB hP
  obtain ⟨negativeCut, hnegativeCarrier, hnegativeRank⟩ :=
    hS.exists_rank_zero_inter_description hn hB hN
  exact ⟨exactCut, positiveCut, negativeCut,
    hexactCarrier, hexactRank, hpositiveCarrier, hpositiveRank,
    hnegativeCarrier, hnegativeRank⟩

end AbelFormalization
