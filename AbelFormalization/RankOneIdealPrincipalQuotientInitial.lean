import AbelFormalization.FiniteWeightRestrictedDescent
import AbelFormalization.FiniteWeightScalarMultiple
import AbelFormalization.RankOneLexicographicWindowCompatibility
import Mathlib.RingTheory.Ideal.Operations

set_option autoImplicit false

/-!
# Initial submodules in a principal restricted quotient

This file isolates the quotient calculation in the induction step of the
rank-one ideal argument.  If `b • K ≤ N ≤ K`, with `K` homogeneous for the
finite ordered weights, then the image of the initial submodule of `N` in
`K / bK` is the initial submodule of the image of `N`.

The statement is deliberately made in the coordinate product attached to
`K`.  In that product, the quotient map is coordinatewise and has kernel
exactly `b • ⊤`.  Thus the reverse inclusion is the manuscript's operation
of subtracting all lower components that vanish modulo `b`.

The last section translates the two sides of the sandwich from polynomial
ideals, where the lower term is `span {C b} * K`, to the bounded ordered
weight module used by the rank-one iteration.
-/

noncomputable section

namespace AbelFormalization

open scoped Pointwise

section FiniteWeight

variable {R : Type*} [CommRing R] {w : ℕ}
variable {M : Fin w → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The lower half of the sandwich `b • K ≤ N` contains the kernel of the
coordinatewise quotient map after pulling `N` back to the coordinate product
belonging to `K`. -/
theorem ker_finiteWeightRestrictedPiQuotientMap_le_coordinatePullback
    (K N : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (b : R) (hbKN : b • K ≤ N) :
    LinearMap.ker (finiteWeightRestrictedPiQuotientMap K b) ≤
      finiteWeightCoordinatePullback K N := by
  rw [ker_finiteWeightRestrictedPiQuotientMap,
    Submodule.ideal_span_singleton_smul,
    ← finiteWeightCoordinatePullback_pointwise_smul K hK b]
  exact Submodule.comap_mono hbKN

/-- Componentwise form of the principal-quotient initial calculation.

It says that the image of the possible least nonzero `i`th components of
`N`, viewed inside the homogeneous ambient module `K`, is precisely the set
of possible least nonzero `i`th components after passage to `K / bK`. -/
theorem map_finiteWeightInitialPiece_coordinatePullback_restrictedQuotient
    (K N : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (b : R) (hbKN : b • K ≤ N) (i : Fin w) :
    (finiteWeightInitialPiece
        (finiteWeightCoordinatePullback K N) i).map
          (finiteWeightRestrictedCoordinateQuotientMap K b i) =
      finiteWeightInitialPiece
        ((finiteWeightCoordinatePullback K N).map
          (finiteWeightRestrictedPiQuotientMap K b)) i := by
  simpa only [finiteWeightRestrictedPiQuotientMap] using
    (map_finiteWeightInitialPiece_eq_finiteWeightInitialPiece_map
      (finiteWeightRestrictedCoordinateQuotientMap K b)
      (finiteWeightCoordinatePullback K N)
      (ker_finiteWeightRestrictedPiQuotientMap_le_coordinatePullback
        K N hK b hbKN) i)

/-- Initial formation commutes with passage from `N` to its image in the
restricted principal quotient `K / bK`.

Only the lower inclusion `b • K ≤ N` is required for this equality.  The
upper inclusion `N ≤ K` is used separately to identify the coordinate
pullback with the original ambient submodule. -/
theorem map_finiteWeightInitial_coordinatePullback_restrictedQuotient
    (K N : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (b : R) (hbKN : b • K ≤ N) :
    (finiteWeightInitial
        (finiteWeightCoordinatePullback K N)).map
          (finiteWeightRestrictedPiQuotientMap K b) =
      finiteWeightInitial
        ((finiteWeightCoordinatePullback K N).map
          (finiteWeightRestrictedPiQuotientMap K b)) := by
  simpa only [finiteWeightRestrictedPiQuotientMap] using
    (map_finiteWeightInitial_eq_finiteWeightInitial_map
      (finiteWeightRestrictedCoordinateQuotientMap K b)
      (finiteWeightCoordinatePullback K N)
      (ker_finiteWeightRestrictedPiQuotientMap_le_coordinatePullback
        K N hK b hbKN))

/-- If a triangular action preserves `K`, the whole descent recursion on
`N` commutes with the restricted quotient.  The case `j = 1` is the
manuscript's successor calculation; the iterated statement is the form used
by dimension induction. -/
theorem map_finiteWeightInvariantCoordinatePullback_descentIterate_restrictedQuotient
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (K N : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hJK : K.map J.toLinearMap = K)
    (b : R) (hbKN : b • K ≤ N) (j : ℕ) :
    (finiteWeightDescentIterate
        (finiteWeightInvariantCoordinateEquiv J K hK hJK)
        (finiteWeightCoordinatePullback K N) j).map
          (finiteWeightRestrictedPiQuotientMap K b) =
      finiteWeightDescentIterate
        (finiteWeightRestrictedEquivOfInvariant J K hK hJK b)
        ((finiteWeightCoordinatePullback K N).map
          (finiteWeightRestrictedPiQuotientMap K b)) j := by
  apply map_finiteWeightInvariantCoordinate_descentIterate_eq
    J K hK hJK b (finiteWeightCoordinatePullback K N)
  rw [Submodule.ideal_span_singleton_smul,
    ← finiteWeightCoordinatePullback_pointwise_smul K hK b]
  exact Submodule.comap_mono hbKN

/-- If `N ≤ K`, the internal initial submodule formed in the coordinate
product of `K` maps back to the ordinary finite-weight initial submodule of
`N` in the ambient product. -/
theorem map_finiteWeightInitial_coordinatePullback_inclusion
    (K N : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hNK : N ≤ K) :
    (finiteWeightInitial
        (finiteWeightCoordinatePullback K N)).map
          (finiteWeightCoordinateInclusionMap K) =
      finiteWeightInitial N := by
  have h := map_finiteWeightInitial_eq_finiteWeightInitial_map
    (σ := RingHom.id R) (finiteWeightCoordinateInclusion K)
    (finiteWeightCoordinatePullback K N)
    (by
      change LinearMap.ker (finiteWeightCoordinateInclusionMap K) ≤
        finiteWeightCoordinatePullback K N
      rw [ker_finiteWeightCoordinateInclusionMap]
      exact bot_le)
  change
    (finiteWeightInitial
        (finiteWeightCoordinatePullback K N)).map
          (finiteWeightCoordinateInclusionMap K) =
      finiteWeightInitial
        ((finiteWeightCoordinatePullback K N).map
          (finiteWeightCoordinateInclusionMap K)) at h
  rw [map_finiteWeightCoordinatePullback_eq K N hK hNK] at h
  exact h

end FiniteWeight

section RankOneWindow

variable {B : Type*} [CommRing B] {n h : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The ordered bounded-window part of a polynomial ideal, transported to
the rank-one polynomial module. -/
abbrev rankOneIdealOrderedWindow
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B)) :=
  (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).polynomialWindowOrderedWeightPart
    hpositive D
      (rankOnePolynomialIdealSubmodule I)

/-- Inclusion of polynomial ideals restricts to inclusion of their ordered
bounded-window parts. -/
theorem rankOneIdealOrderedWindow_mono
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    {N K : Ideal (MvPolynomial (Fin n) B)} (hNK : N ≤ K) :
    rankOneIdealOrderedWindow ordinaryDegree multiDegree hpositive D N ≤
      rankOneIdealOrderedWindow ordinaryDegree multiDegree hpositive D K := by
  let G := rankOnePolynomialGradedLexData ordinaryDegree multiDegree
  intro x hx
  apply (G.mem_polynomialWindowOrderedWeightPart_rankOneIdeal_iff
    hpositive D K x).mpr
  exact hNK ((G.mem_polynomialWindowOrderedWeightPart_rankOneIdeal_iff
    hpositive D N x).mp hx)

/-- Multiplication by the coefficient `b` in an ideal becomes scalar
multiplication by `b` on its ordered bounded-window part.

The hypothesis is the literal ideal-theoretic lower sandwich
`span {C b} * K ≤ N` from the manuscript. -/
theorem pointwise_smul_rankOneIdealOrderedWindow_le
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (b : B) (K N : Ideal (MvPolynomial (Fin n) B))
    (hbKN : Ideal.span {MvPolynomial.C b} * K ≤ N) :
    b • rankOneIdealOrderedWindow
        ordinaryDegree multiDegree hpositive D K ≤
      rankOneIdealOrderedWindow
        ordinaryDegree multiDegree hpositive D N := by
  let G := rankOnePolynomialGradedLexData ordinaryDegree multiDegree
  intro x hx
  rcases (mem_pointwise_smul_submodule_iff b
    (rankOneIdealOrderedWindow
      ordinaryDegree multiDegree hpositive D K) x).mp hx with
    ⟨y, hyK, hby⟩
  have hyK' :
      ((((G.windowOrderedWeightLinearEquiv
          (B := B) hpositive D).symm y :
            G.windowModule B hpositive D) :
          artinianFreePolynomialModule B n 1) 0) ∈ K :=
    (G.mem_polynomialWindowOrderedWeightPart_rankOneIdeal_iff
      hpositive D K y).mp hyK
  apply (G.mem_polynomialWindowOrderedWeightPart_rankOneIdeal_iff
    hpositive D N x).mpr
  rw [← hby]
  have hmul :
      MvPolynomial.C b *
          ((((G.windowOrderedWeightLinearEquiv
              (B := B) hpositive D).symm y :
                G.windowModule B hpositive D) :
              artinianFreePolynomialModule B n 1) 0) ∈ N :=
    hbKN (Ideal.mul_mem_mul
      (Ideal.mem_span_singleton_self (MvPolynomial.C b)) hyK')
  simpa only [map_smul, Submodule.coe_smul, Pi.smul_apply,
    MvPolynomial.smul_eq_C_mul] using hmul

/-- Multiweight homogeneity of a rank-one ideal makes its ordered window
literally coordinatewise homogeneous. -/
theorem rankOneIdealOrderedWindow_homogeneous
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (K : Ideal (MvPolynomial (Fin n) B))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => toLex (multiDegree i)))) :
    ∀ x ∈ rankOneIdealOrderedWindow
        ordinaryDegree multiDegree hpositive D K,
      ∀ i, Pi.single i (x i) ∈
        rankOneIdealOrderedWindow
          ordinaryDegree multiDegree hpositive D K := by
  let G := rankOnePolynomialGradedLexData ordinaryDegree multiDegree
  exact G.polynomialWindowOrderedWeightPart_homogeneous
    hpositive D (rankOnePolynomialIdealSubmodule K)
      (rankOnePolynomialIdealSubmodule_weightHomogeneous
        ordinaryDegree multiDegree K hK)

/-- The exact restricted quotient statement for rank-one polynomial ideals.

The first conjunct records that the image really is the passage of `N`
inside `K`.  The second conjunct is

`image (initial N) = initial (image N)`

in the coordinatewise model of `K / C(b)K`. -/
def RankOnePrincipalQuotientInitialCompatible
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (b : B) (K N : Ideal (MvPolynomial (Fin n) B)) : Prop :=
  let WK := rankOneIdealOrderedWindow
    ordinaryDegree multiDegree hpositive D K
  let WN := rankOneIdealOrderedWindow
    ordinaryDegree multiDegree hpositive D N
  WN ≤ WK ∧
    (finiteWeightInitial (finiteWeightCoordinatePullback WK WN)).map
        (finiteWeightRestrictedPiQuotientMap WK b) =
      finiteWeightInitial
        ((finiteWeightCoordinatePullback WK WN).map
          (finiteWeightRestrictedPiQuotientMap WK b))

/-- The polynomial sandwich `C(b)K ≤ N ≤ K` implies exact compatibility of
initial formation with the restricted principal quotient in every bounded
ordinary-degree window. -/
theorem rankOnePrincipalQuotientInitialCompatible_of_sandwich
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (b : B) (K N : Ideal (MvPolynomial (Fin n) B))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => toLex (multiDegree i))))
    (hbKN : Ideal.span {MvPolynomial.C b} * K ≤ N)
    (hNK : N ≤ K) :
    RankOnePrincipalQuotientInitialCompatible
      ordinaryDegree multiDegree hpositive D b K N := by
  let WK := rankOneIdealOrderedWindow
    ordinaryDegree multiDegree hpositive D K
  let WN := rankOneIdealOrderedWindow
    ordinaryDegree multiDegree hpositive D N
  have hWKh : ∀ x ∈ WK, ∀ i, Pi.single i (x i) ∈ WK := by
    simpa only [WK] using rankOneIdealOrderedWindow_homogeneous
      ordinaryDegree multiDegree hpositive D K hK
  have hbWN : b • WK ≤ WN := by
    simpa only [WK, WN] using
      pointwise_smul_rankOneIdealOrderedWindow_le
        ordinaryDegree multiDegree hpositive D b K N hbKN
  have hWNK : WN ≤ WK := by
    simpa only [WK, WN] using
      rankOneIdealOrderedWindow_mono
        ordinaryDegree multiDegree hpositive D hNK
  change WN ≤ WK ∧
    (finiteWeightInitial (finiteWeightCoordinatePullback WK WN)).map
        (finiteWeightRestrictedPiQuotientMap WK b) =
      finiteWeightInitial
        ((finiteWeightCoordinatePullback WK WN).map
          (finiteWeightRestrictedPiQuotientMap WK b))
  exact ⟨hWNK,
    map_finiteWeightInitial_coordinatePullback_restrictedQuotient
      WK WN hWKh b hbWN⟩

/-- Returning from the coordinate product of `K` to the ambient ordered
window identifies the internal initial submodule with the actual bounded
window of the lexicographic initial ideal of `N`. -/
theorem map_rankOneInternalInitial_inclusion_eq_lexicographicInitialWindow
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (K N : Ideal (MvPolynomial (Fin n) B))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => toLex (multiDegree i))))
    (hNordinary : N.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (hNK : N ≤ K) :
    let WK := rankOneIdealOrderedWindow
      ordinaryDegree multiDegree hpositive D K
    let WN := rankOneIdealOrderedWindow
      ordinaryDegree multiDegree hpositive D N
    (finiteWeightInitial (finiteWeightCoordinatePullback WK WN)).map
        (finiteWeightCoordinateInclusionMap WK) =
      rankOneIdealOrderedWindow ordinaryDegree multiDegree hpositive D
        (lexicographicInitialIdeal multiDegree N) := by
  let G := rankOnePolynomialGradedLexData ordinaryDegree multiDegree
  let WK := rankOneIdealOrderedWindow
    ordinaryDegree multiDegree hpositive D K
  let WN := rankOneIdealOrderedWindow
    ordinaryDegree multiDegree hpositive D N
  have hWKh : ∀ x ∈ WK, ∀ i, Pi.single i (x i) ∈ WK := by
    simpa only [WK] using rankOneIdealOrderedWindow_homogeneous
      ordinaryDegree multiDegree hpositive D K hK
  have hWNK : WN ≤ WK := by
    simpa only [WK, WN] using
      rankOneIdealOrderedWindow_mono
        ordinaryDegree multiDegree hpositive D hNK
  calc
    (finiteWeightInitial (finiteWeightCoordinatePullback WK WN)).map
        (finiteWeightCoordinateInclusionMap WK) =
      finiteWeightInitial WN :=
        map_finiteWeightInitial_coordinatePullback_inclusion
          WK WN hWKh hWNK
    _ = rankOneIdealOrderedWindow ordinaryDegree multiDegree hpositive D
        (lexicographicInitialIdeal multiDegree N) := by
      symm
      simpa only [G, WN, rankOneIdealOrderedWindow] using
        polynomialWindowOrderedWeightPart_rankOne_lexicographicInitialIdeal
          ordinaryDegree multiDegree hpositive D N hNordinary

end RankOneWindow

end AbelFormalization
