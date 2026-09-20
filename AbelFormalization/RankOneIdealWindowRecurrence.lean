import AbelFormalization.PolynomialWindowIteration
import AbelFormalization.RankOneLexicographicWindowCompatibility

set_option autoImplicit false

/-!
# Rank-one ideal iteration and its bounded-window recurrence

This file packages the manuscript's ideal sequence

`I₀ = in(Q)`, `I_(j+1) = in(J(I_j))`

and identifies the bounded ordered-weight part of every successor with the
finite-weight descent step.  The only interface required from the polynomial
automorphism is its action on the chosen bounded window and preservation of
the independent ordinary grading.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n h : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## The ideal and rank-one-submodule sequences -/

/-- Iterate full lexicographic initial formation after applying a polynomial
ring automorphism.  The initial object is itself a full initial ideal, so
every term of the sequence is homogeneous for the lexicographic grading. -/
def lexicographicInitialIdealIteration
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) :
    ℕ → Ideal (MvPolynomial (Fin n) B)
  | 0 => lexicographicInitialIdeal multiDegree Q
  | j + 1 =>
      lexicographicInitialIdeal multiDegree
        ((lexicographicInitialIdealIteration multiDegree J Q j).map
          J.toRingHom)

@[simp]
theorem lexicographicInitialIdealIteration_zero
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) :
    lexicographicInitialIdealIteration multiDegree J Q 0 =
      lexicographicInitialIdeal multiDegree Q :=
  rfl

@[simp]
theorem lexicographicInitialIdealIteration_succ
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j : ℕ) :
    lexicographicInitialIdealIteration multiDegree J Q (j + 1) =
      lexicographicInitialIdeal multiDegree
        ((lexicographicInitialIdealIteration multiDegree J Q j).map
          J.toRingHom) :=
  rfl

/-- The actual rank-one polynomial submodule corresponding to `I_j`. -/
def rankOneLexicographicInitialSubmoduleIteration
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j : ℕ) :
    Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n 1) :=
  rankOnePolynomialIdealSubmodule
    (lexicographicInitialIdealIteration multiDegree J Q j)

/-- The rank-one submodule obtained by applying `J` to `I_j`.  This is the
sequence called `JN` by the abstract polynomial-window stabilization API. -/
def rankOneMappedLexicographicInitialSubmoduleIteration
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j : ℕ) :
    Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n 1) :=
  rankOnePolynomialIdealSubmodule
    ((lexicographicInitialIdealIteration multiDegree J Q j).map J.toRingHom)

/-! ## Homogeneity of the iteration -/

/-- Every rank-one term of the ideal iteration is homogeneous for the
ordered lexicographic weight projections. -/
theorem rankOneLexicographicInitialSubmoduleIteration_weightHomogeneous
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j : ℕ) :
    PolynomialGradedLexData.IsPolynomialModuleWeightHomogeneous
      (rankOnePolynomialGradedLexData ordinaryDegree multiDegree)
      (rankOneLexicographicInitialSubmoduleIteration multiDegree J Q j) := by
  cases j with
  | zero =>
      exact
        rankOnePolynomialIdealSubmodule_lexicographicInitial_weightHomogeneous
          ordinaryDegree multiDegree Q
  | succ j =>
      exact
        rankOnePolynomialIdealSubmodule_lexicographicInitial_weightHomogeneous
          ordinaryDegree multiDegree
          ((lexicographicInitialIdealIteration multiDegree J Q j).map
            J.toRingHom)

/-- If `Q` is ordinary homogeneous and `J` preserves ordinary homogeneous
ideals, then every `I_j` remains ordinary homogeneous. -/
theorem lexicographicInitialIdealIteration_ordinaryHomogeneous
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (hJordinary : ∀ I : Ideal (MvPolynomial (Fin n) B),
      I.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) →
        (I.map J.toRingHom).IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ)))) :
    ∀ j, (lexicographicInitialIdealIteration multiDegree J Q j).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))) := by
  intro j
  induction j with
  | zero =>
      exact lexicographicInitialIdeal_isHomogeneous_of_isHomogeneous
        (fun i => (ordinaryDegree i : ℤ)) multiDegree Q hQ
  | succ j ih =>
      exact lexicographicInitialIdeal_isHomogeneous_of_isHomogeneous
        (fun i => (ordinaryDegree i : ℤ)) multiDegree
        ((lexicographicInitialIdealIteration multiDegree J Q j).map
          J.toRingHom)
        (hJordinary _ ih)

/-- The intermediate mapped ideal `J(I_j)` is ordinary homogeneous. -/
theorem lexicographicInitialIdealIteration_map_ordinaryHomogeneous
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (hJordinary : ∀ I : Ideal (MvPolynomial (Fin n) B),
      I.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) →
        (I.map J.toRingHom).IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))))
    (j : ℕ) :
    ((lexicographicInitialIdealIteration multiDegree J Q j).map
        J.toRingHom).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))) :=
  hJordinary _
    (lexicographicInitialIdealIteration_ordinaryHomogeneous
      ordinaryDegree multiDegree J Q hQ hJordinary j)

/-! ## Exact bounded-window recurrence -/

/-- The ideal recurrence becomes the literal finite-weight recurrence on
the bounded ordered-weight product.  `hJpart` is precisely the remaining
window-restriction statement about the concrete polynomial automorphism. -/
theorem rankOneLexicographicInitialSubmoduleIteration_window_recurrence
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (A :
      ((i : Fin ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).weightCount hpositive D)) →
        (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).orderedWeightPiece B hpositive D i) ≃ₗ[B]
      ((i : Fin ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).weightCount hpositive D)) →
        (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).orderedWeightPiece B hpositive D i))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (hJordinary : ∀ I : Ideal (MvPolynomial (Fin n) B),
      I.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) →
        (I.map J.toRingHom).IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))))
    (hJpart : ∀ j,
      (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).polynomialWindowOrderedWeightPart hpositive D
          (rankOneMappedLexicographicInitialSubmoduleIteration
            multiDegree J Q j) =
        ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).polynomialWindowOrderedWeightPart hpositive D
          (rankOneLexicographicInitialSubmoduleIteration
            multiDegree J Q j)).map A.toLinearMap) :
    ∀ j,
      (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).polynomialWindowOrderedWeightPart hpositive D
          (rankOneLexicographicInitialSubmoduleIteration
            multiDegree J Q (j + 1)) =
        finiteWeightDescentStep A
          ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).polynomialWindowOrderedWeightPart hpositive D
            (rankOneLexicographicInitialSubmoduleIteration
              multiDegree J Q j)) := by
  intro j
  let G := rankOnePolynomialGradedLexData ordinaryDegree multiDegree
  let Ij := lexicographicInitialIdealIteration multiDegree J Q j
  calc
    G.polynomialWindowOrderedWeightPart hpositive D
        (rankOneLexicographicInitialSubmoduleIteration
          multiDegree J Q (j + 1)) =
      G.polynomialWindowOrderedWeightPart hpositive D
        (rankOnePolynomialIdealSubmodule
          (lexicographicInitialIdeal multiDegree (Ij.map J.toRingHom))) := rfl
    _ = finiteWeightInitial
        (G.polynomialWindowOrderedWeightPart hpositive D
          (rankOnePolynomialIdealSubmodule (Ij.map J.toRingHom))) :=
      polynomialWindowOrderedWeightPart_rankOne_lexicographicInitialIdeal
        ordinaryDegree multiDegree hpositive D (Ij.map J.toRingHom)
        (lexicographicInitialIdealIteration_map_ordinaryHomogeneous
          ordinaryDegree multiDegree J Q hQ hJordinary j)
    _ = finiteWeightInitial
        ((G.polynomialWindowOrderedWeightPart hpositive D
          (rankOneLexicographicInitialSubmoduleIteration
            multiDegree J Q j)).map A.toLinearMap) := by
      congr 1
      simpa [G, Ij,
        rankOneMappedLexicographicInitialSubmoduleIteration] using hJpart j
    _ = finiteWeightDescentStep A
        (G.polynomialWindowOrderedWeightPart hpositive D
          (rankOneLexicographicInitialSubmoduleIteration
            multiDegree J Q j)) := rfl

/-! ## Direct interface to polynomial-window stabilization -/

/-- Once one common generation window and the concrete triangular window
action are supplied, the actual ideal iteration stabilizes at an ideal
fixed by `J`. -/
theorem exists_lexicographicInitialIdealIteration_stabilizes_of_window_data
    (d : ℕ) [IsNoetherianRing B] [Ring.KrullDimLE d B]
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Q : Ideal (MvPolynomial (Fin n) B))
    (A :
      ((i : Fin ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).weightCount hpositive D)) →
        (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).orderedWeightPiece B hpositive D i) ≃ₗ[B]
      ((i : Fin ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).weightCount hpositive D)) →
        (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).orderedWeightPiece B hpositive D i))
    (htri : ∀ i
      (v : (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).orderedWeightPiece B hpositive D i),
      A (Pi.single i v) = Pi.single i v +
        finiteWeightPrefixProjection B
          (fun i : Fin ((rankOnePolynomialGradedLexData
              ordinaryDegree multiDegree).weightCount hpositive D) =>
            (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).orderedWeightPiece B hpositive D i) i.val
          (A (Pi.single i v)))
    (hQ : Q.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    (hJordinary : ∀ I : Ideal (MvPolynomial (Fin n) B),
      I.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) →
        (I.map J.toRingHom).IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))))
    (hNgen : ∀ j,
      (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).IsGeneratedInPolynomialWindow hpositive D
        (rankOneLexicographicInitialSubmoduleIteration multiDegree J Q j))
    (hJNgen : ∀ j,
      (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).IsGeneratedInPolynomialWindow hpositive D
        (rankOneMappedLexicographicInitialSubmoduleIteration
          multiDegree J Q j))
    (hJpart : ∀ j,
      (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).polynomialWindowOrderedWeightPart hpositive D
          (rankOneMappedLexicographicInitialSubmoduleIteration
            multiDegree J Q j) =
        ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).polynomialWindowOrderedWeightPart hpositive D
          (rankOneLexicographicInitialSubmoduleIteration
            multiDegree J Q j)).map A.toLinearMap) :
    ∃ j₀ : ℕ,
      (lexicographicInitialIdealIteration multiDegree J Q j₀).map
          J.toRingHom =
        lexicographicInitialIdealIteration multiDegree J Q j₀ ∧
      ∀ j, j₀ ≤ j →
        lexicographicInitialIdealIteration multiDegree J Q j =
          lexicographicInitialIdealIteration multiDegree J Q j₀ := by
  let G := rankOnePolynomialGradedLexData ordinaryDegree multiDegree
  let N := rankOneLexicographicInitialSubmoduleIteration multiDegree J Q
  let JN := rankOneMappedLexicographicInitialSubmoduleIteration multiDegree J Q
  obtain ⟨j₀, hfixed, hstable⟩ :=
    G.exists_polynomialSubmodule_stabilizes_of_window_recurrence
      d hpositive D A htri N JN
      (rankOneLexicographicInitialSubmoduleIteration_weightHomogeneous
        ordinaryDegree multiDegree J Q)
      hNgen hJNgen hJpart
      (rankOneLexicographicInitialSubmoduleIteration_window_recurrence
        ordinaryDegree multiDegree hpositive D J Q A
        hQ hJordinary hJpart)
  refine ⟨j₀, ?_, ?_⟩
  · apply rankOnePolynomialIdealSubmodule_injective
    exact hfixed
  · intro j hj
    apply rankOnePolynomialIdealSubmodule_injective
    exact hstable j hj

end AbelFormalization
