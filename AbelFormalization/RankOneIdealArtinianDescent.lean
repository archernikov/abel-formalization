import AbelFormalization.RankOneIdealInitialHilbert
import AbelFormalization.RankOneIdealWindowRecurrence

set_option autoImplicit false

/-!
# Artinian stabilization of the rank-one initial-ideal iteration

This file closes the abstract finite-descent argument for the rank-one ideal
sequence

`I₀ = in(Q)`, `I_(j+1) = in(J(I_j))`.

The Artinian uniform generator theorem supplies one ordinary-degree window
for every `I_j` and every intermediate ideal `J(I_j)`.  Equality of the
ordinary Hilbert lengths along the sequence follows from two facts: `J`
preserves the lengths of ordinary slices, and full lexicographic initial
formation preserves them.  The bounded-window recurrence then invokes
`exists_lexicographicInitialIdealIteration_stabilizes_of_window_data`.

The hypotheses concerning `Jmodule` are the exact interface expected from a
concrete polynomial automorphism: it realizes the action of `J` on rank-one
bounded parts, preserves every ordinary window, and is strictly lower
triangular in the ordered lexicographic weights.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n h : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Hilbert lengths along the recursive ideal sequence -/

/-- If the polynomial automorphism preserves the length of every ordinary
homogeneous slice, then all ideals in the recursive lexicographic-initial
sequence have the same ordinary Hilbert-length function. -/
theorem lexicographicInitialIdealIteration_degreeLength_toNat
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i)
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
    (hJlength : ∀ (I : Ideal (MvPolynomial (Fin n) B)),
      I.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) →
      ∀ degree : ℤ,
        (Module.length B
          (artinianPolynomialSubmoduleDegree
            (rankOnePolynomialIdealSubmodule (I.map J.toRingHom))
            ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat =
          (Module.length B
            (artinianPolynomialSubmoduleDegree
              (rankOnePolynomialIdealSubmodule I)
              ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat) :
    ∀ (j : ℕ) (degree : ℤ),
      (Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOneLexicographicInitialSubmoduleIteration
            multiDegree J Q j)
          ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat =
        (Module.length B
          (artinianPolynomialSubmoduleDegree
            (rankOneLexicographicInitialSubmoduleIteration
              multiDegree J Q 0)
            ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat := by
  intro j
  induction j with
  | zero =>
      intro degree
      rfl
  | succ j ih =>
      intro degree
      let Ij := lexicographicInitialIdealIteration multiDegree J Q j
      have hIj : Ij.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) :=
        lexicographicInitialIdealIteration_ordinaryHomogeneous
          ordinaryDegree multiDegree J Q hQ hJordinary j
      have hJIj : (Ij.map J.toRingHom).IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) :=
        hJordinary Ij hIj
      calc
        (Module.length B
            (artinianPolynomialSubmoduleDegree
              (rankOneLexicographicInitialSubmoduleIteration
                multiDegree J Q (j + 1))
              ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat =
            (Module.length B
              (artinianPolynomialSubmoduleDegree
                (rankOnePolynomialIdealSubmodule
                  (lexicographicInitialIdeal multiDegree
                    (Ij.map J.toRingHom)))
                ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat := by
                  rfl
        _ = (Module.length B
              (artinianPolynomialSubmoduleDegree
                (rankOnePolynomialIdealSubmodule (Ij.map J.toRingHom))
                ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat :=
          rankOne_lexicographicInitialIdeal_degree_length_int_toNat
            ordinaryDegree multiDegree hpositive
              (Ij.map J.toRingHom) hJIj degree
        _ = (Module.length B
              (artinianPolynomialSubmoduleDegree
                (rankOnePolynomialIdealSubmodule Ij)
                ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat :=
          hJlength Ij hIj degree
        _ = (Module.length B
              (artinianPolynomialSubmoduleDegree
                (rankOneLexicographicInitialSubmoduleIteration
                  multiDegree J Q 0)
                ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat :=
          ih degree

/-- The intermediate mapped ideals `J(I_j)` have the same Hilbert-length
function as the recursive initial ideals. -/
theorem mappedLexicographicInitialIdealIteration_degreeLength_toNat
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i)
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
    (hJlength : ∀ (I : Ideal (MvPolynomial (Fin n) B)),
      I.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) →
      ∀ degree : ℤ,
        (Module.length B
          (artinianPolynomialSubmoduleDegree
            (rankOnePolynomialIdealSubmodule (I.map J.toRingHom))
            ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat =
          (Module.length B
            (artinianPolynomialSubmoduleDegree
              (rankOnePolynomialIdealSubmodule I)
              ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat) :
    ∀ (j : ℕ) (degree : ℤ),
      (Module.length B
        (artinianPolynomialSubmoduleDegree
          (rankOneMappedLexicographicInitialSubmoduleIteration
            multiDegree J Q j)
          ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat =
        (Module.length B
          (artinianPolynomialSubmoduleDegree
            (rankOneLexicographicInitialSubmoduleIteration
              multiDegree J Q 0)
            ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat := by
  intro j degree
  let Ij := lexicographicInitialIdealIteration multiDegree J Q j
  have hIj : Ij.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))) :=
    lexicographicInitialIdealIteration_ordinaryHomogeneous
      ordinaryDegree multiDegree J Q hQ hJordinary j
  exact (hJlength Ij hIj degree).trans
    (lexicographicInitialIdealIteration_degreeLength_toNat
      ordinaryDegree multiDegree hpositive J Q hQ hJordinary hJlength
        j degree)

/-! ## Artinian descent -/

/-- Over an Artinian coefficient ring, a nilpotent maximal coefficient
ideal gives a uniform generator window for the whole recursive sequence.
If the concrete polynomial automorphism has the stated graded and
triangular rank-one realizations, the sequence stabilizes at an ideal fixed
by the automorphism. -/
theorem exists_lexicographicInitialIdealIteration_stabilizes_of_isArtinianRing
    [IsArtinianRing B]
    (monomialOrder : MonomialOrder (Fin n))
    (coefficientIdeal : Ideal B) [coefficientIdeal.IsMaximal]
    {e : ℕ} (he : coefficientIdeal ^ e = ⊥)
    (ordinaryDegree : Fin n → ℕ)
    (multiDegree : Fin n → Fin h → ℤ)
    (hpositive : ∀ i, 0 < ordinaryDegree i)
    (J : MvPolynomial (Fin n) B ≃+* MvPolynomial (Fin n) B)
    (Jmodule : artinianFreePolynomialModule B n 1 ≃ₗ[B]
      artinianFreePolynomialModule B n 1)
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
    (hJlength : ∀ (I : Ideal (MvPolynomial (Fin n) B)),
      I.IsHomogeneous
          (MvPolynomial.weightedHomogeneousSubmodule B
            (fun i => (ordinaryDegree i : ℤ))) →
      ∀ degree : ℤ,
        (Module.length B
          (artinianPolynomialSubmoduleDegree
            (rankOnePolynomialIdealSubmodule (I.map J.toRingHom))
            ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat =
          (Module.length B
            (artinianPolynomialSubmoduleDegree
              (rankOnePolynomialIdealSubmodule I)
              ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat)
    (hJwindow : ∀ D : ℤ,
      ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).windowModule B hpositive D).map Jmodule.toLinearMap =
        (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).windowModule B hpositive D)
    (hJtriangular : ∀ D : ℤ,
      (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).IsWindowWeightTriangular hpositive D Jmodule)
    (hJpart : ∀ (D : ℤ) (I : Ideal (MvPolynomial (Fin n) B)),
      (rankOnePolynomialGradedLexData ordinaryDegree multiDegree).polynomialWindowOrderedWeightPart hpositive D
          (rankOnePolynomialIdealSubmodule (I.map J.toRingHom)) =
        ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).polynomialWindowOrderedWeightPart hpositive D
          (rankOnePolynomialIdealSubmodule I)).map
            ((rankOnePolynomialGradedLexData ordinaryDegree multiDegree).windowOrderedWeightConjugate hpositive D Jmodule
                (hJwindow D)).toLinearMap) :
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
  let hilbertLength : ℤ → ℕ := fun degree =>
    (Module.length B
      (artinianPolynomialSubmoduleDegree (N 0)
        ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat
  have hIordinary : ∀ j,
      (lexicographicInitialIdealIteration multiDegree J Q j).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule B
          (fun i => (ordinaryDegree i : ℤ))) :=
    lexicographicInitialIdealIteration_ordinaryHomogeneous
      ordinaryDegree multiDegree J Q hQ hJordinary
  have hJIordinary : ∀ j,
      ((lexicographicInitialIdealIteration multiDegree J Q j).map
          J.toRingHom).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule B
          (fun i => (ordinaryDegree i : ℤ))) := fun j =>
    hJordinary _ (hIordinary j)
  have hNordinary : ∀ j,
      IsArtinianPolynomialSubmoduleHomogeneous
        ordinaryDegree (fun _ : Fin 1 => 0) (N j) := fun j =>
    rankOnePolynomialIdealSubmodule_ordinaryHomogeneous
      ordinaryDegree _ (hIordinary j)
  have hJNordinary : ∀ j,
      IsArtinianPolynomialSubmoduleHomogeneous
        ordinaryDegree (fun _ : Fin 1 => 0) (JN j) := fun j =>
    rankOnePolynomialIdealSubmodule_ordinaryHomogeneous
      ordinaryDegree _ (hJIordinary j)
  have hNlength : ∀ j degree,
      (Module.length B
        (artinianPolynomialSubmoduleDegree (N j)
          ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat =
        hilbertLength degree :=
    lexicographicInitialIdealIteration_degreeLength_toNat
      ordinaryDegree multiDegree hpositive J Q hQ hJordinary hJlength
  have hJNlength : ∀ j degree,
      (Module.length B
        (artinianPolynomialSubmoduleDegree (JN j)
          ordinaryDegree (fun _ : Fin 1 => 0) degree)).toNat =
        hilbertLength degree :=
    mappedLexicographicInitialIdealIteration_degreeLength_toNat
      ordinaryDegree multiDegree hpositive J Q hQ hJordinary hJlength
  obtain ⟨D, hD⟩ :=
    G.exists_uniform_generatedInPolynomialWindow
      monomialOrder coefficientIdeal hpositive he hilbertLength
  have hNgen : ∀ j,
      G.IsGeneratedInPolynomialWindow hpositive (D : ℤ) (N j) := fun j =>
    hD (N j) (hNordinary j) (hNlength j)
  have hJNgen : ∀ j,
      G.IsGeneratedInPolynomialWindow hpositive (D : ℤ) (JN j) := fun j =>
    hD (JN j) (hJNordinary j) (hJNlength j)
  let A := G.windowOrderedWeightConjugate hpositive (D : ℤ) Jmodule
    (hJwindow (D : ℤ))
  have hAtri : ∀ i (v : G.orderedWeightPiece B hpositive (D : ℤ) i),
      A (Pi.single i v) = Pi.single i v +
        finiteWeightPrefixProjection B
          (n := G.weightCount hpositive (D : ℤ))
          (fun i : Fin (G.weightCount hpositive (D : ℤ)) =>
            G.orderedWeightPiece B hpositive (D : ℤ) i) i.val
          (A (Pi.single i v)) :=
    G.windowOrderedWeightConjugate_triangular hpositive (D : ℤ)
      Jmodule (hJwindow (D : ℤ)) (hJtriangular (D : ℤ))
  have hJpartIteration : ∀ j,
      G.polynomialWindowOrderedWeightPart hpositive (D : ℤ) (JN j) =
        (G.polynomialWindowOrderedWeightPart hpositive (D : ℤ) (N j)).map
          A.toLinearMap := fun j =>
    hJpart (D : ℤ)
      (lexicographicInitialIdealIteration multiDegree J Q j)
  exact exists_lexicographicInitialIdealIteration_stabilizes_of_window_data
    0 ordinaryDegree multiDegree hpositive (D : ℤ) J Q A hAtri
      hQ hJordinary hNgen hJNgen hJpartIteration

end AbelFormalization
