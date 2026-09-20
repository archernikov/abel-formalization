import AbelFormalization.FiniteWeightNoetherianDescent
import AbelFormalization.PolynomialWindowDescent

set_option autoImplicit false

/-!
# Noetherian stabilization in a bounded polynomial window

The bounded ordinary-degree window is the finite product of its grouped
lexicographic weight pieces.  Their coordinatewise finiteness lets us apply
the Noetherian finite-weight stabilization theorem over any coefficient ring
with a finite upper bound on Krull dimension.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n r h : ℕ}
variable (G : PolynomialGradedLexData n r h)

/-- Direct specialization of Noetherian finite-weight stabilization to the
ordered grouped pieces of one bounded polynomial window. -/
theorem PolynomialGradedLexData.exists_windowOrderedWeightDescent_stabilizes_of_krullDimLE
    (d : ℕ) [IsNoetherianRing B] [Ring.KrullDimLE d B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J :
      ((i : Fin (G.weightCount hpositive D)) →
          G.orderedWeightPiece B hpositive D i) ≃ₗ[B]
        ((i : Fin (G.weightCount hpositive D)) →
          G.orderedWeightPiece B hpositive D i))
    (htri : ∀ i (v : G.orderedWeightPiece B hpositive D i),
      J (Pi.single i v) = Pi.single i v +
        finiteWeightPrefixProjection B
          (n := G.weightCount hpositive D)
          (fun i : Fin (G.weightCount hpositive D) =>
            G.orderedWeightPiece B hpositive D i) i.val
          (J (Pi.single i v)))
    (N₀ : Submodule B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀) :
    ∃ j₀ : ℕ,
      (finiteWeightDescentIterate J N₀ j₀).map J.toLinearMap =
          finiteWeightDescentIterate J N₀ j₀ ∧
        ∀ j, j₀ ≤ j →
          finiteWeightDescentIterate J N₀ j =
            finiteWeightDescentIterate J N₀ j₀ := by
  let _ : ∀ i : Fin (G.weightCount hpositive D),
      Module.Finite B (G.orderedWeightPiece B hpositive D i) :=
    fun i => G.orderedWeightPiece_moduleFinite
      (B := B) hpositive D i
  exact exists_finiteWeightDescent_stabilizes_of_krullDimLE
    (R := B)
    (n := G.weightCount hpositive D)
    (M := fun i : Fin (G.weightCount hpositive D) =>
      G.orderedWeightPiece B hpositive D i)
    d J htri N₀ hN₀

/-- A polynomial automorphism which preserves the bounded window and is
strictly triangular in lexicographic weight has a stable finite-weight
iterate on the transported bounded part of every weight-homogeneous
polynomial submodule. -/
theorem PolynomialGradedLexData.exists_polynomialWindowOrderedWeightDescent_stabilizes_of_krullDimLE
    (d : ℕ) [IsNoetherianRing B] [Ring.KrullDimLE d B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r)
    (hJ : (G.windowModule B hpositive D).map J.toLinearMap =
      G.windowModule B hpositive D)
    (htri : G.IsWindowWeightTriangular hpositive D J)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (hN : G.IsPolynomialModuleWeightHomogeneous N) :
    ∃ j₀ : ℕ,
      (finiteWeightDescentIterate
          (G.windowOrderedWeightConjugate hpositive D J hJ)
          (G.polynomialWindowOrderedWeightPart hpositive D N) j₀).map
          (G.windowOrderedWeightConjugate hpositive D J hJ).toLinearMap =
        finiteWeightDescentIterate
          (G.windowOrderedWeightConjugate hpositive D J hJ)
          (G.polynomialWindowOrderedWeightPart hpositive D N) j₀ ∧
      ∀ j, j₀ ≤ j →
        finiteWeightDescentIterate
          (G.windowOrderedWeightConjugate hpositive D J hJ)
          (G.polynomialWindowOrderedWeightPart hpositive D N) j =
        finiteWeightDescentIterate
          (G.windowOrderedWeightConjugate hpositive D J hJ)
          (G.polynomialWindowOrderedWeightPart hpositive D N) j₀ := by
  exact G.exists_windowOrderedWeightDescent_stabilizes_of_krullDimLE
    d hpositive D
    (G.windowOrderedWeightConjugate hpositive D J hJ)
    (G.windowOrderedWeightConjugate_triangular hpositive D J hJ htri)
    (G.polynomialWindowOrderedWeightPart hpositive D N)
    (G.polynomialWindowOrderedWeightPart_homogeneous hpositive D N hN)

end AbelFormalization
