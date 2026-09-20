import AbelFormalization.PolynomialWindowNoetherianDescent

set_option autoImplicit false

/-!
# Lifting bounded-window descent to polynomial submodules

This file isolates the formal bridge needed after identifying the bounded
part of a polynomial initial operation with finite-weight initial formation.
If a sequence of polynomial submodules is generated in one common ordinary
degree window and its bounded parts follow the finite-weight recurrence, then
finite-product stabilization determines the full sequence.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n r h : ℕ}
variable (G : PolynomialGradedLexData n r h)

/-- Equality of transported bounded parts determines two polynomial
submodules generated in the same window. -/
theorem PolynomialGradedLexData.eq_of_polynomialWindowOrderedWeightPart_eq
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (N N' : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (hN : G.IsGeneratedInPolynomialWindow hpositive D N)
    (hN' : G.IsGeneratedInPolynomialWindow hpositive D N')
    (hpart : G.polynomialWindowOrderedWeightPart hpositive D N =
      G.polynomialWindowOrderedWeightPart hpositive D N') :
    N = N' := by
  apply G.eq_of_polynomialWindowPart_eq hpositive D N N' hN hN'
  exact Submodule.map_injective_of_injective
    (G.windowOrderedWeightLinearEquiv (B := B) hpositive D).injective hpart

/-- A common bounded generation window turns finite-weight stabilization of
the transported window parts into stabilization of the actual polynomial
submodules.  `JN j` records the polynomial submodule obtained by applying the
semilinear polynomial automorphism to `N j`; the two displayed compatibility
hypotheses are exactly what the concrete initial operation must supply. -/
theorem PolynomialGradedLexData.exists_polynomialSubmodule_stabilizes_of_window_recurrence
    (d : ℕ) [IsNoetherianRing B] [Ring.KrullDimLE d B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (A :
      ((i : Fin (G.weightCount hpositive D)) →
          G.orderedWeightPiece B hpositive D i) ≃ₗ[B]
        ((i : Fin (G.weightCount hpositive D)) →
          G.orderedWeightPiece B hpositive D i))
    (htri : ∀ i (v : G.orderedWeightPiece B hpositive D i),
      A (Pi.single i v) = Pi.single i v +
        finiteWeightPrefixProjection B
          (n := G.weightCount hpositive D)
          (fun i : Fin (G.weightCount hpositive D) =>
            G.orderedWeightPiece B hpositive D i) i.val
          (A (Pi.single i v)))
    (N JN : ℕ → Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (hNhom : ∀ j, G.IsPolynomialModuleWeightHomogeneous (N j))
    (hNgen : ∀ j, G.IsGeneratedInPolynomialWindow hpositive D (N j))
    (hJNgen : ∀ j, G.IsGeneratedInPolynomialWindow hpositive D (JN j))
    (hJpart : ∀ j,
      G.polynomialWindowOrderedWeightPart hpositive D (JN j) =
        (G.polynomialWindowOrderedWeightPart hpositive D (N j)).map
          A.toLinearMap)
    (hstep : ∀ j,
      G.polynomialWindowOrderedWeightPart hpositive D (N (j + 1)) =
        finiteWeightDescentStep A
          (G.polynomialWindowOrderedWeightPart hpositive D (N j))) :
    ∃ j₀ : ℕ, JN j₀ = N j₀ ∧
      ∀ j, j₀ ≤ j → N j = N j₀ := by
  let U₀ := G.polynomialWindowOrderedWeightPart hpositive D (N 0)
  have hU₀ : ∀ x ∈ U₀, ∀ i, Pi.single i (x i) ∈ U₀ :=
    G.polynomialWindowOrderedWeightPart_homogeneous
      hpositive D (N 0) (hNhom 0)
  obtain ⟨j₀, hinv, hpermanent⟩ :=
    G.exists_windowOrderedWeightDescent_stabilizes_of_krullDimLE
      d hpositive D A htri U₀ hU₀
  have hiterate : ∀ j,
      G.polynomialWindowOrderedWeightPart hpositive D (N j) =
        finiteWeightDescentIterate A U₀ j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
        rw [hstep j, ih]
        rfl
  refine ⟨j₀, ?_, ?_⟩
  · apply G.eq_of_polynomialWindowOrderedWeightPart_eq
      hpositive D (JN j₀) (N j₀) (hJNgen j₀) (hNgen j₀)
    calc
      G.polynomialWindowOrderedWeightPart hpositive D (JN j₀) =
          (G.polynomialWindowOrderedWeightPart hpositive D (N j₀)).map
            A.toLinearMap := hJpart j₀
      _ = (finiteWeightDescentIterate A U₀ j₀).map A.toLinearMap :=
        congrArg (fun U => U.map A.toLinearMap) (hiterate j₀)
      _ = finiteWeightDescentIterate A U₀ j₀ := hinv
      _ = G.polynomialWindowOrderedWeightPart hpositive D (N j₀) :=
        (hiterate j₀).symm
  · intro j hj
    apply G.eq_of_polynomialWindowOrderedWeightPart_eq
      hpositive D (N j) (N j₀) (hNgen j) (hNgen j₀)
    exact (hiterate j).trans ((hpermanent j hj).trans (hiterate j₀).symm)

end AbelFormalization
