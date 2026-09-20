import AbelFormalization.HermiteBeforeRankPolynomialSubstitution
import AbelFormalization.RestrictedBasePaperRankElimination

/-!
# Coefficients after Hermite-before-rank substitution

This scratch file records the finite coefficient bookkeeping needed to apply
`exists_restrictedPaperCoefficientNeighborhood` after replacing the selected
jet variables by their Hermite polynomials.
-/

noncomputable section
set_option autoImplicit false

open Set

namespace AbelFormalization

universe u v

/-- Currying with an empty active family commutes with a change of scalar
coefficients. -/
theorem map_emptyActiveSplitCurryHom
    {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (c : R →+* S) (m order : ℕ)
    (P : MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ order) (fun _ ↦ order)) R) :
    MvPolynomial.map c (emptyActiveSplitCurryHom R m order P) =
      emptyActiveSplitCurryHom S m order (MvPolynomial.map c P) := by
  let lhs : MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ order) (fun _ ↦ order)) R →+*
      MvPolynomial (ClusterOperationSymbol (Fin m) (fun _ ↦ order)) S :=
    (MvPolynomial.map c).comp (emptyActiveSplitCurryHom R m order).toRingHom
  let rhs : MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ order) (fun _ ↦ order)) R →+*
      MvPolynomial (ClusterOperationSymbol (Fin m) (fun _ ↦ order)) S :=
    (emptyActiveSplitCurryHom S m order).toRingHom.comp (MvPolynomial.map c)
  change lhs P = rhs P
  apply DFunLike.congr_fun _ P
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [lhs, rhs, emptyActiveSplitCurryHom]
  · intro z
    rcases z with ((i | j) | (⟨i | j, k⟩ | (i | j)))
    all_goals
      first | exact Fin.elim0 i | simp [lhs, rhs, emptyActiveSplitCurryHom,
        splitClusterCurryAlgEquiv, splitClusterBlockSymbolEquiv]

/-- Apply one Hermite-before-rank substitution pointwise to a finite family. -/
def hermiteBeforeRankPolynomialFamily
    (R : Type u) [CommSemiring R]
    {n a m b order : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ order) (fun _ ↦ order)) R)
    (Q : Fin n → MvPolynomial (PaperRankSymbols m a b) R) :
    Fin n → MvPolynomial
      (PaperRankSymbols m a (m * (order + 1))) R :=
  fun i ↦ hermiteBeforeRankPolynomialHom R jetPolynomial (Q i)

/-- The canonical finite set of coefficients used by the transformed family. -/
def hermiteBeforeRankPolynomialFamilyCoefficients
    (R : Type u) [CommSemiring R]
    {n a m b order : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ order) (fun _ ↦ order)) R)
    (Q : Fin n → MvPolynomial (PaperRankSymbols m a b) R) : Finset R :=
  restrictedPolynomialFamilyCoefficients
    (hermiteBeforeRankPolynomialFamily R jetPolynomial Q)

theorem coeff_mem_hermiteBeforeRankPolynomialFamilyCoefficients
    (R : Type u) [CommSemiring R]
    {n a m b order : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ order) (fun _ ↦ order)) R)
    (Q : Fin n → MvPolynomial (PaperRankSymbols m a b) R)
    (i : Fin n)
    (d : PaperRankSymbols m a (m * (order + 1)) →₀ ℕ)
    (hd : d ∈ (hermiteBeforeRankPolynomialFamily R jetPolynomial Q i).support) :
    (hermiteBeforeRankPolynomialFamily R jetPolynomial Q i).coeff d ∈
      hermiteBeforeRankPolynomialFamilyCoefficients R jetPolynomial Q := by
  exact coeff_mem_restrictedPolynomialFamilyCoefficients
    (hermiteBeforeRankPolynomialFamily R jetPolynomial Q) i d hd

/-- A finite coefficient set containing every supported coefficient of the
Hermite-before-rank transform exists without any extra hypothesis. -/
theorem exists_hermiteBeforeRankPolynomialFamilyCoefficientFinset
    (R : Type u) [CommSemiring R]
    {n a m b order : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ order) (fun _ ↦ order)) R)
    (Q : Fin n → MvPolynomial (PaperRankSymbols m a b) R) :
    ∃ C' : Finset R,
      ∀ i d,
        d ∈ (hermiteBeforeRankPolynomialFamily R jetPolynomial Q i).support →
        (hermiteBeforeRankPolynomialFamily R jetPolynomial Q i).coeff d ∈ C' := by
  exact ⟨hermiteBeforeRankPolynomialFamilyCoefficients R jetPolynomial Q,
    coeff_mem_hermiteBeforeRankPolynomialFamilyCoefficients R jetPolynomial Q⟩

/-- The transformed restricted polynomial family satisfies the common
coefficient-neighborhood conclusion used by paper-rank elimination. -/
theorem exists_hermiteBeforeRankPolynomialCoefficientNeighborhood
    {p n a m b order : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ order) (fun _ ↦ order))
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (Q : Fin n → MvPolynomial (PaperRankSymbols m a b)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    ∃ W₀ : Set (RestrictedBoxSpace p),
      IsOpen W₀ ∧ (0 : RestrictedBoxSpace p) ∈ W₀ ∧
      (∀ i d,
        d ∈ (restrictedPaperGermPolynomial D h0D
          (hermiteBeforeRankPolynomialFamily
            (RestrictedBox.analyticNearClosedBoxSubalgebra D)
            jetPolynomial Q i)).support →
        AnalyticOnNhd ℝ
          (restrictedPaperCoefficientRepresentative
            (hermiteBeforeRankPolynomialFamily
              (RestrictedBox.analyticNearClosedBoxSubalgebra D)
              jetPolynomial Q) i d) W₀) ∧
      ∀ i w, w ∈ W₀ →
        restrictedPaperRealPolynomial D
            (hermiteBeforeRankPolynomialFamily
              (RestrictedBox.analyticNearClosedBoxSubalgebra D)
              jetPolynomial Q i) w =
          polynomialFromCoefficientRepresentatives
            (restrictedPaperGermPolynomial D h0D
              (hermiteBeforeRankPolynomialFamily
                (RestrictedBox.analyticNearClosedBoxSubalgebra D)
                jetPolynomial Q i)).support
            (restrictedPaperCoefficientRepresentative
              (hermiteBeforeRankPolynomialFamily
                (RestrictedBox.analyticNearClosedBoxSubalgebra D)
                jetPolynomial Q) i) w := by
  exact exists_restrictedPaperCoefficientNeighborhood D h0D
    (hermiteBeforeRankPolynomialFamily
      (RestrictedBox.analyticNearClosedBoxSubalgebra D) jetPolynomial Q)
    (hermiteBeforeRankPolynomialFamilyCoefficients
      (RestrictedBox.analyticNearClosedBoxSubalgebra D) jetPolynomial Q)
    (coeff_mem_hermiteBeforeRankPolynomialFamilyCoefficients
      (RestrictedBox.analyticNearClosedBoxSubalgebra D) jetPolynomial Q)

end AbelFormalization
