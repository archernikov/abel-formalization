import AbelFormalization.PaperRankFullHermiteValue
import AbelFormalization.RestrictedBasePaperRankElimination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace AbelFormalization

open Filter Set
open scoped Topology ContDiff

variable {ι : Type*}

theorem test_eval₂Hom_hermiteBeforeRankPolynomialHom_at_source
    {A : ℝ → ℝ} {m p a : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    {B X K K0 : ℝ} {F : ℂ → ℂ}
    (H : AbelHermiteFamilySpec A B (paperRankHermiteNodeMultiplicity S)
      X K K0 (fun _ => F))
    (hB : 0 < B)
    (x : PaperRankSource m p a)
    (hxbox : x.1.2 ∈ D.closedBox)
    (hxcenter : ∀ i, X < x.1.1 i)
    (hoffset : ∀ j : Fin S.card,
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) x.1.2| ≤ B)
    (P : MvPolynomial (PaperRankSymbols m a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    MvPolynomial.eval₂Hom
        (subalgebraPointEval D.analyticNearClosedBoxSubalgebra x.1.2)
        (paperRankSymbolArgument
          (paperRankFullHermiteSmoothValue D representative offset S B F) x)
        (hermiteBeforeRankPolynomialHom
          D.analyticNearClosedBoxSubalgebra
          (paperRankHermiteJetPolynomial D representative offset S
            (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)) P) =
      MvPolynomial.eval₂Hom
        (subalgebraPointEval D.analyticNearClosedBoxSubalgebra x.1.2)
        (paperRankSymbolArgument
          (restrictedSelectedAbelJets A representative offset
            (restrictedJetEnumeration S)) x) P := by
  change MvPolynomial.eval₂Hom
      (subalgebraPointEval D.analyticNearClosedBoxSubalgebra x.1.2)
      (Sum.elim x.2
        (paperRankRetainedArgument
          (paperRankFullHermiteSmoothValue D representative offset S B F) x))
      (hermiteBeforeRankPolynomialHom
        D.analyticNearClosedBoxSubalgebra
        (paperRankHermiteJetPolynomial D representative offset S
          (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)) P) = _
  rw [eval₂Hom_hermiteBeforeRankPolynomialHom]
  have hval :
      Sum.elim x.2 (fun z =>
        MvPolynomial.eval₂Hom
          (subalgebraPointEval D.analyticNearClosedBoxSubalgebra x.1.2)
          (paperRankRetainedArgument
            (paperRankFullHermiteSmoothValue D representative offset S B F) x)
          ((hermiteBeforeRankRetainedHom
            D.analyticNearClosedBoxSubalgebra
            (paperRankHermiteJetPolynomial D representative offset S
              (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m))
            (MvPolynomial.X z)))) =
        paperRankSymbolArgument
          (restrictedSelectedAbelJets A representative offset
            (restrictedJetEnumeration S)) x := by
    funext z
    cases z with
    | inl i =>
        simp [Sum.elim, hermiteBeforeRankRetainedHom,
          paperRankSymbolArgument]
    | inr z =>
        cases z with
        | inl i =>
            simp only [Sum.elim_inr]
            change MvPolynomial.eval₂Hom
              (subalgebraPointEval D.analyticNearClosedBoxSubalgebra x.1.2)
              (paperRankRetainedArgument
                (paperRankFullHermiteSmoothValue D representative offset S B F) x)
              ((hermiteBeforeRankRetainedHom
                D.analyticNearClosedBoxSubalgebra
                (paperRankHermiteJetPolynomial D representative offset S
                  (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m))
                (MvPolynomial.X (Sum.inl i)))) = x.1.1 i
            rw [hermiteBeforeRankRetainedHom_apply_X_free]
            simp [paperRankRetainedArgument]
        | inr j =>
            simp only [Sum.elim_inr]
            rw [show paperRankRetainedArgument
                (paperRankFullHermiteSmoothValue D representative offset S B F) x =
              paperRankFullHermiteRetainedValue D representative offset S B F x.1 by
                exact paperRankRetainedArgument_fullHermiteSmoothValue
                  D representative offset S B F x]
            change MvPolynomial.eval₂Hom
              (subalgebraPointEval D.analyticNearClosedBoxSubalgebra x.1.2)
              (paperRankFullHermiteRetainedValue D representative offset S B F x.1)
              ((hermiteBeforeRankRetainedHom
                D.analyticNearClosedBoxSubalgebra
                (paperRankHermiteJetPolynomial D representative offset S
                  (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m))
                (MvPolynomial.X (Sum.inr j)))) =
              (restrictedSelectedAbelJets A representative offset
                (restrictedJetEnumeration S) x.1 j)
            simpa [MvPolynomial.eval₂Hom_X, Sum.elim, paperRankSymbolArgument] using
              (eval₂Hom_hermiteBeforeRankRetainedHom_fullHermiteValue
                D representative offset S H hB x.1 hxcenter hoffset
                (MvPolynomial.X (Sum.inr j)))
  rw [hval]

theorem test_paperRankEquation_from_eval
    {A : ℝ → ℝ} {m p a : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (S : Finset (ι × ℕ))
    (QH : Fin (m + p + a) → MvPolynomial
      (PaperRankSymbols m a (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (F : Fin (m + p + a) → PaperRankSource m p a → ℝ)
    (V : PaperRankParameterSpace m p →
      PaperRankRealSpace (m * (paperRankHermitePositiveDerivativeCount S + 1)))
    (hQH : ∀ i x, MvPolynomial.eval₂Hom
      (subalgebraPointEval D.analyticNearClosedBoxSubalgebra x.1.2)
      (paperRankSymbolArgument V x) (QH i) = F i x)
    (W₀ : Set (RestrictedBoxSpace p))
    (hpoly : ∀ i w, w ∈ W₀ →
      restrictedPaperRealPolynomial D (QH i) w =
        polynomialFromCoefficientRepresentatives
          (restrictedPaperGermPolynomial D h0D (QH i)).support
          (restrictedPaperCoefficientRepresentative QH i) w)
    (x : PaperRankSource m p a) (hxW : x.1.2 ∈ W₀) :
    paperRankEquation (fun i => restrictedPaperGermPolynomial D h0D (QH i))
        (restrictedPaperCoefficientRepresentative QH) V x =
      constraintMap F x := by
  funext i
  change MvPolynomial.eval
      (paperRankSymbolArgument V x)
      (polynomialFromCoefficientRepresentatives
        (restrictedPaperGermPolynomial D h0D (QH i)).support
        (restrictedPaperCoefficientRepresentative QH i) x.1.2) = F i x
  rw [← hpoly i x.1.2 hxW]
  rw [restrictedPaperRealPolynomial]
  rw [← MvPolynomial.eval₂_eq_eval_map]
  exact hQH i x

end AbelFormalization
