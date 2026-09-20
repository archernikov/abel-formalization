import AbelFormalization.HermiteBeforeRankEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace AbelFormalization

open Filter Set
open scoped Topology ContDiff

variable {ι : Type*}

theorem test_exists_hermiteRankElimination
    {A : ℝ → ℝ} {m p a : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (R X B K K0 : ℝ) (Fbranch : ℂ → ℂ)
    (hFbranch : AnalyticOnNhd ℂ Fbranch (rightHalfStrip X (B + 2)))
    (hB : 0 < B)
    (H : AbelHermiteFamilySpec A B (paperRankHermiteNodeMultiplicity S)
      X K K0 (fun _ => Fbranch))
    (hbound : ∀ w ∈ D.closedBox, ∀ j : Fin S.card,
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) w| ≤ B)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (Q : Fin (m + p + a) → MvPolynomial (PaperRankSymbols m a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hQ : ∀ i, restrictedPaperPolynomialValue A D representative offset
      (restrictedJetEnumeration S) (Q i) = F i) :
    ∃ I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p)),
    ((m + p : ℕ) : ℕ∞) ≤ I.height := by
  let jetPolynomial := paperRankHermiteJetPolynomial D representative offset S
    (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
  let QH : Fin (m + p + a) → MvPolynomial
      (PaperRankSymbols m a
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RestrictedBox.analyticNearClosedBoxSubalgebra D) :=
    fun i => hermiteBeforeRankPolynomialHom
      D.analyticNearClosedBoxSubalgebra jetPolynomial (Q i)
  let C := restrictedPolynomialFamilyCoefficients QH
  have hC : ∀ i d, d ∈ (QH i).support → (QH i).coeff d ∈ C := by
    intro i d hd
    exact coeff_mem_restrictedPolynomialFamilyCoefficients QH i d hd
  obtain ⟨W₀, hWopen, h0W, hcoeff, hpoly⟩ :=
    exists_restrictedPaperCoefficientNeighborhood D h0D QH C hC
  let R' := max R (X + B + 3)
  let Ω : Set (PaperRankSource m p a) :=
    restrictedBaseOpenDomain D R' ∩ {y | y.1.2 ∈ W₀}
  have hΩopen : IsOpen Ω := by
    exact (isOpen_restrictedBaseOpenDomain D R').inter
      (hWopen.preimage (continuous_snd.comp continuous_fst))
  have hΩbase : Ω ⊆ restrictedBaseOpenDomain D R := by
    intro y hy
    refine ⟨?_, hy.1.2⟩
    intro i
    exact lt_of_le_of_lt (le_max_left R (X + B + 3)) (hy.1.1 i)
  have hΩbox : ∀ y ∈ Ω, y.1.2 ∈ D.closedBox := by
    intro y hy
    exact (restrictedBaseOpenDomain_subset_closedDomain D R' hy.1).2
  have hΩcenter : ∀ y ∈ Ω, ∀ i, X + B + 3 < y.1.1 i := by
    intro y hy i
    exact lt_of_le_of_lt (le_max_right R (X + B + 3)) (hy.1.1 i)
  have hV : ContDiffOn ℝ ∞
      (paperRankFullHermiteSmoothValue D representative offset S B Fbranch)
      (Prod.fst '' Ω) := by
    exact paperRankFullHermiteSmoothValue_contDiffOn (A := A)
      D representative offset S hB
      hFbranch hbound Ω hΩopen hΩbox hΩcenter
  have hQH_eval : ∀ i y, y ∈ Ω →
      MvPolynomial.eval₂Hom
        (subalgebraPointEval D.analyticNearClosedBoxSubalgebra y.1.2)
        (paperRankSymbolArgument
          (paperRankFullHermiteSmoothValue D representative offset S B Fbranch) y)
        (QH i) = F i y := by
    intro i y hy
    have hybox := hΩbox y hy
    have hycenter : ∀ k, X < y.1.1 k := by
      intro k
      linarith [hΩcenter y hy k, hB]
    have hEval := eval₂Hom_hermiteBeforeRankPolynomialHom_at_source
      D h0D representative offset S H hB y hybox hycenter (hbound y.1.2 hybox)
      (Q i)
    change MvPolynomial.eval₂Hom
      (subalgebraPointEval D.analyticNearClosedBoxSubalgebra y.1.2)
      (paperRankSymbolArgument
        (paperRankFullHermiteSmoothValue D representative offset S B Fbranch) y)
      (hermiteBeforeRankPolynomialHom
        D.analyticNearClosedBoxSubalgebra jetPolynomial (Q i)) = F i y
    rw [show jetPolynomial = paperRankHermiteJetPolynomial D representative offset S
      (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m) by rfl]
    rw [hEval]
    simpa [paperRankSymbolArgument, restrictedPaperPolynomialValue] using
      (congrFun (hQ i) y)
  let V := paperRankFullHermiteSmoothValue D representative offset S B Fbranch
  have hΩW₀ : ∀ y ∈ Ω, y.1.2 ∈ W₀ := by intro y hy; exact hy.2
  have hrep : ∀ i d (hd : d ∈ (restrictedPaperGermPolynomial D h0D (QH i)).support),
      (restrictedPaperGermPolynomial D h0D (QH i)).coeff d =
        analyticGermOf (restrictedPaperCoefficientRepresentative QH i d)
          (hcoeff i d hd 0 h0W) := by
    intro i d hd
    exact restrictedPaperGermPolynomial_coeff_representation D h0D QH i d
  obtain ⟨I, c, g, G, W, hI, hheight, hspan, hWopen, h0W', hWW₀,
      hsupport, hanalytic, hG, hvanish⟩ :=
    exists_paperRankElimination m p a
      (m * (paperRankHermitePositiveDerivativeCount S + 1))
      (fun i => restrictedPaperGermPolynomial D h0D (QH i))
      (restrictedPaperCoefficientRepresentative QH)
      W₀ hWopen h0W hcoeff hrep Ω hΩopen hΩW₀ V
      (by simpa [V] using hV)
  exact ⟨I, hheight⟩

end AbelFormalization
