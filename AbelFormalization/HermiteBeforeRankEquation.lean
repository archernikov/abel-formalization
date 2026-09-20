import AbelFormalization.PaperRankFullHermiteValue
import AbelFormalization.RestrictedBasePaperRankElimination
import AbelFormalization.CommonStripAbelHermiteFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace AbelFormalization

open Filter Set
open scoped Topology ContDiff

variable {ι : Type*}

/-- Evaluation of the complete Hermite-before-rank substitution at a source
point is evaluation of the original polynomial at the selected Abel jets. -/
theorem eval₂Hom_hermiteBeforeRankPolynomialHom_at_source
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
    (_hxbox : x.1.2 ∈ D.closedBox)
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
        simp [Sum.elim, paperRankSymbolArgument]
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

/-- The rank equation built from transformed Hermite polynomials agrees with
the original compressed system wherever the coefficient representatives are
valid. -/
theorem paperRankEquation_from_eval
    {m p a : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (S : Finset (ι × ℕ))
    (QH : Fin (m + p + a) → MvPolynomial
      (PaperRankSymbols m a
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
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

/-- Height output of rank elimination after substituting the complete Hermite
coordinate family.  This is the corrected rank-side wrapper: the equation
system is first transformed, then its coefficient germs are eliminated on a
common coefficient neighborhood. -/
theorem exists_hermiteBeforeRankElimination_height
    {A : ℝ → ℝ} {m p a : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (R Xstrip X0 B K K0 : ℝ) (Fbranch : ℂ → ℂ)
    (hFbranch : AnalyticOnNhd ℂ Fbranch
      (rightHalfStrip Xstrip (B + 2)))
    (hB : 0 < B)
    (H : AbelHermiteFamilySpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 (fun _ => Fbranch))
    (hbound : ∀ w ∈ D.closedBox, ∀ j : Fin S.card,
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) w| ≤ B)
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
  let R' := max R (max X0 (Xstrip + B + 3))
  let Ω : Set (PaperRankSource m p a) :=
    restrictedBaseOpenDomain D R' ∩ {y | y.1.2 ∈ W₀}
  have hΩopen : IsOpen Ω := by
    exact (isOpen_restrictedBaseOpenDomain D R').inter
      (hWopen.preimage (continuous_snd.comp continuous_fst))
  have hΩbox : ∀ y ∈ Ω, y.1.2 ∈ D.closedBox := by
    intro y hy
    exact (restrictedBaseOpenDomain_subset_closedDomain D R' hy.1).2
  have hΩcenter : ∀ y ∈ Ω, ∀ i,
      max X0 (Xstrip + B + 3) < y.1.1 i := by
    intro y hy i
    exact lt_of_le_of_lt
      (le_max_right R (max X0 (Xstrip + B + 3))) (hy.1.1 i)
  have hV : ContDiffOn ℝ ∞
      (paperRankFullHermiteSmoothValue D representative offset S B Fbranch)
      (Prod.fst '' Ω) := by
    exact paperRankFullHermiteSmoothValue_contDiffOn (A := A)
      D representative offset S hB hFbranch hbound Ω hΩopen hΩbox
      (fun y hy i =>
        (le_max_right X0 (Xstrip + B + 3)).trans_lt (hΩcenter y hy i))
  have hQH_eval : ∀ i y, y ∈ Ω →
      MvPolynomial.eval₂Hom
        (subalgebraPointEval D.analyticNearClosedBoxSubalgebra y.1.2)
        (paperRankSymbolArgument
          (paperRankFullHermiteSmoothValue D representative offset S B Fbranch) y)
        (QH i) = F i y := by
    intro i y hy
    have hybox := hΩbox y hy
    have hycenter : ∀ k, X0 < y.1.1 k := by
      intro k
      exact (le_max_left X0 (Xstrip + B + 3)).trans_lt
        (hΩcenter y hy k)
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
  have hΩW₀ : ∀ y ∈ Ω, y.1.2 ∈ W₀ := by
    intro y hy
    exact hy.2
  have hrep : ∀ i d
      (hd : d ∈ (restrictedPaperGermPolynomial D h0D (QH i)).support),
      (restrictedPaperGermPolynomial D h0D (QH i)).coeff d =
        analyticGermOf (restrictedPaperCoefficientRepresentative QH i d)
          (hcoeff i d hd 0 h0W) := by
    intro i d hd
    exact restrictedPaperGermPolynomial_coeff_representation D h0D QH i d
  obtain ⟨I, c, g, G, W, hI, hheight, hspan, hWopen', h0W', hWW₀,
      hsupport, hanalytic, hG, hvanish⟩ :=
    exists_paperRankElimination m p a
      (m * (paperRankHermitePositiveDerivativeCount S + 1))
      (fun i => restrictedPaperGermPolynomial D h0D (QH i))
      (restrictedPaperCoefficientRepresentative QH)
      W₀ hWopen h0W hcoeff hrep Ω hΩopen hΩW₀ V
      (by simpa [V] using hV)
  exact ⟨I, hheight⟩

/-- A finite restricted expression system has a full-Hermite retained ideal
of height at least `m + p`.  The finite jet list, its polynomial compression,
the uniform offset bound, and one common complex strip are all chosen from the
given data and `IsAbel`; no Hermite or rank-elimination input remains as an
extra hypothesis. -/
theorem IsAbel.exists_restrictedBaseHermiteBeforeRankElimination_height
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (R : ℝ)
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hF : ∀ i, F i ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)) :
    ∃ S : Finset (ι × ℕ),
    ∃ Q : Fin (m + p + a) →
        MvPolynomial (PaperRankSymbols m a S.card)
          (RestrictedBox.analyticNearClosedBoxSubalgebra D),
    ∃ I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p)),
      (∀ i, restrictedPaperPolynomialValue A D representative offset
        (restrictedJetEnumeration S) (Q i) = F i) ∧
      ((m + p : ℕ) : ℕ∞) ≤ I.height := by
  obtain ⟨S, Q, _C, _hC, hQ⟩ :=
    exists_restrictedPaperPolynomialFamilyValue_eq_of_mem_base
      A D representative offset F hF
  obtain ⟨B, hB, hbound⟩ :=
    exists_paperRankHermiteOffsetBound D offset S
  obtain ⟨Xstrip, K, K0, Fbranch, _hXstrip, hFbranch, _hreal, H⟩ :=
    hA.exists_commonStrip_abelHermiteFamily
      (ι := Option (Fin S.card)) hB
      (paperRankHermiteNodeMultiplicity S)
      (paperRankHermiteCoefficientCount_pos S)
  obtain ⟨I, hheight⟩ := exists_hermiteBeforeRankElimination_height
    D h0D representative offset S R Xstrip (Xstrip + B + 3) B K K0
      Fbranch hFbranch hB H hbound Q F hQ
  exact ⟨S, Q, I, hQ, hheight⟩

end AbelFormalization
