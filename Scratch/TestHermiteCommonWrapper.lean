import AbelFormalization.HermiteBeforeRankEquation

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

variable {ι : Type*}

theorem IsAbel.test_exists_restrictedBaseHermiteBeforeRankElimination_height
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
  obtain ⟨S, Q, C, hC, hQ⟩ :=
    exists_restrictedPaperPolynomialFamilyValue_eq_of_mem_base
      A D representative offset F hF
  obtain ⟨B, hB, hbound⟩ :=
    exists_paperRankHermiteOffsetBound D offset S
  obtain ⟨Xstrip, K, K0, Fbranch, hXstrip, hFbranch, hreal, H⟩ :=
    hA.exists_commonStrip_abelHermiteFamily
      (ι := Option (Fin S.card)) hB
      (paperRankHermiteNodeMultiplicity S)
      (paperRankHermiteCoefficientCount_pos S)
  obtain ⟨I, hheight⟩ := exists_hermiteBeforeRankElimination_height
    D h0D representative offset S R Xstrip (Xstrip + B + 3) B K K0
      Fbranch hFbranch hB H hbound Q F hQ
  exact ⟨S, Q, I, hQ, hheight⟩

end AbelFormalization
