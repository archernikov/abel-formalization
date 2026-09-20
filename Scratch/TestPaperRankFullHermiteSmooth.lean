import AbelFormalization.PaperRankFullHermiteValue

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace AbelFormalization

open _root_.Set
open scoped Topology ContDiff

variable {ι : Type*}

theorem test_paperRankFullHermiteSmoothValue_contDiffOn
    {A : ℝ → ℝ} {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    {B X : ℝ} {F : ℂ → ℂ}
    (hB : 0 < B)
    (hF : AnalyticOnNhd ℂ F (rightHalfStrip X (B + 2)))
    (hoffset : ∀ w ∈ D.closedBox, ∀ j : Fin S.card,
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) w| ≤ B)
    (Ω : Set (PaperRankSource m p a))
    (hΩ : IsOpen Ω)
    (hΩbox : ∀ x ∈ Ω, x.1.2 ∈ D.closedBox)
    (hΩcenter : ∀ x ∈ Ω, ∀ i, X + B + 3 < x.1.1 i) :
    ContDiffOn ℝ ∞
      (paperRankFullHermiteSmoothValue D representative offset S B F)
      (Prod.fst '' Ω) := by
  rw [contDiffOn_pi]
  intro j
  have hanalytic : AnalyticOnNhd ℝ
      (fun sw => paperRankFullHermiteSmoothValue D representative offset S B F sw j)
      (Prod.fst '' Ω) := by
    rintro _ ⟨x, hx, rfl⟩
    have hswbox : x.1.2 ∈ D.closedBox := hΩbox x hx
    have hswcenter : ∀ i, X + B + 3 < x.1.1 i := hΩcenter x hx
    have hret := analyticAt_paperRankFullHermiteCoefficientBlockValue
      D representative offset S hB hF x.1 hswcenter hswbox
      (fun k => hoffset x.1.2 hswbox k)
      (paperRankRetainedFlatHermiteEquiv m
        (paperRankHermitePositiveDerivativeCount S) (Sum.inr j))
    change AnalyticAt ℝ
      (fun sw => paperRankFullHermiteRetainedValue D representative offset S B F sw
        (Sum.inr j)) x.1
    exact hret
  exact (hanalytic.contDiffOn_of_completeSpace)

end AbelFormalization
