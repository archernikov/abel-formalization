import AbelFormalization.HermiteBeforeRankSequence
import AbelFormalization.RestrictedBoxTranslation

/-!
# Hermite-before-rank elimination at an arbitrary bounded limit

This module translates an arbitrary bounded-coordinate limit to zero and
then applies the zero-centered Hermite-before-rank sequence theorem.  Its
output is deliberately stated in the translated coordinates: the germ ring
is `RealAnalyticGerm p`, hence is based at zero, while evaluation at a
translated coordinate `w` represents evaluation at `w + w₀` in the original
box.
-/

noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false
set_option maxHeartbeats 600000

variable {ι : Type*}

/-- Translate the analytic coefficients of a paper polynomial to the box
centered at zero.  Its polynomial symbols are unchanged. -/
def restrictedPaperPolynomialTranslateToZero
    {m p a b : ℕ} (D : RestrictedBox p) (w₀ : RestrictedBoxSpace p)
    (P : MvPolynomial (PaperRankSymbols m a b)
      D.analyticNearClosedBoxSubalgebra) :
    MvPolynomial (PaperRankSymbols m a b)
      (D.translateToZero w₀).analyticNearClosedBoxSubalgebra :=
  MvPolynomial.map (D.translateCoefficientToZeroAlgHom w₀).toRingHom P

/-- The paper symbol valuation with translated offsets is the pullback of the
original valuation along bounded-coordinate translation. -/
theorem paperRankSymbolArgument_translateFromZero
    (A : ℝ → ℝ) {m p a b : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (selected : Fin b → ι × ℕ)
    (w₀ : RestrictedBoxSpace p) (x : RestrictedSource m p a) :
    paperRankSymbolArgument
        (restrictedSelectedAbelJets A representative
          (restrictedOffsetTranslateToZero w₀ offset) selected) x =
      paperRankSymbolArgument
        (restrictedSelectedAbelJets A representative offset selected)
        (restrictedSourceTranslateFromZero w₀ x) := by
  funext z
  rcases z with k | z
  · rfl
  · rcases z with i | j
    · rfl
    · exact restrictedAbelJet_translateFromZero A representative offset w₀
        (selected j).1 (selected j).2 x

/-- Translating a paper polynomial's coefficients and its offsets gives the
pullback of its represented function along bounded-coordinate translation. -/
theorem restrictedPaperPolynomialValue_translateToZero
    (A : ℝ → ℝ) {m p a b : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (selected : Fin b → ι × ℕ)
    (w₀ : RestrictedBoxSpace p)
    (P : MvPolynomial (PaperRankSymbols m a b)
      D.analyticNearClosedBoxSubalgebra) :
    restrictedPaperPolynomialValue A (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) selected
        (restrictedPaperPolynomialTranslateToZero D w₀ P) =
      fun x ↦ restrictedPaperPolynomialValue A D representative offset selected P
        (restrictedSourceTranslateFromZero w₀ x) := by
  funext x
  unfold restrictedPaperPolynomialValue restrictedPaperPolynomialTranslateToZero
  rw [MvPolynomial.eval₂_map]
  rw [subalgebraPointEval_translateCoefficientToZero]
  rw [paperRankSymbolArgument_translateFromZero]
  rfl

/-- Normalize an arbitrary bounded-coordinate limit to zero, transport the
box, offsets, compressed polynomial system, regular zeros, and divergence,
then apply full Hermite substitution followed by rank elimination.

The conclusion is the exact zero-centered package transported from the
original data.  Thus `x₀ n` has bounded coordinate `(x n).1.2 - w₀`, and a
coefficient evaluated at `w` in `D₀` is the original coefficient evaluated at
`w + w₀`. -/
theorem exists_hermiteBeforeRankElimination_at_limit
    {A : ℝ → ℝ} {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (S : Finset (ι × ℕ))
    (R Xstrip X0 B K K0 : ℝ) (Fbranch : ℂ → ℂ)
    (hFbranch : AnalyticOnNhd ℂ Fbranch (rightHalfStrip Xstrip (B + 2)))
    (hB : 0 < B)
    (H : AbelHermiteFamilySpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 (fun _ => Fbranch))
    (hbound : ∀ w ∈ D.closedBox, ∀ j : Fin S.card,
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) w| ≤ B)
    (Q : Fin (m + p + a) → MvPolynomial (PaperRankSymbols m a S.card)
      D.analyticNearClosedBoxSubalgebra)
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hQ : ∀ i, restrictedPaperPolynomialValue A D representative offset
      (restrictedJetEnumeration S) (Q i) = F i)
    (x : ℕ → RestrictedSource m p a)
    (hx : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) (constraintMap F))
    (hxrepresentative : ∀ i,
      Tendsto (fun n => (x n).1.1 i) atTop atTop)
    (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
    (hxlim : Tendsto (fun n => (x n).1.2) atTop (𝓝 w₀)) :
    let D₀ : RestrictedBox p := D.translateToZero w₀
    let h0D₀ : (0 : RestrictedBoxSpace p) ∈ D₀.closedBox :=
      D.zero_mem_closedBox_translateToZero hw₀
    let offset₀ : ι → D₀.analyticNearClosedBoxSubalgebra :=
      restrictedOffsetTranslateToZero w₀ offset
    let Q₀ : Fin (m + p + a) →
        MvPolynomial (PaperRankSymbols m a S.card)
          D₀.analyticNearClosedBoxSubalgebra :=
      fun i => restrictedPaperPolynomialTranslateToZero D w₀ (Q i)
    let x₀ : ℕ → RestrictedSource m p a :=
      fun n => restrictedSourceTranslateToZero w₀ (x n)
    ∃ I : Ideal (MvPolynomial
        (PaperRankRetainedSymbols m
          (m * (paperRankHermitePositiveDerivativeCount S + 1)))
        (RealAnalyticGerm p)),
      ∃ c : ℕ,
      ∃ g : Fin c → MvPolynomial
          (PaperRankRetainedSymbols m
            (m * (paperRankHermitePositiveDerivativeCount S + 1)))
          (RealAnalyticGerm p),
      ∃ G : Fin c → RestrictedBoxSpace p → MvPolynomial
          (PaperRankRetainedSymbols m
            (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ,
      ∃ W : Set (RestrictedBoxSpace p),
        I = jacobianEliminationIdeal a
          (fun i => restrictedPaperGermPolynomial D₀ h0D₀
            (hermiteBeforeRankPolynomialFamily D₀ representative offset₀ S Q₀ i))
          (analyticGermFormalDerivations p) ∧
        ((m + p : ℕ) : ℕ∞) ≤ I.height ∧
        Ideal.span (Set.range g) = I ∧
        IsOpen W ∧ (0 : RestrictedBoxSpace p) ∈ W ∧
        (∀ j w, (G j w).support ⊆ (g j).support) ∧
        (∀ j d, AnalyticOnNhd ℝ (fun w => (G j w).coeff d) W) ∧
        (∀ j, analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (g j) =
          (G j : Germ (𝓝 (0 : RestrictedBoxSpace p))
            (MvPolynomial
              (PaperRankRetainedSymbols m
                (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ))) ∧
        ∀ᶠ n in atTop, ∀ j,
          MvPolynomial.eval
            (paperRankRetainedArgument
              (paperRankFullHermiteSmoothValue
                D₀ representative offset₀ S B Fbranch) (x₀ n))
            (G j (x₀ n).1.2) = 0 := by
  dsimp only
  let D₀ : RestrictedBox p := D.translateToZero w₀
  let h0D₀ : (0 : RestrictedBoxSpace p) ∈ D₀.closedBox :=
    D.zero_mem_closedBox_translateToZero hw₀
  let offset₀ : ι → D₀.analyticNearClosedBoxSubalgebra :=
    restrictedOffsetTranslateToZero w₀ offset
  let Q₀ : Fin (m + p + a) →
      MvPolynomial (PaperRankSymbols m a S.card)
        D₀.analyticNearClosedBoxSubalgebra :=
    fun i => restrictedPaperPolynomialTranslateToZero D w₀ (Q i)
  let F₀ : Fin (m + p + a) → RestrictedSource m p a → ℝ :=
    restrictedEquationFamilyTranslateToZero w₀ F
  let x₀ : ℕ → RestrictedSource m p a :=
    fun n => restrictedSourceTranslateToZero w₀ (x n)
  have hbound₀ : ∀ w ∈ D₀.closedBox, ∀ j : Fin S.card,
      |(offset₀ (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) w| ≤ B := by
    intro w hw j
    have hwOld : RestrictedBox.translateFromZero w₀ w ∈ D.closedBox :=
      (D.mem_closedBox_translateToZero_iff w₀ w).mp hw
    simpa only [D₀, offset₀, restrictedOffsetTranslateToZero,
      RestrictedBox.translateCoefficientToZero_apply,
      RestrictedBox.translateFromZero] using hbound (w + w₀) hwOld j
  have hQ₀ : ∀ i, restrictedPaperPolynomialValue A D₀ representative offset₀
      (restrictedJetEnumeration S) (Q₀ i) = F₀ i := by
    intro i
    funext y
    have htranslate := congrFun
      (restrictedPaperPolynomialValue_translateToZero A D representative offset
        (restrictedJetEnumeration S) w₀ (Q i)) y
    change restrictedPaperPolynomialValue A (D.translateToZero w₀)
        representative (restrictedOffsetTranslateToZero w₀ offset)
          (restrictedJetEnumeration S)
          (restrictedPaperPolynomialTranslateToZero D w₀ (Q i)) y =
      F i (restrictedSourceTranslateFromZero w₀ y)
    exact htranslate.trans (congrFun (hQ i)
      (restrictedSourceTranslateFromZero w₀ y))
  have hx₀ : ∀ n, x₀ n ∈ regularZeroSet
      (restrictedBaseOpenDomain D₀ R) (constraintMap F₀) := by
    intro n
    exact mem_regularZeroSet_restrictedEquationFamilyTranslateToZero
      D R w₀ F (hx n)
  have hxrepresentative₀ : ∀ i,
      Tendsto (fun n => (x₀ n).1.1 i) atTop atTop := by
    intro i
    simpa only [x₀, restrictedSourceTranslateToZero] using hxrepresentative i
  have hxlim₀ : Tendsto (fun n => (x₀ n).1.2) atTop
      (𝓝 (0 : RestrictedBoxSpace p)) :=
    tendsto_restrictedSourceTranslateToZero_box_zero w₀ x hxlim
  exact exists_hermiteBeforeRankElimination_along_divergent_sequence
    D₀ h0D₀ representative offset₀ S R Xstrip X0 B K K0 Fbranch
      hFbranch hB H hbound₀ Q₀ F₀ hQ₀ x₀ hx₀ hxrepresentative₀ hxlim₀

end AbelFormalization
