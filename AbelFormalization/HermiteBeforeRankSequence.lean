import AbelFormalization.HermiteBeforeRankEquation

/-!
# Full Hermite substitution followed by rank elimination along a sequence

This module retains the complete finite-generator output of analytic rank
elimination after the full Hermite coordinate substitution.  The two real
thresholds have distinct roles: `Xstrip` controls the common holomorphic
strip used to construct the smooth retained-coordinate value, while `X0`
is the center threshold in the Hermite interpolation specification.
-/

noncomputable section

open Filter Set
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false
set_option maxHeartbeats 600000

variable {ι : Type*}

/-- The polynomial family obtained by applying the complete
Hermite-before-rank substitution to every equation. -/
def hermiteBeforeRankPolynomialFamily
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (Q : Fin (m + p + a) → MvPolynomial (PaperRankSymbols m a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    Fin (m + p + a) → MvPolynomial
      (PaperRankSymbols m a
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RestrictedBox.analyticNearClosedBoxSubalgebra D) :=
  fun i => hermiteBeforeRankPolynomialHom
    D.analyticNearClosedBoxSubalgebra
    (paperRankHermiteJetPolynomial D representative offset S
      (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m))
    (Q i)

/-- Full analytic rank-elimination output after the complete Hermite
substitution.  Along a sequence of regular zeros whose bounded coordinates
converge to zero, every analytic representative of a finite generating
family for the eliminated ideal vanishes eventually.

The source cutoff simultaneously implies the common-strip bound
`Xstrip + B + 3` and the interpolation-center bound `X0`. -/
theorem exists_hermiteBeforeRankElimination_along_sequence
    {A : ℝ → ℝ} {m p a : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
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
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hQ : ∀ i, restrictedPaperPolynomialValue A D representative offset
      (restrictedJetEnumeration S) (Q i) = F i)
    (x : ℕ → RestrictedSource m p a)
    (hx : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) (constraintMap F))
    (hxlarge : ∀ᶠ n in atTop, ∀ i,
      max X0 (Xstrip + B + 3) < (x n).1.1 i)
    (hxlim : Tendsto (fun n => (x n).1.2) atTop
      (𝓝 (0 : RestrictedBoxSpace p))) :
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
          (fun i => restrictedPaperGermPolynomial D h0D
            (hermiteBeforeRankPolynomialFamily D representative offset S Q i))
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
                D representative offset S B Fbranch) (x n))
            (G j (x n).1.2) = 0 := by
  classical
  let QH := hermiteBeforeRankPolynomialFamily D representative offset S Q
  let C := restrictedPolynomialFamilyCoefficients QH
  have hC : ∀ i d, d ∈ (QH i).support → (QH i).coeff d ∈ C := by
    intro i d hd
    exact coeff_mem_restrictedPolynomialFamilyCoefficients QH i d hd
  obtain ⟨W₀, hW₀open, h0W₀, hcoeff, hpoly⟩ :=
    exists_restrictedPaperCoefficientNeighborhood D h0D QH C hC
  let R' := max R (max X0 (Xstrip + B + 3))
  let Ω : Set (PaperRankSource m p a) :=
    restrictedBaseOpenDomain D R' ∩ {y | y.1.2 ∈ W₀}
  have hΩopen : IsOpen Ω := by
    exact (isOpen_restrictedBaseOpenDomain D R').inter
      (hW₀open.preimage (continuous_snd.comp continuous_fst))
  have hΩbox : ∀ y ∈ Ω, y.1.2 ∈ D.closedBox := by
    intro y hy
    exact (restrictedBaseOpenDomain_subset_closedDomain D R' hy.1).2
  have hΩstrip : ∀ y ∈ Ω, ∀ i, Xstrip + B + 3 < y.1.1 i := by
    intro y hy i
    exact lt_of_le_of_lt
      (le_trans (le_max_right X0 (Xstrip + B + 3))
        (le_max_right R (max X0 (Xstrip + B + 3))))
      (hy.1.1 i)
  have hΩcenter : ∀ y ∈ Ω, ∀ i, X0 < y.1.1 i := by
    intro y hy i
    exact lt_of_le_of_lt
      (le_trans (le_max_left X0 (Xstrip + B + 3))
        (le_max_right R (max X0 (Xstrip + B + 3))))
      (hy.1.1 i)
  let V := paperRankFullHermiteSmoothValue
    D representative offset S B Fbranch
  have hV : ContDiffOn ℝ ∞ V (Prod.fst '' Ω) := by
    exact paperRankFullHermiteSmoothValue_contDiffOn (A := A)
      D representative offset S hB hFbranch hbound Ω hΩopen hΩbox hΩstrip
  have hQH_eval : ∀ i y, y ∈ Ω →
      MvPolynomial.eval₂Hom
        (subalgebraPointEval D.analyticNearClosedBoxSubalgebra y.1.2)
        (paperRankSymbolArgument V y) (QH i) = F i y := by
    intro i y hy
    have hEval := eval₂Hom_hermiteBeforeRankPolynomialHom_at_source
      D h0D representative offset S H hB y (hΩbox y hy) (hΩcenter y hy)
      (hbound y.1.2 (hΩbox y hy)) (Q i)
    change MvPolynomial.eval₂Hom
      (subalgebraPointEval D.analyticNearClosedBoxSubalgebra y.1.2)
      (paperRankSymbolArgument V y)
      (hermiteBeforeRankPolynomialHom
        D.analyticNearClosedBoxSubalgebra
        (paperRankHermiteJetPolynomial D representative offset S
          (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m))
        (Q i)) = F i y
    rw [show V = paperRankFullHermiteSmoothValue
        D representative offset S B Fbranch by rfl]
    rw [hEval]
    simpa [paperRankSymbolArgument, restrictedPaperPolynomialValue] using
      (congrFun (hQ i) y)
  let FQH : Fin (m + p + a) → PaperRankSource m p a → ℝ :=
    fun i y => MvPolynomial.eval₂Hom
      (subalgebraPointEval D.analyticNearClosedBoxSubalgebra y.1.2)
      (paperRankSymbolArgument V y) (QH i)
  have heqOn : ∀ y ∈ Ω,
      paperRankEquation
          (fun i => restrictedPaperGermPolynomial D h0D (QH i))
          (restrictedPaperCoefficientRepresentative QH) V y =
        constraintMap F y := by
    intro y hy
    calc
      paperRankEquation
          (fun i => restrictedPaperGermPolynomial D h0D (QH i))
          (restrictedPaperCoefficientRepresentative QH) V y =
          constraintMap FQH y :=
        paperRankEquation_from_eval D h0D S QH FQH V
          (by intro i z; rfl) W₀ hpoly y hy.2
      _ = constraintMap F y := by
        funext i
        exact hQH_eval i y hy
  have hΩW₀ : ∀ y ∈ Ω, y.1.2 ∈ W₀ := by
    intro y hy
    exact hy.2
  have hrep : ∀ i d
      (hd : d ∈ (restrictedPaperGermPolynomial D h0D (QH i)).support),
      (restrictedPaperGermPolynomial D h0D (QH i)).coeff d =
        analyticGermOf (restrictedPaperCoefficientRepresentative QH i d)
          (hcoeff i d hd 0 h0W₀) := by
    intro i d hd
    exact restrictedPaperGermPolynomial_coeff_representation D h0D QH i d
  obtain ⟨I, c, g, G, W, hI, hheight, hspan, hWopen, h0W, hWW₀,
      hsupport, hanalytic, hG, hvanish⟩ :=
    exists_paperRankElimination m p a
      (m * (paperRankHermitePositiveDerivativeCount S + 1))
      (fun i => restrictedPaperGermPolynomial D h0D (QH i))
      (restrictedPaperCoefficientRepresentative QH)
      W₀ hW₀open h0W₀ hcoeff hrep Ω hΩopen hΩW₀ V hV
  refine ⟨I, c, g, G, W, ?_, hheight, hspan, hWopen, h0W,
    hsupport, hanalytic, hG, ?_⟩
  · simpa [QH] using hI
  · have hxW : ∀ᶠ n in atTop, (x n).1.2 ∈ W :=
      hxlim (hWopen.mem_nhds h0W)
    filter_upwards [hxW, hxlarge] with n hnW hnlarge
    intro j
    have hxnBase : x n ∈ restrictedBaseOpenDomain D R' := by
      refine ⟨?_, (hx n).1.2⟩
      intro i
      exact max_lt ((hx n).1.1 i) (hnlarge i)
    have hxnΩ : x n ∈ Ω := ⟨hxnBase, hWW₀ hnW⟩
    have hzero : paperRankEquation
        (fun i => restrictedPaperGermPolynomial D h0D (QH i))
        (restrictedPaperCoefficientRepresentative QH) V (x n) = 0 := by
      rw [heqOn (x n) hxnΩ]
      exact (hx n).2.1
    have heventuallyEq : paperRankEquation
        (fun i => restrictedPaperGermPolynomial D h0D (QH i))
        (restrictedPaperCoefficientRepresentative QH) V =ᶠ[𝓝 (x n)]
          constraintMap F := by
      filter_upwards [hΩopen.mem_nhds hxnΩ] with y hy
      exact heqOn y hy
    have hregular : Function.Surjective
        (fderiv ℝ
          (paperRankEquation
            (fun i => restrictedPaperGermPolynomial D h0D (QH i))
            (restrictedPaperCoefficientRepresentative QH) V)
          (x n)) := by
      rw [heventuallyEq.fderiv_eq]
      exact (hx n).2.2
    have hj := hvanish (x n) hxnΩ hnW hzero hregular j
    simpa [V] using hj

/-- The all-unbounded interface to full Hermite rank elimination.  Pointwise
divergence of the representative coordinates supplies the eventual common
cutoff required by `exists_hermiteBeforeRankElimination_along_sequence`. -/
theorem exists_hermiteBeforeRankElimination_along_divergent_sequence
    {A : ℝ → ℝ} {m p a : ℕ} (D : RestrictedBox p)
    (h0D : (0 : RestrictedBoxSpace p) ∈ D.closedBox)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
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
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hQ : ∀ i, restrictedPaperPolynomialValue A D representative offset
      (restrictedJetEnumeration S) (Q i) = F i)
    (x : ℕ → RestrictedSource m p a)
    (hx : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) (constraintMap F))
    (hxrepresentative : ∀ i,
      Tendsto (fun n => (x n).1.1 i) atTop atTop)
    (hxlim : Tendsto (fun n => (x n).1.2) atTop
      (𝓝 (0 : RestrictedBoxSpace p))) :
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
          (fun i => restrictedPaperGermPolynomial D h0D
            (hermiteBeforeRankPolynomialFamily D representative offset S Q i))
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
                D representative offset S B Fbranch) (x n))
            (G j (x n).1.2) = 0 := by
  apply exists_hermiteBeforeRankElimination_along_sequence
    D h0D representative offset S R Xstrip X0 B K K0 Fbranch
      hFbranch hB H hbound Q F hQ x hx
  · apply Filter.eventually_all.mpr
    intro i
    exact (hxrepresentative i).eventually
      (eventually_gt_atTop (max X0 (Xstrip + B + 3)))
  · exact hxlim

end AbelFormalization
