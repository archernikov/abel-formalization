import AbelFormalization.AnalyticRegularZeroElimination
import AbelFormalization.PolynomialCoefficientPadding
import AbelFormalization.PaperRankCoordinates

/-!
# The manuscript's elimination lemma at actual regular zeros

The real source is `((s,w),y)` and
the independent polynomial symbols are ordered `y,(s,v)`. This is a
permutation of the manuscript's symbol order, with no change to the actual
source variables. The equation map uses the original coefficient functions.

Only the coefficients in each original polynomial support need analytic
representatives. The auxiliary function is arbitrary and smooth on the
open projection of the original domain. Regularity means surjectivity of
the actual Fréchet derivative of the full equation map.
-/

noncomputable section

set_option autoImplicit false

open Filter Set
open scoped Topology ContDiff

namespace AbelFormalization

/-- The manuscript's actual equation map `P(s,w,y,V(s,w))`, using the
original finite coefficient representatives without padding the data. -/
def paperRankEquation {m p a b : ℕ}
    (P : Fin (m + p + a) → MvPolynomial (PaperRankSymbols m a b) (RealAnalyticGerm p))
    (coeff : Fin (m + p + a) → (PaperRankSymbols m a b →₀ ℕ) →
      PaperRankRealSpace p → ℝ)
    (V : PaperRankParameterSpace m p → PaperRankRealSpace b) :
    PaperRankSource m p a → Fin (m + p + a) → ℝ :=
  polynomialFamilyEvaluation (fun i => (P i).support) coeff
    (paperRankCoefficientArgument m p a) (paperRankSymbolArgument V)

/-- The paper's hypotheses make its actual equation map differentiable
on its given open domain; no coefficient outside its support is used. -/
theorem differentiableOn_paperRankEquation (m p a b : ℕ)
    (P : Fin (m + p + a) → MvPolynomial (PaperRankSymbols m a b) (RealAnalyticGerm p))
    (coeff : Fin (m + p + a) → (PaperRankSymbols m a b →₀ ℕ) →
      PaperRankRealSpace p → ℝ)
    (W₀ : Set (PaperRankRealSpace p))
    (hcoeff : ∀ i d, d ∈ (P i).support → AnalyticOnNhd ℝ (coeff i d) W₀)
    (Ω : Set (PaperRankSource m p a)) (hΩ : IsOpen Ω)
    (hΩW₀ : ∀ x ∈ Ω, x.1.2 ∈ W₀)
    (V : PaperRankParameterSpace m p → PaperRankRealSpace b)
    (hV : ContDiffOn ℝ ∞ V (Prod.fst '' Ω)) :
    DifferentiableOn ℝ (paperRankEquation P coeff V) Ω := by
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  exact differentiableAt_polynomialFamilyEvaluation
    (fun i => (P i).support) coeff
    (paperRankCoefficientArgument m p a) (paperRankSymbolArgument V) x
    (differentiableAt_paperRankCoefficientArgument m p a x)
    (differentiableAt_paperRankSymbolArgument hΩ hV hx)
    (fun i d hd => (hcoeff i d hd x.1.2 (hΩW₀ x hx)).differentiableAt)

/-- Elimination at regular zeros, with the paper's actual analytic germ
ring, supported analytic coefficient representatives, arbitrary smooth
auxiliary function, finite generators, and one common smaller neighborhood.
The ideal is exactly the retained-variable contraction of the Jacobian
ideal; its height is at least `m+p`. -/
theorem exists_paperRankElimination (m p a b : ℕ)
    (P : Fin (m + p + a) → MvPolynomial (PaperRankSymbols m a b) (RealAnalyticGerm p))
    (coeff : Fin (m + p + a) → (PaperRankSymbols m a b →₀ ℕ) →
      PaperRankRealSpace p → ℝ)
    (W₀ : Set (PaperRankRealSpace p)) (hW₀ : IsOpen W₀)
    (h0W₀ : (0 : PaperRankRealSpace p) ∈ W₀)
    (hcoeff : ∀ i d, d ∈ (P i).support → AnalyticOnNhd ℝ (coeff i d) W₀)
    (hrep : ∀ i d (hd : d ∈ (P i).support), (P i).coeff d =
      analyticGermOf (coeff i d) (hcoeff i d hd 0 h0W₀))
    (Ω : Set (PaperRankSource m p a)) (hΩ : IsOpen Ω)
    (_hΩW₀ : ∀ x ∈ Ω, x.1.2 ∈ W₀)
    (V : PaperRankParameterSpace m p → PaperRankRealSpace b)
    (hV : ContDiffOn ℝ ∞ V (Prod.fst '' Ω)) :
    ∃ I : Ideal (MvPolynomial (PaperRankRetainedSymbols m b) (RealAnalyticGerm p)),
      ∃ c : ℕ,
      ∃ g : Fin c → MvPolynomial (PaperRankRetainedSymbols m b) (RealAnalyticGerm p),
      ∃ G : Fin c → PaperRankRealSpace p → MvPolynomial (PaperRankRetainedSymbols m b) ℝ,
      ∃ W : Set (PaperRankRealSpace p),
        I = jacobianEliminationIdeal a P (analyticGermFormalDerivations p) ∧
        ((m + p : ℕ) : ℕ∞) ≤ I.height ∧
        Ideal.span (Set.range g) = I ∧
        IsOpen W ∧ (0 : PaperRankRealSpace p) ∈ W ∧ W ⊆ W₀ ∧
        (∀ j w, (G j w).support ⊆ (g j).support) ∧
        (∀ j d, AnalyticOnNhd ℝ (fun w => (G j w).coeff d) W) ∧
        (∀ j, analyticPolynomialGermHom (0 : PaperRankRealSpace p) (g j) =
          (G j : Germ (𝓝 (0 : PaperRankRealSpace p))
            (MvPolynomial (PaperRankRetainedSymbols m b) ℝ))) ∧
        ∀ x ∈ Ω, x.1.2 ∈ W →
          paperRankEquation P coeff V x = 0 →
          Function.Surjective (fderiv ℝ (paperRankEquation P coeff V) x) →
          ∀ j, MvPolynomial.eval (paperRankRetainedArgument V x) (G j x.1.2) = 0 := by
  classical
  let padded : Fin (m + p + a) → (PaperRankSymbols m a b →₀ ℕ) →
      PaperRankRealSpace p → ℝ :=
    fun i => zeroPadCoefficients (P i).support (coeff i)
  have hpad : ∀ i d, AnalyticOnNhd ℝ (padded i d) W₀ := by
    intro i
    exact analyticOnNhd_zeroPadCoefficients (P i).support (coeff i) W₀ (hcoeff i)
  have hpadRep : ∀ i d, d ∈ (P i).support → (P i).coeff d =
      analyticGermOf (padded i d) (hpad i d 0 h0W₀) := by
    intro i d hd
    calc
      (P i).coeff d = analyticGermOf (coeff i d) (hcoeff i d hd 0 h0W₀) := hrep i d hd
      _ = analyticGermOf (padded i d) (hpad i d 0 h0W₀) :=
        (analyticGermOf_zeroPadCoefficients_of_mem (P i).support (coeff i) hd 0
          (hpad i d 0 h0W₀) (hcoeff i d hd 0 h0W₀)).symm
  have hFpad : polynomialFamilyEvaluation (fun i => (P i).support) padded
      (paperRankCoefficientArgument m p a) (paperRankSymbolArgument V) =
        paperRankEquation P coeff V :=
    polynomialFamilyEvaluation_zeroPadCoefficients (fun i => (P i).support) coeff
      (paperRankCoefficientArgument m p a) (paperRankSymbolArgument V)
  obtain ⟨I, c, g, G, W, hI, hheight, hspan, hWopen, h0W, hWW₀,
      hsupport, hanalytic, hG, hvanish⟩ :=
    exists_analyticRegularZeroElimination p (m + p) a P padded W₀ hW₀ h0W₀ hpad hpadRep
      Ω hΩ (paperRankCoefficientArgument m p a) (paperRankSymbolArgument V)
      (differentiableOn_paperRankCoefficientArgument m p a Ω)
      (differentiableOn_paperRankSymbolArgument hΩ hV)
  refine ⟨I, c, g, G, W, hI, hheight, hspan, hWopen, h0W, hWW₀,
    hsupport, hanalytic, hG, ?_⟩
  intro x hx hxW hzero hregular j
  have hzeroPad : polynomialFamilyEvaluation (fun i => (P i).support) padded
      (paperRankCoefficientArgument m p a) (paperRankSymbolArgument V) x = 0 := by
    rw [hFpad]
    exact hzero
  have hregularPad : Function.Surjective
      (fderiv ℝ (polynomialFamilyEvaluation (fun i => (P i).support) padded
        (paperRankCoefficientArgument m p a) (paperRankSymbolArgument V)) x) := by
    rw [hFpad]
    exact hregular
  have hvalue := hvanish x hx hxW hzeroPad hregularPad j
  simpa only [paperRankSymbolArgument_comp_inr, paperRankCoefficientArgument_apply] using hvalue

end AbelFormalization
