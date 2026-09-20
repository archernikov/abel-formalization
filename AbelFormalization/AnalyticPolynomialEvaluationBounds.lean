import AbelFormalization.RestrictedRankHermiteCurriedRepresentatives
import AbelFormalization.FiniteSupportCoefficientPerturbation

noncomputable section
set_option autoImplicit false

open Filter Set
open scoped Topology

namespace AbelFormalization

universe u v w x

/-- A point-dependent real polynomial whose support stays in one fixed finite
set has a polynomially bounded evaluation when its scalar coefficients are
analytic along a convergent parameter sequence and all variables are
polynomially bounded. -/
theorem analyticMvPolynomialEvaluation_hasPolynomialUpperBound
    {Param : Type u} [NormedAddCommGroup Param] [NormedSpace ℝ Param]
    {X σ : Type v} {l : Filter X} {S : X → ℝ}
    (F : Param → MvPolynomial σ ℝ)
    (support : Finset (σ →₀ ℕ))
    (U : Set Param) (x₀ : Param) (hx₀U : x₀ ∈ U)
    (w : X → Param) (hw : Tendsto w l (𝓝 x₀))
    (hsupport : ∀ z, (F z).support ⊆ support)
    (hanalytic : ∀ e ∈ support,
      AnalyticOnNhd ℝ (fun z ↦ (F z).coeff e) U)
    (y : σ → X → ℝ)
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (hy : ∀ i, HasPolynomialUpperBound l S (y i)) :
    HasPolynomialUpperBound l S
      (fun n ↦ MvPolynomial.eval (fun i ↦ y i n) (F (w n))) := by
  have hfixed : HasPolynomialUpperBound l S
      (finiteMonomialSetEvaluation support
        (fun e n ↦ (F (w n)).coeff e) y) := by
    apply finiteMonomialSetEvaluation_hasPolynomialUpperBound hS
    · intro e he
      exact HasPolynomialUpperBound.of_analyticOnNhd_comp
        hx₀U (hanalytic e he) hw
    · exact hy
  apply hfixed.congr
  intro n
  rw [MvPolynomial.eval_eq]
  change
    (∑ d ∈ (F (w n)).support,
        (F (w n)).coeff d * d.prod (fun i k ↦ y i n ^ k)) =
      ∑ d ∈ support,
        (F (w n)).coeff d * d.prod (fun i k ↦ y i n ^ k)
  apply Finset.sum_subset (hsupport (w n))
  intro d _ hd
  simp only [MvPolynomial.mem_support_iff, not_ne_iff] at hd
  simp [hd]

/-- In a point-dependent curried polynomial, evaluating one outer
coefficient at polynomially bounded values of the retained variables is
polynomially bounded.  The fixed inner support may be read from any
germ-valued model polynomial. -/
theorem analyticCurriedCoefficientEvaluation_hasPolynomialUpperBound
    {R : Type u} [CommRing R]
    {Param : Type v} [NormedAddCommGroup Param] [NormedSpace ℝ Param]
    {X Active Coeff κ : Type w} {l : Filter X} {S : X → ℝ}
    (P : κ → MvPolynomial Active (MvPolynomial Coeff R))
    (F : κ → Param → MvPolynomial Active (MvPolynomial Coeff ℝ))
    (U : Set Param) (x₀ : Param) (hx₀U : x₀ ∈ U)
    (wParam : X → Param) (hw : Tendsto wParam l (𝓝 x₀))
    (hsupport : ∀ i z a, ((F i z).coeff a).support ⊆
      ((P i).coeff a).support)
    (hanalytic : ∀ i a e,
      AnalyticOnNhd ℝ (fun z ↦ ((F i z).coeff a).coeff e) U)
    (y : Coeff → X → ℝ)
    (hS : ∀ᶠ n in l, 1 ≤ S n)
    (hy : ∀ i, HasPolynomialUpperBound l S (y i)) :
    ∀ i a, HasPolynomialUpperBound l S (fun n ↦
      MvPolynomial.eval (fun c ↦ y c n) ((F i (wParam n)).coeff a)) := by
  intro i a
  exact analyticMvPolynomialEvaluation_hasPolynomialUpperBound
    (fun z ↦ (F i z).coeff a) ((P i).coeff a).support U x₀ hx₀U
    wParam hw (fun z ↦ hsupport i z a)
    (fun e _ ↦ hanalytic i a e) y hS hy

end AbelFormalization
