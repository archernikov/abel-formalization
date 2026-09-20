import AbelFormalization.HermiteBounds
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Holomorphic dependence of the Hermite coefficient kernels

The coefficients of the node polynomial are polynomial expressions in the nodes.
The contour coefficient kernels are therefore jointly analytic wherever their
denominator is nonzero, including when some nodes coincide.
-/

noncomputable section

namespace AbelFormalization

open Polynomial Set Metric

private theorem analyticAt_polynomial_coeff_mul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {P Q : E → ℂ[X]} {x : E}
    (hP : ∀ j, AnalyticAt ℂ (fun y => (P y).coeff j) x)
    (hQ : ∀ j, AnalyticAt ℂ (fun y => (Q y).coeff j) x) (j : ℕ) :
    AnalyticAt ℂ (fun y => (P y * Q y).coeff j) x := by
  simp only [Polynomial.coeff_mul]
  exact Finset.analyticAt_fun_sum _ fun ij _ => (hP ij.1).fun_mul (hQ ij.2)

private theorem analyticAt_polynomial_coeff_pow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {P : E → ℂ[X]} {x : E}
    (hP : ∀ j, AnalyticAt ℂ (fun y => (P y).coeff j) x) :
    ∀ n j : ℕ, AnalyticAt ℂ (fun y => (P y ^ n).coeff j) x := by
  intro n
  induction n with
  | zero =>
      intro j
      simpa only [pow_zero] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : E => (1 : ℂ[X]).coeff j) x)
  | succ n ih =>
      intro j
      simp only [pow_succ]
      exact analyticAt_polynomial_coeff_mul ih hP j

private theorem analyticAt_polynomial_coeff_prod {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (P : ι → E → ℂ[X]) {x : E}
    (hP : ∀ i j, AnalyticAt ℂ (fun y => (P i y).coeff j) x) :
    ∀ (s : Finset ι) (j : ℕ), AnalyticAt ℂ (fun y => (∏ i ∈ s, P i y).coeff j) x := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro j
      simpa only [Finset.prod_empty] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : E => (1 : ℂ[X]).coeff j) x)
  | @insert i s hi ih =>
      intro j
      simp only [Finset.prod_insert hi]
      exact analyticAt_polynomial_coeff_mul (hP i) ih j

variable {ι : Type*} [Fintype ι]

/-- Every coefficient of the node polynomial is entire in its nodes. -/
theorem analyticAt_nodePolynomial_coeff (m : ι → ℕ) (j : ℕ) (δ : ι → ℂ) :
    AnalyticAt ℂ (fun ε : ι → ℂ => (nodePolynomial ε m).coeff j) δ := by
  have hfactor : ∀ i j,
      AnalyticAt ℂ (fun ε : ι → ℂ => (X - C (ε i)).coeff j) δ := by
    intro i j
    by_cases hj : j = 0
    · subst j
      simpa only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
        zero_sub, ContinuousLinearMap.proj_apply] using
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt δ).fun_neg
    · simpa only [Polynomial.coeff_sub, Polynomial.coeff_C, ite_eq_right hj, sub_zero] using
        (analyticAt_const : AnalyticAt ℂ (fun _ : ι → ℂ => (X : ℂ[X]).coeff j) δ)
  unfold nodePolynomial
  apply analyticAt_polynomial_coeff_prod
  intro i k
  exact analyticAt_polynomial_coeff_pow (hfactor i) (m i) k

/-- Evaluation of the node polynomial is jointly entire in nodes and argument. -/
theorem analyticAt_nodePolynomial_eval_joint (m : ι → ℕ) (p : (ι → ℂ) × ℂ) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × ℂ => (nodePolynomial q.1 m).eval q.2) p := by
  simp only [nodePolynomial_eval]
  exact Finset.analyticAt_fun_prod _ fun i _ =>
    (analyticAt_snd.fun_sub
      (((ContinuousLinearMap.proj (R := ℂ) i).analyticAt p.1).fun_comp analyticAt_fst)).fun_pow (m i)

/-- The Hermite numerator coefficients are jointly entire. -/
theorem analyticAt_hermiteKernel_nodePolynomial_coeff_joint (m : ι → ℕ) (j : ℕ)
    (p : (ι → ℂ) × ℂ) :
    AnalyticAt ℂ
      (fun q : (ι → ℂ) × ℂ => (hermiteKernel (nodePolynomial q.1 m) q.2).coeff j) p := by
  simp only [hermiteKernel_coeff, nodePolynomial_natDegree]
  exact Finset.analyticAt_fun_sum _ fun i _ =>
    (analyticAt_snd.fun_pow (i - (j + 1))).fun_mul
      ((analyticAt_nodePolynomial_coeff m i p.1).fun_comp analyticAt_fst)

/-- Joint analyticity holds at every parameter tuple with nonzero denominator. -/
theorem analyticAt_hermiteCoefficientKernel_joint (m : ι → ℕ) (j : ℕ)
    (p : (ι → ℂ) × ℂ) (hp : (nodePolynomial p.1 m).eval p.2 ≠ 0) :
    AnalyticAt ℂ (fun q : (ι → ℂ) × ℂ => hermiteCoefficientKernel q.1 m q.2 j) p :=
  (analyticAt_hermiteKernel_nodePolynomial_coeff_joint m j p).fun_div
    (analyticAt_nodePolynomial_eval_joint m p) hp

/-- Fixing the contour argument preserves analytic dependence on all nodes. -/
theorem analyticAt_hermiteCoefficientKernel_nodes (m : ι → ℕ) (j : ℕ)
    (δ : ι → ℂ) (ζ : ℂ) (h : (nodePolynomial δ m).eval ζ ≠ 0) :
    AnalyticAt ℂ (fun ε : ι → ℂ => hermiteCoefficientKernel ε m ζ j) δ := by
  have hp : AnalyticAt ℂ (fun ε : ι → ℂ => (ε, ζ)) δ :=
    analyticAt_id.prod analyticAt_const
  exact (analyticAt_hermiteCoefficientKernel_joint m j (δ, ζ) h).fun_comp
    (f := fun ε : ι → ℂ => (ε, ζ)) hp

/-- Analytic neighborhoods exist at all points of the compact contour domain. -/
theorem analyticOnNhd_hermiteCoefficientKernel_joint (B : ℝ) (m : ι → ℕ) (j : ℕ) :
    AnalyticOnNhd ℂ (fun p : (ι → ℂ) × ℂ => hermiteCoefficientKernel p.1 m p.2 j)
      (hermiteContourParameters B) := by
  intro p hp
  exact analyticAt_hermiteCoefficientKernel_joint m j p
    (nodePolynomial_contour_ne_zero_closed m hp.1 hp.2)

/-- All joint first derivatives have one uniform operator-norm bound on the
closed contour parameter domain. -/
theorem exists_uniform_fderiv_hermiteCoefficientKernel_bound (B : ℝ) (m : ι → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ι → ℂ) (ζ : ℂ),
      (∀ i, ‖δ i‖ ≤ B + 1 / 4) → ‖ζ‖ = B + 1 →
      ∀ j : ℕ, j < totalMultiplicity m →
        ‖fderiv ℂ (fun p : (ι → ℂ) × ℂ => hermiteCoefficientKernel p.1 m p.2 j)
          (δ, ζ)‖ ≤ C := by
  let f : ((ι → ℂ) × ℂ) → Fin (totalMultiplicity m) →
      ((ι → ℂ) × ℂ) →L[ℂ] ℂ :=
    fun p j => fderiv ℂ (fun q : (ι → ℂ) × ℂ => hermiteCoefficientKernel q.1 m q.2 j) p
  have hf : ContinuousOn f (hermiteContourParameters B) :=
    continuousOn_pi.mpr fun j =>
      (analyticOnNhd_hermiteCoefficientKernel_joint B m j).fderiv.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_hermiteContourParameters B).exists_bound_of_continuousOn hf
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro δ ζ hδ hζ j hj
  have hp : (δ, ζ) ∈ hermiteContourParameters B := ⟨hδ, hζ⟩
  have hb := (norm_le_pi_norm (f (δ, ζ)) ⟨j, hj⟩).trans (hC (δ, ζ) hp)
  exact hb.trans (le_max_left C 1)

/-- The derivative in the nodes is the restriction of the joint derivative. -/
theorem fderiv_hermiteCoefficientKernel_nodes (m : ι → ℕ) (j : ℕ)
    (δ : ι → ℂ) (ζ : ℂ) (h : (nodePolynomial δ m).eval ζ ≠ 0) :
    fderiv ℂ (fun ε : ι → ℂ => hermiteCoefficientKernel ε m ζ j) δ =
      (fderiv ℂ (fun p : (ι → ℂ) × ℂ => hermiteCoefficientKernel p.1 m p.2 j)
        (δ, ζ)).comp (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ) := by
  have hp : HasFDerivAt (fun ε : ι → ℂ => (ε, ζ))
      (ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ) δ := hasFDerivAt_prodMk_left δ ζ
  have hd := (analyticAt_hermiteCoefficientKernel_joint m j (δ, ζ) h).differentiableAt.hasFDerivAt
  exact (hd.comp δ hp).fderiv

/-- The same compactness bound controls derivatives only in the node variables. -/
theorem exists_uniform_fderiv_hermiteCoefficientKernel_nodes_bound (B : ℝ) (m : ι → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ι → ℂ) (ζ : ℂ),
      (∀ i, ‖δ i‖ ≤ B + 1 / 4) → ‖ζ‖ = B + 1 →
      ∀ j : ℕ, j < totalMultiplicity m →
        ‖fderiv ℂ (fun ε : ι → ℂ => hermiteCoefficientKernel ε m ζ j) δ‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_fderiv_hermiteCoefficientKernel_bound B m
  refine ⟨C, hC, ?_⟩
  intro δ ζ hδ hζ j hj
  rw [fderiv_hermiteCoefficientKernel_nodes m j δ ζ
    (nodePolynomial_contour_ne_zero_closed m hδ hζ)]
  calc
    _ ≤ _ * ‖ContinuousLinearMap.inl ℂ (ι → ℂ) ℂ‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ _ * 1 := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_inl_le_one ℂ (ι → ℂ) ℂ) (norm_nonneg _)
    _ ≤ C := by simpa only [mul_one] using hbound δ ζ hδ hζ j hj

end AbelFormalization
