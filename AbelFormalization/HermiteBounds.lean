import AbelFormalization.HermiteKernel
import AbelFormalization.HermiteNodeBounds
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Uniform bounds for Hermite coefficient kernels

Each coefficient of the node polynomial and of the divided-difference kernel
is continuous jointly in the nodes and the contour point. On the closed node
polydisk and the contour circle, the denominator is bounded away from zero.
Compactness then supplies one positive bound for every coefficient below the
total multiplicity, including when nodes coincide.
-/

noncomputable section

namespace AbelFormalization

open Polynomial Set Metric

private theorem continuous_polynomial_coeff_mul {α : Type*} [TopologicalSpace α]
    {P Q : α → ℂ[X]}
    (hP : ∀ j, Continuous (fun x => (P x).coeff j))
    (hQ : ∀ j, Continuous (fun x => (Q x).coeff j)) (j : ℕ) :
    Continuous (fun x => (P x * Q x).coeff j) := by
  simp only [Polynomial.coeff_mul]
  exact continuous_finsetSum _ fun ij _ => (hP ij.1).mul (hQ ij.2)

private theorem continuous_polynomial_coeff_pow {α : Type*} [TopologicalSpace α]
    {P : α → ℂ[X]} (hP : ∀ j, Continuous (fun x => (P x).coeff j)) :
    ∀ n j : ℕ, Continuous (fun x => (P x ^ n).coeff j) := by
  intro n
  induction n with
  | zero =>
      intro j
      simpa only [pow_zero] using
        (continuous_const : Continuous (fun _ : α => (1 : ℂ[X]).coeff j))
  | succ n ih =>
      intro j
      simp only [pow_succ]
      exact continuous_polynomial_coeff_mul ih hP j

private theorem continuous_polynomial_coeff_prod {α ι : Type*} [TopologicalSpace α]
    (P : ι → α → ℂ[X])
    (hP : ∀ i j, Continuous (fun x => (P i x).coeff j)) :
    ∀ (s : Finset ι) (j : ℕ), Continuous (fun x => (∏ i ∈ s, P i x).coeff j) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro j
      simpa only [Finset.prod_empty] using
        (continuous_const : Continuous (fun _ : α => (1 : ℂ[X]).coeff j))
  | @insert i s hi ih =>
      intro j
      simp only [Finset.prod_insert hi]
      exact continuous_polynomial_coeff_mul (hP i) ih j

variable {ι : Type*} [Fintype ι]

/-- Each node-polynomial coefficient varies continuously with all nodes. -/
theorem continuous_nodePolynomial_coeff (m : ι → ℕ) (j : ℕ) :
    Continuous (fun δ : ι → ℂ => (nodePolynomial δ m).coeff j) := by
  have hfactor : ∀ i j, Continuous (fun δ : ι → ℂ => (X - C (δ i)).coeff j) := by
    intro i j
    by_cases hj : j = 0
    · subst j
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
        zero_sub]
      fun_prop
    · simpa only [Polynomial.coeff_sub, Polynomial.coeff_C, ite_eq_right hj, sub_zero] using
        (continuous_const : Continuous (fun _ : ι → ℂ => (X : ℂ[X]).coeff j))
  unfold nodePolynomial
  apply continuous_polynomial_coeff_prod
  intro i k
  exact continuous_polynomial_coeff_pow (hfactor i) (m i) k

/-- Joint continuity of evaluating the node polynomial at the contour point. -/
theorem continuous_nodePolynomial_eval_joint (m : ι → ℕ) :
    Continuous (fun p : (ι → ℂ) × ℂ => (nodePolynomial p.1 m).eval p.2) := by
  simp only [nodePolynomial_eval]
  exact continuous_finsetProd _ fun i _ =>
    (continuous_snd.sub ((continuous_apply i).comp continuous_fst)).pow (m i)

/-- The degree of the node polynomial is fixed, so the finite coefficient
formula for the Hermite kernel is continuous jointly in all its parameters. -/
theorem continuous_hermiteKernel_nodePolynomial_coeff_joint (m : ι → ℕ) (j : ℕ) :
    Continuous (fun p : (ι → ℂ) × ℂ => (hermiteKernel (nodePolynomial p.1 m) p.2).coeff j) := by
  simp only [hermiteKernel_coeff, nodePolynomial_natDegree]
  exact continuous_finsetSum _ fun i _ =>
    (continuous_snd.pow (i - (j + 1))).mul
      ((continuous_nodePolynomial_coeff m i).comp continuous_fst)

/-- The scalar coefficient kernel in contour Hermite interpolation. -/
def hermiteCoefficientKernel (δ : ι → ℂ) (m : ι → ℕ) (ζ : ℂ) (j : ℕ) : ℂ :=
  (hermiteKernel (nodePolynomial δ m) ζ).coeff j / (nodePolynomial δ m).eval ζ

/-- Joint continuity wherever the contour denominator is nonzero. -/
theorem continuousAt_hermiteCoefficientKernel (m : ι → ℕ) (j : ℕ)
    (p : (ι → ℂ) × ℂ) (hp : (nodePolynomial p.1 m).eval p.2 ≠ 0) :
    ContinuousAt (fun q : (ι → ℂ) × ℂ => hermiteCoefficientKernel q.1 m q.2 j) p :=
  (continuous_hermiteKernel_nodePolynomial_coeff_joint m j).continuousAt.div
    (continuous_nodePolynomial_eval_joint m).continuousAt hp

/-- The closed parameter domain used to obtain a uniform coefficient bound. -/
def hermiteContourParameters (B : ℝ) : Set ((ι → ℂ) × ℂ) :=
  {p | (∀ i, ‖p.1 i‖ ≤ B + 1 / 4) ∧ ‖p.2‖ = B + 1}

omit [Fintype ι] in
theorem isCompact_hermiteContourParameters (B : ℝ) :
    IsCompact (hermiteContourParameters (ι := ι) B) := by
  have hn : IsCompact {δ : ι → ℂ | ∀ i, δ i ∈ closedBall 0 (B + 1 / 4)} :=
    isCompact_pi_infinite fun _ => isCompact_closedBall 0 (B + 1 / 4)
  have hn' : IsCompact {δ : ι → ℂ | ∀ i, ‖δ i‖ ≤ B + 1 / 4} := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hn
  have hs : IsCompact {ζ : ℂ | ‖ζ‖ = B + 1} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : ℂ) (B + 1)
  exact hn'.prod hs

/-- The contour denominator bound also holds on the closed node polydisk. -/
theorem nodePolynomial_contour_lower_bound_closed (m : ι → ℕ) {δ : ι → ℂ}
    {ζ : ℂ} {B : ℝ} (hδ : ∀ i, ‖δ i‖ ≤ B + 1 / 4) (hζ : ‖ζ‖ = B + 1) :
    (3 / 4 : ℝ) ^ totalMultiplicity m ≤ ‖(nodePolynomial δ m).eval ζ‖ := by
  apply nodePolynomial_radius_gap_bound m (R := B + 1 / 4) (by norm_num)
  · exact hδ
  · linarith

theorem nodePolynomial_contour_ne_zero_closed (m : ι → ℕ) {δ : ι → ℂ}
    {ζ : ℂ} {B : ℝ} (hδ : ∀ i, ‖δ i‖ ≤ B + 1 / 4) (hζ : ‖ζ‖ = B + 1) :
    (nodePolynomial δ m).eval ζ ≠ 0 :=
  norm_pos_iff.mp ((pow_pos (by norm_num : (0 : ℝ) < 3 / 4) _).trans_le
    (nodePolynomial_contour_lower_bound_closed m hδ hζ))

/-- The coefficient kernel is continuous on the entire compact parameter domain. -/
theorem continuousOn_hermiteCoefficientKernel (B : ℝ) (m : ι → ℕ) (j : ℕ) :
    ContinuousOn (fun p : (ι → ℂ) × ℂ => hermiteCoefficientKernel p.1 m p.2 j)
      (hermiteContourParameters B) := by
  intro p hp
  exact (continuousAt_hermiteCoefficientKernel m j p
    (nodePolynomial_contour_ne_zero_closed m hp.1 hp.2)).continuousWithinAt

/-- One positive constant, depending only on the radius bound and multiplicities,
bounds every coefficient below the total multiplicity for every allowed tuple of
nodes and every point on the contour. No distinctness hypothesis is used. -/
theorem exists_uniform_hermiteCoefficientKernel_bound (B : ℝ) (m : ι → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ι → ℂ) (ζ : ℂ),
      (∀ i, ‖δ i‖ ≤ B + 1 / 4) → ‖ζ‖ = B + 1 →
      ∀ j : ℕ, j < totalMultiplicity m → ‖hermiteCoefficientKernel δ m ζ j‖ ≤ C := by
  let f : ((ι → ℂ) × ℂ) → Fin (totalMultiplicity m) → ℂ :=
    fun p j => hermiteCoefficientKernel p.1 m p.2 j
  have hf : ContinuousOn f (hermiteContourParameters B) :=
    continuousOn_pi.mpr fun j => continuousOn_hermiteCoefficientKernel B m j
  obtain ⟨C, hC⟩ := (isCompact_hermiteContourParameters B).exists_bound_of_continuousOn hf
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro δ ζ hδ hζ j hj
  have hp : (δ, ζ) ∈ hermiteContourParameters B := ⟨hδ, hζ⟩
  have hb := (norm_le_pi_norm (f (δ, ζ)) ⟨j, hj⟩).trans (hC (δ, ζ) hp)
  exact hb.trans (le_max_left C 1)

end AbelFormalization
