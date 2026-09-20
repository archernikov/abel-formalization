import AbelFormalization.ComplexEstimates
import AbelFormalization.HermiteCoefficientAnalytic
import AbelFormalization.HermiteCoefficientBounds
import AbelFormalization.HermiteInterpolation
import AbelFormalization.NormalizedPolynomial

/-!
# The uniform Abel Hermite family

This assembles the first part of the manuscript's Hermite interpolation lemma.
The node neighborhood is fixed independently of the real center. Complex
values and jets use the explicitly chosen compatible extensions of the real
Abel function. The coefficient bound has the uniform exponent `M₀ = 1`.
-/

noncomputable section

namespace AbelFormalization

open Set Metric Polynomial Filter
open scoped Topology

variable {ι : Type*} [Fintype ι]

/-- The manuscript's fixed node neighborhood, with a quarter-unit margin. -/
def hermiteNodeNeighborhood (B : ℝ) : Set (ι → ℂ) :=
  {δ | ∀ i, ‖δ i‖ < B + 1 / 4}

theorem hermiteNodeNeighborhood_eq_ball {B : ℝ} (hB : 0 < B) :
    hermiteNodeNeighborhood (ι := ι) B = ball 0 (B + 1 / 4) := by
  ext δ
  simp only [hermiteNodeNeighborhood, mem_ofPred_eq, mem_ball, dist_zero_right,
    pi_norm_lt_iff (show 0 < B + 1 / 4 by linarith)]

theorem isOpen_hermiteNodeNeighborhood {B : ℝ} (hB : 0 < B) :
    IsOpen (hermiteNodeNeighborhood (ι := ι) B) := by
  rw [hermiteNodeNeighborhood_eq_ball hB]
  exact isOpen_ball

theorem isBounded_hermiteNodeNeighborhood {B : ℝ} (hB : 0 < B) :
    Bornology.IsBounded (hermiteNodeNeighborhood (ι := ι) B) := by
  rw [hermiteNodeNeighborhood_eq_ball hB]
  exact isBounded_ball

omit [Fintype ι] in
theorem closed_nodes_subset_hermiteNodeNeighborhood (B : ℝ) :
    {δ : ι → ℂ | ∀ i, ‖δ i‖ ≤ B} ⊆ hermiteNodeNeighborhood B := by
  intro δ hδ i
  have hi := hδ i
  linarith

theorem nodeMultiplicity_le_totalMultiplicity (δ : ι → ℂ) (m : ι → ℕ) (ξ : ℂ) :
    nodeMultiplicity δ m ξ ≤ totalMultiplicity m := by
  classical
  unfold nodeMultiplicity totalMultiplicity
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

/-- The chosen complex branch translated so that its real center is the origin. -/
def shiftedAbelExtension (branch : ℝ → ℂ → ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  branch x ((x : ℂ) + z)

/-- The explicit contour interpolant for the shifted branch. -/
def abelHermitePolynomial (branch : ℝ → ℂ → ℂ) (B : ℝ) (m : ι → ℕ)
    (x : ℝ) (δ : ι → ℂ) : ℂ[X] :=
  hermiteContourPolynomial (shiftedAbelExtension branch x) (nodePolynomial δ m) (B + 1)

/-- Factorial-normalized coefficients of the explicit contour polynomial. -/
def abelHermiteCoeff (branch : ℝ → ℂ → ℂ) (B : ℝ) (m : ι → ℕ)
    (x : ℝ) (δ : ι → ℂ) (j : ℕ) : ℂ :=
  normalizedCoeff (abelHermitePolynomial branch B m x δ) j

private theorem shifted_mem_branch_ball (x B : ℝ) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) (B + 1)) :
    (x : ℂ) + z ∈ ball (x : ℂ) (B + 2) := by
  have hn : ‖z‖ ≤ B + 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have ht : ‖z‖ < B + 2 := by linarith
  simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using ht

private theorem shiftedAbelExtension_analytic {branch : ℝ → ℂ → ℂ} {x B : ℝ}
    (h : AnalyticOnNhd ℂ (branch x) (ball (x : ℂ) (B + 2))) :
    AnalyticOnNhd ℂ (shiftedAbelExtension branch x) (closedBall (0 : ℂ) (B + 1)) := by
  intro z hz
  exact (h _ (shifted_mem_branch_ball x B hz)).fun_comp
    (f := fun w : ℂ => (x : ℂ) + w) (analyticAt_const.fun_add analyticAt_id)

private theorem shiftedAbelExtension_realAgreement {A : ℝ → ℝ}
    {branch : ℝ → ℂ → ℂ} {x B : ℝ}
    (h : ∀ y : ℝ, y ∈ ball x (B + 2) → branch x (y : ℂ) = (A y : ℂ))
    (t : ℝ) (ht : |t| ≤ B + 1) :
    shiftedAbelExtension branch x (t : ℂ) = (A (x + t) : ℂ) := by
  have hy : x + t ∈ ball x (B + 2) := by
    have ht' : |t| < B + 2 := by linarith
    simpa only [mem_ball, Real.dist_eq, add_sub_cancel_left] using ht'
  simpa only [shiftedAbelExtension, Complex.ofReal_add] using h (x + t) hy

private theorem analyticAt_normalized_hermiteContourCoeff (R : ℝ) (hR : 0 ≤ R)
    (m : ι → ℕ) (j : ℕ) (hj : j < totalMultiplicity m)
    (f : ℂ → ℂ) (hf : ContinuousOn f (sphere (0 : ℂ) R)) (δ : ι → ℂ)
    (hQ : ∀ z ∈ sphere (0 : ℂ) R, (nodePolynomial δ m).eval z ≠ 0) :
    AnalyticAt ℂ
      (fun ε : ι → ℂ => normalizedCoeff (hermiteContourPolynomial f (nodePolynomial ε m) R) j) δ := by
  have ha : AnalyticAt ℂ
      (fun ε : ι → ℂ => (j.factorial : ℂ) * hermiteContourCoeff f (nodePolynomial ε m) R j) δ :=
    analyticAt_const.fun_mul (analyticAt_hermiteContourCoeff_nodes R hR m j f hf δ hQ)
  apply ha.congr
  apply Filter.Eventually.of_forall
  intro ε
  change (j.factorial : ℂ) * hermiteContourCoeff f (nodePolynomial ε m) R j =
    (j.factorial : ℂ) * (hermiteContourPolynomial f (nodePolynomial ε m) R).coeff j
  rw [hermiteContourPolynomial_coeff f (nodePolynomial ε m) R
    (by simpa only [nodePolynomial_natDegree] using hj)]

/-- The first part of the manuscript's Hermite lemma, with all data and their
uniform quantifiers recorded together. `branch` explicitly supplies the meaning
of complex Abel values; `shiftedAbelExtension branch x` is `z ↦ A(x+z)` on its disk. -/
structure AbelHermiteFamilySpec (A : ℝ → ℝ) (B : ℝ) (m : ι → ℕ)
    (X0 K K0 : ℝ) (branch : ℝ → ℂ → ℂ) : Prop where
  threshold_gt_one : 1 < X0
  extensionConstant_pos : 0 < K
  coefficientConstant_pos : 0 < K0
  neighborhood_open : IsOpen (hermiteNodeNeighborhood (ι := ι) B)
  neighborhood_bounded : Bornology.IsBounded (hermiteNodeNeighborhood (ι := ι) B)
  neighborhood_contains : {δ : ι → ℂ | ∀ i, ‖δ i‖ ≤ B} ⊆ hermiteNodeNeighborhood B
  branch_analytic : ∀ x, X0 < x → AnalyticOnNhd ℂ (branch x) (ball (x : ℂ) (B + 2))
  branch_realAgreement : ∀ x, X0 < x →
    ∀ y : ℝ, y ∈ ball x (B + 2) → branch x (y : ℂ) = (A y : ℂ)
  branch_bound : ∀ x, X0 < x →
    ∀ z ∈ ball (x : ℂ) (B + 2), ‖branch x z‖ ≤ K * Real.log x
  branch_compatible : ∀ x y, X0 < x → X0 < y →
    EqOn (branch x) (branch y) (ball (x : ℂ) (B + 2) ∩ ball (y : ℂ) (B + 2))
  shifted_analytic : ∀ x, X0 < x →
    AnalyticOnNhd ℂ (shiftedAbelExtension branch x) (closedBall (0 : ℂ) (B + 1))
  shifted_realAgreement : ∀ x, X0 < x → ∀ t : ℝ, |t| ≤ B + 1 →
    shiftedAbelExtension branch x (t : ℂ) = (A (x + t) : ℂ)
  shifted_bound : ∀ x, X0 < x → ∀ z ∈ closedBall (0 : ℂ) (B + 1),
    ‖shiftedAbelExtension branch x z‖ ≤ K * Real.log x
  coefficient_analytic : ∀ x, X0 < x → ∀ j, j < totalMultiplicity m →
    AnalyticOnNhd ℂ (fun δ => abelHermiteCoeff branch B m x δ j) (hermiteNodeNeighborhood B)
  coefficient_bound : ∀ x, X0 < x → ∀ δ ∈ hermiteNodeNeighborhood B,
    ∀ j, j < totalMultiplicity m → ‖abelHermiteCoeff branch B m x δ j‖ ≤ K0 * (1 + x)
  degree_bound : ∀ x, X0 < x → ∀ δ ∈ hermiteNodeNeighborhood B,
    (abelHermitePolynomial branch B m x δ).degree < (totalMultiplicity m : WithBot ℕ)
  normalized_expansion : ∀ x, X0 < x → ∀ δ ∈ hermiteNodeNeighborhood B, ∀ z : ℂ,
    (abelHermitePolynomial branch B m x δ).eval z =
      ∑ j ∈ Finset.range (totalMultiplicity m),
        abelHermiteCoeff branch B m x δ j * z ^ j / (j.factorial : ℂ)
  combined_jets : ∀ x, X0 < x → ∀ δ ∈ hermiteNodeNeighborhood B,
    ∀ (ξ : ℂ) (r : ℕ), r < nodeMultiplicity δ m ξ →
      iteratedDeriv r (shiftedAbelExtension branch x) ξ =
        iteratedDeriv r (fun z => (abelHermitePolynomial branch B m x δ).eval z) ξ
  combined_jets_explicit : ∀ x, X0 < x → ∀ δ ∈ hermiteNodeNeighborhood B,
    ∀ (ξ : ℂ) (r : ℕ), r < nodeMultiplicity δ m ξ →
      iteratedDeriv r (shiftedAbelExtension branch x) ξ =
        ∑ j ∈ Finset.Ico r (totalMultiplicity m),
          abelHermiteCoeff branch B m x δ j * ξ ^ (j - r) / ((j - r).factorial : ℂ)
  constant_coefficient : ∀ x, X0 < x → ∀ δ ∈ hermiteNodeNeighborhood B,
    ∀ i, δ i = 0 → 0 < m i → abelHermiteCoeff branch B m x δ 0 = (A x : ℂ)

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- Uniform Hermite families exist for every real-analytic increasing Abel
function, using only the specified finite multiplicities and radius bound. -/
theorem exists_abelHermiteFamily {B : ℝ} (hB : 0 < B) (m : ι → ℕ)
    (hd : 0 < totalMultiplicity m) :
    ∃ X0 K K0 : ℝ, ∃ branch : ℝ → ℂ → ℂ,
      AbelHermiteFamilySpec A B m X0 K K0 branch := by
  obtain ⟨X0, K, branch, hX0, hK, hbranch, hcompat⟩ :=
    hA.exists_compatible_bounded_complex_extensions (show 0 < B + 2 by linarith)
  obtain ⟨D, hD, hcoeff⟩ := exists_uniform_hermiteContour_coeff_bounds B m hB.le
  have hR : 0 < B + 1 := by linarith
  have hshift : ∀ x, X0 < x →
      AnalyticOnNhd ℂ (shiftedAbelExtension branch x) (closedBall (0 : ℂ) (B + 1)) :=
    fun x hx => shiftedAbelExtension_analytic (hbranch x hx).1
  have hreal : ∀ x, X0 < x → ∀ t : ℝ, |t| ≤ B + 1 →
      shiftedAbelExtension branch x (t : ℂ) = (A (x + t) : ℂ) :=
    fun x hx => shiftedAbelExtension_realAgreement (hbranch x hx).2.1
  have hbound : ∀ x, X0 < x → ∀ z ∈ closedBall (0 : ℂ) (B + 1),
      ‖shiftedAbelExtension branch x z‖ ≤ K * Real.log x :=
    fun x hx z hz => (hbranch x hx).2.2 _ (shifted_mem_branch_ball x B hz)
  have hnodes : ∀ δ ∈ hermiteNodeNeighborhood (ι := ι) B,
      ∀ i, δ i ∈ ball (0 : ℂ) (B + 1) := by
    intro δ hδ i
    have hi := hδ i
    have ht : ‖δ i‖ < B + 1 := by linarith
    simpa only [mem_ball, dist_zero_right] using ht
  have hdegree : ∀ x δ, (abelHermitePolynomial branch B m x δ).natDegree < totalMultiplicity m := by
    intro x δ
    simpa only [abelHermitePolynomial, nodePolynomial_natDegree] using
      hermiteContourPolynomial_natDegree_lt (shiftedAbelExtension branch x)
        (nodePolynomial δ m) (B + 1) (by simpa only [nodePolynomial_natDegree] using hd)
  have hjets : ∀ x, X0 < x → ∀ δ ∈ hermiteNodeNeighborhood B,
      ∀ (ξ : ℂ) (r : ℕ), r < nodeMultiplicity δ m ξ →
        iteratedDeriv r (shiftedAbelExtension branch x) ξ =
          iteratedDeriv r (fun z => (abelHermitePolynomial branch B m x δ).eval z) ξ :=
    fun x hx δ hδ _ _ hr => hermiteContour_interpolates_combined δ m hR
      (hshift x hx) (hnodes δ hδ) hd hr
  refine ⟨X0, K, D * K, branch, {
    threshold_gt_one := hX0
    extensionConstant_pos := hK
    coefficientConstant_pos := mul_pos hD hK
    neighborhood_open := isOpen_hermiteNodeNeighborhood hB
    neighborhood_bounded := isBounded_hermiteNodeNeighborhood hB
    neighborhood_contains := closed_nodes_subset_hermiteNodeNeighborhood B
    branch_analytic := fun x hx => (hbranch x hx).1
    branch_realAgreement := fun x hx => (hbranch x hx).2.1
    branch_bound := fun x hx => (hbranch x hx).2.2
    branch_compatible := hcompat
    shifted_analytic := hshift
    shifted_realAgreement := hreal
    shifted_bound := hbound
    coefficient_analytic := ?_
    coefficient_bound := ?_
    degree_bound := ?_
    normalized_expansion := ?_
    combined_jets := hjets
    combined_jets_explicit := ?_
    constant_coefficient := ?_ }⟩
  · intro x hx j hj δ hδ
    exact analyticAt_normalized_hermiteContourCoeff (B + 1) hR.le m j hj
      (shiftedAbelExtension branch x) ((hshift x hx).continuousOn.mono sphere_subset_closedBall) δ
      (fun _ hz => nodePolynomial_eval_ne_zero_on_sphere δ m (hnodes δ hδ) hz)
  · intro x hx δ hδ j hj
    have hx1 : 1 < x := hX0.trans hx
    have hS : 0 ≤ K * Real.log x := mul_nonneg hK.le (Real.log_nonneg hx1.le)
    have hb := (hcoeff δ (shiftedAbelExtension branch x) (K * Real.log x)
      (fun i => (hδ i).le) hS
      (fun z hz => hbound x hx z (by simpa only [mem_closedBall, dist_zero_right] using hz.le))
      j hj).2
    have hlog : Real.log x ≤ 1 + x := (Real.log_le_self (by linarith)).trans (by linarith)
    calc
      _ ≤ D * (K * Real.log x) := hb
      _ = (D * K) * Real.log x := by ring
      _ ≤ (D * K) * (1 + x) := mul_le_mul_of_nonneg_left hlog (mul_pos hD hK).le
  · intro x _ δ _
    exact hermiteContour_node_degree_lt (shiftedAbelExtension branch x) δ m (B + 1)
  · intro x _ δ _ z
    exact polynomial_eval_normalized _ (hdegree x δ) z
  · intro x hx δ hδ ξ r hr
    rw [hjets x hx δ hδ ξ r hr]
    exact polynomial_iteratedDeriv_normalized _ (hdegree x δ)
      (hr.trans_le (nodeMultiplicity_le_totalMultiplicity δ m ξ)) ξ
  · intro x hx δ hδ i hi hmi
    have hc := hermiteContour_coeff_zero δ m hR (hshift x hx) (hnodes δ hδ) hd hi hmi
    have hzero := hreal x hx 0 (by simpa using hR.le)
    simpa only [abelHermiteCoeff, normalizedCoeff, Nat.factorial_zero, Nat.cast_one, one_mul,
      abelHermitePolynomial, hc, Complex.ofReal_zero, add_zero] using hzero

end IsAbel

end AbelFormalization
