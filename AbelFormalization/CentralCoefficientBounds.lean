import AbelFormalization.CentralCoefficients
import AbelFormalization.CentralBounds
import AbelFormalization.GeneralHermiteBounds
import AbelFormalization.HermiteCoefficientAnalytic
import AbelFormalization.AnalyticRemainder

/-! # Uniform scale bounds for the central Hermite coefficients

The contour has radius `1/4`.  The scale disk below places every scaled node
inside radius `1/8`, uniformly over the allowed unscaled nodes.  The actual
contour coefficients are analytic in that scale, and their divided-difference
remainders have a uniform bound on the same scale disk.
-/

noncomputable section

open Set Filter Metric Polynomial
open scoped Topology

namespace AbelFormalization

/-- A scale radius that keeps all scaled nodes inside the half-radius disk. -/
def centralScaleRadius (B : ℝ) : ℝ := 1 / (8 * (B + 1 / 4))

theorem centralScaleRadius_pos {B : ℝ} (hB : 0 < B) : 0 < centralScaleRadius B := by
  unfold centralScaleRadius
  positivity

theorem norm_central_scaled_node_lt {B : ℝ} (hB : 0 < B) {q δ : ℂ}
    (hq : ‖q‖ < centralScaleRadius B) (hδ : ‖δ‖ ≤ B + 1 / 4) :
    ‖q * δ‖ < 1 / 8 := by
  have hpos : 0 < B + 1 / 4 := by linarith
  have he : centralScaleRadius B * (B + 1 / 4) = 1 / 8 := by
    unfold centralScaleRadius
    field_simp
  calc
    ‖q * δ‖ = ‖q‖ * ‖δ‖ := norm_mul _ _
    _ ≤ ‖q‖ * (B + 1 / 4) := mul_le_mul_of_nonneg_left hδ (norm_nonneg _)
    _ < centralScaleRadius B * (B + 1 / 4) := mul_lt_mul_of_pos_right hq hpos
    _ = 1 / 8 := he

variable {ι : Type*} [Fintype ι]

/-- Normalizing a contour coefficient preserves its full node analyticity. -/
theorem analyticAt_normalizedHermiteCoeff_nodes (R : ℝ) (hR : 0 ≤ R)
    (m : ι → ℕ) (r : ℕ) (hr : r < totalMultiplicity m)
    (f : ℂ → ℂ) (hf : ContinuousOn f (sphere (0 : ℂ) R)) (δ : ι → ℂ)
    (hQ : ∀ z ∈ sphere (0 : ℂ) R, (nodePolynomial δ m).eval z ≠ 0) :
    AnalyticAt ℂ (fun ε : ι → ℂ =>
      normalizedCoeff (hermiteContourPolynomial f (nodePolynomial ε m) R) r) δ := by
  have ha := analyticAt_const.fun_mul
    (analyticAt_hermiteContourCoeff_nodes R hR m r f hf δ hQ)
      (f := fun _ : ι → ℂ => (r.factorial : ℂ))
  apply ha.congr
  filter_upwards with ε
  dsimp only [normalizedCoeff]
  rw [hermiteContourPolynomial_coeff f (nodePolynomial ε m) R
    (by simpa only [nodePolynomial_natDegree] using hr)]

/-- The actual central coefficient is analytic in the independent scale
throughout the uniform scale disk, including scale zero. -/
theorem centralCoefficient_analyticOnNhd_scale {F : ℂ → ℂ} (m : ι → ℕ)
    {B : ℝ} (hB : 0 < B) {u : ℂ}
    (hH : AnalyticOnNhd ℂ (centralComplexFunction F u) (closedBall (0 : ℂ) (1 / 4)))
    (δ : ι → ℂ) (hδ : ∀ i, ‖δ i‖ ≤ B + 1 / 4)
    {r : ℕ} (hr : r < totalMultiplicity m) :
    AnalyticOnNhd ℂ (fun q => centralCoefficient F m (1 / 4) u q δ r)
      (ball (0 : ℂ) (centralScaleRadius B)) := by
  intro q hq
  have hqn : ‖q‖ < centralScaleRadius B := by simpa using hq
  have hscaled : ∀ i, ‖q * δ i‖ ≤ 1 / 8 :=
    fun i => (norm_central_scaled_node_lt hB hqn (hδ i)).le
  have hQ : ∀ z ∈ sphere (0 : ℂ) (1 / 4),
      (nodePolynomial (fun i => q * δ i) m).eval z ≠ 0 := by
    intro z hz
    exact nodePolynomial_ne_zero_of_radius_gap m (by norm_num : (1 / 8 : ℝ) < 1 / 4)
      hscaled (by simpa only [mem_sphere, dist_zero_right] using hz)
  have hc := analyticAt_normalizedHermiteCoeff_nodes (1 / 4) (by norm_num) m r hr
    (centralComplexFunction F u) (hH.continuousOn.mono sphere_subset_closedBall)
    (fun i => q * δ i) hQ
  have hm : AnalyticAt ℂ (fun t : ℂ => fun i => t * δ i) q :=
    AnalyticAt.pi fun _ => analyticAt_id.fun_mul analyticAt_const
  exact hc.fun_comp (f := fun t : ℂ => fun i => t * δ i) hm

/-- The analytic remainder after subtracting the zero-scale coefficient. -/
def centralRemainder (F : ℂ → ℂ) (m : ι → ℕ) (ρ : ℝ)
    (u q : ℂ) (δ : ι → ℂ) (r : ℕ) : ℂ :=
  analyticRemainder (fun t => centralCoefficient F m ρ u t δ r) q

theorem centralRemainder_identity (F : ℂ → ℂ) (m : ι → ℕ) (ρ : ℝ)
    (u q : ℂ) (δ : ι → ℂ) (r : ℕ) :
    centralCoefficient F m ρ u q δ r = centralCoefficient F m ρ u 0 δ r +
      q * centralRemainder F m ρ u q δ r :=
  analyticRemainder_identity (fun t => centralCoefficient F m ρ u t δ r) q

theorem centralRemainder_analyticOnNhd_scale {F : ℂ → ℂ} (m : ι → ℕ)
    {B : ℝ} (hB : 0 < B) {u : ℂ}
    (hH : AnalyticOnNhd ℂ (centralComplexFunction F u) (closedBall (0 : ℂ) (1 / 4)))
    (δ : ι → ℂ) (hδ : ∀ i, ‖δ i‖ ≤ B + 1 / 4)
    {r : ℕ} (hr : r < totalMultiplicity m) :
    AnalyticOnNhd ℂ (fun q => centralRemainder F m (1 / 4) u q δ r)
      (ball (0 : ℂ) (centralScaleRadius B)) :=
  analyticOnNhd_analyticRemainder (centralScaleRadius_pos hB)
    (centralCoefficient_analyticOnNhd_scale m hB hH δ hδ hr)

/-- Uniform bounds for the central coefficients before dividing by scale. -/
theorem exists_uniform_centralCoefficient_bound (m : ι → ℕ) {B : ℝ} (hB : 0 < B) :
    ∃ D : ℝ, 0 < D ∧ ∀ (F : ℂ → ℂ) (K : ℝ) (u : ℂ) (δ : ι → ℂ),
      0 < K → 0 < u.re →
      (∀ η : ℂ, ‖η‖ < 1 / 2 → ‖centralComplexFunction F u η‖ ≤ K * (1 + u.re)) →
      (∀ i, ‖δ i‖ ≤ B + 1 / 4) →
      ∀ (q : ℂ) (r : ℕ), ‖q‖ < centralScaleRadius B → r < totalMultiplicity m →
        ‖centralCoefficient F m (1 / 4) u q δ r‖ ≤ D * K * (1 + u.re) := by
  obtain ⟨D, hD, hb⟩ := exists_uniform_normalizedHermiteCoeff_bound m
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 8 : ℝ) < 1 / 4)
  refine ⟨D, hD, ?_⟩
  intro F K u δ hK hu hH hδ q r hq hr
  have hscaled : ∀ i, ‖q * δ i‖ ≤ 1 / 8 :=
    fun i => (norm_central_scaled_node_lt hB hq (hδ i)).le
  have he := hb (fun i => q * δ i) (centralComplexFunction F u) (K * (1 + u.re))
    hscaled (by positivity) (fun η hη => hH η (by linarith)) r hr
  simpa only [centralCoefficient, mul_assoc] using he

/-- The coefficients and their analytic scale remainders are uniformly
bounded by a linear function of the real part of the center. The radius
and constants work simultaneously for every allowed node tuple and jet. -/
theorem exists_uniform_centralCoefficient_remainder_bounds (m : ι → ℕ)
    {B : ℝ} (hB : 0 < B) :
    ∃ D : ℝ, 0 < D ∧ ∀ (F : ℂ → ℂ) (K : ℝ) (u : ℂ) (δ : ι → ℂ),
      0 < K → 0 < u.re →
      AnalyticOnNhd ℂ (centralComplexFunction F u) (closedBall (0 : ℂ) (1 / 4)) →
      (∀ η : ℂ, ‖η‖ < 1 / 2 → ‖centralComplexFunction F u η‖ ≤ K * (1 + u.re)) →
      (∀ i, ‖δ i‖ ≤ B + 1 / 4) →
      ∀ r : ℕ, r < totalMultiplicity m →
        AnalyticOnNhd ℂ (fun q => centralRemainder F m (1 / 4) u q δ r)
          (ball (0 : ℂ) (centralScaleRadius B)) ∧
        ∀ q : ℂ, ‖q‖ < centralScaleRadius B →
          ‖centralCoefficient F m (1 / 4) u q δ r‖ ≤ D * K * (1 + u.re) ∧
          ‖centralRemainder F m (1 / 4) u q δ r‖ ≤
            (2 * D * K / centralScaleRadius B) * (1 + u.re) := by
  obtain ⟨D, hD, hb⟩ := exists_uniform_centralCoefficient_bound m hB
  refine ⟨D, hD, ?_⟩
  intro F K u δ hK hu hH hbound hδ r hr
  have hc := centralCoefficient_analyticOnNhd_scale m hB hH δ hδ hr
  have hcb : ∀ q ∈ ball (0 : ℂ) (centralScaleRadius B),
      ‖centralCoefficient F m (1 / 4) u q δ r‖ ≤ D * K * (1 + u.re) := by
    intro q hq
    exact hb F K u δ hK hu hbound hδ q r (by simpa using hq) hr
  refine ⟨centralRemainder_analyticOnNhd_scale m hB hH δ hδ hr, ?_⟩
  intro q hq
  have hqball : q ∈ ball (0 : ℂ) (centralScaleRadius B) := by simpa using hq
  refine ⟨hcb q hqball, ?_⟩
  have he := norm_analyticRemainder_le (centralScaleRadius_pos hB) hc hcb hqball
  change ‖centralRemainder F m (1 / 4) u q δ r‖ ≤ _ at he
  calc
    ‖centralRemainder F m (1 / 4) u q δ r‖ ≤
        2 * (D * K * (1 + u.re)) / centralScaleRadius B := he
    _ = (2 * D * K / centralScaleRadius B) * (1 + u.re) := by ring

end AbelFormalization
