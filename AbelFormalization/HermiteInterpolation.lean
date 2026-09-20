import AbelFormalization.HermiteContour
import AbelFormalization.AnalyticMultiplicity

/-! # Contour Hermite interpolation, including coincident nodes

The exact contour remainder supplies all interpolation jets.  When nodes
coincide their multiplicities add; no distinctness hypothesis is imposed.
-/

noncomputable section

open Set Filter Metric Polynomial
open scoped Topology

namespace AbelFormalization

variable {ι : Type*} [Fintype ι]

theorem multiplicity_le_nodeMultiplicity (δ : ι → ℂ) (m : ι → ℕ) (i : ι) :
    m i ≤ nodeMultiplicity δ m (δ i) := by
  classical
  exact Finset.single_le_sum_of_canonicallyOrdered
    (show i ∈ Finset.univ.filter (fun j => δ j = δ i) by simp)

theorem nodeMultiplicity_pos_iff (δ : ι → ℂ) (m : ι → ℕ) (ξ : ℂ) :
    0 < nodeMultiplicity δ m ξ ↔ ∃ i, δ i = ξ ∧ 0 < m i := by
  classical
  simp only [nodeMultiplicity, Finset.sum_pos_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- A node polynomial has no boundary zero if every node is in the disk. -/
theorem nodePolynomial_eval_ne_zero_on_sphere (δ : ι → ℂ) (m : ι → ℕ) {R : ℝ}
    (hδ : ∀ i, δ i ∈ ball (0 : ℂ) R) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) R) :
    (nodePolynomial δ m).eval ζ ≠ 0 := by
  rw [nodePolynomial_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply pow_ne_zero
  apply sub_ne_zero.mpr
  intro he
  have hs : δ i ∈ sphere (0 : ℂ) R := he ▸ hζ
  exact (ne_of_lt (mem_ball.mp (hδ i))) (mem_sphere.mp hs)

/-- The explicit contour polynomial has the required interpolation degree. -/
theorem hermiteContour_node_degree_lt (f : ℂ → ℂ) (δ : ι → ℂ) (m : ι → ℕ) (R : ℝ) :
    (hermiteContourPolynomial f (nodePolynomial δ m) R).degree <
      (totalMultiplicity m : WithBot ℕ) := by
  simpa only [nodePolynomial_natDegree] using
    hermiteContourPolynomial_degree_lt f (nodePolynomial δ m) R

/-- At any node, all derivatives below the combined multiplicity interpolate.
The positive multiplicity itself ensures that the point is one of the nodes. -/
theorem hermiteContour_interpolates_combined {f : ℂ → ℂ} (δ : ι → ℂ) (m : ι → ℕ)
    {R : ℝ} (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hδ : ∀ i, δ i ∈ ball (0 : ℂ) R) (hd : 0 < totalMultiplicity m)
    {ξ : ℂ} {r : ℕ} (hr : r < nodeMultiplicity δ m ξ) :
    iteratedDeriv r f ξ = iteratedDeriv r
      (fun z => (hermiteContourPolynomial f (nodePolynomial δ m) R).eval z) ξ := by
  obtain ⟨i, hi, _⟩ := (nodeMultiplicity_pos_iff δ m ξ).mp
    ((Nat.zero_le r).trans_lt hr)
  have hξ : ξ ∈ ball (0 : ℂ) R := hi ▸ hδ i
  have hQ : ∀ ζ ∈ sphere (0 : ℂ) R, (nodePolynomial δ m).eval ζ ≠ 0 :=
    fun _ hζ => nodePolynomial_eval_ne_zero_on_sphere δ m hδ hζ
  have hdQ : 0 < (nodePolynomial δ m).natDegree := by
    simpa only [nodePolynomial_natDegree] using hd
  apply iteratedDeriv_eq_of_nodePolynomial_remainder δ m
    (hf ξ (ball_subset_closedBall hξ))
    (hermiteContourQuotient_analyticOnNhd hR
      (hf.continuousOn.mono sphere_subset_closedBall) hQ ξ hξ) _ hr
  filter_upwards [isOpen_ball.mem_nhds hξ] with z hz
  exact hermiteContour_remainder hR hf hQ hdQ hz

/-- In particular the prescribed jet at each supplied node interpolates. -/
theorem hermiteContour_interpolates {f : ℂ → ℂ} (δ : ι → ℂ) (m : ι → ℕ)
    {R : ℝ} (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hδ : ∀ i, δ i ∈ ball (0 : ℂ) R) (hd : 0 < totalMultiplicity m)
    (i : ι) {r : ℕ} (hr : r < m i) :
    iteratedDeriv r f (δ i) = iteratedDeriv r
      (fun z => (hermiteContourPolynomial f (nodePolynomial δ m) R).eval z) (δ i) :=
  hermiteContour_interpolates_combined δ m hR hf hδ hd
    (hr.trans_le (multiplicity_le_nodeMultiplicity δ m i))

/-- A positive-multiplicity central node fixes the constant coefficient. -/
theorem hermiteContour_coeff_zero {f : ℂ → ℂ} (δ : ι → ℂ) (m : ι → ℕ)
    {R : ℝ} (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hδ : ∀ i, δ i ∈ ball (0 : ℂ) R) (hd : 0 < totalMultiplicity m)
    {i : ι} (hi : δ i = 0) (hmi : 0 < m i) :
    (hermiteContourPolynomial f (nodePolynomial δ m) R).coeff 0 = f 0 := by
  rw [coeff_zero_eq_eval_zero]
  simpa only [iteratedDeriv_zero, hi] using
    (hermiteContour_interpolates δ m hR hf hδ hd i hmi).symm

/-- Hermite interpolation exists for arbitrary finite node families, with
colliding nodes interpreted by summing their multiplicities. -/
theorem exists_hermite_interpolating_polynomial {f : ℂ → ℂ}
    (δ : ι → ℂ) (m : ι → ℕ) {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hδ : ∀ i, δ i ∈ ball (0 : ℂ) R) (hd : 0 < totalMultiplicity m) :
    ∃ P : ℂ[X], P.degree < (totalMultiplicity m : WithBot ℕ) ∧
      ∀ (ξ : ℂ) (r : ℕ), r < nodeMultiplicity δ m ξ →
        iteratedDeriv r f ξ = iteratedDeriv r (fun z => P.eval z) ξ := by
  exact ⟨hermiteContourPolynomial f (nodePolynomial δ m) R,
    hermiteContour_node_degree_lt f δ m R,
    fun _ _ hr => hermiteContour_interpolates_combined δ m hR hf hδ hd hr⟩

/-- The contour construction is the unique polynomial of the required degree
with the combined interpolation jets. -/
theorem exists_unique_hermite_interpolating_polynomial {f : ℂ → ℂ}
    (δ : ι → ℂ) (m : ι → ℕ) {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hδ : ∀ i, δ i ∈ ball (0 : ℂ) R) (hd : 0 < totalMultiplicity m) :
    ∃! P : ℂ[X], P.degree < (totalMultiplicity m : WithBot ℕ) ∧
      ∀ (ξ : ℂ) (r : ℕ), r < nodeMultiplicity δ m ξ →
        iteratedDeriv r f ξ = iteratedDeriv r (fun z => P.eval z) ξ := by
  obtain ⟨P, hPdegree, hPjets⟩ :=
    exists_hermite_interpolating_polynomial δ m hR hf hδ hd
  refine ⟨P, ⟨hPdegree, hPjets⟩, ?_⟩
  intro P' hP'
  apply polynomial_eq_of_grouped_jets δ m hP'.1 hPdegree
  intro ξ r hr
  exact (hP'.2 ξ r hr).symm.trans (hPjets ξ r hr)

end AbelFormalization
