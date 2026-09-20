import AbelFormalization.HermiteInterpolation
import AbelFormalization.NormalizedPolynomial
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Scaling Hermite interpolants

Nonzero complex scaling preserves the combined multiplicity of every node.
Local equality `f(z) = g(q*z)` therefore identifies the two interpolating
polynomials by uniqueness. Their factorial-normalized coefficients differ by
the factor `q^r`, independently of the contours used to construct them.
-/

noncomputable section

open Set Filter Metric Polynomial
open scoped Topology

namespace AbelFormalization

/-- Complex scalar substitution commutes with iterated derivatives, including
zero scale, without a differentiability hypothesis. -/
theorem iteratedDeriv_comp_mul_complex (f : ℂ → ℂ) (q : ℂ) (r : ℕ) :
    iteratedDeriv r (fun z => f (q * z)) =
      fun z => q ^ r * iteratedDeriv r f (q * z) := by
  induction r with
  | zero => simp
  | succ r ih =>
    funext z
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul, ← iteratedDeriv_succ, pow_succ]
    ring

/-- Polynomial substitution by a scalar multiple of `X` rescales each
factorial-normalized coefficient by the corresponding power. -/
theorem normalizedCoeff_comp_scale (P : ℂ[X]) (q : ℂ) (r : ℕ) :
    normalizedCoeff (P.comp (C q * X)) r = q ^ r * normalizedCoeff P r := by
  simp only [normalizedCoeff, comp_C_mul_X_coeff]
  ring

theorem degree_comp_scale (P : ℂ[X]) {q : ℂ} (hq : q ≠ 0) :
    (P.comp (C q * X)).degree = P.degree := by
  rw [Polynomial.degree_comp (by simp [degree_C_mul_X hq]), degree_C_mul_X hq, mul_one]

variable {ι : Type*} [Fintype ι]

/-- Nonzero scaling preserves collisions and their summed multiplicities. -/
theorem nodeMultiplicity_scale (δ : ι → ℂ) (m : ι → ℕ) {q : ℂ} (hq : q ≠ 0)
    (ξ : ℂ) :
    nodeMultiplicity (fun i => q * δ i) m (q * ξ) = nodeMultiplicity δ m ξ := by
  classical
  simp only [nodeMultiplicity, mul_right_inj' hq]

/-- A local scaling identity at every supplied node identifies any pair of
Hermite interpolants. No distinctness of the nodes is required. -/
theorem polynomial_eq_comp_scale_of_grouped_jets
    (δ : ι → ℂ) (m : ι → ℕ) {q : ℂ} (hq : q ≠ 0)
    {f g : ℂ → ℂ} {P Q : ℂ[X]}
    (hPdegree : P.degree < (totalMultiplicity m : WithBot ℕ))
    (hQdegree : Q.degree < (totalMultiplicity m : WithBot ℕ))
    (hPjets : ∀ ξ r, r < nodeMultiplicity δ m ξ →
      iteratedDeriv r f ξ = iteratedDeriv r (fun z => P.eval z) ξ)
    (hQjets : ∀ ξ r, r < nodeMultiplicity (fun i => q * δ i) m ξ →
      iteratedDeriv r g ξ = iteratedDeriv r (fun z => Q.eval z) ξ)
    (hlocal : ∀ i, f =ᶠ[𝓝 (δ i)] fun z => g (q * z)) :
    P = Q.comp (C q * X) := by
  apply polynomial_eq_of_grouped_jets δ m hPdegree
    (by simpa only [degree_comp_scale Q hq] using hQdegree)
  intro ξ r hr
  obtain ⟨i, hi, _⟩ := (nodeMultiplicity_pos_iff δ m ξ).mp
    ((Nat.zero_le r).trans_lt hr)
  have he : f =ᶠ[𝓝 ξ] fun z => g (q * z) := hi ▸ hlocal i
  have hscaled : r < nodeMultiplicity (fun i => q * δ i) m (q * ξ) := by
    rwa [nodeMultiplicity_scale δ m hq]
  have heval : (fun z => (Q.comp (C q * X)).eval z) =
      (fun z => Q.eval (q * z)) := by
    funext z
    simp
  rw [heval, iteratedDeriv_comp_mul_complex (fun z => Q.eval z) q r]
  calc
    _ = iteratedDeriv r f ξ := (hPjets ξ r hr).symm
    _ = iteratedDeriv r (fun z => g (q * z)) ξ := he.iteratedDeriv_eq r
    _ = q ^ r * iteratedDeriv r g (q * ξ) :=
      congrFun (iteratedDeriv_comp_mul_complex g q r) ξ
    _ = _ := congrArg (fun v => q ^ r * v) (hQjets (q * ξ) r hscaled)

/-- The coefficient form of local scaling for arbitrary interpolants. -/
theorem normalizedCoeff_scale_of_grouped_jets
    (δ : ι → ℂ) (m : ι → ℕ) {q : ℂ} (hq : q ≠ 0)
    {f g : ℂ → ℂ} {P Q : ℂ[X]}
    (hPdegree : P.degree < (totalMultiplicity m : WithBot ℕ))
    (hQdegree : Q.degree < (totalMultiplicity m : WithBot ℕ))
    (hPjets : ∀ ξ r, r < nodeMultiplicity δ m ξ →
      iteratedDeriv r f ξ = iteratedDeriv r (fun z => P.eval z) ξ)
    (hQjets : ∀ ξ r, r < nodeMultiplicity (fun i => q * δ i) m ξ →
      iteratedDeriv r g ξ = iteratedDeriv r (fun z => Q.eval z) ξ)
    (hlocal : ∀ i, f =ᶠ[𝓝 (δ i)] fun z => g (q * z)) (r : ℕ) :
    normalizedCoeff P r = q ^ r * normalizedCoeff Q r := by
  rw [polynomial_eq_comp_scale_of_grouped_jets δ m hq
    hPdegree hQdegree hPjets hQjets hlocal, normalizedCoeff_comp_scale]

/-- Contour interpolants constructed on two independent radii satisfy the
same polynomial scaling identity whenever their target functions do locally. -/
theorem hermiteContourPolynomial_scale
    (δ : ι → ℂ) (m : ι → ℕ) {q : ℂ} (hq : q ≠ 0)
    {f g : ℂ → ℂ} {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hg : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) S))
    (hδ : ∀ i, δ i ∈ ball (0 : ℂ) R)
    (hqδ : ∀ i, q * δ i ∈ ball (0 : ℂ) S) (hd : 0 < totalMultiplicity m)
    (hlocal : ∀ i, f =ᶠ[𝓝 (δ i)] fun z => g (q * z)) :
    hermiteContourPolynomial f (nodePolynomial δ m) R =
      (hermiteContourPolynomial g (nodePolynomial (fun i => q * δ i) m) S).comp
        (C q * X) := by
  apply polynomial_eq_comp_scale_of_grouped_jets δ m hq
    (hermiteContour_node_degree_lt f δ m R)
    (hermiteContour_node_degree_lt g (fun i => q * δ i) m S)
  · exact fun _ _ hr => hermiteContour_interpolates_combined δ m hR hf hδ hd hr
  · exact fun _ _ hr => hermiteContour_interpolates_combined
      (fun i => q * δ i) m hS hg hqδ hd hr
  · exact hlocal

/-- The manuscript's coefficient scaling identity, with arbitrary independent
contour radii and with colliding nodes allowed. -/
theorem hermiteContour_normalizedCoeff_scale
    (δ : ι → ℂ) (m : ι → ℕ) {q : ℂ} (hq : q ≠ 0)
    {f g : ℂ → ℂ} {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R))
    (hg : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) S))
    (hδ : ∀ i, δ i ∈ ball (0 : ℂ) R)
    (hqδ : ∀ i, q * δ i ∈ ball (0 : ℂ) S) (hd : 0 < totalMultiplicity m)
    (hlocal : ∀ i, f =ᶠ[𝓝 (δ i)] fun z => g (q * z)) (r : ℕ) :
    normalizedCoeff (hermiteContourPolynomial f (nodePolynomial δ m) R) r =
      q ^ r * normalizedCoeff
        (hermiteContourPolynomial g (nodePolynomial (fun i => q * δ i) m) S) r := by
  rw [hermiteContourPolynomial_scale δ m hq hR hS hf hg hδ hqδ hd hlocal,
    normalizedCoeff_comp_scale]

end AbelFormalization
