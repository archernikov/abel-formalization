import AbelFormalization.TransferPolynomialPerturbation
import AbelFormalization.PolynomialGermIdentities

/-!
# Polynomial bounds for finite analytic coefficient families

Analytic coefficient representatives evaluated along a parameter sequence
converging to their base point are eventually bounded.  This file packages
that observation as a polynomial upper bound and consolidates finitely many
individual bounds into the uniform matrix bound used by quantitative
transfer.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Set
open scoped Topology

variable {X E ι κ : Type*}

/-- Every convergent real-valued function has a polynomial upper bound of
exponent zero, for any comparison scale. -/
theorem HasPolynomialUpperBound.of_tendsto
    {l : Filter X} {S f : X → ℝ} {a : ℝ}
    (hf : Tendsto f l (𝓝 a)) :
    HasPolynomialUpperBound l S f := by
  refine ⟨|a| + 1, by positivity, 0, ?_⟩
  have hball := hf.eventually (Metric.ball_mem_nhds a zero_lt_one)
  filter_upwards [hball] with x hx
  have hdiff : |f x - a| < 1 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hx
  have htriangle : |f x| ≤ |f x - a| + |a| := by
    have := abs_add_le (f x - a) a
    simpa only [sub_add_cancel] using this
  simpa only [pow_zero, mul_one] using htriangle.trans (by linarith)

/-- Composing a continuous function at its base point with a convergent
parameter sequence gives an exponent-zero polynomial bound. -/
theorem HasPolynomialUpperBound.of_continuousAt_comp
    {l : Filter X} {S : X → ℝ} {w : X → E} {x : E}
    [TopologicalSpace E] {f : E → ℝ}
    (hf : ContinuousAt f x) (hw : Tendsto w l (𝓝 x)) :
    HasPolynomialUpperBound l S (fun n => f (w n)) := by
  exact HasPolynomialUpperBound.of_tendsto (hf.tendsto.comp hw)

/-- An analytic coefficient on a neighborhood is bounded along every
sequence tending to the base point in that neighborhood. -/
theorem HasPolynomialUpperBound.of_analyticOnNhd_comp
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter X} {S : X → ℝ} {w : X → E} {x : E}
    {U : Set E} (hxU : x ∈ U) {f : E → ℝ}
    (hf : AnalyticOnNhd ℝ f U) (hw : Tendsto w l (𝓝 x)) :
    HasPolynomialUpperBound l S (fun n => f (w n)) := by
  exact HasPolynomialUpperBound.of_continuousAt_comp
    (hf x hxU).continuousAt hw

/-- Finitely many pointwise polynomial upper bounds can be replaced by one
constant and one exponent. -/
theorem hasUniformPolynomialUpperBound_of_finite
    [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    {l : Filter X} {S : X → ℝ} (a : κ → ι → X → ℝ)
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (ha : ∀ b i, HasPolynomialUpperBound l S (a b i)) :
    HasUniformPolynomialUpperBound l S a := by
  classical
  choose C hC P hbound using fun p : κ × ι => ha p.1 p.2
  let Ctotal : ℝ := ∑ p : κ × ι, C p
  let Ptotal : ℕ := ∑ p : κ × ι, P p
  have hCtotal : 0 < Ctotal := by
    exact Finset.sum_pos (fun p _ => hC p) Finset.univ_nonempty
  refine ⟨Ctotal, hCtotal, Ptotal, ?_⟩
  have hall : ∀ᶠ x in l, ∀ p : κ × ι,
      |a p.1 p.2 x| ≤ C p * (S x) ^ P p :=
    Filter.eventually_all.mpr (fun p => hbound p)
  filter_upwards [hS, hall] with x hxS hx
  intro b i
  let p : κ × ι := (b, i)
  have hCle : C p ≤ Ctotal := by
    apply Finset.single_le_sum
    · intro q hq
      exact (hC q).le
    · exact Finset.mem_univ p
  have hPle : P p ≤ Ptotal := by
    apply Finset.single_le_sum
    · intro q hq
      exact Nat.zero_le _
    · exact Finset.mem_univ p
  have hpow : (S x) ^ P p ≤ (S x) ^ Ptotal :=
    pow_le_pow_right₀ hxS hPle
  calc
    |a b i x| ≤ C p * (S x) ^ P p := hx p
    _ ≤ Ctotal * (S x) ^ Ptotal :=
      mul_le_mul hCle hpow (pow_nonneg (zero_le_one.trans hxS) _)
        hCtotal.le

/-- A finite matrix of analytic coefficient representatives has the uniform
bound required by generator-list transfer along any parameter sequence
converging to the common base point. -/
theorem analyticCoefficientMatrix_hasUniformPolynomialUpperBound
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype κ] [Nonempty κ] [Fintype ι] [Nonempty ι]
    {l : Filter X} {S : X → ℝ} (a : κ → ι → E → ℝ)
    {w : X → E} {x : E} {U : Set E} (hxU : x ∈ U)
    (ha : ∀ b i, AnalyticOnNhd ℝ (a b i) U)
    (hw : Tendsto w l (𝓝 x))
    (hS : ∀ᶠ n in l, 1 ≤ S n) :
    HasUniformPolynomialUpperBound l S
      (fun b i n => a b i (w n)) := by
  apply hasUniformPolynomialUpperBound_of_finite _ hS
  intro b i
  exact HasPolynomialUpperBound.of_analyticOnNhd_comp
    hxU (ha b i) hw

end AbelFormalization
