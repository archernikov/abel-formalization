import AbelFormalization.WeightedSeriesDivision
import AbelFormalization.WeightedSeriesEvaluationMap
import Mathlib.Analysis.Analytic.Basic

/-! # Weighted coefficient representatives of actual analytic functions

A convergent multilinear expansion in finitely many real coordinates gives
an absolutely summable coefficient series on a sufficiently small polydisk.
Each homogeneous term is expanded over finite words of coordinate indices.
-/

noncomputable section

open Filter Finset
open scoped Topology NNReal ENNReal

namespace AbelFormalization

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Expand the diagonal value in the standard coordinate basis, without
requiring symmetry of the multilinear map. -/
theorem multilinear_diagonal_eq_coordinate_sum {n : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => σ → ℝ) ℝ)
    (x : σ → ℝ) :
    L (fun _ => x) = ∑ w : Fin n → σ,
      L (fun i => Pi.single (w i) 1) * ∏ i, x (w i) := by
  classical
  calc
    L (fun _ => x) = L (fun _ : Fin n => ∑ j : σ, x j • Pi.single j 1) := by
      congr 1
      funext i
      exact pi_eq_sum_univ' x
    _ = ∑ w : Fin n → σ, L (fun i => x (w i) • Pi.single (w i) 1) :=
      L.map_sum (fun _ j => x j • Pi.single j 1)
    _ = _ := by simp only [L.map_smul_univ, smul_eq_mul, mul_comm]

/-- The coordinate expansion of a continuous multilinear map, regarded as a
polynomial in the weighted Banach algebra. -/
def weightedMultilinearPolynomial {n : ℕ} (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => σ → ℝ) ℝ) :
    WeightedSeries ρ hρ :=
  ∑ w : Fin n → σ,
    L (fun i => Pi.single (w i) 1) • ∏ i, weightedSeriesX ρ hρ (w i)

/-- Multilinear coefficients evaluated on coordinate unit vectors are bounded
by the operator norm. -/
theorem norm_multilinear_coordinate_coefficient_le {n : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => σ → ℝ) ℝ)
    (w : Fin n → σ) : ‖L (fun i => Pi.single (w i) 1)‖ ≤ ‖L‖ := by
  simpa only [Pi.norm_single, norm_one, prod_const_one, mul_one] using
    L.le_opNorm (fun i => Pi.single (w i) 1)

/-- The homogeneous polynomial has the geometric majorant required for
summation of an actual analytic expansion. -/
theorem weightedMultilinearPolynomial_norm_le {n : ℕ} (r : ℝ) (hr : 0 < r)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => σ → ℝ) ℝ) :
    ‖weightedMultilinearPolynomial (fun _ => r) (fun _ => hr) L‖ ≤
      ‖L‖ * ((Fintype.card σ : ℝ) * r) ^ n := by
  classical
  have hX : ∀ i : σ, ‖weightedSeriesX (fun _ : σ => r) (fun _ => hr) i‖ = r := by
    intro i
    simp [weightedSeriesX, multiRadiusWeight_single]
  unfold weightedMultilinearPolynomial
  calc
    ‖∑ w : Fin n → σ,
        L (fun i => Pi.single (w i) 1) • ∏ i, weightedSeriesX (fun _ => r) (fun _ => hr) (w i)‖
      ≤ ∑ w : Fin n → σ,
        ‖L (fun i => Pi.single (w i) 1) •
          ∏ i, weightedSeriesX (fun _ => r) (fun _ => hr) (w i)‖ := norm_sum_le _ _
    _ ≤ ∑ _w : Fin n → σ, ‖L‖ * r ^ n := by
      apply sum_le_sum
      intro w _
      rw [norm_smul]
      apply mul_le_mul (norm_multilinear_coordinate_coefficient_le L w)
        (show ‖∏ i, weightedSeriesX (fun _ => r) (fun _ => hr) (w i)‖ ≤ r ^ n from ?_)
        (norm_nonneg _) (norm_nonneg _)
      simpa only [hX, prod_const, card_univ, Fintype.card_fin] using
        norm_prod_le (univ : Finset (Fin n))
          (fun i => weightedSeriesX (fun _ => r) (fun _ => hr) (w i))
    _ = ‖L‖ * ((Fintype.card σ : ℝ) * r) ^ n := by
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, mul_pow]
      ring

/-- A sufficiently small constant polyradius makes the homogeneous coordinate
polynomials of a convergent multilinear series summable in the Banach algebra. -/
theorem weightedMultilinearPolynomial_summable
    (P : FormalMultilinearSeries ℝ (σ → ℝ) ℝ)
    (s : ℝ≥0) (hs : (s : ℝ≥0∞) < P.radius)
    (r : ℝ) (hr : 0 < r) (hrs : (Fintype.card σ : ℝ) * r ≤ s) :
    Summable (fun n => weightedMultilinearPolynomial (fun _ => r) (fun _ => hr) (P n)) := by
  apply Summable.of_norm
  apply (P.summable_norm_mul_pow hs).of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  exact (weightedMultilinearPolynomial_norm_le r hr (P n)).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg (Fintype.card σ)) hr.le) hrs n)
      (norm_nonneg _))

/-- Evaluation of the coefficient polynomial recovers exactly the diagonal
multilinear term. -/
theorem weightedMultilinearPolynomial_eval {n : ℕ}
    (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin n => σ → ℝ) ℝ)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ ρ i) :
    weightedSeriesEval (weightedMultilinearPolynomial ρ hρ L).val x = L (fun _ => x) := by
  classical
  change weightedSeriesEvalAlgHom ρ hρ x hx (weightedMultilinearPolynomial ρ hρ L) = _
  simp only [weightedMultilinearPolynomial, map_sum, map_smul, map_prod,
    weightedSeriesEvalAlgHom_apply, weightedSeriesX_val, weightedSeriesEval_X, smul_eq_mul]
  exact (multilinear_diagonal_eq_coordinate_sum L x).symm

/-- Every actual real analytic function germ in finitely many variables has a
representative in a weighted absolutely summable coefficient Banach algebra.
The summability radius is derived from its convergent multilinear expansion. -/
theorem analyticAt_exists_weightedSeries_representation {f : (σ → ℝ) → ℝ}
    (hf : AnalyticAt ℝ f 0) :
    ∃ (r : ℝ) (hr : 0 < r), ∃ S : WeightedSeries (fun _ : σ => r) (fun _ => hr),
      (fun x => weightedSeriesEval S.val x) =ᶠ[𝓝 0] f := by
  obtain ⟨P, R, hP⟩ := hf
  obtain ⟨s, hs0, hsR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hP.r_pos
  have hs : 0 < (s : ℝ) := by exact_mod_cast hs0
  let r : ℝ := s / ((Fintype.card σ : ℝ) + 1)
  have hr : 0 < r := div_pos hs (by positivity)
  have hrs : (Fintype.card σ : ℝ) * r ≤ s := by
    dsimp [r]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (Fintype.card σ : ℝ) + 1)]
    nlinarith
  have hsum : Summable (fun n =>
      weightedMultilinearPolynomial (fun _ : σ => r) (fun _ => hr) (P n)) :=
    weightedMultilinearPolynomial_summable P s (hsR.trans_le hP.r_le) r hr hrs
  let S : WeightedSeries (fun _ : σ => r) (fun _ => hr) :=
    ∑' n, weightedMultilinearPolynomial (fun _ => r) (fun _ => hr) (P n)
  refine ⟨r, hr, S, ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : σ → ℝ) hr, hP.eventually_hasSum]
    with x hx hactual
  have hxr : ∀ i, |x i| ≤ r := by
    intro i
    exact (show |x i| ≤ ‖x‖ from norm_le_pi_norm x i).trans
      (show ‖x‖ < r from by simpa only [Metric.mem_ball, dist_zero_right] using hx).le
  calc
    weightedSeriesEval S.val x =
        ∑' n, weightedSeriesEval
          (weightedMultilinearPolynomial (fun _ => r) (fun _ => hr) (P n)).val x := by
      exact (weightedSeriesEvalCLM (fun _ => r) (fun _ => hr) x hxr).map_tsum hsum
    _ = ∑' n, P n (fun _ => x) := by
      apply tsum_congr
      intro n
      exact weightedMultilinearPolynomial_eval _ _ _ x hxr
    _ = f x := by simpa only [zero_add] using hactual.tsum_eq

end AbelFormalization
