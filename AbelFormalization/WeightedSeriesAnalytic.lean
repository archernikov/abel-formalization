import AbelFormalization.WeightedSeriesEvaluation
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin

/-! # Analytic expansions of absolutely summable coefficient series

Each multivariate monomial is the diagonal of a continuous multilinear map.
Grouping these maps by total degree supplies the actual convergent analytic
expansion of a weighted summable coefficient series.
-/

noncomputable section

open scoped BigOperators ENNReal

namespace AbelFormalization

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- An ordered representative of a symmetric word. -/
def symmetricWord {n : ℕ} (s : Sym σ n) : Fin n → σ :=
  fun j => (s : Multiset σ).toList.get
    (Fin.cast (by rw [Multiset.length_toList]; exact s.property.symm) j)

omit [Fintype σ] in
theorem multiRadiusWeight_toFinsupp (x : σ → ℝ) (s : Multiset σ) :
    multiRadiusWeight x s.toFinsupp = (s.map x).prod := by
  classical
  rw [← Multiset.toFinsupp_toMultiset s, Finsupp.toMultiset_map,
    Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index]
  · simp only [Finsupp.toMultiset_toFinsupp]
    rfl
  · intro b
    exact pow_zero b
  · intro b m n
    exact pow_add b m n

omit [Fintype σ] in
theorem symmetricWord_prod {n : ℕ} (s : Sym σ n) (x : σ → ℝ) :
    (∏ j, x (symmetricWord s j)) = multiRadiusWeight x (s : Multiset σ).toFinsupp := by
  classical
  rw [multiRadiusWeight_toFinsupp]
  have he : n = (s : Multiset σ).toList.length := by
    rw [Multiset.length_toList]
    exact s.property.symm
  calc
    _ = ∏ j : Fin (s : Multiset σ).toList.length,
        x ((s : Multiset σ).toList.get j) :=
      Fintype.prod_equiv (finCongr he) _ _ (fun _ => rfl)
    _ = ((s : Multiset σ).toList.map x).prod := by
      simp
    _ = ((s : Multiset σ).map x).prod := by
      rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]

/-- A norm-at-most-one multilinear realization of a monomial. -/
def symmetricMonomialMap {n : ℕ} (s : Sym σ n) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => σ → ℝ) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
    (fun j => ContinuousLinearMap.proj (symmetricWord s j))

omit [Fintype σ] [DecidableEq σ] in
@[simp]
theorem symmetricMonomialMap_apply {n : ℕ} (s : Sym σ n)
    (v : Fin n → σ → ℝ) : symmetricMonomialMap s v = ∏ j, v j (symmetricWord s j) := rfl

omit [Fintype σ] in
theorem symmetricMonomialMap_diagonal {n : ℕ} (s : Sym σ n) (x : σ → ℝ) :
    symmetricMonomialMap s (fun _ => x) =
      multiRadiusWeight x (s : Multiset σ).toFinsupp :=
  symmetricWord_prod s x

omit [DecidableEq σ] in
theorem symmetricMonomialMap_norm_le {n : ℕ} (s : Sym σ n) :
    ‖symmetricMonomialMap s‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1)
  intro v
  simp only [symmetricMonomialMap_apply, norm_prod, one_mul]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => norm_le_pi_norm (v j) _)

/-- The homogeneous multilinear expansion associated to a coefficient series. -/
def weightedSeriesExpansion (f : MvPowerSeries σ ℝ) :
    FormalMultilinearSeries ℝ (σ → ℝ) ℝ := fun n =>
  ∑ s : Sym σ n, MvPowerSeries.coeff (s : Multiset σ).toFinsupp f •
    symmetricMonomialMap s

theorem weightedSeriesExpansion_norm_le (f : MvPowerSeries σ ℝ) (n : ℕ) :
    ‖weightedSeriesExpansion f n‖ ≤
      ∑ s : Sym σ n, ‖MvPowerSeries.coeff (s : Multiset σ).toFinsupp f‖ := by
  classical
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (symmetricMonomialMap_norm_le s)

/-- All symmetric words, indexed by their degree, enumerate multiindices once. -/
def symmetricWordsEquivMultiIndex : (Σ n, Sym σ n) ≃ (σ →₀ ℕ) := by
  classical
  exact (Equiv.sigmaCongrRight fun n => Sym.equivNatSum σ n).trans
    (Equiv.sigmaFiberEquiv fun d : σ →₀ ℕ => d.sum fun _ => id)

omit [Fintype σ] in
@[simp]
theorem symmetricWordsEquivMultiIndex_apply (s : Σ n, Sym σ n) :
    symmetricWordsEquivMultiIndex s = (s.2 : Multiset σ).toFinsupp := rfl

omit [Fintype σ] [DecidableEq σ] in
theorem multiRadiusWeight_const (r : ℝ) (d : σ →₀ ℕ) :
    multiRadiusWeight (fun _ => r) d = r ^ (d.sum fun _ => id) := by
  classical
  exact Finset.prod_pow_eq_pow_sum d.support (fun i => d i) r

omit [Fintype σ] in
theorem symmetricWord_weight_const (r : ℝ) {n : ℕ} (s : Sym σ n) :
    multiRadiusWeight (fun _ => r) (s : Multiset σ).toFinsupp = r ^ n := by
  rw [multiRadiusWeight_const, ← Finsupp.card_toMultiset,
    Multiset.toFinsupp_toMultiset]
  exact congrArg (fun k => r ^ k) s.property

/-- Absolute coefficient convergence bounds the actual multilinear expansion. -/
theorem weightedSeriesExpansion_summable_norm {r : ℝ} (hr : 0 ≤ r)
    {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable (fun _ => r) f) :
    Summable (fun n => ‖weightedSeriesExpansion f n‖ * r ^ n) := by
  classical
  have hs : Summable (fun s : Σ n, Sym σ n =>
      ‖MvPowerSeries.coeff (s.2 : Multiset σ).toFinsupp f‖ * r ^ s.1) := by
    simpa only [Function.comp_def, symmetricWordsEquivMultiIndex_apply,
      symmetricWord_weight_const] using
      ((symmetricWordsEquivMultiIndex (σ := σ)).summable_iff.mpr hf)
  have hm := hs.sigma
  simp only [tsum_fintype] at hm
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (pow_nonneg hr _))
    (fun n => ?_) hm
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (weightedSeriesExpansion_norm_le f n) (pow_nonneg hr n)

/-- The formal multilinear expansion has a positive radius whenever the
coefficient series converges absolutely at a positive scalar radius. -/
theorem weightedSeriesExpansion_radius_pos {r : ℝ} (hr : 0 < r)
    {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable (fun _ => r) f) :
    0 < (weightedSeriesExpansion f).radius := by
  have h := (weightedSeriesExpansion f).le_radius_of_summable_norm
    (r := ⟨r, hr.le⟩) (weightedSeriesExpansion_summable_norm hr.le hf)
  apply lt_of_lt_of_le _ h
  exact ENNReal.coe_pos.mpr hr

theorem weightedSeriesExpansion_diagonal (f : MvPowerSeries σ ℝ) (n : ℕ) (x : σ → ℝ) :
    weightedSeriesExpansion f n (fun _ => x) =
      ∑ s : Sym σ n, MvPowerSeries.coeff (s : Multiset σ).toFinsupp f *
        multiRadiusWeight x (s : Multiset σ).toFinsupp := by
  classical
  simp only [weightedSeriesExpansion, sum_apply,
    smul_apply, smul_eq_mul, symmetricMonomialMap_diagonal]

theorem weightedSeriesExpansion_sum_eq_eval {r : ℝ} {f : MvPowerSeries σ ℝ}
    (hf : WeightedCoeffSummable (fun _ => r) f) {x : σ → ℝ}
    (hx : ∀ i, |x i| ≤ r) :
    (weightedSeriesExpansion f).sum x = weightedSeriesEval f x := by
  classical
  have hs := (weightedSeriesEval_summable hx hf)
  have ht := (symmetricWordsEquivMultiIndex (σ := σ)).summable_iff.mpr hs
  rw [FormalMultilinearSeries.sum]
  simp_rw [weightedSeriesExpansion_diagonal]
  calc
    _ = ∑' n, ∑' s : Sym σ n, MvPowerSeries.coeff (s : Multiset σ).toFinsupp f *
        multiRadiusWeight x (s : Multiset σ).toFinsupp := by simp only [tsum_fintype]
    _ = ∑' s : Σ n, Sym σ n, MvPowerSeries.coeff (s.2 : Multiset σ).toFinsupp f *
        multiRadiusWeight x (s.2 : Multiset σ).toFinsupp := ht.tsum_sigma.symm
    _ = _ := (symmetricWordsEquivMultiIndex (σ := σ)).tsum_eq
      (fun d => MvPowerSeries.coeff d f * multiRadiusWeight x d)

/-- Weighted absolute convergence supplies an actual real analytic function,
not merely a formally defined or pointwise convergent series. -/
theorem analyticAt_weightedSeriesEval {r : ℝ} (hr : 0 < r)
    {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable (fun _ => r) f) :
    AnalyticAt ℝ (weightedSeriesEval f) 0 := by
  have ha := ((weightedSeriesExpansion f).hasFPowerSeriesOnBall
    (weightedSeriesExpansion_radius_pos hr hf)).analyticAt
  apply ha.congr
  filter_upwards [Metric.ball_mem_nhds (0 : σ → ℝ) hr] with x hx
  apply weightedSeriesExpansion_sum_eq_eval hf
  intro i
  exact (norm_le_pi_norm x i).trans
    (show ‖x‖ < r from by simpa only [Metric.mem_ball, dist_zero_right] using hx).le

end AbelFormalization
