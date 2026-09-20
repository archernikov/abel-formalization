import AbelFormalization.AnalyticGermComposition
import AbelFormalization.AnalyticGermDomain
import Mathlib.RingTheory.KrullDimension.Basic

/-! # A coordinate prime chain in the analytic-germ ring

Setting successively more coordinates to zero gives a chain of prime kernels.
The coordinate germs make every inclusion strict, proving the lower bound on
Krull dimension without a Noetherian hypothesis.
-/

noncomputable section

open Filter
open scoped Topology

namespace AbelFormalization

/-- Set the first `k` coordinates of a real tuple to zero. -/
def zeroPrefixLinear (p k : ℕ) : (Fin p → ℝ) →L[ℝ] (Fin p → ℝ) :=
  ContinuousLinearMap.pi (fun i => if i.val < k then 0 else ContinuousLinearMap.proj i)

@[simp]
theorem zeroPrefixLinear_apply (p k : ℕ) (x : Fin p → ℝ) (i : Fin p) :
    zeroPrefixLinear p k x i = if i.val < k then 0 else x i := by
  by_cases hi : i.val < k <;> simp [zeroPrefixLinear, hi]

theorem zeroPrefixLinear_comp_of_le (p : ℕ) {k l : ℕ} (hkl : k ≤ l)
    (x : Fin p → ℝ) :
    zeroPrefixLinear p k (zeroPrefixLinear p l x) = zeroPrefixLinear p l x := by
  funext i
  by_cases hi : i.val < k
  · have hil : i.val < l := lt_of_lt_of_le hi hkl
    simp [hi, hil]
  · simp [hi]

/-- Restrict a germ by setting the first `k` coordinates to zero, still viewing
the result as a germ in the original `p` variables. -/
def analyticGermKillPrefix (p k : ℕ) : RealAnalyticGerm p →ₐ[ℝ] RealAnalyticGerm p :=
  analyticGermPullback (zeroPrefixLinear p k) ((zeroPrefixLinear p k).analyticAt 0) (map_zero _)

theorem analyticGermKillPrefix_comp_of_le (p : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    (analyticGermKillPrefix p l).comp (analyticGermKillPrefix p k) =
      analyticGermKillPrefix p l := by
  apply AlgHom.ext
  intro g
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
  simp only [AlgHom.comp_apply, analyticGermKillPrefix, analyticGermPullback_of]
  rw [analyticGermOf_eq_iff]
  filter_upwards with x
  exact congrArg f (zeroPrefixLinear_comp_of_le p hkl x)

/-- The prime ideal of germs vanishing on the coordinate subspace. -/
def analyticGermCoordinatePrime (p k : ℕ) : PrimeSpectrum (RealAnalyticGerm p) :=
  ⟨RingHom.ker (analyticGermKillPrefix p k), RingHom.ker_isPrime _⟩

theorem analyticGermCoordinatePrime_mono (p : ℕ) :
    Monotone (analyticGermCoordinatePrime p) := by
  intro k l hkl
  change RingHom.ker (analyticGermKillPrefix p k) ≤ RingHom.ker (analyticGermKillPrefix p l)
  intro g hg
  change analyticGermKillPrefix p k g = 0 at hg
  change analyticGermKillPrefix p l g = 0
  have he := congrArg (fun h : RealAnalyticGerm p →ₐ[ℝ] RealAnalyticGerm p => h g)
    (analyticGermKillPrefix_comp_of_le p hkl)
  simpa only [AlgHom.comp_apply, hg, map_zero] using he.symm

@[simp]
theorem analyticGermKillPrefix_coordinate (p k : ℕ) (i : Fin p) :
    analyticGermKillPrefix p k (analyticGermCoordinate p i) =
      if i.val < k then 0 else analyticGermCoordinate p i := by
  unfold analyticGermCoordinate analyticGermKillPrefix
  rw [analyticGermPullback_of]
  split_ifs with hi
  · rw [analyticGermOf_eq_zero_iff]
    filter_upwards with x
    change zeroPrefixLinear p k x i = 0
    simp [hi]
  · rw [analyticGermOf_eq_iff]
    filter_upwards with x
    change zeroPrefixLinear p k x i = x i
    simp [hi]

/-- A coordinate germ is nonzero, as witnessed by its coordinate derivative. -/
theorem analyticGermCoordinate_ne_zero (p : ℕ) (i : Fin p) :
    analyticGermCoordinate p i ≠ 0 := by
  intro h
  have he := congrArg (analyticGermPartial p i) h
  simp only [analyticGermPartial_coordinate, ite_true, map_one, map_zero] at he
  exact one_ne_zero he

/-- Each newly killed coordinate makes the prime kernel strictly larger. -/
theorem analyticGermCoordinatePrime_lt_succ (p : ℕ) (i : Fin p) :
    analyticGermCoordinatePrime p i.val < analyticGermCoordinatePrime p (i.val + 1) := by
  refine lt_of_le_of_ne (analyticGermCoordinatePrime_mono p (Nat.le_succ _)) ?_
  intro he
  have hm : analyticGermCoordinate p i ∈
      (analyticGermCoordinatePrime p (i.val + 1)).asIdeal := by
    change analyticGermKillPrefix p (i.val + 1) (analyticGermCoordinate p i) = 0
    simp
  rw [← he] at hm
  change analyticGermKillPrefix p i.val (analyticGermCoordinate p i) = 0 at hm
  exact analyticGermCoordinate_ne_zero p i (by simpa using hm)

/-- The explicit coordinate prime chain has length exactly `p`. -/
def analyticGermCoordinatePrimeChain (p : ℕ) : LTSeries (PrimeSpectrum (RealAnalyticGerm p)) where
  length := p
  toFun i := analyticGermCoordinatePrime p i.val
  step i := analyticGermCoordinatePrime_lt_succ p i

/-- The actual ring of analytic germs in `p` real variables has Krull dimension
at least `p`; no finiteness or Noetherian assumption is used. -/
theorem realAnalyticGerm_dimension_lower (p : ℕ) :
    (p : WithBot ℕ∞) ≤ ringKrullDim (RealAnalyticGerm p) :=
  Order.LTSeries.length_le_krullDim (analyticGermCoordinatePrimeChain p)

end AbelFormalization
