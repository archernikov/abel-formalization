import AbelFormalization.PairMergeSequenceEstimate
import AbelFormalization.ClusterBalancing
import Mathlib.Algebra.Order.Round

/-!
# Selecting the fixed pair in the all-unbounded branch

This file isolates the finite-pigeonhole step immediately preceding the
pair-merging coordinate change.  At every term, a pair in one fixed cluster
is close modulo `ℤ`.  We orient the pair by its Abel times and use
`round` to choose a nonnegative integer bounded by the cluster width.
The resulting data live in a finite type, hence become constant on a strict
subsequence.  The final theorem packages exactly the limits consumed by
`IsAbel.pairMergeCoordinates_tendsto`.
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- Integer distance is invariant under changing the sign of its argument. -/
theorem integerDistance_neg (x : ℝ) :
    integerDistance (-x) = integerDistance x := by
  unfold integerDistance
  congr 1
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨-z, ?_⟩
    push_cast
    rw [show -x - (z : ℝ) = -(x - -(z : ℝ)) by ring, abs_neg]
  · rintro ⟨z, rfl⟩
    refine ⟨-z, ?_⟩
    push_cast
    rw [show x - (z : ℝ) = -(-x - -(z : ℝ)) by ring, abs_neg]

/-- `round x` realizes the distance of `x` to the integers.  The
one-sided form is all that the pair-selection argument needs. -/
theorem abs_sub_round_le_integerDistance (x : ℝ) :
    |x - (round x : ℝ)| ≤ integerDistance x := by
  rw [le_integerDistance_iff]
  exact fun z => round_le x z

/-- If `x` lies in `[0,D]` and is within `r` of the integers, its rounded
integer is a natural number at most `D` and retains the strict bound. -/
theorem exists_bounded_nat_abs_sub_lt_of_integerDistance_lt
    {x r : ℝ} {D : ℕ} (hx0 : 0 ≤ x) (hxD : x ≤ (D : ℝ))
    (hx : integerDistance x < r) :
    ∃ k : ℕ, k ≤ D ∧ |x - (k : ℝ)| < r := by
  let z : ℤ := round x
  have hz0 : 0 ≤ z := by
    dsimp only [z]
    rw [round_eq]
    exact Int.floor_nonneg.mpr (by linarith)
  have hzlt : z < (D : ℤ) + 1 := by
    have hzR : (z : ℝ) < (D : ℝ) + 1 := by
      have hzhalf : (z : ℝ) ≤ x + 1 / 2 := round_le_add_half x
      linarith
    exact_mod_cast hzR
  let k : ℕ := z.toNat
  have hkcast : (k : ℤ) = z := by
    dsimp only [k]
    exact Int.toNat_of_nonneg hz0
  have hkD : k ≤ D := by
    omega
  refine ⟨k, hkD, ?_⟩
  have hkR : (k : ℝ) = (z : ℝ) := by exact_mod_cast hkcast
  rw [hkR]
  exact (abs_sub_round_le_integerDistance x).trans_lt hx

/-- Orient a near-integer pair inside a width-`D` cluster and replace its
integer witness by a bounded natural number. -/
theorem exists_oriented_bounded_nearInteger_pair
    {m : ℕ} (a : Fin m → ℝ) (t r : ℝ) (D : ℕ)
    (α : Finset (Fin m))
    (hcluster : ∀ i ∈ α, t ≤ a i ∧ a i ≤ t + (D : ℝ))
    (hnear : ∃ i ∈ α, ∃ j ∈ α, i ≠ j ∧
      integerDistance (a i - a j) < r) :
    ∃ i ∈ α, ∃ j ∈ α, i ≠ j ∧ a j ≤ a i ∧
      ∃ k : ℕ, k ≤ D ∧ |a i - a j - (k : ℝ)| < r := by
  obtain ⟨i, hi, j, hj, hij, hdist⟩ := hnear
  rcases le_total (a j) (a i) with hji | hijOrder
  · have hx0 : 0 ≤ a i - a j := sub_nonneg.mpr hji
    have hxD : a i - a j ≤ (D : ℝ) := by
      obtain ⟨_, hiUpper⟩ := hcluster i hi
      obtain ⟨hjLower, _⟩ := hcluster j hj
      linarith
    obtain ⟨k, hkD, hk⟩ :=
      exists_bounded_nat_abs_sub_lt_of_integerDistance_lt hx0 hxD hdist
    exact ⟨i, hi, j, hj, hij, hji, k, hkD, hk⟩
  · have hx0 : 0 ≤ a j - a i := sub_nonneg.mpr hijOrder
    have hxD : a j - a i ≤ (D : ℝ) := by
      obtain ⟨_, hjUpper⟩ := hcluster j hj
      obtain ⟨hiLower, _⟩ := hcluster i hi
      linarith
    have hdist' : integerDistance (a j - a i) < r := by
      rw [show a j - a i = -(a i - a j) by ring, integerDistance_neg]
      exact hdist
    obtain ⟨k, hkD, hk⟩ :=
      exists_bounded_nat_abs_sub_lt_of_integerDistance_lt hx0 hxD hdist'
    exact ⟨j, hj, i, hi, hij.symm, hijOrder, k, hkD, hk⟩

/-- A fixed pair and bounded integer can be selected from pointwise
near-integer witnesses in one finite cluster.  The strict subsequence keeps
the orientation and the near-integer inequality at every term. -/
theorem exists_fixed_nearInteger_pair_subsequence
    {m : ℕ} (a : ℕ → Fin m → ℝ) (t radius : ℕ → ℝ) (D : ℕ)
    (α : Finset (Fin m))
    (hcluster : ∀ n i, i ∈ α →
      t n ≤ a n i ∧ a n i ≤ t n + (D : ℝ))
    (hnear : ∀ n, ∃ i ∈ α, ∃ j ∈ α, i ≠ j ∧
      integerDistance (a n i - a n j) < radius n) :
    ∃ (i j : Fin m) (k : ℕ) (φ : ℕ → ℕ),
      i ∈ α ∧ j ∈ α ∧ i ≠ j ∧ k ≤ D ∧ StrictMono φ ∧
      (∀ n, a (φ n) j ≤ a (φ n) i) ∧
      (∀ n, |a (φ n) i - a (φ n) j - (k : ℝ)| < radius (φ n)) := by
  classical
  let Code := (Fin m × Fin m) × Fin (D + 1)
  have hwitness (n : ℕ) :
      ∃ c : Code,
        c.1.1 ∈ α ∧ c.1.2 ∈ α ∧ c.1.1 ≠ c.1.2 ∧
        a n c.1.2 ≤ a n c.1.1 ∧
        |a n c.1.1 - a n c.1.2 - (c.2 : ℝ)| < radius n := by
    obtain ⟨i, hi, j, hj, hij, hji, k, hkD, hk⟩ :=
      exists_oriented_bounded_nearInteger_pair
        (a n) (t n) (radius n) D α (hcluster n) (hnear n)
    exact ⟨((i, j), ⟨k, Nat.lt_succ_iff.mpr hkD⟩), hi, hj, hij, hji, hk⟩
  let code : ℕ → Code := fun n => Classical.choose (hwitness n)
  have hcode (n : ℕ) :
      (code n).1.1 ∈ α ∧ (code n).1.2 ∈ α ∧
      (code n).1.1 ≠ (code n).1.2 ∧
      a n (code n).1.2 ≤ a n (code n).1.1 ∧
      |a n (code n).1.1 - a n (code n).1.2 - ((code n).2 : ℝ)| < radius n :=
    Classical.choose_spec (hwitness n)
  obtain ⟨φ, c, hφ, hc⟩ :=
    exists_strictMono_subsequence_const_of_finite code
  refine ⟨c.1.1, c.1.2, c.2, φ, ?_, ?_, ?_, ?_, hφ, ?_, ?_⟩
  · simpa [hc 0] using (hcode (φ 0)).1
  · simpa [hc 0] using (hcode (φ 0)).2.1
  · simpa [hc 0] using (hcode (φ 0)).2.2.1
  · exact Nat.le_of_lt_succ c.2.isLt
  · intro n
    simpa [hc n] using (hcode (φ n)).2.2.2.1
  · intro n
    simpa [hc n] using (hcode (φ n)).2.2.2.2

/-- Simultaneous version for a finite family of clusters.  This is the
finite-pigeonhole step used on the complement of the manuscript's
`Gamma_N`: the cluster, the ordered pair in it, and the bounded integer all
become fixed on one strict subsequence. -/
theorem exists_fixed_cluster_nearInteger_pair_subsequence
    {clusterCount m : ℕ} (a : ℕ → Fin m → ℝ)
    (t radius : ℕ → Fin clusterCount → ℝ) (D : ℕ)
    (cluster : Fin clusterCount → Finset (Fin m))
    (hcluster : ∀ n c i, i ∈ cluster c →
      t n c ≤ a n i ∧ a n i ≤ t n c + (D : ℝ))
    (hnear : ∀ n, ∃ c : Fin clusterCount,
      ∃ i ∈ cluster c, ∃ j ∈ cluster c, i ≠ j ∧
        integerDistance (a n i - a n j) < radius n c) :
    ∃ (c : Fin clusterCount) (i j : Fin m) (k : ℕ) (φ : ℕ → ℕ),
      i ∈ cluster c ∧ j ∈ cluster c ∧ i ≠ j ∧ k ≤ D ∧ StrictMono φ ∧
      (∀ n, a (φ n) j ≤ a (φ n) i) ∧
      (∀ n, |a (φ n) i - a (φ n) j - (k : ℝ)| < radius (φ n) c) := by
  classical
  let Code := ((Fin clusterCount × Fin m) × Fin m) × Fin (D + 1)
  have hwitness (n : ℕ) :
      ∃ q : Code,
        q.1.1.2 ∈ cluster q.1.1.1 ∧
        q.1.2 ∈ cluster q.1.1.1 ∧
        q.1.1.2 ≠ q.1.2 ∧
        a n q.1.2 ≤ a n q.1.1.2 ∧
        |a n q.1.1.2 - a n q.1.2 - (q.2 : ℝ)| < radius n q.1.1.1 := by
    obtain ⟨c, i, hi, j, hj, hij, hdist⟩ := hnear n
    obtain ⟨i', hi', j', hj', hij', hji', k, hkD, hk⟩ :=
      exists_oriented_bounded_nearInteger_pair
        (a n) (t n c) (radius n c) D (cluster c)
        (hcluster n c) ⟨i, hi, j, hj, hij, hdist⟩
    exact ⟨(((c, i'), j'), ⟨k, Nat.lt_succ_iff.mpr hkD⟩),
      hi', hj', hij', hji', hk⟩
  let code : ℕ → Code := fun n => Classical.choose (hwitness n)
  have hcode (n : ℕ) :
      (code n).1.1.2 ∈ cluster (code n).1.1.1 ∧
      (code n).1.2 ∈ cluster (code n).1.1.1 ∧
      (code n).1.1.2 ≠ (code n).1.2 ∧
      a n (code n).1.2 ≤ a n (code n).1.1.2 ∧
      |a n (code n).1.1.2 - a n (code n).1.2 - ((code n).2 : ℝ)| <
        radius n (code n).1.1.1 :=
    Classical.choose_spec (hwitness n)
  obtain ⟨φ, q, hφ, hq⟩ :=
    exists_strictMono_subsequence_const_of_finite code
  refine ⟨q.1.1.1, q.1.1.2, q.1.2, q.2, φ,
    ?_, ?_, ?_, ?_, hφ, ?_, ?_⟩
  · simpa [hq 0] using (hcode (φ 0)).1
  · simpa [hq 0] using (hcode (φ 0)).2.1
  · simpa [hq 0] using (hcode (φ 0)).2.2.1
  · exact Nat.le_of_lt_succ q.2.isLt
  · intro n
    simpa [hq n] using (hcode (φ n)).2.2.2.1
  · intro n
    simpa [hq n] using (hcode (φ n)).2.2.2.2

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- The all-unbounded near-integer branch, through the quantitative part of
pair merging.  It fixes the cluster pair, the integer `k`, and
`K = N + D + 3`, and returns the two coordinate limits required by the
restricted pair-merge map. -/
theorem exists_fixed_pairMergeCoordinates_tendsto
    {m : ℕ} (a : ℕ → Fin m → ℝ) (t : ℕ → ℝ) (N D : ℕ)
    (α : Finset (Fin m))
    (ht : Tendsto t atTop atTop)
    (ha : ∀ i ∈ α, Tendsto (fun n => a n i) atTop atTop)
    (hcluster : ∀ n i, i ∈ α →
      t n ≤ a n i ∧ a n i ≤ t n + (D : ℝ))
    (hnear : ∀ n, ∃ i ∈ α, ∃ j ∈ α, i ≠ j ∧
      integerDistance (a n i - a n j) <
        (inverse A (t n - (N : ℝ)))⁻¹) :
    ∃ (i j : Fin m) (k K : ℕ) (φ : ℕ → ℕ),
      i ∈ α ∧ j ∈ α ∧ i ≠ j ∧ k ≤ D ∧
      K = N + D + 3 ∧ StrictMono φ ∧
      (∀ n, a (φ n) j ≤ a (φ n) i) ∧
      (∀ n,
        |pairMergeDelta (fun r => a (φ r) i) (fun r => a (φ r) j) k n| <
          (inverse A ((t ∘ φ) n - (N : ℝ)))⁻¹) ∧
      Tendsto
          (fun n => inverse A
            (pairMergeSigma (fun r => a (φ r) j) K n))
          atTop atTop ∧
        Tendsto
          (pairMergeXi A (fun r => a (φ r) i) (fun r => a (φ r) j) K k)
          atTop (𝓝 0) := by
  let radius : ℕ → ℝ := fun n => (inverse A (t n - (N : ℝ)))⁻¹
  obtain ⟨i, j, k, φ, hi, hj, hij, hkD, hφ, horient, hnearFixed⟩ :=
    exists_fixed_nearInteger_pair_subsequence a t radius D α hcluster hnear
  let K : ℕ := N + D + 3
  have htφ : Tendsto (t ∘ φ) atTop atTop := ht.comp hφ.tendsto_atTop
  have hajφ : Tendsto (fun n => a (φ n) j) atTop atTop :=
    (ha j hj).comp hφ.tendsto_atTop
  have haiUpper : ∀ᶠ n in atTop,
      a (φ n) i ≤ (t ∘ φ) n + (D : ℝ) :=
    Eventually.of_forall fun n => (hcluster (φ n) i hi).2
  have hajUpper : ∀ᶠ n in atTop,
      a (φ n) j ≤ (t ∘ φ) n + (D : ℝ) :=
    Eventually.of_forall fun n => (hcluster (φ n) j hj).2
  have hnearEventually : ∀ᶠ n in atTop,
      |pairMergeDelta (fun r => a (φ r) i) (fun r => a (φ r) j) k n| <
        (inverse A ((t ∘ φ) n - (N : ℝ)))⁻¹ :=
    Eventually.of_forall hnearFixed
  have hlimits := hA.pairMergeCoordinates_tendsto
    (t ∘ φ) (fun r => a (φ r) i) (fun r => a (φ r) j)
    N D K k rfl htφ hajφ haiUpper hajUpper hnearEventually
  exact ⟨i, j, k, K, φ, hi, hj, hij, hkD, rfl, hφ,
    horient, hnearFixed, hlimits⟩

/-- The full finite-cluster selection and quantitative merge wrapper.  Its
pointwise hypothesis is exactly the negation of simultaneous separation in
all clusters, after an infinite set has been enumerated by `ℕ`. -/
theorem exists_fixed_cluster_pairMergeCoordinates_tendsto
    {clusterCount m : ℕ} (a : ℕ → Fin m → ℝ)
    (t : ℕ → Fin clusterCount → ℝ) (N D : ℕ)
    (cluster : Fin clusterCount → Finset (Fin m))
    (ht : ∀ c, Tendsto (fun n => t n c) atTop atTop)
    (ha : ∀ i, Tendsto (fun n => a n i) atTop atTop)
    (hcluster : ∀ n c i, i ∈ cluster c →
      t n c ≤ a n i ∧ a n i ≤ t n c + (D : ℝ))
    (hnear : ∀ n, ∃ c : Fin clusterCount,
      ∃ i ∈ cluster c, ∃ j ∈ cluster c, i ≠ j ∧
        integerDistance (a n i - a n j) <
          (inverse A (t n c - (N : ℝ)))⁻¹) :
    ∃ (c : Fin clusterCount) (i j : Fin m) (k K : ℕ) (φ : ℕ → ℕ),
      i ∈ cluster c ∧ j ∈ cluster c ∧ i ≠ j ∧ k ≤ D ∧
      K = N + D + 3 ∧ StrictMono φ ∧
      (∀ n, a (φ n) j ≤ a (φ n) i) ∧
      (∀ n,
        |pairMergeDelta (fun r => a (φ r) i) (fun r => a (φ r) j) k n| <
          (inverse A ((fun r => t (φ r) c) n - (N : ℝ)))⁻¹) ∧
      Tendsto
          (fun n => inverse A
            (pairMergeSigma (fun r => a (φ r) j) K n))
          atTop atTop ∧
        Tendsto
          (pairMergeXi A (fun r => a (φ r) i) (fun r => a (φ r) j) K k)
          atTop (𝓝 0) := by
  let radius : ℕ → Fin clusterCount → ℝ :=
    fun n c => (inverse A (t n c - (N : ℝ)))⁻¹
  obtain ⟨c, i, j, k, φ, hi, hj, hij, hkD, hφ, horient, hnearFixed⟩ :=
    exists_fixed_cluster_nearInteger_pair_subsequence
      a t radius D cluster hcluster hnear
  let K : ℕ := N + D + 3
  have htφ : Tendsto (fun n => t (φ n) c) atTop atTop :=
    (ht c).comp hφ.tendsto_atTop
  have hajφ : Tendsto (fun n => a (φ n) j) atTop atTop :=
    (ha j).comp hφ.tendsto_atTop
  have haiUpper : ∀ᶠ n in atTop,
      a (φ n) i ≤ t (φ n) c + (D : ℝ) :=
    Eventually.of_forall fun n => (hcluster (φ n) c i hi).2
  have hajUpper : ∀ᶠ n in atTop,
      a (φ n) j ≤ t (φ n) c + (D : ℝ) :=
    Eventually.of_forall fun n => (hcluster (φ n) c j hj).2
  have hnearEventually : ∀ᶠ n in atTop,
      |pairMergeDelta (fun r => a (φ r) i) (fun r => a (φ r) j) k n| <
        (inverse A ((fun r => t (φ r) c) n - (N : ℝ)))⁻¹ :=
    Eventually.of_forall hnearFixed
  have hlimits := hA.pairMergeCoordinates_tendsto
    (fun r => t (φ r) c) (fun r => a (φ r) i) (fun r => a (φ r) j)
    N D K k rfl htφ hajφ haiUpper hajUpper hnearEventually
  exact ⟨c, i, j, k, K, φ, hi, hj, hij, hkD, rfl, hφ,
    horient, hnearFixed, hlimits⟩

/-- Original-representative form of the full selection theorem.  Its last
conclusion is the literal appended coordinate of
`restrictedPairMergePullback`: `L^[K+k] s_i - L^[K] s_j` tends to zero. -/
theorem exists_fixed_cluster_pairMerge_logCoordinate_tendsto
    {clusterCount m : ℕ} (s : ℕ → Fin m → ℝ)
    (t : ℕ → Fin clusterCount → ℝ) (N D : ℕ)
    (cluster : Fin clusterCount → Finset (Fin m))
    (ht : ∀ c, Tendsto (fun n => t n c) atTop atTop)
    (hs : ∀ i, Tendsto (fun n => s n i) atTop atTop)
    (hcluster : ∀ n c i, i ∈ cluster c →
      t n c ≤ A (s n i) ∧ A (s n i) ≤ t n c + (D : ℝ))
    (hnear : ∀ n, ∃ c : Fin clusterCount,
      ∃ i ∈ cluster c, ∃ j ∈ cluster c, i ≠ j ∧
        integerDistance (A (s n i) - A (s n j)) <
          (inverse A (t n c - (N : ℝ)))⁻¹) :
    ∃ (c : Fin clusterCount) (i j : Fin m) (k K : ℕ) (φ : ℕ → ℕ),
      i ∈ cluster c ∧ j ∈ cluster c ∧ i ≠ j ∧ k ≤ D ∧
      K = N + D + 3 ∧ StrictMono φ ∧
      (∀ n, A (s (φ n) j) ≤ A (s (φ n) i)) ∧
      (∀ n,
        |pairMergeDelta
            (fun r => A (s (φ r) i))
            (fun r => A (s (φ r) j)) k n| <
          (inverse A ((fun r => t (φ r) c) n - (N : ℝ)))⁻¹) ∧
      Tendsto
        (fun n => L^[K + k] (s (φ n) i) - L^[K] (s (φ n) j))
        atTop (𝓝 0) := by
  let a : ℕ → Fin m → ℝ := fun n i => A (s n i)
  let radius : ℕ → Fin clusterCount → ℝ :=
    fun n c => (inverse A (t n c - (N : ℝ)))⁻¹
  obtain ⟨c, i, j, k, φ, hi, hj, hij, hkD, hφ, horient, hnearFixed⟩ :=
    exists_fixed_cluster_nearInteger_pair_subsequence
      a t radius D cluster hcluster hnear
  let K : ℕ := N + D + 3
  have htφ : Tendsto (fun n => t (φ n) c) atTop atTop :=
    (ht c).comp hφ.tendsto_atTop
  have hsiφ : Tendsto (fun n => s (φ n) i) atTop atTop :=
    (hs i).comp hφ.tendsto_atTop
  have hsjφ : Tendsto (fun n => s (φ n) j) atTop atTop :=
    (hs j).comp hφ.tendsto_atTop
  have haiUpper : ∀ᶠ n in atTop,
      A (s (φ n) i) ≤ t (φ n) c + (D : ℝ) :=
    Eventually.of_forall fun n => (hcluster (φ n) c i hi).2
  have hajUpper : ∀ᶠ n in atTop,
      A (s (φ n) j) ≤ t (φ n) c + (D : ℝ) :=
    Eventually.of_forall fun n => (hcluster (φ n) c j hj).2
  have hnearEventually : ∀ᶠ n in atTop,
      |pairMergeDelta
          (fun r => A (s (φ r) i))
          (fun r => A (s (φ r) j)) k n| <
        (inverse A ((fun r => t (φ r) c) n - (N : ℝ)))⁻¹ :=
    Eventually.of_forall hnearFixed
  have hxi := hA.pairMerge_logCoordinate_tendsto_zero
    (fun r => t (φ r) c) (fun r => s (φ r) i) (fun r => s (φ r) j)
    N D K k rfl htφ hsiφ hsjφ haiUpper hajUpper hnearEventually
  exact ⟨c, i, j, k, K, φ, hi, hj, hij, hkD, rfl, hφ,
    horient, hnearFixed, hxi⟩

end IsAbel
end AbelFormalization
