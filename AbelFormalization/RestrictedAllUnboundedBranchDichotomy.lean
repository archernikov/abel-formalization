import AbelFormalization.RestrictedAllUnboundedPairBranch
import Mathlib.Data.Nat.Nth

/-!
# Exact infinite-set dichotomy for the all-unbounded branches

The separated-cluster proposition produces an infinite set `Λ` and a fixed
rank `N`.  Its useful branch is the intersection of `Λ` with the simultaneous
separation set.  When that intersection is finite, the complement inside
`Λ` is infinite and its canonical increasing enumeration supplies the
pointwise near-integer hypothesis used by pair merging.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- The pointwise failure of simultaneous within-cluster separation at rank
`N`. -/
def RestrictedAllUnboundedNearIntegerAt
    {A : ℝ → ℝ} {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (N n : ℕ) : Prop :=
  ∃ c : Fin data.orderedClusterCount,
    ∃ i ∈ data.orderedCluster c,
      ∃ j ∈ data.orderedCluster c, i ≠ j ∧
        integerDistance
            (A ((x (data.subsequence n)).1.1 i) -
              A ((x (data.subsequence n)).1.1 j)) <
          (inverse A
            (data.orderedClusterMinTime c n - (N : ℝ)))⁻¹

/-- The literal simultaneous separation set `Γ_N` for the ordered clusters
returned by the all-unbounded setup. -/
def restrictedAllUnboundedSeparationSet
    {A : ℝ → ℝ} {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (N : ℕ) : Set ℕ :=
  {n | ∀ c : Fin data.orderedClusterCount,
    ∀ i ∈ data.orderedCluster c,
      ∀ j ∈ data.orderedCluster c, i ≠ j →
        (inverse A
            (data.orderedClusterMinTime c n - (N : ℝ)))⁻¹ ≤
          integerDistance
            (A ((x (data.subsequence n)).1.1 i) -
              A ((x (data.subsequence n)).1.1 j))}

/-- The existing branch predicate is exactly pointwise near-integer failure
at every index. -/
theorem restrictedAllUnboundedNearIntegerBranch_iff
    {A : ℝ → ℝ} {m p a : ℕ}
    {x : ℕ → RestrictedSource m p a}
    {data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i))}
    {N : ℕ} :
    RestrictedAllUnboundedNearIntegerBranch (A := A) x data N ↔
      ∀ n, RestrictedAllUnboundedNearIntegerAt x data N n := by
  rfl

/-- Membership in `Γ_N` is exactly the negation of the pointwise
near-integer branch. -/
theorem mem_restrictedAllUnboundedSeparationSet_iff_not_nearIntegerAt
    {A : ℝ → ℝ} {m p a : ℕ}
    {x : ℕ → RestrictedSource m p a}
    {data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i))}
    {N n : ℕ} :
    n ∈ restrictedAllUnboundedSeparationSet x data N ↔
      ¬ RestrictedAllUnboundedNearIntegerAt x data N n := by
  classical
  simp only [restrictedAllUnboundedSeparationSet,
    RestrictedAllUnboundedNearIntegerAt, Set.mem_ofPred_eq]
  push Not
  rfl

/-- Equivalently, every index outside `Γ_N` supplies the literal strict
near-integer witness consumed by pair selection. -/
theorem not_mem_restrictedAllUnboundedSeparationSet_iff_nearIntegerAt
    {A : ℝ → ℝ} {m p a : ℕ}
    {x : ℕ → RestrictedSource m p a}
    {data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i))}
    {N n : ℕ} :
    n ∉ restrictedAllUnboundedSeparationSet x data N ↔
      RestrictedAllUnboundedNearIntegerAt x data N n := by
  rw [mem_restrictedAllUnboundedSeparationSet_iff_not_nearIntegerAt]
  tauto

/-- Removing a finite separated intersection from an infinite `Λ` leaves an
infinite set of near-integer indices. -/
theorem infinite_sdiff_restrictedAllUnboundedSeparationSet
    {A : ℝ → ℝ} {m p a : ℕ}
    {x : ℕ → RestrictedSource m p a}
    {data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i))}
    {N : ℕ} {Λ : Set ℕ}
    (hΛ : Λ.Infinite)
    (hfinite :
      (Λ ∩ restrictedAllUnboundedSeparationSet x data N).Finite) :
    (Λ \ restrictedAllUnboundedSeparationSet x data N).Infinite := by
  have h := hΛ.sdiff hfinite
  have heq :
      Λ \ (Λ ∩ restrictedAllUnboundedSeparationSet x data N) =
        Λ \ restrictedAllUnboundedSeparationSet x data N := by
    ext n
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  simpa only [heq] using h

/-- In the finite-intersection branch, the canonical increasing enumeration
of the complement gives one strict subsequence lying in `Λ` and satisfying
the near-integer condition at every term. -/
theorem exists_strictMono_nearInteger_subsequence_of_finite_inter
    {A : ℝ → ℝ} {m p a : ℕ}
    {x : ℕ → RestrictedSource m p a}
    {data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i))}
    {N : ℕ} {Λ : Set ℕ}
    (hΛ : Λ.Infinite)
    (hfinite :
      (Λ ∩ restrictedAllUnboundedSeparationSet x data N).Finite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n, φ n ∈ Λ ∧
        RestrictedAllUnboundedNearIntegerAt x data N (φ n) := by
  let s : Set ℕ :=
    Λ \ restrictedAllUnboundedSeparationSet x data N
  have hs : s.Infinite :=
    infinite_sdiff_restrictedAllUnboundedSeparationSet hΛ hfinite
  let φ : ℕ → ℕ := Nat.nth (fun n ↦ n ∈ s)
  refine ⟨φ, Nat.nth_strictMono hs, ?_⟩
  intro n
  have hφs : φ n ∈ s := by
    exact Nat.nth_mem_of_infinite hs n
  refine ⟨hφs.1, ?_⟩
  exact not_mem_restrictedAllUnboundedSeparationSet_iff_nearIntegerAt.mp
    hφs.2

/-- Exact infinite-set dichotomy: the separated branch is infinite, or a
strict subsequence through `Λ` satisfies the pair branch pointwise. -/
theorem restrictedAllUnbounded_separation_or_nearInteger_subsequence
    {A : ℝ → ℝ} {m p a : ℕ}
    {x : ℕ → RestrictedSource m p a}
    {data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i))}
    (N : ℕ) (Λ : Set ℕ) (hΛ : Λ.Infinite) :
    (Λ ∩ restrictedAllUnboundedSeparationSet x data N).Infinite ∨
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ n, φ n ∈ Λ ∧
          RestrictedAllUnboundedNearIntegerAt x data N (φ n) := by
  rcases (Λ ∩ restrictedAllUnboundedSeparationSet x data N).finite_or_infinite with
    hfinite | hinfinite
  · exact Or.inr
      (exists_strictMono_nearInteger_subsequence_of_finite_inter hΛ hfinite)
  · exact Or.inl hinfinite

/-- The finite separated-intersection branch already contains the complete
fixed-pair quantitative conclusion.  The first subsequence enumerates the
near-integer indices in `Λ`; the second finite-pigeonhole subsequence fixes
the cluster, pair, and integer. -/
theorem IsAbel.exists_fixed_pairBranch_of_finite_separated_inter
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (N width : ℕ)
    (hmin : ∀ c, Tendsto (data.orderedClusterMinTime c) atTop atTop)
    (hxrep : ∀ i, Tendsto
      (fun n ↦ (x (data.subsequence n)).1.1 i) atTop atTop)
    (hinterval : ∀ c n i, i ∈ data.orderedCluster c →
      data.orderedClusterMinTime c n ≤
          A ((x (data.subsequence n)).1.1 i) ∧
        A ((x (data.subsequence n)).1.1 i) ≤
          data.orderedClusterMinTime c n + (width : ℝ))
    (Λ : Set ℕ) (hΛ : Λ.Infinite)
    (hfinite :
      (Λ ∩ restrictedAllUnboundedSeparationSet x data N).Finite) :
    ∃ (c : Fin data.orderedClusterCount) (i j : Fin m)
      (k K : ℕ) (φ : ℕ → ℕ),
      i ∈ data.orderedCluster c ∧
      j ∈ data.orderedCluster c ∧
      i ≠ j ∧
      k ≤ width ∧
      K = N + width + 3 ∧
      StrictMono φ ∧
      (∀ n, φ n ∈ Λ) ∧
      (∀ n,
        A ((x (data.subsequence (φ n))).1.1 j) ≤
          A ((x (data.subsequence (φ n))).1.1 i)) ∧
      (∀ n,
        |pairMergeDelta
            (fun r ↦ A ((x (data.subsequence (φ r))).1.1 i))
            (fun r ↦ A ((x (data.subsequence (φ r))).1.1 j))
            k n| <
          (inverse A
            (data.orderedClusterMinTime c (φ n) - (N : ℝ)))⁻¹) ∧
      Tendsto (fun n ↦
        L^[K + k] ((x (data.subsequence (φ n))).1.1 i) -
          L^[K] ((x (data.subsequence (φ n))).1.1 j))
        atTop (nhds 0) := by
  obtain ⟨ψ, hψ, hψmem⟩ :=
    exists_strictMono_nearInteger_subsequence_of_finite_inter hΛ hfinite
  let s : ℕ → Fin m → ℝ :=
    fun n i ↦ (x (data.subsequence (ψ n))).1.1 i
  let t : ℕ → Fin data.orderedClusterCount → ℝ :=
    fun n c ↦ data.orderedClusterMinTime c (ψ n)
  have ht : ∀ c, Tendsto (fun n ↦ t n c) atTop atTop := by
    intro c
    exact (hmin c).comp hψ.tendsto_atTop
  have hs : ∀ i, Tendsto (fun n ↦ s n i) atTop atTop := by
    intro i
    exact (hxrep i).comp hψ.tendsto_atTop
  have hcluster : ∀ n c i, i ∈ data.orderedCluster c →
      t n c ≤ A (s n i) ∧ A (s n i) ≤ t n c + (width : ℝ) := by
    intro n c i hi
    exact hinterval c (ψ n) i hi
  have hnear : ∀ n, ∃ c : Fin data.orderedClusterCount,
      ∃ i ∈ data.orderedCluster c,
        ∃ j ∈ data.orderedCluster c, i ≠ j ∧
          integerDistance (A (s n i) - A (s n j)) <
            (inverse A (t n c - (N : ℝ)))⁻¹ := by
    intro n
    exact (hψmem n).2
  obtain ⟨c, i, j, k, K, θ, hi, hj, hij, hk, hK, hθ,
      horient, hdelta, hlog⟩ :=
    hA.exists_fixed_cluster_pairMerge_logCoordinate_tendsto
      s t N width data.orderedCluster ht hs hcluster hnear
  let φ : ℕ → ℕ := ψ ∘ θ
  refine ⟨c, i, j, k, K, φ, hi, hj, hij, hk, hK,
    hψ.comp hθ, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (hψmem (θ n)).1
  · intro n
    exact horient n
  · intro n
    exact hdelta n
  · exact hlog

end AbelFormalization
