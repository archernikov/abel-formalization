import AbelFormalization.InversePowerLowerBoundNonvanishing
import AbelFormalization.RestrictedAllUnboundedBranchDichotomy

/-!
# Eliminating the separated branch when the equations vanish

Once a separated-cluster certificate gives an inverse-power lower bound for
a finite generating family, eventual common vanishing on the regular-zero
sequence rules out an infinite separated intersection.  The exact
infinite-set dichotomy then forces the fixed pair branch.
-/

noncomputable section

open Filter Function Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- A separated lower bound for generators which eventually all vanish
forces the fixed near-integer pair branch, with no hidden nonvacuity
assumption. -/
theorem IsAbel.exists_fixed_pairBranch_of_separatedLowerBound_and_zeros
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
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (scale : ℕ → ℝ) (value : κ → ℕ → ℝ)
    (hlower : HasInversePowerLowerBound
      (separatedRestriction Λ
        (fun q ↦ restrictedAllUnboundedSeparationSet x data q) N)
      scale value)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hzero : ∀ᶠ n in atTop, ∀ j, value j n = 0) :
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
  let Γ : ℕ → Set ℕ :=
    fun q ↦ restrictedAllUnboundedSeparationSet x data q
  rcases (Λ ∩ Γ N).finite_or_infinite with hfinite | hinfinite
  · exact hA.exists_fixed_pairBranch_of_finite_separated_inter
      x data N width hmin hxrep hinterval Λ hΛ hfinite
  · have hscale' : ∀ᶠ n in separatedRestriction Λ Γ N,
        1 ≤ scale n := by
      rw [eventually_separatedRestriction_iff]
      filter_upwards [hscale] with n hn
      exact fun _ ↦ hn
    have hzero' : ∀ᶠ n in separatedRestriction Λ Γ N,
        ∀ j, value j n = 0 := by
      rw [eventually_separatedRestriction_iff]
      filter_upwards [hzero] with n hn
      exact fun _ ↦ hn
    exact (hlower.false_of_separatedRestriction_zeros
      hinfinite hscale' hzero').elim

end AbelFormalization
