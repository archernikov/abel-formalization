import AbelFormalization.RestrictedAllUnboundedClusterSetup
import AbelFormalization.RestrictedUnboundedPairSelection

/-!
# The near-integer branch of the all-unbounded reduction

The ordered-cluster setup is chosen existentially.  Consequently, the
manuscript's complement-branch hypothesis is stated on that returned setup,
inside the same existential package.  This avoids requiring the branch for
every possible subsequence or for every possible choice of cluster data.
-/

noncomputable section

open Filter Function Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- The complement of simultaneous within-cluster separation at rank `N`.
At every sequence term, some ordered cluster contains a distinct pair whose
Abel-time difference is closer to an integer than the inverse-Abel scale at
the minimum of that cluster. -/
def RestrictedAllUnboundedNearIntegerBranch
    {A : ℝ → ℝ} {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (N : ℕ) : Prop :=
  ∀ n, ∃ c : Fin data.orderedClusterCount,
    ∃ i ∈ data.orderedCluster c,
      ∃ j ∈ data.orderedCluster c, i ≠ j ∧
        integerDistance
            (A ((x (data.subsequence n)).1.1 i) -
              A ((x (data.subsequence n)).1.1 j)) <
          (inverse A
            (data.orderedClusterMinTime c n - (N : ℝ)))⁻¹

/-- End-to-end extraction of the fixed pair in the near-integer branch.

The first strict subsequence and its ordered clusters are returned before the
branch implication because those data are selected from the infinite regular
zero set.  Assuming the complement branch for precisely those returned data,
the theorem fixes a cluster, an oriented distinct pair, the bounded integer
`k`, and `K = N + width + 3` on one further strict subsequence.  It retains
all regular-zero and convergence properties and proves convergence of the
literal logarithmic pullback coordinate to zero. -/
theorem IsAbel.exists_restrictedAllUnboundedPairBranch
    {A : ℝ → ℝ} (hA : IsAbel A) {m : ℕ}
    (houter : RestrictedBaseRegularZeroFiniteForRepresentativeCount A m)
    {ι : Type} [Finite ι] {p a : ℕ}
    (box : RestrictedBox p)
    (representative : ι → Fin (m + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra box)
    (R : ℝ)
    (hDomain :
      restrictedBaseClosedDomain (m := m + 1) (a := a) box R ⊆
        restrictedAbelJetDomain (a := a) box representative offset)
    (F : Fin (((m + 1) + p) + a) →
      RestrictedSource (m + 1) p a → ℝ)
    (hF : ∀ r, F r ∈ restrictedExpressionBase box
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (hZ : (regularZeroSet (restrictedBaseOpenDomain box R)
      (constraintMap F)).Infinite)
    (N : ℕ) :
    ∃ (x : ℕ → RestrictedSource (m + 1) p a)
      (w₀ : RestrictedBoxSpace p)
      (data : RepresentativeClusterSubsequence
        (fun n i ↦ A ((x n).1.1 i)))
      (width : ℕ),
      StrictMono data.subsequence ∧
      Function.Injective (fun n ↦ x (data.subsequence n)) ∧
      (∀ n, x (data.subsequence n) ∈
        regularZeroSet (restrictedBaseOpenDomain box R) (constraintMap F)) ∧
      w₀ ∈ box.closedBox ∧
      Tendsto (fun n ↦ (x (data.subsequence n)).1.2)
        atTop (nhds w₀) ∧
      (∀ i, Tendsto (fun n ↦ (x (data.subsequence n)).1.1 i)
        atTop atTop) ∧
      (∀ c, (data.orderedCluster c).Nonempty) ∧
      Pairwise (Disjoint on data.orderedCluster) ∧
      Finset.univ.biUnion data.orderedCluster =
        (Finset.univ : Finset (Fin (m + 1))) ∧
      (∀ c, Tendsto (data.orderedClusterMinTime c) atTop atTop) ∧
      (∀ c n i, i ∈ data.orderedCluster c →
        data.orderedClusterMinTime c n ≤
            A ((x (data.subsequence n)).1.1 i) ∧
          A ((x (data.subsequence n)).1.1 i) ≤
            data.orderedClusterMinTime c n + (width : ℝ)) ∧
      (∀ c d, c < d → ∀ i, i ∈ data.orderedCluster c →
        ∀ j, j ∈ data.orderedCluster d →
          Tendsto (fun n ↦
            A ((x (data.subsequence n)).1.1 j) -
              A ((x (data.subsequence n)).1.1 i)) atTop atTop) ∧
      (∀ c d, c < d →
        Tendsto (fun n ↦
          data.orderedClusterMinTime d n -
            data.orderedClusterMaxTime c n) atTop atTop) ∧
      (RestrictedAllUnboundedNearIntegerBranch (A := A) x data N →
        ∃ (c : Fin data.orderedClusterCount) (i j : Fin (m + 1))
          (k K : ℕ) (φ : ℕ → ℕ),
          i ∈ data.orderedCluster c ∧
          j ∈ data.orderedCluster c ∧
          i ≠ j ∧
          k ≤ width ∧
          K = N + width + 3 ∧
          StrictMono φ ∧
          StrictMono (data.subsequence ∘ φ) ∧
          Function.Injective
            (fun n ↦ x (data.subsequence (φ n))) ∧
          (∀ n, x (data.subsequence (φ n)) ∈
            regularZeroSet
              (restrictedBaseOpenDomain box R) (constraintMap F)) ∧
          Tendsto (fun n ↦ (x (data.subsequence (φ n))).1.2)
            atTop (nhds w₀) ∧
          (∀ r, Tendsto
            (fun n ↦ (x (data.subsequence (φ n))).1.1 r)
            atTop atTop) ∧
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
            atTop (nhds 0)) := by
  obtain ⟨x, w₀, data, width, hsub, hxinj, hxmem, hw₀, hxlim, hxrep,
      hnonempty, hdisjoint, hcover, hmin, hinterval, hcross, hgap⟩ :=
    hA.exists_restrictedAllUnboundedClusterSetup
      houter box representative offset R hDomain F hF hZ
  refine ⟨x, w₀, data, width, hsub, hxinj, hxmem, hw₀, hxlim, hxrep,
    hnonempty, hdisjoint, hcover, hmin, hinterval, hcross, hgap, ?_⟩
  intro hnear
  obtain ⟨c, i, j, k, K, φ, hi, hj, hij, hk, hK, hφ,
      horient, hdelta, hlog⟩ :=
    hA.exists_fixed_cluster_pairMerge_logCoordinate_tendsto
      (fun n i ↦ (x (data.subsequence n)).1.1 i)
      (fun n c ↦ data.orderedClusterMinTime c n)
      N width data.orderedCluster hmin hxrep
      (fun n c i hi ↦ hinterval c n i hi) hnear
  refine ⟨c, i, j, k, K, φ, hi, hj, hij, hk, hK, hφ,
    hsub.comp hφ, hxinj.comp hφ.injective, ?_, ?_, ?_, horient,
    hdelta, hlog⟩
  · intro n
    exact hxmem (φ n)
  · change Tendsto
      ((fun n ↦ (x (data.subsequence n)).1.2) ∘ φ) atTop (nhds w₀)
    exact hxlim.comp hφ.tendsto_atTop
  · intro r
    change Tendsto
      ((fun n ↦ (x (data.subsequence n)).1.1 r) ∘ φ) atTop atTop
    exact (hxrep r).comp hφ.tendsto_atTop

end AbelFormalization
