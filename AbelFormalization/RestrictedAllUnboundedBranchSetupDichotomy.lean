import AbelFormalization.RestrictedAllUnboundedBranchDichotomy

/-!
# End-to-end separated/pair dichotomy after all-unbounded normalization

This module combines the outer-induction sequence normalization with the
exact infinite-set dichotomy.  It keeps the ordered-cluster data fixed.  For
every later infinite set `Λ`, either its separated part is infinite or one
strict subsequence through `Λ` carries all data needed by pair merging.
-/

noncomputable section

open Filter Function Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

theorem IsAbel.exists_restrictedAllUnboundedBranchSetupDichotomy
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
      ∀ Λ : Set ℕ, Λ.Infinite →
        (Λ ∩ restrictedAllUnboundedSeparationSet x data N).Infinite ∨
          ∃ (c : Fin data.orderedClusterCount)
            (i j : Fin (m + 1)) (k K : ℕ) (φ : ℕ → ℕ),
            i ∈ data.orderedCluster c ∧
            j ∈ data.orderedCluster c ∧
            i ≠ j ∧
            k ≤ width ∧
            K = N + width + 3 ∧
            StrictMono φ ∧
            (∀ n, φ n ∈ Λ) ∧
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
              atTop (nhds 0) := by
  obtain ⟨x, w₀, data, width, hsub, hxinj, hxmem, hw₀, hxlim, hxrep,
      hnonempty, hdisjoint, hcover, hmin, hinterval, hcross, hgap⟩ :=
    hA.exists_restrictedAllUnboundedClusterSetup
      houter box representative offset R hDomain F hF hZ
  refine ⟨x, w₀, data, width, hsub, hxinj, hxmem, hw₀, hxlim, hxrep,
    hnonempty, hdisjoint, hcover, hmin, hinterval, hcross, hgap, ?_⟩
  intro Λ hΛ
  rcases (Λ ∩ restrictedAllUnboundedSeparationSet x data N).finite_or_infinite with
    hfinite | hinfinite
  · right
    obtain ⟨c, i, j, k, K, φ, hi, hj, hij, hk, hK, hφ,
        hφΛ, horient, hdelta, hlog⟩ :=
      hA.exists_fixed_pairBranch_of_finite_separated_inter
        x data N width hmin hxrep hinterval Λ hΛ hfinite
    refine ⟨c, i, j, k, K, φ, hi, hj, hij, hk, hK, hφ, hφΛ,
      hsub.comp hφ, hxinj.comp hφ.injective, ?_, ?_, ?_, horient,
      hdelta, hlog⟩
    · intro n
      exact hxmem (φ n)
    · change Tendsto
        ((fun n ↦ (x (data.subsequence n)).1.2) ∘ φ)
          atTop (nhds w₀)
      exact hxlim.comp hφ.tendsto_atTop
    · intro r
      change Tendsto
        ((fun n ↦ (x (data.subsequence n)).1.1 r) ∘ φ)
          atTop atTop
      exact (hxrep r).comp hφ.tendsto_atTop
  · exact Or.inl hinfinite

end AbelFormalization
