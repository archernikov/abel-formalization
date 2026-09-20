import AbelFormalization.RestrictedAllUnboundedBranchSetupDichotomy
import AbelFormalization.RestrictedPairMergeLowerCountContradiction

/-!
# The lower-count theorem eliminates the pair branch

For a system with `q + 2` representative coordinates, the exact branch
dichotomy and the pair-merge contradiction leave an infinite separated set.
-/

noncomputable section

open Filter Function Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- Assuming restricted base finiteness for `q + 1` representatives, an
infinite regular-zero set with `q + 2` representatives has an all-unbounded
cluster subsequence whose simultaneous separation set is infinite at every
fixed rank `N`. -/
theorem IsAbel.exists_restrictedAllUnboundedSeparatedSetup_q_add_two
    {A : ℝ → ℝ} (hA : IsAbel A) {q : ℕ}
    (hlower : RestrictedBaseRegularZeroFiniteForRepresentativeCount A (q + 1))
    {ι : Type} [Finite ι] {p a : ℕ}
    (box : RestrictedBox p)
    (representative : ι → Fin (q + 2))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra box)
    (R : ℝ)
    (hDomain :
      restrictedBaseClosedDomain (m := q + 2) (a := a) box R ⊆
        restrictedAbelJetDomain (a := a) box representative offset)
    (F : Fin (((q + 2) + p) + a) →
      RestrictedSource (q + 2) p a → ℝ)
    (hF : ∀ r, F r ∈ restrictedExpressionBase box
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (hZ : (regularZeroSet (restrictedBaseOpenDomain box R)
      (constraintMap F)).Infinite)
    (N : ℕ) :
    ∃ (x : ℕ → RestrictedSource (q + 2) p a)
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
        (Finset.univ : Finset (Fin (q + 2))) ∧
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
      (restrictedAllUnboundedSeparationSet x data N).Infinite := by
  obtain ⟨x, w₀, data, width, hsub, hxinj, hxmem, hw₀, hxlim, hxrep,
      hnonempty, hdisjoint, hcover, hmin, hinterval, hcross, hgap,
      hdichotomy⟩ :=
    hA.exists_restrictedAllUnboundedBranchSetupDichotomy
      hlower box representative offset R hDomain F hF hZ N
  refine ⟨x, w₀, data, width, hsub, hxinj, hxmem, hw₀, hxlim, hxrep,
    hnonempty, hdisjoint, hcover, hmin, hinterval, hcross, hgap, ?_⟩
  have huniv : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
  rcases hdichotomy Set.univ huniv with hsep | hpair
  · simpa only [Set.univ_inter] using hsep
  · obtain ⟨c, i, j, k, K, φ, _hi, _hj, hij, _hk, hK, _hφ,
        _hφmem, _hsubφ, hxinjφ, hxmemφ, hxlimφ, hxrepφ,
        _horient, _hdelta, hlog⟩ := hpair
    obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
    let y : ℕ → RestrictedSource (q + 2) p a :=
      fun n ↦ x (data.subsequence (φ n))
    have hKpos : 1 ≤ K := by
      omega
    have hlog' : Tendsto (fun n ↦
        L^[K + k] ((y n).1.1 i) -
          L^[K] ((y n).1.1 (i.succAbove j')))
        atTop (nhds 0) := by
      simpa only [y, hj'] using hlog
    exact (hA.false_of_restrictedPairMergeBranch_q_add_two
      hlower box representative offset R hDomain F hF y w₀ i j'
        hKpos hxinjφ hxmemφ hw₀ hxlimφ hxrepφ hlog').elim

end AbelFormalization
