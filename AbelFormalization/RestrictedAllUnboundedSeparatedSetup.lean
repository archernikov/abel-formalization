import AbelFormalization.RestrictedAllUnboundedBranchSetupDichotomy
import AbelFormalization.RestrictedPairMergeLowerCountContradiction
import AbelFormalization.RepresentativeClusterSubsequenceRestriction

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

/-- Once one all-unbounded ordered-cluster sequence has been fixed, lower
representative-count finiteness rules out the near-integer branch for every
subsequently chosen separation rank.  This form keeps the cluster and
algebraic data fixed while `N` is chosen later from the finite descent. -/
theorem IsAbel.restrictedAllUnboundedSeparationSet_infinite_q_add_two
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
    (x : ℕ → RestrictedSource (q + 2) p a)
    (w₀ : RestrictedBoxSpace p)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (width : ℕ)
    (hxinj : Function.Injective (fun n ↦ x (data.subsequence n)))
    (hxmem : ∀ n, x (data.subsequence n) ∈
      regularZeroSet (restrictedBaseOpenDomain box R) (constraintMap F))
    (hw₀ : w₀ ∈ box.closedBox)
    (hxlim : Tendsto (fun n ↦ (x (data.subsequence n)).1.2)
      atTop (nhds w₀))
    (hxrep : ∀ i, Tendsto
      (fun n ↦ (x (data.subsequence n)).1.1 i) atTop atTop)
    (hmin : ∀ c, Tendsto (data.orderedClusterMinTime c) atTop atTop)
    (hinterval : ∀ c n i, i ∈ data.orderedCluster c →
      data.orderedClusterMinTime c n ≤
          A ((x (data.subsequence n)).1.1 i) ∧
        A ((x (data.subsequence n)).1.1 i) ≤
          data.orderedClusterMinTime c n + (width : ℝ))
    (N : ℕ) :
    (restrictedAllUnboundedSeparationSet x data N).Infinite := by
  rcases (restrictedAllUnboundedSeparationSet x data N).finite_or_infinite with
    hfinite | hinfinite
  · have huniv : (Set.univ : Set ℕ).Infinite := Set.infinite_univ
    have hfinite' :
        (Set.univ ∩ restrictedAllUnboundedSeparationSet x data N).Finite := by
      simpa only [Set.univ_inter] using hfinite
    obtain ⟨c, i, j, k, K, φ, _hi, _hj, hij, _hk, hK, _hφ,
        _hφmem, _horient, _hdelta, hlog⟩ :=
      hA.exists_fixed_pairBranch_of_finite_separated_inter
        x data N width hmin hxrep hinterval Set.univ huniv hfinite'
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
        hKpos (hxinj.comp _hφ.injective)
        (fun n ↦ hxmem (φ n)) hw₀
        (hxlim.comp _hφ.tendsto_atTop)
        (fun r ↦ (hxrep r).comp _hφ.tendsto_atTop) hlog').elim
  · exact hinfinite

/-- Normalize the all-unbounded cluster setup so its selected subsequence is
the ambient sequence.  This is the form consumed by the Hermite/rank boundary:
regular-zero membership and all limits hold at every natural index, while the
ordered clusters are exactly those already chosen by the compactness step. -/
theorem IsAbel.exists_restrictedAllUnboundedNormalizedClusterSetup
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
      (constraintMap F)).Infinite) :
    ∃ (x : ℕ → RestrictedSource (m + 1) p a)
      (w₀ : RestrictedBoxSpace p)
      (data : RepresentativeClusterSubsequence
        (fun n i ↦ A ((x n).1.1 i)))
      (width : ℕ),
      data.subsequence = id ∧
      Function.Injective x ∧
      (∀ n, x n ∈ regularZeroSet
        (restrictedBaseOpenDomain box R) (constraintMap F)) ∧
      w₀ ∈ box.closedBox ∧
      Tendsto (fun n ↦ (x n).1.2) atTop (nhds w₀) ∧
      (∀ i, Tendsto (fun n ↦ (x n).1.1 i) atTop atTop) ∧
      (∀ c, (data.orderedCluster c).Nonempty) ∧
      Pairwise (Disjoint on data.orderedCluster) ∧
      Finset.univ.biUnion data.orderedCluster =
        (Finset.univ : Finset (Fin (m + 1))) ∧
      (∀ c, Tendsto (data.orderedClusterMinTime c) atTop atTop) ∧
      (∀ c n i, i ∈ data.orderedCluster c →
        data.orderedClusterMinTime c n ≤ A ((x n).1.1 i) ∧
          A ((x n).1.1 i) ≤
            data.orderedClusterMinTime c n + (width : ℝ)) ∧
      (∀ c d, c < d → ∀ i, i ∈ data.orderedCluster c →
        ∀ j, j ∈ data.orderedCluster d →
          Tendsto (fun n ↦ A ((x n).1.1 j) - A ((x n).1.1 i))
            atTop atTop) ∧
      ∀ c d, c < d →
        Tendsto (fun n ↦ data.orderedClusterMinTime d n -
          data.orderedClusterMaxTime c n) atTop atTop := by
  obtain ⟨x, w₀, data, _width, _hsub, hxinj, hxmem, hw₀, hxlim, hxrep,
      _hnonempty, _hdisjoint, _hcover, _hmin, _hinterval, _hcross, _hgap⟩ :=
    hA.exists_restrictedAllUnboundedClusterSetup
      houter box representative offset R hDomain F hF hZ
  let y : ℕ → RestrictedSource (m + 1) p a :=
    fun n ↦ x (data.subsequence n)
  let data₀ : RepresentativeClusterSubsequence
      (fun n i ↦ A ((y n).1.1 i)) := data.restrictToSubsequence
  have htime : ∀ i, Tendsto (fun n ↦ A ((y n).1.1 i)) atTop atTop := by
    intro i
    exact hA.tendsto_atTop.comp (hxrep i)
  obtain ⟨width, hnonempty, hdisjoint, hcover, hmin, hinterval, hgap⟩ :=
    data₀.exists_orderedCluster_partition_width_of_tendsto htime
  refine ⟨y, w₀, data₀, width, rfl, hxinj, hxmem, hw₀, hxlim, hxrep,
    hnonempty, hdisjoint, hcover, hmin, hinterval, ?_, hgap⟩
  intro c d hcd i hi j hj
  exact data₀.tendsto_orderedCluster_gap_atTop hcd hi hj

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
