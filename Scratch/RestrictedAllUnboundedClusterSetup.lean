import AbelFormalization.RestrictedAllRepresentativesDiverge
import AbelFormalization.RestrictedOrderedClusterPartition

/-!
# Ordered cluster setup in the all-unbounded branch

This module composes the outer representative-count induction step with the
canonical ordered clustering of Abel times.  Starting from an infinite base
regular-zero set, it selects one strict subsequence on which the box
coordinates still converge, every source representative tends to positive
infinity, the representatives form uniformly bounded ordered clusters, and
the gaps between successive ordered clusters diverge.
-/

noncomputable section

open Filter Function Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- The complete ordered-cluster data extracted from an infinite base
regular-zero set in the all-unbounded branch.  The strict subsequence is
`data.subsequence`; all sequence assertions below are already restricted to
that subsequence. -/
theorem IsAbel.exists_restrictedAllUnboundedClusterSetup
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
    (hF : ∀ k, F k ∈ restrictedExpressionBase box
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (hZ : (regularZeroSet (restrictedBaseOpenDomain box R)
      (constraintMap F)).Infinite) :
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
      ∀ c d, c < d →
        Tendsto (fun n ↦
          data.orderedClusterMinTime d n -
            data.orderedClusterMaxTime c n) atTop atTop := by
  obtain ⟨x, w₀, hxinj, hxmem, hw₀, hxlim, hxrep⟩ :=
    hA.exists_restrictedRegularZeroSequence_all_representatives_tendsto
      houter box representative offset R hDomain F hF hZ
  obtain ⟨data⟩ := exists_representativeClusterSubsequence
    (fun n i ↦ A ((x n).1.1 i))
  have htime : ∀ i, Tendsto (fun n ↦ A ((x n).1.1 i)) atTop atTop := by
    intro i
    exact hA.tendsto_atTop.comp (hxrep i)
  obtain ⟨width, hnonempty, hdisjoint, hcover, hmin, hinterval, hgap⟩ :=
    data.exists_orderedCluster_partition_width_of_tendsto htime
  refine ⟨x, w₀, data, width, data.strictMono_subsequence, ?_, ?_, hw₀,
    ?_, ?_, hnonempty, hdisjoint, hcover, hmin, hinterval, ?_, hgap⟩
  · exact hxinj.comp data.strictMono_subsequence.injective
  · intro n
    exact hxmem (data.subsequence n)
  · change Tendsto
      ((fun n ↦ (x n).1.2) ∘ data.subsequence) atTop (nhds w₀)
    exact hxlim.comp data.strictMono_subsequence.tendsto_atTop
  · intro i
    change Tendsto
      ((fun n ↦ (x n).1.1 i) ∘ data.subsequence) atTop atTop
    exact (hxrep i).comp data.strictMono_subsequence.tendsto_atTop
  · intro c d hcd i hi j hj
    exact data.tendsto_orderedCluster_gap_atTop hcd hi hj

end AbelFormalization
