import AbelFormalization.ClusterBalancing
import AbelFormalization.RepresentativeClusterSubsequenceRestriction

/-!
# One fixed balancing trace for every ordered cluster

The ordered cluster partition already supplies a uniform width bound.  This
module feeds its literal finite clusters to the simultaneous balancing
selector and obtains one further subsequence on which every decrement list
and every final order is fixed.  It is the finite-pigeonhole choice made
before the algebraic transformations in the separated-cluster argument.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

/-- Write the positive cardinality of an ordered cluster as a successor. -/
def orderedClusterTailSize
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) : ℕ :=
  (data.orderedCluster c).card - 1

theorem orderedClusterTailSize_add_one
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    data.orderedClusterTailSize c + 1 = (data.orderedCluster c).card := by
  have hpos : 0 < (data.orderedCluster c).card :=
    Finset.card_pos.mpr (data.orderedCluster_nonempty c)
  unfold orderedClusterTailSize
  omega

/-- Canonical enumeration of a cluster, with its cardinality displayed in
the successor form required by the balancing and hierarchy APIs. -/
def orderedClusterEnumeration
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    Fin (data.orderedClusterTailSize c + 1) → Fin m :=
  fun i ↦ (((data.orderedCluster c).equivFin).symm
    (finCongr (data.orderedClusterTailSize_add_one c) i)).1

theorem orderedClusterEnumeration_mem
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    data.orderedClusterEnumeration c i ∈ data.orderedCluster c := by
  exact (((data.orderedCluster c).equivFin).symm
    (finCongr (data.orderedClusterTailSize_add_one c) i)).2

/-- The original Abel-time vector of one ordered cluster in its canonical
successor-cardinality enumeration. -/
def orderedClusterRawTime
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (n : ℕ) (c : Fin data.orderedClusterCount) :
    Fin (data.orderedClusterTailSize c + 1) → ℝ :=
  fun i ↦ time (data.subsequence n) (data.orderedClusterEnumeration c i)

/-- Simultaneously choose all balancing plans and pass to one subsequence on
which every cluster's decrement list and final permutation are constant.
The same natural `D` bounds the original width of every cluster and every
chosen decrement-list length. -/
theorem exists_fixed_orderedClusterBalancing_subsequence
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) :
    ∃ (D : ℕ) (φ : ℕ → ℕ)
        (fixedSteps : ∀ c : Fin data.orderedClusterCount,
          List (Fin (data.orderedClusterTailSize c + 1)))
        (fixedOrder : ∀ c : Fin data.orderedClusterCount,
          Equiv.Perm (Fin (data.orderedClusterTailSize c + 1)))
        (plans : ∀ n (c : Fin data.orderedClusterCount),
          ClusterBalancingPlan
            (data.orderedClusterRawTime (φ n) c)
            (data.orderedClusterMinTime c (φ n))),
      StrictMono φ ∧
      (∀ c n i,
        data.orderedClusterMinTime c n ≤ data.orderedClusterRawTime n c i ∧
        data.orderedClusterRawTime n c i ≤
          data.orderedClusterMinTime c n + (D : ℝ)) ∧
      (∀ c, (fixedSteps c).length ≤
        (data.orderedClusterTailSize c + 1) * (⌊(D : ℝ)⌋₊ + 1)) ∧
      (∀ n c, (plans n c).steps = fixedSteps c) ∧
      ∀ n c, (plans n c).finalOrder = fixedOrder c := by
  classical
  obtain ⟨D, _hnonempty, _hdisjoint, _hcover, hinterval, _hgap⟩ :=
    data.exists_orderedCluster_partition_width
  have hbase : ∀ n (c : Fin data.orderedClusterCount)
      (i : Fin (data.orderedClusterTailSize c + 1)),
      data.orderedClusterMinTime c n ≤ data.orderedClusterRawTime n c i := by
    intro n c i
    exact (hinterval c n (data.orderedClusterEnumeration c i)
      (data.orderedClusterEnumeration_mem c i)).1
  have hwidth : ∀ n (c : Fin data.orderedClusterCount)
      (i : Fin (data.orderedClusterTailSize c + 1)),
      data.orderedClusterRawTime n c i -
          data.orderedClusterMinTime c n ≤ (D : ℝ) := by
    intro n c i
    have hi := (hinterval c n (data.orderedClusterEnumeration c i)
      (data.orderedClusterEnumeration_mem c i)).2
    change time (data.subsequence n) (data.orderedClusterEnumeration c i) -
        data.orderedClusterMinTime c n ≤ (D : ℝ)
    linarith
  obtain ⟨φ, fixedSteps, fixedOrder, plans, hφ, hlength,
      hsteps, horder⟩ :=
    exists_simultaneously_fixed_clusterBalancing_subsequence
      (fun c : Fin data.orderedClusterCount ↦ data.orderedClusterTailSize c)
      (fun n c ↦ data.orderedClusterRawTime n c)
      (fun n c ↦ data.orderedClusterMinTime c n) (D : ℝ)
      hbase hwidth
  exact ⟨D, φ, fixedSteps, fixedOrder, plans, hφ,
    fun c n i ↦ hinterval c n (data.orderedClusterEnumeration c i)
      (data.orderedClusterEnumeration_mem c i),
    by simpa using hlength, hsteps, horder⟩

end RepresentativeClusterSubsequence
end AbelFormalization
