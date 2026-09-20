import AbelFormalization.WilkieSection4DeepSimultaneousInduction

/-!
# The retained graph branch of Wilkie's Section 4 induction

A target relatively closed in a graph cell projects losslessly to the
retained base.  This file lifts a partitioned deep cover of that projected
target back through the graph.  The lifted family remains a partition and its
hereditary projection coherence is exactly the coherence of the lower cover.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

namespace CharbonnelDeepEnrichedCell

/-- Restrict a retained graph to a deep subcell of its retained base. -/
def liftThroughGraph
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (small base : CharbonnelDeepEnrichedCell S n)
    (hsmall : small.carrier ⊆ base.carrier)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1)) :
    CharbonnelDeepEnrichedCell S (n + 1) :=
  small.ofVertical hC hn
    (.graph f (hf.mono hsmall)
      (charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
        hC hn hsmall (small.toCell hC).carrier_mem hgraph))

@[simp]
theorem liftThroughGraph_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (small base : CharbonnelDeepEnrichedCell S n)
    (hsmall : small.carrier ⊆ base.carrier)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1)) :
    (small.liftThroughGraph hC hn base hsmall f hf hgraph).carrier =
      charbonnelRestrictedGraph small.carrier f := by
  rfl

@[simp]
theorem liftThroughGraph_projectedBase
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (small base : CharbonnelDeepEnrichedCell S n)
    (hsmall : small.carrier ⊆ base.carrier)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1)) :
    (small.liftThroughGraph hC hn base hsmall f hf hgraph).projectedBase hn =
      small := by
  exact ofVertical_projectedBase hC hn small _

end CharbonnelDeepEnrichedCell

namespace CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover

/-- Lift a partitioned deep cover of a projected target through a retained
graph.  This is the complete data-producing part of the graph-cell branch of
Wilkie's simultaneous induction. -/
def liftThroughGraph
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {m : ℕ}
    (base : CharbonnelDeepEnrichedCell S (m + 1))
    (f : RealEuclidean (m + 1) → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (m + 2))
    {J : Type}
    (target : J → Set (RealEuclidean (m + 2)))
    (htarget : ∀ j, target j ⊆
      charbonnelRestrictedGraph base.carrier f)
    (cover :
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S base.carrier
          (fun j ↦ realEuclideanExistentialProjection
            (n := m + 1) (m := 1) (target j))) :
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
      S (charbonnelRestrictedGraph base.carrier f) target := by
  let hn : 0 < m + 1 := by omega
  let cell : cover.Index → CharbonnelDeepEnrichedCell S (m + 2) :=
    fun i ↦ (cover.cell i).liftThroughGraph hC hn base
      (cover.contained i) f hf hgraph
  exact
    { Index := cover.Index
      indexFinite := cover.indexFinite
      cell := cell
      contained := by
        intro i z hz
        exact ⟨cover.contained i hz.1, hz.2⟩
      covers := by
        intro z hz
        obtain ⟨i, hi⟩ := cover.covers (realEuclideanTakeLeft z) hz.1
        exact ⟨i, by
          change realEuclideanTakeLeft z ∈ (cover.cell i).carrier ∧ _
          exact ⟨hi, hz.2⟩⟩
      compatible := by
        intro i j
        rcases cover.compatible i j with hinside | hdisjoint
        · left
          intro z hz
          obtain ⟨y, hy⟩ := hinside hz.1
          have hyGraph := htarget j hy
          have hright : realEuclideanTakeRight z = y := by
            funext k
            rw [Fin.eq_zero k]
            have hzValue :
                f (realEuclideanTakeLeft z) =
                  realEuclideanTakeRight z 0 := hz.2.symm
            have hyValue :
                f (realEuclideanTakeLeft z) = y 0 := by
              simpa using hyGraph.2.symm
            linarith
          have hzy : z =
              realEuclideanAppend (realEuclideanTakeLeft z) y := by
            rw [← hright]
            exact (realEuclideanAppend_takeLeft_takeRight z).symm
          rwa [hzy]
        · right
          rw [Set.disjoint_left]
          intro z hz hzTarget
          exact Set.disjoint_left.mp hdisjoint hz.1
            ⟨realEuclideanTakeRight z, by
              rwa [realEuclideanAppend_takeLeft_takeRight]⟩
      cells_eq_or_disjoint := by
        intro i k
        rcases cover.cells_eq_or_disjoint i k with heq | hdisjoint
        · left
          simp only [cell,
            CharbonnelDeepEnrichedCell.liftThroughGraph_carrier]
          rw [heq]
        · right
          rw [Set.disjoint_left]
          intro z hzi hzk
          exact Set.disjoint_left.mp hdisjoint hzi.1 hzk.1
      hereditary_projection_coherent := by
        change
          (∀ i k,
            ((cell i).projectedBase hn).carrier =
                ((cell k).projectedBase hn).carrier ∨
              Disjoint ((cell i).projectedBase hn).carrier
                ((cell k).projectedBase hn).carrier) ∧
            CharbonnelDeepCellFamilyProjectionCoherent m
              (fun i ↦ (cell i).projectedBase hn)
        constructor
        · intro i k
          simpa only [cell,
            CharbonnelDeepEnrichedCell.liftThroughGraph_projectedBase] using
            cover.cells_eq_or_disjoint i k
        · simpa only [cell,
            CharbonnelDeepEnrichedCell.liftThroughGraph_projectedBase] using
            cover.hereditary_projection_coherent }

end CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover

end AbelFormalization
