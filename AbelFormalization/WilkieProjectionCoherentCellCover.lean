import AbelFormalization.WilkieSection4EnrichedCells

/-!
# Projection-coherent enriched cell covers

Wilkie repeatedly projects a cell decomposition compatible with a set and
uses the induced decomposition in one fewer coordinate.  Compatibility does
not descend from an arbitrary finite cover: cells above overlapping base
pieces can carry conflicting information.  It does descend when every cell
remembers its exact projected base and those bases are equal or disjoint.

This module records precisely that one-step argument.  It is purely
set-theoretic once the enriched cell theorem
`CharbonnelEnrichedSuccessorCell.existentialProjection_carrier` is available.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A finite relative cover by enriched successor cells whose projected base
cells form a partition up to repetitions.  Repetitions are useful because a
single base cell can support several vertically stacked cells. -/
structure CharbonnelFiniteProjectionCoherentEnrichedCellCover
    (S : EuclideanSetFamily) {n : ℕ}
    (D A : Set (RealEuclidean (n + 1))) where
  Index : Type
  indexFinite : Finite Index
  cell : Index → CharbonnelEnrichedSuccessorCell S n
  target_subset_domain : A ⊆ D
  contained : ∀ i, (cell i).carrier ⊆ D
  covers : ∀ z ∈ D, ∃ i, z ∈ (cell i).carrier
  compatible : ∀ i,
    (cell i).carrier ⊆ A ∨ Disjoint (cell i).carrier A
  bases_eq_or_disjoint : ∀ i j,
    (cell i).base.carrier = (cell j).base.carrier ∨
      Disjoint (cell i).base.carrier (cell j).base.carrier

namespace CharbonnelFiniteProjectionCoherentEnrichedCellCover

/-- Membership in an enriched cell projects to membership in its recorded
base. -/
theorem base_mem_of_cell_mem
    {S : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A)
    (i : cover.Index) {z : RealEuclidean (n + 1)}
    (hz : z ∈ (cover.cell i).carrier) :
    realEuclideanTakeLeft z ∈ (cover.cell i).base.carrier := by
  have hzProjection : realEuclideanTakeLeft z ∈
      realEuclideanExistentialProjection (cover.cell i).carrier := by
    refine ⟨realEuclideanTakeRight z, ?_⟩
    rwa [realEuclideanAppend_take]
  rwa [(cover.cell i).existentialProjection_carrier] at hzProjection

/-- Every point of a recorded base has a point in the corresponding enriched
cell above it. -/
theorem exists_cell_point_over_base
    {S : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A)
    (i : cover.Index) {x : RealEuclidean n}
    (hx : x ∈ (cover.cell i).base.carrier) :
    ∃ y : RealEuclidean 1,
      realEuclideanAppend x y ∈ (cover.cell i).carrier := by
  have hxProjection : x ∈
      realEuclideanExistentialProjection (cover.cell i).carrier := by
    rwa [(cover.cell i).existentialProjection_carrier]
  exact hxProjection

/-- If one vertical cell above a base piece lies in the target, then the
whole base piece lies in the projected target. -/
theorem base_subset_projection_of_same_base_inside
    {S : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A)
    {i j : cover.Index}
    (hbase : (cover.cell i).base.carrier =
      (cover.cell j).base.carrier)
    (hinside : (cover.cell j).carrier ⊆ A) :
    (cover.cell i).base.carrier ⊆
      realEuclideanExistentialProjection A := by
  intro x hx
  obtain ⟨y, hy⟩ := cover.exists_cell_point_over_base j (hbase ▸ hx)
  exact ⟨y, hinside hy⟩

/-- The projected base cell is compatible with the projected target. -/
theorem projected_base_compatible
    {S : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A)
    (i : cover.Index) :
    (cover.cell i).base.carrier ⊆
        realEuclideanExistentialProjection A ∨
      Disjoint (cover.cell i).base.carrier
        (realEuclideanExistentialProjection A) := by
  classical
  by_cases hinside : ∃ j : cover.Index,
      (cover.cell i).base.carrier = (cover.cell j).base.carrier ∧
        (cover.cell j).carrier ⊆ A
  · obtain ⟨j, hbase, hj⟩ := hinside
    exact Or.inl (cover.base_subset_projection_of_same_base_inside hbase hj)
  · right
    rw [Set.disjoint_left]
    intro x hxi hxA
    obtain ⟨y, hxyA⟩ := hxA
    have hxyD : realEuclideanAppend x y ∈ D :=
      cover.target_subset_domain hxyA
    obtain ⟨j, hjCell⟩ := cover.covers _ hxyD
    have hxj : x ∈ (cover.cell j).base.carrier := by
      simpa only [realEuclideanTakeLeft_append] using
        cover.base_mem_of_cell_mem j hjCell
    have hbaseEq : (cover.cell i).base.carrier =
        (cover.cell j).base.carrier := by
      rcases cover.bases_eq_or_disjoint i j with heq | hdisjoint
      · exact heq
      · exact False.elim (Set.disjoint_left.mp hdisjoint hxi hxj)
    have hjInside : (cover.cell j).carrier ⊆ A := by
      rcases cover.compatible j with hjInside | hjDisjoint
      · exact hjInside
      · exact False.elim
          (Set.disjoint_left.mp hjDisjoint hjCell hxyA)
    exact hinside ⟨j, hbaseEq, hjInside⟩

/-- Projecting a coherent enriched relative cover gives a finite relative
cell cover compatible with the projected target. -/
def project
    {S : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A) :
    CharbonnelFiniteCompatibleRelativeCellCover
      (charbonnelClosure S)
      (realEuclideanExistentialProjection D)
      (realEuclideanExistentialProjection A) where
  Index := cover.Index
  indexFinite := cover.indexFinite
  cell i := (cover.cell i).base
  contained := by
    intro i x hx
    obtain ⟨y, hyCell⟩ := cover.exists_cell_point_over_base i hx
    exact ⟨y, cover.contained i hyCell⟩
  covers := by
    intro x hxD
    obtain ⟨y, hxyD⟩ := hxD
    obtain ⟨i, hi⟩ := cover.covers _ hxyD
    exact ⟨i, by
      simpa only [realEuclideanTakeLeft_append] using
        cover.base_mem_of_cell_mem i hi⟩
  compatible := cover.projected_base_compatible

end CharbonnelFiniteProjectionCoherentEnrichedCellCover

end AbelFormalization
