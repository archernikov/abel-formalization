import AbelFormalization.WilkieSection4OpenCell
import AbelFormalization.CharbonnelBoundarySelectorAssembly

/-!
# Wilkie Section 4: mixed open and lower-dimensional cell assembly

Wilkie's last assembly step treats the cells of a simultaneous base
decomposition in two different ways.  Over a nonempty open base cell, the
closed cardinality loci and the collision/escape exclusions give continuous
ordered selectors.  Over a non-open base cell, the already-proved
lower-dimensional case supplies a relative cell cover.  Empty base cells
contribute nothing.

This file performs exactly that finite dependent flattening.  The open-cell
branch can be discharged either from the operational no-escape premise or by
the source-shaped band and endpoint-locus constructor; the only geometric
cover still supplied as an input is the non-open-cell branch.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Empty base cells -/

/-- The cylinder over an empty base carrier has a relative cover with no
cells.  This avoids asking for membership of an empty cylinder in the ambient
family merely to flatten a finite base cover containing a vacuous cell. -/
def charbonnelEmptyBaseRelativeCellCover
    {C : EuclideanSetFamily} {n : ℕ}
    {base : Set (RealEuclidean n)}
    (hbase : ¬ base.Nonempty)
    {A : Set (RealEuclidean (n + 1))} :
    CharbonnelFiniteCompatibleRelativeCellCover C
      (charbonnelCylinderCell base) A :=
  { Index := Empty
    indexFinite := inferInstance
    cell := Empty.elim
    contained := fun i ↦ i.elim
    covers := by
      intro z hz
      exact (hbase ⟨realEuclideanTakeLeft z, hz⟩).elim
    compatible := fun i ↦ i.elim }

/-- A cylinder already known to avoid the target is a one-cell relative
cover.  Cylinder membership follows from WS2--WS3 and membership of the base
cell, so this constructor introduces no new family-membership premise. -/
def charbonnelDisjointCylinderRelativeCellCover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {base : Set (RealEuclidean n)}
    (hbaseShape : CharbonnelCellShape n base)
    (hbaseMem : base ∈ charbonnelClosure S n)
    {A : Set (RealEuclidean (n + 1))}
    (hdisjoint : Disjoint (charbonnelCylinderCell base) A) :
    CharbonnelFiniteCompatibleRelativeCellCover (charbonnelClosure S)
      (charbonnelCylinderCell base) A := by
  apply charbonnelEmptySelectorRelativeCellCover hn hbaseShape
  · intro z hz hzA
    exact Set.disjoint_left.mp hdisjoint hz hzA
  · exact charbonnelCylinderCell_mem_charbonnelClosure hC hn hbaseMem

/-! ## Mixed finite-base assembly -/

/-- Assemble Wilkie's Section 4 construction over a finite base cover.

For a nonempty open base cell, simultaneous compatibility with the closed
cardinality loci, together with the local no-escape and collision-locus
exclusions, invokes the completed ordered-selector construction.  A non-open
base cell is handled by the explicit lower-dimensional relative-cover input.
An empty base cell uses `charbonnelEmptyBaseRelativeCellCover` and therefore
requires neither branch.

The parameter `Cbase` is Wilkie's ambient base region.  Only open nonempty
base cells need to lie in it, since the other cells are delegated to the
lower-dimensional induction. -/
noncomputable def
    CharbonnelFiniteCompatibleCellCover.section4MixedCellCover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {baseTarget Cbase : Set (RealEuclidean p)}
    (baseCover : CharbonnelFiniteCompatibleCellCover
      (charbonnelClosure S) baseTarget)
    {A : MaxwellRelation p 1}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hNempty : interior
      (closure
        (wilkieSection4FiberCardinalityLocus Cbase A N)) = ∅)
    (hopen_subset : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      (baseCover.cell i).carrier ⊆ Cbase)
    (hcardinality_compatible : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      ∀ j, j ≤ N →
        (baseCover.cell i).carrier ⊆
            closure (wilkieSection4FiberCardinalityLocus Cbase A j) ∨
          Disjoint (baseCover.cell i).carrier
            (closure
              (wilkieSection4FiberCardinalityLocus Cbase A j)))
    (hopen_noEscape : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      MaxwellScalarFiberNoEscape (baseCover.cell i).carrier A)
    (hopen_collisionLocus : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      Disjoint (baseCover.cell i).carrier
        (wilkieSection4CollisionLocus Cbase A))
    (hnonopen : ∀ i,
      ¬ IsOpen (baseCover.cell i).carrier →
      CharbonnelFiniteCompatibleRelativeCellCover
        (charbonnelClosure S)
        (charbonnelCylinderCell (baseCover.cell i).carrier) A) :
    CharbonnelFiniteCompatibleCellCover (charbonnelClosure S) A := by
  apply baseCover.flattenRelativeCylindersGlobal
  intro i
  by_cases hnonempty : (baseCover.cell i).carrier.Nonempty
  · by_cases hopen : IsOpen (baseCover.cell i).carrier
    · exact
        charbonnelFiniteSelectorRelativeCellCover_of_section4_compatible_loci
          hC hp hN (baseCover.cell i).shape hopen hnonempty
          (baseCover.cell i).carrier_mem
          (hopen_subset i hopen hnonempty) hAmem hNempty
          (hcardinality_compatible i hopen hnonempty)
          (hopen_noEscape i hopen hnonempty)
          (hopen_collisionLocus i hopen hnonempty)
    · exact hnonopen i hopen
  · exact charbonnelEmptyBaseRelativeCellCover hnonempty

/-- Source-shaped mixed assembly using the complete Section 4 open-cell
constructor.  The operational `MaxwellScalarFiberNoEscape` premise of
`section4MixedCellCover` is replaced by Wilkie's actual data: the relation is
relatively closed in a continuous open band and every nonempty open base cell
avoids the lower and upper endpoint zero traces. -/
noncomputable def
    CharbonnelFiniteCompatibleCellCover.section4MixedCellCover_of_openCellBand
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {baseTarget Cbase : Set (RealEuclidean p)}
    (baseCover : CharbonnelFiniteCompatibleCellCover
      (charbonnelClosure S) baseTarget)
    {A : MaxwellRelation p 1} {f g : RealEuclidean p → ℝ}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hAsub : A ⊆ charbonnelOpenBand Cbase f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A : Set (charbonnelOpenBand Cbase f g)))
    (hf : ContinuousOn f Cbase) (hg : ContinuousOn g Cbase)
    (hNempty : interior
      (closure
        (wilkieSection4FiberCardinalityLocus Cbase A N)) = ∅)
    (hopen_subset : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      (baseCover.cell i).carrier ⊆ Cbase)
    (hcardinality_compatible : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      ∀ j, j ≤ N →
        (baseCover.cell i).carrier ⊆
            closure (wilkieSection4FiberCardinalityLocus Cbase A j) ∨
          Disjoint (baseCover.cell i).carrier
            (closure
              (wilkieSection4FiberCardinalityLocus Cbase A j)))
    (hopen_collisionLocus : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      Disjoint (baseCover.cell i).carrier
        (wilkieSection4CollisionLocus Cbase A))
    (hopen_lowerEndpointLocus : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      Disjoint (baseCover.cell i).carrier
        (wilkieSection4LowerEndpointLocus Cbase A f))
    (hopen_upperEndpointLocus : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      Disjoint (baseCover.cell i).carrier
        (wilkieSection4UpperEndpointLocus Cbase A g))
    (hnonopen : ∀ i,
      ¬ IsOpen (baseCover.cell i).carrier →
      CharbonnelFiniteCompatibleRelativeCellCover
        (charbonnelClosure S)
        (charbonnelCylinderCell (baseCover.cell i).carrier) A) :
    CharbonnelFiniteCompatibleCellCover (charbonnelClosure S) A := by
  apply baseCover.flattenRelativeCylindersGlobal
  intro i
  by_cases hnonempty : (baseCover.cell i).carrier.Nonempty
  · by_cases hopen : IsOpen (baseCover.cell i).carrier
    · exact
        charbonnelFiniteSelectorRelativeCellCover_of_wilkieSection4_openCell
          hC hp hN (baseCover.cell i).shape hopen hnonempty
          (baseCover.cell i).carrier_mem
          (hopen_subset i hopen hnonempty) hAmem hAsub hAclosed hf hg
          hNempty (hcardinality_compatible i hopen hnonempty)
          (hopen_collisionLocus i hopen hnonempty)
          (hopen_lowerEndpointLocus i hopen hnonempty)
          (hopen_upperEndpointLocus i hopen hnonempty)
    · exact hnonopen i hopen
  · exact charbonnelEmptyBaseRelativeCellCover hnonempty

/-- Global-space version of the source-shaped mixed assembly.  Here the base
cover is itself compatible with Wilkie's ambient base region `Cbase`.  Thus a
nonempty open cell contained in `Cbase` uses the full open-cell theorem, while
a nonempty open cell disjoint from `Cbase` contributes one cylinder disjoint
from `A` because `A` lies in the band over `Cbase`.  Non-open cells are still
the sole lower-dimensional induction input. -/
noncomputable def
    CharbonnelFiniteCompatibleCellCover.section4MixedCellCover_of_baseRefinement
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {Cbase : Set (RealEuclidean p)}
    (baseCover : CharbonnelFiniteCompatibleCellCover
      (charbonnelClosure S) Cbase)
    {A : MaxwellRelation p 1} {f g : RealEuclidean p → ℝ}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hAsub : A ⊆ charbonnelOpenBand Cbase f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A : Set (charbonnelOpenBand Cbase f g)))
    (hf : ContinuousOn f Cbase) (hg : ContinuousOn g Cbase)
    (hNempty : interior
      (closure
        (wilkieSection4FiberCardinalityLocus Cbase A N)) = ∅)
    (hcardinality_compatible : ∀ i,
      (baseCover.cell i).carrier ⊆ Cbase →
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      ∀ j, j ≤ N →
        (baseCover.cell i).carrier ⊆
            closure (wilkieSection4FiberCardinalityLocus Cbase A j) ∨
          Disjoint (baseCover.cell i).carrier
            (closure
              (wilkieSection4FiberCardinalityLocus Cbase A j)))
    (hopen_collisionLocus : ∀ i,
      (baseCover.cell i).carrier ⊆ Cbase →
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      Disjoint (baseCover.cell i).carrier
        (wilkieSection4CollisionLocus Cbase A))
    (hopen_lowerEndpointLocus : ∀ i,
      (baseCover.cell i).carrier ⊆ Cbase →
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      Disjoint (baseCover.cell i).carrier
        (wilkieSection4LowerEndpointLocus Cbase A f))
    (hopen_upperEndpointLocus : ∀ i,
      (baseCover.cell i).carrier ⊆ Cbase →
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      Disjoint (baseCover.cell i).carrier
        (wilkieSection4UpperEndpointLocus Cbase A g))
    (hnonopen : ∀ i,
      ¬ IsOpen (baseCover.cell i).carrier →
      CharbonnelFiniteCompatibleRelativeCellCover
        (charbonnelClosure S)
        (charbonnelCylinderCell (baseCover.cell i).carrier) A) :
    CharbonnelFiniteCompatibleCellCover (charbonnelClosure S) A := by
  apply baseCover.flattenRelativeCylindersGlobal
  intro i
  by_cases hnonempty : (baseCover.cell i).carrier.Nonempty
  · by_cases hopen : IsOpen (baseCover.cell i).carrier
    · by_cases hinside : (baseCover.cell i).carrier ⊆ Cbase
      · exact
          charbonnelFiniteSelectorRelativeCellCover_of_wilkieSection4_openCell
            hC hp hN (baseCover.cell i).shape hopen hnonempty
            (baseCover.cell i).carrier_mem hinside hAmem hAsub hAclosed
            hf hg hNempty
            (hcardinality_compatible i hinside hopen hnonempty)
            (hopen_collisionLocus i hinside hopen hnonempty)
            (hopen_lowerEndpointLocus i hinside hopen hnonempty)
            (hopen_upperEndpointLocus i hinside hopen hnonempty)
      · have houtside : Disjoint (baseCover.cell i).carrier Cbase :=
          (baseCover.compatible i).resolve_left hinside
        apply charbonnelDisjointCylinderRelativeCellCover hC hp
          (baseCover.cell i).shape (baseCover.cell i).carrier_mem
        rw [Set.disjoint_left]
        intro z hzCylinder hzA
        have hzBand := hAsub hzA
        exact Set.disjoint_left.mp houtside hzCylinder hzBand.1
    · exact hnonopen i hopen
  · exact charbonnelEmptyBaseRelativeCellCover hnonempty

/-- Boundary-intersection form of the mixed assembly.  Once the mixed cover
has been constructed for `A ∩ B`, closedness of `A` and containment of its
frontier in `B` transfer compatibility from `A ∩ B` to `A`.  This is the
topological step used by the existing closed-boundary pipeline. -/
noncomputable def
    CharbonnelFiniteCompatibleCellCover.section4MixedCellCover_of_boundaryIntersection
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {baseTarget Cbase : Set (RealEuclidean p)}
    (baseCover : CharbonnelFiniteCompatibleCellCover
      (charbonnelClosure S) baseTarget)
    {A B : Set (RealEuclidean (p + 1))}
    (hAclosed : IsClosed A) (hfrontier : frontier A ⊆ B)
    (hintersection_mem : A ∩ B ∈ charbonnelClosure S (p + 1))
    (hNempty : interior
      (closure
        (wilkieSection4FiberCardinalityLocus Cbase (A ∩ B) N)) = ∅)
    (hopen_subset : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      (baseCover.cell i).carrier ⊆ Cbase)
    (hcardinality_compatible : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      ∀ j, j ≤ N →
        (baseCover.cell i).carrier ⊆
            closure
              (wilkieSection4FiberCardinalityLocus Cbase (A ∩ B) j) ∨
          Disjoint (baseCover.cell i).carrier
            (closure
              (wilkieSection4FiberCardinalityLocus Cbase (A ∩ B) j)))
    (hopen_noEscape : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      MaxwellScalarFiberNoEscape (baseCover.cell i).carrier (A ∩ B))
    (hopen_collisionLocus : ∀ i,
      IsOpen (baseCover.cell i).carrier →
      (baseCover.cell i).carrier.Nonempty →
      Disjoint (baseCover.cell i).carrier
        (wilkieSection4CollisionLocus Cbase (A ∩ B)))
    (hnonopen : ∀ i,
      ¬ IsOpen (baseCover.cell i).carrier →
      CharbonnelFiniteCompatibleRelativeCellCover
        (charbonnelClosure S)
        (charbonnelCylinderCell (baseCover.cell i).carrier) (A ∩ B)) :
    CharbonnelFiniteCompatibleCellCover (charbonnelClosure S) A :=
  CharbonnelFiniteCompatibleCellCover.of_boundaryIntersection_auto
    hAclosed hfrontier
    (baseCover.section4MixedCellCover hC hp hN hintersection_mem hNempty
      hopen_subset hcardinality_compatible hopen_noEscape
      hopen_collisionLocus hnonopen)

end AbelFormalization
