import AbelFormalization.WilkieProjectionCoherentCellCoverTower
import AbelFormalization.WilkieSection4PartitionedEnrichedSelectorOutput

/-!
# Projection towers from retained relative covers

The bounded enriched source premise already supplies a finite family of
successor cells over each visible cube.  To make that family projection
coherent, it is enough to partition the recorded bases and restrict every
source cell to the partition pieces contained in its base.  No new cover of
boundary-equality loci is needed for this operation.

Repeating the construction for the successive visible/hidden splittings of
the same closed lift gives the complete projection-coherent tower.  Coordinate
reassociation identifies the lower-dimensional source target with the
projection of the preceding target, while bounded compactification commutes
with that projection.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## The positive-dimensional partition interface -/

/-- Partitioned common refinement at one specified dimension.  Unlike the
older all-dimensional interface, this does not demand nonexistent cells in
dimension zero. -/
def CharbonnelFinitePartitionedCellFamilyCommonRefinementAt
    (C : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ {I : Type} [Fintype I],
    ∀ cells : I → CharbonnelCell C n,
      Nonempty
        (CharbonnelFinitePartitionedSimultaneouslyCompatibleCellCover C
          (fun i ↦ (cells i).carrier))

/-- The partitioned common-refinement property in precisely the positive
dimensions in which recursive Charbonnel cells exist. -/
def CharbonnelPositiveDimensionalFinitePartitionedCellFamilyCommonRefinementProperty
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n →
    CharbonnelFinitePartitionedCellFamilyCommonRefinementAt C n

/-- There are no recursive Charbonnel cells in dimension zero: the base
constructor is unary and every other constructor raises a positive base
dimension. -/
theorem not_nonempty_charbonnelCell_zero (C : EuclideanSetFamily) :
    ¬ Nonempty (CharbonnelCell C 0) := by
  rintro ⟨cell⟩
  exact nomatch cell.shape

/-- The older all-dimensional partitioned interface is inconsistent.  At
dimension zero and for an empty input family it still demands a cover of the
inhabited space `ℝ⁰` by zero-dimensional Charbonnel cells. -/
theorem not_charbonnelFinitePartitionedCellFamilyCommonRefinementProperty
    (C : EuclideanSetFamily) :
    ¬ CharbonnelFinitePartitionedCellFamilyCommonRefinementProperty C := by
  intro hII
  let cells : Fin 0 → CharbonnelCell C 0 := Fin.elim0
  obtain ⟨fine⟩ := hII cells
  obtain ⟨i, _hi⟩ := fine.cover.covers (0 : RealEuclidean 0)
  exact not_nonempty_charbonnelCell_zero C ⟨fine.cover.cell i⟩

/-- Forgetting the impossible zero-dimensional clause of the older interface
recovers the corrected positive-dimensional form. -/
theorem
    charbonnelPositiveDimensionalFinitePartitionedCellFamilyCommonRefinementProperty_of_allDimensions
    {C : EuclideanSetFamily}
    (hII : CharbonnelFinitePartitionedCellFamilyCommonRefinementProperty C) :
    CharbonnelPositiveDimensionalFinitePartitionedCellFamilyCommonRefinementProperty C := by
  intro n _hn I _ cells
  exact hII cells

/-! ## Restricting a retained cell to a smaller recorded base -/

namespace CharbonnelEnrichedVerticalCell

/-- Restrict an enriched vertical cell to a smaller recursive base cell.
Every boundary graph remains in the Charbonnel closure by intersecting it
with the cylinder over the smaller base. -/
def restrictBase
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {large small : CharbonnelCell (charbonnelClosure S) n}
    (hsmall : small.carrier ⊆ large.carrier)
    (cell : CharbonnelEnrichedVerticalCell S large) :
    CharbonnelEnrichedVerticalCell S small := by
  cases cell with
  | graph f hf hgraph =>
      exact .graph f (hf.mono hsmall)
        (charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
          hC hn hsmall small.carrier_mem hgraph)
  | band f g hf hg hfg hfgraph hggraph =>
      exact .band f g (hf.mono hsmall) (hg.mono hsmall)
        (fun x hx ↦ hfg x (hsmall hx))
        (charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
          hC hn hsmall small.carrier_mem hfgraph)
        (charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
          hC hn hsmall small.carrier_mem hggraph)
  | lowerRay g hg hgraph =>
      exact .lowerRay g (hg.mono hsmall)
        (charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
          hC hn hsmall small.carrier_mem hgraph)
  | upperRay f hf hgraph =>
      exact .upperRay f (hf.mono hsmall)
        (charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
          hC hn hsmall small.carrier_mem hgraph)
  | cylinder =>
      exact .cylinder

@[simp]
theorem restrictBase_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {large small : CharbonnelCell (charbonnelClosure S) n}
    (hsmall : small.carrier ⊆ large.carrier)
    (cell : CharbonnelEnrichedVerticalCell S large) :
    (cell.restrictBase hC hn hsmall).carrier =
      cell.carrierOn small.carrier := by
  cases cell <;> rfl

end CharbonnelEnrichedVerticalCell

namespace CharbonnelEnrichedSuccessorCell

/-- Restrict a retained successor cell to a recursive subcell of its recorded
base. -/
def restrictBase
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelEnrichedSuccessorCell S n)
    (small : CharbonnelCell (charbonnelClosure S) n)
    (hsmall : small.carrier ⊆ cell.base.carrier) :
    CharbonnelEnrichedSuccessorCell S n :=
  ⟨small, cell.vertical.restrictBase hC hn hsmall⟩

@[simp]
theorem restrictBase_base
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelEnrichedSuccessorCell S n)
    (small : CharbonnelCell (charbonnelClosure S) n)
    (hsmall : small.carrier ⊆ cell.base.carrier) :
    (cell.restrictBase hC hn small hsmall).base = small :=
  rfl

theorem restrictBase_carrier_subset
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelEnrichedSuccessorCell S n)
    (small : CharbonnelCell (charbonnelClosure S) n)
    (hsmall : small.carrier ⊆ cell.base.carrier) :
    (cell.restrictBase hC hn small hsmall).carrier ⊆ cell.carrier := by
  rw [CharbonnelEnrichedSuccessorCell.carrier, restrictBase,
    CharbonnelEnrichedVerticalCell.restrictBase_carrier,
    cell.vertical.carrierOn_eq_inter_cylinder small.carrier hsmall]
  exact inter_subset_left

theorem mem_restrictBase_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelEnrichedSuccessorCell S n)
    (small : CharbonnelCell (charbonnelClosure S) n)
    (hsmall : small.carrier ⊆ cell.base.carrier)
    {z : RealEuclidean (n + 1)} (hz : z ∈ cell.carrier)
    (hx : realEuclideanTakeLeft z ∈ small.carrier) :
    z ∈ (cell.restrictBase hC hn small hsmall).carrier := by
  rw [CharbonnelEnrichedSuccessorCell.carrier, restrictBase,
    CharbonnelEnrichedVerticalCell.restrictBase_carrier,
    cell.vertical.carrierOn_eq_inter_cylinder small.carrier hsmall]
  exact ⟨hz, by simpa [charbonnelCylinderCell] using hx⟩

end CharbonnelEnrichedSuccessorCell

/-! ## Partitioning the bases of an existing enriched relative cover -/

/-- Partitioned common refinement applied only to the recorded bases turns an
existing enriched relative cover into a projection-coherent enriched cover on
the same domain.  This avoids the stronger closed-member-cover premise needed
by the ordered-selector reconstruction. -/
theorem
    exists_charbonnelFiniteProjectionCoherentEnrichedCellCover_of_partitionedBases
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (hII : CharbonnelFinitePartitionedCellFamilyCommonRefinementAt
      (charbonnelClosure S) n)
    {D A : Set (RealEuclidean (n + 1))}
    (source : CharbonnelFiniteEnrichedCompatibleRelativeCellCover S n D A)
    (hAD : A ⊆ D) :
  Nonempty
      (CharbonnelFiniteProjectionCoherentEnrichedCellCover S D A) := by
  classical
  let _ : Finite source.Index := source.indexFinite
  let _ : Fintype source.Index := Fintype.ofFinite source.Index
  obtain ⟨fine⟩ := hII (fun i ↦ (source.cell i).base)
  let Index := Σ k : Fin fine.cover.count,
    {i : source.Index //
      (fine.cover.cell k).carrier ⊆ (source.cell i).base.carrier}
  let cell : Index → CharbonnelEnrichedSuccessorCell S n :=
    fun p ↦ (source.cell p.2.1).restrictBase hC hn
      (fine.cover.cell p.1) p.2.2
  refine ⟨
    { Index := Index
      indexFinite := inferInstance
      cell := cell
      target_subset_domain := hAD
      contained := ?_
      covers := ?_
      compatible := ?_
      bases_eq_or_disjoint := ?_ }⟩
  · intro p
    exact (CharbonnelEnrichedSuccessorCell.restrictBase_carrier_subset
      hC hn (source.cell p.2.1) (fine.cover.cell p.1) p.2.2).trans
        (source.contained p.2.1)
  · intro z hzD
    obtain ⟨i, hzi⟩ := source.covers z hzD
    have hxSource : realEuclideanTakeLeft z ∈
        (source.cell i).base.carrier := by
      rw [← (source.cell i).existentialProjection_carrier]
      refine ⟨realEuclideanTakeRight z, ?_⟩
      rwa [realEuclideanAppend_take]
    obtain ⟨k, hxk⟩ := fine.cover.covers (realEuclideanTakeLeft z)
    have hkSubset : (fine.cover.cell k).carrier ⊆
        (source.cell i).base.carrier := by
      rcases fine.cover.compatible k i with hsubset | hdisjoint
      · exact hsubset
      · exact False.elim (Set.disjoint_left.mp hdisjoint hxk hxSource)
    let p : Index := ⟨k, ⟨i, hkSubset⟩⟩
    refine ⟨p, ?_⟩
    exact CharbonnelEnrichedSuccessorCell.mem_restrictBase_carrier
      hC hn (source.cell i) (fine.cover.cell k) hkSubset hzi hxk
  · intro p
    have hsub : (cell p).carrier ⊆ (source.cell p.2.1).carrier :=
      CharbonnelEnrichedSuccessorCell.restrictBase_carrier_subset
        hC hn (source.cell p.2.1) (fine.cover.cell p.1) p.2.2
    rcases source.compatible p.2.1 with htarget | hdisjoint
    · exact Or.inl (hsub.trans htarget)
    · exact Or.inr (hdisjoint.mono hsub Subset.rfl)
  · intro p r
    simpa [cell, CharbonnelEnrichedSuccessorCell.restrictBase] using
      fine.cells_eq_or_disjoint p.1 r.1

/-! ## Iterating the source covers through all visible splittings -/

/-- Every bounded image lies in the corresponding open cube. -/
theorem wilkieBoundedImage_subset_openCube
    {n : ℕ} (A : Set (RealEuclidean n)) :
    wilkieBoundedImage A ⊆ wilkieOpenCube n := by
  rintro _ ⟨x, _hx, rfl⟩
  exact wilkieBoundedMap_mem_openCube n x

/-- Projecting the last coordinate from an open cube gives the lower open
cube. -/
@[simp]
theorem realEuclideanExistentialProjection_wilkieOpenCube_succ (n : ℕ) :
    realEuclideanExistentialProjection (wilkieOpenCube (n + 1)) =
      wilkieOpenCube n := by
  ext x
  simp only [realEuclideanExistentialProjection, wilkieOpenCube,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, hy⟩ i
    simpa [realEuclideanAppend] using hy (Fin.castAdd 1 i)
  · intro hx
    refine ⟨0, ?_⟩
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa [realEuclideanAppend] using hx j
    · fin_cases j
      norm_num [realEuclideanAppend]

/-- Enriched relative covers for every visible/hidden split, together with a
partitioned common-refinement theorem for their recorded bases, construct the
entire bounded projection-coherent tower. -/
theorem
    wilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty_of_enrichedRelativeCovers
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hII :
      CharbonnelPositiveDimensionalFinitePartitionedCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    (hsource : WilkieBoundedEnrichedProjectedClosedLiftCellCoverProperty S) :
    WilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty S := by
  intro n
  induction n with
  | zero =>
      intro q hn
      omega
  | succ n ih =>
      intro q _hn B hBclosed hBmem
      obtain ⟨source⟩ := hsource (n := n + 1) (q := q)
        (by omega) hBclosed hBmem
      obtain ⟨top⟩ :=
        exists_charbonnelFiniteProjectionCoherentEnrichedCellCover_of_partitionedBases
          hC (by omega) (hII (by omega)) source
            (wilkieBoundedImage_subset_openCube _)
      by_cases hn : n = 0
      · subst n
        exact ⟨.one top⟩
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        let B' : Set (RealEuclidean ((n + 1) + (1 + q))) :=
          charbonnelWitnessReassociation (n := n + 1) (q := 1) (r := q) B
        have hBclosed' : IsClosed B' := by
          exact isClosed_charbonnelWitnessReassociation hBclosed
        have hBmem' : B' ∈ charbonnelClosure S ((n + 1) + (1 + q)) := by
          exact hC.toDescriptionReindexBase.coordinateReindex
            (by omega : 0 < ((n + 1) + 1) + q) hBmem
              (finAddAssocCoordinateEquiv (n + 1) 1 q).symm
        obtain ⟨lower⟩ := ih (q := 1 + q) hnpos
          (B := B') hBclosed' hBmem'
        have htarget :
            realEuclideanExistentialProjection
                (wilkieBoundedImage
                  (realEuclideanExistentialProjection B)) =
              wilkieBoundedImage
                (realEuclideanExistentialProjection B') := by
          rw [realEuclideanExistentialProjection_wilkieBoundedImage]
          congr 1
          exact
            (realEuclideanExistentialProjection_witnessReassociation B).symm
        refine ⟨.succ top ?_⟩
        simpa only [realEuclideanExistentialProjection_wilkieOpenCube_succ,
          htarget] using lower

/-- Under partitioned common refinement, projection-coherent towers contain
exactly the same bounded source information as enriched relative covers. -/
theorem
    wilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty_iff_enrichedRelativeCovers
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hII :
      CharbonnelPositiveDimensionalFinitePartitionedCellFamilyCommonRefinementProperty
      (charbonnelClosure S)) :
    WilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty S ↔
      WilkieBoundedEnrichedProjectedClosedLiftCellCoverProperty S := by
  constructor
  · exact
      wilkieBoundedEnrichedProjectedClosedLiftCellCoverProperty_of_projectionCoherentTowers
  · exact
      wilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty_of_enrichedRelativeCovers
        hC hII

/-! ## Literal-zero source assembly -/

/-- For a literal-zero family, the existing bounded enriched relative-cover
assembly and partitioned common refinement already imply the full bounded
projection-coherent tower assembly. -/
theorem
    charbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly_of_enrichedRelativeCovers
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hII :
      CharbonnelPositiveDimensionalFinitePartitionedCellFamilyCommonRefinementProperty
      (charbonnelClosure (literalZeroSetFamily G)))
    (hsource : CharbonnelBoundedEnrichedClosedBoundaryCellCoverAssembly G) :
    CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly G := by
  intro hboundary
  exact
    wilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty_of_enrichedRelativeCovers
      (literalZeroSet_charbonnelClosure_positiveArityWeakSetStructure
        hG hsmooth)
      hII (hsource hboundary)

/-- For literal-zero families with partitioned common refinement, the tower
assembly is equivalent to the existing bounded enriched relative-cover
assembly.  Thus those two source interfaces, and no further closed-member
cover datum, are the remaining Section 4 input in this route. -/
theorem
    charbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly_iff_enrichedRelativeCovers
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hII :
      CharbonnelPositiveDimensionalFinitePartitionedCellFamilyCommonRefinementProperty
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly G ↔
      CharbonnelBoundedEnrichedClosedBoundaryCellCoverAssembly G := by
  constructor
  · exact
      charbonnelBoundedEnrichedClosedBoundaryCellCoverAssembly_of_projectionCoherentTowers
  · exact
      charbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly_of_enrichedRelativeCovers
        hG hsmooth hII

end AbelFormalization
