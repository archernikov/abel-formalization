import AbelFormalization.WilkieProjectionCoherentCellCover
import AbelFormalization.WilkieSection4EnrichedSelectorOutput
import AbelFormalization.CharbonnelSourceEnrichedCellPipeline

/-!
# Partitioned retained selector output

The simultaneous common-refinement interface used in the preceding Section 4
formalization only says that each new cell is compatible with every old cell.
It does not say that two new cells are disjoint, and therefore cannot by itself
make the recorded bases in the retained selector output projection coherent.

Wilkie's source decomposition is a partition.  This file isolates exactly that
additional conclusion in a source-shaped common-refinement property and carries
it through the equality-locus refinement and ordered-selector construction.
The resulting retained enriched cover has pairwise equal-or-disjoint recorded
bases, hence gives a `CharbonnelFiniteProjectionCoherentEnrichedCellCover` for
each input target.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## The missing partition clause in common refinement -/

/-- A simultaneous compatible cell cover whose output cells form a partition
up to repetitions.  Equality is allowed because repetitions are harmless and
are useful after flattening indexed local covers. -/
structure CharbonnelFinitePartitionedSimultaneouslyCompatibleCellCover
    (C : EuclideanSetFamily) {n : ℕ} {I : Type}
    (target : I → Set (RealEuclidean n)) where
  cover : CharbonnelFiniteSimultaneouslyCompatibleCellCover C target
  cells_eq_or_disjoint : ∀ i j,
    (cover.cell i).carrier = (cover.cell j).carrier ∨
      Disjoint (cover.cell i).carrier (cover.cell j).carrier

/-- Source-shaped strengthening of finite cell-family common refinement: the
common compatible cover is also a partition up to repeated cells. -/
def CharbonnelFinitePartitionedCellFamilyCommonRefinementProperty
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ} {I : Type} [Fintype I],
    ∀ cells : I → CharbonnelCell C n,
      Nonempty
        (CharbonnelFinitePartitionedSimultaneouslyCompatibleCellCover C
          (fun i ↦ (cells i).carrier))

/-- Forgetting the partition clause recovers the common-refinement property
used by the earlier Section 4 construction. -/
theorem charbonnelFiniteCellFamilyCommonRefinementProperty_of_partitioned
    {C : EuclideanSetFamily}
    (hII : CharbonnelFinitePartitionedCellFamilyCommonRefinementProperty C) :
    CharbonnelFiniteCellFamilyCommonRefinementProperty C := by
  intro n I _ cells
  obtain ⟨fine⟩ := hII cells
  exact ⟨fine.cover⟩

/-! ## A partitioned equality-compatible base refinement -/

/-- The equality-compatible base refinement together with the partition
property of its output cells. -/
structure CharbonnelPartitionedEnrichedEqualityBaseRefinement
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    (input : I → CharbonnelEnrichedSuccessorCell S n) where
  refinement : CharbonnelEnrichedEqualityBaseRefinement input
  cells_eq_or_disjoint : ∀ i j,
    (refinement.cell i).carrier = (refinement.cell j).carrier ∨
      Disjoint (refinement.cell i).carrier (refinement.cell j).carrier

/-- Lower-dimensional closed-cell covers and partitioned common refinement
construct the equality-compatible base partition needed by the successor
selector step. -/
theorem exists_charbonnelPartitionedEnrichedEqualityBaseRefinement
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFinitePartitionedCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {I : Type} [Fintype I]
    (input : I → CharbonnelEnrichedSuccessorCell S n) :
    Nonempty (CharbonnelPartitionedEnrichedEqualityBaseRefinement input) := by
  classical
  let Boundary := CharbonnelEnrichedBoundaryIndex input
  let target : Boundary × Boundary → Set (RealEuclidean n) :=
    fun qr ↦ charbonnelEnrichedBoundaryEqualityTarget input qr.1 qr.2
  have htarget : ∀ qr, Nonempty
      (CharbonnelFiniteCompatibleCellCover
        (charbonnelClosure S) (target qr)) := by
    intro qr
    apply hI hn isClosed_closure
    exact closure_charbonnelBoundaryEqualityLocus_mem_charbonnelClosure
      hC hn ((input qr.1.1).boundary_graph_mem qr.1.2)
        ((input qr.2.1).boundary_graph_mem qr.2.2)
  have hIIordinary : CharbonnelFiniteCellFamilyCommonRefinementProperty
      (charbonnelClosure S) :=
    charbonnelFiniteCellFamilyCommonRefinementProperty_of_partitioned hII
  obtain ⟨old⟩ :=
    finiteSimultaneouslyCompatibleCellCover_of_individual_fintype
      (finiteCompatibleCoverCommonRefinement_of_cellFamily hIIordinary)
      target htarget
  let oldAndBases : (Fin old.count ⊕ I) →
      CharbonnelCell (charbonnelClosure S) n
    | Sum.inl k => old.cell k
    | Sum.inr j => (input j).base
  obtain ⟨fine⟩ := hII oldAndBases
  let refinement : CharbonnelEnrichedEqualityBaseRefinement input :=
    { count := fine.cover.count
      cell := fine.cover.cell
      covers := fine.cover.covers
      base_compatible := by
        intro i j
        simpa [oldAndBases] using fine.cover.compatible i (Sum.inr j)
      equality_compatible := by
        intro i q r
        apply compatible_target_of_compatible_cover_cells
          (cover := old.targetCover (q, r))
        intro k
        change (fine.cover.cell i).carrier ⊆ (old.cell k).carrier ∨
          Disjoint (fine.cover.cell i).carrier (old.cell k).carrier
        simpa [oldAndBases] using
          fine.cover.compatible i (Sum.inl k) }
  refine ⟨
    { refinement := refinement
      cells_eq_or_disjoint := ?_ }⟩
  intro i j
  exact fine.cells_eq_or_disjoint i j

/-! ## Local retained selector covers with their exact base exposed -/

/-- A retained local selector cover together with the fact that every output
cell records the base over which the selector construction was performed. -/
structure CharbonnelFiniteEnrichedLocalSelectorCoverOverBase
    (S : EuclideanSetFamily) {n : ℕ} {I : Type}
    (base : CharbonnelCell (charbonnelClosure S) n)
    (target : I → Set (RealEuclidean (n + 1))) where
  cover : CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
    S (charbonnelCylinderCell base.carrier) target
  cell_base_eq : ∀ i, (cover.cell i).base.carrier = base.carrier

/-- The retained ordered-selector construction over one refined cell records
that same cell as the base of every graph, band, ray, or cylinder it emits. -/
theorem exists_charbonnelEnrichedLocalSelectorCoverRetained_overBase
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {I : Type} [Fintype I]
    {input : I → CharbonnelEnrichedSuccessorCell S n}
    (refinement : CharbonnelEnrichedEqualityBaseRefinement input)
    (k : Fin refinement.count) :
    Nonempty
      (CharbonnelFiniteEnrichedLocalSelectorCoverOverBase S
        (refinement.cell k) (fun i ↦ (input i).carrier)) := by
  classical
  obtain ⟨ordering⟩ := exists_charbonnelActiveBoundaryOrdering refinement k
  let J := CharbonnelActiveEnrichedBoundary refinement k
  let active : J → RealEuclidean n → ℝ :=
    charbonnelActiveEnrichedBoundaryFunction refinement k
  let selector : Fin ordering.count → RealEuclidean n → ℝ :=
    fun i ↦ active (ordering.origin i)
  have hcontinuous : ∀ i,
      ContinuousOn (selector i) (refinement.cell k).carrier := by
    intro i
    exact ((input (ordering.origin i).1.1).boundary_continuous
      (ordering.origin i).1.2).mono (ordering.origin i).2
  have hordered : ∀ x ∈ (refinement.cell k).carrier,
      StrictMono (fun i ↦ selector i x) := by
    simpa [selector, active] using ordering.strictlyOrdered
  have hgraph : ∀ i,
      charbonnelRestrictedGraph (refinement.cell k).carrier (selector i) ∈
        charbonnelClosure S (n + 1) := by
    intro i
    apply charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
      hC hn (ordering.origin i).2 (refinement.cell k).carrier_mem
    exact (input (ordering.origin i).1.1).boundary_graph_mem
      (ordering.origin i).1.2
  by_cases hr : 0 < ordering.count
  · let cell : CharbonnelOrderedSelectorRegion ordering.count →
        CharbonnelEnrichedSuccessorCell S n :=
      charbonnelOrderedSelectorEnrichedCell (refinement.cell k)
        selector hr hcontinuous hordered hgraph
    let cover :
        CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
          S (charbonnelCylinderCell (refinement.cell k).carrier)
          (fun i ↦ (input i).carrier) :=
      { Index := CharbonnelOrderedSelectorRegion ordering.count
        indexFinite := inferInstance
        cell := cell
        contained := by
          intro region z hz
          have hcarrier : (cell region).carrier =
              charbonnelOrderedSelectorRegionCarrier
                (refinement.cell k).carrier selector hr region := by
            simp [cell]
          rw [hcarrier] at hz
          exact charbonnelOrderedSelectorRegionCarrier_subset_cylinder
            (refinement.cell k).carrier selector hr region hz
        covers := by
          intro z hz
          obtain ⟨region, hregion⟩ :=
            exists_charbonnelOrderedSelectorRegion_contains hr
              (fun i ↦ selector i (realEuclideanTakeLeft z))
              (realEuclideanTakeRight z 0)
          refine ⟨region, ?_⟩
          have hcarrier : (cell region).carrier =
              charbonnelOrderedSelectorRegionCarrier
                (refinement.cell k).carrier selector hr region := by
            simp [cell]
          rw [hcarrier]
          cases region <;> exact ⟨hz, hregion⟩
        compatible := by
          intro region i
          have hcarrier : (cell region).carrier =
              charbonnelOrderedSelectorRegionCarrier
                (refinement.cell k).carrier selector hr region := by
            simp [cell]
          rw [hcarrier]
          change charbonnelOrderedSelectorRegionCarrier
              (refinement.cell k).carrier selector hr region ⊆
                (input i).carrier ∨
            Disjoint (charbonnelOrderedSelectorRegionCarrier
              (refinement.cell k).carrier selector hr region) (input i).carrier
          have hregion :
              charbonnelOrderedSelectorRegionCarrier
                  (refinement.cell k).carrier selector hr region ⊆
                charbonnelCylinderCell (refinement.cell k).carrier :=
            charbonnelOrderedSelectorRegionCarrier_subset_cylinder
              (refinement.cell k).carrier selector hr region
          rcases refinement.base_compatible k i with hsubset | hdisjoint
          · have hrep : ∀ b : Fin (input i).boundaryCount,
                ∃ j, Set.EqOn ((input i).boundary b) (selector j)
                  (refinement.cell k).carrier := by
              intro b
              let q : J := ⟨⟨i, b⟩, hsubset⟩
              obtain ⟨j, hj⟩ := ordering.represents q
              exact ⟨j, by simpa [q, active, selector,
                charbonnelActiveEnrichedBoundaryFunction] using hj⟩
            have hlocal :=
              charbonnelOrderedSelectorRegionCarrier_compatible_enriched
                (input i).vertical selector hr hordered hrep region
            simpa [CharbonnelEnrichedSuccessorCell.carrier] using
              compatible_enriched_of_compatible_carrierOn
                (input i).vertical hsubset hregion hlocal
          · right
            simpa [CharbonnelEnrichedSuccessorCell.carrier] using
              disjoint_enriched_of_disjoint_bases
                (input i).vertical hdisjoint hregion }
    refine ⟨
      { cover := cover
        cell_base_eq := ?_ }⟩
    intro region
    cases region <;> rfl
  · have hrzero : ordering.count = 0 := Nat.eq_zero_of_not_pos hr
    let cylinder : CharbonnelEnrichedSuccessorCell S n :=
      ⟨refinement.cell k, .cylinder⟩
    let cover :
        CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
          S (charbonnelCylinderCell (refinement.cell k).carrier)
          (fun i ↦ (input i).carrier) :=
      { Index := Unit
        indexFinite := inferInstance
        cell := fun _ ↦ cylinder
        contained := fun _ ↦ Subset.rfl
        covers := fun z hz ↦ ⟨(), hz⟩
        compatible := by
          intro _ i
          change charbonnelCylinderCell (refinement.cell k).carrier ⊆
                (input i).carrier ∨
            Disjoint (charbonnelCylinderCell (refinement.cell k).carrier)
              (input i).carrier
          rcases refinement.base_compatible k i with hsubset | hdisjoint
          · by_cases hD : (refinement.cell k).carrier.Nonempty
            · have hboundaryZero : (input i).boundaryCount = 0 := by
                by_contra hne
                have hpos : 0 < (input i).boundaryCount :=
                  Nat.pos_of_ne_zero hne
                let b : Fin (input i).boundaryCount := ⟨0, hpos⟩
                let q : J := ⟨⟨i, b⟩, hsubset⟩
                obtain ⟨j, _hj⟩ := ordering.represents q
                exact (hr (Nat.zero_lt_of_lt j.isLt)).elim
              have hcarrier :=
                (input i).vertical.carrier_eq_cylinder_of_boundaryCount_eq_zero
                  hboundaryZero
              left
              intro z hz
              change z ∈ (input i).vertical.carrier
              rw [hcarrier]
              exact hsubset hz
            · right
              rw [Set.disjoint_left]
              intro z hz _hzTarget
              exact hD ⟨realEuclideanTakeLeft z, hz⟩
          · right
            simpa [CharbonnelEnrichedSuccessorCell.carrier] using
              disjoint_enriched_of_disjoint_bases
                (input i).vertical hdisjoint (Subset.rfl :
                  charbonnelCylinderCell (refinement.cell k).carrier ⊆
                    charbonnelCylinderCell (refinement.cell k).carrier) }
    refine ⟨
      { cover := cover
        cell_base_eq := ?_ }⟩
    intro i
    cases i
    rfl

/-! ## Flattening preserves the base partition -/

/-- A retained simultaneous enriched cover whose recorded projected bases are
pairwise equal or disjoint. -/
structure CharbonnelFiniteBasePartitionedEnrichedSimultaneouslyCompatibleRelativeCellCover
    (S : EuclideanSetFamily) {n : ℕ} {I : Type}
    (domain : Set (RealEuclidean (n + 1)))
    (target : I → Set (RealEuclidean (n + 1))) where
  cover : CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
    S domain target
  bases_eq_or_disjoint : ∀ i j,
    (cover.cell i).base.carrier = (cover.cell j).base.carrier ∨
      Disjoint (cover.cell i).base.carrier (cover.cell j).base.carrier

/-- Flattening the local selector covers over a partitioned equality
refinement preserves the recorded-base partition. -/
theorem charbonnelFinitePartitionedEnrichedCellFamilyCommonRefinement_succ_retained
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFinitePartitionedCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {I : Type} [Fintype I]
    (input : I → CharbonnelEnrichedSuccessorCell S n) :
    Nonempty
      (CharbonnelFiniteBasePartitionedEnrichedSimultaneouslyCompatibleRelativeCellCover
        S Set.univ (fun i ↦ (input i).carrier)) := by
  classical
  obtain ⟨partitioned⟩ :=
    exists_charbonnelPartitionedEnrichedEqualityBaseRefinement
      hC hI hII hn input
  let refinement := partitioned.refinement
  let lift : ∀ k,
      CharbonnelFiniteEnrichedLocalSelectorCoverOverBase S
        (refinement.cell k) (fun i ↦ (input i).carrier) :=
    fun k ↦ Classical.choice
      (exists_charbonnelEnrichedLocalSelectorCoverRetained_overBase
        hC hn refinement k)
  let _ : ∀ k, Finite (lift k).cover.Index :=
    fun k ↦ (lift k).cover.indexFinite
  let Index := Σ k, (lift k).cover.Index
  let _ : Fintype Index := Fintype.ofFinite Index
  let cover :
      CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
        S Set.univ (fun i ↦ (input i).carrier) :=
    { Index := Index
      indexFinite := inferInstance
      cell := fun q ↦ (lift q.1).cover.cell q.2
      contained := fun _ _ _ ↦ Set.mem_univ _
      covers := by
        intro z _hz
        obtain ⟨k, hk⟩ := refinement.covers (realEuclideanTakeLeft z)
        have hzCylinder : z ∈
            charbonnelCylinderCell (refinement.cell k).carrier := hk
        obtain ⟨j, hj⟩ := (lift k).cover.covers z hzCylinder
        exact ⟨⟨k, j⟩, hj⟩
      compatible := by
        intro q i
        exact (lift q.1).cover.compatible q.2 i }
  refine ⟨
    { cover := cover
      bases_eq_or_disjoint := ?_ }⟩
  intro q r
  have hq : (cover.cell q).base.carrier =
      (refinement.cell q.1).carrier := (lift q.1).cell_base_eq q.2
  have hr : (cover.cell r).base.carrier =
      (refinement.cell r.1).carrier := (lift r.1).cell_base_eq r.2
  rw [hq, hr]
  exact partitioned.cells_eq_or_disjoint q.1 r.1

namespace CharbonnelFiniteBasePartitionedEnrichedSimultaneouslyCompatibleRelativeCellCover

/-- Select one simultaneous target.  The recorded-base partition turns the
retained selector output into a projection-coherent enriched cover. -/
def targetProjectionCoherentCover
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    {domain : Set (RealEuclidean (n + 1))}
    {target : I → Set (RealEuclidean (n + 1))}
    (partitioned :
      CharbonnelFiniteBasePartitionedEnrichedSimultaneouslyCompatibleRelativeCellCover
        S domain target)
    (j : I) (htarget : target j ⊆ domain) :
    CharbonnelFiniteProjectionCoherentEnrichedCellCover
      S domain (target j) where
  Index := partitioned.cover.Index
  indexFinite := partitioned.cover.indexFinite
  cell := partitioned.cover.cell
  target_subset_domain := htarget
  contained := partitioned.cover.contained
  covers := partitioned.cover.covers
  compatible := fun i ↦ partitioned.cover.compatible i j
  bases_eq_or_disjoint := partitioned.bases_eq_or_disjoint

/-- Global partitioned retained output is projection coherent for every one
of its simultaneous targets. -/
def targetProjectionCoherentCover_univ
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    {target : I → Set (RealEuclidean (n + 1))}
    (partitioned :
      CharbonnelFiniteBasePartitionedEnrichedSimultaneouslyCompatibleRelativeCellCover
        S Set.univ target)
    (j : I) :
    CharbonnelFiniteProjectionCoherentEnrichedCellCover
      S Set.univ (target j) :=
  partitioned.targetProjectionCoherentCover j (Set.subset_univ _)

end CharbonnelFiniteBasePartitionedEnrichedSimultaneouslyCompatibleRelativeCellCover

/-- The partitioned successor common-refinement hypothesis supplies the exact
one-step projection-coherent cover required downstream, for every enriched
input cell chosen as target. -/
theorem exists_charbonnelFiniteProjectionCoherentEnrichedCellCover_succ
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFinitePartitionedCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {I : Type} [Fintype I]
    (input : I → CharbonnelEnrichedSuccessorCell S n) (j : I) :
    Nonempty
      (CharbonnelFiniteProjectionCoherentEnrichedCellCover
        S Set.univ (input j).carrier) := by
  obtain ⟨partitioned⟩ :=
    charbonnelFinitePartitionedEnrichedCellFamilyCommonRefinement_succ_retained
      hC hI hII hn input
  exact ⟨partitioned.targetProjectionCoherentCover_univ j⟩

/-! ## Refining an enriched relative target cover -/

/-- Compatibility with every cell of an enriched relative cover transfers to
its target when that target lies in the covered domain.  This is the enriched
set-theoretic form needed before installing the recorded-base partition. -/
theorem compatible_target_of_compatible_enriched_relative_cover_cells
    {S : EuclideanSetFamily} {n : ℕ}
    {D A s : Set (RealEuclidean (n + 1))}
    (source : CharbonnelFiniteEnrichedCompatibleRelativeCellCover S n D A)
    (hAD : A ⊆ D)
    (hs : ∀ j,
      s ⊆ (source.cell j).carrier ∨
        Disjoint s (source.cell j).carrier) :
    s ⊆ A ∨ Disjoint s A := by
  classical
  by_cases hhit : ∃ x, x ∈ s ∧ x ∈ A
  · obtain ⟨x, hxs, hxA⟩ := hhit
    obtain ⟨j, hxj⟩ := source.covers x (hAD hxA)
    rcases hs j with hsubset | hdisjoint
    · rcases source.compatible j with htarget | htarget
      · exact Or.inl (hsubset.trans htarget)
      · exact False.elim
          (Set.disjoint_left.mp htarget (hsubset hxs) hxA)
    · exact False.elim (Set.disjoint_left.mp hdisjoint hxs hxj)
  · right
    rw [Set.disjoint_left]
    intro x hxs hxA
    exact hhit ⟨x, hxs, hxA⟩

/-- A finite enriched relative cover of `A` can be refined by the partitioned
successor selector construction to a global projection-coherent enriched
cover of `A`.  This is the one-step form consumed by projection towers. -/
theorem
    exists_charbonnelFiniteProjectionCoherentEnrichedCellCover_of_enrichedRelativeCover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFinitePartitionedCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {D A : Set (RealEuclidean (n + 1))}
    (source : CharbonnelFiniteEnrichedCompatibleRelativeCellCover S n D A)
    (hAD : A ⊆ D) :
    Nonempty
      (CharbonnelFiniteProjectionCoherentEnrichedCellCover S Set.univ A) := by
  classical
  let _ : Finite source.Index := source.indexFinite
  let _ : Fintype source.Index := Fintype.ofFinite source.Index
  obtain ⟨partitioned⟩ :=
    charbonnelFinitePartitionedEnrichedCellFamilyCommonRefinement_succ_retained
      hC hI hII hn source.cell
  refine ⟨
    { Index := partitioned.cover.Index
      indexFinite := partitioned.cover.indexFinite
      cell := partitioned.cover.cell
      target_subset_domain := Set.subset_univ A
      contained := partitioned.cover.contained
      covers := partitioned.cover.covers
      compatible := ?_
      bases_eq_or_disjoint := partitioned.bases_eq_or_disjoint }⟩
  intro i
  exact compatible_target_of_compatible_enriched_relative_cover_cells
    source hAD (partitioned.cover.compatible i)

end AbelFormalization
