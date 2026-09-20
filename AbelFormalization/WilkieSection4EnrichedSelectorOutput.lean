import AbelFormalization.WilkieSection4EnrichedCells

/-!
# Retaining enrichment in the Section 4 selector output

The ordered-selector construction already proves membership of every
restricted selector graph.  Its former output type nevertheless forgot those
certificates immediately.  This file packages the very same graph, band, ray,
and cylinder regions as enriched successor cells and proves the local and
global simultaneous-cover statements without losing their projected bases or
boundary graphs.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The selector region over a recorded base, with all boundary graph
certificates retained. -/
def charbonnelOrderedSelectorEnrichedCell
    {S : EuclideanSetFamily} {n r : ℕ}
    (base : CharbonnelCell (charbonnelClosure S) n)
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hcontinuous : ∀ i, ContinuousOn (f i) base.carrier)
    (hordered : ∀ x ∈ base.carrier, StrictMono (fun i ↦ f i x))
    (hgraph : ∀ i, charbonnelRestrictedGraph base.carrier (f i) ∈
      charbonnelClosure S (n + 1)) :
    CharbonnelOrderedSelectorRegion r → CharbonnelEnrichedSuccessorCell S n
  | .lower =>
      ⟨base, .lowerRay (f (charbonnelFirstSelectorIndex hr))
        (hcontinuous _) (hgraph _)⟩
  | .graph i => ⟨base, .graph (f i) (hcontinuous i) (hgraph i)⟩
  | .band i =>
      ⟨base, .band
        (f (charbonnelBandLeftIndex i))
        (f (charbonnelBandRightIndex i))
        (hcontinuous _) (hcontinuous _)
        (fun x hx ↦ hordered x hx
          (charbonnelBandLeftIndex_lt_rightIndex i))
        (hgraph _) (hgraph _)⟩
  | .upper =>
      ⟨base, .upperRay (f (charbonnelLastSelectorIndex hr))
        (hcontinuous _) (hgraph _)⟩

@[simp]
theorem charbonnelOrderedSelectorEnrichedCell_carrier
    {S : EuclideanSetFamily} {n r : ℕ}
    (base : CharbonnelCell (charbonnelClosure S) n)
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hcontinuous : ∀ i, ContinuousOn (f i) base.carrier)
    (hordered : ∀ x ∈ base.carrier, StrictMono (fun i ↦ f i x))
    (hgraph : ∀ i, charbonnelRestrictedGraph base.carrier (f i) ∈
      charbonnelClosure S (n + 1))
    (region : CharbonnelOrderedSelectorRegion r) :
    (charbonnelOrderedSelectorEnrichedCell base f hr hcontinuous hordered
      hgraph region).carrier =
      charbonnelOrderedSelectorRegionCarrier base.carrier f hr region := by
  cases region <;> rfl

/-- A relative simultaneous cover whose cells retain their enriched
successor data. -/
structure CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
    (S : EuclideanSetFamily) {n : ℕ} {I : Type}
    (domain : Set (RealEuclidean (n + 1)))
    (target : I → Set (RealEuclidean (n + 1))) where
  Index : Type
  indexFinite : Finite Index
  cell : Index → CharbonnelEnrichedSuccessorCell S n
  contained : ∀ i, (cell i).carrier ⊆ domain
  covers : ∀ z ∈ domain, ∃ i, z ∈ (cell i).carrier
  compatible : ∀ i j,
    (cell i).carrier ⊆ target j ∨ Disjoint (cell i).carrier (target j)

/-- Forgetting enrichment gives the earlier relative simultaneous cover. -/
def CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover.toOrdinary
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {I : Type}
    {domain : Set (RealEuclidean (n + 1))}
    {target : I → Set (RealEuclidean (n + 1))}
    (cover : CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
      S domain target) :
    CharbonnelFiniteSimultaneouslyCompatibleRelativeCellCover
      (charbonnelClosure S) domain target where
  Index := cover.Index
  indexFinite := cover.indexFinite
  cell i := (cover.cell i).toCell hC hn
  contained := by
    intro i
    simpa using cover.contained i
  covers := by
    intro z hz
    obtain ⟨i, hi⟩ := cover.covers z hz
    exact ⟨i, by simpa using hi⟩
  compatible := by
    intro i j
    simpa using cover.compatible i j

/-- Over one equality-compatible refined base cell, the selector cover can be
constructed without discarding any enrichment. -/
theorem exists_charbonnelEnrichedLocalSelectorCoverRetained
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {I : Type} [Fintype I]
    {input : I → CharbonnelEnrichedSuccessorCell S n}
    (refinement : CharbonnelEnrichedEqualityBaseRefinement input)
    (k : Fin refinement.count) :
    Nonempty
      (CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
        S (charbonnelCylinderCell (refinement.cell k).carrier)
        (fun i ↦ (input i).carrier)) := by
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
    refine ⟨
      { Index := CharbonnelOrderedSelectorRegion ordering.count
        indexFinite := inferInstance
        cell := cell
        contained := ?_
        covers := ?_
        compatible := ?_ }⟩
    · intro region z hz
      have hcarrier : (cell region).carrier =
          charbonnelOrderedSelectorRegionCarrier
            (refinement.cell k).carrier selector hr region := by
        simp [cell]
      rw [hcarrier] at hz
      exact charbonnelOrderedSelectorRegionCarrier_subset_cylinder
        (refinement.cell k).carrier selector hr region hz
    · intro z hz
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
    · intro region i
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
            (input i).vertical hdisjoint hregion
  · have hrzero : ordering.count = 0 := Nat.eq_zero_of_not_pos hr
    let cylinder : CharbonnelEnrichedSuccessorCell S n :=
      ⟨refinement.cell k, .cylinder⟩
    refine ⟨
      { Index := Unit
        indexFinite := inferInstance
        cell := fun _ ↦ cylinder
        contained := fun _ ↦ Subset.rfl
        covers := fun z hz ↦ ⟨(), hz⟩
        compatible := ?_ }⟩
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
              charbonnelCylinderCell (refinement.cell k).carrier)

/-- The successor common-refinement construction itself can return enriched
cells.  Thus enrichment is preserved when the input family was enriched. -/
theorem charbonnelFiniteEnrichedCellFamilyCommonRefinement_succ_retained
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFiniteCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {I : Type} [Fintype I]
    (input : I → CharbonnelEnrichedSuccessorCell S n) :
    Nonempty
      (CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
        S Set.univ (fun i ↦ (input i).carrier)) := by
  classical
  obtain ⟨refinement⟩ :=
    exists_charbonnelEnrichedEqualityBaseRefinement hC hI hII hn input
  let lift : ∀ k,
      CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
        S (charbonnelCylinderCell (refinement.cell k).carrier)
        (fun i ↦ (input i).carrier) :=
    fun k ↦ Classical.choice
      (exists_charbonnelEnrichedLocalSelectorCoverRetained hC hn refinement k)
  letI : ∀ k, Finite (lift k).Index := fun k ↦ (lift k).indexFinite
  let Index := Σ k, (lift k).Index
  letI : Fintype Index := Fintype.ofFinite Index
  refine ⟨
    { Index := Index
      indexFinite := inferInstance
      cell := fun q ↦ (lift q.1).cell q.2
      contained := fun _ _ _ ↦ Set.mem_univ _
      covers := ?_
      compatible := ?_ }⟩
  · intro z _hz
    obtain ⟨k, hk⟩ := refinement.covers (realEuclideanTakeLeft z)
    have hzCylinder : z ∈
        charbonnelCylinderCell (refinement.cell k).carrier := hk
    obtain ⟨j, hj⟩ := (lift k).covers z hzCylinder
    exact ⟨⟨k, j⟩, hj⟩
  · intro q i
    exact (lift q.1).compatible q.2 i

end AbelFormalization
