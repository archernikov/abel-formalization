import AbelFormalization.WilkieSection4DeepSimultaneousInduction

/-!
# The retained successor common-refinement step

This file proves the common-refinement half of Wilkie's simultaneous
Section 4 induction at a successor dimension.  The construction refines the
retained projected bases by every closed boundary-equality locus, orders the
active boundary functions over each resulting deep base cell, and attaches
the corresponding graph, band, and ray cells without forgetting the lower
projection history.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## The ordered-selector regions are a partition -/

/-- Distinct regions cut out by one strictly ordered selector family are
disjoint.  We state equality-or-disjointness because that is the form used by
the retained partition invariant. -/
theorem charbonnelOrderedSelectorRegionCarrier_eq_or_disjoint
    {n r : ℕ} {base : Set (RealEuclidean n)}
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    (p q : CharbonnelOrderedSelectorRegion r) :
    charbonnelOrderedSelectorRegionCarrier base f hr p =
        charbonnelOrderedSelectorRegionCarrier base f hr q ∨
      Disjoint
        (charbonnelOrderedSelectorRegionCarrier base f hr p)
        (charbonnelOrderedSelectorRegionCarrier base f hr q) := by
  classical
  by_cases hpq : p = q
  · exact Or.inl (congrArg _ hpq)
  · right
    rw [Set.disjoint_left]
    intro z hzp hzq
    cases p with
    | lower =>
        cases q with
        | lower => exact hpq rfl
        | graph j =>
            have hidx : charbonnelFirstSelectorIndex hr ≤ j := by
              show (charbonnelFirstSelectorIndex hr).1 ≤ j.1
              simp [charbonnelFirstSelectorIndex]
            have hmono := (hordered _ hzp.1).monotone hidx
            exact (by linarith [hzp.2, hzq.2, hmono])
        | band j =>
            have hidx : charbonnelFirstSelectorIndex hr ≤
                charbonnelBandLeftIndex j := by
              show (charbonnelFirstSelectorIndex hr).1 ≤
                (charbonnelBandLeftIndex j).1
              simp [charbonnelFirstSelectorIndex,
                charbonnelBandLeftIndex]
            have hmono := (hordered _ hzp.1).monotone hidx
            exact (by linarith [hzp.2, hzq.2.1, hmono])
        | upper =>
            have hidx : charbonnelFirstSelectorIndex hr ≤
                charbonnelLastSelectorIndex hr := by
              show (charbonnelFirstSelectorIndex hr).1 ≤
                (charbonnelLastSelectorIndex hr).1
              simp [charbonnelFirstSelectorIndex,
                charbonnelLastSelectorIndex]
            have hmono := (hordered _ hzp.1).monotone hidx
            exact (by linarith [hzp.2, hzq.2, hmono])
    | graph i =>
        cases q with
        | lower =>
            have hidx : charbonnelFirstSelectorIndex hr ≤ i := by
              show (charbonnelFirstSelectorIndex hr).1 ≤ i.1
              simp [charbonnelFirstSelectorIndex]
            have hmono := (hordered _ hzp.1).monotone hidx
            exact (by linarith [hzp.2, hzq.2, hmono])
        | graph j =>
            have hij : i ≠ j := by
              intro hij
              subst j
              exact hpq rfl
            rcases lt_or_gt_of_ne hij with hij | hji
            · have hmono := hordered _ hzp.1 hij
              exact (by linarith [hzp.2, hzq.2, hmono])
            · have hmono := hordered _ hzp.1 hji
              exact (by linarith [hzp.2, hzq.2, hmono])
        | band j =>
            by_cases hij : i ≤ charbonnelBandLeftIndex j
            · have hmono := (hordered _ hzp.1).monotone hij
              exact (by linarith [hzp.2, hzq.2.1, hmono])
            · have hright : charbonnelBandRightIndex j ≤ i := by
                show (charbonnelBandRightIndex j).1 ≤ i.1
                simp [charbonnelBandLeftIndex,
                  charbonnelBandRightIndex] at hij ⊢
                omega
              have hmono := (hordered _ hzp.1).monotone hright
              exact (by linarith [hzp.2, hzq.2.2, hmono])
        | upper =>
            have hidx : i ≤ charbonnelLastSelectorIndex hr := by
              show i.1 ≤ (charbonnelLastSelectorIndex hr).1
              simp [charbonnelLastSelectorIndex]
              omega
            have hmono := (hordered _ hzp.1).monotone hidx
            exact (by linarith [hzp.2, hzq.2, hmono])
    | band i =>
        cases q with
        | lower =>
            have hidx : charbonnelFirstSelectorIndex hr ≤
                charbonnelBandLeftIndex i := by
              show (charbonnelFirstSelectorIndex hr).1 ≤
                (charbonnelBandLeftIndex i).1
              simp [charbonnelFirstSelectorIndex,
                charbonnelBandLeftIndex]
            have hmono := (hordered _ hzp.1).monotone hidx
            exact (by linarith [hzp.2.1, hzq.2, hmono])
        | graph j =>
            by_cases hji : j ≤ charbonnelBandLeftIndex i
            · have hmono := (hordered _ hzp.1).monotone hji
              exact (by linarith [hzp.2.1, hzq.2, hmono])
            · have hright : charbonnelBandRightIndex i ≤ j := by
                show (charbonnelBandRightIndex i).1 ≤ j.1
                simp [charbonnelBandLeftIndex,
                  charbonnelBandRightIndex] at hji ⊢
                omega
              have hmono := (hordered _ hzp.1).monotone hright
              exact (by linarith [hzp.2.2, hzq.2, hmono])
        | band j =>
            have hij : i ≠ j := by
              intro hij
              subst j
              exact hpq rfl
            rcases lt_or_gt_of_ne hij with hij | hji
            · have hidx : charbonnelBandRightIndex i ≤
                  charbonnelBandLeftIndex j := by
                show (charbonnelBandRightIndex i).1 ≤
                  (charbonnelBandLeftIndex j).1
                simp [charbonnelBandLeftIndex,
                  charbonnelBandRightIndex] at hij ⊢
                omega
              have hmono := (hordered _ hzp.1).monotone hidx
              exact (by linarith [hzp.2.2, hzq.2.1, hmono])
            · have hidx : charbonnelBandRightIndex j ≤
                  charbonnelBandLeftIndex i := by
                show (charbonnelBandRightIndex j).1 ≤
                  (charbonnelBandLeftIndex i).1
                simp [charbonnelBandLeftIndex,
                  charbonnelBandRightIndex] at hji ⊢
                omega
              have hmono := (hordered _ hzp.1).monotone hidx
              exact (by linarith [hzp.2.1, hzq.2.2, hmono])
        | upper =>
            have hidx : charbonnelBandRightIndex i ≤
                charbonnelLastSelectorIndex hr := by
              show (charbonnelBandRightIndex i).1 ≤
                (charbonnelLastSelectorIndex hr).1
              simp [charbonnelBandRightIndex,
                charbonnelLastSelectorIndex]
            have hmono := (hordered _ hzp.1).monotone hidx
            exact (by linarith [hzp.2.2, hzq.2, hmono])
    | upper =>
        cases q with
        | lower =>
            have hidx : charbonnelFirstSelectorIndex hr ≤
                charbonnelLastSelectorIndex hr := by
              show (charbonnelFirstSelectorIndex hr).1 ≤
                (charbonnelLastSelectorIndex hr).1
              simp [charbonnelFirstSelectorIndex,
                charbonnelLastSelectorIndex]
            have hmono := (hordered _ hzp.1).monotone hidx
            exact (by linarith [hzp.2, hzq.2, hmono])
        | graph j =>
            have hidx : j ≤ charbonnelLastSelectorIndex hr := by
              show j.1 ≤ (charbonnelLastSelectorIndex hr).1
              simp [charbonnelLastSelectorIndex]
              omega
            have hmono := (hordered _ hzp.1).monotone hidx
            exact (by linarith [hzp.2, hzq.2, hmono])
        | band j =>
            have hidx : charbonnelBandRightIndex j ≤
                charbonnelLastSelectorIndex hr := by
              show (charbonnelBandRightIndex j).1 ≤
                (charbonnelLastSelectorIndex hr).1
              simp [charbonnelBandRightIndex,
                charbonnelLastSelectorIndex]
            have hmono := (hordered _ hzp.1).monotone hidx
            exact (by linarith [hzp.2, hzq.2.2, hmono])
        | upper => exact hpq rfl

/-! ## A local selector partition over one retained deep base -/

/-- The boundary functions whose recorded bases contain a fixed retained
base cell. -/
abbrev CharbonnelActiveBoundaryOverDeepBase
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    (base : CharbonnelDeepEnrichedCell S n)
    (input : I → CharbonnelEnrichedSuccessorCell S n) :=
  {q : CharbonnelEnrichedBoundaryIndex input //
    base.carrier ⊆ (input q.1).base.carrier}

def charbonnelActiveBoundaryOverDeepBaseFunction
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    (base : CharbonnelDeepEnrichedCell S n)
    (input : I → CharbonnelEnrichedSuccessorCell S n)
    (q : CharbonnelActiveBoundaryOverDeepBase base input) :
    RealEuclidean n → ℝ :=
  (input q.1.1).boundary q.1.2

/-- Compatibility with every closed equality locus makes each pair of active
boundary functions either identical or nowhere equal on a retained base. -/
theorem boundary_eqOn_or_neOn_over_deepBase
    {S : EuclideanSetFamily} {n : ℕ} {I : Type}
    (base : CharbonnelDeepEnrichedCell S n)
    (input : I → CharbonnelEnrichedSuccessorCell S n)
    (hequality : ∀ q r : CharbonnelEnrichedBoundaryIndex input,
      base.carrier ⊆ charbonnelEnrichedBoundaryEqualityTarget input q r ∨
        Disjoint base.carrier
          (charbonnelEnrichedBoundaryEqualityTarget input q r))
    (q r : CharbonnelActiveBoundaryOverDeepBase base input) :
    Set.EqOn ((input q.1.1).boundary q.1.2)
        ((input r.1.1).boundary r.1.2) base.carrier ∨
      (∀ x ∈ base.carrier,
        (input q.1.1).boundary q.1.2 x ≠
          (input r.1.1).boundary r.1.2 x) := by
  rcases hequality q.1 r.1 with hsubset | hdisjoint
  · left
    intro x hx
    exact (mem_charbonnelBoundaryEqualityLocus_of_mem_bases_of_mem_closure
      ((input q.1.1).boundary_continuous q.1.2)
      ((input r.1.1).boundary_continuous r.1.2)
      (q.2 hx) (r.2 hx) (hsubset hx)).2.2
  · right
    intro x hx hEq
    exact Set.disjoint_left.mp hdisjoint hx
      (subset_closure ⟨q.2 hx, r.2 hx, hEq⟩)

/-- Equality-locus compatibility orders all active boundary germs over one
retained base. -/
theorem exists_charbonnelBoundaryOrdering_over_deepBase
    {S : EuclideanSetFamily} {n : ℕ} {I : Type} [Fintype I]
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (base : CharbonnelDeepEnrichedCell S n)
    (input : I → CharbonnelEnrichedSuccessorCell S n)
    (hequality : ∀ q r : CharbonnelEnrichedBoundaryIndex input,
      base.carrier ⊆ charbonnelEnrichedBoundaryEqualityTarget input q r ∨
        Disjoint base.carrier
          (charbonnelEnrichedBoundaryEqualityTarget input q r)) :
    Nonempty (CharbonnelBoundaryOrdering base.carrier
      (charbonnelActiveBoundaryOverDeepBaseFunction base input)) := by
  classical
  let J := CharbonnelActiveBoundaryOverDeepBase base input
  letI : Fintype J := Fintype.ofFinite J
  let f : J → RealEuclidean n → ℝ :=
    charbonnelActiveBoundaryOverDeepBaseFunction base input
  by_cases hbase : base.carrier.Nonempty
  · apply exists_charbonnelBoundaryOrdering
      (base.toCell hC).shape.isPreconnected hbase f
    · intro q
      exact ((input q.1.1).boundary_continuous q.1.2).mono q.2
    · intro q r
      exact boundary_eqOn_or_neOn_over_deepBase base input hequality q r
  · let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
    exact ⟨
      { count := Fintype.card J
        origin := e
        strictlyOrdered := by
          intro x hx
          exact (hbase ⟨x, hx⟩).elim
        represents := by
          intro q
          refine ⟨e.symm q, ?_⟩
          intro x hx
          exact (hbase ⟨x, hx⟩).elim }⟩

/-- The local selector construction over one retained base, including the
partition and exact projected-base conclusions needed for flattening. -/
structure CharbonnelFinitePartitionedDeepLocalSelectorCover
    (S : EuclideanSetFamily) {n : ℕ} {I : Type}
    (base : CharbonnelDeepEnrichedCell S n)
    (input : I → CharbonnelEnrichedSuccessorCell S n) where
  Index : Type
  indexFinite : Finite Index
  cell : Index → CharbonnelDeepEnrichedCell S (n + 1)
  contained : ∀ i,
    (cell i).carrier ⊆ charbonnelCylinderCell base.carrier
  covers : ∀ z ∈ charbonnelCylinderCell base.carrier,
    ∃ i, z ∈ (cell i).carrier
  compatible : ∀ i j,
    (cell i).carrier ⊆ (input j).carrier ∨
      Disjoint (cell i).carrier (input j).carrier
  cells_eq_or_disjoint : ∀ i j,
    (cell i).carrier = (cell j).carrier ∨
      Disjoint (cell i).carrier (cell j).carrier
  projectedBase_eq : ∀ i (hn : 0 < n),
    (cell i).projectedBase hn = base

/-- Ordered selectors, attached with `ofVertical`, partition the cylinder over
one retained base and are simultaneously compatible with all enriched input
cells. -/
theorem exists_charbonnelFinitePartitionedDeepLocalSelectorCover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {I : Type} [Fintype I]
    (base : CharbonnelDeepEnrichedCell S n)
    (input : I → CharbonnelEnrichedSuccessorCell S n)
    (hbaseCompatible : ∀ j,
      base.carrier ⊆ (input j).base.carrier ∨
        Disjoint base.carrier (input j).base.carrier)
    (hequality : ∀ q r : CharbonnelEnrichedBoundaryIndex input,
      base.carrier ⊆ charbonnelEnrichedBoundaryEqualityTarget input q r ∨
        Disjoint base.carrier
          (charbonnelEnrichedBoundaryEqualityTarget input q r)) :
    Nonempty
      (CharbonnelFinitePartitionedDeepLocalSelectorCover S base input) := by
  classical
  obtain ⟨ordering⟩ :=
    exists_charbonnelBoundaryOrdering_over_deepBase hC base input hequality
  let J := CharbonnelActiveBoundaryOverDeepBase base input
  let active : J → RealEuclidean n → ℝ :=
    charbonnelActiveBoundaryOverDeepBaseFunction base input
  let selector : Fin ordering.count → RealEuclidean n → ℝ :=
    fun i ↦ active (ordering.origin i)
  have hcontinuous : ∀ i, ContinuousOn (selector i) base.carrier := by
    intro i
    exact ((input (ordering.origin i).1.1).boundary_continuous
      (ordering.origin i).1.2).mono (ordering.origin i).2
  have hordered : ∀ x ∈ base.carrier,
      StrictMono (fun i ↦ selector i x) := by
    simpa [selector, active] using ordering.strictlyOrdered
  have hgraph : ∀ i,
      charbonnelRestrictedGraph base.carrier (selector i) ∈
        charbonnelClosure S (n + 1) := by
    intro i
    apply charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
      hC hn (ordering.origin i).2 (base.toCell hC).carrier_mem
    exact (input (ordering.origin i).1.1).boundary_graph_mem
      (ordering.origin i).1.2
  by_cases hr : 0 < ordering.count
  · let cell : CharbonnelOrderedSelectorRegion ordering.count →
        CharbonnelDeepEnrichedCell S (n + 1)
      | .lower => base.ofVertical hC hn
          (.lowerRay (selector (charbonnelFirstSelectorIndex hr))
            (hcontinuous _) (hgraph _))
      | .graph i => base.ofVertical hC hn
          (.graph (selector i) (hcontinuous i) (hgraph i))
      | .band i => base.ofVertical hC hn
          (.band
            (selector (charbonnelBandLeftIndex i))
            (selector (charbonnelBandRightIndex i))
            (hcontinuous _) (hcontinuous _)
            (fun x hx ↦ hordered x hx
              (charbonnelBandLeftIndex_lt_rightIndex i))
            (hgraph _) (hgraph _))
      | .upper => base.ofVertical hC hn
          (.upperRay (selector (charbonnelLastSelectorIndex hr))
            (hcontinuous _) (hgraph _))
    have hcellCarrier : ∀ region,
        (cell region).carrier =
          charbonnelOrderedSelectorRegionCarrier
            base.carrier selector hr region := by
      intro region
      cases region <;> rfl
    refine ⟨
      { Index := CharbonnelOrderedSelectorRegion ordering.count
        indexFinite := inferInstance
        cell := cell
        contained := ?_
        covers := ?_
        compatible := ?_
        cells_eq_or_disjoint := ?_
        projectedBase_eq := ?_ }⟩
    · intro region z hz
      rw [hcellCarrier region] at hz
      exact charbonnelOrderedSelectorRegionCarrier_subset_cylinder
        base.carrier selector hr region hz
    · intro z hz
      obtain ⟨region, hregion⟩ :=
        exists_charbonnelOrderedSelectorRegion_contains hr
          (fun i ↦ selector i (realEuclideanTakeLeft z))
          (realEuclideanTakeRight z 0)
      refine ⟨region, ?_⟩
      rw [hcellCarrier region]
      cases region <;> exact ⟨hz, hregion⟩
    · intro region i
      rw [hcellCarrier region]
      have hregion :
          charbonnelOrderedSelectorRegionCarrier
              base.carrier selector hr region ⊆
            charbonnelCylinderCell base.carrier :=
        charbonnelOrderedSelectorRegionCarrier_subset_cylinder
          base.carrier selector hr region
      rcases hbaseCompatible i with hsubset | hdisjoint
      · have hrep : ∀ b : Fin (input i).boundaryCount,
            ∃ j, Set.EqOn ((input i).boundary b) (selector j)
              base.carrier := by
          intro b
          let q : J := ⟨⟨i, b⟩, hsubset⟩
          obtain ⟨j, hj⟩ := ordering.represents q
          exact ⟨j, by simpa [q, active, selector,
            charbonnelActiveBoundaryOverDeepBaseFunction] using hj⟩
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
    · intro p q
      rcases charbonnelOrderedSelectorRegionCarrier_eq_or_disjoint
          selector hr hordered p q with heq | hdisjoint
      · left
        exact (hcellCarrier p).trans (heq.trans (hcellCarrier q).symm)
      · right
        simpa only [hcellCarrier p, hcellCarrier q] using hdisjoint
    · intro region hn'
      have hproof : hn' = hn := Subsingleton.elim _ _
      subst hn'
      cases region <;> simp [cell]
  · have hrzero : ordering.count = 0 := Nat.eq_zero_of_not_pos hr
    let vertical : CharbonnelEnrichedVerticalCell S (base.toCell hC) :=
      .cylinder
    let cell : CharbonnelDeepEnrichedCell S (n + 1) :=
      base.ofVertical hC hn vertical
    have hcell : cell.carrier = charbonnelCylinderCell base.carrier := by
      rfl
    refine ⟨
      { Index := Unit
        indexFinite := inferInstance
        cell := fun _ ↦ cell
        contained := fun _ ↦ hcell.le
        covers := fun z hz ↦ ⟨(), hcell.symm ▸ hz⟩
        compatible := ?_
        cells_eq_or_disjoint := fun _ _ ↦ Or.inl rfl
        projectedBase_eq := fun _ hn' ↦ by
          exact CharbonnelDeepEnrichedCell.ofVertical_projectedBase
            hC hn base vertical }⟩
    intro _ i
    change cell.carrier ⊆ (input i).carrier ∨
      Disjoint cell.carrier (input i).carrier
    rw [hcell]
    rcases hbaseCompatible i with hsubset | hdisjoint
    · by_cases hbaseNonempty : base.carrier.Nonempty
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
        intro z hz _hzInput
        exact hbaseNonempty ⟨realEuclideanTakeLeft z, hz⟩
    · right
      simpa [CharbonnelEnrichedSuccessorCell.carrier] using
        disjoint_enriched_of_disjoint_bases
          (input i).vertical hdisjoint (Subset.rfl :
            charbonnelCylinderCell base.carrier ⊆
              charbonnelCylinderCell base.carrier)

/-! ## Relative equality refinement and flattening -/

/-- Compatibility with every cell of a relative deep cover transfers to its
selected target for sets already contained in the covered domain. -/
theorem compatible_target_of_compatible_deep_relative_cover_cells
    {S : EuclideanSetFamily} {n : ℕ}
    {D A s : Set (RealEuclidean (n + 1))}
    (cover :
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D (fun _ : Unit ↦ A))
    (hsD : s ⊆ D)
    (hs : ∀ k,
      s ⊆ (cover.cell k).carrier ∨
        Disjoint s (cover.cell k).carrier) :
    s ⊆ A ∨ Disjoint s A := by
  by_cases hsNonempty : s.Nonempty
  · obtain ⟨x, hxs⟩ := hsNonempty
    obtain ⟨k, hxk⟩ := cover.covers x (hsD hxs)
    rcases hs k with hsubset | hdisjoint
    · rcases cover.compatible k () with htarget | htarget
      · exact Or.inl (hsubset.trans htarget)
      · exact Or.inr (htarget.mono hsubset Subset.rfl)
    · exact (Set.disjoint_left.mp hdisjoint hxs hxk).elim
  · left
    intro x hx
    exact (hsNonempty ⟨x, hx⟩).elim

/-- Hereditary projection coherence is preserved by arbitrary reindexing. -/
private theorem deepCellFamilyProjectionCoherent_comp
    {S : EuclideanSetFamily} {I K : Type} :
    ∀ {n : ℕ} {cell : I → CharbonnelDeepEnrichedCell S (n + 1)},
      CharbonnelDeepCellFamilyProjectionCoherent n cell →
      (f : K → I) →
      CharbonnelDeepCellFamilyProjectionCoherent n (fun k ↦ cell (f k))
  | 0, _cell, _hcoherent, _f => trivial
  | n + 1, cell, hcoherent, f => by
      refine ⟨?_, ?_⟩
      · intro i j
        exact hcoherent.1 (f i) (f j)
      · exact deepCellFamilyProjectionCoherent_comp hcoherent.2 f

/-- The bounded common-refinement half of Wilkie's retained simultaneous
induction passes from dimension `n + 1` to dimension `n + 2`. -/
theorem charbonnelBoundedDeepRelativeCommonRefinementAt_succ
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ}
    (hI : CharbonnelBoundedDeepRelativeClosedDecompositionAt S n)
    (hII : CharbonnelBoundedDeepRelativeCommonRefinementAt S n) :
    CharbonnelBoundedDeepRelativeCommonRefinementAt S (n + 1) := by
  classical
  intro D hDbounded J _ target
  let hn : 0 < n + 1 := by omega
  let topDeep : Option J → CharbonnelDeepEnrichedCell S ((n + 1) + 1)
    | none => D
    | some j => target j
  let input : Option J → CharbonnelEnrichedSuccessorCell S (n + 1) :=
    fun i ↦ (topDeep i).toEnrichedSuccessorCell hC hn
  let base : CharbonnelDeepEnrichedCell S (n + 1) :=
    D.projectedBase hn
  have hbaseBounded : Bornology.IsBounded base.carrier := by
    exact D.projectedBase_isBounded hC hn hDbounded
  let Boundary := CharbonnelEnrichedBoundaryIndex input
  let equalityTarget (qr : Boundary × Boundary) :
      Set (RealEuclidean (n + 1)) :=
    base.carrier ∩
      charbonnelEnrichedBoundaryEqualityTarget input qr.1 qr.2
  have hequalityMem : ∀ qr,
      equalityTarget qr ∈ charbonnelClosure S (n + 1) := by
    intro qr
    apply hC.ws1_inter (by omega)
    · simpa [base] using (base.toCell hC).carrier_mem
    · exact closure_charbonnelBoundaryEqualityLocus_mem_charbonnelClosure
        hC hn ((input qr.1.1).boundary_graph_mem qr.1.2)
          ((input qr.2.1).boundary_graph_mem qr.2.2)
  have hequalityClosed : ∀ qr,
      IsClosed (Subtype.val ⁻¹' equalityTarget qr : Set base.carrier) := by
    intro qr
    have hclosed : IsClosed
        (Subtype.val ⁻¹'
          charbonnelEnrichedBoundaryEqualityTarget input qr.1 qr.2 :
            Set base.carrier) :=
      isClosed_closure.preimage continuous_subtype_val
    simpa [equalityTarget] using hclosed
  have hequalityCover : ∀ qr,
      Nonempty
        (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
          S base.carrier (fun _ : Unit ↦ equalityTarget qr)) := by
    intro qr
    exact hI base hbaseBounded inter_subset_left
      (hequalityMem qr) (hequalityClosed qr)
  let equalityCover : (qr : Boundary × Boundary) →
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S base.carrier (fun _ : Unit ↦ equalityTarget qr) :=
    fun qr ↦ Classical.choice (hequalityCover qr)
  letI : ∀ qr, Finite (equalityCover qr).Index :=
    fun qr ↦ (equalityCover qr).indexFinite
  letI : ∀ qr, Fintype (equalityCover qr).Index :=
    fun qr ↦ Fintype.ofFinite (equalityCover qr).Index
  let BaseTarget := (Option J) ⊕
    (Σ qr : Boundary × Boundary, (equalityCover qr).Index)
  let baseTarget : BaseTarget → CharbonnelDeepEnrichedCell S (n + 1)
    | .inl i => (topDeep i).projectedBase hn
    | .inr q => (equalityCover q.1).cell q.2
  obtain ⟨fine⟩ := hII base hbaseBounded baseTarget
  have hbaseCompatible : ∀ k i,
      (fine.cell k).carrier ⊆ (input i).base.carrier ∨
        Disjoint (fine.cell k).carrier (input i).base.carrier := by
    intro k i
    have hcompat := fine.compatible k (Sum.inl i)
    simpa only [baseTarget, input,
      CharbonnelDeepEnrichedCell.toEnrichedSuccessorCell_base_carrier] using
      hcompat
  have hequalityCompatible : ∀ k q r,
      (fine.cell k).carrier ⊆
          charbonnelEnrichedBoundaryEqualityTarget input q r ∨
        Disjoint (fine.cell k).carrier
          (charbonnelEnrichedBoundaryEqualityTarget input q r) := by
    intro k q r
    let qr : Boundary × Boundary := (q, r)
    have hintersection :
        (fine.cell k).carrier ⊆ equalityTarget qr ∨
          Disjoint (fine.cell k).carrier (equalityTarget qr) := by
      apply compatible_target_of_compatible_deep_relative_cover_cells
        (cover := equalityCover qr) (fine.contained k)
      intro l
      have hcompat := fine.compatible k (Sum.inr ⟨qr, l⟩)
      simpa only [baseTarget] using hcompat
    rcases hintersection with hsubset | hdisjoint
    · left
      exact hsubset.trans inter_subset_right
    · right
      rw [Set.disjoint_left]
      intro x hx hxeq
      exact Set.disjoint_left.mp hdisjoint hx ⟨fine.contained k hx, hxeq⟩
  let carrierSetoid : Setoid fine.Index :=
    Setoid.ker (fun k ↦ (fine.cell k).carrier)
  let BaseIndex := Quotient carrierSetoid
  let representative : BaseIndex → fine.Index := Quotient.out
  let baseCell : BaseIndex → CharbonnelDeepEnrichedCell S (n + 1) :=
    fun q ↦ fine.cell (representative q)
  letI : Finite fine.Index := fine.indexFinite
  letI : Finite BaseIndex := Quotient.finite carrierSetoid
  have hlocal : ∀ q,
      Nonempty
        (CharbonnelFinitePartitionedDeepLocalSelectorCover
          S (baseCell q) input) := by
    intro q
    apply exists_charbonnelFinitePartitionedDeepLocalSelectorCover
      hC hn (baseCell q) input
    · exact hbaseCompatible (representative q)
    · exact hequalityCompatible (representative q)
  let selectorCover : (q : BaseIndex) →
      CharbonnelFinitePartitionedDeepLocalSelectorCover
        S (baseCell q) input :=
    fun q ↦ Classical.choice (hlocal q)
  letI : ∀ q, Finite (selectorCover q).Index :=
    fun q ↦ (selectorCover q).indexFinite
  let Index := Σ q : BaseIndex,
    {i : (selectorCover q).Index // ((selectorCover q).cell i).carrier ⊆ D.carrier}
  let cell : Index → CharbonnelDeepEnrichedCell S ((n + 1) + 1) :=
    fun p ↦ (selectorCover p.1).cell p.2.1
  have hrepresentativeCarrier : ∀ (i : fine.Index),
      (baseCell (Quotient.mk carrierSetoid i)).carrier =
        (fine.cell i).carrier := by
    intro i
    have hq : Quotient.mk carrierSetoid
          (representative (Quotient.mk carrierSetoid i)) =
        Quotient.mk carrierSetoid i :=
      Quotient.out_eq (Quotient.mk carrierSetoid i)
    exact Quotient.exact hq
  have hinputNone : (input none).carrier = D.carrier := by
    simp [input, topDeep]
  have hinputSome : ∀ j, (input (some j)).carrier = (target j).carrier := by
    intro j
    simp [input, topDeep]
  refine ⟨
    { Index := Index
      indexFinite := inferInstance
      cell := cell
      contained := fun p ↦ p.2.2
      covers := ?_
      compatible := ?_
      cells_eq_or_disjoint := ?_
      hereditary_projection_coherent := ?_ }⟩
  · intro z hzD
    have hxBase : realEuclideanTakeLeft z ∈ base.carrier := by
      rw [← D.existentialProjection_carrier hC hn]
      exact ⟨realEuclideanTakeRight z, by
        rwa [realEuclideanAppend_take]⟩
    obtain ⟨i, hxi⟩ := fine.covers _ hxBase
    let q : BaseIndex := Quotient.mk carrierSetoid i
    have hxq : realEuclideanTakeLeft z ∈ (baseCell q).carrier := by
      rw [hrepresentativeCarrier i]
      exact hxi
    obtain ⟨l, hzl⟩ := (selectorCover q).covers z hxq
    have hlD : ((selectorCover q).cell l).carrier ⊆ D.carrier := by
      have hcompat := (selectorCover q).compatible l none
      rw [hinputNone] at hcompat
      rcases hcompat with hsub | hdisjoint
      · exact hsub
      · exact False.elim (Set.disjoint_left.mp hdisjoint hzl hzD)
    exact ⟨⟨q, ⟨l, hlD⟩⟩, hzl⟩
  · intro p j
    have hcompat := (selectorCover p.1).compatible p.2.1 (some j)
    rwa [hinputSome j] at hcompat
  · rintro ⟨q, i⟩ ⟨r, j⟩
    change ((selectorCover q).cell i.1).carrier =
          ((selectorCover r).cell j.1).carrier ∨
        Disjoint ((selectorCover q).cell i.1).carrier
          ((selectorCover r).cell j.1).carrier
    by_cases hqr : q = r
    · subst r
      exact (selectorCover q).cells_eq_or_disjoint i.1 j.1
    · have hbaseDisjoint :
          Disjoint (baseCell q).carrier (baseCell r).carrier := by
        rcases fine.cells_eq_or_disjoint
            (representative q) (representative r) with heq | hdisjoint
        · have hquot : q = r := by
            calc
              q = Quotient.mk carrierSetoid (representative q) :=
                (Quotient.out_eq q).symm
              _ = Quotient.mk carrierSetoid (representative r) :=
                Quotient.sound heq
              _ = r := Quotient.out_eq r
          exact False.elim (hqr hquot)
        · exact hdisjoint
      right
      rw [Set.disjoint_left]
      intro z hzp hzr
      exact Set.disjoint_left.mp hbaseDisjoint
        ((selectorCover q).contained i.1 hzp)
        ((selectorCover r).contained j.1 hzr)
  · change
      (∀ p r,
        ((cell p).projectedBase (by omega : 0 < n + 1)).carrier =
            ((cell r).projectedBase (by omega : 0 < n + 1)).carrier ∨
          Disjoint
            ((cell p).projectedBase (by omega : 0 < n + 1)).carrier
            ((cell r).projectedBase (by omega : 0 < n + 1)).carrier) ∧
      CharbonnelDeepCellFamilyProjectionCoherent n
        (fun p ↦ (cell p).projectedBase (by omega : 0 < n + 1))
    constructor
    · intro p r
      simpa only [cell, (selectorCover p.1).projectedBase_eq p.2.1,
        (selectorCover r.1).projectedBase_eq r.2.1] using
        fine.cells_eq_or_disjoint
          (representative p.1) (representative r.1)
    · have hcoherent := deepCellFamilyProjectionCoherent_comp
          fine.hereditary_projection_coherent
          (fun p : Index ↦ representative p.1)
      simpa only [cell, (selectorCover _).projectedBase_eq] using hcoherent

end AbelFormalization
