import AbelFormalization.WilkieSection4DeepOpenBandBranch
import AbelFormalization.WilkieSection4DeepBoundaryReduction
import AbelFormalization.WilkieSection4DeepNonOpenTransport
import AbelFormalization.WilkieSection4DeepGraphLift
import AbelFormalization.WilkieSection4GraphInduction

/-!
# Source-faithful bounded successor assembly for Wilkie Section 4

The bounded successor step separates the only full-dimensional top shape,
an open band, from cells carrying a graph at some lower projection depth.
Bounded top-level rays and cylinders have empty carrier.  The open-band case
uses the genuine cardinality-cutoff argument, while the buried-graph case is
transported through deletion and reinsertion of its first graph coordinate.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A constant family of deep cells is projection coherent at every depth. -/
theorem charbonnelDeepCellFamilyProjectionCoherent_const
    {S : EuclideanSetFamily} {I : Type} :
    ∀ {n : ℕ} (cell : CharbonnelDeepEnrichedCell S (n + 1)),
      CharbonnelDeepCellFamilyProjectionCoherent n (fun _ : I ↦ cell)
  | 0, _cell => trivial
  | n + 1, cell => by
      constructor
      · intro _ _
        exact Or.inl rfl
      · exact charbonnelDeepCellFamilyProjectionCoherent_const
          (cell.projectedBase (by omega))

/-- Hereditary projection coherence is preserved under reindexing. -/
theorem charbonnelDeepCellFamilyProjectionCoherent_reindex
    {S : EuclideanSetFamily} {I K : Type} :
    ∀ {n : ℕ} {cell : I → CharbonnelDeepEnrichedCell S (n + 1)},
      CharbonnelDeepCellFamilyProjectionCoherent n cell →
      (e : K → I) →
      CharbonnelDeepCellFamilyProjectionCoherent n (fun k ↦ cell (e k))
  | 0, _cell, _hcoherent, _e => trivial
  | n + 1, cell, hcoherent, e => by
      constructor
      · intro i j
        exact hcoherent.1 (e i) (e j)
      · exact charbonnelDeepCellFamilyProjectionCoherent_reindex
          hcoherent.2 e

/-- An empty deep domain has its tautological one-cell relative partition. -/
theorem exists_charbonnelFinitePartitionedDeepRelativeCover_of_empty
    {S : EuclideanSetFamily} {n : ℕ}
    (D : CharbonnelDeepEnrichedCell S (n + 1))
    (hD : D.carrier = ∅)
    (A : Set (RealEuclidean (n + 1))) :
    Nonempty
      (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D.carrier (fun _ : Unit ↦ A)) := by
  refine ⟨
    { Index := Unit
      indexFinite := inferInstance
      cell := fun _ ↦ D
      contained := fun _ ↦ Subset.rfl
      covers := fun z hz ↦ ⟨(), hz⟩
      compatible := ?_
      cells_eq_or_disjoint := fun _ _ ↦ Or.inl rfl
      hereditary_projection_coherent :=
        charbonnelDeepCellFamilyProjectionCoherent_const D }⟩
  intro _ _
  left
  rw [hD]
  exact Set.empty_subset A

/-- Openness of a positive-dimensional deep cell descends to its retained
projected base, since coordinate projection is an open linear map. -/
theorem isOpen_charbonnelDeepEnrichedCell_projectedBase
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + 1))
    (hopen : IsOpen cell.carrier) :
    IsOpen (cell.projectedBase hn).carrier := by
  have hsurjective : Function.Surjective
      (realEuclideanTakeLeftLinearMap n 1) := by
    intro x
    refine ⟨realEuclideanAppend x 0, ?_⟩
    exact realEuclideanTakeLeft_append x 0
  have hopenMap : IsOpenMap (realEuclideanTakeLeftLinearMap n 1) :=
    LinearMap.isOpenMap_of_finiteDimensional _ hsurjective
  have hprojection :
      (realEuclideanTakeLeftLinearMap n 1) '' cell.carrier =
        realEuclideanExistentialProjection cell.carrier := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨realEuclideanTakeRight z, by
        simpa only [realEuclideanTakeLeftLinearMap_apply,
          realEuclideanAppend_takeLeft_takeRight] using hz⟩
    · rintro ⟨y, hxy⟩
      exact ⟨realEuclideanAppend x y, hxy,
        realEuclideanTakeLeft_append x y⟩
  rw [← cell.existentialProjection_carrier hC hn, ← hprojection]
  exact hopenMap cell.carrier hopen

/-! ## Normalizing the top projected bases of a raw partition -/

namespace CharbonnelFinitePartitionedDeepRelativeCellPrecover

/-- Compatibility with the trace of a target on the domain is equivalent to
compatibility with the target itself for cells contained in that domain. -/
def retargetInterDomain
    {S : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean (n + 1))}
    (source :
      CharbonnelFinitePartitionedDeepRelativeCellPrecover S D (A ∩ D)) :
    CharbonnelFinitePartitionedDeepRelativeCellPrecover S D A :=
  { Index := source.Index
    indexFinite := source.indexFinite
    cell := source.cell
    contained := source.contained
    covers := source.covers
    compatible := by
      intro i
      rcases source.compatible i with hinside | hdisjoint
      · exact Or.inl (hinside.trans inter_subset_left)
      · right
        rw [Set.disjoint_left]
        intro z hzCell hzA
        exact Set.disjoint_left.mp hdisjoint hzCell
          ⟨hzA, source.contained i hzCell⟩
    cells_eq_or_disjoint := source.cells_eq_or_disjoint }

end CharbonnelFinitePartitionedDeepRelativeCellPrecover

/-- Relative closedness restricts from a domain to any smaller domain after
the target is replaced by its trace. -/
theorem isClosed_preimage_val_inter_of_subset
    {X : Type*} [TopologicalSpace X] {A D E : Set X}
    (hED : E ⊆ D)
    (hclosed : IsClosed (Subtype.val ⁻¹' A : Set D)) :
    IsClosed (Subtype.val ⁻¹' (A ∩ E) : Set E) := by
  rw [isClosed_preimage_val]
  intro z hz
  refine ⟨?_, hz.1⟩
  apply (isClosed_preimage_val.mp hclosed)
  refine ⟨hED hz.1, ?_⟩
  exact closure_mono (by
    intro w hw
    exact ⟨hED hw.1, hw.2.1⟩) hz.2

namespace CharbonnelDeepEnrichedCell

/-- Restrict only the top vertical constructor of a deep cell to a retained
deep subbase. -/
def restrictTopToDeepBase
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + 1))
    (small : CharbonnelDeepEnrichedCell S n)
    (hsmall : small.carrier ⊆ (cell.projectedBase hn).carrier) :
    CharbonnelDeepEnrichedCell S (n + 1) := by
  rcases cell with ⟨carrier, shape⟩
  cases shape with
  | unary piece => omega
  | graph _ baseShape f hf hgraph =>
      exact small.ofVertical hC hn
        (.graph f (hf.mono hsmall)
          (charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
            hC hn hsmall (small.toCell hC).carrier_mem hgraph))
  | band _ baseShape f g hf hg hfg hfgraph hggraph =>
      exact small.ofVertical hC hn
        (.band f g (hf.mono hsmall) (hg.mono hsmall)
          (fun x hx ↦ hfg x (hsmall hx))
          (charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
            hC hn hsmall (small.toCell hC).carrier_mem hfgraph)
          (charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
            hC hn hsmall (small.toCell hC).carrier_mem hggraph))
  | lowerRay _ baseShape g hg hgraph =>
      exact small.ofVertical hC hn
        (.lowerRay g (hg.mono hsmall)
          (charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
            hC hn hsmall (small.toCell hC).carrier_mem hgraph))
  | upperRay _ baseShape f hf hgraph =>
      exact small.ofVertical hC hn
        (.upperRay f (hf.mono hsmall)
          (charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
            hC hn hsmall (small.toCell hC).carrier_mem hgraph))
  | cylinder _ baseShape =>
      exact small.ofVertical hC hn .cylinder

@[simp]
theorem restrictTopToDeepBase_projectedBase
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + 1))
    (small : CharbonnelDeepEnrichedCell S n)
    (hsmall : small.carrier ⊆ (cell.projectedBase hn).carrier) :
    (cell.restrictTopToDeepBase hC hn small hsmall).projectedBase hn = small := by
  rcases cell with ⟨carrier, shape⟩
  cases shape with
  | unary piece => omega
  | graph => rfl
  | band => rfl
  | lowerRay => rfl
  | upperRay => rfl
  | cylinder => rfl

/-- Restriction to a deep subbase is intersection with its cylinder. -/
theorem restrictTopToDeepBase_carrier_eq_inter
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + 1))
    (small : CharbonnelDeepEnrichedCell S n)
    (hsmall : small.carrier ⊆ (cell.projectedBase hn).carrier) :
    (cell.restrictTopToDeepBase hC hn small hsmall).carrier =
      cell.carrier ∩ charbonnelCylinderCell small.carrier := by
  rcases cell with ⟨carrier, shape⟩
  cases shape with
  | unary piece => omega
  | @graph _ base hm baseShape f hf hgraph =>
      have hproof : hm = hn := Subsingleton.elim _ _
      subst hm
      have hsmall' : small.carrier ⊆ base := by
        exact hsmall
      change charbonnelRestrictedGraph small.carrier f =
        charbonnelRestrictedGraph base f ∩
          charbonnelCylinderCell small.carrier
      ext z
      simp only [charbonnelRestrictedGraph, charbonnelCylinderCell,
        Set.mem_inter_iff, Set.mem_setOf_eq]
      aesop
  | @band _ base hm baseShape f g hf hg hfg hfgraph hggraph =>
      have hproof : hm = hn := Subsingleton.elim _ _
      subst hm
      have hsmall' : small.carrier ⊆ base := by
        exact hsmall
      change charbonnelOpenBand small.carrier f g =
        charbonnelOpenBand base f g ∩ charbonnelCylinderCell small.carrier
      ext z
      simp only [charbonnelOpenBand, charbonnelCylinderCell,
        Set.mem_inter_iff, Set.mem_setOf_eq]
      aesop
  | @lowerRay _ base hm baseShape g hg hgraph =>
      have hproof : hm = hn := Subsingleton.elim _ _
      subst hm
      have hsmall' : small.carrier ⊆ base := by
        exact hsmall
      change charbonnelLowerRayCell small.carrier g =
        charbonnelLowerRayCell base g ∩ charbonnelCylinderCell small.carrier
      ext z
      simp only [charbonnelLowerRayCell, charbonnelCylinderCell,
        Set.mem_inter_iff, Set.mem_setOf_eq]
      aesop
  | @upperRay _ base hm baseShape f hf hgraph =>
      have hproof : hm = hn := Subsingleton.elim _ _
      subst hm
      have hsmall' : small.carrier ⊆ base := by
        exact hsmall
      change charbonnelUpperRayCell small.carrier f =
        charbonnelUpperRayCell base f ∩ charbonnelCylinderCell small.carrier
      ext z
      simp only [charbonnelUpperRayCell, charbonnelCylinderCell,
        Set.mem_inter_iff, Set.mem_setOf_eq]
      aesop
  | @cylinder _ base hm baseShape =>
      have hproof : hm = hn := Subsingleton.elim _ _
      subst hm
      have hsmall' : small.carrier ⊆ base := by
        exact hsmall
      change charbonnelCylinderCell small.carrier =
        charbonnelCylinderCell base ∩ charbonnelCylinderCell small.carrier
      ext z
      simp only [charbonnelCylinderCell, Set.mem_inter_iff,
        Set.mem_setOf_eq]
      aesop

theorem restrictTopToDeepBase_carrier_subset
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + 1))
    (small : CharbonnelDeepEnrichedCell S n)
    (hsmall : small.carrier ⊆ (cell.projectedBase hn).carrier) :
    (cell.restrictTopToDeepBase hC hn small hsmall).carrier ⊆
      cell.carrier := by
  rw [restrictTopToDeepBase_carrier_eq_inter]
  exact inter_subset_left

theorem mem_restrictTopToDeepBase_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelDeepEnrichedCell S (n + 1))
    (small : CharbonnelDeepEnrichedCell S n)
    (hsmall : small.carrier ⊆ (cell.projectedBase hn).carrier)
    {z : RealEuclidean (n + 1)} (hz : z ∈ cell.carrier)
    (hx : realEuclideanTakeLeft z ∈ small.carrier) :
    z ∈ (cell.restrictTopToDeepBase hC hn small hsmall).carrier := by
  rw [restrictTopToDeepBase_carrier_eq_inter]
  exact ⟨hz, by simpa [charbonnelCylinderCell] using hx⟩

end CharbonnelDeepEnrichedCell

/-- A bounded lower common refinement normalizes the top projected bases of
any finite partitioned precover.  This is the extra refinement needed after
deleting and reinserting a graph below one or more trailing coordinates. -/
theorem
    exists_charbonnelFinitePartitionedDeepRelativeCover_of_topBaseRefinement
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ}
    (hII : CharbonnelBoundedDeepRelativeCommonRefinementAt S n)
    (base : CharbonnelDeepEnrichedCell S (n + 1))
    (hbaseBounded : Bornology.IsBounded base.carrier)
    {D A : Set (RealEuclidean ((n + 1) + 1))}
    (hDbase : ∀ z ∈ D, realEuclideanTakeLeft z ∈ base.carrier)
    (source : CharbonnelFinitePartitionedDeepRelativeCellPrecover S D A) :
    Nonempty
      (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D (fun _ : Unit ↦ A)) := by
  classical
  let hn : 0 < n + 1 := by omega
  letI : Finite source.Index := source.indexFinite
  letI : Fintype source.Index := Fintype.ofFinite source.Index
  obtain ⟨fine⟩ := hII base hbaseBounded
    (fun i ↦ (source.cell i).projectedBase hn)
  letI : Finite fine.Index := fine.indexFinite
  let Index := Σ k : fine.Index,
    {i : source.Index //
      (fine.cell k).carrier ⊆
        ((source.cell i).projectedBase hn).carrier}
  let cell : Index → CharbonnelDeepEnrichedCell S ((n + 1) + 1) :=
    fun p ↦ (source.cell p.2.1).restrictTopToDeepBase
      hC hn (fine.cell p.1) p.2.2
  refine ⟨
    { Index := Index
      indexFinite := inferInstance
      cell := cell
      contained := ?_
      covers := ?_
      compatible := ?_
      cells_eq_or_disjoint := ?_
      hereditary_projection_coherent := ?_ }⟩
  · intro p
    exact
      (CharbonnelDeepEnrichedCell.restrictTopToDeepBase_carrier_subset
        hC hn (source.cell p.2.1) (fine.cell p.1) p.2.2).trans
        (source.contained p.2.1)
  · intro z hzD
    obtain ⟨i, hzi⟩ := source.covers z hzD
    have hxSource : realEuclideanTakeLeft z ∈
        ((source.cell i).projectedBase hn).carrier := by
      rw [← (source.cell i).existentialProjection_carrier hC hn]
      exact ⟨realEuclideanTakeRight z, by
        rwa [realEuclideanAppend_takeLeft_takeRight]⟩
    obtain ⟨k, hxk⟩ := fine.covers _ (hDbase z hzD)
    have hkSubset : (fine.cell k).carrier ⊆
        ((source.cell i).projectedBase hn).carrier := by
      rcases fine.compatible k i with hsubset | hdisjoint
      · exact hsubset
      · exact False.elim (Set.disjoint_left.mp hdisjoint hxk hxSource)
    let p : Index := ⟨k, ⟨i, hkSubset⟩⟩
    refine ⟨p, ?_⟩
    exact CharbonnelDeepEnrichedCell.mem_restrictTopToDeepBase_carrier
      hC hn (source.cell i) (fine.cell k) hkSubset hzi hxk
  · intro p _
    have hsub : (cell p).carrier ⊆ (source.cell p.2.1).carrier := by
      exact
        (CharbonnelDeepEnrichedCell.restrictTopToDeepBase_carrier_subset
          hC hn (source.cell p.2.1) (fine.cell p.1) p.2.2)
    rcases source.compatible p.2.1 with htarget | hdisjoint
    · exact Or.inl (hsub.trans htarget)
    · exact Or.inr (hdisjoint.mono hsub Subset.rfl)
  · intro p r
    have hpCarrier : (cell p).carrier =
        (source.cell p.2.1).carrier ∩
          charbonnelCylinderCell (fine.cell p.1).carrier := by
      simpa only [cell] using
        CharbonnelDeepEnrichedCell.restrictTopToDeepBase_carrier_eq_inter
          hC hn (source.cell p.2.1) (fine.cell p.1) p.2.2
    have hrCarrier : (cell r).carrier =
        (source.cell r.2.1).carrier ∩
          charbonnelCylinderCell (fine.cell r.1).carrier := by
      simpa only [cell] using
        CharbonnelDeepEnrichedCell.restrictTopToDeepBase_carrier_eq_inter
          hC hn (source.cell r.2.1) (fine.cell r.1) r.2.2
    rw [hpCarrier, hrCarrier]
    rcases fine.cells_eq_or_disjoint p.1 r.1 with hbase | hbase
    · rcases source.cells_eq_or_disjoint p.2.1 r.2.1 with hsource | hsource
      · left
        ext z
        constructor
        · rintro ⟨hzSource, hzBase⟩
          refine ⟨?_, ?_⟩
          · exact hsource ▸ hzSource
          · change realEuclideanTakeLeft z ∈ (fine.cell r.1).carrier
            change realEuclideanTakeLeft z ∈ (fine.cell p.1).carrier at hzBase
            exact hbase ▸ hzBase
        · rintro ⟨hzSource, hzBase⟩
          refine ⟨?_, ?_⟩
          · exact hsource.symm ▸ hzSource
          · change realEuclideanTakeLeft z ∈ (fine.cell p.1).carrier
            change realEuclideanTakeLeft z ∈ (fine.cell r.1).carrier at hzBase
            exact hbase.symm ▸ hzBase
      · exact Or.inr
          (hsource.mono Set.inter_subset_left Set.inter_subset_left)
    · right
      rw [Set.disjoint_left]
      intro z hzp hzr
      exact Set.disjoint_left.mp hbase
        (by simpa [charbonnelCylinderCell] using hzp.2)
        (by simpa [charbonnelCylinderCell] using hzr.2)
  · change
      (∀ p r,
        ((cell p).projectedBase hn).carrier =
            ((cell r).projectedBase hn).carrier ∨
          Disjoint ((cell p).projectedBase hn).carrier
            ((cell r).projectedBase hn).carrier) ∧
      CharbonnelDeepCellFamilyProjectionCoherent n
        (fun p ↦ (cell p).projectedBase hn)
    constructor
    · intro p r
      simpa only [cell,
        CharbonnelDeepEnrichedCell.restrictTopToDeepBase_projectedBase] using
        fine.cells_eq_or_disjoint p.1 r.1
    · have hcoherent :=
        charbonnelDeepCellFamilyProjectionCoherent_reindex
          fine.hereditary_projection_coherent (fun p : Index ↦ p.1)
      simpa only [cell,
        CharbonnelDeepEnrichedCell.restrictTopToDeepBase_projectedBase] using
        hcoherent

namespace CharbonnelFinitePartitionedDeepLocalBandCover

/-- Forget the exact-base field of a local band cover, retaining precisely
the raw partition data consumed by the global normalization step. -/
def toPrecover
    {S : EuclideanSetFamily} {m : ℕ}
    {base : CharbonnelDeepEnrichedCell S (m + 1)}
    {f g : RealEuclidean (m + 1) → ℝ}
    {A : Set (RealEuclidean ((m + 1) + 1))}
    (cover : CharbonnelFinitePartitionedDeepLocalBandCover S base f g A) :
    CharbonnelFinitePartitionedDeepRelativeCellPrecover S
      (charbonnelOpenBand base.carrier f g) A :=
  { Index := cover.Index
    indexFinite := cover.indexFinite
    cell := cover.cell
    contained := cover.contained
    covers := cover.covers
    compatible := cover.compatible
    cells_eq_or_disjoint := cover.cells_eq_or_disjoint }

/-- Forget the exact-base field of a local band cover while retaining full
hereditary coherence. -/
def toRelativeCover
    {S : EuclideanSetFamily} {m : ℕ}
    {base : CharbonnelDeepEnrichedCell S (m + 1)}
    {f g : RealEuclidean (m + 1) → ℝ}
    {A : Set (RealEuclidean ((m + 1) + 1))}
    (cover : CharbonnelFinitePartitionedDeepLocalBandCover S base f g A) :
    CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
      S (charbonnelOpenBand base.carrier f g) (fun _ : Unit ↦ A) := by
  exact
    { Index := cover.Index
      indexFinite := cover.indexFinite
      cell := cover.cell
      contained := cover.contained
      covers := cover.covers
      compatible := fun i _ ↦ cover.compatible i
      cells_eq_or_disjoint := cover.cells_eq_or_disjoint
      hereditary_projection_coherent := by
        change
          (∀ i j,
            ((cover.cell i).projectedBase (by omega)).carrier =
                ((cover.cell j).projectedBase (by omega)).carrier ∨
              Disjoint
                ((cover.cell i).projectedBase (by omega)).carrier
                ((cover.cell j).projectedBase (by omega)).carrier) ∧
          CharbonnelDeepCellFamilyProjectionCoherent m
            (fun i ↦ (cover.cell i).projectedBase (by omega))
        constructor
        · intro i j
          left
          rw [cover.projectedBase_eq i, cover.projectedBase_eq j]
        · have hconstant :
              CharbonnelDeepCellFamilyProjectionCoherent m
                (fun _ : cover.Index ↦ base) :=
            charbonnelDeepCellFamilyProjectionCoherent_const base
          simpa only [cover.projectedBase_eq] using hconstant }

end CharbonnelFinitePartitionedDeepLocalBandCover

/-! ## The top graph branch on bounded domains -/

/-- Bounded form of the retained top-graph branch. -/
theorem charbonnelBoundedDeepRelativeClosedDecomposition_graph
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {m : ℕ}
    (hI : CharbonnelBoundedDeepRelativeClosedDecompositionAt S m)
    (base : CharbonnelDeepEnrichedCell S (m + 1))
    (hbaseBounded : Bornology.IsBounded base.carrier)
    (f : RealEuclidean (m + 1) → ℝ)
    (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (m + 2))
    {A : Set (RealEuclidean (m + 2))}
    (hA : A ⊆ charbonnelRestrictedGraph base.carrier f)
    (hAmem : A ∈ charbonnelClosure S (m + 2))
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A :
        Set (charbonnelRestrictedGraph base.carrier f))) :
    Nonempty
      (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S (charbonnelRestrictedGraph base.carrier f)
          (fun _ : Unit ↦ A)) := by
  let projectedA : Set (RealEuclidean (m + 1)) :=
    realEuclideanExistentialProjection
      (n := m + 1) (m := 1) A
  have hprojectedSub : projectedA ⊆ base.carrier := by
    rintro x ⟨y, hxy⟩
    simpa only [realEuclideanTakeLeft_append] using (hA hxy).1
  have hprojectedMem : projectedA ∈ charbonnelClosure S (m + 1) :=
    graphProjection_mem_charbonnelClosure (by omega) hAmem
  have hprojectedClosed : IsClosed
      (Subtype.val ⁻¹' projectedA : Set base.carrier) :=
    isClosed_graphProjection_in_base hf hA hAclosed
  obtain ⟨lower⟩ :=
    hI base hbaseBounded hprojectedSub hprojectedMem hprojectedClosed
  exact ⟨lower.liftThroughGraph hC base f hf hgraph
    (fun _ : Unit ↦ A) (fun _ ↦ hA)⟩

/-! ## The open-band branch with lower-dimensional local refinements -/

/-- The genuine cutoff/selector open-band proof, allowing the non-open local
branches to subdivide their projected bases.  A final bounded `(II)`
refinement normalizes all those projected bases simultaneously. -/
theorem
    exists_charbonnelFinitePartitionedDeepRelativeClosedDecomposition_openBand_bounded
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {m : ℕ}
    (hI : CharbonnelBoundedDeepRelativeClosedDecompositionAt S m)
    (hII : CharbonnelBoundedDeepRelativeCommonRefinementAt S m)
    (base : CharbonnelDeepEnrichedCell S (m + 1))
    (hbaseBounded : Bornology.IsBounded base.carrier)
    (f g : RealEuclidean (m + 1) → ℝ)
    (hf : ContinuousOn f base.carrier)
    (hg : ContinuousOn g base.carrier)
    (hfg : ∀ x ∈ base.carrier, f x < g x)
    (hfGraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S ((m + 1) + 1))
    (hgGraph : charbonnelRestrictedGraph base.carrier g ∈
      charbonnelClosure S ((m + 1) + 1))
    {A : MaxwellRelation (m + 1) 1}
    (hAmem : A ∈ charbonnelClosure S ((m + 1) + 1))
    (hAempty : interior A = ∅)
    (hAsub : A ⊆ charbonnelOpenBand base.carrier f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A : Set (charbonnelOpenBand base.carrier f g)))
    (hnonopen : ∀ small : CharbonnelDeepEnrichedCell S (m + 1),
      small.carrier ⊆ base.carrier →
      Bornology.IsBounded small.carrier →
      small.carrier.Nonempty →
      ¬ IsOpen small.carrier →
      Nonempty
        (CharbonnelFinitePartitionedDeepRelativeCellPrecover S
          (charbonnelOpenBand small.carrier f g) A)) :
    Nonempty
      (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S (charbonnelOpenBand base.carrier f g) (fun _ : Unit ↦ A)) := by
  classical
  let hp : 0 < m + 1 := by omega
  let hweak : PositiveArityWeakSetStructure (charbonnelClosure S) :=
    hC.toPositiveArityWeakSetStructure
  have hbaseMem : base.carrier ∈ charbonnelClosure S (m + 1) := by
    simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using
      (base.toCell hweak).carrier_mem
  obtain ⟨N, hN, hNempty⟩ :=
    exists_wilkieSection4_cardinalityCutoff
      hC h21 hp hbaseMem hAmem hAempty
  let loci : WilkieSection4LociIndex N → Set (RealEuclidean (m + 1)) :=
    wilkieSection4LociTarget base.carrier A f g
  let target : WilkieSection4LociIndex N → Set (RealEuclidean (m + 1)) :=
    fun j ↦ loci j ∩ base.carrier
  have htargetSub : ∀ j, target j ⊆ base.carrier :=
    fun _ ↦ inter_subset_right
  have htargetMem : ∀ j,
      target j ∈ charbonnelClosure S (m + 1) := by
    intro j
    exact hweak.ws1_inter (by omega)
      (wilkieSection4LociTarget_mem_charbonnelClosure
        hweak hp hbaseMem hAmem hfGraph hgGraph j)
      hbaseMem
  have htargetClosed : ∀ j,
      IsClosed (Subtype.val ⁻¹' target j : Set base.carrier) := by
    intro j
    exact isClosed_preimage_val_inter_right
      (wilkieSection4LociTarget_isClosed j)
  obtain ⟨fine⟩ :=
    exists_charbonnelFinitePartitionedBoundedDeepSimultaneousClosedRefinement
      hI hII base hbaseBounded target htargetSub htargetMem htargetClosed
  let carrierSetoid : Setoid fine.Index :=
    Setoid.ker (fun i ↦ (fine.cell i).carrier)
  let BaseIndex := Quotient carrierSetoid
  let representative : BaseIndex → fine.Index := Quotient.out
  let baseCell : BaseIndex → CharbonnelDeepEnrichedCell S (m + 1) :=
    fun q ↦ fine.cell (representative q)
  letI : Finite fine.Index := fine.indexFinite
  letI : Finite BaseIndex := Quotient.finite carrierSetoid
  have hbaseCellSub : ∀ q, (baseCell q).carrier ⊆ base.carrier :=
    fun q ↦ fine.contained (representative q)
  have hbaseCellBounded : ∀ q,
      Bornology.IsBounded (baseCell q).carrier :=
    fun q ↦ hbaseBounded.subset (hbaseCellSub q)
  have hlociCompatible : ∀ q j,
      (baseCell q).carrier ⊆ loci j ∨
        Disjoint (baseCell q).carrier (loci j) := by
    intro q j
    have hcompat := fine.compatible (representative q) j
    rcases hcompat with hsub | hdisjoint
    · exact Or.inl (hsub.trans inter_subset_left)
    · right
      rw [Set.disjoint_left]
      intro x hx hxlocus
      exact Set.disjoint_left.mp hdisjoint hx
        ⟨hxlocus, hbaseCellSub q hx⟩
  have hlocal : ∀ q,
      Nonempty
        (CharbonnelFinitePartitionedDeepRelativeCellPrecover S
          (charbonnelOpenBand (baseCell q).carrier f g) A) := by
    intro q
    by_cases hnonempty : (baseCell q).carrier.Nonempty
    · by_cases hopen : IsOpen (baseCell q).carrier
      · have hcardinalityCompatible : ∀ j, j ≤ N →
            (baseCell q).carrier ⊆
                closure (wilkieSection4FiberCardinalityLocus
                  base.carrier A j) ∨
              Disjoint (baseCell q).carrier
                (closure (wilkieSection4FiberCardinalityLocus
                  base.carrier A j)) := by
          intro j hj
          simpa [loci, wilkieSection4LociTarget] using
            hlociCompatible q
              (Sum.inl (⟨j, by omega⟩ : Fin (N + 1)))
        have hencard : ∀ x ∈ (baseCell q).carrier,
            (maxwellScalarFiber A x).encard < (N : ℕ∞) :=
          maxwellScalarFiber_encard_lt_cutoff_of_open_compatible_locus_deep
            hopen hnonempty (hbaseCellSub q) hNempty
              (hcardinalityCompatible N le_rfl)
        have hcollisionCompatible :
            (baseCell q).carrier ⊆
                wilkieSection4CollisionLocus base.carrier A ∨
              Disjoint (baseCell q).carrier
                (wilkieSection4CollisionLocus base.carrier A) := by
          simpa [loci, wilkieSection4LociTarget] using
            hlociCompatible q (Sum.inr (0 : Fin 3))
        have hlowerCompatible :
            (baseCell q).carrier ⊆
                wilkieSection4LowerEndpointLocus base.carrier A f ∨
              Disjoint (baseCell q).carrier
                (wilkieSection4LowerEndpointLocus base.carrier A f) := by
          simpa [loci, wilkieSection4LociTarget] using
            hlociCompatible q (Sum.inr (1 : Fin 3))
        have hupperCompatible :
            (baseCell q).carrier ⊆
                wilkieSection4UpperEndpointLocus base.carrier A g ∨
              Disjoint (baseCell q).carrier
                (wilkieSection4UpperEndpointLocus base.carrier A g) := by
          simpa [loci, wilkieSection4LociTarget] using
            hlociCompatible q (Sum.inr (2 : Fin 3))
        obtain ⟨hcollisionLocus, hlowerLocus, hupperLocus⟩ :=
          disjoint_wilkieSection4_badLoci_of_uniform_cardinality_of_compatible
            hweak h22 hp hopen hnonempty
              (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using
                ((baseCell q).toCell hweak).carrier_mem)
              (hbaseCellSub q) hAmem hfGraph hgGraph hencard
              hcollisionCompatible hlowerCompatible hupperCompatible
        have hescape : MaxwellScalarFiberNoEscape (baseCell q).carrier A :=
          maxwellScalarFiberNoEscape_of_relativelyClosedBand_of_disjoint_endpointLoci
            (hbaseCellSub q) hAsub hAclosed hf hg hlowerLocus hupperLocus
        have hcollision : MaxwellScalarFiberNoCollision
            (baseCell q).carrier A :=
          maxwellScalarFiberNoCollision_of_disjoint_collisionLocus
            (hbaseCellSub q) hcollisionLocus
        obtain ⟨r, _hrN, hfiber⟩ :=
          exists_exact_maxwellScalarFiber_cardinality_of_open_compatible_loci
            hN hopen hnonempty (hbaseCellSub q) hNempty
              hcardinalityCompatible hescape hcollision
        obtain ⟨localBand⟩ :=
          exists_charbonnelFinitePartitionedDeepLocalBandCover_of_exactFibers
            hweak hp base (baseCell q) (hbaseCellSub q) f g hf hg hfg
              hfGraph hgGraph hAsub hAmem hfiber hescape hcollision
        exact ⟨localBand.toPrecover⟩
      · exact hnonopen (baseCell q) (hbaseCellSub q)
          (hbaseCellBounded q) hnonempty hopen
    · have hfiber : ∀ x ∈ (baseCell q).carrier,
          (maxwellScalarFiber A x).Finite ∧
            (maxwellScalarFiber A x).ncard = 0 := by
        intro x hx
        exact (hnonempty ⟨x, hx⟩).elim
      have hescape : MaxwellScalarFiberNoEscape (baseCell q).carrier A := by
        intro x hx
        exact (hnonempty ⟨x, hx⟩).elim
      have hcollision : MaxwellScalarFiberNoCollision
          (baseCell q).carrier A := by
        intro x hx
        exact (hnonempty ⟨x, hx⟩).elim
      obtain ⟨localBand⟩ :=
        exists_charbonnelFinitePartitionedDeepLocalBandCover_of_exactFibers
          hweak hp base (baseCell q) (hbaseCellSub q) f g hf hg hfg
            hfGraph hgGraph hAsub hAmem hfiber hescape hcollision
      exact ⟨localBand.toPrecover⟩
  let localCover : (q : BaseIndex) →
      CharbonnelFinitePartitionedDeepRelativeCellPrecover S
        (charbonnelOpenBand (baseCell q).carrier f g) A :=
    fun q ↦ Classical.choice (hlocal q)
  letI : ∀ q, Finite (localCover q).Index :=
    fun q ↦ (localCover q).indexFinite
  let Index := Σ q : BaseIndex, (localCover q).Index
  let cell : Index → CharbonnelDeepEnrichedCell S ((m + 1) + 1) :=
    fun i ↦ (localCover i.1).cell i.2
  have hrepresentativeCarrier : ∀ i : fine.Index,
      (baseCell (Quotient.mk carrierSetoid i)).carrier =
        (fine.cell i).carrier := by
    intro i
    have hq : Quotient.mk carrierSetoid
          (representative (Quotient.mk carrierSetoid i)) =
        Quotient.mk carrierSetoid i :=
      Quotient.out_eq (Quotient.mk carrierSetoid i)
    exact Quotient.exact hq
  let precover : CharbonnelFinitePartitionedDeepRelativeCellPrecover S
      (charbonnelOpenBand base.carrier f g) A :=
    { Index := Index
      indexFinite := inferInstance
      cell := cell
      contained := by
        rintro ⟨q, i⟩ z hz
        have hzLocal := (localCover q).contained i hz
        exact ⟨hbaseCellSub q hzLocal.1, hzLocal.2⟩
      covers := by
        intro z hz
        obtain ⟨i, hxi⟩ := fine.covers (realEuclideanTakeLeft z) hz.1
        let q : BaseIndex := Quotient.mk carrierSetoid i
        have hxq : realEuclideanTakeLeft z ∈ (baseCell q).carrier := by
          rw [hrepresentativeCarrier i]
          exact hxi
        have hzLocal : z ∈ charbonnelOpenBand (baseCell q).carrier f g :=
          ⟨hxq, hz.2⟩
        obtain ⟨j, hzj⟩ := (localCover q).covers z hzLocal
        exact ⟨⟨q, j⟩, hzj⟩
      compatible := by
        rintro ⟨q, i⟩
        exact (localCover q).compatible i
      cells_eq_or_disjoint := by
        rintro ⟨q, i⟩ ⟨r, j⟩
        change ((localCover q).cell i).carrier =
            ((localCover r).cell j).carrier ∨
          Disjoint ((localCover q).cell i).carrier
            ((localCover r).cell j).carrier
        by_cases hqr : q = r
        · subst r
          exact (localCover q).cells_eq_or_disjoint i j
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
          intro z hzi hzj
          exact Set.disjoint_left.mp hbaseDisjoint
            ((localCover q).contained i hzi).1
            ((localCover r).contained j hzj).1 }
  exact
    exists_charbonnelFinitePartitionedDeepRelativeCover_of_topBaseRefinement
      hweak hII base hbaseBounded (fun _ hz ↦ hz.1) precover

/-- A bounded lower ray over a deep base has empty base. -/
theorem charbonnelLowerRayCell_base_eq_empty_of_isBounded
    {n : ℕ} {base : Set (RealEuclidean n)}
    (g : RealEuclidean n → ℝ)
    (hbounded : Bornology.IsBounded (charbonnelLowerRayCell base g)) :
    base = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hbounded
  let u : RealEuclidean 1 := fun _ ↦ g x - 1
  let v : RealEuclidean 1 := fun _ ↦ g x - (|C| + 2)
  let z := realEuclideanAppend x u
  let w := realEuclideanAppend x v
  have hpos : 0 < |C| + 2 := by
    linarith [abs_nonneg C]
  have hz : z ∈ charbonnelLowerRayCell base g := by
    simp [charbonnelLowerRayCell, z, u, hx]
  have hw : w ∈ charbonnelLowerRayCell base g := by
    simp [charbonnelLowerRayCell, w, v, hx, hpos]
  have hdist : dist (z (Fin.last n)) (w (Fin.last n)) ≤ dist z w := by
    exact (dist_pi_le_iff dist_nonneg).mp le_rfl (Fin.last n)
  have hzw : dist z w ≤ C := hC hz hw
  have hlarge : C < dist (z (Fin.last n)) (w (Fin.last n)) := by
    have hlast : Fin.last n = Fin.natAdd n (0 : Fin 1) := by
      apply Fin.ext
      rfl
    rw [hlast]
    simp only [z, w, realEuclideanAppend_natAdd, u, v, Real.dist_eq]
    have hCabs : C ≤ |C| := le_abs_self C
    rw [show g x - 1 - (g x - (|C| + 2)) = |C| + 1 by ring]
    rw [abs_of_nonneg (by positivity : 0 ≤ |C| + 1)]
    linarith
  linarith

theorem charbonnelLowerRayCell_eq_empty_of_isBounded
    {n : ℕ} {base : Set (RealEuclidean n)}
    (g : RealEuclidean n → ℝ)
    (hbounded : Bornology.IsBounded (charbonnelLowerRayCell base g)) :
    charbonnelLowerRayCell base g = ∅ := by
  rw [charbonnelLowerRayCell_base_eq_empty_of_isBounded g hbounded]
  ext z
  simp [charbonnelLowerRayCell]

/-- A bounded upper ray over a deep base has empty base. -/
theorem charbonnelUpperRayCell_base_eq_empty_of_isBounded
    {n : ℕ} {base : Set (RealEuclidean n)}
    (f : RealEuclidean n → ℝ)
    (hbounded : Bornology.IsBounded (charbonnelUpperRayCell base f)) :
    base = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hbounded
  let u : RealEuclidean 1 := fun _ ↦ f x + 1
  let v : RealEuclidean 1 := fun _ ↦ f x + (|C| + 2)
  let z := realEuclideanAppend x u
  let w := realEuclideanAppend x v
  have hpos : 0 < |C| + 2 := by
    linarith [abs_nonneg C]
  have hz : z ∈ charbonnelUpperRayCell base f := by
    simp [charbonnelUpperRayCell, z, u, hx]
  have hw : w ∈ charbonnelUpperRayCell base f := by
    simp [charbonnelUpperRayCell, w, v, hx, hpos]
  have hdist : dist (z (Fin.last n)) (w (Fin.last n)) ≤ dist z w := by
    exact (dist_pi_le_iff dist_nonneg).mp le_rfl (Fin.last n)
  have hzw : dist z w ≤ C := hC hz hw
  have hlarge : C < dist (z (Fin.last n)) (w (Fin.last n)) := by
    have hlast : Fin.last n = Fin.natAdd n (0 : Fin 1) := by
      apply Fin.ext
      rfl
    rw [hlast]
    simp only [z, w, realEuclideanAppend_natAdd, u, v, Real.dist_eq]
    have hCabs : C ≤ |C| := le_abs_self C
    rw [show f x + 1 - (f x + (|C| + 2)) = -(|C| + 1) by ring]
    rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ |C| + 1)]
    linarith
  linarith

theorem charbonnelUpperRayCell_eq_empty_of_isBounded
    {n : ℕ} {base : Set (RealEuclidean n)}
    (f : RealEuclidean n → ℝ)
    (hbounded : Bornology.IsBounded (charbonnelUpperRayCell base f)) :
    charbonnelUpperRayCell base f = ∅ := by
  rw [charbonnelUpperRayCell_base_eq_empty_of_isBounded f hbounded]
  ext z
  simp [charbonnelUpperRayCell]

/-- A bounded full cylinder over a deep base has empty base. -/
theorem charbonnelCylinderCell_base_eq_empty_of_isBounded
    {n : ℕ} {base : Set (RealEuclidean n)}
    (hbounded : Bornology.IsBounded (charbonnelCylinderCell base)) :
    base = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hbounded
  let u : RealEuclidean 1 := fun _ ↦ 0
  let v : RealEuclidean 1 := fun _ ↦ |C| + 1
  let z := realEuclideanAppend x u
  let w := realEuclideanAppend x v
  have hz : z ∈ charbonnelCylinderCell base := by
    simpa [charbonnelCylinderCell, z] using hx
  have hw : w ∈ charbonnelCylinderCell base := by
    simpa [charbonnelCylinderCell, w] using hx
  have hdist : dist (z (Fin.last n)) (w (Fin.last n)) ≤ dist z w := by
    exact (dist_pi_le_iff dist_nonneg).mp le_rfl (Fin.last n)
  have hzw : dist z w ≤ C := hC hz hw
  have hlarge : C < dist (z (Fin.last n)) (w (Fin.last n)) := by
    have hlast : Fin.last n = Fin.natAdd n (0 : Fin 1) := by
      apply Fin.ext
      rfl
    rw [hlast]
    simp only [z, w, realEuclideanAppend_natAdd, u, v, Real.dist_eq,
      zero_sub, abs_neg]
    rw [abs_of_nonneg (by positivity : 0 ≤ |C| + 1)]
    linarith [le_abs_self C]
  linarith

theorem charbonnelCylinderCell_eq_empty_of_isBounded
    {n : ℕ} {base : Set (RealEuclidean n)}
    (hbounded : Bornology.IsBounded (charbonnelCylinderCell base)) :
    charbonnelCylinderCell base = ∅ := by
  rw [charbonnelCylinderCell_base_eq_empty_of_isBounded hbounded]
  ext z
  simp [charbonnelCylinderCell]

/-! ## Successor assembly -/

/-- The precise local output needed from deletion and reinsertion of the
first singular coordinate of a bounded non-open successor cell. -/
def CharbonnelBoundedDeepNonOpenPrecoverAt
    (S : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ (D : CharbonnelDeepEnrichedCell S ((n + 1) + 1)),
    Bornology.IsBounded D.carrier →
    D.carrier.Nonempty →
    ¬ IsOpen D.carrier →
    ∀ {A : Set (RealEuclidean ((n + 1) + 1))},
      A ⊆ D.carrier →
      A ∈ charbonnelClosure S ((n + 1) + 1) →
      IsClosed (Subtype.val ⁻¹' A : Set D.carrier) →
      Nonempty
        (CharbonnelFinitePartitionedDeepRelativeCellPrecover
          S D.carrier A)

/-- Assemble the bounded successor step from the singular-coordinate
transport precover.  This statement isolates the geometric shape split from
the deletion/reinsertion implementation. -/
theorem
    charbonnelBoundedDeepRelativeEmptyInteriorDecompositionAt_succ_of_nonOpenPrecover
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {n : ℕ}
    (hI : CharbonnelBoundedDeepRelativeClosedDecompositionAt S n)
    (hII : CharbonnelBoundedDeepRelativeCommonRefinementAt S n)
    (hnonopen : CharbonnelBoundedDeepNonOpenPrecoverAt S n) :
    CharbonnelBoundedDeepRelativeEmptyInteriorDecompositionAt S (n + 1) := by
  let hweak : PositiveArityWeakSetStructure (charbonnelClosure S) :=
    hC.toPositiveArityWeakSetStructure
  intro D hDbounded A hAD hAmem hAclosed hAempty
  rcases D with ⟨carrier, shape⟩
  cases shape with
  | graph hn baseShape f hf hgraph =>
      let base : CharbonnelDeepEnrichedCell S (n + 1) :=
        ⟨_, baseShape⟩
      have hbaseBounded : Bornology.IsBounded base.carrier := by
        exact CharbonnelDeepEnrichedCell.projectedBase_isBounded
          hweak hn
          ⟨charbonnelRestrictedGraph base.carrier f,
            .graph hn baseShape f hf hgraph⟩ hDbounded
      exact charbonnelBoundedDeepRelativeClosedDecomposition_graph
        hweak hI base hbaseBounded f hf hgraph hAD hAmem hAclosed
  | band hn baseShape f g hf hg hfg hfGraph hgGraph =>
      let base : CharbonnelDeepEnrichedCell S (n + 1) :=
        ⟨_, baseShape⟩
      have hbaseBounded : Bornology.IsBounded base.carrier := by
        exact CharbonnelDeepEnrichedCell.projectedBase_isBounded
          hweak hn
          ⟨charbonnelOpenBand base.carrier f g,
            .band hn baseShape f g hf hg hfg hfGraph hgGraph⟩ hDbounded
      apply
        exists_charbonnelFinitePartitionedDeepRelativeClosedDecomposition_openBand_bounded
          hC h21 h22 hI hII base hbaseBounded f g hf hg hfg
            hfGraph hgGraph hAmem hAempty hAD hAclosed
      intro small hsmallSub hsmallBounded hsmallNonempty hsmallNotOpen
      have hfSmall : ContinuousOn f small.carrier := hf.mono hsmallSub
      have hgSmall : ContinuousOn g small.carrier := hg.mono hsmallSub
      have hfgSmall : ∀ x ∈ small.carrier, f x < g x :=
        fun x hx ↦ hfg x (hsmallSub hx)
      have hfGraphSmall : charbonnelRestrictedGraph small.carrier f ∈
          charbonnelClosure S ((n + 1) + 1) :=
        charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
          hweak hn hsmallSub (small.toCell hweak).carrier_mem hfGraph
      have hgGraphSmall : charbonnelRestrictedGraph small.carrier g ∈
          charbonnelClosure S ((n + 1) + 1) :=
        charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
          hweak hn hsmallSub (small.toCell hweak).carrier_mem hgGraph
      let localCell : CharbonnelDeepEnrichedCell S ((n + 1) + 1) :=
        small.ofVertical hweak hn
          (.band f g hfSmall hgSmall hfgSmall hfGraphSmall hgGraphSmall)
      have hlocalCarrier : localCell.carrier =
          charbonnelOpenBand small.carrier f g := rfl
      have hlocalSub : localCell.carrier ⊆
          charbonnelOpenBand base.carrier f g := by
        rw [hlocalCarrier]
        intro z hz
        exact ⟨hsmallSub hz.1, hz.2⟩
      have hlocalBounded : Bornology.IsBounded localCell.carrier :=
        hDbounded.subset hlocalSub
      have hlocalNonempty : localCell.carrier.Nonempty := by
        obtain ⟨x, hx⟩ := hsmallNonempty
        let y : RealEuclidean 1 := fun _ ↦ (f x + g x) / 2
        refine ⟨realEuclideanAppend x y, ?_⟩
        rw [hlocalCarrier]
        simp only [charbonnelOpenBand, realEuclideanTakeLeft_append,
          realEuclideanTakeRight_append, Set.mem_setOf_eq, y]
        constructor
        · exact hx
        constructor <;> linarith [hfgSmall x hx]
      have hlocalNotOpen : ¬ IsOpen localCell.carrier := by
        intro hopen
        exact hsmallNotOpen
          (isOpen_charbonnelDeepEnrichedCell_projectedBase
            hweak hn localCell hopen)
      let localA : Set (RealEuclidean ((n + 1) + 1)) :=
        A ∩ localCell.carrier
      have hlocalASub : localA ⊆ localCell.carrier := inter_subset_right
      have hlocalAMem : localA ∈
          charbonnelClosure S ((n + 1) + 1) := by
        exact hweak.ws1_inter (by omega) hAmem
          (by simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using
            (localCell.toCell hweak).carrier_mem)
      have hlocalAClosed : IsClosed
          (Subtype.val ⁻¹' localA : Set localCell.carrier) := by
        exact isClosed_preimage_val_inter_of_subset hlocalSub hAclosed
      obtain ⟨localCover⟩ := hnonopen localCell hlocalBounded hlocalNonempty
        hlocalNotOpen hlocalASub hlocalAMem hlocalAClosed
      exact ⟨localCover.retargetInterDomain⟩
  | lowerRay hn baseShape g hg hgraph =>
      let cell : CharbonnelDeepEnrichedCell S ((n + 1) + 1) :=
        ⟨charbonnelLowerRayCell _ g,
          .lowerRay hn baseShape g hg hgraph⟩
      exact exists_charbonnelFinitePartitionedDeepRelativeCover_of_empty
        cell (charbonnelLowerRayCell_eq_empty_of_isBounded g hDbounded) A
  | upperRay hn baseShape f hf hgraph =>
      let cell : CharbonnelDeepEnrichedCell S ((n + 1) + 1) :=
        ⟨charbonnelUpperRayCell _ f,
          .upperRay hn baseShape f hf hgraph⟩
      exact exists_charbonnelFinitePartitionedDeepRelativeCover_of_empty
        cell (charbonnelUpperRayCell_eq_empty_of_isBounded f hDbounded) A
  | cylinder hn baseShape =>
      let cell : CharbonnelDeepEnrichedCell S ((n + 1) + 1) :=
        ⟨charbonnelCylinderCell _, .cylinder hn baseShape⟩
      exact exists_charbonnelFinitePartitionedDeepRelativeCover_of_empty
        cell (charbonnelCylinderCell_eq_empty_of_isBounded hDbounded) A

/-- Source-faithful bounded empty-interior decomposition in the successor
dimension.  The buried graph or unary point coordinate is deleted exactly
once, and all local cells are normalized together afterward. -/
theorem charbonnelBoundedDeepRelativeEmptyInteriorDecompositionAt_succ
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {n : ℕ}
    (hI : CharbonnelBoundedDeepRelativeClosedDecompositionAt S n)
    (hII : CharbonnelBoundedDeepRelativeCommonRefinementAt S n) :
    CharbonnelBoundedDeepRelativeEmptyInteriorDecompositionAt S (n + 1) := by
  apply
    charbonnelBoundedDeepRelativeEmptyInteriorDecompositionAt_succ_of_nonOpenPrecover
      hC h21 h22 hI hII
  exact charbonnelBoundedDeepNonOpenPrecover_of_lower
    hC.toPositiveArityWeakSetStructure hI

/-- The bounded closed-decomposition successor step, obtained from the
empty-interior construction by the supplied boundary carrier. -/
theorem charbonnelBoundedDeepRelativeClosedDecompositionAt_succ
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {n : ℕ}
    (hI : CharbonnelBoundedDeepRelativeClosedDecompositionAt S n)
    (hII : CharbonnelBoundedDeepRelativeCommonRefinementAt S n)
    (hboundary : ∀ {K : Set (RealEuclidean ((n + 1) + 1))},
      IsClosed K → K ∈ charbonnelClosure S ((n + 1) + 1) →
      ∃ B : Set (RealEuclidean ((n + 1) + 1)),
        IsClosed B ∧ B ∈ charbonnelClosure S ((n + 1) + 1) ∧
          interior B = ∅ ∧ frontier K ⊆ B) :
    CharbonnelBoundedDeepRelativeClosedDecompositionAt S (n + 1) := by
  exact charbonnelBoundedDeepRelativeClosedDecompositionAt_of_emptyInterior
    hC.toPositiveArityWeakSetStructure hboundary
      (charbonnelBoundedDeepRelativeEmptyInteriorDecompositionAt_succ
        hC h21 h22 hI hII)

end AbelFormalization
