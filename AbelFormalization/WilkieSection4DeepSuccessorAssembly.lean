import AbelFormalization.WilkieSection4DeepProjectionTower
import AbelFormalization.WilkieSection4BoundedEnrichedReduction

/-!
# Wilkie Section 4: hereditary successor assembly

Wilkie's successor step first partitions the projected bases and then lifts
the resulting base pieces through the vertical cells.  For recursively
enriched cells the same construction must retain the complete lower
projection history.  This file proves that exact step.

Given a retained enriched cover in dimension `n + 2` and a partitioned deep
cover of its projected domain which is compatible with every recorded base,
we restrict each vertical cell to every lower piece contained in its base.
The resulting family is a deep projection-coherent cover.  Thus the
higher-dimensional deep-cover obligation reduces to Wilkie's lower-dimensional
partitioned refinement, rather than requiring an unrelated deep cover as a
new primitive assumption.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

namespace CharbonnelDeepEnrichedCell

/-- Restrict a retained successor cell to a recursively enriched subcell of
its recorded base, preserving the complete lower projection history. -/
def restrictToDeepBase
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelEnrichedSuccessorCell S n)
    (small : CharbonnelDeepEnrichedCell S n)
    (hsmall : small.carrier ⊆ cell.base.carrier) :
    CharbonnelDeepEnrichedCell S (n + 1) :=
  small.ofVertical hC hn
    (cell.vertical.restrictBase hC hn
      (by simpa only [small.toCell_carrier hC] using hsmall))

@[simp]
theorem restrictToDeepBase_projectedBase
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelEnrichedSuccessorCell S n)
    (small : CharbonnelDeepEnrichedCell S n)
    (hsmall : small.carrier ⊆ cell.base.carrier) :
    (restrictToDeepBase hC hn cell small hsmall).projectedBase hn = small := by
  exact ofVertical_projectedBase hC hn small _

theorem restrictToDeepBase_carrier_subset
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelEnrichedSuccessorCell S n)
    (small : CharbonnelDeepEnrichedCell S n)
    (hsmall : small.carrier ⊆ cell.base.carrier) :
    (restrictToDeepBase hC hn cell small hsmall).carrier ⊆ cell.carrier := by
  let hsmall' : (small.toCell hC).carrier ⊆ cell.base.carrier := by
    simpa only [small.toCell_carrier hC] using hsmall
  simpa only [restrictToDeepBase, ofVertical_carrier,
    CharbonnelEnrichedSuccessorCell.restrictBase,
    CharbonnelEnrichedSuccessorCell.carrier] using
    (CharbonnelEnrichedSuccessorCell.restrictBase_carrier_subset
      hC hn cell (small.toCell hC) hsmall')

theorem mem_restrictToDeepBase_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (cell : CharbonnelEnrichedSuccessorCell S n)
    (small : CharbonnelDeepEnrichedCell S n)
    (hsmall : small.carrier ⊆ cell.base.carrier)
    {z : RealEuclidean (n + 1)} (hz : z ∈ cell.carrier)
    (hx : realEuclideanTakeLeft z ∈ small.carrier) :
    z ∈ (restrictToDeepBase hC hn cell small hsmall).carrier := by
  let hsmall' : (small.toCell hC).carrier ⊆ cell.base.carrier := by
    simpa only [small.toCell_carrier hC] using hsmall
  simpa only [restrictToDeepBase, ofVertical_carrier,
    CharbonnelEnrichedSuccessorCell.restrictBase,
    CharbonnelEnrichedSuccessorCell.carrier,
    small.toCell_carrier hC] using
    (CharbonnelEnrichedSuccessorCell.mem_restrictBase_carrier
      hC hn cell (small.toCell hC) hsmall' hz hx)

end CharbonnelDeepEnrichedCell

namespace CharbonnelCell

/-- Unary recursive cells retain enough information to recover their deep
enrichment: their shape is already an elementary unary piece.  This is first
stated propositionally because `CharbonnelCellShape` itself is a proposition. -/
theorem exists_deepUnary
    {S : EuclideanSetFamily}
    (cell : CharbonnelCell (charbonnelClosure S) 1) :
    ∃ deep : CharbonnelDeepEnrichedCell S 1,
      deep.carrier = cell.carrier := by
  rcases cell with ⟨cellCarrier, shape, hcarrier⟩
  cases shape with
  | unary piece =>
      exact ⟨⟨realEuclideanUnaryPiece piece, .unary piece⟩, rfl⟩
  | graph hn => omega
  | band hn => omega
  | lowerRay hn => omega
  | upperRay hn => omega
  | cylinder hn => omega

/-- A chosen deep enrichment of a unary recursive cell. -/
noncomputable def toDeepUnary
    {S : EuclideanSetFamily}
    (cell : CharbonnelCell (charbonnelClosure S) 1) :
    CharbonnelDeepEnrichedCell S 1 :=
  Classical.choose cell.exists_deepUnary

@[simp]
theorem toDeepUnary_carrier
    {S : EuclideanSetFamily}
    (cell : CharbonnelCell (charbonnelClosure S) 1) :
    cell.toDeepUnary.carrier = cell.carrier :=
  Classical.choose_spec cell.exists_deepUnary

end CharbonnelCell

/-! ## The hereditary successor step -/

/-- Hereditary projection coherence is preserved when a family is reindexed.
This is used below because one lower base piece can support several distinct
vertical cells. -/
theorem charbonnelDeepCellFamilyProjectionCoherent_comp
    {S : EuclideanSetFamily} {I J : Type} :
    ∀ {n : ℕ} {cells : I → CharbonnelDeepEnrichedCell S (n + 1)},
      CharbonnelDeepCellFamilyProjectionCoherent n cells →
      (f : J → I) →
      CharbonnelDeepCellFamilyProjectionCoherent n (fun j ↦ cells (f j))
  | 0, _cells, _hcoherent, _f => trivial
  | n + 1, cells, hcoherent, f => by
      refine ⟨?_, ?_⟩
      · intro i j
        exact hcoherent.1 (f i) (f j)
      · exact charbonnelDeepCellFamilyProjectionCoherent_comp
          hcoherent.2 f

/-- A retained cover in dimension `n + 2`, together with a partitioned deep
cover of its projected domain compatible with all recorded bases, assembles
to one deep projection-coherent cover.  The lower cover's target is arbitrary:
only its domain partition and hereditary enrichment are used in the lift. -/
theorem exists_charbonnelFiniteDeepProjectionCoherentCellCover_succ
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ}
    {D A : Set (RealEuclidean ((n + 1) + 1))}
    (source : CharbonnelFiniteEnrichedCompatibleRelativeCellCover
      S (n + 1) D A)
    (hAD : A ⊆ D)
    {lowerDomain lowerTarget : Set (RealEuclidean (n + 1))}
    (lower : CharbonnelFiniteDeepProjectionCoherentCellCover S
      lowerDomain lowerTarget)
    (hlowerDomain : lowerDomain = realEuclideanExistentialProjection D)
    (hlowerPartition : ∀ k l,
      (lower.cell k).carrier = (lower.cell l).carrier ∨
        Disjoint (lower.cell k).carrier (lower.cell l).carrier)
    (hlowerCompatible : ∀ k i,
      (lower.cell k).carrier ⊆ (source.cell i).base.carrier ∨
        Disjoint (lower.cell k).carrier (source.cell i).base.carrier) :
    Nonempty
      (CharbonnelFiniteDeepProjectionCoherentCellCover S D A) := by
  classical
  let _ : Finite source.Index := source.indexFinite
  let _ : Finite lower.Index := lower.indexFinite
  let Index := Σ k : lower.Index,
    {i : source.Index //
      (lower.cell k).carrier ⊆ (source.cell i).base.carrier}
  let cell : Index → CharbonnelDeepEnrichedCell S ((n + 1) + 1) :=
    fun p ↦ CharbonnelDeepEnrichedCell.restrictToDeepBase
      hC (by omega) (source.cell p.2.1) (lower.cell p.1) p.2.2
  refine ⟨
    { Index := Index
      indexFinite := inferInstance
      cell := cell
      target_subset_domain := hAD
      contained := ?_
      covers := ?_
      compatible := ?_
      hereditary_projection_coherent := ?_ }⟩
  · intro p
    exact (CharbonnelDeepEnrichedCell.restrictToDeepBase_carrier_subset
      hC (by omega) (source.cell p.2.1) (lower.cell p.1) p.2.2).trans
        (source.contained p.2.1)
  · intro z hzD
    obtain ⟨i, hzi⟩ := source.covers z hzD
    have hxSource : realEuclideanTakeLeft z ∈
        (source.cell i).base.carrier := by
      rw [← (source.cell i).existentialProjection_carrier]
      exact ⟨realEuclideanTakeRight z, by rwa [realEuclideanAppend_take]⟩
    have hxD : realEuclideanTakeLeft z ∈
        realEuclideanExistentialProjection D :=
      ⟨realEuclideanTakeRight z, by rwa [realEuclideanAppend_take]⟩
    have hxLower : realEuclideanTakeLeft z ∈ lowerDomain := by
      rwa [hlowerDomain]
    obtain ⟨k, hxk⟩ := lower.covers _ hxLower
    have hkSubset : (lower.cell k).carrier ⊆
        (source.cell i).base.carrier := by
      rcases hlowerCompatible k i with hsubset | hdisjoint
      · exact hsubset
      · exact False.elim (Set.disjoint_left.mp hdisjoint hxk hxSource)
    let p : Index := ⟨k, ⟨i, hkSubset⟩⟩
    refine ⟨p, ?_⟩
    exact CharbonnelDeepEnrichedCell.mem_restrictToDeepBase_carrier
      hC (by omega) (source.cell i) (lower.cell k) hkSubset hzi hxk
  · intro p
    have hsub : (cell p).carrier ⊆ (source.cell p.2.1).carrier :=
      CharbonnelDeepEnrichedCell.restrictToDeepBase_carrier_subset
        hC (by omega) (source.cell p.2.1) (lower.cell p.1) p.2.2
    rcases source.compatible p.2.1 with htarget | hdisjoint
    · exact Or.inl (hsub.trans htarget)
    · exact Or.inr (hdisjoint.mono hsub Subset.rfl)
  · change
      (∀ p r,
        ((cell p).projectedBase (by omega)).carrier =
            ((cell r).projectedBase (by omega)).carrier ∨
          Disjoint
            ((cell p).projectedBase (by omega)).carrier
            ((cell r).projectedBase (by omega)).carrier) ∧
      CharbonnelDeepCellFamilyProjectionCoherent n
        (fun p ↦ (cell p).projectedBase (by omega))
    constructor
    · intro p r
      simpa only [cell,
        CharbonnelDeepEnrichedCell.restrictToDeepBase_projectedBase] using
        hlowerPartition p.1 r.1
    · have hcoherent :=
        charbonnelDeepCellFamilyProjectionCoherent_comp
          lower.hereditary_projection_coherent (fun p : Index ↦ p.1)
      simpa only [cell,
        CharbonnelDeepEnrichedCell.restrictToDeepBase_projectedBase] using
        hcoherent

/-! ## The unary base of the hereditary induction -/

/-- Select from a partitioned unary common refinement exactly the cells lying
in one distinguished domain cell, and retain their canonical deep unary
enrichment.  This is the lower cover used in the first successor step. -/
def
    CharbonnelFinitePartitionedSimultaneouslyCompatibleCellCover.deepUnaryDomainCover
    {S : EuclideanSetFamily} {I : Type}
    {target : I → Set (RealEuclidean 1)}
    (fine : CharbonnelFinitePartitionedSimultaneouslyCompatibleCellCover
      (charbonnelClosure S) target)
    (j : I)
    (domainCell : CharbonnelCell (charbonnelClosure S) 1)
    (hdomain : target j = domainCell.carrier) :
    CharbonnelFiniteDeepProjectionCoherentCellCover S
      domainCell.carrier (∅ : Set (RealEuclidean 1)) := by
  classical
  let Index := {k : Fin fine.cover.count //
    (fine.cover.cell k).carrier ⊆ domainCell.carrier}
  exact
    { Index := Index
      indexFinite := inferInstance
      cell := fun k ↦ (fine.cover.cell k.1).toDeepUnary
      target_subset_domain := Set.empty_subset _
      contained := by
        intro k
        simpa only [CharbonnelCell.toDeepUnary_carrier] using k.2
      covers := by
        intro x hx
        obtain ⟨k, hxk⟩ := fine.cover.covers x
        have hkSubset : (fine.cover.cell k).carrier ⊆
            domainCell.carrier := by
          have hcompat := fine.cover.compatible k j
          rw [hdomain] at hcompat
          rcases hcompat with hsubset | hdisjoint
          · exact hsubset
          · exact False.elim (Set.disjoint_left.mp hdisjoint hxk hx)
        exact ⟨⟨k, hkSubset⟩, by
          simpa only [CharbonnelCell.toDeepUnary_carrier] using hxk⟩
      compatible := by
        intro k
        exact Or.inr (Set.disjoint_empty _)
      hereditary_projection_coherent := trivial }

theorem
    CharbonnelFinitePartitionedSimultaneouslyCompatibleCellCover.deepUnaryDomainCover_partitioned
    {S : EuclideanSetFamily} {I : Type}
    {target : I → Set (RealEuclidean 1)}
    (fine : CharbonnelFinitePartitionedSimultaneouslyCompatibleCellCover
      (charbonnelClosure S) target)
    (j : I)
    (domainCell : CharbonnelCell (charbonnelClosure S) 1)
    (hdomain : target j = domainCell.carrier) :
    ∀ k l,
      ((fine.deepUnaryDomainCover j domainCell hdomain).cell k).carrier =
          ((fine.deepUnaryDomainCover j domainCell hdomain).cell l).carrier ∨
        Disjoint
          ((fine.deepUnaryDomainCover j domainCell hdomain).cell k).carrier
          ((fine.deepUnaryDomainCover j domainCell hdomain).cell l).carrier := by
  intro k l
  simpa only [deepUnaryDomainCover,
    CharbonnelCell.toDeepUnary_carrier] using
    fine.cells_eq_or_disjoint k.1 l.1

/-- The first nontrivial hereditary case.  A partitioned `(II)₁` refinement
of the recorded unary bases and the projected domain cell turns any enriched
relative cover in dimension two into a deep projection-coherent cover. -/
theorem exists_charbonnelFiniteDeepProjectionCoherentCellCover_two
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hII : CharbonnelFinitePartitionedCellFamilyCommonRefinementAt
      (charbonnelClosure S) 1)
    {D A : Set (RealEuclidean (1 + 1))}
    (source : CharbonnelFiniteEnrichedCompatibleRelativeCellCover S 1 D A)
    (hAD : A ⊆ D)
    (domainCell : CharbonnelCell (charbonnelClosure S) 1)
    (hdomain : domainCell.carrier =
      realEuclideanExistentialProjection D) :
    Nonempty (CharbonnelFiniteDeepProjectionCoherentCellCover S D A) := by
  classical
  let _ : Finite source.Index := source.indexFinite
  let _ : Fintype source.Index := Fintype.ofFinite source.Index
  let input : (source.Index ⊕ Unit) →
      CharbonnelCell (charbonnelClosure S) 1
    | Sum.inl i => (source.cell i).base
    | Sum.inr _ => domainCell
  obtain ⟨fine⟩ := hII input
  have htargetDomain : (fun i ↦ (input i).carrier) (Sum.inr ()) =
      domainCell.carrier := rfl
  let lower :=
    fine.deepUnaryDomainCover (Sum.inr ()) domainCell htargetDomain
  have hlowerPartition : ∀ k l,
      (lower.cell k).carrier = (lower.cell l).carrier ∨
        Disjoint (lower.cell k).carrier (lower.cell l).carrier := by
    simpa only [lower] using
      (fine.deepUnaryDomainCover_partitioned
        (Sum.inr ()) domainCell htargetDomain)
  have hlowerCompatible : ∀ k i,
      (lower.cell k).carrier ⊆ (source.cell i).base.carrier ∨
        Disjoint (lower.cell k).carrier (source.cell i).base.carrier := by
    intro k i
    have hcompat := fine.cover.compatible k.1 (Sum.inl i)
    simpa only [lower, input,
      CharbonnelFinitePartitionedSimultaneouslyCompatibleCellCover.deepUnaryDomainCover,
      CharbonnelCell.toDeepUnary_carrier] using hcompat
  exact exists_charbonnelFiniteDeepProjectionCoherentCellCover_succ
    hC source hAD lower hdomain hlowerPartition hlowerCompatible

/-- Bounded-cube form of the two-dimensional base case. -/
theorem exists_charbonnelFiniteDeepProjectionCoherentCellCover_openCube_two
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hII : CharbonnelFinitePartitionedCellFamilyCommonRefinementAt
      (charbonnelClosure S) 1)
    {A : Set (RealEuclidean (1 + 1))}
    (source : CharbonnelFiniteEnrichedCompatibleRelativeCellCover S 1
      (wilkieOpenCube (1 + 1)) A)
    (hA : A ⊆ wilkieOpenCube (1 + 1)) :
    Nonempty
      (CharbonnelFiniteDeepProjectionCoherentCellCover S
        (wilkieOpenCube (1 + 1)) A) := by
  let domainCell := charbonnelOpenCubeCell hC 1 (by omega)
  apply exists_charbonnelFiniteDeepProjectionCoherentCellCover_two
    hC hII source hA domainCell
  rw [charbonnelOpenCubeCell_carrier hC (by omega),
    realEuclideanExistentialProjection_wilkieOpenCube_succ]

/-- The dimension-two slice of the bounded deep-cover property follows from
the already existing enriched closed-lift cover and partitioned unary
refinement interfaces. -/
theorem wilkieBoundedDeepProjectionCoherentCellCoverProperty_two
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hII : CharbonnelFinitePartitionedCellFamilyCommonRefinementAt
      (charbonnelClosure S) 1)
    (hsource : WilkieBoundedEnrichedProjectedClosedLiftCellCoverProperty S) :
    ∀ {q : ℕ} {B : Set (RealEuclidean ((1 + 1) + q))},
      IsClosed B → B ∈ charbonnelClosure S ((1 + 1) + q) →
        Nonempty
          (CharbonnelFiniteDeepProjectionCoherentCellCover S
            (wilkieOpenCube (1 + 1))
            (wilkieBoundedImage (realEuclideanExistentialProjection B))) := by
  intro q B hBclosed hBmem
  obtain ⟨source⟩ := hsource (n := 1) (q := q) (by omega)
    hBclosed hBmem
  exact exists_charbonnelFiniteDeepProjectionCoherentCellCover_openCube_two
    hC hII source (wilkieBoundedImage_subset_openCube _)

end AbelFormalization
