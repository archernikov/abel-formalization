import AbelFormalization.WilkieSection4ProjectionTowerAssembly
import AbelFormalization.WilkieSection4SourceAssembly
import AbelFormalization.CharbonnelCellBoundaryCompatibility

/-!
# Wilkie Section 4: the intrinsic graph-cell induction

The first non-open case in Wilkie's simultaneous induction is a graph cell.
Projection onto its recorded base is a homeomorphism, so a relatively closed
target pulls back to a relatively closed target one dimension lower.  A
compatible cover of that lower target then lifts, cell by cell, through the
same retained graph.

This file records the complete construction.  In particular, graph
membership after restricting the base is derived from the retained graph
certificate; no complement closure or additional cell-existence premise is
used.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## The intrinsic graph homeomorphism -/

/-- Projection onto the first coordinate block is a homeomorphism from a
restricted graph to its base.  We orient the homeomorphism from the base to
the graph so its inverse is literally the coordinate projection. -/
def charbonnelRestrictedGraphToFun
    {n : ℕ} {base : Set (RealEuclidean n)}
    (f : RealEuclidean n → ℝ) (x : base) :
    charbonnelRestrictedGraph base f :=
  ⟨charbonnelGraphParam f x, by
    simp [charbonnelRestrictedGraph, charbonnelGraphParam,
      realEuclideanSingletonVector, x.2]⟩

def charbonnelRestrictedGraphInvFun
    {n : ℕ} {base : Set (RealEuclidean n)}
    (f : RealEuclidean n → ℝ)
    (z : charbonnelRestrictedGraph base f) : base :=
  ⟨realEuclideanTakeLeft (n := n) (m := 1)
      (z : RealEuclidean (n + 1)), z.2.1⟩

def charbonnelRestrictedGraphHomeomorph
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f : RealEuclidean n → ℝ} (hf : ContinuousOn f base) :
    base ≃ₜ charbonnelRestrictedGraph base f where
  toFun := charbonnelRestrictedGraphToFun f
  invFun := charbonnelRestrictedGraphInvFun f
  left_inv x := by
    apply Subtype.ext
    simp [charbonnelRestrictedGraphToFun,
      charbonnelRestrictedGraphInvFun, charbonnelGraphParam]
  right_inv z := by
    apply Subtype.ext
    have hright :
        realEuclideanSingletonVector
            (f (realEuclideanTakeLeft (n := n) (m := 1)
              (z : RealEuclidean (n + 1)))) =
          realEuclideanTakeRight (n := n) (m := 1)
            (z : RealEuclidean (n + 1)) := by
      funext j
      rw [Fin.eq_zero j]
      simpa [realEuclideanSingletonVector] using z.2.2.symm
    change charbonnelGraphParam f (realEuclideanTakeLeft (z :
      RealEuclidean (n + 1))) = (z : RealEuclidean (n + 1))
    rw [charbonnelGraphParam, hright]
    exact realEuclideanAppend_takeLeft_takeRight
      (z : RealEuclidean (n + 1))
  continuous_toFun := by
    exact Continuous.subtype_mk
      (continuousOn_charbonnelGraphParam hf).domRestrict (fun _ ↦ by
        simp [charbonnelRestrictedGraph, charbonnelGraphParam,
          realEuclideanSingletonVector])
  continuous_invFun := by
    exact Continuous.subtype_mk
      ((realEuclideanTakeLeftContinuousLinearMap n 1).continuous.comp
        continuous_subtype_val) (fun z ↦ by
          exact z.2.1)

@[simp]
theorem charbonnelRestrictedGraphHomeomorph_apply
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f : RealEuclidean n → ℝ} (hf : ContinuousOn f base)
    (x : base) :
    (charbonnelRestrictedGraphHomeomorph hf x : RealEuclidean (n + 1)) =
      charbonnelGraphParam f x :=
  rfl

@[simp]
theorem charbonnelRestrictedGraphHomeomorph_symm_apply
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f : RealEuclidean n → ℝ} (hf : ContinuousOn f base)
    (z : charbonnelRestrictedGraph base f) :
    ((charbonnelRestrictedGraphHomeomorph hf).symm z :
        RealEuclidean n) =
      realEuclideanTakeLeft (n := n) (m := 1)
        (z : RealEuclidean (n + 1)) :=
  rfl

/-! ## Pulling a relative target into the base -/

/-- On a target contained in a restricted graph, the preimage under the graph
parameterization is exactly its existential projection.  This is the
lossless set identity behind the graph-cell induction. -/
theorem charbonnelRestrictedGraphHomeomorph_preimage
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f : RealEuclidean n → ℝ} (hf : ContinuousOn f base)
    {A : Set (RealEuclidean (n + 1))}
    (hA : A ⊆ charbonnelRestrictedGraph base f) :
    charbonnelRestrictedGraphHomeomorph hf ⁻¹'
        (Subtype.val ⁻¹' A :
          Set (charbonnelRestrictedGraph base f)) =
      (Subtype.val ⁻¹' realEuclideanExistentialProjection A :
        Set base) := by
  ext x
  constructor
  · intro hx
    change charbonnelGraphParam f x ∈ A at hx
    change ∃ y : RealEuclidean 1,
      realEuclideanAppend (x : RealEuclidean n) y ∈ A
    exact ⟨realEuclideanSingletonVector (f x), by
      simpa [charbonnelGraphParam] using hx⟩
  · rintro ⟨y, hy⟩
    change charbonnelGraphParam f x ∈ A
    have hyGraph := hA hy
    have hyRight : y = realEuclideanSingletonVector (f x) := by
      funext j
      rw [Fin.eq_zero j]
      simpa [realEuclideanSingletonVector] using hyGraph.2
    simpa [charbonnelGraphParam, hyRight] using hy

/-- Relative closedness descends through the intrinsic graph coordinate
projection. -/
theorem isClosed_graphProjection_in_base
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f : RealEuclidean n → ℝ} (hf : ContinuousOn f base)
    {A : Set (RealEuclidean (n + 1))}
    (hA : A ⊆ charbonnelRestrictedGraph base f)
    (hclosed : IsClosed
      (Subtype.val ⁻¹' A : Set (charbonnelRestrictedGraph base f))) :
    IsClosed
      (Subtype.val ⁻¹' realEuclideanExistentialProjection A :
        Set base) := by
  rw [← charbonnelRestrictedGraphHomeomorph_preimage hf hA]
  exact hclosed.preimage (charbonnelRestrictedGraphHomeomorph hf).continuous

/-- Charbonnel membership of the lower-dimensional graph target follows from
the genuine projection constructor. -/
theorem graphProjection_mem_charbonnelClosure
    {S : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    {A : Set (RealEuclidean (n + 1))}
    (hA : A ∈ charbonnelClosure S (n + 1)) :
    realEuclideanExistentialProjection A ∈ charbonnelClosure S n :=
  charbonnelClosure_projection hn hA

/-! ## The lower-dimensional relatively closed band step -/

/-- Lower-dimensional `(I)` and `(II)` give the relative cover needed after
passing to intrinsic coordinates.  The closed set to which `(I)` is applied
is `closure A`.  Relative closedness identifies its part in the open band
with `A`; one common refinement with the band cell and its cylinder then
restricts the resulting global cover to the required domain.

This formulation is useful for the non-open branch because it does not ask
the intrinsic pullback of `A` to have empty interior or finite fibres. -/
theorem exists_relativeCellCover_of_relativelyClosedBand
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (hII : CharbonnelFiniteCellFamilyCommonRefinementAt
      (charbonnelClosure S) (n + 1))
    (base : CharbonnelCell (charbonnelClosure S) n)
    (f g : RealEuclidean n → ℝ)
    (hf : ContinuousOn f base.carrier)
    (hg : ContinuousOn g base.carrier)
    (hfg : ∀ x ∈ base.carrier, f x < g x)
    (hfGraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    (hgGraph : charbonnelRestrictedGraph base.carrier g ∈
      charbonnelClosure S (n + 1))
    {A : Set (RealEuclidean (n + 1))}
    (hAmem : A ∈ charbonnelClosure S (n + 1))
    (hAsub : A ⊆ charbonnelOpenBand base.carrier f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A :
        Set (charbonnelOpenBand base.carrier f g))) :
    Nonempty
      (CharbonnelFiniteCompatibleRelativeCellCover
        (charbonnelClosure S)
        (charbonnelCylinderCell base.carrier) A) := by
  classical
  let bandCell : CharbonnelCell (charbonnelClosure S) (n + 1) :=
    { carrier := charbonnelOpenBand base.carrier f g
      shape := .band hn base.shape f g hf hg hfg
      carrier_mem :=
        charbonnelOpenBand_mem_charbonnelClosure_of_graph_mem
          hC hfGraph hgGraph }
  let cylinderCell : CharbonnelCell (charbonnelClosure S) (n + 1) :=
    { carrier := charbonnelCylinderCell base.carrier
      shape := .cylinder hn base.shape
      carrier_mem :=
        charbonnelCylinderCell_mem_charbonnelClosure
          hC hn base.carrier_mem }
  obtain ⟨closedCover⟩ := hI (by omega : 0 < n + 1)
    isClosed_closure (charbonnelClosure_topologicalClosure hAmem)
  let input : (Fin closedCover.count ⊕ Fin 2) →
      CharbonnelCell (charbonnelClosure S) (n + 1)
    | Sum.inl i => closedCover.cell i
    | Sum.inr i => if i = 0 then bandCell else cylinderCell
  obtain ⟨fine⟩ := hII input
  have hrelative :
      closure A ∩ charbonnelOpenBand base.carrier f g ⊆ A := by
    have hclosed := isClosed_preimage_val.mp hAclosed
    intro z hz
    apply hclosed
    refine ⟨hz.2, ?_⟩
    have hinter : charbonnelOpenBand base.carrier f g ∩ A = A :=
      inter_eq_right.mpr hAsub
    simpa only [hinter] using hz.1
  let Index := {i : Fin fine.count //
    (fine.cell i).carrier ⊆ charbonnelCylinderCell base.carrier}
  refine ⟨
    { Index := Index
      indexFinite := inferInstance
      cell := fun i ↦ fine.cell i.1
      contained := fun i ↦ i.2
      covers := ?_
      compatible := ?_ }⟩
  · intro z hz
    obtain ⟨i, hi⟩ := fine.covers z
    have hdomain := fine.compatible i (Sum.inr (1 : Fin 2))
    change (fine.cell i).carrier ⊆
        charbonnelCylinderCell base.carrier ∨
      Disjoint (fine.cell i).carrier
        (charbonnelCylinderCell base.carrier) at hdomain
    rcases hdomain with hsubset | hdisjoint
    · exact ⟨⟨i, hsubset⟩, hi⟩
    · exact False.elim (Set.disjoint_left.mp hdisjoint hi hz)
  · intro i
    have hclosure : (fine.cell i.1).carrier ⊆ closure A ∨
        Disjoint (fine.cell i.1).carrier (closure A) :=
      compatible_target_of_compatible_cover_cells closedCover
        (fun j ↦ fine.compatible i.1 (Sum.inl j))
    have hband := fine.compatible i.1 (Sum.inr (0 : Fin 2))
    change (fine.cell i.1).carrier ⊆
        charbonnelOpenBand base.carrier f g ∨
      Disjoint (fine.cell i.1).carrier
        (charbonnelOpenBand base.carrier f g) at hband
    rcases hclosure with hclosure | hclosure <;>
      rcases hband with hband | hband
    · left
      intro z hz
      exact hrelative ⟨hclosure hz, hband hz⟩
    · right
      exact hband.mono_right hAsub
    · right
      exact hclosure.mono_right subset_closure
    · right
      exact hclosure.mono_right subset_closure

/-! ## The ordinary relative cover required by the non-open branch -/

/-- A relatively closed target in an ambient band admits the relative cover
needed over the cylinder of every recursive base cell.  First refine the
given base cell simultaneously with the ambient base.  A refined piece
disjoint from the ambient base has a cylinder disjoint from the target.  On a
piece contained in the ambient base, restrict the two boundary graphs and
apply `exists_relativeCellCover_of_relativelyClosedBand` to the part of the
target over that piece.  Flattening these finitely many covers gives the
ordinary relative cover used by `hnonopen`.

The construction does not use the openness of the input cell; in particular
it supplies the stronger statement quantified over all recursive cells. -/
theorem exists_relativeCellCover_cylinder_of_relativelyClosedBand
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFiniteCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    (ambient : CharbonnelCell (charbonnelClosure S) p)
    (f g : RealEuclidean p → ℝ)
    (hf : ContinuousOn f ambient.carrier)
    (hg : ContinuousOn g ambient.carrier)
    (hfg : ∀ x ∈ ambient.carrier, f x < g x)
    (hfGraph : charbonnelRestrictedGraph ambient.carrier f ∈
      charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph ambient.carrier g ∈
      charbonnelClosure S (p + 1))
    {A : Set (RealEuclidean (p + 1))}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hAsub : A ⊆ charbonnelOpenBand ambient.carrier f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A :
        Set (charbonnelOpenBand ambient.carrier f g)))
    (cell : CharbonnelCell (charbonnelClosure S) p) :
    Nonempty
      (CharbonnelFiniteCompatibleRelativeCellCover
        (charbonnelClosure S)
        (charbonnelCylinderCell cell.carrier) A) := by
  classical
  let input : Fin 2 → CharbonnelCell (charbonnelClosure S) p :=
    fun i ↦ if i = 0 then cell else ambient
  obtain ⟨fine⟩ := hII input
  let Piece := {i : Fin fine.count //
    (fine.cell i).carrier ⊆ cell.carrier}
  have pieceCover (i : Piece) :
      Nonempty
        (CharbonnelFiniteCompatibleRelativeCellCover
          (charbonnelClosure S)
          (charbonnelCylinderCell (fine.cell i.1).carrier) A) := by
    have hambient := fine.compatible i.1 (1 : Fin 2)
    change (fine.cell i.1).carrier ⊆ ambient.carrier ∨
      Disjoint (fine.cell i.1).carrier ambient.carrier at hambient
    rcases hambient with hinside | houtside
    · have hfSmall : ContinuousOn f (fine.cell i.1).carrier :=
        hf.mono hinside
      have hgSmall : ContinuousOn g (fine.cell i.1).carrier :=
        hg.mono hinside
      have hfgSmall : ∀ x ∈ (fine.cell i.1).carrier, f x < g x :=
        fun x hx ↦ hfg x (hinside hx)
      have hfGraphSmall :
          charbonnelRestrictedGraph (fine.cell i.1).carrier f ∈
            charbonnelClosure S (p + 1) :=
        charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
          hC hp hinside (fine.cell i.1).carrier_mem hfGraph
      have hgGraphSmall :
          charbonnelRestrictedGraph (fine.cell i.1).carrier g ∈
            charbonnelClosure S (p + 1) :=
        charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
          hC hp hinside (fine.cell i.1).carrier_mem hgGraph
      let localBand : Set (RealEuclidean (p + 1)) :=
        charbonnelOpenBand (fine.cell i.1).carrier f g
      let localTarget : Set (RealEuclidean (p + 1)) := A ∩ localBand
      have hlocalBandMem : localBand ∈ charbonnelClosure S (p + 1) :=
        charbonnelOpenBand_mem_charbonnelClosure_of_graph_mem
          hC hfGraphSmall hgGraphSmall
      have hlocalTargetMem : localTarget ∈
          charbonnelClosure S (p + 1) :=
        hC.ws1_inter (by omega) hAmem hlocalBandMem
      have hlocalTargetSub : localTarget ⊆ localBand := inter_subset_right
      have hlocalBandSub : localBand ⊆
          charbonnelOpenBand ambient.carrier f g := by
        intro z hz
        exact ⟨hinside hz.1, hz.2⟩
      let inclusion : localBand →
          charbonnelOpenBand ambient.carrier f g :=
        fun z ↦ ⟨z.1, hlocalBandSub z.2⟩
      have hinclusion : Continuous inclusion :=
        Continuous.subtype_mk continuous_subtype_val
          (fun z ↦ hlocalBandSub z.2)
      have hlocalTargetClosed : IsClosed
          (Subtype.val ⁻¹' localTarget : Set localBand) := by
        have heq : (Subtype.val ⁻¹' localTarget : Set localBand) =
            inclusion ⁻¹'
              (Subtype.val ⁻¹' A : Set
                (charbonnelOpenBand ambient.carrier f g)) := by
          ext z
          simp [localTarget, localBand, inclusion]
        rw [heq]
        exact hAclosed.preimage hinclusion
      obtain ⟨localCover⟩ :=
        exists_relativeCellCover_of_relativelyClosedBand
        hC hI hp (hII (n := p + 1)) (fine.cell i.1) f g
          hfSmall hgSmall hfgSmall hfGraphSmall hgGraphSmall
          hlocalTargetMem hlocalTargetSub hlocalTargetClosed
      refine ⟨
        { Index := localCover.Index
          indexFinite := localCover.indexFinite
          cell := localCover.cell
          contained := localCover.contained
          covers := localCover.covers
          compatible := ?_ }⟩
      intro j
      rcases localCover.compatible j with hj | hj
      · exact Or.inl (hj.trans inter_subset_left)
      · right
        rw [Set.disjoint_left]
        intro z hz hzA
        apply Set.disjoint_left.mp hj hz
        refine ⟨hzA, ?_⟩
        have hzDomain := localCover.contained j hz
        have hzBand := hAsub hzA
        exact ⟨hzDomain, hzBand.2⟩
    · let cylinder : CharbonnelCell (charbonnelClosure S) (p + 1) :=
        { carrier := charbonnelCylinderCell (fine.cell i.1).carrier
          shape := .cylinder hp (fine.cell i.1).shape
          carrier_mem :=
            charbonnelCylinderCell_mem_charbonnelClosure hC hp
              (fine.cell i.1).carrier_mem }
      refine ⟨
        { Index := PUnit
          indexFinite := inferInstance
          cell := fun _ ↦ cylinder
          contained := fun _ ↦ Subset.rfl
          covers := fun z hz ↦ ⟨PUnit.unit, hz⟩
          compatible := fun _ ↦ Or.inr ?_ }⟩
      rw [Set.disjoint_left]
      intro z hz hzA
      exact Set.disjoint_left.mp houtside hz
        (hAsub hzA).1
  let piecewiseCover (i : Piece) := Classical.choice (pieceCover i)
  letI (i : Piece) : Fintype (piecewiseCover i).Index :=
    @Fintype.ofFinite (piecewiseCover i).Index
      (piecewiseCover i).indexFinite
  refine ⟨
    { Index := Σ i : Piece, (piecewiseCover i).Index
      indexFinite := inferInstance
      cell := fun q ↦ (piecewiseCover q.1).cell q.2
      contained := ?_
      covers := ?_
      compatible := fun q ↦ (piecewiseCover q.1).compatible q.2 }⟩
  · intro q z hz
    have hz' := (piecewiseCover q.1).contained q.2 hz
    exact q.1.2 hz'
  · intro z hz
    obtain ⟨j, hj⟩ := fine.covers (realEuclideanTakeLeft z)
    have hcell := fine.compatible j (0 : Fin 2)
    change (fine.cell j).carrier ⊆ cell.carrier ∨
      Disjoint (fine.cell j).carrier cell.carrier at hcell
    rcases hcell with hsubset | hdisjoint
    · let j' : Piece := ⟨j, hsubset⟩
      obtain ⟨k, hk⟩ := (piecewiseCover j').covers z hj
      exact ⟨⟨j', k⟩, hk⟩
    · exact False.elim
        (Set.disjoint_left.mp hdisjoint hj hz)

/-- The preceding construction has exactly the type of the `hnonopen`
premise in `WilkieSection4SourceAssembly`.  The proof is uniform in the input
cell, so the fact that the cell is non-open is not needed once the ambient
band is known to be ordered. -/
theorem wilkieSection4_hnonopen_of_relativelyClosedBand
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFiniteCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)}
    (ambient : CharbonnelCell (charbonnelClosure S) p)
    (hambient : ambient.carrier = C)
    {f g : RealEuclidean p → ℝ}
    (hf : ContinuousOn f C) (hg : ContinuousOn g C)
    (hfg : ∀ x ∈ C, f x < g x)
    (hfGraph : charbonnelRestrictedGraph C f ∈
      charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph C g ∈
      charbonnelClosure S (p + 1))
    {A : Set (RealEuclidean (p + 1))}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hAsub : A ⊆ charbonnelOpenBand C f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A : Set (charbonnelOpenBand C f g))) :
    ∀ cell : CharbonnelCell (charbonnelClosure S) p,
      ¬ IsOpen cell.carrier →
      Nonempty
        (CharbonnelFiniteCompatibleRelativeCellCover
          (charbonnelClosure S)
          (charbonnelCylinderCell cell.carrier) A) := by
  subst C
  intro cell _
  exact exists_relativeCellCover_cylinder_of_relativelyClosedBand
    hC hI hII hp ambient f g hf hg hfg hfGraph hgGraph
      hAmem hAsub hAclosed cell

/-- Section 4 with its former non-open-cell premise discharged by the
relative-band construction. -/
theorem exists_charbonnelFiniteCompatibleCellCover_of_wilkieSection4_orderedBand
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFiniteCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f g : RealEuclidean p → ℝ}
    (baseCell : CharbonnelCell (charbonnelClosure S) p)
    (hbase : baseCell.carrier = C)
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hAempty : interior A = ∅)
    (hAsub : A ⊆ charbonnelOpenBand C f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A : Set (charbonnelOpenBand C f g)))
    (hf : ContinuousOn f C) (hg : ContinuousOn g C)
    (hfg : ∀ x ∈ C, f x < g x)
    (hfGraph : charbonnelRestrictedGraph C f ∈
      charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph C g ∈
      charbonnelClosure S (p + 1)) :
    Nonempty (CharbonnelFiniteCompatibleCellCover
      (charbonnelClosure S) A) := by
  apply exists_charbonnelFiniteCompatibleCellCover_of_wilkieSection4
    hC h21 h22 hI hII hp baseCell hbase hAmem hAempty hAsub hAclosed
      hf hg hfGraph hgGraph
  exact wilkieSection4_hnonopen_of_relativelyClosedBand
    hC.toPositiveArityWeakSetStructure hI hII hp baseCell hbase hf hg hfg
      hfGraph hgGraph hAmem hAsub hAclosed

/-! ## Lifting lower-dimensional compatible covers -/

/-- Restrict a retained graph to one lower-dimensional recursive cell. -/
def CharbonnelCell.liftThroughGraph
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {base : CharbonnelCell (charbonnelClosure S) n}
    (small : CharbonnelCell (charbonnelClosure S) n)
    (hsmall : small.carrier ⊆ base.carrier)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1)) :
    CharbonnelCell (charbonnelClosure S) (n + 1) :=
  { carrier := charbonnelRestrictedGraph small.carrier f
    shape := .graph hn small.shape f (hf.mono hsmall)
    carrier_mem :=
      charbonnelRestrictedGraph_mem_charbonnelClosure_of_enriched_subset
        hC hn hsmall small.carrier_mem hgraph }

@[simp]
theorem CharbonnelCell.liftThroughGraph_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {base : CharbonnelCell (charbonnelClosure S) n}
    (small : CharbonnelCell (charbonnelClosure S) n)
    (hsmall : small.carrier ⊆ base.carrier)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1)) :
    (CharbonnelCell.liftThroughGraph hC hn small hsmall f hf hgraph).carrier =
      charbonnelRestrictedGraph small.carrier f :=
  rfl

/-- A compatible relative cover of the projected target lifts through the
retained graph to a compatible relative cover of the original target. -/
def CharbonnelFiniteCompatibleRelativeCellCover.liftThroughGraph
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelCell (charbonnelClosure S) n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    {A : Set (RealEuclidean (n + 1))}
    (hA : A ⊆ charbonnelRestrictedGraph base.carrier f)
    (cover : CharbonnelFiniteCompatibleRelativeCellCover
      (charbonnelClosure S) base.carrier
      (realEuclideanExistentialProjection A)) :
    CharbonnelFiniteCompatibleRelativeCellCover
      (charbonnelClosure S)
      (charbonnelRestrictedGraph base.carrier f) A where
  Index := cover.Index
  indexFinite := cover.indexFinite
  cell i := CharbonnelCell.liftThroughGraph hC hn (cover.cell i)
    (cover.contained i) f hf hgraph
  contained := by
    intro i z hz
    exact ⟨cover.contained i hz.1, hz.2⟩
  covers := by
    intro z hz
    obtain ⟨i, hi⟩ := cover.covers (realEuclideanTakeLeft z) hz.1
    exact ⟨i, hi, hz.2⟩
  compatible := by
    intro i
    rcases cover.compatible i with hinside | hdisjoint
    · left
      intro z hz
      obtain ⟨y, hy⟩ := hinside hz.1
      have hyGraph := hA hy
      have hright : realEuclideanTakeRight z = y := by
        funext j
        rw [Fin.eq_zero j]
        have hzValue :
            f (realEuclideanTakeLeft z) = realEuclideanTakeRight z 0 := hz.2.symm
        have hyValue :
            f (realEuclideanTakeLeft z) = y 0 := by
          simpa using hyGraph.2.symm
        linarith
      have hzy : z = realEuclideanAppend (realEuclideanTakeLeft z) y := by
        rw [← hright]
        exact (realEuclideanAppend_takeLeft_takeRight z).symm
      rwa [hzy]
    · right
      rw [Set.disjoint_left]
      intro z hz hzA
      exact Set.disjoint_left.mp hdisjoint hz.1
        ⟨realEuclideanTakeRight z, by
          rwa [realEuclideanAppend_takeLeft_takeRight]⟩

/-! ## Complete graph branch of the induction -/

/-- The complete lossless datum for Wilkie's graph-cell case.  The target one
dimension lower is a Charbonnel member and is relatively closed in the
recorded base; any compatible relative cover of it lifts to the original
graph target.

This is deliberately stated as a conjunction of the usable facts needed by
the recursive graph branch. -/
theorem wilkieSection4_graphInductionDatum
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (base : CharbonnelCell (charbonnelClosure S) n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    {A : Set (RealEuclidean (n + 1))}
    (hAmem : A ∈ charbonnelClosure S (n + 1))
    (hA : A ⊆ charbonnelRestrictedGraph base.carrier f)
    (hclosed : IsClosed
      (Subtype.val ⁻¹' A :
        Set (charbonnelRestrictedGraph base.carrier f))) :
    realEuclideanExistentialProjection A ∈ charbonnelClosure S n ∧
      IsClosed
        (Subtype.val ⁻¹' realEuclideanExistentialProjection A :
          Set base.carrier) ∧
      ∀ _cover : CharbonnelFiniteCompatibleRelativeCellCover
          (charbonnelClosure S) base.carrier
          (realEuclideanExistentialProjection A),
        Nonempty
          (CharbonnelFiniteCompatibleRelativeCellCover
            (charbonnelClosure S)
            (charbonnelRestrictedGraph base.carrier f) A) := by
  refine ⟨graphProjection_mem_charbonnelClosure hn hAmem,
    isClosed_graphProjection_in_base hf hA hclosed, ?_⟩
  intro cover
  exact ⟨cover.liftThroughGraph hC hn base f hf hgraph hA⟩

end AbelFormalization
