import AbelFormalization.WilkieSection4LociRefinement
import AbelFormalization.WilkieSection4BadLocusExclusion
import AbelFormalization.WilkieSection4MixedCellAssembly

/-!
# Wilkie Section 4: source-shaped open-band assembly

This module joins the finite simultaneous loci refinement, Theorem 2.2's
automatic exclusion of the collision and endpoint traces, and the mixed
open/lower-dimensional cylinder assembly.  The only local cell input left is
the recursive cover over non-open base cells, exactly the induction branch in
Wilkie's proof.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- On a nonempty open set compatible with the cutoff locus, empty interior
of `closure A_N` forces every fibre to have cardinality strictly below `N`.
This is the finite-fibre input needed before applying Theorem 2.2 to the three
bad loci. -/
theorem maxwellScalarFiber_encard_lt_cutoff_of_open_compatible_locus
    {p N : ℕ} {C B : Set (RealEuclidean p)}
    {A : MaxwellRelation p 1}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty) (hBC : B ⊆ C)
    (hNempty : interior
      (closure (wilkieSection4FiberCardinalityLocus C A N)) = ∅)
    (hcompatible :
      B ⊆ closure (wilkieSection4FiberCardinalityLocus C A N) ∨
        Disjoint B
          (closure (wilkieSection4FiberCardinalityLocus C A N))) :
    ∀ x ∈ B, (maxwellScalarFiber A x).encard < (N : ℕ∞) := by
  have hdisjoint : Disjoint B
      (closure (wilkieSection4FiberCardinalityLocus C A N)) := by
    rcases hcompatible with hsubset | hdisjoint
    · have hBInterior : B ⊆ interior
          (closure (wilkieSection4FiberCardinalityLocus C A N)) :=
        interior_maximal hsubset hBopen
      obtain ⟨x, hxB⟩ := hBnonempty
      have hxEmpty : x ∈ (∅ : Set (RealEuclidean p)) := by
        rw [← hNempty]
        exact hBInterior hxB
      exact hxEmpty.elim
    · exact hdisjoint
  intro x hxB
  have hxNot : x ∉ wilkieSection4FiberCardinalityLocus C A N := by
    intro hx
    exact Set.disjoint_left.mp hdisjoint hxB (subset_closure hx)
  have hnotLe : ¬ (N : ℕ∞) ≤ (maxwellScalarFiber A x).encard := by
    intro hle
    exact hxNot
      ((mem_wilkieSection4FiberCardinalityLocus_iff_encard C A x).mpr
        ⟨hBC hxB, hle⟩)
  exact lt_of_not_ge hnotLe

/-- Once a base cover has been simultaneously refined against all Section 4
loci, Theorem 2.2 forces its nonempty open cells to avoid the three bad loci,
and the full mixed cylinder construction follows. -/
noncomputable def
    CharbonnelFiniteBaseAndTargetsCompatibleCellCover.section4MixedCellCover
    {S : EuclideanSetFamily}
    (hweak : PositiveArityWeakSetStructure (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f g : RealEuclidean p → ℝ}
    (cover : CharbonnelFiniteBaseAndTargetsCompatibleCellCover
      (charbonnelClosure S) C (wilkieSection4LociTarget C A f g :
        WilkieSection4LociIndex N → Set (RealEuclidean p)))
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hAsub : A ⊆ charbonnelOpenBand C f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A : Set (charbonnelOpenBand C f g)))
    (hf : ContinuousOn f C) (hg : ContinuousOn g C)
    (hfGraph : charbonnelRestrictedGraph C f ∈
      charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph C g ∈
      charbonnelClosure S (p + 1))
    (hNempty : interior
      (closure (wilkieSection4FiberCardinalityLocus C A N)) = ∅)
    (hnonopen : ∀ i,
      ¬ IsOpen (cover.cell i).carrier →
      CharbonnelFiniteCompatibleRelativeCellCover
        (charbonnelClosure S)
        (charbonnelCylinderCell (cover.cell i).carrier) A) :
    CharbonnelFiniteCompatibleCellCover (charbonnelClosure S) A := by
  let baseCover := cover.baseCover
  have hbad : ∀ i : Fin cover.count,
      (cover.cell i).carrier ⊆ C →
      IsOpen (cover.cell i).carrier →
      (cover.cell i).carrier.Nonempty →
      Disjoint (cover.cell i).carrier
          (wilkieSection4CollisionLocus C A) ∧
        Disjoint (cover.cell i).carrier
          (wilkieSection4LowerEndpointLocus C A f) ∧
        Disjoint (cover.cell i).carrier
          (wilkieSection4UpperEndpointLocus C A g) := by
    intro i hiC hiOpen hiNonempty
    have hcard : ∀ x ∈ (cover.cell i).carrier,
        (maxwellScalarFiber A x).encard < (N : ℕ∞) :=
      maxwellScalarFiber_encard_lt_cutoff_of_open_compatible_locus
        hiOpen hiNonempty hiC hNempty
          (cover.section4_cardinality_compatible i le_rfl)
    exact
      disjoint_wilkieSection4_badLoci_of_uniform_cardinality_of_compatible
        hweak h22 hp hiOpen hiNonempty (cover.cell i).carrier_mem hiC
          hAmem hfGraph hgGraph hcard
          (cover.section4_collision_compatible i)
          (cover.section4_lowerEndpoint_compatible i)
          (cover.section4_upperEndpoint_compatible i)
  exact baseCover.section4MixedCellCover_of_baseRefinement
    hweak hp hN hAmem hAsub hAclosed hf hg hNempty
    (fun i _hiC _hiOpen _hiNonempty j hj ↦
      cover.section4_cardinality_compatible i hj)
    (fun i hiC hiOpen hiNonempty ↦
      (hbad i hiC hiOpen hiNonempty).1)
    (fun i hiC hiOpen hiNonempty ↦
      (hbad i hiC hiOpen hiNonempty).2.1)
    (fun i hiC hiOpen hiNonempty ↦
      (hbad i hiC hiOpen hiNonempty).2.2)
    hnonopen

/-- Complete full-dimensional Section 4 branch over an enriched ambient base
cell.  Individual compatible covers and finite common refinement build the
simultaneous loci cover; only the non-open-cell recursive branch is supplied. -/
theorem exists_charbonnelFiniteCompatibleCellCover_of_wilkieSection4_cutoff
    {S : EuclideanSetFamily}
    (hweak : PositiveArityWeakSetStructure (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFiniteCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {p N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f g : RealEuclidean p → ℝ}
    (baseCell : CharbonnelCell (charbonnelClosure S) p)
    (hbase : baseCell.carrier = C)
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hAsub : A ⊆ charbonnelOpenBand C f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A : Set (charbonnelOpenBand C f g)))
    (hf : ContinuousOn f C) (hg : ContinuousOn g C)
    (hfGraph : charbonnelRestrictedGraph C f ∈
      charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph C g ∈
      charbonnelClosure S (p + 1))
    (hNempty : interior
      (closure (wilkieSection4FiberCardinalityLocus C A N)) = ∅)
    (hnonopen : ∀ cell : CharbonnelCell (charbonnelClosure S) p,
      ¬ IsOpen cell.carrier →
      Nonempty (CharbonnelFiniteCompatibleRelativeCellCover
        (charbonnelClosure S) (charbonnelCylinderCell cell.carrier) A)) :
    Nonempty (CharbonnelFiniteCompatibleCellCover
      (charbonnelClosure S) A) := by
  obtain ⟨cover⟩ := exists_wilkieSection4_baseAndLociCompatibleCellCover
    hweak hI hII hp baseCell hbase hAmem hfGraph hgGraph
  refine ⟨cover.section4MixedCellCover hweak h22 hp hN hAmem hAsub
    hAclosed hf hg hfGraph hgGraph hNempty ?_⟩
  intro i hi
  exact Classical.choice (hnonopen (cover.cell i) hi)

/-- Source form with the cutoff `N` derived internally from WS5/Fubini and
Theorem 2.1. -/
theorem exists_charbonnelFiniteCompatibleCellCover_of_wilkieSection4
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
    (hfGraph : charbonnelRestrictedGraph C f ∈
      charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph C g ∈
      charbonnelClosure S (p + 1))
    (hnonopen : ∀ cell : CharbonnelCell (charbonnelClosure S) p,
      ¬ IsOpen cell.carrier →
      Nonempty (CharbonnelFiniteCompatibleRelativeCellCover
        (charbonnelClosure S) (charbonnelCylinderCell cell.carrier) A)) :
    Nonempty (CharbonnelFiniteCompatibleCellCover
      (charbonnelClosure S) A) := by
  have hCmem : C ∈ charbonnelClosure S p := by
    simpa [← hbase] using baseCell.carrier_mem
  obtain ⟨N, hN, hNempty⟩ :=
    exists_wilkieSection4_cardinalityCutoff hC h21 hp hCmem hAmem hAempty
  exact exists_charbonnelFiniteCompatibleCellCover_of_wilkieSection4_cutoff
    hC.toPositiveArityWeakSetStructure h22 hI hII hp hN baseCell hbase
      hAmem hAsub hAclosed hf hg hfGraph hgGraph hNempty hnonopen

end AbelFormalization
