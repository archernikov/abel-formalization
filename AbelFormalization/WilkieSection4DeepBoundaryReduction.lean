import AbelFormalization.WilkieSection4DeepSimultaneousInduction
import AbelFormalization.CharbonnelCellBoundaryCompatibility

/-!
# Boundary reduction for retained relative decompositions

Wilkie applies the finite-fibre argument to a closed empty-interior carrier
containing the frontier of the closed target.  Connectedness of every cell
then transfers compatibility from the carrier intersection to the target.
This file records that reduction for the retained deep-cell invariant.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The empty-interior form of retained relative closed decomposition at one
positive ambient dimension. -/
def CharbonnelDeepRelativeEmptyInteriorDecompositionAt
    (S : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ (D : CharbonnelDeepEnrichedCell S (n + 1))
    {A : Set (RealEuclidean (n + 1))},
    A ⊆ D.carrier →
    A ∈ charbonnelClosure S (n + 1) →
    IsClosed (Subtype.val ⁻¹' A : Set D.carrier) →
    interior A = ∅ →
    Nonempty
      (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D.carrier (fun _ : Unit ↦ A))

/-- The empty-interior assertion on the bounded domains used in Wilkie's
Section 4 induction. -/
def CharbonnelBoundedDeepRelativeEmptyInteriorDecompositionAt
    (S : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ (D : CharbonnelDeepEnrichedCell S (n + 1)),
    Bornology.IsBounded D.carrier →
    ∀ {A : Set (RealEuclidean (n + 1))},
      A ⊆ D.carrier →
      A ∈ charbonnelClosure S (n + 1) →
      IsClosed (Subtype.val ⁻¹' A : Set D.carrier) →
      interior A = ∅ →
      Nonempty
        (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
          S D.carrier (fun _ : Unit ↦ A))

/-- A closed empty-interior boundary carrier upgrades the empty-interior
relative decomposition statement to the full relatively closed statement.
The target is first replaced by its ambient closure; relative closedness says
that this closure has the same trace on the domain cell. -/
theorem charbonnelDeepRelativeClosedDecompositionAt_of_emptyInterior
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ}
    (hboundary : ∀ {K : Set (RealEuclidean (n + 1))},
      IsClosed K → K ∈ charbonnelClosure S (n + 1) →
      ∃ B : Set (RealEuclidean (n + 1)),
        IsClosed B ∧ B ∈ charbonnelClosure S (n + 1) ∧
          interior B = ∅ ∧ frontier K ⊆ B)
    (hempty : CharbonnelDeepRelativeEmptyInteriorDecompositionAt S n) :
    CharbonnelDeepRelativeClosedDecompositionAt S n := by
  intro D A hAD hAmem hAclosed
  let K : Set (RealEuclidean (n + 1)) := closure A
  have hKclosed : IsClosed K := isClosed_closure
  have hKmem : K ∈ charbonnelClosure S (n + 1) := by
    exact charbonnelClosure_topologicalClosure hAmem
  obtain ⟨B, hBclosed, hBmem, hBempty, hfrontier⟩ :=
    hboundary hKclosed hKmem
  let R : Set (RealEuclidean (n + 1)) :=
    (K ∩ B) ∩ D.carrier
  have hRsub : R ⊆ D.carrier := inter_subset_right
  have hRmem : R ∈ charbonnelClosure S (n + 1) := by
    apply hC.ws1_inter (by omega)
    · exact hC.ws1_inter (by omega) hKmem hBmem
    · simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using
        (D.toCell hC).carrier_mem
  have hRclosed : IsClosed
      (Subtype.val ⁻¹' R : Set D.carrier) := by
    have hKBclosed : IsClosed (K ∩ B) := hKclosed.inter hBclosed
    have heq : (Subtype.val ⁻¹' R : Set D.carrier) =
        Subtype.val ⁻¹' (K ∩ B) := by
      ext x
      simp only [R, Set.mem_preimage, Set.mem_inter_iff,
        Subtype.coe_prop, and_true]
    rw [heq]
    exact hKBclosed.preimage continuous_subtype_val
  have hRempty : interior R = ∅ :=
    interior_eq_empty_of_subset
      (fun _ hz ↦ hz.1.2) hBempty
  obtain ⟨cover⟩ := hempty D hRsub hRmem hRclosed hRempty
  have hrelative : K ∩ D.carrier ⊆ A := by
    have hclosed := isClosed_preimage_val.mp hAclosed
    intro z hz
    apply hclosed
    refine ⟨hz.2, ?_⟩
    have hinter : D.carrier ∩ A = A := inter_eq_right.mpr hAD
    simpa only [K, hinter] using hz.1
  refine ⟨
    { Index := cover.Index
      indexFinite := cover.indexFinite
      cell := cover.cell
      contained := cover.contained
      covers := cover.covers
      compatible := ?_
      cells_eq_or_disjoint := cover.cells_eq_or_disjoint
      hereditary_projection_coherent :=
        cover.hereditary_projection_coherent }⟩
  intro i _
  have hKBcompat :
      (cover.cell i).carrier ⊆ K ∩ B ∨
        Disjoint (cover.cell i).carrier (K ∩ B) := by
    rcases cover.compatible i () with hinside | hdisjoint
    · left
      intro z hz
      exact (hinside hz).1
    · right
      rw [Set.disjoint_left]
      intro z hz hKB
      exact Set.disjoint_left.mp hdisjoint hz
        ⟨hKB, cover.contained i hz⟩
  have hKcompat :
      (cover.cell i).carrier ⊆ K ∨
        Disjoint (cover.cell i).carrier K :=
    connected_cell_compatible_of_boundary_intersection
      ((cover.cell i).toCell hC).shape.isPreconnected
      hKclosed hfrontier hKBcompat
  rcases hKcompat with hinside | hdisjoint
  · left
    intro z hz
    exact hrelative ⟨hinside hz, cover.contained i hz⟩
  · right
    exact hdisjoint.mono_right subset_closure

/-- Bounded-domain boundary reduction used by the source-faithful induction. -/
theorem charbonnelBoundedDeepRelativeClosedDecompositionAt_of_emptyInterior
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ}
    (hboundary : ∀ {K : Set (RealEuclidean (n + 1))},
      IsClosed K → K ∈ charbonnelClosure S (n + 1) →
      ∃ B : Set (RealEuclidean (n + 1)),
        IsClosed B ∧ B ∈ charbonnelClosure S (n + 1) ∧
          interior B = ∅ ∧ frontier K ⊆ B)
    (hempty : CharbonnelBoundedDeepRelativeEmptyInteriorDecompositionAt S n) :
    CharbonnelBoundedDeepRelativeClosedDecompositionAt S n := by
  intro D hDbounded A hAD hAmem hAclosed
  let K : Set (RealEuclidean (n + 1)) := closure A
  have hKclosed : IsClosed K := isClosed_closure
  have hKmem : K ∈ charbonnelClosure S (n + 1) :=
    charbonnelClosure_topologicalClosure hAmem
  obtain ⟨B, hBclosed, hBmem, hBempty, hfrontier⟩ :=
    hboundary hKclosed hKmem
  let R : Set (RealEuclidean (n + 1)) := (K ∩ B) ∩ D.carrier
  have hRsub : R ⊆ D.carrier := inter_subset_right
  have hRmem : R ∈ charbonnelClosure S (n + 1) := by
    apply hC.ws1_inter (by omega)
    · exact hC.ws1_inter (by omega) hKmem hBmem
    · simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using
        (D.toCell hC).carrier_mem
  have hRclosed : IsClosed
      (Subtype.val ⁻¹' R : Set D.carrier) := by
    have hKBclosed : IsClosed (K ∩ B) := hKclosed.inter hBclosed
    have heq : (Subtype.val ⁻¹' R : Set D.carrier) =
        Subtype.val ⁻¹' (K ∩ B) := by
      ext x
      simp only [R, Set.mem_preimage, Set.mem_inter_iff,
        Subtype.coe_prop, and_true]
    rw [heq]
    exact hKBclosed.preimage continuous_subtype_val
  have hRempty : interior R = ∅ :=
    interior_eq_empty_of_subset (fun _ hz ↦ hz.1.2) hBempty
  obtain ⟨cover⟩ :=
    hempty D hDbounded hRsub hRmem hRclosed hRempty
  have hrelative : K ∩ D.carrier ⊆ A := by
    have hclosed := isClosed_preimage_val.mp hAclosed
    intro z hz
    apply hclosed
    refine ⟨hz.2, ?_⟩
    have hinter : D.carrier ∩ A = A := inter_eq_right.mpr hAD
    simpa only [K, hinter] using hz.1
  refine ⟨
    { Index := cover.Index
      indexFinite := cover.indexFinite
      cell := cover.cell
      contained := cover.contained
      covers := cover.covers
      compatible := ?_
      cells_eq_or_disjoint := cover.cells_eq_or_disjoint
      hereditary_projection_coherent :=
        cover.hereditary_projection_coherent }⟩
  intro i _
  have hKBcompat :
      (cover.cell i).carrier ⊆ K ∩ B ∨
        Disjoint (cover.cell i).carrier (K ∩ B) := by
    rcases cover.compatible i () with hinside | hdisjoint
    · left
      intro z hz
      exact (hinside hz).1
    · right
      rw [Set.disjoint_left]
      intro z hz hKB
      exact Set.disjoint_left.mp hdisjoint hz
        ⟨hKB, cover.contained i hz⟩
  have hKcompat :
      (cover.cell i).carrier ⊆ K ∨
        Disjoint (cover.cell i).carrier K :=
    connected_cell_compatible_of_boundary_intersection
      ((cover.cell i).toCell hC).shape.isPreconnected
      hKclosed hfrontier hKBcompat
  rcases hKcompat with hinside | hdisjoint
  · left
    intro z hz
    exact hrelative ⟨hinside hz, cover.contained i hz⟩
  · right
    exact hdisjoint.mono_right subset_closure

end AbelFormalization
