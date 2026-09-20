import AbelFormalization.CharbonnelUnaryCompatibleCellCover
import AbelFormalization.WilkieSection4SimultaneousRefinement
import AbelFormalization.WilkieSection4OpenCell

/-!
# Wilkie Section 4: one base cover for all auxiliary loci

This file packages the finite simultaneous refinement used on page 418.  The
targets are all closed cardinality loci `closure A_j` for `0 ≤ j ≤ N`, followed
by the collision and two endpoint zero traces.  The resulting cover is refined
once more against the ambient base cell, so every output cell is either inside
that base cell or disjoint from it.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Reindex the finite-cover refinement theorem from `Fin r` to an arbitrary
finite index type. -/
theorem finiteSimultaneouslyCompatibleCellCover_of_individual_fintype
    {C : EuclideanSetFamily}
    (hrefine : CharbonnelFiniteCompatibleCoverCommonRefinementProperty C)
    {n : ℕ} {ι : Type} [Fintype ι]
    (target : ι → Set (RealEuclidean n))
    (hcover : ∀ j,
      Nonempty (CharbonnelFiniteCompatibleCellCover C (target j))) :
    Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleCellCover C target) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let targetFin : Fin (Fintype.card ι) → Set (RealEuclidean n) :=
    fun j ↦ target (e.symm j)
  have hcoverFin : ∀ j,
      Nonempty (CharbonnelFiniteCompatibleCellCover C (targetFin j)) :=
    fun j ↦ hcover (e.symm j)
  obtain ⟨cover⟩ :=
    finiteSimultaneouslyCompatibleCellCover_of_individual
      hrefine targetFin hcoverFin
  refine ⟨
    { count := cover.count
      cell := cover.cell
      covers := cover.covers
      compatible := ?_ }⟩
  intro i j
  simpa [targetFin, e] using cover.compatible i (e j)

/-- A finite cover compatible both with a distinguished base cell and with
every target in a finite family. -/
structure CharbonnelFiniteBaseAndTargetsCompatibleCellCover
    (C : EuclideanSetFamily) {n : ℕ} {ι : Type}
    (base : Set (RealEuclidean n))
    (target : ι → Set (RealEuclidean n)) where
  count : ℕ
  cell : Fin count → CharbonnelCell C n
  covers : ∀ x : RealEuclidean n, ∃ i, x ∈ (cell i).carrier
  base_compatible : ∀ i,
    (cell i).carrier ⊆ base ∨ Disjoint (cell i).carrier base
  target_compatible : ∀ i j,
    (cell i).carrier ⊆ target j ∨ Disjoint (cell i).carrier (target j)

namespace CharbonnelFiniteBaseAndTargetsCompatibleCellCover

/-- Forget the auxiliary loci and retain the compatible base cover. -/
def baseCover
    {C : EuclideanSetFamily} {n : ℕ} {ι : Type}
    {base : Set (RealEuclidean n)} {target : ι → Set (RealEuclidean n)}
    (cover : CharbonnelFiniteBaseAndTargetsCompatibleCellCover
      C base target) :
    CharbonnelFiniteCompatibleCellCover C base :=
  { count := cover.count
    cell := cover.cell
    covers := cover.covers
    compatible := cover.base_compatible }

end CharbonnelFiniteBaseAndTargetsCompatibleCellCover

/-- Refine a simultaneous target cover once more against one existing cell.
Compatibility with the old targets transfers through the old covering. -/
theorem finiteBaseAndTargetsCompatibleCellCover_of_simultaneous
    {C : EuclideanSetFamily}
    (hrefine : CharbonnelFiniteCellFamilyCommonRefinementProperty C)
    {n : ℕ} {ι : Type}
    {target : ι → Set (RealEuclidean n)}
    (old : CharbonnelFiniteSimultaneouslyCompatibleCellCover C target)
    {base : Set (RealEuclidean n)}
    (baseCell : CharbonnelCell C n) (hbase : baseCell.carrier = base) :
    Nonempty
      (CharbonnelFiniteBaseAndTargetsCompatibleCellCover C base target) := by
  classical
  let cells : (Fin old.count ⊕ Unit) → CharbonnelCell C n
    | Sum.inl i => old.cell i
    | Sum.inr _ => baseCell
  obtain ⟨fine⟩ := hrefine cells
  refine ⟨
    { count := fine.count
      cell := fine.cell
      covers := fine.covers
      base_compatible := ?_
      target_compatible := ?_ }⟩
  · intro i
    simpa [cells, hbase] using fine.compatible i (Sum.inr ())
  · intro i j
    apply compatible_target_of_compatible_cover_cells
      (cover := old.targetCover j)
    intro k
    change (fine.cell i).carrier ⊆ (old.cell k).carrier ∨
      Disjoint (fine.cell i).carrier (old.cell k).carrier
    simpa [cells] using fine.compatible i (Sum.inl k)

/-- The finite index set for Wilkie's Section 4 base refinement. -/
abbrev WilkieSection4LociIndex (N : ℕ) := Fin (N + 1) ⊕ Fin 3

/-- Collision, lower-endpoint, and upper-endpoint zero traces. -/
def wilkieSection4BadLocus {p : ℕ}
    (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (f g : RealEuclidean p → ℝ) : Fin 3 → Set (RealEuclidean p) :=
  Fin.cases (wilkieSection4CollisionLocus C A) fun i ↦
    Fin.cases (wilkieSection4LowerEndpointLocus C A f)
      (fun _ ↦ wilkieSection4UpperEndpointLocus C A g) i

@[simp]
theorem wilkieSection4BadLocus_zero
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (f g : RealEuclidean p → ℝ) :
    wilkieSection4BadLocus C A f g (0 : Fin 3) =
      wilkieSection4CollisionLocus C A := rfl

@[simp]
theorem wilkieSection4BadLocus_one
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (f g : RealEuclidean p → ℝ) :
    wilkieSection4BadLocus C A f g (1 : Fin 3) =
      wilkieSection4LowerEndpointLocus C A f := rfl

@[simp]
theorem wilkieSection4BadLocus_two
    {p : ℕ} (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (f g : RealEuclidean p → ℝ) :
    wilkieSection4BadLocus C A f g (2 : Fin 3) =
      wilkieSection4UpperEndpointLocus C A g := rfl

/-- The whole finite family refined simultaneously in the open-cell branch. -/
def wilkieSection4LociTarget {p N : ℕ}
    (C : Set (RealEuclidean p)) (A : MaxwellRelation p 1)
    (f g : RealEuclidean p → ℝ) :
    WilkieSection4LociIndex N → Set (RealEuclidean p)
  | Sum.inl j => closure (wilkieSection4FiberCardinalityLocus C A j)
  | Sum.inr j => wilkieSection4BadLocus C A f g j

namespace CharbonnelFiniteBaseAndTargetsCompatibleCellCover

theorem section4_cardinality_compatible
    {S : EuclideanSetFamily} {p N : ℕ}
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f g : RealEuclidean p → ℝ}
    (cover : CharbonnelFiniteBaseAndTargetsCompatibleCellCover
      (charbonnelClosure S) C (wilkieSection4LociTarget C A f g :
        WilkieSection4LociIndex N → Set (RealEuclidean p)))
    (i : Fin cover.count) {j : ℕ} (hj : j ≤ N) :
    (cover.cell i).carrier ⊆
        closure (wilkieSection4FiberCardinalityLocus C A j) ∨
      Disjoint (cover.cell i).carrier
        (closure (wilkieSection4FiberCardinalityLocus C A j)) := by
  simpa [wilkieSection4LociTarget] using
    cover.target_compatible i
      (Sum.inl (⟨j, by omega⟩ : Fin (N + 1)))

theorem section4_collision_compatible
    {S : EuclideanSetFamily} {p N : ℕ}
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f g : RealEuclidean p → ℝ}
    (cover : CharbonnelFiniteBaseAndTargetsCompatibleCellCover
      (charbonnelClosure S) C (wilkieSection4LociTarget C A f g :
        WilkieSection4LociIndex N → Set (RealEuclidean p)))
    (i : Fin cover.count) :
    (cover.cell i).carrier ⊆ wilkieSection4CollisionLocus C A ∨
      Disjoint (cover.cell i).carrier
        (wilkieSection4CollisionLocus C A) := by
  simpa [wilkieSection4LociTarget] using
    cover.target_compatible i (Sum.inr (0 : Fin 3))

theorem section4_lowerEndpoint_compatible
    {S : EuclideanSetFamily} {p N : ℕ}
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f g : RealEuclidean p → ℝ}
    (cover : CharbonnelFiniteBaseAndTargetsCompatibleCellCover
      (charbonnelClosure S) C (wilkieSection4LociTarget C A f g :
        WilkieSection4LociIndex N → Set (RealEuclidean p)))
    (i : Fin cover.count) :
    (cover.cell i).carrier ⊆ wilkieSection4LowerEndpointLocus C A f ∨
      Disjoint (cover.cell i).carrier
        (wilkieSection4LowerEndpointLocus C A f) := by
  simpa [wilkieSection4LociTarget] using
    cover.target_compatible i (Sum.inr (1 : Fin 3))

theorem section4_upperEndpoint_compatible
    {S : EuclideanSetFamily} {p N : ℕ}
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f g : RealEuclidean p → ℝ}
    (cover : CharbonnelFiniteBaseAndTargetsCompatibleCellCover
      (charbonnelClosure S) C (wilkieSection4LociTarget C A f g :
        WilkieSection4LociIndex N → Set (RealEuclidean p)))
    (i : Fin cover.count) :
    (cover.cell i).carrier ⊆ wilkieSection4UpperEndpointLocus C A g ∨
      Disjoint (cover.cell i).carrier
        (wilkieSection4UpperEndpointLocus C A g) := by
  simpa [wilkieSection4LociTarget] using
    cover.target_compatible i (Sum.inr (2 : Fin 3))

end CharbonnelFiniteBaseAndTargetsCompatibleCellCover

theorem wilkieSection4LociTarget_isClosed
    {p N : ℕ} {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f g : RealEuclidean p → ℝ}
    (j : WilkieSection4LociIndex N) :
    IsClosed (wilkieSection4LociTarget C A f g j) := by
  rcases j with j | j
  · exact isClosed_closure
  · refine Fin.cases ?_ (fun i ↦ ?_) j
    · exact wilkieSection4CollisionLocus_isClosed C A
    · refine Fin.cases ?_ (fun _ ↦ ?_) i
      · exact wilkieSection4LowerEndpointLocus_isClosed C A f
      · exact wilkieSection4UpperEndpointLocus_isClosed C A g

theorem wilkieSection4LociTarget_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p N : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f g : RealEuclidean p → ℝ}
    (hCmem : C ∈ charbonnelClosure S p)
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hfGraph : charbonnelRestrictedGraph C f ∈
      charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph C g ∈
      charbonnelClosure S (p + 1))
    (j : WilkieSection4LociIndex N) :
    wilkieSection4LociTarget C A f g j ∈ charbonnelClosure S p := by
  rcases j with j | j
  · exact closure_wilkieSection4FiberCardinalityLocus_mem_charbonnelClosure
      hC hp hCmem hAmem
  · refine Fin.cases ?_ (fun i ↦ ?_) j
    · exact wilkieSection4CollisionLocus_mem_charbonnelClosure
        hC hp hCmem hAmem
    · refine Fin.cases ?_ (fun _ ↦ ?_) i
      · exact wilkieSection4LowerEndpointLocus_mem_charbonnelClosure
          hC hp hCmem hAmem hfGraph
      · exact wilkieSection4UpperEndpointLocus_mem_charbonnelClosure
          hC hp hCmem hAmem hgGraph

/-- Wilkie's `(I)ₚ + (II)ₚ` construction of one base cover compatible with
the ambient base cell and all cardinality/collision/endpoint loci. -/
theorem exists_wilkieSection4_baseAndLociCompatibleCellCover
    {S : EuclideanSetFamily}
    (hweak : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    (hII : CharbonnelFiniteCellFamilyCommonRefinementProperty
      (charbonnelClosure S))
    {p N : ℕ} (hp : 0 < p)
    {C : Set (RealEuclidean p)} {A : MaxwellRelation p 1}
    {f g : RealEuclidean p → ℝ}
    (baseCell : CharbonnelCell (charbonnelClosure S) p)
    (hbase : baseCell.carrier = C)
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hfGraph : charbonnelRestrictedGraph C f ∈
      charbonnelClosure S (p + 1))
    (hgGraph : charbonnelRestrictedGraph C g ∈
      charbonnelClosure S (p + 1)) :
    Nonempty
      (CharbonnelFiniteBaseAndTargetsCompatibleCellCover
        (charbonnelClosure S) C (wilkieSection4LociTarget C A f g :
          WilkieSection4LociIndex N → Set (RealEuclidean p))) := by
  have hCmem : C ∈ charbonnelClosure S p := by
    simpa [← hbase] using baseCell.carrier_mem
  have hindividual : ∀ j : WilkieSection4LociIndex N,
      Nonempty (CharbonnelFiniteCompatibleCellCover
        (charbonnelClosure S) (wilkieSection4LociTarget C A f g j)) :=
    fun j ↦ hI hp (wilkieSection4LociTarget_isClosed j)
      (wilkieSection4LociTarget_mem_charbonnelClosure hweak hp hCmem
        hAmem hfGraph hgGraph j)
  obtain ⟨old⟩ :=
    finiteSimultaneouslyCompatibleCellCover_of_individual_fintype
      (finiteCompatibleCoverCommonRefinement_of_cellFamily hII)
      (wilkieSection4LociTarget C A f g) hindividual
  exact finiteBaseAndTargetsCompatibleCellCover_of_simultaneous
    hII old baseCell hbase

end AbelFormalization
