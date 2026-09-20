import AbelFormalization.CharbonnelOrderedSelectorCells
import AbelFormalization.CharbonnelCellBoundaryCompatibility

/-!
# Boundary carriers assembled with finite selector cylinders

This file joins the two completed parts of Wilkie's open-cell argument.
A finite compatible base cover carrying constant-cardinality continuous
ordered selectors gives a compatible cylinder cover.  If the selectors
describe the intersection of a closed set with a carrier containing its
frontier, connectedness of the recursive cells transfers compatibility to
the closed set itself.

The remaining input is therefore only the simultaneous lower-dimensional
refinement which produces the base cover and its selector data.  No
complement closure is used in this assembly.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- All data needed to cut the cylinders over a finite recursive base-cell
cover into cells compatible with `A`.  Fibre cardinality may vary between
base cells, including cardinality zero. -/
structure CharbonnelFiniteSelectorCylinderData
    (C : EuclideanSetFamily) {n : ℕ}
    (A : Set (RealEuclidean (n + 1))) where
  baseTarget : Set (RealEuclidean n)
  baseCover : CharbonnelFiniteCompatibleCellCover C baseTarget
  card : Fin baseCover.count → ℕ
  selector : ∀ i, Fin (card i) → RealEuclidean n → ℝ
  selector_continuous : ∀ i j,
    ContinuousOn (selector i j) (baseCover.cell i).carrier
  selector_ordered : ∀ i x, x ∈ (baseCover.cell i).carrier →
    StrictMono (fun j ↦ selector i j x)
  exact_fiber : ∀ i z,
    realEuclideanTakeLeft z ∈ (baseCover.cell i).carrier →
      (z ∈ A ↔ ∃ j, realEuclideanTakeRight z 0 =
        selector i j (realEuclideanTakeLeft z))
  empty_cylinder_mem : ∀ i, card i = 0 →
    charbonnelCylinderCell (baseCover.cell i).carrier ∈ C (n + 1)
  selector_region_mem : ∀ i (hcard : 0 < card i) region,
    charbonnelOrderedSelectorRegionCarrier
      (baseCover.cell i).carrier (selector i) hcard region ∈ C (n + 1)

namespace CharbonnelFiniteSelectorCylinderData

/-- The selector data gives the global finite compatible cover supplied by
the graph, gap, ray, and empty-cylinder construction. -/
noncomputable def compatibleCover
    {C : EuclideanSetFamily} {n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (data : CharbonnelFiniteSelectorCylinderData C A) (hn : 0 < n) :
    CharbonnelFiniteCompatibleCellCover C A :=
  data.baseCover.finiteSelectorCylinderCover hn
    data.card data.selector data.selector_continuous data.selector_ordered
    data.exact_fiber data.empty_cylinder_mem data.selector_region_mem

/-- If the selector data describes `A ∩ B`, where `A` is closed and `B`
contains `frontier A`, the same connected recursive cells are compatible
with `A`. -/
noncomputable def compatibleCover_of_boundaryIntersection
    {C : EuclideanSetFamily} {n : ℕ}
    {A B : Set (RealEuclidean (n + 1))}
    (data : CharbonnelFiniteSelectorCylinderData C (A ∩ B))
    (hn : 0 < n) (hAclosed : IsClosed A)
    (hfrontier : frontier A ⊆ B) :
    CharbonnelFiniteCompatibleCellCover C A :=
  CharbonnelFiniteCompatibleCellCover.of_boundaryIntersection_auto
    hAclosed hfrontier (data.compatibleCover hn)

end CharbonnelFiniteSelectorCylinderData

/-- The exact remaining open-cell refinement premise: after choosing any
closed empty-interior boundary carrier in the family, simultaneously refine
the base into recursive cells on which the intersection has a finite exact
ordered-selector description and all resulting regions remain in the
family. -/
def CharbonnelBoundarySelectorRefinementProperty
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n →
    ∀ {A B : Set (RealEuclidean (n + 1))},
      IsClosed A → A ∈ C (n + 1) →
      IsClosed B → B ∈ C (n + 1) → interior B = ∅ →
      frontier A ⊆ B →
        Nonempty (CharbonnelFiniteSelectorCylinderData C (A ∩ B))

/-- Finite compatible covers for closed family members in every dimension
strictly above one.  This is the global-space instance of Wilkie `(I)`. -/
def CharbonnelHigherDimensionalClosedMemberCellCoverProperty
    (C : EuclideanSetFamily) : Prop :=
  ∀ {d : ℕ}, 1 < d →
    ∀ {A : Set (RealEuclidean d)}, IsClosed A → A ∈ C d →
      Nonempty (CharbonnelFiniteCompatibleCellCover C A)

/-- Boundary carriers plus the exact selector refinement premise prove the
higher-dimensional closed-member cell-cover property. -/
theorem higherDimensionalClosedMemberCellCovers_of_boundarySelectors
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hboundary : CharbonnelClosedBoundaryCarrierProperty G)
    (hrefine : CharbonnelBoundarySelectorRefinementProperty
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelHigherDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure (literalZeroSetFamily G)) := by
  intro d hd A hAclosed hAmem
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hn : 0 < n := by omega
  obtain ⟨B, hBclosed, hBmem, hBempty, hfrontier⟩ :=
    hboundary (by omega : 0 < n + 1) hAclosed hAmem
  obtain ⟨data⟩ :=
    hrefine hn hAclosed hAmem hBclosed hBmem hBempty hfrontier
  exact ⟨data.compatibleCover_of_boundaryIntersection hn hAclosed hfrontier⟩

end AbelFormalization
