import AbelFormalization.WilkieSection4DeepEnrichedCells

/-!
# Core structures for hereditary deep cell covers

This lightweight module contains only the recursively enriched cover data.
Conversions to the older projection-tower API remain in
`WilkieSection4DeepProjectionTower`.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Pairwise equality-or-disjointness of projected bases at every depth of a
finite family of deep cells.  At dimension one there is no further projected
base, so the condition is vacuous. -/
def CharbonnelDeepCellFamilyProjectionCoherent
    {S : EuclideanSetFamily} {I : Type} :
    (n : ℕ) → (I → CharbonnelDeepEnrichedCell S (n + 1)) → Prop
  | 0, _ => True
  | n + 1, cells =>
      (∀ i j,
        ((cells i).projectedBase (by omega : 0 < n + 1)).carrier =
            ((cells j).projectedBase (by omega : 0 < n + 1)).carrier ∨
          Disjoint
            ((cells i).projectedBase (by omega : 0 < n + 1)).carrier
            ((cells j).projectedBase (by omega : 0 < n + 1)).carrier) ∧
      CharbonnelDeepCellFamilyProjectionCoherent n
        (fun i ↦ (cells i).projectedBase (by omega : 0 < n + 1))

/-- A finite relative cover by recursively enriched cells, whose projected
bases form a partition up to repetitions at every lower positive dimension. -/
structure CharbonnelFiniteDeepProjectionCoherentCellCover
    (S : EuclideanSetFamily) {n : ℕ}
    (D A : Set (RealEuclidean (n + 1))) where
  Index : Type
  indexFinite : Finite Index
  cell : Index → CharbonnelDeepEnrichedCell S (n + 1)
  target_subset_domain : A ⊆ D
  contained : ∀ i, (cell i).carrier ⊆ D
  covers : ∀ z ∈ D, ∃ i, z ∈ (cell i).carrier
  compatible : ∀ i,
    (cell i).carrier ⊆ A ∨ Disjoint (cell i).carrier A
  hereditary_projection_coherent :
    CharbonnelDeepCellFamilyProjectionCoherent n cell

end AbelFormalization
