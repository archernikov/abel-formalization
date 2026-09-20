import AbelFormalization.WilkieSection4EndpointLoci
import AbelFormalization.WilkieSection4CardinalityStability

/-!
# Wilkie Section 4: the complete open-base-cell branch

This file joins the three source loci used on pages 418--419.  On one
nonempty open recursive base cell:

* avoidance of the endpoint zero traces `H̃_f,H̃_g`, together with relative
  closedness in the ambient continuous band, gives no escape;
* avoidance of the collision zero trace `H̃` gives no collision;
* simultaneous compatibility with the closed cardinality loci and the
  WS5/Fubini cutoff gives exact constant fibre cardinality; and
* the ordered-tuple incidences construct every selector graph and hence the
  finite compatible graph/band/ray cover of the cylinder.

Thus the theorem below contains the whole full-dimensional local branch of
Wilkie's Section 4 induction.  No complement closure is used.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Intersecting an ambient closed set with a carrier gives a closed subset
of that carrier. -/
theorem isClosed_preimage_val_inter_right
    {X : Type*} [TopologicalSpace X] {K D : Set X}
    (hK : IsClosed K) :
    IsClosed (Subtype.val ⁻¹' (K ∩ D) : Set D) := by
  have hpreimage : (Subtype.val ⁻¹' (K ∩ D) : Set D) =
      Subtype.val ⁻¹' K := by
    ext x
    simp
  rw [hpreimage]
  exact hK.preimage continuous_subtype_val

/-- Full open-cell cylinder construction from Wilkie's three bad-locus
avoidance conditions and simultaneous compatibility with the cardinality
loci. -/
noncomputable def
    charbonnelFiniteSelectorRelativeCellCover_of_wilkieSection4_openCell
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {C B : Set (RealEuclidean p)}
    (hBshape : CharbonnelCellShape p B)
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBmem : B ∈ charbonnelClosure S p)
    (hBC : B ⊆ C)
    {A : MaxwellRelation p 1} {f g : RealEuclidean p → ℝ}
    (hAmem : A ∈ charbonnelClosure S (p + 1))
    (hAsub : A ⊆ charbonnelOpenBand C f g)
    (hAclosed : IsClosed
      (Subtype.val ⁻¹' A : Set (charbonnelOpenBand C f g)))
    (hf : ContinuousOn f C) (hg : ContinuousOn g C)
    (hNempty : interior
      (closure (wilkieSection4FiberCardinalityLocus C A N)) = ∅)
    (hcardinalityCompatible : ∀ j, j ≤ N →
      B ⊆ closure (wilkieSection4FiberCardinalityLocus C A j) ∨
        Disjoint B
          (closure (wilkieSection4FiberCardinalityLocus C A j)))
    (hcollision : Disjoint B (wilkieSection4CollisionLocus C A))
    (hlower : Disjoint B (wilkieSection4LowerEndpointLocus C A f))
    (hupper : Disjoint B (wilkieSection4UpperEndpointLocus C A g)) :
    CharbonnelFiniteCompatibleRelativeCellCover (charbonnelClosure S)
      (charbonnelCylinderCell B) A := by
  have hescape : MaxwellScalarFiberNoEscape B A :=
    maxwellScalarFiberNoEscape_of_relativelyClosedBand_of_disjoint_endpointLoci
      hBC hAsub hAclosed hf hg hlower hupper
  exact
    charbonnelFiniteSelectorRelativeCellCover_of_section4_compatible_loci
      hC hp hN hBshape hBopen hBnonempty hBmem hBC hAmem hNempty
        hcardinalityCompatible hescape hcollision

/-- Common source specialization: the scalar relation is the intersection
of an ambient closed carrier with the open band.  Its containment and
relative closedness premises are then automatic. -/
noncomputable def
    charbonnelFiniteSelectorRelativeCellCover_of_wilkieSection4_closedInterBand
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p N : ℕ} (hp : 0 < p) (hN : 0 < N)
    {C B : Set (RealEuclidean p)}
    (hBshape : CharbonnelCellShape p B)
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBmem : B ∈ charbonnelClosure S p)
    (hBC : B ⊆ C)
    {K : MaxwellRelation p 1} {f g : RealEuclidean p → ℝ}
    (hKclosed : IsClosed K)
    (hAmem : K ∩ charbonnelOpenBand C f g ∈
      charbonnelClosure S (p + 1))
    (hf : ContinuousOn f C) (hg : ContinuousOn g C)
    (hNempty : interior
      (closure (wilkieSection4FiberCardinalityLocus C
        (K ∩ charbonnelOpenBand C f g) N)) = ∅)
    (hcardinalityCompatible : ∀ j, j ≤ N →
      B ⊆ closure (wilkieSection4FiberCardinalityLocus C
          (K ∩ charbonnelOpenBand C f g) j) ∨
        Disjoint B
          (closure (wilkieSection4FiberCardinalityLocus C
            (K ∩ charbonnelOpenBand C f g) j)))
    (hcollision : Disjoint B
      (wilkieSection4CollisionLocus C
        (K ∩ charbonnelOpenBand C f g)))
    (hlower : Disjoint B
      (wilkieSection4LowerEndpointLocus C
        (K ∩ charbonnelOpenBand C f g) f))
    (hupper : Disjoint B
      (wilkieSection4UpperEndpointLocus C
        (K ∩ charbonnelOpenBand C f g) g)) :
    CharbonnelFiniteCompatibleRelativeCellCover (charbonnelClosure S)
      (charbonnelCylinderCell B)
      (K ∩ charbonnelOpenBand C f g) :=
  charbonnelFiniteSelectorRelativeCellCover_of_wilkieSection4_openCell
    hC hp hN hBshape hBopen hBnonempty hBmem hBC hAmem
      inter_subset_right (isClosed_preimage_val_inter_right hKclosed)
      hf hg hNempty hcardinalityCompatible hcollision hlower hupper

end AbelFormalization
