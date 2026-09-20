import AbelFormalization.WilkieSection4DeepNonOpenPresentation

/-!
# Bounded transport across the first singular coordinate

A bounded nonempty deep cell which is not open has, by the presentation
theorem, either a buried graph root or a buried unary-point root.  Delete that
coordinate, apply the bounded lower-dimensional relative closed decomposition,
and pull the resulting partition back through the exact insertion map.

Only the raw local precover is retained here.  The successor assembly performs
its projection-coherence normalization once after flattening all local covers.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

open CharbonnelDeepEnrichedCell

/-- Transport a lower-dimensional decomposition along an already chosen
singular-coordinate presentation.  The explicit dimension equality lets the
indexed presentation eliminate while retaining the fixed induction level. -/
private theorem charbonnelDeepNonOpenPresentation_precover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n ambient : ℕ}
    (hI : CharbonnelBoundedDeepRelativeClosedDecompositionAt S n)
    (hdim : ambient = (n + 1) + 1)
    (D : CharbonnelDeepEnrichedCell S ambient)
    (presentation : CharbonnelDeepNonOpenPresentation hC D)
    {A : Set (RealEuclidean ambient)}
    (hAD : A ⊆ D.carrier)
    (hAmem : A ∈ charbonnelClosure S ambient)
    (hAclosed : IsClosed (Subtype.val ⁻¹' A : Set D.carrier)) :
    Nonempty
      (CharbonnelFinitePartitionedDeepRelativeCellPrecover
        S D.carrier A) := by
  cases presentation with
  | @graph rootN trail hn D base f hf hgraph deleted hroot carrier_eq
      projection_image deleted_isBounded =>
      cases trail with
      | zero =>
          cases rootN with
          | zero => omega
          | succ m =>
              have hnEq : n = m := by omega
              subst n
              let P := charbonnelBuriedGraphProjectionLinearMap (m + 1) 0
              let projectedA := P '' A
              have hprojectedSub : projectedA ⊆ deleted.carrier := by
                rw [← projection_image]
                exact Set.image_mono hAD
              have hprojectedMem : projectedA ∈
                  charbonnelClosure S _ := by
                exact charbonnelDeepGraphPresentation_projectedTarget_mem
                  hC hn hAmem
              have hprojectedClosed : IsClosed
                  (Subtype.val ⁻¹' projectedA : Set deleted.carrier) := by
                exact charbonnelDeepGraphPresentation_projectedTarget_isClosed
                  hC hn D base f hf hgraph deleted hroot carrier_eq
                    projection_image hAD hAclosed
              obtain ⟨lower⟩ := hI deleted deleted_isBounded hprojectedSub
                hprojectedMem hprojectedClosed
              have hAinserted : A ⊆
                  (insertGraphAtDepth hC hn base f hf hgraph 0 deleted
                    hroot).carrier := by
                rw [← carrier_eq]
                exact hAD
              rw [carrier_eq]
              exact ⟨insertGraphAtDepthZeroPrecover hC base f hf hgraph
                deleted hroot hAinserted lower⟩
      | succ q =>
          have hnEq : n = rootN + q := by omega
          subst n
          let P := charbonnelBuriedGraphProjectionLinearMap rootN (q + 1)
          let projectedA := P '' A
          have hprojectedSub : projectedA ⊆ deleted.carrier := by
            rw [← projection_image]
            exact Set.image_mono hAD
          have hprojectedMem : projectedA ∈
              charbonnelClosure S _ := by
            exact charbonnelDeepGraphPresentation_projectedTarget_mem
              hC hn hAmem
          have hprojectedClosed : IsClosed
              (Subtype.val ⁻¹' projectedA : Set deleted.carrier) := by
            exact charbonnelDeepGraphPresentation_projectedTarget_isClosed
              hC hn D base f hf hgraph deleted hroot carrier_eq
                projection_image hAD hAclosed
          obtain ⟨lower⟩ := hI deleted deleted_isBounded hprojectedSub
            hprojectedMem hprojectedClosed
          have hAinserted : A ⊆
              (insertGraphAtDepth hC hn base f hf hgraph (q + 1) deleted
                hroot).carrier := by
            rw [← carrier_eq]
            exact hAD
          rw [carrier_eq]
          exact ⟨insertGraphAtPositiveDepthPrecover hC hn base f hf hgraph
            deleted hroot hAinserted lower⟩
  | @point q D a deleted carrier_eq projection_image deleted_isBounded =>
      have hnEq : n = q := by omega
      subst n
      let P := charbonnelUnaryPointProjectionLinearMap (q + 1)
      let projectedA := P '' A
      have hprojectedSub : projectedA ⊆ deleted.carrier := by
        rw [← projection_image]
        exact Set.image_mono hAD
      have hprojectedMem : projectedA ∈
          charbonnelClosure S _ := by
        exact charbonnelDeepPointPresentation_projectedTarget_mem hC hAmem
      have hprojectedClosed : IsClosed
          (Subtype.val ⁻¹' projectedA : Set deleted.carrier) := by
        exact charbonnelDeepPointPresentation_projectedTarget_isClosed
          hC D a deleted carrier_eq projection_image hAD hAclosed
      obtain ⟨lower⟩ := hI deleted deleted_isBounded hprojectedSub
        hprojectedMem hprojectedClosed
      have hAinserted : A ⊆
          (insertUnaryPointAtDepth hC a q deleted).carrier := by
        rw [← carrier_eq]
        exact hAD
      rw [carrier_eq]
      exact ⟨insertUnaryPointAtDepthPrecover hC a q deleted
        hAinserted lower⟩

/-- The bounded lower-dimensional closed-decomposition hypothesis supplies a
raw relative precover on every bounded nonempty non-open deep cell one
dimension higher.  Both possible first singular roots, a positive-dimensional
graph and a unary point, are included. -/
theorem charbonnelBoundedDeepNonOpenPrecover_of_lower
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ}
    (hI : CharbonnelBoundedDeepRelativeClosedDecompositionAt S n) :
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
            S D.carrier A) := by
  intro D hDbounded hDnonempty hDnotOpen A hAD hAmem hAclosed
  let presentation :=
    charbonnelDeepNonOpenPresentation_of_isBounded_nonempty_not_isOpen
      hC (by omega) D hDbounded hDnonempty hDnotOpen
  exact charbonnelDeepNonOpenPresentation_precover hC hI rfl D presentation
    hAD hAmem hAclosed

end AbelFormalization
