import AbelFormalization.WilkieSection4DeepGraphLift
import AbelFormalization.WilkieSection4GraphInduction

/-!
# The retained closed-decomposition graph branch

For a target relatively closed in a retained graph cell, projection to the
retained base is lossless.  The lower-dimensional closed-decomposition
hypothesis applies to that projection, and the resulting deep partition lifts
back through the graph without losing any projection data.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The graph-cell case of the successor step for Wilkie's retained relative
closed-decomposition induction. -/
theorem charbonnelDeepRelativeClosedDecomposition_graph
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {m : ℕ}
    (hI : CharbonnelDeepRelativeClosedDecompositionAt S m)
    (base : CharbonnelDeepEnrichedCell S (m + 1))
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
        S (charbonnelRestrictedGraph base.carrier f) (fun _ : Unit ↦ A)) := by
  let projectedA : Set (RealEuclidean (m + 1)) :=
    realEuclideanExistentialProjection
      (n := m + 1) (m := 1) A
  have hprojectedSub : projectedA ⊆ base.carrier := by
    rintro x ⟨y, hxy⟩
    simpa only [realEuclideanTakeLeft_append] using (hA hxy).1
  have hprojectedMem : projectedA ∈ charbonnelClosure S (m + 1) := by
    exact graphProjection_mem_charbonnelClosure (by omega) hAmem
  have hprojectedClosed : IsClosed
      (Subtype.val ⁻¹' projectedA : Set base.carrier) := by
    exact isClosed_graphProjection_in_base hf hA hAclosed
  obtain ⟨lower⟩ :=
    hI base hprojectedSub hprojectedMem hprojectedClosed
  exact ⟨lower.liftThroughGraph hC base f hf hgraph
    (fun _ : Unit ↦ A) (fun _ ↦ hA)⟩

end AbelFormalization
