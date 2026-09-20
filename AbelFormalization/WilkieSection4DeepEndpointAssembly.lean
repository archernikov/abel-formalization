import AbelFormalization.WilkieSection4DeepSimultaneousInduction
import AbelFormalization.WilkieSection4DeepProjectionPlumbing

/-!
# Endpoint assembly from the retained Section 4 induction

A completed bounded retained simultaneous induction supplies relative closed
 decompositions in every positive ambient dimension.  Applying those
 decompositions inside the retained bounded cube, projecting the resulting
 hereditary deep covers, and forgetting the deep data produces exactly the
 projection-coherent tower premise used by the complement pipeline.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- A bounded retained simultaneous Section 4 induction in every dimension
 gives the bounded projection-coherent tower property. -/
theorem
    wilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty_of_boundedDeepSection4Induction
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hinduction : ∀ n : ℕ,
      CharbonnelBoundedDeepSection4InductionAt S n) :
    WilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty S := by
  apply wilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty_of_deep
    hC
  apply wilkieBoundedDeepProjectionCoherentCellCoverProperty_of_fullClosedDeepCovers
    hC
  exact fullClosedDeepCovers_of_boundedDeepRelativeClosedDecomposition hC
    (fun n ↦ (hinduction n).1)

/-- For a literal-zero family, a bounded retained simultaneous induction
constructed from the closed-boundary carrier datum packages into the exact
bounded tower assembly callback consumed by the complement theorem. -/
theorem
    charbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly_of_boundedDeepSection4Induction
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hinduction : CharbonnelClosedBoundaryCarrierProperty G →
      ∀ n : ℕ,
        CharbonnelBoundedDeepSection4InductionAt
          (literalZeroSetFamily G) n) :
    CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly G := by
  intro hboundary
  exact
    wilkieBoundedProjectionCoherentEnrichedCellCoverTowerProperty_of_boundedDeepSection4Induction
      (literalZeroSet_charbonnelClosure_positiveArityWeakSetStructure
        hG hsmooth)
      (hinduction hboundary)

end AbelFormalization
