import AbelFormalization.WilkieSection4UnaryPartitionBase
import AbelFormalization.WilkieSection4DeepCommonRefinementSuccessor
import AbelFormalization.WilkieSection4DeepBoundedSuccessorAssembly
import AbelFormalization.CharbonnelPositiveZeroTraceCategory
import AbelFormalization.WilkieSection4DeepMainTheoremEndpoint

/-!
# The literal-zero instance of Wilkie's bounded Section 4 induction

The unary partition theorem starts the retained simultaneous induction.
At each successor dimension the closed-decomposition and common-refinement
steps use the same lower-dimensional pair.  For literal-zero families,
Charbonnel's Theorems 2.1 and 2.2 are supplied by the proved category
argument, while the boundary-carrier hypothesis is exactly the callback
passed by the complement pipeline.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- The bounded retained Section 4 induction in every dimension for a
literal-zero family. -/
theorem literalZeroSet_charbonnelClosure_boundedDeepSection4Induction
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hboundary : CharbonnelClosedBoundaryCarrierProperty G) :
    ∀ n : ℕ,
      CharbonnelBoundedDeepSection4InductionAt
        (literalZeroSetFamily G) n := by
  let hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  let h21 : CharbonnelTheorem21
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_theorem21 hG hsmooth hUFF
  let h22 : CharbonnelTheorem22
      (charbonnelClosure (literalZeroSetFamily G)) :=
    literalZeroSet_charbonnelClosure_theorem22 hG hsmooth hUFF
  intro n
  induction n with
  | zero =>
      exact hC.charbonnelBoundedDeepSection4InductionAt_zero
  | succ n ih =>
      refine ⟨?_, ?_⟩
      · exact
          charbonnelBoundedDeepRelativeClosedDecompositionAt_succ
            hC h21 h22 ih.1 ih.2
            (fun hKclosed hKmem ↦
              hboundary (by omega) hKclosed hKmem)
      · exact
          charbonnelBoundedDeepRelativeCommonRefinementAt_succ
            hC.toPositiveArityWeakSetStructure ih.1 ih.2

/-- The all-dimensional literal-zero induction packages into the exact tower
assembly callback used by the complement pipeline. -/
theorem
    charbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly_of_literalZeroInduction
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G) :
    CharbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly G := by
  apply
    charbonnelBoundedProjectionCoherentEnrichedCellCoverTowerAssembly_of_boundedDeepSection4Induction
      hG hsmooth
  intro hboundary
  exact literalZeroSet_charbonnelClosure_boundedDeepSection4Induction
    hG hsmooth hUFF hboundary

/-- Wilkie's bounded Section 4 induction, together with the established Lion,
trace, and Sardian results, proves the literal theorem stated by the project. -/
theorem mainTheorem : MainTheorem := by
  apply mainTheorem_of_boundedDeepSection4Induction
  intro A hA hboundary
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact literalZeroSet_charbonnelClosure_boundedDeepSection4Induction
    hG hsmooth hA.hasUniformFiberFiniteness hboundary

end AbelFormalization
