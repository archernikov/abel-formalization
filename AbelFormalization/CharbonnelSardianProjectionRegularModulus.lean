import AbelFormalization.CharbonnelSardianProjectionCriticalValues
import AbelFormalization.WilkieLemma34NestedModulusAvoidance

/-!
# A common regular-value modulus for Sardian projection

Wilkie's nested-modulus avoidance lemma turns empty interior of the finite
exact-depth critical-parameter set into a modulus on which every old tuple
level is regular. Taking its infimum with the old approximation modulus
preserves both requirements.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Empty interior of the exact-depth finite critical-value set gives one
refinement of the old modulus on which all normalized old tuple levels are
regular. -/
theorem exists_sardianProjectionRegularModulus
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)))
    {order n : ℕ} {A : Set (RealEuclidean (n + 1))}
    (old : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A)
    (hcritical :
      interior
        (old.family.exactDepthProjectionCriticalParameterSet
          hG hsmooth) = ∅) :
    ∃ regularModulus : CharbonnelModulus
        (old.commonHiddenArity + 1),
      regularModulus.Refines old.modulus ∧
      ∀ epsilon : RealEuclidean
          ((old.commonHiddenArity + 1) + 1),
        regularModulus.IsBounded epsilon →
          ∀ exactOld ∈
              sardianProjectionOldExactDepthList
                hG hsmooth old.family,
            ∀ v : RealEuclidean
                (n + (old.commonHiddenArity + 1)),
              sardianProjectionOldTuple exactOld v =
                  CharbonnelModulus.parameterTail epsilon →
                Function.Surjective
                  (fderiv ℝ
                    (sardianProjectionOldTuple exactOld) v) := by
  let bad :=
    old.family.exactDepthProjectionCriticalParameterSet hG hsmooth
  have hbad : bad ∈
      charbonnelClosure (literalZeroSetFamily G)
        (old.commonHiddenArity + 1) :=
    old.family.exactDepthProjectionCriticalParameterSet_mem_literalZeroCharbonnel
      hG hsmooth hderiv
  obtain ⟨avoidModulus, havoid⟩ :=
    wilkieLemma34_exists_nested_modulus_avoiding
      hC (by omega) hbad hcritical
  let regularModulus :=
    CharbonnelModulus.infimum old.modulus avoidModulus
  refine ⟨regularModulus,
    CharbonnelModulus.infimum_refines_left
      old.modulus avoidModulus, ?_⟩
  intro epsilon hepsilon exactOld hexactOld v hv
  have hparts :=
    (CharbonnelModulus.isBounded_infimum_iff
      old.modulus avoidModulus epsilon).1 hepsilon
  have hnotBad :
      CharbonnelModulus.parameterTail epsilon ∉ bad :=
    havoid epsilon hparts.2
  exact old.family.exactDepthOldTuple_fderiv_surjective_of_not_mem
    hG hsmooth hnotBad exactOld hexactOld v hv

end AbelFormalization
