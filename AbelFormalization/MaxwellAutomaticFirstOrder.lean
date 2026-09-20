import AbelFormalization.MaxwellCorrectedFirstOrderAssembly
import AbelFormalization.MaxwellSameInfinityDirectLimits

/-!
# Automatic Maxwell first-order assembly

The established Charbonnel interfaces make the remaining corrected
first-order mechanisms automatic.  One-sided bad-locus smallness gives the
two equal-infinity affine-chord mechanisms, and translated separation then
upgrades those chords to the hard slope mechanisms used by the corrected
assembly.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- The corrected scalar first-order mechanisms follow from the four
established Charbonnel interfaces, with no additional analytic source data. -/
theorem maxwellScalarCorrectedFirstOrderMechanisms_of_charbonnel
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S)) :
    MaxwellScalarCorrectedFirstOrderMechanisms (charbonnelClosure S) := by
  intro p hp U R hUopen hUmem hRmem hRpseudo i
  have hsmall : MaxwellOneSidedExtendedSlopeBadLociSmallness S U R i :=
    maxwellOneSidedExtendedSlopeBadLociSmallness_of_chosenContinuity
      hC hmem h21 h22 i hUopen hUmem hRmem hRpseudo
  have hchords : MaxwellCoordinateAffineChordMechanisms U R i :=
    { positiveInfinity_affineChord :=
        hRpseudo.positiveInfinity_affineChord_of_oneSidedBadSmallness
          hC h21 hp hUopen hRmem i hsmall
      negativeInfinity_affineChord :=
        hRpseudo.negativeInfinity_affineChord_of_oneSidedBadSmallness
          hC h21 hp hUopen hRmem i hsmall }
  exact
    { hard := hchords.toHardSlopeMechanisms
        hC hmem h21 h22 hUopen hUmem hRmem hRpseudo }

/-- The scalar first-order package is automatic from the four established
Charbonnel interfaces. -/
theorem maxwellScalarFirstOrderPackage_of_charbonnel
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S)) :
    MaxwellScalarFirstOrderPackage (charbonnelClosure S) :=
  maxwellScalarFirstOrderPackage_of_correctedMechanisms
    hC hmem h21 h22
      (maxwellScalarCorrectedFirstOrderMechanisms_of_charbonnel
        hC hmem h21 h22)

/-- Every finite scalar differentiability order is automatic from the four
established Charbonnel interfaces. -/
theorem maxwellScalarPseudofunctionOrderSmoothness_of_charbonnel
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S)) :
    ∀ N : ℕ, MaxwellScalarPseudofunctionOrderSmoothness
      (charbonnelClosure S) N :=
  maxwellScalarPseudofunctionOrderSmoothness_of_correctedMechanisms
    hC hmem h21 h22
      (maxwellScalarCorrectedFirstOrderMechanisms_of_charbonnel
        hC hmem h21 h22)

/-- Maxwell's full finite-order, finite-output almost-everywhere smoothness
theorem is automatic from the four established Charbonnel interfaces. -/
theorem maxwellAlmostEverywhereSmoothness_of_charbonnel
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S)) :
    MaxwellAlmostEverywhereSmoothness (charbonnelClosure S) :=
  maxwellAlmostEverywhereSmoothness_of_correctedMechanisms
    hC hmem h21 h22
      (maxwellScalarCorrectedFirstOrderMechanisms_of_charbonnel
        hC hmem h21 h22)

end AbelFormalization
