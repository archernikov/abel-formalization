import AbelFormalization.MaxwellSlopeBadDomainClosure

/-!
# Local assembly of Maxwell's coordinate slope-bad smallness

The source only needs the one-sided cluster classification on the open
pseudofunction domain.  Boundary points are handled by density: the whole
slope-bad locus lies in the closure of that domain, so any open subset of it
meets the domain in a nonempty open set.  This removes the former global
`residual_oneSidedClusterData` premise.
-/

noncomputable section

open Set MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-- The coordinate mechanisms still needed after the residual cluster
classification has been derived. -/
structure MaxwellCoordinateFirstOrderLocalMechanisms
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
  positiveStep_intermediateValue : MaxwellExtendedSlopeIntermediateValue
    (maxwellPositiveStepZeroTrace U R i)
    (maxwellPositiveStepPositiveInfinityBase U R i)
    (maxwellPositiveStepNegativeInfinityBase U R i)
  negativeStep_intermediateValue : MaxwellExtendedSlopeIntermediateValue
    (maxwellNegativeStepZeroTrace U R i)
    (maxwellNegativeStepPositiveInfinityBase U R i)
    (maxwellNegativeStepNegativeInfinityBase U R i)
  equalInfinity_continuous : ContinuousOn (maxwellChosenScalarValue R)
    (maxwellSamePositiveInfinityLocus U R i ∪
      maxwellSameNegativeInfinityLocus U R i)
  positiveInfinity_affineChord : MaxwellWS5AffineChordCrossingMechanism
    (maxwellChosenScalarValue R) i .positiveInfinity
      (maxwellSamePositiveInfinityLocus U R i)
  negativeInfinity_affineChord : MaxwellWS5AffineChordCrossingMechanism
    (maxwellChosenScalarValue R) i .negativeInfinity
      (maxwellSameNegativeInfinityLocus U R i)
  differingSlopes_translatedSeparation :
    MaxwellTranslatedOneSidedSeparationMechanism
      (maxwellChosenScalarValue R) i
      (maxwellOneSidedSlopeDisagreementLocus U R i)

/-- The local source mechanisms imply nullity of the full coordinate
slope-bad locus.  No cluster-existence or common-finite-cluster premise is
left in the statement. -/
theorem maxwellCoordinateSlopeBadLocus_volume_eq_zero_of_localMechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hUopen : IsOpen U)
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunctionOn U R)
    (hsource : MaxwellCoordinateFirstOrderLocalMechanisms U R i) :
    (volume : Measure (RealEuclidean p))
      (maxwellCoordinateSlopeBadLocus U R i) = 0 := by
  have hp : 0 < p := maxwellFinArity_pos i
  have honeSided :=
    maxwellOneSidedExtendedSlopeBadLociSmallness_of_pseudofunction_and_intermediateValue
      hC hmem h21 h22 i hU hR hRpseudo.multivalued_null
        hsource.positiveStep_intermediateValue
        hsource.negativeStep_intermediateValue
  have hhard := maxwellThreeHardSlopeCasesSmallness
    hC hmem h21 i hU hR (maxwellChosenScalarValue R)
      hsource.equalInfinity_continuous
      hsource.positiveInfinity_affineChord
      hsource.negativeInfinity_affineChord
      hsource.differingSlopes_translatedSeparation
  let cover : Set (RealEuclidean p) :=
    (maxwellPositiveStepExtendedMultivaluedLocus U R i ∪
      maxwellNegativeStepExtendedMultivaluedLocus U R i) ∪
        maxwellThreeHardSlopeCasesLocus U R i
  have hcoverMem : cover ∈ charbonnelClosure S p := by
    exact charbonnelClosure_union
      (charbonnelClosure_union
        honeSided.clusterMembership.positiveExtendedMultivalued_mem
        honeSided.clusterMembership.negativeExtendedMultivalued_mem)
      hhard.membership.union_mem
  have hcoverNull :
      (volume : Measure (RealEuclidean p)) cover = 0 := by
    exact measure_union_null
      (measure_union_null
        honeSided.positiveBadLocus.locus_volume_eq_zero
        honeSided.negativeBadLocus.locus_volume_eq_zero)
      hhard.unionSmallness.locus_volume_eq_zero
  have hcoverEmpty : interior cover = ∅ :=
    (h21 hp hcoverMem).1.mpr hcoverNull
  have hlocal : maxwellCoordinateSlopeBadLocus U R i ∩ U ⊆ cover := by
    exact
      maxwellCoordinateSlopeBadLocus_inter_domain_subset_oneSidedBad_union_threeHard
        hRpseudo hUopen i
  have hslopeEmpty :
      interior (maxwellCoordinateSlopeBadLocus U R i) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hinterior
    obtain ⟨x, hx⟩ := hinterior
    have hxClosure : x ∈ closure U :=
      maxwellCoordinateSlopeBadLocus_subset_closure_domain U R i
        (interior_subset hx)
    rw [mem_closure_iff] at hxClosure
    obtain ⟨z, hzInterior, hzU⟩ :=
      hxClosure (interior (maxwellCoordinateSlopeBadLocus U R i))
        isOpen_interior hx
    have hopen : IsOpen
        (interior (maxwellCoordinateSlopeBadLocus U R i) ∩ U) :=
      isOpen_interior.inter hUopen
    have hsubset :
        interior (maxwellCoordinateSlopeBadLocus U R i) ∩ U ⊆ cover := by
      intro w hw
      exact hlocal ⟨interior_subset hw.1, hw.2⟩
    have hintoInterior :
        interior (maxwellCoordinateSlopeBadLocus U R i) ∩ U ⊆
          interior cover :=
      hopen.subset_interior_iff.mpr hsubset
    have hz : z ∈ interior cover := hintoInterior ⟨hzInterior, hzU⟩
    simpa [hcoverEmpty] using hz
  let G : MaxwellRelation p 1 :=
    maxwellDifferenceQuotientZeroTrace U R i
  have hG : G ∈ charbonnelClosure S (p + 1) :=
    maxwellDifferenceQuotientZeroTrace_mem_charbonnelClosure hC i hU hR
  have hpositive := maxwellPositiveInfinityBase_mem_charbonnelClosure
    hC hp hG
  have hnegative := maxwellNegativeInfinityBase_mem_charbonnelClosure
    hC hp hG
  have hfinite := maxwellMultivaluedLocus_mem_charbonnelClosure
    hC hp hG
  have hslopeMem : maxwellCoordinateSlopeBadLocus U R i ∈
      charbonnelClosure S p := by
    change maxwellPositiveInfinityBase G ∪
      maxwellNegativeInfinityBase G ∪
        maxwellMultivaluedLocus G ∈ charbonnelClosure S p
    exact charbonnelClosure_union
      (charbonnelClosure_union hpositive hnegative) hfinite
  exact (h21 hp hslopeMem).1.mp hslopeEmpty

end AbelFormalization
