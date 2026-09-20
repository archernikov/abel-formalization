import AbelFormalization.MaxwellChosenContinuityBridge
import AbelFormalization.MaxwellSlopeBadDomainClosure

/-!
# Smallness of the source-defined one-sided infinity obstruction

The corrected differentiability domain for Maxwell's canonical scalar
representative removes the four loci obtained by reciprocating a one-sided
difference quotient before taking its zero-step trace.  This file proves the
set-theoretic and topological reductions needed to show that their finite
union is small.

The equal-infinity argument only needs continuity after deleting the already
small relation-level continuity obstruction.  Thus no global continuity
hypothesis on the canonical representative is introduced here.
-/

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Domain control -/

/-- Every source-defined one-sided infinity base lies in the closure of the
open domain from which its quotient points are drawn. -/
theorem maxwellOneSidedInfinityBase_subset_closure_domain
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (infinity : MaxwellSlopeInfinitySign) :
    maxwellOneSidedInfinityBase U R i side infinity ⊆ closure U := by
  intro x hx
  obtain ⟨happroach⟩ :=
    (mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
      U R i side infinity x).mp hx
  let hdivergent := happroach.toDivergentSlopeApproach
  have hsourceU : ∀ n, (hdivergent.source n).1 ∈ U := by
    intro n
    have hn := hdivergent.point_mem n
    rw [mem_maxwellStepLastDifferenceQuotientRelation_append_iff,
      realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff]
      at hn
    exact hn.1
  have hsourceLimit :
      Tendsto (fun n ↦ (hdivergent.source n).1) atTop (nhds x) := by
    have h := continuous_fst.tendsto (x, 0) |>.comp
      hdivergent.source_tendsto
    simpa only [Function.comp_def] using h
  exact mem_closure_iff_seq_limit.mpr
    ⟨fun n ↦ (hdivergent.source n).1, hsourceU, hsourceLimit⟩

/-- The finite union used by the corrected derivative domain also remains
inside `closure U`. -/
theorem maxwellChosenOneSidedInfinityBadLocus_subset_closure_domain
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    maxwellChosenOneSidedInfinityBadLocus U R ⊆ closure U := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨side, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨infinity, hx⟩
  exact maxwellOneSidedInfinityBase_subset_closure_domain
    U R i side infinity hx

/-! ## Pointwise classification -/

/-- At an interior domain point, one source-defined infinite cluster and a
cluster on the other side give either equal infinities or a cross-side
disagreement.  Hence every such point lies in one of Maxwell's three hard
cases. -/
theorem maxwellOneSidedInfinityBase_inter_domain_subset_threeHard
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (infinity : MaxwellSlopeInfinitySign) :
    maxwellOneSidedInfinityBase U R i side infinity ∩ U ⊆
      maxwellThreeHardSlopeCasesLocus U R i := by
  intro x hx
  have hclusters := hR.twoSidedExtendedSlopeFibers_nonempty hU i hx.2
  cases side with
  | positive =>
      cases infinity with
      | positive =>
          obtain ⟨b, hb⟩ := hclusters.2
          by_cases hab : MaxwellExtendedSlopeValue.positiveInfinity = b
          · subst b
            exact Or.inl (Or.inl ⟨hx.1, hb⟩)
          · exact Or.inr
              ⟨.positiveInfinity, b, hx.1, hb, hab⟩
      | negative =>
          obtain ⟨b, hb⟩ := hclusters.2
          by_cases hab : MaxwellExtendedSlopeValue.negativeInfinity = b
          · subst b
            exact Or.inl (Or.inr ⟨hx.1, hb⟩)
          · exact Or.inr
              ⟨.negativeInfinity, b, hx.1, hb, hab⟩
  | negative =>
      cases infinity with
      | positive =>
          obtain ⟨a, ha⟩ := hclusters.1
          by_cases hab : a = MaxwellExtendedSlopeValue.positiveInfinity
          · subst a
            exact Or.inl (Or.inl ⟨ha, hx.1⟩)
          · exact Or.inr
              ⟨a, .positiveInfinity, ha, hx.1, hab⟩
      | negative =>
          obtain ⟨a, ha⟩ := hclusters.1
          by_cases hab : a = MaxwellExtendedSlopeValue.negativeInfinity
          · subst a
            exact Or.inl (Or.inr ⟨ha, hx.1⟩)
          · exact Or.inr
              ⟨a, .negativeInfinity, ha, hx.1, hab⟩

/-- The full finite union is locally covered by the coordinatewise hard
cases on the actual pseudofunction domain. -/
theorem maxwellChosenOneSidedInfinityBadLocus_inter_domain_subset_hardUnion
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U) :
    maxwellChosenOneSidedInfinityBadLocus U R ∩ U ⊆
      ⋃ i : Fin p, maxwellThreeHardSlopeCasesLocus U R i := by
  intro x hx
  rcases Set.mem_iUnion.mp hx.1 with ⟨i, hxBase⟩
  rcases Set.mem_iUnion.mp hxBase with ⟨side, hxBase⟩
  rcases Set.mem_iUnion.mp hxBase with ⟨infinity, hxBase⟩
  exact Set.mem_iUnion_of_mem i
    (maxwellOneSidedInfinityBase_inter_domain_subset_threeHard
      hR hU i side infinity ⟨hxBase, hx.2⟩)

/-! ## Family membership -/

/-- The union over the two step sides and two infinity signs for one fixed
coordinate is the explicit four-piece finite union. -/
theorem iUnion_maxwellOneSidedInfinityBase_eq_four
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    (⋃ side : MaxwellOneSidedStep,
      ⋃ infinity : MaxwellSlopeInfinitySign,
        maxwellOneSidedInfinityBase U R i side infinity) =
      (maxwellPositiveStepPositiveInfinityBase U R i ∪
        maxwellPositiveStepNegativeInfinityBase U R i) ∪
      (maxwellNegativeStepPositiveInfinityBase U R i ∪
        maxwellNegativeStepNegativeInfinityBase U R i) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨side, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨infinity, hx⟩
    cases side <;> cases infinity <;> aesop
  · intro hx
    rcases hx with (hx | hx) | (hx | hx)
    · exact Set.mem_iUnion_of_mem .positive <|
        Set.mem_iUnion_of_mem .positive hx
    · exact Set.mem_iUnion_of_mem .positive <|
        Set.mem_iUnion_of_mem .negative hx
    · exact Set.mem_iUnion_of_mem .negative <|
        Set.mem_iUnion_of_mem .positive hx
    · exact Set.mem_iUnion_of_mem .negative <|
        Set.mem_iUnion_of_mem .negative hx

/-- The raw source-defined infinity obstruction is a member of the
Charbonnel closure. -/
theorem maxwellChosenOneSidedInfinityBadLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellChosenOneSidedInfinityBadLocus U R ∈
      charbonnelClosure S p := by
  unfold maxwellChosenOneSidedInfinityBadLocus
  apply charbonnelClosure_iUnion_fin hC hp
  intro i
  rw [iUnion_maxwellOneSidedInfinityBase_eq_four]
  have hclusters := maxwellOneSidedExtendedSlopeClusterMembership
    hC hmem i hU hR
  exact charbonnelClosure_union
    (charbonnelClosure_union
      hclusters.positiveStepPositiveInfinity_mem
      hclusters.positiveStepNegativeInfinity_mem)
    (charbonnelClosure_union
      hclusters.negativeStepPositiveInfinity_mem
      hclusters.negativeStepNegativeInfinity_mem)

/-- The closed enlargement removed by the corrected derivative domain is
also a Charbonnel-closure member. -/
theorem maxwellChosenOneSidedInfinityExceptionalLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellChosenOneSidedInfinityExceptionalLocus U R ∈
      charbonnelClosure S p := by
  exact charbonnelClosure_topologicalClosure
    (maxwellChosenOneSidedInfinityBadLocus_mem_charbonnelClosure
      hC hmem hp hU hR)

/-! ## Hard-case smallness with continuity localized off its obstruction -/

/-- An equal-infinity affine-chord mechanism only needs continuity after a
closed nowhere-dense set has been deleted.  The assumption `A ⊆ closure U`
ensures that every hypothetical open part of `A` first meets `U`; deleting
the exceptional set then leaves a nonempty open patch on which the usual
chord contradiction applies. -/
theorem interior_eq_empty_of_ws5AffineChordCrossing_off_closed
    {p : ℕ} {f : RealEuclidean p → ℝ} {i : Fin p}
    {s : MaxwellSameInfinitySign}
    {U E A : Set (RealEuclidean p)}
    (hUopen : IsOpen U) (hAclosure : A ⊆ closure U)
    (hEclosed : IsClosed E) (hEempty : interior E = ∅)
    (hf : ContinuousOn f (U \ E))
    (hextract : MaxwellWS5AffineChordCrossingMechanism f i s A) :
    interior A = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hAinterior
  obtain ⟨x, hx⟩ := hAinterior
  have hxClosure : x ∈ closure U := hAclosure (interior_subset hx)
  rw [mem_closure_iff] at hxClosure
  obtain ⟨z, hzInterior, hzU⟩ :=
    hxClosure (interior A) isOpen_interior hx
  let V : Set (RealEuclidean p) := interior A ∩ U
  have hVopen : IsOpen V := isOpen_interior.inter hUopen
  have hVnonempty : V.Nonempty := ⟨z, hzInterior, hzU⟩
  have hVnotSubset : ¬ V ⊆ E := by
    intro hsubset
    have hVinterior : V ⊆ interior E :=
      hVopen.subset_interior_iff.mpr hsubset
    obtain ⟨w, hw⟩ := hVnonempty
    have hwE : w ∈ interior E := hVinterior hw
    simpa [hEempty] using hwE
  obtain ⟨w, hwV, hwE⟩ := Set.not_subset.mp hVnotSubset
  let W : Set (RealEuclidean p) := V \ E
  have hWopen : IsOpen W := hVopen.sdiff hEclosed
  have hWnonempty : W.Nonempty := ⟨w, hwV, hwE⟩
  have hWsubsetA : W ⊆ A := by
    intro y hy
    exact interior_subset hy.1.1
  obtain ⟨hchord⟩ := hextract W hWopen hWnonempty hWsubsetA
  apply hchord.false
  apply hf.mono
  intro y hy
  exact ⟨hy.1.2, hy.2⟩

/-- The three genuinely geometric mechanisms left in Maxwell's hard-case
argument for one coordinate.  Continuity is supplied canonically outside
the already controlled relation-level exceptional locus. -/
structure MaxwellCoordinateHardSlopeMechanisms
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
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

/-- Maxwell's three hard slope cases are small without assuming continuity
on the entire equal-infinity loci.  The canonical representative is
continuous on `U` away from its relation-level exceptional locus, and that
closed exceptional locus already has empty interior. -/
theorem maxwellThreeHardSlopeCasesSmallness_of_chosenContinuity
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hUopen : IsOpen U)
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunctionOn U R)
    (hsource : MaxwellCoordinateHardSlopeMechanisms U R i) :
    MaxwellThreeHardSlopeCasesSmallness S U R i := by
  have hp : 0 < p := maxwellFinArity_pos i
  let E : Set (RealEuclidean p) :=
    maxwellChosenContinuityExceptionalLocus U R
  have hEsmall :=
    maxwellChosenContinuityBadLocusSmallness_of_theorem21
      hC h21 hp hR hRpseudo
  have hEclosed : IsClosed E :=
    isClosed_maxwellChosenContinuityExceptionalLocus U R
  have hEempty : interior E = ∅ := hEsmall.exceptionalLocus_interior_eq_empty
  have hf : ContinuousOn (maxwellChosenScalarValue R) (U \ E) := by
    simpa only [E] using
      hRpseudo.continuousOn_chosenScalarValue_compl_exceptional
  have hpositiveClosure :
      maxwellSamePositiveInfinityLocus U R i ⊆ closure U := by
    intro x hx
    exact maxwellOneSidedInfinityBase_subset_closure_domain
      U R i .positive .positive hx.1
  have hnegativeClosure :
      maxwellSameNegativeInfinityLocus U R i ⊆ closure U := by
    intro x hx
    exact maxwellOneSidedInfinityBase_subset_closure_domain
      U R i .positive .negative hx.1
  have hpositiveEmpty :
      interior (maxwellSamePositiveInfinityLocus U R i) = ∅ :=
    interior_eq_empty_of_ws5AffineChordCrossing_off_closed
      hUopen hpositiveClosure hEclosed hEempty hf
        hsource.positiveInfinity_affineChord
  have hnegativeEmpty :
      interior (maxwellSameNegativeInfinityLocus U R i) = ∅ :=
    interior_eq_empty_of_ws5AffineChordCrossing_off_closed
      hUopen hnegativeClosure hEclosed hEempty hf
        hsource.negativeInfinity_affineChord
  have hdisagreementEmpty :
      interior (maxwellOneSidedSlopeDisagreementLocus U R i) = ∅ :=
    interior_eq_empty_of_translatedOneSidedSeparation
      hsource.differingSlopes_translatedSeparation
  have hmembership := maxwellThreeHardSlopeCasesMembership
    hC.toPositiveArityWeakSetStructure hmem i hU hR
  have hpositiveSmall := maxwellSlopeBaseLocusSmallness_of_interior_eq_empty
    h21 hp hmembership.samePositiveInfinity_mem hpositiveEmpty
  have hnegativeSmall := maxwellSlopeBaseLocusSmallness_of_interior_eq_empty
    h21 hp hmembership.sameNegativeInfinity_mem hnegativeEmpty
  have hdisagreementSmall :=
    maxwellSlopeBaseLocusSmallness_of_interior_eq_empty h21 hp
      hmembership.disagreement_mem hdisagreementEmpty
  have hunionNull :
      (volume : Measure (RealEuclidean p))
        (maxwellThreeHardSlopeCasesLocus U R i) = 0 := by
    exact measure_union_null
      (measure_union_null hpositiveSmall.locus_volume_eq_zero
        hnegativeSmall.locus_volume_eq_zero)
      hdisagreementSmall.locus_volume_eq_zero
  have hunionSmall := maxwellSlopeBaseLocusSmallness_of_volume_eq_zero
    h21 hp hmembership.union_mem hunionNull
  exact
    { membership := hmembership
      samePositiveInfinity := hpositiveSmall
      sameNegativeInfinity := hnegativeSmall
      disagreement := hdisagreementSmall
      unionSmallness := hunionSmall }

/-! ## Smallness of the corrected source-infinity exceptional set -/

/-- Family membership, nullity, and empty interior for the raw union of all
source-defined one-sided infinity bases and for its closure. -/
structure MaxwellChosenOneSidedInfinityBadLocusSmallness
    (S : EuclideanSetFamily) {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) : Prop where
  badLocus_mem : maxwellChosenOneSidedInfinityBadLocus U R ∈
    charbonnelClosure S p
  badLocus_volume_eq_zero :
    (volume : Measure (RealEuclidean p))
      (maxwellChosenOneSidedInfinityBadLocus U R) = 0
  badLocus_interior_eq_empty :
    interior (maxwellChosenOneSidedInfinityBadLocus U R) = ∅
  exceptionalLocus_mem : maxwellChosenOneSidedInfinityExceptionalLocus U R ∈
    charbonnelClosure S p
  exceptionalLocus_interior_eq_empty :
    interior (maxwellChosenOneSidedInfinityExceptionalLocus U R) = ∅
  exceptionalLocus_volume_eq_zero :
    (volume : Measure (RealEuclidean p))
      (maxwellChosenOneSidedInfinityExceptionalLocus U R) = 0

/-- The hard-case mechanisms in every coordinate imply smallness of the
entire source-defined infinity obstruction.  No one-sided finite IVT or
residual cluster-data assumption is needed for this conclusion. -/
theorem maxwellChosenOneSidedInfinityBadLocusSmallness_of_hardMechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hUopen : IsOpen U)
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunctionOn U R)
    (hsource : ∀ i : Fin p,
      MaxwellCoordinateHardSlopeMechanisms U R i) :
    MaxwellChosenOneSidedInfinityBadLocusSmallness S U R := by
  have hhard : ∀ i : Fin p,
      MaxwellThreeHardSlopeCasesSmallness S U R i := by
    intro i
    exact maxwellThreeHardSlopeCasesSmallness_of_chosenContinuity
      hC hmem h21 i hUopen hU hR hRpseudo (hsource i)
  let cover : Set (RealEuclidean p) :=
    ⋃ i : Fin p, maxwellThreeHardSlopeCasesLocus U R i
  have hcoverMem : cover ∈ charbonnelClosure S p := by
    dsimp only [cover]
    exact charbonnelClosure_iUnion_fin
      hC.toPositiveArityWeakSetStructure hp _
        (fun i ↦ (hhard i).membership.union_mem)
  have hcoverNull :
      (volume : Measure (RealEuclidean p)) cover = 0 := by
    dsimp only [cover]
    exact measure_iUnion_null
      (fun i ↦ (hhard i).unionSmallness.locus_volume_eq_zero)
  have hcoverEmpty : interior cover = ∅ :=
    (h21 hp hcoverMem).1.mpr hcoverNull
  have hlocal :
      maxwellChosenOneSidedInfinityBadLocus U R ∩ U ⊆ cover := by
    exact
      maxwellChosenOneSidedInfinityBadLocus_inter_domain_subset_hardUnion
        hRpseudo hUopen
  have hbadClosure :
      maxwellChosenOneSidedInfinityBadLocus U R ⊆ closure U :=
    maxwellChosenOneSidedInfinityBadLocus_subset_closure_domain U R
  have hbadEmpty :
      interior (maxwellChosenOneSidedInfinityBadLocus U R) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hinterior
    obtain ⟨x, hx⟩ := hinterior
    have hxClosure : x ∈ closure U := hbadClosure (interior_subset hx)
    rw [mem_closure_iff] at hxClosure
    obtain ⟨z, hzInterior, hzU⟩ :=
      hxClosure
        (interior (maxwellChosenOneSidedInfinityBadLocus U R))
        isOpen_interior hx
    have hopen : IsOpen
        (interior (maxwellChosenOneSidedInfinityBadLocus U R) ∩ U) :=
      isOpen_interior.inter hUopen
    have hsubset :
        interior (maxwellChosenOneSidedInfinityBadLocus U R) ∩ U ⊆
          cover := by
      intro w hw
      exact hlocal ⟨interior_subset hw.1, hw.2⟩
    have hintoInterior :
        interior (maxwellChosenOneSidedInfinityBadLocus U R) ∩ U ⊆
          interior cover :=
      hopen.subset_interior_iff.mpr hsubset
    have hz : z ∈ interior cover := hintoInterior ⟨hzInterior, hzU⟩
    simpa [hcoverEmpty] using hz
  have hbadMem :=
    maxwellChosenOneSidedInfinityBadLocus_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hmem hp hU hR
  have hbadNull :
      (volume : Measure (RealEuclidean p))
        (maxwellChosenOneSidedInfinityBadLocus U R) = 0 :=
    (h21 hp hbadMem).1.mp hbadEmpty
  have hexceptionalMem :=
    maxwellChosenOneSidedInfinityExceptionalLocus_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hmem hp hU hR
  have hexceptionalEmpty :
      interior (maxwellChosenOneSidedInfinityExceptionalLocus U R) = ∅ :=
    (h21 hp hbadMem).2.1.mp hbadNull
  have hexceptionalNull :
      (volume : Measure (RealEuclidean p))
        (maxwellChosenOneSidedInfinityExceptionalLocus U R) = 0 :=
    (h21 hp hbadMem).2.2.mp hexceptionalEmpty
  exact
    { badLocus_mem := hbadMem
      badLocus_volume_eq_zero := hbadNull
      badLocus_interior_eq_empty := hbadEmpty
      exceptionalLocus_mem := hexceptionalMem
      exceptionalLocus_interior_eq_empty := hexceptionalEmpty
      exceptionalLocus_volume_eq_zero := hexceptionalNull }

end AbelFormalization
