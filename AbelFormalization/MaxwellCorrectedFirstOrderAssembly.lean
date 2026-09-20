import AbelFormalization.MaxwellChosenInfinitySmallness
import AbelFormalization.MaxwellSlopeBadLocalAssembly
import AbelFormalization.MaxwellLocalizedOneSidedIVT

/-!
# Maxwell's corrected scalar first-order assembly

This file rebuilds the scalar first-order package using the honest open
domain on which the canonical representative has been proved differentiable.
Besides the old finite-trace exceptional locus, that domain removes the
relation-level continuity obstruction and the four source-defined one-sided
infinity bases.

The resulting theorem feeds the existing arbitrary-order and finite-output
inductions without retaining a separate differentiability premise.
-/

noncomputable section

open Set MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Remaining coordinate mechanisms -/

/-- The coordinatewise hard mechanisms still needed after continuity,
one-sided interval filling, cluster existence, residual finite-cluster
compatibility, and coordinate-line differentiability have all been derived. -/
structure MaxwellCoordinateCorrectedFirstOrderMechanisms
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
  hard : MaxwellCoordinateHardSlopeMechanisms U R i

/-- The corrected coordinate mechanisms imply nullity of the full old
coordinate slope-bad locus.  Continuity on the equal-infinity loci is
obtained internally after deleting its already-small obstruction. -/
theorem maxwellCoordinateSlopeBadLocus_volume_eq_zero_of_correctedMechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hUopen : IsOpen U)
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunctionOn U R)
    (hsource : MaxwellCoordinateCorrectedFirstOrderMechanisms U R i) :
    (volume : Measure (RealEuclidean p))
      (maxwellCoordinateSlopeBadLocus U R i) = 0 := by
  have hp : 0 < p := maxwellFinArity_pos i
  have honeSided :=
    maxwellOneSidedExtendedSlopeBadLociSmallness_of_chosenContinuity
      hC hmem h21 h22 i hUopen hU hR hRpseudo
  have hhard := maxwellThreeHardSlopeCasesSmallness_of_chosenContinuity
    hC hmem h21 i hUopen hU hR hRpseudo hsource.hard
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
  have hlocal : maxwellCoordinateSlopeBadLocus U R i ∩ U ⊆ cover :=
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
    maxwellDifferenceQuotientZeroTrace_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure i hU hR
  have hpositive := maxwellPositiveInfinityBase_mem_charbonnelClosure
    hC.toPositiveArityWeakSetStructure hp hG
  have hnegative := maxwellNegativeInfinityBase_mem_charbonnelClosure
    hC.toPositiveArityWeakSetStructure hp hG
  have hfinite := maxwellMultivaluedLocus_mem_charbonnelClosure
    hC.toPositiveArityWeakSetStructure hp hG
  have hslopeMem : maxwellCoordinateSlopeBadLocus U R i ∈
      charbonnelClosure S p := by
    change maxwellPositiveInfinityBase G ∪
      maxwellNegativeInfinityBase G ∪
        maxwellMultivaluedLocus G ∈ charbonnelClosure S p
    exact charbonnelClosure_union
      (charbonnelClosure_union hpositive hnegative) hfinite
  exact (h21 hp hslopeMem).1.mp hslopeEmpty

/-! ## The corrected common exceptional set -/

/-- The common closed exceptional set used by the corrected first-order
package. -/
def maxwellCorrectedFirstOrderExceptionalLocus {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    Set (RealEuclidean p) :=
  (maxwellChosenContinuityExceptionalLocus U R ∪
    maxwellFirstOrderExceptionalLocus U R) ∪
      maxwellChosenOneSidedInfinityExceptionalLocus U R

theorem isClosed_maxwellCorrectedFirstOrderExceptionalLocus
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    IsClosed (maxwellCorrectedFirstOrderExceptionalLocus U R) := by
  exact
    ((isClosed_maxwellChosenContinuityExceptionalLocus U R).union
      (isClosed_maxwellFirstOrderExceptionalLocus U R)).union
        (isClosed_maxwellChosenOneSidedInfinityExceptionalLocus U R)

/-- The corrected derivative regular domain is exactly the complement of
the preceding common exceptional set inside `U`. -/
theorem maxwellChosenDerivativeRegularDomain_eq_diff_correctedExceptional
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) :
    maxwellChosenDerivativeRegularDomain U R =
      U \ maxwellCorrectedFirstOrderExceptionalLocus U R := by
  ext x
  simp only [maxwellChosenDerivativeRegularDomain,
    maxwellChosenLineRegularDomain,
    maxwellCorrectedFirstOrderExceptionalLocus,
    Set.mem_sdiff, Set.mem_union, not_or]
  tauto

/-! ## Family-wide first-order assembly -/

/-- The only family-wide analytic mechanisms retained by the corrected
first-order theorem. -/
def MaxwellScalarCorrectedFirstOrderMechanisms
    (C : EuclideanSetFamily) : Prop :=
  ∀ {p : ℕ}, 0 < p →
    ∀ (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1),
      IsOpen U → U ∈ C p → R ∈ C (p + 1) →
      IsMaxwellPseudofunctionOn U R →
      ∀ i : Fin p,
        MaxwellCoordinateCorrectedFirstOrderMechanisms U R i

/-- The corrected mechanisms produce the scalar first-order package needed
by the arbitrary differentiability-order induction.  Differentiability of
the canonical representative is a theorem on the corrected regular domain,
not a field of the source-mechanism interface. -/
theorem maxwellScalarFirstOrderPackage_of_correctedMechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    (hsource : MaxwellScalarCorrectedFirstOrderMechanisms
      (charbonnelClosure S)) :
    MaxwellScalarFirstOrderPackage (charbonnelClosure S) := by
  intro p hp U R hUopen hUmem hRmem hRpseudo
  let A0 : Set (RealEuclidean p) :=
    maxwellCorrectedFirstOrderExceptionalLocus U R
  let f : RealEuclidean p → ℝ := maxwellChosenScalarValue R
  let H : Fin p → MaxwellRelation p 1 :=
    fun i ↦ maxwellExceptionalDerivativePseudograph U R A0 i
  have hmechanisms : ∀ i : Fin p,
      MaxwellCoordinateCorrectedFirstOrderMechanisms U R i :=
    hsource hp U R hUopen hUmem hRmem hRpseudo
  have hslopeNull : ∀ i : Fin p,
      (volume : Measure (RealEuclidean p))
        (maxwellCoordinateSlopeBadLocus U R i) = 0 := by
    intro i
    exact
      maxwellCoordinateSlopeBadLocus_volume_eq_zero_of_correctedMechanisms
        hC hmem h21 h22 i hUopen hUmem hRmem hRpseudo
          (hmechanisms i)
  have hrawNull : ∀ i : Fin p,
      (volume : Measure (RealEuclidean p))
        (maxwellCoordinateRawBadLocus U R i) = 0 := by
    intro i
    rw [maxwellCoordinateRawBadLocus_eq_multivalued_union_slopeBad]
    exact measure_union_null hRpseudo.multivalued_null (hslopeNull i)
  have hcoordinateMem : ∀ i : Fin p,
      maxwellCoordinateExceptionalLocus U R i ∈
        charbonnelClosure S p := by
    intro i
    exact maxwellCoordinateExceptionalLocus_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure i hUmem hRmem
  have hcoordinateEmpty : ∀ i : Fin p,
      interior (maxwellCoordinateExceptionalLocus U R i) = ∅ := by
    intro i
    have hrawMem : maxwellCoordinateRawBadLocus U R i ∈
        charbonnelClosure S p :=
      maxwellCoordinateRawBadLocus_mem_charbonnelClosure
        hC.toPositiveArityWeakSetStructure i hUmem hRmem
    exact (h21 hp hrawMem).2.1.mp (hrawNull i)
  have hcoordinateNull : ∀ i : Fin p,
      (volume : Measure (RealEuclidean p))
        (maxwellCoordinateExceptionalLocus U R i) = 0 := by
    intro i
    exact (h21 hp (hcoordinateMem i)).1.mp (hcoordinateEmpty i)
  have hfirstMem : maxwellFirstOrderExceptionalLocus U R ∈
      charbonnelClosure S p :=
    maxwellFirstOrderExceptionalLocus_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hUmem hRmem
  have hfirstNull :
      (volume : Measure (RealEuclidean p))
        (maxwellFirstOrderExceptionalLocus U R) = 0 := by
    unfold maxwellFirstOrderExceptionalLocus
    exact measure_iUnion_null hcoordinateNull
  have hcontinuitySmall :=
    maxwellChosenContinuityBadLocusSmallness_of_theorem21
      hC h21 hp hRmem hRpseudo
  have hhard : ∀ i : Fin p,
      MaxwellCoordinateHardSlopeMechanisms U R i :=
    fun i ↦ (hmechanisms i).hard
  have hinfinitySmall :=
    maxwellChosenOneSidedInfinityBadLocusSmallness_of_hardMechanisms
      hC hmem h21 hp hUopen hUmem hRmem hRpseudo hhard
  have hA0closed : IsClosed A0 :=
    isClosed_maxwellCorrectedFirstOrderExceptionalLocus U R
  have hA0mem : A0 ∈ charbonnelClosure S p := by
    dsimp only [A0, maxwellCorrectedFirstOrderExceptionalLocus]
    exact charbonnelClosure_union
      (charbonnelClosure_union
        hcontinuitySmall.exceptionalLocus_mem hfirstMem)
      hinfinitySmall.exceptionalLocus_mem
  have hA0null : (volume : Measure (RealEuclidean p)) A0 = 0 := by
    dsimp only [A0, maxwellCorrectedFirstOrderExceptionalLocus]
    exact measure_union_null
      (measure_union_null
        hcontinuitySmall.exceptionalLocus_volume_eq_zero hfirstNull)
      hinfinitySmall.exceptionalLocus_volume_eq_zero
  have hA0empty : interior A0 = ∅ :=
    (h21 hp hA0mem).1.mpr hA0null
  have hmultiSubset : maxwellMultivaluedLocus R ⊆ A0 := by
    let i0 : Fin p := ⟨0, hp⟩
    intro x hx
    change x ∈
      (maxwellChosenContinuityExceptionalLocus U R ∪
        maxwellFirstOrderExceptionalLocus U R) ∪
          maxwellChosenOneSidedInfinityExceptionalLocus U R
    apply Or.inl
    apply Or.inr
    apply maxwellCoordinateExceptionalLocus_subset_firstOrder U R i0
    apply subset_closure
    unfold maxwellCoordinateRawBadLocus
    aesop
  have hRrep : MaxwellRelation.RepresentsOn R (U \ A0)
      (fun x : RealEuclidean p ↦ fun _ : Fin 1 ↦ f x) :=
    hRpseudo.representsOn_maxwellChosenScalarValue_of_subset hmultiSubset
  have hfdiff : ∀ x ∈ U \ A0, DifferentiableAt ℝ f x := by
    intro x hx
    apply hRpseudo.differentiableAt_chosenScalarValue_derivativeRegularDomain
      hUopen
    rw [maxwellChosenDerivativeRegularDomain_eq_diff_correctedExceptional]
    exact hx
  refine ⟨A0, f, H, hA0closed, hA0mem, hA0empty, hRrep, hfdiff, ?_⟩
  intro i
  have hHmem : H i ∈ charbonnelClosure S (p + 1) :=
    maxwellExceptionalDerivativePseudograph_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp i hUmem hA0mem hRmem
  have htraceMulti : maxwellMultivaluedLocus
      (maxwellDifferenceQuotientZeroTrace U R i) ⊆ A0 := by
    intro x hx
    change x ∈
      (maxwellChosenContinuityExceptionalLocus U R ∪
        maxwellFirstOrderExceptionalLocus U R) ∪
          maxwellChosenOneSidedInfinityExceptionalLocus U R
    exact Or.inl <| Or.inr <|
      maxwellCoordinateExceptionalLocus_subset_firstOrder U R i <|
        subset_closure <| by
          unfold maxwellCoordinateRawBadLocus
          aesop
  have hHpseudo : IsMaxwellPseudofunctionOn U (H i) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy⟩ := hx
      exact
        ((realEuclideanAppend_mem_maxwellExceptionalDerivativePseudograph_iff
          U R A0 i x y).mp hy).1
    · intro x hx
      by_cases hxA : x ∈ A0
      · exact ⟨(1 : RealEuclidean 1),
          (realEuclideanAppend_mem_maxwellExceptionalDerivativePseudograph_iff
            U R A0 i x (1 : RealEuclidean 1)).mpr
              ⟨hx, Or.inr ⟨hxA, rfl⟩⟩⟩
      · let d : RealEuclidean 1 := fun _ : Fin 1 ↦
          fderiv ℝ f x (Pi.single i 1 : RealEuclidean p)
        have hdTrace : realEuclideanAppend x d ∈
            maxwellDifferenceQuotientZeroTrace U R i :=
          hRpseudo.chosenScalar_directionalDerivative_mem_trace
            hUopen i hx (hfdiff x ⟨hx, hxA⟩)
        exact ⟨d,
          (realEuclideanAppend_mem_maxwellExceptionalDerivativePseudograph_iff
            U R A0 i x d).mpr ⟨hx, Or.inl hdTrace⟩⟩
    · unfold IsMaxwellPseudofunction
      exact measure_mono_null
        (maxwellMultivaluedLocus_exceptionalDerivativePseudograph_subset
          U R A0 i htraceMulti) hA0null
  refine ⟨hHmem, hHpseudo, ?_⟩
  intro x hx y
  let d : RealEuclidean 1 := fun _ : Fin 1 ↦
    fderiv ℝ f x ((Pi.basisFun ℝ (Fin p)) i)
  have hdTrace : realEuclideanAppend x d ∈
      maxwellDifferenceQuotientZeroTrace U R i := by
    have hchosen :=
      hRpseudo.chosenScalar_directionalDerivative_mem_trace
        hUopen i hx.1 (hfdiff x hx)
    simpa only [f, d, pi_basisFun_eq_single] using hchosen
  have hdH : realEuclideanAppend x d ∈ H i :=
    (maxwellExceptionalDerivativePseudograph_iff_zeroTrace_of_not_exceptional
      U R A0 i hx d).mpr hdTrace
  constructor
  · intro hy
    by_contra hne
    have hmulti : x ∈ maxwellMultivaluedLocus (H i) :=
      ⟨y, d, hy, hdH, hne⟩
    exact hx.2
      (maxwellMultivaluedLocus_exceptionalDerivativePseudograph_subset
        U R A0 i htraceMulti hmulti)
  · intro hy
    change y = d at hy
    simpa only [hy] using hdH

/-- Every finite scalar differentiability order follows from the corrected
mechanisms. -/
theorem maxwellScalarPseudofunctionOrderSmoothness_of_correctedMechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    (hsource : MaxwellScalarCorrectedFirstOrderMechanisms
      (charbonnelClosure S)) :
    ∀ N : ℕ, MaxwellScalarPseudofunctionOrderSmoothness
      (charbonnelClosure S) N :=
  maxwellScalarPseudofunctionOrderSmoothness_of_firstOrderPackage hC
    (maxwellScalarFirstOrderPackage_of_correctedMechanisms
      hC hmem h21 h22 hsource)

/-- Maxwell's full finite-order, finite-output almost-everywhere smoothness
theorem follows from the corrected coordinate mechanisms. -/
theorem maxwellAlmostEverywhereSmoothness_of_correctedMechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    (hsource : MaxwellScalarCorrectedFirstOrderMechanisms
      (charbonnelClosure S)) :
    MaxwellAlmostEverywhereSmoothness (charbonnelClosure S) :=
  maxwellAlmostEverywhereSmoothness_of_scalarPseudofunctionOrderSmoothness
    hC.toPositiveArityWeakSetStructure
    (maxwellScalarPseudofunctionOrderSmoothness_of_correctedMechanisms
      hC hmem h21 h22 hsource)

end AbelFormalization
