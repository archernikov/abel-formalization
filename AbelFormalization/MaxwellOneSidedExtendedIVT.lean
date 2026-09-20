import AbelFormalization.MaxwellOneSidedSlopeIVT

/-!
# Exact extended one-sided intermediate values

This file removes the finite-anchor hypothesis from the final form of the
one-sided slope IVT used in Figueiredo--Maxwell Lemma 2.3.3.  A finite trace
point already carries an actual nonzero-step sequence, so it supplies the
finite comparison sequence needed against one infinite slope.  When both
infinities occur, their two divergent ordinary-slope sequences can be used
directly.

The unrestricted theorem retains the necessary premise that every relevant
closure fiber is based in the open representative domain.  The restricted
theorem, which intersects all three kinds of fibers with that domain, needs
no such global premise.
-/

noncomputable section

open Set Filter Topology
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Finite trace points are direct finite anchors -/

/-- A genuine finite one-sided trace approach is already the direct finite
comparison sequence needed by the shrinking-core IVT. -/
def MaxwellOneSidedSlopeApproach.toDirectFiniteSlopeAnchor
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    {side : MaxwellOneSidedStep} {x : RealEuclidean p} {a : ℝ}
    (h : MaxwellOneSidedSlopeApproach U R i side x a)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z)) :
    MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x a where
  source n := maxwellOneSidedApproachSource side (h.point n)
  source_mem n := (h.source_mem_domain_of_representsOn hrep n).1
  source_tendsto := h.source_tendsto
  quotient_tendsto := by
    convert h.value_tendsto using 1
    funext n
    exact (h.source_mem_domain_of_representsOn hrep n).2.symm

/-! ## The three extended cases -/

/-- A finite trace value and a positive-infinity trace fill every strictly
larger finite value.  No separately postulated anchor is needed: the finite
trace membership supplies it. -/
theorem maxwellOneSidedStepZeroTrace_above_of_positiveInfinity_and_finiteTrace
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ U) {a b : ℝ}
    (ha : realEuclideanAppend x (fun _ : Fin 1 ↦ a) ∈
      maxwellOneSidedStepZeroTrace U R i side)
    (hinfinity : x ∈
      maxwellOneSidedInfinityBase U R i side .positive)
    (hab : a < b) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ b) ∈
      maxwellOneSidedStepZeroTrace U R i side := by
  obtain ⟨hfinite⟩ :=
    (mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
      U R i side x a).mp ha
  exact maxwellOneSidedStepZeroTrace_above_of_positiveInfinity_and_anchor
    i side hUopen hf hrep hx
    (hfinite.toDirectFiniteSlopeAnchor hrep) hinfinity hab

/-- A negative-infinity trace and a finite trace value fill every strictly
smaller finite value. -/
theorem maxwellOneSidedStepZeroTrace_below_of_negativeInfinity_and_finiteTrace
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ U) {a b : ℝ}
    (ha : realEuclideanAppend x (fun _ : Fin 1 ↦ a) ∈
      maxwellOneSidedStepZeroTrace U R i side)
    (hinfinity : x ∈
      maxwellOneSidedInfinityBase U R i side .negative)
    (hba : b < a) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ b) ∈
      maxwellOneSidedStepZeroTrace U R i side := by
  obtain ⟨hfinite⟩ :=
    (mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
      U R i side x a).mp ha
  exact maxwellOneSidedStepZeroTrace_below_of_negativeInfinity_and_anchor
    i side hUopen hf hrep hx
    (hfinite.toDirectFiniteSlopeAnchor hrep) hinfinity hba

/-- Opposite infinite one-sided clusters fill every finite value between
them.  The proof uses the two divergent ordinary-slope sequences directly. -/
theorem maxwellOneSidedStepZeroTrace_of_bothInfinities
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ U) (y : ℝ)
    (hpositive : x ∈
      maxwellOneSidedInfinityBase U R i side .positive)
    (hnegative : x ∈
      maxwellOneSidedInfinityBase U R i side .negative) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
      maxwellOneSidedStepZeroTrace U R i side := by
  obtain ⟨hpositiveReciprocal⟩ :=
    (mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
      U R i side .positive x).mp hpositive
  obtain ⟨hnegativeReciprocal⟩ :=
    (mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
      U R i side .negative x).mp hnegative
  let hpositiveDivergent :=
    hpositiveReciprocal.toDivergentSlopeApproach
  let hnegativeDivergent :=
    hnegativeReciprocal.toDivergentSlopeApproach
  have hpositiveTop :
      Tendsto hpositiveDivergent.slope atTop atTop := by
    simpa only [MaxwellSlopeInfinitySign.divergenceFilter] using
      hpositiveDivergent.slope_tendsto
  have hnegativeBot :
      Tendsto hnegativeDivergent.slope atTop atBot := by
    simpa only [MaxwellSlopeInfinitySign.divergenceFilter] using
      hnegativeDivergent.slope_tendsto
  have hnegativeBelow : ∀ᶠ n in atTop,
      hnegativeDivergent.slope n < y :=
    hnegativeBot.eventually_lt_atBot y
  have hpositiveAbove : ∀ᶠ n in atTop,
      y < hpositiveDivergent.slope n :=
    hpositiveTop.eventually_gt_atTop y
  exact maxwellOneSidedStepZeroTrace_mem_of_straddling_sources
    i side hUopen hf hrep hx
    hnegativeDivergent.source_tendsto
    hpositiveDivergent.source_tendsto
    hnegativeDivergent.source_step_pos
    hpositiveDivergent.source_step_pos
    (fun n ↦
      hnegativeDivergent.source_mem_domain_of_representsOn hrep n)
    (fun n ↦
      hpositiveDivergent.source_mem_domain_of_representsOn hrep n)
    (hnegativeBelow.and hpositiveAbove)

/-! ## Exact source-shaped extended IVT packages -/

/-- The exact four-case extended intermediate-value theorem after restricting
all finite and infinite fibers to the open representative domain. -/
theorem maxwellOneSidedExtendedSlopeIntermediateValue_restrict_of_continuousOn
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z)) :
    MaxwellExtendedSlopeIntermediateValue
      (maxwellRelationRestrict
        (maxwellOneSidedStepZeroTrace U R i side) U)
      (maxwellOneSidedInfinityBase U R i side .positive ∩ U)
      (maxwellOneSidedInfinityBase U R i side .negative ∩ U) := by
  refine
    { finite_between :=
        maxwellFiniteSlopeIntervalFibers_restrict_oneSidedTrace_of_continuousOn
          i side hUopen hf hrep
      finite_to_positiveInfinity := ?_
      negativeInfinity_to_finite := ?_
      negativeInfinity_to_positiveInfinity := ?_ }
  · intro x a b hab ha hx
    rcases eq_or_lt_of_le hab with hEq | hlt
    · subst b
      exact ha
    · apply
        (realEuclideanAppend_mem_maxwellRelationRestrict_iff
          (maxwellOneSidedStepZeroTrace U R i side) U x
          (fun _ : Fin 1 ↦ b)).mpr
      have ha' :=
        (realEuclideanAppend_mem_maxwellRelationRestrict_iff
          (maxwellOneSidedStepZeroTrace U R i side) U x
          (fun _ : Fin 1 ↦ a)).mp ha
      exact ⟨
        maxwellOneSidedStepZeroTrace_above_of_positiveInfinity_and_finiteTrace
          i side hUopen hf hrep hx.2 ha'.1 hx.1 hlt,
        hx.2⟩
  · intro x a b hba ha hx
    rcases eq_or_lt_of_le hba with hEq | hlt
    · subst b
      exact ha
    · apply
        (realEuclideanAppend_mem_maxwellRelationRestrict_iff
          (maxwellOneSidedStepZeroTrace U R i side) U x
          (fun _ : Fin 1 ↦ b)).mpr
      have ha' :=
        (realEuclideanAppend_mem_maxwellRelationRestrict_iff
          (maxwellOneSidedStepZeroTrace U R i side) U x
          (fun _ : Fin 1 ↦ a)).mp ha
      exact ⟨
        maxwellOneSidedStepZeroTrace_below_of_negativeInfinity_and_finiteTrace
          i side hUopen hf hrep hx.2 ha'.1 hx.1 hlt,
        hx.2⟩
  · intro x y hpositive hnegative
    apply
      (realEuclideanAppend_mem_maxwellRelationRestrict_iff
        (maxwellOneSidedStepZeroTrace U R i side) U x
        (fun _ : Fin 1 ↦ y)).mpr
    exact ⟨
      maxwellOneSidedStepZeroTrace_of_bothInfinities
        i side hUopen hf hrep hpositive.2 y hpositive.1 hnegative.1,
      hpositive.2⟩

/-- On an unrestricted trace, base containment is the only additional input
needed to obtain the exact four-case extended intermediate-value theorem. -/
theorem maxwellOneSidedExtendedSlopeIntermediateValue_of_continuousOn
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    (hfiniteBase : maxwellRelationDomain
      (maxwellOneSidedStepZeroTrace U R i side) ⊆ U)
    (hpositiveBase :
      maxwellOneSidedInfinityBase U R i side .positive ⊆ U)
    (hnegativeBase :
      maxwellOneSidedInfinityBase U R i side .negative ⊆ U) :
    MaxwellExtendedSlopeIntermediateValue
      (maxwellOneSidedStepZeroTrace U R i side)
      (maxwellOneSidedInfinityBase U R i side .positive)
      (maxwellOneSidedInfinityBase U R i side .negative) := by
  refine
    { finite_between :=
        maxwellFiniteSlopeIntervalFibers_oneSidedTrace_of_continuousOn
          i side hUopen hf hrep hfiniteBase
      finite_to_positiveInfinity := ?_
      negativeInfinity_to_finite := ?_
      negativeInfinity_to_positiveInfinity := ?_ }
  · intro x a b hab ha hx
    rcases eq_or_lt_of_le hab with hEq | hlt
    · subst b
      exact ha
    · exact
        maxwellOneSidedStepZeroTrace_above_of_positiveInfinity_and_finiteTrace
          i side hUopen hf hrep (hpositiveBase hx) ha hx hlt
  · intro x a b hba ha hx
    rcases eq_or_lt_of_le hba with hEq | hlt
    · subst b
      exact ha
    · exact
        maxwellOneSidedStepZeroTrace_below_of_negativeInfinity_and_finiteTrace
          i side hUopen hf hrep (hnegativeBase hx) ha hx hlt
  · intro x y hpositive hnegative
    exact maxwellOneSidedStepZeroTrace_of_bothInfinities
      i side hUopen hf hrep (hpositiveBase hpositive) y hpositive hnegative

/-- Exact interval filling for the restricted one-sided extended
multivalued locus, with no finite-anchor assumptions. -/
theorem maxwellOneSidedExtendedSlopeIntervalFilling_restrict_of_continuousOn
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z)) :
    MaxwellExtendedSlopeIntervalFilling
      (maxwellRelationRestrict
        (maxwellOneSidedStepZeroTrace U R i side) U)
      (maxwellOneSidedExtendedMultivaluedLocus
        (maxwellRelationRestrict
          (maxwellOneSidedStepZeroTrace U R i side) U)
        (maxwellOneSidedInfinityBase U R i side .positive ∩ U)
        (maxwellOneSidedInfinityBase U R i side .negative ∩ U)) :=
  (maxwellOneSidedExtendedSlopeIntermediateValue_restrict_of_continuousOn
    i side hUopen hf hrep).intervalFilling

/-- Exact interval filling for the unrestricted one-sided extended
multivalued locus once all relevant closure fibers are based in `U`. -/
theorem maxwellOneSidedExtendedSlopeIntervalFilling_of_continuousOn
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    (hfiniteBase : maxwellRelationDomain
      (maxwellOneSidedStepZeroTrace U R i side) ⊆ U)
    (hpositiveBase :
      maxwellOneSidedInfinityBase U R i side .positive ⊆ U)
    (hnegativeBase :
      maxwellOneSidedInfinityBase U R i side .negative ⊆ U) :
    MaxwellExtendedSlopeIntervalFilling
      (maxwellOneSidedStepZeroTrace U R i side)
      (maxwellOneSidedExtendedMultivaluedLocus
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative)) :=
  (maxwellOneSidedExtendedSlopeIntermediateValue_of_continuousOn
    i side hUopen hf hrep hfiniteBase hpositiveBase hnegativeBase).intervalFilling

end AbelFormalization
