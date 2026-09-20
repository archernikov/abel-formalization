import AbelFormalization.MaxwellOneSidedClusterCoverage

/-!
# The residual one-sided slope classification

This file compares the two orders in which Maxwell's constructions take a
zero-step trace and reciprocate the slope.  A nonzero reciprocal of a finite
one-sided trace value already belongs to the corresponding reciprocal trace.
Consequently, an infinite cluster of the full finite trace comes from one of
the source-defined one-sided infinite clusters.
-/

noncomputable section

open Set Filter Topology
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Reciprocating a finite one-sided trace value -/

/-- Reciprocating a nonzero finite one-sided trace value before or after the
zero-step trace gives the same membership needed below. -/
theorem realEuclideanAppend_mem_maxwellOneSidedReciprocalTrace_of_finite
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (side : MaxwellOneSidedStep)
    (infinity : MaxwellSlopeInfinitySign)
    {x : RealEuclidean p} {y r : ℝ}
    (hy : realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
      maxwellOneSidedStepZeroTrace U R i side)
    (hyr : y * r = 1)
    (hr : infinity.AcceptsReciprocal r) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ r) ∈
      maxwellOneSidedReciprocalTrace U R i side infinity := by
  obtain ⟨h⟩ :=
    (mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
      U R i side x y).mp hy
  have hyne : y ≠ 0 := by
    intro hyzero
    rw [hyzero, zero_mul] at hyr
    norm_num at hyr
  have hyrInv : y⁻¹ = r := by
    calc
      y⁻¹ = (r⁻¹)⁻¹ := congrArg Inv.inv (eq_inv_of_mul_eq_one_left hyr)
      _ = r := inv_inv r
  have hinv : Tendsto
      (fun n ↦ (maxwellStepLastValue (h.point n))⁻¹)
      atTop (nhds r) := by
    rw [← hyrInv]
    exact h.value_tendsto.inv₀ hyne
  have hsign : ∀ᶠ n in atTop,
      infinity.AcceptsReciprocal
        ((maxwellStepLastValue (h.point n))⁻¹) := by
    cases infinity with
    | positive =>
        exact hinv.eventually_const_lt hr
    | negative =>
        exact hinv.eventually_lt_const hr
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsign
  let source : ℕ → RealEuclidean p × ℝ := fun n ↦
    maxwellOneSidedApproachSource side (h.point (n + N))
  let reciprocal : ℕ → ℝ := fun n ↦
    (maxwellStepLastValue (h.point (n + N)))⁻¹
  let point : ℕ → RealEuclidean ((p + 1) + 1) := fun n ↦
    realEuclideanAppend
      (realEuclideanAppend (source n).1
        (fun _ : Fin 1 ↦ reciprocal n))
      (fun _ : Fin 1 ↦ side.sign * (source n).2)
  have htailSign (n : ℕ) :
      infinity.AcceptsReciprocal (reciprocal n) :=
    hN (n + N) (by omega)
  have hsourceStep (n : ℕ) : 0 < (source n).2 := by
    exact (side.sign_mul_step_pos_iff
      (maxwellStepLastStep (h.point (n + N)))).mpr
        (h.step_sign (n + N))
  have hpointMem (n : ℕ) :
      point n ∈
        maxwellOneSidedReciprocalStepLastRelation U R i infinity := by
    apply
      (realEuclideanAppend_append_mem_maxwellOneSidedReciprocalStepLastRelation_iff
        U R i infinity (source n).1
          (side.sign * (source n).2) (reciprocal n)).2
    refine ⟨maxwellStepLastValue (h.point (n + N)), ?_, ?_,
      htailSign n⟩
    · simpa only [source, maxwellOneSidedApproachSource,
          reciprocal, ← mul_assoc, side.sign_mul_self, one_mul,
          realEuclideanAppend_stepLastCoordinates] using
        h.point_mem (n + N)
    · apply mul_inv_cancel₀
      cases infinity with
      | positive =>
          intro hzero
          have hsign := htailSign n
          simp only [reciprocal, hzero, inv_zero,
            MaxwellSlopeInfinitySign.AcceptsReciprocal, lt_self_iff_false]
            at hsign
      | negative =>
          intro hzero
          have hsign := htailSign n
          simp only [reciprocal, hzero, inv_zero,
            MaxwellSlopeInfinitySign.AcceptsReciprocal, lt_self_iff_false]
            at hsign
  have hsource : Tendsto source atTop (nhds (x, 0)) := by
    exact h.source_tendsto.comp (tendsto_add_atTop_nat N)
  have hreciprocal : Tendsto reciprocal atTop (nhds r) := by
    exact hinv.comp (tendsto_add_atTop_nat N)
  have hpoint : Tendsto point atTop
      (nhds (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ r))
        (fun _ : Fin 1 ↦ 0))) :=
    tendsto_stepLastPoint_of_source_and_value_tendsto
      side hsource hreciprocal
  have hpointSign (n : ℕ) :
      side.Accepts (point n (Fin.last (p + 1))) := by
    cases side <;>
      simpa [point, MaxwellOneSidedStep.Accepts,
        MaxwellOneSidedStep.sign] using hsourceStep n
  cases side with
  | positive =>
      change charbonnelAppendLastCoordinate
          (realEuclideanAppend x (fun _ : Fin 1 ↦ r)) 0 ∈
        closure (charbonnelPositiveLastPart
          (maxwellOneSidedReciprocalStepLastRelation U R i infinity))
      apply mem_closure_iff_seq_limit.mpr
      refine ⟨point, fun n ↦ ⟨hpointMem n, hpointSign n⟩, ?_⟩
      simpa only [charbonnelAppendLastCoordinate] using hpoint
  | negative =>
      rw [maxwellOneSidedReciprocalTrace,
        maxwellNegativeZeroTrace_eq_zeroSection_closure_negativeLastPart]
      change charbonnelAppendLastCoordinate
          (realEuclideanAppend x (fun _ : Fin 1 ↦ r)) 0 ∈
        closure (maxwellNegativeLastPart
          (maxwellOneSidedReciprocalStepLastRelation U R i infinity))
      apply mem_closure_iff_seq_limit.mpr
      refine ⟨point, fun n ↦ ⟨hpointMem n, hpointSign n⟩, ?_⟩
      simpa only [charbonnelAppendLastCoordinate] using hpoint

/-! ## Comparing the two orders of tracing and reciprocating -/

theorem isClosed_maxwellOneSidedReciprocalTrace
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (infinity : MaxwellSlopeInfinitySign) :
    IsClosed (maxwellOneSidedReciprocalTrace U R i side infinity) := by
  cases side with
  | positive =>
      let A := maxwellOneSidedReciprocalStepLastRelation U R i infinity
      have hEq : charbonnelPositiveZeroTrace A =
          charbonnelZeroSection (closure (charbonnelPositiveLastPart A)) := by
        calc
          charbonnelPositiveZeroTrace A =
              charbonnelPositiveZeroTrace (charbonnelPositiveLastPart A) :=
            (charbonnelPositiveZeroTrace_positiveLastPart A).symm
          _ = charbonnelZeroSection
              (closure (charbonnelPositiveLastPart A)) :=
            charbonnelPositiveZeroTrace_eq_zeroSection_closure
              inter_subset_right
      change IsClosed (charbonnelPositiveZeroTrace A)
      rw [hEq]
      exact charbonnelZeroSection_isClosed isClosed_closure
  | negative =>
      rw [maxwellOneSidedReciprocalTrace,
        maxwellNegativeZeroTrace_eq_zeroSection_closure_negativeLastPart]
      exact charbonnelZeroSection_isClosed isClosed_closure

/-- If reciprocals of finite values in a one-sided trace approach zero,
then the original pre-trace quotient already has the corresponding
source-defined one-sided infinite cluster. -/
theorem maxwellInfinityBase_oneSidedTrace_subset_oneSidedInfinityBase
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (infinity : MaxwellSlopeInfinitySign) :
    (match infinity with
      | .positive => maxwellPositiveInfinityBase
          (maxwellOneSidedStepZeroTrace U R i side)
      | .negative => maxwellNegativeInfinityBase
          (maxwellOneSidedStepZeroTrace U R i side)) ⊆
        maxwellOneSidedInfinityBase U R i side infinity := by
  cases infinity with
  | positive =>
      intro x hx
      let G := maxwellOneSidedStepZeroTrace U R i side
      let H := maxwellOneSidedReciprocalTrace U R i side .positive
      have hreciprocal : maxwellPositiveReciprocalRelation G ⊆ H := by
        intro w hw
        rw [← realEuclideanAppend_takeLeft_takeRight w] at hw ⊢
        let a : RealEuclidean p := realEuclideanTakeLeft w
        let r : ℝ := realEuclideanTakeRight w 0
        have hright : realEuclideanTakeRight w =
            (fun _ : Fin 1 ↦ r) := by
          funext j
          have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
          subst j
          rfl
        rw [hright] at hw ⊢
        rcases
            (realEuclideanAppend_scalar_mem_maxwellPositiveReciprocalRelation_iff
              G a r).mp hw with ⟨y, hy, hyr, hr⟩
        exact realEuclideanAppend_mem_maxwellOneSidedReciprocalTrace_of_finite
          i side .positive hy hyr hr
      change realEuclideanAppend x (0 : RealEuclidean 1) ∈ H
      exact closure_minimal hreciprocal
        (isClosed_maxwellOneSidedReciprocalTrace U R i side .positive) hx
  | negative =>
      intro x hx
      let G := maxwellOneSidedStepZeroTrace U R i side
      let H := maxwellOneSidedReciprocalTrace U R i side .negative
      have hreciprocal : maxwellNegativeReciprocalRelation G ⊆ H := by
        intro w hw
        rw [← realEuclideanAppend_takeLeft_takeRight w] at hw ⊢
        let a : RealEuclidean p := realEuclideanTakeLeft w
        let r : ℝ := realEuclideanTakeRight w 0
        have hright : realEuclideanTakeRight w =
            (fun _ : Fin 1 ↦ r) := by
          funext j
          have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
          subst j
          rfl
        rw [hright] at hw ⊢
        rcases
            (realEuclideanAppend_scalar_mem_maxwellNegativeReciprocalRelation_iff
              G a r).mp hw with ⟨y, hy, hyr, hr⟩
        exact realEuclideanAppend_mem_maxwellOneSidedReciprocalTrace_of_finite
          i side .negative hy hyr hr
      change realEuclideanAppend x (0 : RealEuclidean 1) ∈ H
      exact closure_minimal hreciprocal
        (isClosed_maxwellOneSidedReciprocalTrace U R i side .negative) hx

theorem maxwellPositiveReciprocalRelation_union {p : ℕ}
    (G H : MaxwellRelation p 1) :
    maxwellPositiveReciprocalRelation (G ∪ H) =
      maxwellPositiveReciprocalRelation G ∪
        maxwellPositiveReciprocalRelation H := by
  ext w
  simp only [maxwellPositiveReciprocalRelation, Set.mem_ofPred_eq,
    Set.mem_union]
  aesop

theorem maxwellNegativeReciprocalRelation_union {p : ℕ}
    (G H : MaxwellRelation p 1) :
    maxwellNegativeReciprocalRelation (G ∪ H) =
      maxwellNegativeReciprocalRelation G ∪
        maxwellNegativeReciprocalRelation H := by
  ext w
  simp only [maxwellNegativeReciprocalRelation, Set.mem_ofPred_eq,
    Set.mem_union]
  aesop

/-- Every full-trace infinity comes from at least one of the two genuinely
one-sided source traces. -/
theorem maxwellFullTraceInfinityBase_subset_oneSidedInfinityBases
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (infinity : MaxwellSlopeInfinitySign) :
    (match infinity with
      | .positive => maxwellPositiveInfinityBase
          (maxwellDifferenceQuotientZeroTrace U R i)
      | .negative => maxwellNegativeInfinityBase
          (maxwellDifferenceQuotientZeroTrace U R i)) ⊆
        maxwellOneSidedInfinityBase U R i .positive infinity ∪
          maxwellOneSidedInfinityBase U R i .negative infinity := by
  cases infinity with
  | positive =>
      intro x hx
      rw [← maxwellPositiveStepZeroTrace_union_negativeStepZeroTrace U R i]
        at hx
      change realEuclideanAppend x (0 : RealEuclidean 1) ∈
        closure (maxwellPositiveReciprocalRelation
          (maxwellPositiveStepZeroTrace U R i ∪
            maxwellNegativeStepZeroTrace U R i)) at hx
      rw [maxwellPositiveReciprocalRelation_union, closure_union] at hx
      rcases hx with hx | hx
      · exact Or.inl
          (maxwellInfinityBase_oneSidedTrace_subset_oneSidedInfinityBase
            U R i .positive .positive hx)
      · exact Or.inr
          (maxwellInfinityBase_oneSidedTrace_subset_oneSidedInfinityBase
            U R i .negative .positive hx)
  | negative =>
      intro x hx
      rw [← maxwellPositiveStepZeroTrace_union_negativeStepZeroTrace U R i]
        at hx
      change realEuclideanAppend x (0 : RealEuclidean 1) ∈
        closure (maxwellNegativeReciprocalRelation
          (maxwellPositiveStepZeroTrace U R i ∪
            maxwellNegativeStepZeroTrace U R i)) at hx
      rw [maxwellNegativeReciprocalRelation_union, closure_union] at hx
      rcases hx with hx | hx
      · exact Or.inl
          (maxwellInfinityBase_oneSidedTrace_subset_oneSidedInfinityBase
            U R i .positive .negative hx)
      · exact Or.inr
          (maxwellInfinityBase_oneSidedTrace_subset_oneSidedInfinityBase
            U R i .negative .negative hx)

/-! ## The residual cannot have a common finite one-sided value -/

/-- On the literal slope-bad residual, a common finite right/left cluster
would contradict either a full-trace infinity or full-trace
multivaluedness.  This discharges the last field of the residual cluster
classification from the already defined source traces. -/
theorem maxwellNoCommonFiniteOneSidedSlopeCluster_on_residual
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    MaxwellNoCommonFiniteOneSidedSlopeCluster U R i
      (maxwellCoordinateSlopeBadResidualLocus U R i) := by
  intro x hx y hcommon
  rcases hcommon with ⟨hyPos, hyNeg⟩
  have hnotPos :
      x ∉ maxwellPositiveStepExtendedMultivaluedLocus U R i := by
    intro h
    exact hx.2 (Or.inl h)
  have hnotNeg :
      x ∉ maxwellNegativeStepExtendedMultivaluedLocus U R i := by
    intro h
    exact hx.2 (Or.inr h)
  have hposFiniteMulti {z : ℝ}
      (hz : realEuclideanAppend x (fun _ : Fin 1 ↦ z) ∈
        maxwellPositiveStepZeroTrace U R i) (hzy : z ≠ y) :
      x ∈ maxwellPositiveStepExtendedMultivaluedLocus U R i := by
    exact ⟨.finite y, .finite z, hyPos, hz, by simp [hzy.symm]⟩
  have hnegFiniteMulti {z : ℝ}
      (hz : realEuclideanAppend x (fun _ : Fin 1 ↦ z) ∈
        maxwellNegativeStepZeroTrace U R i) (hzy : z ≠ y) :
      x ∈ maxwellNegativeStepExtendedMultivaluedLocus U R i := by
    exact ⟨.finite y, .finite z, hyNeg, hz, by simp [hzy.symm]⟩
  have hposInfiniteMulti (infinity : MaxwellSlopeInfinitySign)
      (hinf : x ∈ maxwellOneSidedInfinityBase U R i .positive infinity) :
      x ∈ maxwellPositiveStepExtendedMultivaluedLocus U R i := by
    cases infinity with
    | positive =>
        exact ⟨.finite y, .positiveInfinity, hyPos, hinf, by simp⟩
    | negative =>
        exact ⟨.finite y, .negativeInfinity, hyPos, hinf, by simp⟩
  have hnegInfiniteMulti (infinity : MaxwellSlopeInfinitySign)
      (hinf : x ∈ maxwellOneSidedInfinityBase U R i .negative infinity) :
      x ∈ maxwellNegativeStepExtendedMultivaluedLocus U R i := by
    cases infinity with
    | positive =>
        exact ⟨.finite y, .positiveInfinity, hyNeg, hinf, by simp⟩
    | negative =>
        exact ⟨.finite y, .negativeInfinity, hyNeg, hinf, by simp⟩
  have hxSlope := hx.1
  simp only [maxwellCoordinateSlopeBadLocus, Set.mem_union] at hxSlope
  rcases hxSlope with hinfinite | hfinite
  · rcases hinfinite with hpositive | hnegative
    · rcases
        maxwellFullTraceInfinityBase_subset_oneSidedInfinityBases
          U R i .positive hpositive with hside | hside
      · exact hnotPos (hposInfiniteMulti .positive hside)
      · exact hnotNeg (hnegInfiniteMulti .positive hside)
    · rcases
        maxwellFullTraceInfinityBase_subset_oneSidedInfinityBases
          U R i .negative hnegative with hside | hside
      · exact hnotPos (hposInfiniteMulti .negative hside)
      · exact hnotNeg (hnegInfiniteMulti .negative hside)
  · rcases hfinite with ⟨z₁, z₂, hz₁, hz₂, hzNe⟩
    have hzScalarNe : z₁ 0 ≠ z₂ 0 := by
      intro h
      apply hzNe
      funext j
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      exact h
    have hz₁' : realEuclideanAppend x (fun _ : Fin 1 ↦ z₁ 0) ∈
        maxwellDifferenceQuotientZeroTrace U R i := by
      change realEuclideanAppend x z₁ ∈
        maxwellDifferenceQuotientZeroTrace U R i at hz₁
      simpa only [← realEuclidean_one_eq_const z₁] using hz₁
    have hz₂' : realEuclideanAppend x (fun _ : Fin 1 ↦ z₂ 0) ∈
        maxwellDifferenceQuotientZeroTrace U R i := by
      change realEuclideanAppend x z₂ ∈
        maxwellDifferenceQuotientZeroTrace U R i at hz₂
      simpa only [← realEuclidean_one_eq_const z₂] using hz₂
    have hclassify {z : ℝ}
        (hz : realEuclideanAppend x (fun _ : Fin 1 ↦ z) ∈
          maxwellDifferenceQuotientZeroTrace U R i) :
        realEuclideanAppend x (fun _ : Fin 1 ↦ z) ∈
            maxwellPositiveStepZeroTrace U R i ∨
          realEuclideanAppend x (fun _ : Fin 1 ↦ z) ∈
            maxwellNegativeStepZeroTrace U R i := by
      have hzUnion : realEuclideanAppend x (fun _ : Fin 1 ↦ z) ∈
          maxwellPositiveStepZeroTrace U R i ∪
            maxwellNegativeStepZeroTrace U R i := by
        rw [maxwellPositiveStepZeroTrace_union_negativeStepZeroTrace]
        exact hz
      exact hzUnion
    by_cases hz₁y : z₁ 0 = y
    · have hz₂y : z₂ 0 ≠ y := by
        intro hz₂y
        exact hzScalarNe (hz₁y.trans hz₂y.symm)
      rcases hclassify hz₂' with hzPos | hzNeg
      · exact hnotPos (hposFiniteMulti hzPos hz₂y)
      · exact hnotNeg (hnegFiniteMulti hzNeg hz₂y)
    · rcases hclassify hz₁' with hzPos | hzNeg
      · exact hnotPos (hposFiniteMulti hzPos hz₁y)
      · exact hnotNeg (hnegFiniteMulti hzNeg hz₁y)

/-- The entire residual cluster-data field now follows from pseudofunction
coverage and the preceding trace comparison. -/
theorem IsMaxwellPseudofunctionOn.nondifferentiableOneSidedClusterData_residual
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U)
    (i : Fin p)
    (hresidualU : maxwellCoordinateSlopeBadResidualLocus U R i ⊆ U) :
    MaxwellNondifferentiableOneSidedClusterData U R i
      (maxwellCoordinateSlopeBadResidualLocus U R i) :=
  hR.nondifferentiableOneSidedClusterData_of_noCommonFinite hU i
    hresidualU
    (maxwellNoCommonFiniteOneSidedSlopeCluster_on_residual U R i)

/-- Without any global containment premise, the source cluster
classification holds on the only part needed for differentiability: the
residual inside the stated open domain. -/
theorem IsMaxwellPseudofunctionOn.nondifferentiableOneSidedClusterData_residual_inter
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U)
    (i : Fin p) :
    MaxwellNondifferentiableOneSidedClusterData U R i
      (maxwellCoordinateSlopeBadResidualLocus U R i ∩ U) := by
  apply hR.nondifferentiableOneSidedClusterData_inter_of_noCommonFinite hU i
  intro x hx y hcommon
  exact maxwellNoCommonFiniteOneSidedSlopeCluster_on_residual U R i
    x hx.1 y hcommon

end AbelFormalization
