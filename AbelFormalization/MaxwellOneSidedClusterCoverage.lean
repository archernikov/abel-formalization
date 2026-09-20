import AbelFormalization.MaxwellOneSidedExtendedIVT

/-!
# Existence of one-sided compactified slope clusters

At an interior base point, choose ordinary nonzero steps tending to zero on
either side.  Their slopes have a bounded subsequence, diverge to positive
infinity along a subsequence, or diverge to negative infinity along a
subsequence.  These three alternatives give exactly one finite or infinite
member of Maxwell's one-sided extended slope fiber.

The result is purely topological and order theoretic.  For a
pseudofunction relation, its full-fiber property supplies the quotient
points by using the canonical chosen value at both endpoints; uniqueness or
continuity is not needed.
-/

noncomputable section

open Set Filter Topology
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## A compactified cluster from any shrinking source sequence -/

/-- Monotonicity of the step-last quotient relation in its value relation. -/
theorem maxwellStepLastDifferenceQuotientRelation_mono
    {p : ℕ} {U : Set (RealEuclidean p)}
    {R T : MaxwellRelation p 1} (hRT : R ⊆ T) (i : Fin p) :
    maxwellStepLastDifferenceQuotientRelation U R i ⊆
      maxwellStepLastDifferenceQuotientRelation U T i := by
  rintro z ⟨w, hw, rfl⟩
  exact ⟨w, maxwellDifferenceQuotientRelation_mono hRT i hw, rfl⟩

/-- Any sequence of valid one-sided quotient points whose positive step
parameters tend to zero has a finite, positive-infinite, or negative-infinite
cluster in the source-defined extended one-sided fiber. -/
theorem exists_maxwellOneSidedExtendedSlopeCluster_of_sequence
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (side : MaxwellOneSidedStep)
    {x : RealEuclidean p}
    {source : ℕ → RealEuclidean p × ℝ} {slope : ℕ → ℝ}
    (hsource : Tendsto source atTop (nhds (x, 0)))
    (hstep : ∀ n, 0 < (source n).2)
    (hpoint : ∀ n,
      realEuclideanAppend
          (realEuclideanAppend (source n).1
            (fun _ : Fin 1 ↦ slope n))
          (fun _ : Fin 1 ↦ side.sign * (source n).2) ∈
        maxwellStepLastDifferenceQuotientRelation U R i) :
    (maxwellExtendedSlopeFiber
      (maxwellOneSidedStepZeroTrace U R i side)
      (maxwellOneSidedInfinityBase U R i side .positive)
      (maxwellOneSidedInfinityBase U R i side .negative) x).Nonempty := by
  by_cases hbounded : Bornology.IsBounded (Set.range slope)
  · obtain ⟨y, _hyClosure, φ, hφmono, hslopeLimit⟩ :=
      tendsto_subseq_of_bounded hbounded
        (fun n ↦ Set.mem_range_self n)
    have hφTop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    let hfinite : MaxwellOneSidedSlopeApproach U R i side x y :=
      { point := fun n ↦
          realEuclideanAppend
            (realEuclideanAppend (source (φ n)).1
              (fun _ : Fin 1 ↦ slope (φ n)))
            (fun _ : Fin 1 ↦ side.sign * (source (φ n)).2)
        point_mem := fun n ↦ hpoint (φ n)
        step_sign := fun n ↦ by
          cases side <;>
            simpa [MaxwellOneSidedStep.Accepts,
              MaxwellOneSidedStep.sign] using hstep (φ n)
        tendsto_zeroStep :=
          tendsto_stepLastPoint_of_source_and_value_tendsto side
            (hsource.comp hφTop)
            (by simpa only [Function.comp_def] using hslopeLimit) }
    refine ⟨.finite y, ?_⟩
    apply (finite_mem_maxwellExtendedSlopeFiber_iff
      (maxwellOneSidedStepZeroTrace U R i side)
      (maxwellOneSidedInfinityBase U R i side .positive)
      (maxwellOneSidedInfinityBase U R i side .negative) x y).2
    exact
      (mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
        U R i side x y).2 ⟨hfinite⟩
  · by_cases hbelow : BddBelow (Set.range slope)
    · have habove : ¬ BddAbove (Set.range slope) := by
        intro h
        exact hbounded
          (isBounded_iff_bddBelow_bddAbove.mpr ⟨hbelow, h⟩)
      have hextract : ∀ n : ℕ, ∃ k : ℕ,
          n ≤ k ∧ (n : ℝ) < slope k :=
        fun n ↦ exists_index_ge_natCast_lt_of_not_bddAbove_range
          slope habove n
      choose φ hφge hφlarge using hextract
      have hφTop : Tendsto φ atTop atTop := by
        rw [tendsto_atTop]
        intro N
        filter_upwards [eventually_ge_atTop N] with n hn
        exact hn.trans (hφge n)
      have hslopeTop : Tendsto (fun n ↦ slope (φ n)) atTop atTop :=
        tendsto_atTop_mono (fun n ↦ (hφlarge n).le)
          (tendsto_natCast_atTop_atTop (R := ℝ))
      have hinvLimit :
          Tendsto (fun n ↦ (slope (φ n))⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp hslopeTop
      let hinfinite : MaxwellOneSidedInfiniteSlopeApproach
          U R i side .positive x :=
        { point := fun n ↦
            realEuclideanAppend
              (realEuclideanAppend (source (φ n)).1
                (fun _ : Fin 1 ↦ (slope (φ n))⁻¹))
              (fun _ : Fin 1 ↦ side.sign * (source (φ n)).2)
          point_mem := fun n ↦ by
            apply
              (realEuclideanAppend_append_mem_maxwellOneSidedReciprocalStepLastRelation_iff
                U R i .positive (source (φ n)).1
                (side.sign * (source (φ n)).2)
                ((slope (φ n))⁻¹)).2
            have hpos : 0 < slope (φ n) :=
              lt_of_le_of_lt (Nat.cast_nonneg n) (hφlarge n)
            exact ⟨slope (φ n), hpoint (φ n),
              mul_inv_cancel₀ (ne_of_gt hpos), by
                simpa [MaxwellSlopeInfinitySign.AcceptsReciprocal] using
                  inv_pos.mpr hpos⟩
          step_sign := fun n ↦ by
            cases side <;>
              simpa [MaxwellOneSidedStep.Accepts,
                MaxwellOneSidedStep.sign] using hstep (φ n)
          tendsto_zeroReciprocalStep :=
            tendsto_stepLastPoint_of_source_and_value_tendsto side
              (hsource.comp hφTop) hinvLimit }
      refine ⟨.positiveInfinity, ?_⟩
      apply (positiveInfinity_mem_maxwellExtendedSlopeFiber_iff
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) x).2
      exact
        (mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
          U R i side .positive x).2 ⟨hinfinite⟩
    · have hextract : ∀ n : ℕ, ∃ k : ℕ,
          n ≤ k ∧ slope k < -(n : ℝ) :=
        fun n ↦ exists_index_ge_lt_neg_natCast_of_not_bddBelow_range
          slope hbelow n
      choose φ hφge hφsmall using hextract
      have hφTop : Tendsto φ atTop atTop := by
        rw [tendsto_atTop]
        intro N
        filter_upwards [eventually_ge_atTop N] with n hn
        exact hn.trans (hφge n)
      have hnegNat : Tendsto (fun n : ℕ ↦ -(n : ℝ)) atTop atBot :=
        tendsto_neg_atTop_atBot.comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
      have hslopeBot : Tendsto (fun n ↦ slope (φ n)) atTop atBot :=
        tendsto_atBot_mono (fun n ↦ (hφsmall n).le) hnegNat
      have hinvLimit :
          Tendsto (fun n ↦ (slope (φ n))⁻¹) atTop (nhds 0) :=
        tendsto_inv_atBot_zero.comp hslopeBot
      let hinfinite : MaxwellOneSidedInfiniteSlopeApproach
          U R i side .negative x :=
        { point := fun n ↦
            realEuclideanAppend
              (realEuclideanAppend (source (φ n)).1
                (fun _ : Fin 1 ↦ (slope (φ n))⁻¹))
              (fun _ : Fin 1 ↦ side.sign * (source (φ n)).2)
          point_mem := fun n ↦ by
            apply
              (realEuclideanAppend_append_mem_maxwellOneSidedReciprocalStepLastRelation_iff
                U R i .negative (source (φ n)).1
                (side.sign * (source (φ n)).2)
                ((slope (φ n))⁻¹)).2
            have hneg : slope (φ n) < 0 :=
              lt_of_lt_of_le (hφsmall n)
                (neg_nonpos.mpr (Nat.cast_nonneg n))
            exact ⟨slope (φ n), hpoint (φ n),
              mul_inv_cancel₀ (ne_of_lt hneg), by
                simpa [MaxwellSlopeInfinitySign.AcceptsReciprocal] using
                  (inv_lt_zero.mpr hneg)⟩
          step_sign := fun n ↦ by
            cases side <;>
              simpa [MaxwellOneSidedStep.Accepts,
                MaxwellOneSidedStep.sign] using hstep (φ n)
          tendsto_zeroReciprocalStep :=
            tendsto_stepLastPoint_of_source_and_value_tendsto side
              (hsource.comp hφTop) hinvLimit }
      refine ⟨.negativeInfinity, ?_⟩
      apply (negativeInfinity_mem_maxwellExtendedSlopeFiber_iff
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) x).2
      exact
        (mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
          U R i side .negative x).2 ⟨hinfinite⟩

/-! ## Canonical shrinking steps inside an open set -/

/-- Every point of an open base admits a valid positive parameter sequence
on either selected side, converging to the zero-step source. -/
theorem exists_maxwellOneSidedSourceSequence
    {p : ℕ} {U : Set (RealEuclidean p)} {x : RealEuclidean p}
    {i : Fin p} (side : MaxwellOneSidedStep)
    (hU : IsOpen U) (hx : x ∈ U) :
    ∃ source : ℕ → RealEuclidean p × ℝ,
      (∀ n, source n ∈ maxwellOneSidedStepDomain U i side) ∧
      Tendsto source atTop (nhds (x, 0)) := by
  obtain ⟨rho, hrho, hball⟩ := Metric.isOpen_iff.mp hU x hx
  let step : ℕ → ℝ := fun n ↦
    (rho / 2) * (1 / ((n : ℝ) + 1))
  let source : ℕ → RealEuclidean p × ℝ := fun n ↦ (x, step n)
  have hstepPos (n : ℕ) : 0 < step n := by
    dsimp only [step]
    positivity
  have hstepLt (n : ℕ) : step n < rho := by
    have hone : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      norm_num
    dsimp only [step]
    nlinarith [hrho]
  have hsourceMem (n : ℕ) :
      source n ∈ maxwellOneSidedStepDomain U i side := by
    refine ⟨hx, hball ?_, hstepPos n⟩
    rw [Metric.mem_ball, dist_eq_norm]
    change ‖x + (side.sign * step n) •
        (Pi.single i 1 : RealEuclidean p) - x‖ < rho
    rw [add_sub_cancel_left, norm_smul, Pi.norm_single]
    cases side <;>
      simp [MaxwellOneSidedStep.sign, abs_of_pos (hstepPos n), hstepLt n]
  have hstepTendsto : Tendsto step atTop (nhds 0) := by
    have h :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (rho / 2)
    simpa only [step, mul_zero] using h
  have hsourceTendsto : Tendsto source atTop (nhds (x, 0)) := by
    simpa only [source, nhds_prod_eq] using
      tendsto_const_nhds.prodMk hstepTendsto
  exact ⟨source, hsourceMem, hsourceTendsto⟩

/-! ## Coverage for a Maxwell pseudofunction -/

/-- Full fibers of a Maxwell pseudofunction supply a compactified slope
cluster from either side at every interior base point. -/
theorem IsMaxwellPseudofunctionOn.oneSidedExtendedSlopeFiber_nonempty
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U)
    (i : Fin p) (side : MaxwellOneSidedStep)
    {x : RealEuclidean p} (hx : x ∈ U) :
    (maxwellExtendedSlopeFiber
      (maxwellOneSidedStepZeroTrace U R i side)
      (maxwellOneSidedInfinityBase U R i side .positive)
      (maxwellOneSidedInfinityBase U R i side .negative) x).Nonempty := by
  obtain ⟨source, hsourceMem, hsourceTendsto⟩ :=
    exists_maxwellOneSidedSourceSequence side hU hx
  let f : RealEuclidean p → ℝ := maxwellChosenScalarValue R
  let slope : ℕ → ℝ := fun n ↦
    maxwellOneSidedDifferenceQuotient f i side (source n)
  let G : MaxwellRelation p 1 :=
    maxwellFunctionGraph U
      (fun z : RealEuclidean p ↦ fun _ : Fin 1 ↦ f z)
  have hgrep : MaxwellRelation.RepresentsOn G U
      (fun z : RealEuclidean p ↦ fun _ : Fin 1 ↦ f z) :=
    MaxwellRelation.representsOn_functionGraph U
      (fun z : RealEuclidean p ↦ fun _ : Fin 1 ↦ f z)
  have hGR : G ⊆ R := by
    simpa only [G, f] using hR.chosenScalarGraph_subset
  have hpoint (n : ℕ) :
      realEuclideanAppend
          (realEuclideanAppend (source n).1
            (fun _ : Fin 1 ↦ slope n))
          (fun _ : Fin 1 ↦ side.sign * (source n).2) ∈
        maxwellStepLastDifferenceQuotientRelation U R i := by
    apply maxwellStepLastDifferenceQuotientRelation_mono hGR i
    exact
      ((realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_oneSided_of_representsOn_iff
        i hgrep side (source n).1 (source n).2 (slope n)).2
          ⟨hsourceMem n, rfl⟩).1
  exact exists_maxwellOneSidedExtendedSlopeCluster_of_sequence
    i side hsourceTendsto (fun n ↦ (hsourceMem n).2.2) hpoint

/-- Both right and reflected-left compactified slope fibers are nonempty at
every point of the open pseudofunction domain. -/
theorem IsMaxwellPseudofunctionOn.twoSidedExtendedSlopeFibers_nonempty
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U)
    (i : Fin p) {x : RealEuclidean p} (hx : x ∈ U) :
    (maxwellExtendedSlopeFiber
      (maxwellPositiveStepZeroTrace U R i)
      (maxwellPositiveStepPositiveInfinityBase U R i)
      (maxwellPositiveStepNegativeInfinityBase U R i) x).Nonempty ∧
    (maxwellExtendedSlopeFiber
      (maxwellNegativeStepZeroTrace U R i)
      (maxwellNegativeStepPositiveInfinityBase U R i)
      (maxwellNegativeStepNegativeInfinityBase U R i) x).Nonempty := by
  constructor
  · simpa only [maxwellOneSidedStepZeroTrace,
      maxwellOneSidedInfinityBase_positive_positive,
      maxwellOneSidedInfinityBase_positive_negative] using
      hR.oneSidedExtendedSlopeFiber_nonempty hU i .positive hx
  · simpa only [maxwellOneSidedStepZeroTrace,
      maxwellOneSidedInfinityBase_negative_positive,
      maxwellOneSidedInfinityBase_negative_negative] using
      hR.oneSidedExtendedSlopeFiber_nonempty hU i .negative hx

/-! ## Reduction of the residual cluster-classification input -/

/-- The mean-value part of the residual classification: no finite slope is
simultaneously a right and reflected-left cluster.  Cluster existence is
kept out of this predicate because it follows from the preceding theorem. -/
def MaxwellNoCommonFiniteOneSidedSlopeCluster
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (B : Set (RealEuclidean p)) : Prop :=
  ∀ x ∈ B, ∀ y : ℝ,
    ¬ (MaxwellExtendedSlopeValue.finite y ∈
          maxwellExtendedSlopeFiber
            (maxwellPositiveStepZeroTrace U R i)
            (maxwellPositiveStepPositiveInfinityBase U R i)
            (maxwellPositiveStepNegativeInfinityBase U R i) x ∧
        MaxwellExtendedSlopeValue.finite y ∈
          maxwellExtendedSlopeFiber
            (maxwellNegativeStepZeroTrace U R i)
            (maxwellNegativeStepPositiveInfinityBase U R i)
            (maxwellNegativeStepNegativeInfinityBase U R i) x)

/-- For a residual set based inside the open pseudofunction domain, the
source's full three-field cluster-classification interface reduces to its
mean-value assertion excluding a common finite cluster. -/
theorem IsMaxwellPseudofunctionOn.nondifferentiableOneSidedClusterData_of_noCommonFinite
    {p : ℕ} {U B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U)
    (i : Fin p) (hBU : B ⊆ U)
    (hno : MaxwellNoCommonFiniteOneSidedSlopeCluster U R i B) :
    MaxwellNondifferentiableOneSidedClusterData U R i B := by
  intro x hx
  have hclusters := hR.twoSidedExtendedSlopeFibers_nonempty hU i (hBU hx)
  exact ⟨hclusters.1, hclusters.2, hno x hx⟩

/-- Base restriction always supplies the containment premise in the preceding
reduction. -/
theorem IsMaxwellPseudofunctionOn.nondifferentiableOneSidedClusterData_inter_of_noCommonFinite
    {p : ℕ} {U B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (hU : IsOpen U)
    (i : Fin p)
    (hno : MaxwellNoCommonFiniteOneSidedSlopeCluster U R i (B ∩ U)) :
    MaxwellNondifferentiableOneSidedClusterData U R i (B ∩ U) :=
  hR.nondifferentiableOneSidedClusterData_of_noCommonFinite
    hU i inter_subset_right hno

end AbelFormalization
