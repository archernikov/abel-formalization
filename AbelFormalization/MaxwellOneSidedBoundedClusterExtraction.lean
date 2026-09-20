import AbelFormalization.MaxwellOneSidedClusterCoverage

/-!
# One-sided bounded cluster extraction

The general shrinking-source trichotomy allows both signs of infinity.  A
uniform lower bound on the supplied slopes rules out negative infinity and
retains either a finite cluster above the same cutoff or a positive-infinite
cluster.  The upper-bounded statement is the order-dual version.
-/

noncomputable section

open Set Filter Topology
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- A shrinking sequence of valid one-sided quotient points which stays
above a fixed cutoff has either a finite zero-step cluster above that cutoff
or a positive-infinite cluster at the limiting base. -/
theorem exists_maxwellOneSidedFiniteCluster_ge_or_positiveInfinity_of_sequence
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (side : MaxwellOneSidedStep) (cutoff : ℝ)
    {x : RealEuclidean p}
    {source : ℕ → RealEuclidean p × ℝ} {slope : ℕ → ℝ}
    (hsource : Tendsto source atTop (nhds (x, 0)))
    (hstep : ∀ n, 0 < (source n).2)
    (hpoint : ∀ n,
      realEuclideanAppend
          (realEuclideanAppend (source n).1
            (fun _ : Fin 1 ↦ slope n))
          (fun _ : Fin 1 ↦ side.sign * (source n).2) ∈
        maxwellStepLastDifferenceQuotientRelation U R i)
    (hcutoff : ∀ n, cutoff ≤ slope n) :
    (∃ y : ℝ, cutoff ≤ y ∧
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellOneSidedStepZeroTrace U R i side) ∨
      x ∈ maxwellOneSidedInfinityBase U R i side .positive := by
  by_cases habove : BddAbove (Set.range slope)
  · have hbelow : BddBelow (Set.range slope) := by
      refine ⟨cutoff, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact hcutoff n
    have hbounded : Bornology.IsBounded (Set.range slope) :=
      isBounded_iff_bddBelow_bddAbove.mpr ⟨hbelow, habove⟩
    obtain ⟨y, _hyClosure, φ, hφmono, hslopeLimit⟩ :=
      tendsto_subseq_of_bounded hbounded
        (fun n ↦ Set.mem_range_self n)
    have hφTop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    have hcutoffLimit : cutoff ≤ y :=
      ge_of_tendsto' hslopeLimit (fun n ↦ hcutoff (φ n))
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
    apply Or.inl
    exact ⟨y, hcutoffLimit,
      (mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
        U R i side x y).2 ⟨hfinite⟩⟩
  · have hextract : ∀ n : ℕ, ∃ k : ℕ,
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
    apply Or.inr
    exact (mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
      U R i side .positive x).2 ⟨hinfinite⟩

/-- A shrinking sequence of valid one-sided quotient points which stays
below a fixed cutoff has either a finite zero-step cluster below that cutoff
or a negative-infinite cluster at the limiting base. -/
theorem exists_maxwellOneSidedFiniteCluster_le_or_negativeInfinity_of_sequence
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (side : MaxwellOneSidedStep) (cutoff : ℝ)
    {x : RealEuclidean p}
    {source : ℕ → RealEuclidean p × ℝ} {slope : ℕ → ℝ}
    (hsource : Tendsto source atTop (nhds (x, 0)))
    (hstep : ∀ n, 0 < (source n).2)
    (hpoint : ∀ n,
      realEuclideanAppend
          (realEuclideanAppend (source n).1
            (fun _ : Fin 1 ↦ slope n))
          (fun _ : Fin 1 ↦ side.sign * (source n).2) ∈
        maxwellStepLastDifferenceQuotientRelation U R i)
    (hcutoff : ∀ n, slope n ≤ cutoff) :
    (∃ y : ℝ, y ≤ cutoff ∧
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellOneSidedStepZeroTrace U R i side) ∨
      x ∈ maxwellOneSidedInfinityBase U R i side .negative := by
  by_cases hbelow : BddBelow (Set.range slope)
  · have habove : BddAbove (Set.range slope) := by
      refine ⟨cutoff, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact hcutoff n
    have hbounded : Bornology.IsBounded (Set.range slope) :=
      isBounded_iff_bddBelow_bddAbove.mpr ⟨hbelow, habove⟩
    obtain ⟨y, _hyClosure, φ, hφmono, hslopeLimit⟩ :=
      tendsto_subseq_of_bounded hbounded
        (fun n ↦ Set.mem_range_self n)
    have hφTop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    have hcutoffLimit : y ≤ cutoff :=
      le_of_tendsto' hslopeLimit (fun n ↦ hcutoff (φ n))
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
    apply Or.inl
    exact ⟨y, hcutoffLimit,
      (mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
        U R i side x y).2 ⟨hfinite⟩⟩
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
    apply Or.inr
    exact (mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
      U R i side .negative x).2 ⟨hinfinite⟩

end AbelFormalization
