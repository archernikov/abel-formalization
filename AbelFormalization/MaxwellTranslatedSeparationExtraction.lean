import AbelFormalization.MaxwellChosenInfinitySmallness
import AbelFormalization.MaxwellLocalizedOneSidedIVT
import AbelFormalization.MaxwellOneSidedBoundedClusterExtraction

/-!
# Fixed-base extraction of Maxwell's translated slope obstruction

The translated quotient identity itself is already formalized in
`MaxwellSlopeClusterSmallness`.  The genuinely local input used before that
identity is a uniform separation of the right and reflected-left quotients at
the *same* base point, on a smaller open set and for all sufficiently small
positive steps.

This file isolates that input and proves the geometric translation step.  The
input only has to hold inside the original open pseudofunction domain.  A
separate closure lemma shows that every cross-side disagreement base lies in
the closure of that domain, so an arbitrary open piece of the disagreement
locus can first be localized back into the domain.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Topology MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## The fixed-base local-uniform source input -/

/-- Uniform fixed-base separation data on a smaller open subset of `V`.

The two quotients in `separated` are evaluated at the same base point.  The
conclusion needed by Maxwell evaluates the reflected-left quotient at the
translated base point; that passage is proved below using only openness. -/
structure MaxwellUniformFixedBaseOneSidedSeparationData {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (V : Set (RealEuclidean p)) where
  W : Set (RealEuclidean p)
  W_open : IsOpen W
  W_nonempty : W.Nonempty
  W_subset : W ⊆ V
  orientation : MaxwellSlopeSeparationOrientation
  cutoff : ℝ
  stepBound : ℝ
  stepBound_pos : 0 < stepBound
  separated : ∀ x ∈ W, ∀ t : ℝ, 0 < t → t < stepBound →
    MaxwellOrientedSlopeSeparation orientation
      (maxwellRightDifferenceQuotient f i x t)
      (maxwellReflectedLeftDifferenceQuotient f i x t)
      cutoff

/-- The exact local-uniform bridge left by the source argument.  It is stated
only on open subsets of `U ∩ A`; boundary points of `U` are handled by the
closure localization theorem below. -/
def MaxwellLocallyUniformFixedBaseOneSidedSeparationOn {p : ℕ}
    (U : Set (RealEuclidean p)) (f : RealEuclidean p → ℝ)
    (i : Fin p) (A : Set (RealEuclidean p)) : Prop :=
  ∀ V : Set (RealEuclidean p), IsOpen V → V.Nonempty → V ⊆ U ∩ A →
    Nonempty (MaxwellUniformFixedBaseOneSidedSeparationData f i V)

/-- A moving-base neighborhood bound for one selected side of the chosen
difference quotient.  This is stronger than a limit with the base held
fixed, and is the form forced by uniqueness of the source-defined extended
fiber. -/
def MaxwellOneSidedDifferenceQuotientLocallyLtAt {p : ℕ}
    (U : Set (RealEuclidean p)) (f : RealEuclidean p → ℝ)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (x : RealEuclidean p) (cutoff : ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ z : RealEuclidean p × ℝ,
      z ∈ maxwellOneSidedStepDomain U i side →
      dist z.1 x < ρ → z.2 < δ →
      maxwellOneSidedDifferenceQuotient f i side z < cutoff

/-- The lower-bound counterpart of
`MaxwellOneSidedDifferenceQuotientLocallyLtAt`. -/
def MaxwellOneSidedDifferenceQuotientLocallyGtAt {p : ℕ}
    (U : Set (RealEuclidean p)) (f : RealEuclidean p → ℝ)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (x : RealEuclidean p) (cutoff : ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ z : RealEuclidean p × ℝ,
      z ∈ maxwellOneSidedStepDomain U i side →
      dist z.1 x < ρ → z.2 < δ →
      cutoff < maxwellOneSidedDifferenceQuotient f i side z

/-! ## Sequential negations of moving-base bounds -/

private theorem exists_shrinking_oneSidedQuotient_ge_sequence_of_not_local_lt
    {p : ℕ} {U : Set (RealEuclidean p)}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    {side : MaxwellOneSidedStep} {x : RealEuclidean p} {cutoff : ℝ}
    (hnot : ¬ MaxwellOneSidedDifferenceQuotientLocallyLtAt
      U f i side x cutoff) :
    ∃ source : ℕ → RealEuclidean p × ℝ,
      (∀ n, source n ∈ maxwellOneSidedStepDomain U i side) ∧
      Tendsto source atTop (nhds (x, 0)) ∧
      ∀ n, cutoff ≤
        maxwellOneSidedDifferenceQuotient f i side (source n) := by
  let scale : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hscalePos (n : ℕ) : 0 < scale n := by
    dsimp only [scale]
    positivity
  have hwitness (n : ℕ) :
      ∃ z : RealEuclidean p × ℝ,
        z ∈ maxwellOneSidedStepDomain U i side ∧
        dist z.1 x < scale n ∧ z.2 < scale n ∧
        cutoff ≤ maxwellOneSidedDifferenceQuotient f i side z := by
    by_contra hnone
    apply hnot
    refine ⟨scale n, hscalePos n, scale n, hscalePos n, ?_⟩
    intro z hz hdist hstep
    exact lt_of_not_ge fun hge ↦
      hnone ⟨z, hz, hdist, hstep, hge⟩
  choose source hsourceDomain hbaseBound hstepBound hslopeBound using hwitness
  have hscaleZero : Tendsto scale atTop (nhds 0) := by
    simpa only [scale] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbase : Tendsto (fun n ↦ (source n).1) atTop (nhds x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ dist_nonneg)
      (fun n ↦ (hbaseBound n).le) hscaleZero
  have hstep : Tendsto (fun n ↦ (source n).2) atTop (nhds 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ by
      rw [Real.dist_eq, sub_zero,
        abs_of_pos (hsourceDomain n).2.2]
      exact (hstepBound n).le) hscaleZero
  exact ⟨source, hsourceDomain,
    (by simpa only [nhds_prod_eq] using hbase.prodMk hstep), hslopeBound⟩

private theorem exists_shrinking_oneSidedQuotient_le_sequence_of_not_local_gt
    {p : ℕ} {U : Set (RealEuclidean p)}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    {side : MaxwellOneSidedStep} {x : RealEuclidean p} {cutoff : ℝ}
    (hnot : ¬ MaxwellOneSidedDifferenceQuotientLocallyGtAt
      U f i side x cutoff) :
    ∃ source : ℕ → RealEuclidean p × ℝ,
      (∀ n, source n ∈ maxwellOneSidedStepDomain U i side) ∧
      Tendsto source atTop (nhds (x, 0)) ∧
      ∀ n, maxwellOneSidedDifferenceQuotient f i side (source n) ≤ cutoff := by
  let scale : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hscalePos (n : ℕ) : 0 < scale n := by
    dsimp only [scale]
    positivity
  have hwitness (n : ℕ) :
      ∃ z : RealEuclidean p × ℝ,
        z ∈ maxwellOneSidedStepDomain U i side ∧
        dist z.1 x < scale n ∧ z.2 < scale n ∧
        maxwellOneSidedDifferenceQuotient f i side z ≤ cutoff := by
    by_contra hnone
    apply hnot
    refine ⟨scale n, hscalePos n, scale n, hscalePos n, ?_⟩
    intro z hz hdist hstep
    exact lt_of_not_ge fun hle ↦
      hnone ⟨z, hz, hdist, hstep, hle⟩
  choose source hsourceDomain hbaseBound hstepBound hslopeBound using hwitness
  have hscaleZero : Tendsto scale atTop (nhds 0) := by
    simpa only [scale] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbase : Tendsto (fun n ↦ (source n).1) atTop (nhds x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ dist_nonneg)
      (fun n ↦ (hbaseBound n).le) hscaleZero
  have hstep : Tendsto (fun n ↦ (source n).2) atTop (nhds 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ by
      rw [Real.dist_eq, sub_zero,
        abs_of_pos (hsourceDomain n).2.2]
      exact (hstepBound n).le) hscaleZero
  exact ⟨source, hsourceDomain,
    (by simpa only [nhds_prod_eq] using hbase.prodMk hstep), hslopeBound⟩

/-! ## Singleton extended fibers force moving-base bounds -/

/-- The chosen quotient supplies a point of the source step-last relation at
every valid one-sided source. -/
theorem IsMaxwellPseudofunctionOn.chosen_oneSidedDifferenceQuotient_mem_stepLast
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (i : Fin p)
    (side : MaxwellOneSidedStep) {z : RealEuclidean p × ℝ}
    (hz : z ∈ maxwellOneSidedStepDomain U i side) :
    realEuclideanAppend
        (realEuclideanAppend z.1
          (fun _ : Fin 1 ↦
            maxwellOneSidedDifferenceQuotient
              (maxwellChosenScalarValue R) i side z))
        (fun _ : Fin 1 ↦ side.sign * z.2) ∈
      maxwellStepLastDifferenceQuotientRelation U R i := by
  let f : RealEuclidean p → ℝ := maxwellChosenScalarValue R
  let G : MaxwellRelation p 1 :=
    maxwellFunctionGraph U (fun x _ ↦ f x)
  have hGrep : MaxwellRelation.RepresentsOn G U
      (fun x : RealEuclidean p ↦ fun _ : Fin 1 ↦ f x) :=
    MaxwellRelation.representsOn_functionGraph U
      (fun x : RealEuclidean p ↦ fun _ : Fin 1 ↦ f x)
  have hGR : G ⊆ R := by
    simpa only [G, f] using hR.chosenScalarGraph_subset
  apply maxwellStepLastDifferenceQuotientRelation_mono hGR i
  exact
    ((realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_oneSided_of_representsOn_iff
      i hGrep side z.1 z.2
        (maxwellOneSidedDifferenceQuotient f i side z)).2
      ⟨hz, rfl⟩).1

/-- A unique finite extended slope gives a moving-base upper bound above its
value.  A violating sequence would have either a second finite cluster above
the cutoff or a positive-infinite cluster. -/
theorem IsMaxwellPseudofunctionOn.oneSidedDifferenceQuotient_locally_lt_of_unique_finite
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (i : Fin p)
    (side : MaxwellOneSidedStep) {x : RealEuclidean p}
    {d cutoff : ℝ}
    (hd : MaxwellExtendedSlopeValue.finite d ∈
      maxwellExtendedSlopeFiber
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) x)
    (hunique : ∀ a,
      a ∈ maxwellExtendedSlopeFiber
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) x →
      a = .finite d)
    (hdcutoff : d < cutoff) :
    MaxwellOneSidedDifferenceQuotientLocallyLtAt U
      (maxwellChosenScalarValue R) i side x cutoff := by
  by_contra hnot
  obtain ⟨source, hsourceDomain, hsource, hcutoff⟩ :=
    exists_shrinking_oneSidedQuotient_ge_sequence_of_not_local_lt hnot
  let slope : ℕ → ℝ := fun n ↦
    maxwellOneSidedDifferenceQuotient
      (maxwellChosenScalarValue R) i side (source n)
  have hpoint : ∀ n,
      realEuclideanAppend
          (realEuclideanAppend (source n).1
            (fun _ : Fin 1 ↦ slope n))
          (fun _ : Fin 1 ↦ side.sign * (source n).2) ∈
        maxwellStepLastDifferenceQuotientRelation U R i := by
    intro n
    exact hR.chosen_oneSidedDifferenceQuotient_mem_stepLast
      i side (hsourceDomain n)
  have hcluster :=
    exists_maxwellOneSidedFiniteCluster_ge_or_positiveInfinity_of_sequence
      i side cutoff hsource (fun n ↦ (hsourceDomain n).2.2)
        hpoint hcutoff
  rcases hcluster with ⟨y, hycutoff, hy⟩ | hinfinity
  · have hymem : MaxwellExtendedSlopeValue.finite y ∈
        maxwellExtendedSlopeFiber
          (maxwellOneSidedStepZeroTrace U R i side)
          (maxwellOneSidedInfinityBase U R i side .positive)
          (maxwellOneSidedInfinityBase U R i side .negative) x :=
      (finite_mem_maxwellExtendedSlopeFiber_iff _ _ _ x y).2 hy
    have hyd : y = d := MaxwellExtendedSlopeValue.finite.inj (hunique _ hymem)
    linarith
  · have himem : MaxwellExtendedSlopeValue.positiveInfinity ∈
        maxwellExtendedSlopeFiber
          (maxwellOneSidedStepZeroTrace U R i side)
          (maxwellOneSidedInfinityBase U R i side .positive)
          (maxwellOneSidedInfinityBase U R i side .negative) x :=
      (positiveInfinity_mem_maxwellExtendedSlopeFiber_iff _ _ _ x).2
        hinfinity
    simpa using hunique _ himem

/-- A unique finite extended slope gives the dual moving-base lower bound
below its value. -/
theorem IsMaxwellPseudofunctionOn.oneSidedDifferenceQuotient_locally_gt_of_unique_finite
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (i : Fin p)
    (side : MaxwellOneSidedStep) {x : RealEuclidean p}
    {d cutoff : ℝ}
    (hd : MaxwellExtendedSlopeValue.finite d ∈
      maxwellExtendedSlopeFiber
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) x)
    (hunique : ∀ a,
      a ∈ maxwellExtendedSlopeFiber
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) x →
      a = .finite d)
    (hcutoffd : cutoff < d) :
    MaxwellOneSidedDifferenceQuotientLocallyGtAt U
      (maxwellChosenScalarValue R) i side x cutoff := by
  by_contra hnot
  obtain ⟨source, hsourceDomain, hsource, hcutoff⟩ :=
    exists_shrinking_oneSidedQuotient_le_sequence_of_not_local_gt hnot
  let slope : ℕ → ℝ := fun n ↦
    maxwellOneSidedDifferenceQuotient
      (maxwellChosenScalarValue R) i side (source n)
  have hpoint : ∀ n,
      realEuclideanAppend
          (realEuclideanAppend (source n).1
            (fun _ : Fin 1 ↦ slope n))
          (fun _ : Fin 1 ↦ side.sign * (source n).2) ∈
        maxwellStepLastDifferenceQuotientRelation U R i := by
    intro n
    exact hR.chosen_oneSidedDifferenceQuotient_mem_stepLast
      i side (hsourceDomain n)
  have hcluster :=
    exists_maxwellOneSidedFiniteCluster_le_or_negativeInfinity_of_sequence
      i side cutoff hsource (fun n ↦ (hsourceDomain n).2.2)
        hpoint hcutoff
  rcases hcluster with ⟨y, hycutoff, hy⟩ | hinfinity
  · have hymem : MaxwellExtendedSlopeValue.finite y ∈
        maxwellExtendedSlopeFiber
          (maxwellOneSidedStepZeroTrace U R i side)
          (maxwellOneSidedInfinityBase U R i side .positive)
          (maxwellOneSidedInfinityBase U R i side .negative) x :=
      (finite_mem_maxwellExtendedSlopeFiber_iff _ _ _ x y).2 hy
    have hyd : y = d := MaxwellExtendedSlopeValue.finite.inj (hunique _ hymem)
    linarith
  · have himem : MaxwellExtendedSlopeValue.negativeInfinity ∈
        maxwellExtendedSlopeFiber
          (maxwellOneSidedStepZeroTrace U R i side)
          (maxwellOneSidedInfinityBase U R i side .positive)
          (maxwellOneSidedInfinityBase U R i side .negative) x :=
      (negativeInfinity_mem_maxwellExtendedSlopeFiber_iff _ _ _ x).2
        hinfinity
    simpa using hunique _ himem

/-- A singleton positive-infinite extended fiber forces every sufficiently
nearby positive-step quotient above any prescribed finite cutoff. -/
theorem IsMaxwellPseudofunctionOn.oneSidedDifferenceQuotient_locally_gt_of_unique_positiveInfinity
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (i : Fin p)
    (side : MaxwellOneSidedStep) {x : RealEuclidean p} {cutoff : ℝ}
    (hinfinity : MaxwellExtendedSlopeValue.positiveInfinity ∈
      maxwellExtendedSlopeFiber
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) x)
    (hunique : ∀ a,
      a ∈ maxwellExtendedSlopeFiber
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) x →
      a = .positiveInfinity) :
    MaxwellOneSidedDifferenceQuotientLocallyGtAt U
      (maxwellChosenScalarValue R) i side x cutoff := by
  by_contra hnot
  obtain ⟨source, hsourceDomain, hsource, hcutoff⟩ :=
    exists_shrinking_oneSidedQuotient_le_sequence_of_not_local_gt hnot
  let slope : ℕ → ℝ := fun n ↦
    maxwellOneSidedDifferenceQuotient
      (maxwellChosenScalarValue R) i side (source n)
  have hpoint : ∀ n,
      realEuclideanAppend
          (realEuclideanAppend (source n).1
            (fun _ : Fin 1 ↦ slope n))
          (fun _ : Fin 1 ↦ side.sign * (source n).2) ∈
        maxwellStepLastDifferenceQuotientRelation U R i := by
    intro n
    exact hR.chosen_oneSidedDifferenceQuotient_mem_stepLast
      i side (hsourceDomain n)
  have hcluster :=
    exists_maxwellOneSidedFiniteCluster_le_or_negativeInfinity_of_sequence
      i side cutoff hsource (fun n ↦ (hsourceDomain n).2.2)
        hpoint hcutoff
  rcases hcluster with ⟨y, _hycutoff, hy⟩ | hnegative
  · have hymem : MaxwellExtendedSlopeValue.finite y ∈
        maxwellExtendedSlopeFiber
          (maxwellOneSidedStepZeroTrace U R i side)
          (maxwellOneSidedInfinityBase U R i side .positive)
          (maxwellOneSidedInfinityBase U R i side .negative) x :=
      (finite_mem_maxwellExtendedSlopeFiber_iff _ _ _ x y).2 hy
    simpa using hunique _ hymem
  · have hnegativeMem : MaxwellExtendedSlopeValue.negativeInfinity ∈
        maxwellExtendedSlopeFiber
          (maxwellOneSidedStepZeroTrace U R i side)
          (maxwellOneSidedInfinityBase U R i side .positive)
          (maxwellOneSidedInfinityBase U R i side .negative) x :=
      (negativeInfinity_mem_maxwellExtendedSlopeFiber_iff _ _ _ x).2
        hnegative
    simpa using hunique _ hnegativeMem

/-- A singleton negative-infinite extended fiber forces every sufficiently
nearby positive-step quotient below any prescribed finite cutoff. -/
theorem IsMaxwellPseudofunctionOn.oneSidedDifferenceQuotient_locally_lt_of_unique_negativeInfinity
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (i : Fin p)
    (side : MaxwellOneSidedStep) {x : RealEuclidean p} {cutoff : ℝ}
    (hinfinity : MaxwellExtendedSlopeValue.negativeInfinity ∈
      maxwellExtendedSlopeFiber
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) x)
    (hunique : ∀ a,
      a ∈ maxwellExtendedSlopeFiber
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) x →
      a = .negativeInfinity) :
    MaxwellOneSidedDifferenceQuotientLocallyLtAt U
      (maxwellChosenScalarValue R) i side x cutoff := by
  by_contra hnot
  obtain ⟨source, hsourceDomain, hsource, hcutoff⟩ :=
    exists_shrinking_oneSidedQuotient_ge_sequence_of_not_local_lt hnot
  let slope : ℕ → ℝ := fun n ↦
    maxwellOneSidedDifferenceQuotient
      (maxwellChosenScalarValue R) i side (source n)
  have hpoint : ∀ n,
      realEuclideanAppend
          (realEuclideanAppend (source n).1
            (fun _ : Fin 1 ↦ slope n))
          (fun _ : Fin 1 ↦ side.sign * (source n).2) ∈
        maxwellStepLastDifferenceQuotientRelation U R i := by
    intro n
    exact hR.chosen_oneSidedDifferenceQuotient_mem_stepLast
      i side (hsourceDomain n)
  have hcluster :=
    exists_maxwellOneSidedFiniteCluster_ge_or_positiveInfinity_of_sequence
      i side cutoff hsource (fun n ↦ (hsourceDomain n).2.2)
        hpoint hcutoff
  rcases hcluster with ⟨y, _hycutoff, hy⟩ | hpositive
  · have hymem : MaxwellExtendedSlopeValue.finite y ∈
        maxwellExtendedSlopeFiber
          (maxwellOneSidedStepZeroTrace U R i side)
          (maxwellOneSidedInfinityBase U R i side .positive)
          (maxwellOneSidedInfinityBase U R i side .negative) x :=
      (finite_mem_maxwellExtendedSlopeFiber_iff _ _ _ x y).2 hy
    simpa using hunique _ hymem
  · have hpositiveMem : MaxwellExtendedSlopeValue.positiveInfinity ∈
        maxwellExtendedSlopeFiber
          (maxwellOneSidedStepZeroTrace U R i side)
          (maxwellOneSidedInfinityBase U R i side .positive)
          (maxwellOneSidedInfinityBase U R i side .negative) x :=
      (positiveInfinity_mem_maxwellExtendedSlopeFiber_iff _ _ _ x).2
        hpositive
    simpa using hunique _ hpositiveMem

/-! ## Two local bounds give the translated obstruction -/

private theorem exists_translatedSlopeSeparationObstruction_of_local_rightBelowLeft
    {p : ℕ} {U V : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {i : Fin p}
    {x : RealEuclidean p} {cutoff : ℝ}
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hxU : x ∈ U) (hxV : x ∈ V)
    (hright : MaxwellOneSidedDifferenceQuotientLocallyLtAt U
      (maxwellChosenScalarValue R) i .positive x cutoff)
    (hleft : MaxwellOneSidedDifferenceQuotientLocallyGtAt U
      (maxwellChosenScalarValue R) i .negative x cutoff) :
    Nonempty (MaxwellTranslatedSlopeSeparationObstruction
      (maxwellChosenScalarValue R) i V) := by
  rcases hright with ⟨ρr, hρr, δr, hδr, hright⟩
  rcases hleft with ⟨ρl, hρl, δl, hδl, hleft⟩
  have hopen : IsOpen (V ∩ U) := hVopen.inter hUopen
  obtain ⟨ε, hε, hball⟩ :=
    (Metric.isOpen_iff.mp hopen) x ⟨hxV, hxU⟩
  let bound : ℝ := min ε (min ρr (min ρl (min δr δl)))
  have hbound : 0 < bound := by
    dsimp only [bound]
    exact lt_min hε (lt_min hρr (lt_min hρl (lt_min hδr hδl)))
  have hboundε : bound ≤ ε := by
    dsimp only [bound]
    exact min_le_left _ _
  have hboundρr : bound ≤ ρr := by
    dsimp only [bound]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hboundρl : bound ≤ ρl := by
    dsimp only [bound]
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hboundδr : bound ≤ δr := by
    dsimp only [bound]
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have hboundδl : bound ≤ δl := by
    dsimp only [bound]
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  let step : ℝ := bound / 2
  let y : RealEuclidean p :=
    x + step • (Pi.single i 1 : RealEuclidean p)
  have hstep : 0 < step := half_pos hbound
  have hstepBound : step < bound := half_lt_self hbound
  have hstepε : step < ε := hstepBound.trans_le hboundε
  have hstepρr : step < ρr := hstepBound.trans_le hboundρr
  have hstepρl : step < ρl := hstepBound.trans_le hboundρl
  have hstepδr : step < δr := hstepBound.trans_le hboundδr
  have hstepδl : step < δl := hstepBound.trans_le hboundδl
  have hydist : dist y x = step := by
    dsimp only [y]
    rw [dist_self_add_left, norm_smul, Pi.norm_single]
    simp only [Real.norm_eq_abs, abs_one, mul_one, abs_of_pos hstep]
  have hcancel :
      y + (MaxwellOneSidedStep.negative.sign * step) •
          (Pi.single i 1 : RealEuclidean p) = x := by
    dsimp only [y]
    simp only [MaxwellOneSidedStep.sign_negative, neg_mul,
      one_mul, neg_smul, add_neg_cancel_right]
  have hyVU : y ∈ V ∩ U := by
    apply hball
    rw [Metric.mem_ball, hydist]
    exact hstepε
  have hrightDomain :
      (x, step) ∈ maxwellOneSidedStepDomain U i .positive := by
    refine ⟨hxU, ?_, hstep⟩
    simpa [y, MaxwellOneSidedStep.sign]
      using hyVU.2
  have hleftDomain :
      (y, step) ∈ maxwellOneSidedStepDomain U i .negative := by
    refine ⟨hyVU.2, ?_, hstep⟩
    simpa only [hcancel] using hxU
  have hrightCut := hright (x, step) hrightDomain
    (by simpa using hρr) hstepδr
  have hleftCut := hleft (y, step) hleftDomain (by
    rw [hydist]
    exact hstepρl) hstepδl
  refine ⟨{
    x := x
    step := step
    cutoff := cutoff
    orientation := .rightBelowLeft
    step_pos := hstep
    x_mem := hxV
    translated_mem := hyVU.1
    separated := ?_ }⟩
  constructor
  · simpa [maxwellOneSidedDifferenceQuotient,
      maxwellRightDifferenceQuotient,
      MaxwellOneSidedStep.sign] using hrightCut
  · simpa [maxwellOneSidedDifferenceQuotient,
      maxwellReflectedLeftDifferenceQuotient,
      MaxwellOneSidedStep.sign, hcancel, y] using hleftCut

private theorem exists_translatedSlopeSeparationObstruction_of_local_leftBelowRight
    {p : ℕ} {U V : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {i : Fin p}
    {x : RealEuclidean p} {cutoff : ℝ}
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hxU : x ∈ U) (hxV : x ∈ V)
    (hright : MaxwellOneSidedDifferenceQuotientLocallyGtAt U
      (maxwellChosenScalarValue R) i .positive x cutoff)
    (hleft : MaxwellOneSidedDifferenceQuotientLocallyLtAt U
      (maxwellChosenScalarValue R) i .negative x cutoff) :
    Nonempty (MaxwellTranslatedSlopeSeparationObstruction
      (maxwellChosenScalarValue R) i V) := by
  rcases hright with ⟨ρr, hρr, δr, hδr, hright⟩
  rcases hleft with ⟨ρl, hρl, δl, hδl, hleft⟩
  have hopen : IsOpen (V ∩ U) := hVopen.inter hUopen
  obtain ⟨ε, hε, hball⟩ :=
    (Metric.isOpen_iff.mp hopen) x ⟨hxV, hxU⟩
  let bound : ℝ := min ε (min ρr (min ρl (min δr δl)))
  have hbound : 0 < bound := by
    dsimp only [bound]
    exact lt_min hε (lt_min hρr (lt_min hρl (lt_min hδr hδl)))
  have hboundε : bound ≤ ε := by
    dsimp only [bound]
    exact min_le_left _ _
  have hboundρr : bound ≤ ρr := by
    dsimp only [bound]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hboundρl : bound ≤ ρl := by
    dsimp only [bound]
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hboundδr : bound ≤ δr := by
    dsimp only [bound]
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have hboundδl : bound ≤ δl := by
    dsimp only [bound]
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  let step : ℝ := bound / 2
  let y : RealEuclidean p :=
    x + step • (Pi.single i 1 : RealEuclidean p)
  have hstep : 0 < step := half_pos hbound
  have hstepBound : step < bound := half_lt_self hbound
  have hstepε : step < ε := hstepBound.trans_le hboundε
  have hstepρr : step < ρr := hstepBound.trans_le hboundρr
  have hstepρl : step < ρl := hstepBound.trans_le hboundρl
  have hstepδr : step < δr := hstepBound.trans_le hboundδr
  have hstepδl : step < δl := hstepBound.trans_le hboundδl
  have hydist : dist y x = step := by
    dsimp only [y]
    rw [dist_self_add_left, norm_smul, Pi.norm_single]
    simp only [Real.norm_eq_abs, abs_one, mul_one, abs_of_pos hstep]
  have hcancel :
      y + (MaxwellOneSidedStep.negative.sign * step) •
          (Pi.single i 1 : RealEuclidean p) = x := by
    dsimp only [y]
    simp only [MaxwellOneSidedStep.sign_negative, neg_mul,
      one_mul, neg_smul, add_neg_cancel_right]
  have hyVU : y ∈ V ∩ U := by
    apply hball
    rw [Metric.mem_ball, hydist]
    exact hstepε
  have hrightDomain :
      (x, step) ∈ maxwellOneSidedStepDomain U i .positive := by
    refine ⟨hxU, ?_, hstep⟩
    simpa [y, MaxwellOneSidedStep.sign]
      using hyVU.2
  have hleftDomain :
      (y, step) ∈ maxwellOneSidedStepDomain U i .negative := by
    refine ⟨hyVU.2, ?_, hstep⟩
    simpa only [hcancel] using hxU
  have hrightCut := hright (x, step) hrightDomain
    (by simpa using hρr) hstepδr
  have hleftCut := hleft (y, step) hleftDomain (by
    rw [hydist]
    exact hstepρl) hstepδl
  refine ⟨{
    x := x
    step := step
    cutoff := cutoff
    orientation := .leftBelowRight
    step_pos := hstep
    x_mem := hxV
    translated_mem := hyVU.1
    separated := ?_ }⟩
  constructor
  · simpa [maxwellOneSidedDifferenceQuotient,
      maxwellReflectedLeftDifferenceQuotient,
      MaxwellOneSidedStep.sign, hcancel, y] using hleftCut
  · simpa [maxwellOneSidedDifferenceQuotient,
      maxwellRightDifferenceQuotient,
      MaxwellOneSidedStep.sign] using hrightCut

/-! ## Singleton cross-side fibers force the translated obstruction -/

/-- At a point where the two one-sided extended fibers are singleton and
their unique values disagree, pseudofunctionality forces a translated slope
separation obstruction in every open neighborhood.  This is the full
finite/infinite nine-case classification behind the source argument. -/
theorem IsMaxwellPseudofunctionOn.exists_translatedSlopeSeparationObstruction_of_unique_disagreeing_fibers
    {p : ℕ} {U V : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {i : Fin p} {x : RealEuclidean p}
    (hR : IsMaxwellPseudofunctionOn U R)
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hxU : x ∈ U) (hxV : x ∈ V)
    {a b : MaxwellExtendedSlopeValue}
    (ha : a ∈ maxwellExtendedSlopeFiber
      (maxwellPositiveStepZeroTrace U R i)
      (maxwellPositiveStepPositiveInfinityBase U R i)
      (maxwellPositiveStepNegativeInfinityBase U R i) x)
    (hb : b ∈ maxwellExtendedSlopeFiber
      (maxwellNegativeStepZeroTrace U R i)
      (maxwellNegativeStepPositiveInfinityBase U R i)
      (maxwellNegativeStepNegativeInfinityBase U R i) x)
    (hab : a ≠ b)
    (huniqueR : ∀ c,
      c ∈ maxwellExtendedSlopeFiber
        (maxwellPositiveStepZeroTrace U R i)
        (maxwellPositiveStepPositiveInfinityBase U R i)
        (maxwellPositiveStepNegativeInfinityBase U R i) x → c = a)
    (huniqueL : ∀ c,
      c ∈ maxwellExtendedSlopeFiber
        (maxwellNegativeStepZeroTrace U R i)
        (maxwellNegativeStepPositiveInfinityBase U R i)
        (maxwellNegativeStepNegativeInfinityBase U R i) x → c = b) :
    Nonempty (MaxwellTranslatedSlopeSeparationObstruction
      (maxwellChosenScalarValue R) i V) := by
  cases a with
  | finite r =>
      cases b with
      | finite l =>
          have hrl : r ≠ l := by
            intro h
            apply hab
            simpa only [h]
          rcases lt_or_gt_of_ne hrl with hrl | hlr
          · have hright :=
              hR.oneSidedDifferenceQuotient_locally_lt_of_unique_finite
                i .positive ha huniqueR (by linarith : r < (r + l) / 2)
            have hleft :=
              hR.oneSidedDifferenceQuotient_locally_gt_of_unique_finite
                i .negative hb huniqueL (by linarith : (r + l) / 2 < l)
            exact
              exists_translatedSlopeSeparationObstruction_of_local_rightBelowLeft
                hUopen hVopen hxU hxV hright hleft
          · have hright :=
              hR.oneSidedDifferenceQuotient_locally_gt_of_unique_finite
                i .positive ha huniqueR (by linarith : (r + l) / 2 < r)
            have hleft :=
              hR.oneSidedDifferenceQuotient_locally_lt_of_unique_finite
                i .negative hb huniqueL (by linarith : l < (r + l) / 2)
            exact
              exists_translatedSlopeSeparationObstruction_of_local_leftBelowRight
                hUopen hVopen hxU hxV hright hleft
      | positiveInfinity =>
          have hright :=
            hR.oneSidedDifferenceQuotient_locally_lt_of_unique_finite
              i .positive ha huniqueR (by linarith : r < r + 1)
          have hleft :=
            hR.oneSidedDifferenceQuotient_locally_gt_of_unique_positiveInfinity
              i .negative hb huniqueL (cutoff := r + 1)
          exact
            exists_translatedSlopeSeparationObstruction_of_local_rightBelowLeft
              hUopen hVopen hxU hxV hright hleft
      | negativeInfinity =>
          have hright :=
            hR.oneSidedDifferenceQuotient_locally_gt_of_unique_finite
              i .positive ha huniqueR (by linarith : r - 1 < r)
          have hleft :=
            hR.oneSidedDifferenceQuotient_locally_lt_of_unique_negativeInfinity
              i .negative hb huniqueL (cutoff := r - 1)
          exact
            exists_translatedSlopeSeparationObstruction_of_local_leftBelowRight
              hUopen hVopen hxU hxV hright hleft
  | positiveInfinity =>
      cases b with
      | finite l =>
          have hright :=
            hR.oneSidedDifferenceQuotient_locally_gt_of_unique_positiveInfinity
              i .positive ha huniqueR (cutoff := l + 1)
          have hleft :=
            hR.oneSidedDifferenceQuotient_locally_lt_of_unique_finite
              i .negative hb huniqueL (by linarith : l < l + 1)
          exact
            exists_translatedSlopeSeparationObstruction_of_local_leftBelowRight
              hUopen hVopen hxU hxV hright hleft
      | positiveInfinity => exact (hab rfl).elim
      | negativeInfinity =>
          have hright :=
            hR.oneSidedDifferenceQuotient_locally_gt_of_unique_positiveInfinity
              i .positive ha huniqueR (cutoff := 0)
          have hleft :=
            hR.oneSidedDifferenceQuotient_locally_lt_of_unique_negativeInfinity
              i .negative hb huniqueL (cutoff := 0)
          exact
            exists_translatedSlopeSeparationObstruction_of_local_leftBelowRight
              hUopen hVopen hxU hxV hright hleft
  | negativeInfinity =>
      cases b with
      | finite l =>
          have hright :=
            hR.oneSidedDifferenceQuotient_locally_lt_of_unique_negativeInfinity
              i .positive ha huniqueR (cutoff := l - 1)
          have hleft :=
            hR.oneSidedDifferenceQuotient_locally_gt_of_unique_finite
              i .negative hb huniqueL (by linarith : l - 1 < l)
          exact
            exists_translatedSlopeSeparationObstruction_of_local_rightBelowLeft
              hUopen hVopen hxU hxV hright hleft
      | positiveInfinity =>
          have hright :=
            hR.oneSidedDifferenceQuotient_locally_lt_of_unique_negativeInfinity
              i .positive ha huniqueR (cutoff := 0)
          have hleft :=
            hR.oneSidedDifferenceQuotient_locally_gt_of_unique_positiveInfinity
              i .negative hb huniqueL (cutoff := 0)
          exact
            exists_translatedSlopeSeparationObstruction_of_local_rightBelowLeft
              hUopen hVopen hxU hxV hright hleft
      | negativeInfinity => exact (hab rfl).elim

/-! ## Translation inside an open set -/

/-- Uniform same-base separation on an open set produces the translated
obstruction.  The step is chosen smaller than both the uniform separation
scale and the radius of an open ball in `W`. -/
theorem MaxwellUniformFixedBaseOneSidedSeparationData.translatedObstruction
    {p : ℕ} {f : RealEuclidean p → ℝ} {i : Fin p}
    {V : Set (RealEuclidean p)}
    (h : MaxwellUniformFixedBaseOneSidedSeparationData f i V) :
    Nonempty (MaxwellTranslatedSlopeSeparationObstruction f i V) := by
  obtain ⟨x, hxW⟩ := h.W_nonempty
  obtain ⟨ε, hεpos, hball⟩ :=
    (Metric.isOpen_iff.mp h.W_open) x hxW
  let step : ℝ := min (h.stepBound / 2) (ε / 2)
  have hstep : 0 < step := by
    dsimp only [step]
    exact lt_min (half_pos h.stepBound_pos) (half_pos hεpos)
  have hstepBound : step < h.stepBound := by
    dsimp only [step]
    exact (min_le_left _ _).trans_lt (half_lt_self h.stepBound_pos)
  have hstepε : step < ε := by
    dsimp only [step]
    exact (min_le_right _ _).trans_lt (half_lt_self hεpos)
  have htranslatedW :
      x + step • (Pi.single i 1 : RealEuclidean p) ∈ h.W := by
    apply hball
    rw [Metric.mem_ball, dist_self_add_left, norm_smul, Pi.norm_single]
    simp only [Real.norm_eq_abs, abs_one, mul_one, abs_of_pos hstep]
    exact hstepε
  have hxSeparated := h.separated x hxW step hstep hstepBound
  have htranslatedSeparated :=
    h.separated
      (x + step • (Pi.single i 1 : RealEuclidean p))
      htranslatedW step hstep hstepBound
  refine ⟨{
    x := x
    step := step
    cutoff := h.cutoff
    orientation := h.orientation
    step_pos := hstep
    x_mem := h.W_subset hxW
    translated_mem := h.W_subset htranslatedW
    separated := ?_ }⟩
  cases horientation : h.orientation with
  | rightBelowLeft =>
      simp only [horientation, MaxwellOrientedSlopeSeparation] at hxSeparated htranslatedSeparated ⊢
      exact ⟨hxSeparated.1, htranslatedSeparated.2⟩
  | leftBelowRight =>
      simp only [horientation, MaxwellOrientedSlopeSeparation] at hxSeparated htranslatedSeparated ⊢
      exact ⟨htranslatedSeparated.1, hxSeparated.2⟩

/-- If `A` lies in the closure of an open domain `U`, the local-uniform
fixed-base bridge inside `U` implies Maxwell's translated-separation
mechanism on all of `A`. -/
theorem maxwellTranslatedOneSidedSeparationMechanism_of_localUniformFixedBase
    {p : ℕ} {U A : Set (RealEuclidean p)}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    (hUopen : IsOpen U) (hAclosure : A ⊆ closure U)
    (hlocal : MaxwellLocallyUniformFixedBaseOneSidedSeparationOn
      U f i A) :
    MaxwellTranslatedOneSidedSeparationMechanism f i A := by
  intro V hVopen hVnonempty hVA
  obtain ⟨x, hxV⟩ := hVnonempty
  have hxClosure : x ∈ closure U := hAclosure (hVA hxV)
  rw [mem_closure_iff] at hxClosure
  obtain ⟨z, hzV, hzU⟩ := hxClosure V hVopen hxV
  have hVUopen : IsOpen (V ∩ U) := hVopen.inter hUopen
  have hVUnonempty : (V ∩ U).Nonempty := ⟨z, hzV, hzU⟩
  have hVUsubset : V ∩ U ⊆ U ∩ A := by
    intro y hy
    exact ⟨hy.2, hVA hy.1⟩
  obtain ⟨hdata⟩ :=
    hlocal (V ∩ U) hVUopen hVUnonempty hVUsubset
  obtain ⟨hobstruction⟩ := hdata.translatedObstruction
  refine ⟨{
    x := hobstruction.x
    step := hobstruction.step
    cutoff := hobstruction.cutoff
    orientation := hobstruction.orientation
    step_pos := hobstruction.step_pos
    x_mem := hobstruction.x_mem.1
    translated_mem := hobstruction.translated_mem.1
    separated := hobstruction.separated }⟩

/-! ## Specialization to the chosen Maxwell representative -/

/-- Every cross-side one-sided-slope disagreement base lies in the closure of
the original domain.  A finite right-hand cluster lies in the full zero-step
trace; either infinite right-hand cluster is covered by the source-defined
one-sided infinity closure theorem. -/
theorem maxwellOneSidedSlopeDisagreementLocus_subset_closure_domain
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    maxwellOneSidedSlopeDisagreementLocus U R i ⊆ closure U := by
  intro x hx
  rcases hx with ⟨a, b, ha, _hb, _hab⟩
  cases a with
  | finite y =>
      apply maxwellDifferenceQuotientZeroTrace_domain_subset_closure U R i
      refine ⟨(fun _ : Fin 1 ↦ y), ?_⟩
      rw [← maxwellPositiveStepZeroTrace_union_negativeStepZeroTrace U R i]
      exact Or.inl ha
  | positiveInfinity =>
      exact maxwellOneSidedInfinityBase_subset_closure_domain
        U R i .positive .positive ha
  | negativeInfinity =>
      exact maxwellOneSidedInfinityBase_subset_closure_domain
        U R i .positive .negative ha

/-- Source-shaped name for the one remaining local statement on the chosen
representative and the cross-side disagreement locus. -/
def MaxwellChosenSlopeDisagreementLocalUniformSeparation {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop :=
  MaxwellLocallyUniformFixedBaseOneSidedSeparationOn U
    (maxwellChosenScalarValue R) i
    (maxwellOneSidedSlopeDisagreementLocus U R i)

/-- The local-uniform fixed-base source statement eliminates the former
translated-separation field for the chosen representative. -/
theorem maxwellChosen_translatedOneSidedSeparation_of_localUniform
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hUopen : IsOpen U)
    (hlocal : MaxwellChosenSlopeDisagreementLocalUniformSeparation U R i) :
    MaxwellTranslatedOneSidedSeparationMechanism
      (maxwellChosenScalarValue R) i
      (maxwellOneSidedSlopeDisagreementLocus U R i) :=
  maxwellTranslatedOneSidedSeparationMechanism_of_localUniformFixedBase
    hUopen
    (maxwellOneSidedSlopeDisagreementLocus_subset_closure_domain U R i)
    hlocal

/-- The translated-separation mechanism for the chosen representative is a
theorem: the two one-sided multivalued loci are null, so every open piece of
the disagreement locus contains a point where both extended fibers are
singleton.  The preceding nine-case extraction then supplies the
obstruction.  No translated-separation source field is retained. -/
theorem maxwellChosen_translatedOneSidedSeparation
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hUopen : IsOpen U)
    (hU : U ∈ charbonnelClosure S p)
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunctionOn U R) :
    MaxwellTranslatedOneSidedSeparationMechanism
      (maxwellChosenScalarValue R) i
      (maxwellOneSidedSlopeDisagreementLocus U R i) := by
  have hp : 0 < p := maxwellFinArity_pos i
  have honeSided :=
    maxwellOneSidedExtendedSlopeBadLociSmallness_of_chosenContinuity
      hC hmem h21 h22 i hUopen hU hRmem hRpseudo
  let E : Set (RealEuclidean p) :=
    maxwellPositiveStepExtendedMultivaluedLocus U R i ∪
      maxwellNegativeStepExtendedMultivaluedLocus U R i
  have hEmem : E ∈ charbonnelClosure S p := by
    dsimp only [E]
    exact charbonnelClosure_union
      honeSided.clusterMembership.positiveExtendedMultivalued_mem
      honeSided.clusterMembership.negativeExtendedMultivalued_mem
  have hEnull : (volume : Measure (RealEuclidean p)) E = 0 := by
    dsimp only [E]
    exact measure_union_null
      honeSided.positiveBadLocus.locus_volume_eq_zero
      honeSided.negativeBadLocus.locus_volume_eq_zero
  have hEempty : interior E = ∅ := (h21 hp hEmem).1.mpr hEnull
  intro V hVopen hVnonempty hVA
  obtain ⟨v, hvV⟩ := hVnonempty
  have hvClosure : v ∈ closure U :=
    maxwellOneSidedSlopeDisagreementLocus_subset_closure_domain U R i
      (hVA hvV)
  rw [mem_closure_iff] at hvClosure
  obtain ⟨z, hzV, hzU⟩ := hvClosure V hVopen hvV
  have hVUopen : IsOpen (V ∩ U) := hVopen.inter hUopen
  have hVUnonempty : (V ∩ U).Nonempty := ⟨z, hzV, hzU⟩
  have hVU_not_subset : ¬ V ∩ U ⊆ E := by
    intro hsubset
    have hintoInterior : V ∩ U ⊆ interior E :=
      hVUopen.subset_interior_iff.mpr hsubset
    obtain ⟨w, hw⟩ := hVUnonempty
    have hwE : w ∈ interior E := hintoInterior hw
    simpa [hEempty] using hwE
  obtain ⟨x, hxVU, hxE⟩ := Set.not_subset.mp hVU_not_subset
  have hxPositive :
      x ∉ maxwellPositiveStepExtendedMultivaluedLocus U R i := by
    intro hx
    exact hxE (Or.inl hx)
  have hxNegative :
      x ∉ maxwellNegativeStepExtendedMultivaluedLocus U R i := by
    intro hx
    exact hxE (Or.inr hx)
  rcases hVA hxVU.1 with ⟨a, b, ha, hb, hab⟩
  have huniqueR : ∀ c,
      c ∈ maxwellExtendedSlopeFiber
        (maxwellPositiveStepZeroTrace U R i)
        (maxwellPositiveStepPositiveInfinityBase U R i)
        (maxwellPositiveStepNegativeInfinityBase U R i) x → c = a := by
    intro c hc
    by_contra hca
    apply hxPositive
    exact ⟨c, a, hc, ha, hca⟩
  have huniqueL : ∀ c,
      c ∈ maxwellExtendedSlopeFiber
        (maxwellNegativeStepZeroTrace U R i)
        (maxwellNegativeStepPositiveInfinityBase U R i)
        (maxwellNegativeStepNegativeInfinityBase U R i) x → c = b := by
    intro c hc
    by_contra hcb
    apply hxNegative
    exact ⟨c, b, hc, hb, hcb⟩
  exact
    hRpseudo.exists_translatedSlopeSeparationObstruction_of_unique_disagreeing_fibers
      hUopen hVopen hxVU.2 hxVU.1 ha hb hab huniqueR huniqueL

/-! ## Reduced hard-mechanism interface -/

/-- After translated separation has been derived, the only retained hard
mechanisms for a coordinate are the two equal-infinity affine chords. -/
structure MaxwellCoordinateAffineChordMechanisms
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
  positiveInfinity_affineChord : MaxwellWS5AffineChordCrossingMechanism
    (maxwellChosenScalarValue R) i .positiveInfinity
      (maxwellSamePositiveInfinityLocus U R i)
  negativeInfinity_affineChord : MaxwellWS5AffineChordCrossingMechanism
    (maxwellChosenScalarValue R) i .negativeInfinity
      (maxwellSameNegativeInfinityLocus U R i)

/-- The reduced two-chord interface supplies the previous three-field hard
mechanism structure, with translated separation filled canonically. -/
theorem MaxwellCoordinateAffineChordMechanisms.toHardSlopeMechanisms
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} (hUopen : IsOpen U)
    (hU : U ∈ charbonnelClosure S p)
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunctionOn U R)
    (hsource : MaxwellCoordinateAffineChordMechanisms U R i) :
    MaxwellCoordinateHardSlopeMechanisms U R i :=
  { positiveInfinity_affineChord := hsource.positiveInfinity_affineChord
    negativeInfinity_affineChord := hsource.negativeInfinity_affineChord
    differingSlopes_translatedSeparation :=
      maxwellChosen_translatedOneSidedSeparation
        hC hmem h21 h22 i hUopen hU hRmem hRpseudo }

/-- Under the established Charbonnel/pseudofunction hypotheses, the old
hard-mechanism structure is equivalent to supplying only its two affine
chords. -/
theorem maxwellCoordinateHardSlopeMechanisms_iff_affineChords
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} (hUopen : IsOpen U)
    (hU : U ∈ charbonnelClosure S p)
    (hRmem : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunctionOn U R) :
    MaxwellCoordinateHardSlopeMechanisms U R i ↔
      MaxwellCoordinateAffineChordMechanisms U R i := by
  constructor
  · intro h
    exact
      { positiveInfinity_affineChord := h.positiveInfinity_affineChord
        negativeInfinity_affineChord := h.negativeInfinity_affineChord }
  · exact fun h ↦ h.toHardSlopeMechanisms
      hC hmem h21 h22 hUopen hU hRmem hRpseudo

end AbelFormalization
