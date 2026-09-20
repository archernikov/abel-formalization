import AbelFormalization.CharbonnelIntegerAffineWeakStageSigns

/-!
# Frontier traces of nonzero integer-affine sign cells

For a genuine hyperplane, a small one-coordinate move from any point on
the hyperplane reaches each strict sign side. Hence neither one-sided
closed sign carrier can have an interior point on the hyperplane. This is
the geometric side condition used before applying Wilkie 3.12 to the two
one-sided closures in 3.13.

The result concerns `closure (B ∩ P(±ell)) ∩ H`. It does not identify that
trace with `closure (B ∩ H)`, or with the carrier of the current
`integerAffineInter` constructor for arbitrary nonclosed `B`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- Add a real displacement in one visible coordinate. -/
def integerAffineSliceMoveAt {n : ℕ} (j : Fin n)
    (x : RealEuclidean n) (t : ℝ) : RealEuclidean n :=
  fun i ↦ if i = j then x i + t else x i

theorem integerAffineSliceLinearForm_moveAt
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (j : Fin n) (x : RealEuclidean n) (t : ℝ) :
    integerAffineSliceLinearForm coeff constant
        (integerAffineSliceMoveAt j x t) =
      integerAffineSliceLinearForm coeff constant x +
        (coeff j : ℝ) * t := by
  classical
  have hsum :
      (∑ i : Fin n,
        (coeff i : ℝ) * integerAffineSliceMoveAt j x t i) =
        (∑ i : Fin n, (coeff i : ℝ) * x i) +
          (coeff j : ℝ) * t := by
    calc
      _ = ∑ i : Fin n,
          ((coeff i : ℝ) * x i +
            (if i = j then (coeff j : ℝ) * t else 0)) := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hij : i = j
              · subst i
                simp [integerAffineSliceMoveAt, mul_add]
              · simp [integerAffineSliceMoveAt, hij]
      _ = (∑ i : Fin n, (coeff i : ℝ) * x i) +
          ∑ i : Fin n,
            (if i = j then (coeff j : ℝ) * t else 0) := by
              rw [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, (coeff i : ℝ) * x i) +
          (coeff j : ℝ) * t := by
              simp [Fintype.sum_ite_eq]
  simp only [integerAffineSliceLinearForm]
  rw [hsum]
  ring

theorem dist_integerAffineSliceMoveAt_le_abs
    {n : ℕ} (j : Fin n) (x : RealEuclidean n) (t : ℝ) :
    dist x (integerAffineSliceMoveAt j x t) ≤ |t| := by
  apply (dist_pi_le_iff (abs_nonneg t)).mpr
  intro i
  by_cases hij : i = j
  · subst i
    simp [integerAffineSliceMoveAt, Real.dist_eq]
  · simp [integerAffineSliceMoveAt, hij, abs_nonneg]

/-- A displacement divided by a nonzero integer coefficient is no larger
than the original displacement in absolute value. -/
theorem abs_div_integerAffineSliceCoeff_le_abs
    {n : ℕ} (coeff : Fin n → ℤ)
    (j : Fin n) (hj : coeff j ≠ 0) (t : ℝ) :
    |t / (coeff j : ℝ)| ≤ |t| := by
  have hjReal : (coeff j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hcoeff : (1 : ℝ) ≤ |(coeff j : ℝ)| :=
    one_le_abs_real_of_int_ne_zero (coeff j) hj
  have hcoeffPos : 0 < |(coeff j : ℝ)| := abs_pos.mpr hjReal
  rw [abs_div]
  apply (div_le_iff₀ hcoeffPos).mpr
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hcoeff (abs_nonneg t)

/-- Both strict sign sides meet every metric ball centered on a genuine
integer-affine hyperplane. -/
theorem exists_integerAffineSlice_nearby_strictSigns
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0)
    (x : RealEuclidean n)
    (hx : x ∈ integerAffineSliceHyperplane coeff constant)
    {radius : ℝ} (hradius : 0 < radius) :
    (∃ y : RealEuclidean n,
        y ∈ Metric.ball x radius ∧
          integerAffineSliceLinearForm coeff constant y < 0) ∧
      (∃ y : RealEuclidean n,
        y ∈ Metric.ball x radius ∧
          0 < integerAffineSliceLinearForm coeff constant y) := by
  obtain ⟨j, hj⟩ := hnonzero
  have hjReal : (coeff j : ℝ) ≠ 0 := by exact_mod_cast hj
  have hxZero : integerAffineSliceLinearForm coeff constant x = 0 := hx
  let epsilon : ℝ := radius / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  have hepsilonLt : epsilon < radius := by dsimp [epsilon]; linarith
  let negative := integerAffineSliceMoveAt j x
    ((-epsilon) / (coeff j : ℝ))
  let positive := integerAffineSliceMoveAt j x
    (epsilon / (coeff j : ℝ))
  have hnegativeDist : dist x negative ≤ epsilon := by
    calc
      dist x negative ≤ |(-epsilon) / (coeff j : ℝ)| :=
        dist_integerAffineSliceMoveAt_le_abs j x _
      _ ≤ |-epsilon| :=
        abs_div_integerAffineSliceCoeff_le_abs coeff j hj _
      _ = epsilon := by simp [abs_of_pos hepsilon]
  have hpositiveDist : dist x positive ≤ epsilon := by
    calc
      dist x positive ≤ |epsilon / (coeff j : ℝ)| :=
        dist_integerAffineSliceMoveAt_le_abs j x _
      _ ≤ |epsilon| :=
        abs_div_integerAffineSliceCoeff_le_abs coeff j hj _
      _ = epsilon := abs_of_pos hepsilon
  have hnegativeValue :
      integerAffineSliceLinearForm coeff constant negative =
        -epsilon := by
    change integerAffineSliceLinearForm coeff constant
        (integerAffineSliceMoveAt j x ((-epsilon) / (coeff j : ℝ))) =
          -epsilon
    rw [integerAffineSliceLinearForm_moveAt, hxZero, zero_add]
    exact mul_div_cancel₀ _ hjReal
  have hpositiveValue :
      integerAffineSliceLinearForm coeff constant positive =
        epsilon := by
    change integerAffineSliceLinearForm coeff constant
        (integerAffineSliceMoveAt j x (epsilon / (coeff j : ℝ))) =
          epsilon
    rw [integerAffineSliceLinearForm_moveAt, hxZero, zero_add]
    exact mul_div_cancel₀ _ hjReal
  constructor
  · refine ⟨negative, Metric.mem_ball.mpr ?_, ?_⟩
    · calc
        dist negative x = dist x negative := dist_comm _ _
        _ ≤ epsilon := hnegativeDist
        _ < radius := hepsilonLt
    · rw [hnegativeValue]
      linarith
  · refine ⟨positive, Metric.mem_ball.mpr ?_, ?_⟩
    · calc
        dist positive x = dist x positive := dist_comm _ _
        _ ≤ epsilon := hpositiveDist
        _ < radius := hepsilonLt
    · rw [hpositiveValue]
      exact hepsilon

/-- The closure of either strict sign cell has no interior point on a
genuine hyperplane. This is exactly the topological premise exposed by
`oneSidedClosure_frontier_trace_of_avoid`. -/
theorem interior_closure_integerAffineSlicePositiveSide_avoid_hyperplane
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0) :
    interior (closure (integerAffineSlicePositiveSide coeff constant)) ∩
      integerAffineSliceHyperplane coeff constant = ∅ := by
  have hcontinuous :
      Continuous (integerAffineSliceLinearForm coeff constant) := by
    unfold integerAffineSliceLinearForm
    fun_prop
  have hclosedNonnegative :
      IsClosed {x : RealEuclidean n |
        0 ≤ integerAffineSliceLinearForm coeff constant x} := by
    change IsClosed
      ((integerAffineSliceLinearForm coeff constant) ⁻¹'
        (Set.Ici 0 : Set ℝ))
    exact isClosed_Ici.preimage hcontinuous
  have hclosureSubset :
      closure (integerAffineSlicePositiveSide coeff constant) ⊆
        {x : RealEuclidean n |
          0 ≤ integerAffineSliceLinearForm coeff constant x} := by
    have hsubset :
        integerAffineSlicePositiveSide coeff constant ⊆
          {x : RealEuclidean n |
            0 ≤ integerAffineSliceLinearForm coeff constant x} := by
      intro x hx
      change 0 < integerAffineSliceLinearForm coeff constant x at hx
      exact le_of_lt hx
    have h := closure_mono hsubset
    rw [hclosedNonnegative.closure_eq] at h
    exact h
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨radius, hradius, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) x hx.1
  obtain ⟨y, hyBall, hyNegative⟩ :=
    (exists_integerAffineSlice_nearby_strictSigns
      coeff constant hnonzero x hx.2 hradius).1
  have hyNonnegative := hclosureSubset
    (interior_subset (hball hyBall))
  exact (not_lt_of_ge hyNonnegative) hyNegative

theorem interior_closure_integerAffineSliceNegativeSide_avoid_hyperplane
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0) :
    interior (closure (integerAffineSliceNegativeSide coeff constant)) ∩
      integerAffineSliceHyperplane coeff constant = ∅ := by
  have hcontinuous :
      Continuous (integerAffineSliceLinearForm coeff constant) := by
    unfold integerAffineSliceLinearForm
    fun_prop
  have hclosedNonpositive :
      IsClosed {x : RealEuclidean n |
        integerAffineSliceLinearForm coeff constant x ≤ 0} := by
    change IsClosed
      ((integerAffineSliceLinearForm coeff constant) ⁻¹'
        (Set.Iic 0 : Set ℝ))
    exact isClosed_Iic.preimage hcontinuous
  have hclosureSubset :
      closure (integerAffineSliceNegativeSide coeff constant) ⊆
        {x : RealEuclidean n |
          integerAffineSliceLinearForm coeff constant x ≤ 0} := by
    have hsubset :
        integerAffineSliceNegativeSide coeff constant ⊆
          {x : RealEuclidean n |
            integerAffineSliceLinearForm coeff constant x ≤ 0} := by
      intro x hx
      change integerAffineSliceLinearForm coeff constant x < 0 at hx
      exact le_of_lt hx
    have h := closure_mono hsubset
    rw [hclosedNonpositive.closure_eq] at h
    exact h
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨radius, hradius, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) x hx.1
  obtain ⟨y, hyBall, hyPositive⟩ :=
    (exists_integerAffineSlice_nearby_strictSigns
      coeff constant hnonzero x hx.2 hradius).2
  have hyNonpositive := hclosureSubset
    (interior_subset (hball hyBall))
  exact (not_lt_of_ge hyNonpositive) hyPositive

/-- A nonzero-row sign cut has precisely the frontier trace needed by
Wilkie 3.12, independently of the inner carrier `B`. -/
theorem oneSidedIntegerAffineClosure_frontier_traces
    {n : ℕ} (B : Set (RealEuclidean n))
    (coeff : Fin n → ℤ) (constant : ℤ)
    (hnonzero : ∃ j : Fin n, coeff j ≠ 0) :
    (closure (B ∩ integerAffineSlicePositiveSide coeff constant) ∩
        integerAffineSliceHyperplane coeff constant =
      frontier (closure
        (B ∩ integerAffineSlicePositiveSide coeff constant)) ∩
        integerAffineSliceHyperplane coeff constant) ∧
    (closure (B ∩ integerAffineSliceNegativeSide coeff constant) ∩
        integerAffineSliceHyperplane coeff constant =
      frontier (closure
        (B ∩ integerAffineSliceNegativeSide coeff constant)) ∩
        integerAffineSliceHyperplane coeff constant) := by
  constructor
  · exact oneSidedClosure_frontier_trace_of_avoid
      B (integerAffineSliceHyperplane coeff constant)
      (integerAffineSlicePositiveSide coeff constant)
      (interior_closure_integerAffineSlicePositiveSide_avoid_hyperplane
        coeff constant hnonzero)
  · exact oneSidedClosure_frontier_trace_of_avoid
      B (integerAffineSliceHyperplane coeff constant)
      (integerAffineSliceNegativeSide coeff constant)
      (interior_closure_integerAffineSliceNegativeSide_avoid_hyperplane
        coeff constant hnonzero)

end AbelFormalization
