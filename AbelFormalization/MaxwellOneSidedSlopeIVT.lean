import AbelFormalization.MaxwellFirstOrderAnalyticAdapter
import AbelFormalization.MaxwellScalarDiscontinuityEscape

/-!
# One-sided intermediate values for Maxwell difference quotients

This file supplies the analytic part of Figueiredo--Maxwell Lemma 2.3.3.
The first results remove an avoidable mismatch between the relational
difference quotient used by Maxwell and an ordinary scalar representative.
Later results keep the step nonzero while applying the intermediate value
theorem; only afterwards is the zero-step closure taken.

The distinction is essential.  Continuity merely on the punctured step
domain does not control a quotient formed directly at a discontinuity of the
representative (for example `f 0 = 0` and `f t = 1` for `t != 0`).  The
zero-step results below therefore expose the required continuity/direct-step
control rather than silently identifying the punctured graph with its trace.
-/

noncomputable section

open Set Filter Topology
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Ordinary scalar representatives -/

/-- A represented scalar relation gives exactly the ordinary directional
difference-quotient equation.  This is the `RepresentsOn` version of
`realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_functionGraph_iff`.
-/
theorem realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_of_representsOn_iff
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (hrep : MaxwellRelation.RepresentsOn R U (fun x _ ↦ f x))
    (x : RealEuclidean p) (epsilon y : ℝ) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
        (fun _ : Fin 1 ↦ y) ∈
      maxwellDifferenceQuotientRelation U R i ↔
    x ∈ U ∧
      x + epsilon • (Pi.single i 1 : RealEuclidean p) ∈ U ∧
      epsilon ≠ 0 ∧
      epsilon * y =
        f (x + epsilon • (Pi.single i 1 : RealEuclidean p)) - f x := by
  rw [realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff]
  constructor
  · rintro ⟨hx, hxepsilon, hepsilon, z₁, z₂, hz₁, hz₂, heq⟩
    have hz₁' := (hrep x hx (fun _ : Fin 1 ↦ z₁)).mp hz₁
    have hz₂' :=
      (hrep (x + epsilon • (Pi.single i 1 : RealEuclidean p))
        hxepsilon (fun _ : Fin 1 ↦ z₂)).mp hz₂
    have hz₁eq : z₁ = f x := congrFun hz₁' 0
    have hz₂eq :
        z₂ = f (x + epsilon • (Pi.single i 1 : RealEuclidean p)) :=
      congrFun hz₂' 0
    rw [hz₁eq, hz₂eq] at heq
    exact ⟨hx, hxepsilon, hepsilon, heq⟩
  · rintro ⟨hx, hxepsilon, hepsilon, heq⟩
    refine ⟨hx, hxepsilon, hepsilon, f x,
      f (x + epsilon • (Pi.single i 1 : RealEuclidean p)), ?_, ?_, heq⟩
    · exact (hrep x hx (fun _ : Fin 1 ↦ f x)).mpr rfl
    · exact
        (hrep (x + epsilon • (Pi.single i 1 : RealEuclidean p))
          hxepsilon
          (fun _ : Fin 1 ↦
            f (x + epsilon • (Pi.single i 1 : RealEuclidean p)))).mpr rfl

/-- In step-last coordinates the represented relation is the graph of the
ordinary right difference quotient on its nonzero-step domain. -/
theorem realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_of_representsOn_iff
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (hrep : MaxwellRelation.RepresentsOn R U (fun x _ ↦ f x))
    (x : RealEuclidean p) (epsilon y : ℝ) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
        (fun _ : Fin 1 ↦ epsilon) ∈
      maxwellStepLastDifferenceQuotientRelation U R i ↔
    x ∈ U ∧
      x + epsilon • (Pi.single i 1 : RealEuclidean p) ∈ U ∧
      epsilon ≠ 0 ∧
      y = maxwellRightDifferenceQuotient f i x epsilon := by
  rw [mem_maxwellStepLastDifferenceQuotientRelation_append_iff]
  rw [realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_of_representsOn_iff
    i hrep]
  refine and_congr_right (fun _hx ↦ and_congr_right (fun _hxepsilon ↦
    and_congr_right (fun hepsilon ↦ ?_)))
  simp only [maxwellRightDifferenceQuotient]
  constructor
  · intro h
    apply (eq_div_iff hepsilon).2
    simpa [mul_comm] using h
  · intro h
    apply (eq_div_iff hepsilon).1 at h
    simpa [mul_comm] using h

/-! ## The two connected punctured step domains -/

/-- The sign of the actual step after both one-sided domains have been
parametrized by a positive number. -/
inductive MaxwellOneSidedStep where
  | positive
  | negative
deriving DecidableEq

/-- `+1` for a right step and `-1` for a reflected left step. -/
def MaxwellOneSidedStep.sign : MaxwellOneSidedStep → ℝ
  | .positive => 1
  | .negative => -1

@[simp]
theorem MaxwellOneSidedStep.sign_positive :
    MaxwellOneSidedStep.positive.sign = 1 :=
  rfl

@[simp]
theorem MaxwellOneSidedStep.sign_negative :
    MaxwellOneSidedStep.negative.sign = -1 :=
  rfl

theorem MaxwellOneSidedStep.sign_ne_zero (side : MaxwellOneSidedStep) :
    side.sign ≠ 0 := by
  cases side <;> norm_num [MaxwellOneSidedStep.sign]

/-- The ordinary quotient on one side, with a positive parameter `t` on
both sides.  On the negative side the actual Maxwell step is `-t`. -/
def maxwellOneSidedDifferenceQuotient {p : ℕ}
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (side : MaxwellOneSidedStep)
    (z : RealEuclidean p × ℝ) : ℝ :=
  (f (z.1 + (side.sign * z.2) •
      (Pi.single i 1 : RealEuclidean p)) - f z.1) /
    (side.sign * z.2)

/-- The connected punctured domain on which a one-sided quotient is an
ordinary continuous function. -/
def maxwellOneSidedStepDomain {p : ℕ}
    (U : Set (RealEuclidean p)) (i : Fin p)
    (side : MaxwellOneSidedStep) : Set (RealEuclidean p × ℝ) :=
  {z | z.1 ∈ U ∧
    z.1 + (side.sign * z.2) •
      (Pi.single i 1 : RealEuclidean p) ∈ U ∧
    0 < z.2}

/-- Continuity of the chosen scalar representative makes its one-sided
difference quotient continuous before the zero-step trace is taken. -/
theorem continuousOn_maxwellOneSidedDifferenceQuotient
    {p : ℕ} {U : Set (RealEuclidean p)} {f : RealEuclidean p → ℝ}
    (i : Fin p) (side : MaxwellOneSidedStep)
    (hf : ContinuousOn f U) :
    ContinuousOn (maxwellOneSidedDifferenceQuotient f i side)
      (maxwellOneSidedStepDomain U i side) := by
  have hbase : Continuous (fun z : RealEuclidean p × ℝ ↦ z.1) :=
    continuous_fst
  have hsignedStep : Continuous
      (fun z : RealEuclidean p × ℝ ↦ side.sign * z.2) :=
    continuous_const.mul continuous_snd
  have hshift : Continuous
      (fun z : RealEuclidean p × ℝ ↦
        z.1 + (side.sign * z.2) •
          (Pi.single i 1 : RealEuclidean p)) :=
    hbase.add (hsignedStep.smul continuous_const)
  have hfbase : ContinuousOn (fun z : RealEuclidean p × ℝ ↦ f z.1)
      (maxwellOneSidedStepDomain U i side) :=
    hf.comp hbase.continuousOn (fun z hz ↦ hz.1)
  have hfshift : ContinuousOn
      (fun z : RealEuclidean p × ℝ ↦
        f (z.1 + (side.sign * z.2) •
          (Pi.single i 1 : RealEuclidean p)))
      (maxwellOneSidedStepDomain U i side) :=
    hf.comp hshift.continuousOn (fun z hz ↦ hz.2.1)
  exact (hfshift.sub hfbase).div hsignedStep.continuousOn
    (fun z hz ↦ mul_ne_zero side.sign_ne_zero (ne_of_gt hz.2.2))

/-- The step-last Maxwell relation is the graph of the corresponding
one-sided quotient over the positive parameter domain. -/
theorem realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_oneSided_of_representsOn_iff
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (hrep : MaxwellRelation.RepresentsOn R U (fun x _ ↦ f x))
    (side : MaxwellOneSidedStep) (x : RealEuclidean p) (t y : ℝ) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
        (fun _ : Fin 1 ↦ side.sign * t) ∈
      maxwellStepLastDifferenceQuotientRelation U R i ∧ 0 < t ↔
    (x, t) ∈ maxwellOneSidedStepDomain U i side ∧
      y = maxwellOneSidedDifferenceQuotient f i side (x, t) := by
  rw [realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_of_representsOn_iff
    i hrep]
  simp only [maxwellOneSidedStepDomain, Set.mem_setOf_eq,
    maxwellOneSidedDifferenceQuotient, maxwellRightDifferenceQuotient]
  constructor
  · rintro ⟨⟨hx, hshift, _hstep, hy⟩, ht⟩
    exact ⟨⟨hx, hshift, ht⟩, hy⟩
  · rintro ⟨⟨hx, hshift, ht⟩, hy⟩
    exact ⟨⟨hx, hshift,
      mul_ne_zero side.sign_ne_zero (ne_of_gt ht), hy⟩, ht⟩

/-! ## Sequential form of the actual zero traces -/

/-- The sign condition on the actual (unreflected) Maxwell step. -/
def MaxwellOneSidedStep.Accepts
    (side : MaxwellOneSidedStep) (epsilon : ℝ) : Prop :=
  match side with
  | .positive => 0 < epsilon
  | .negative => epsilon < 0

@[simp]
theorem MaxwellOneSidedStep.accepts_positive_iff (epsilon : ℝ) :
    MaxwellOneSidedStep.positive.Accepts epsilon ↔ 0 < epsilon :=
  Iff.rfl

@[simp]
theorem MaxwellOneSidedStep.accepts_negative_iff (epsilon : ℝ) :
    MaxwellOneSidedStep.negative.Accepts epsilon ↔ epsilon < 0 :=
  Iff.rfl

/-- A sequence in the nonzero-step quotient graph approaching a prescribed
finite zero-step value from one chosen side. -/
structure MaxwellOneSidedSlopeApproach
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (x : RealEuclidean p) (y : ℝ) where
  point : ℕ → RealEuclidean ((p + 1) + 1)
  point_mem : ∀ n,
    point n ∈ maxwellStepLastDifferenceQuotientRelation U R i
  step_sign : ∀ n,
    side.Accepts (point n (Fin.last (p + 1)))
  tendsto_zeroStep : Tendsto point atTop
    (nhds (realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
      (fun _ : Fin 1 ↦ 0)))

/-- Uniform notation for the positive and reflected-negative finite traces. -/
def maxwellOneSidedStepZeroTrace
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : MaxwellOneSidedStep → MaxwellRelation p 1
  | .positive => maxwellPositiveStepZeroTrace U R i
  | .negative => maxwellNegativeStepZeroTrace U R i

/-- Membership in either finite one-sided trace is exactly a nonzero-step
approach sequence from that side.  This lemma prevents later IVT arguments
from replacing the closure trace by a pointwise `epsilon = 0` quotient. -/
theorem mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (x : RealEuclidean p) (y : ℝ) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellOneSidedStepZeroTrace U R i side ↔
      Nonempty (MaxwellOneSidedSlopeApproach U R i side x y) := by
  cases side with
  | positive =>
      change charbonnelAppendLastCoordinate
          (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) 0 ∈
          closure (charbonnelPositiveLastPart
            (maxwellStepLastDifferenceQuotientRelation U R i)) ↔ _
      constructor
      · intro h
        obtain ⟨w, hw, hwlim⟩ := mem_closure_iff_seq_limit.mp h
        refine ⟨
          { point := w
            point_mem := fun n ↦ (hw n).1
            step_sign := fun n ↦ ?_
            tendsto_zeroStep := ?_ }⟩
        · exact (hw n).2
        · simpa only [charbonnelAppendLastCoordinate] using hwlim
      · rintro ⟨h⟩
        apply mem_closure_iff_seq_limit.mpr
        refine ⟨h.point, ?_, ?_⟩
        · intro n
          exact ⟨h.point_mem n, h.step_sign n⟩
        · simpa only [charbonnelAppendLastCoordinate] using
            h.tendsto_zeroStep
  | negative =>
      rw [maxwellOneSidedStepZeroTrace, maxwellNegativeStepZeroTrace,
        maxwellNegativeZeroTrace_eq_zeroSection_closure_negativeLastPart]
      change charbonnelAppendLastCoordinate
          (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) 0 ∈
          closure (maxwellNegativeLastPart
            (maxwellStepLastDifferenceQuotientRelation U R i)) ↔ _
      constructor
      · intro h
        obtain ⟨w, hw, hwlim⟩ := mem_closure_iff_seq_limit.mp h
        refine ⟨
          { point := w
            point_mem := fun n ↦ (hw n).1
            step_sign := fun n ↦ ?_
            tendsto_zeroStep := ?_ }⟩
        · exact (hw n).2
        · simpa only [charbonnelAppendLastCoordinate] using hwlim
      · rintro ⟨h⟩
        apply mem_closure_iff_seq_limit.mpr
        refine ⟨h.point, ?_, ?_⟩
        · intro n
          exact ⟨h.point_mem n, h.step_sign n⟩
        · simpa only [charbonnelAppendLastCoordinate] using
            h.tendsto_zeroStep

/-! ## Reciprocation before taking the zero-step trace -/

/-- Coordinate movement to step-last form is independent of the relation
being moved.  The existing quotient-specific lemma is a specialization of
this identity. -/
theorem mem_maxwellMoveStepToLastLinearEquiv_image_append_iff
    {p : ℕ} (G : MaxwellRelation (p + 1) 1)
    (x : RealEuclidean p) (y epsilon : RealEuclidean 1) :
    realEuclideanAppend (realEuclideanAppend x y) epsilon ∈
        maxwellMoveStepToLastLinearEquiv p '' G ↔
      realEuclideanAppend (realEuclideanAppend x epsilon) y ∈ G := by
  let E := maxwellMoveStepToLastLinearEquiv p
  constructor
  · rintro ⟨w, hw, hwEq⟩
    have hwCanonical :
        w = realEuclideanAppend (realEuclideanAppend x epsilon) y := by
      apply E.injective
      exact hwEq.trans
        (maxwellMoveStepToLastLinearEquiv_apply_append x epsilon y).symm
    rwa [hwCanonical] at hw
  · intro hw
    exact ⟨realEuclideanAppend (realEuclideanAppend x epsilon) y, hw,
      maxwellMoveStepToLastLinearEquiv_apply_append x epsilon y⟩

/-- A point of the positive reciprocal step-last relation is precisely a
point of the original step-last quotient together with `slope * reciprocal
= 1` and a positive reciprocal. -/
theorem realEuclideanAppend_append_mem_maxwellPositiveReciprocalStepLastRelation_iff
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (x : RealEuclidean p) (epsilon r : ℝ) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ r))
        (fun _ : Fin 1 ↦ epsilon) ∈
      maxwellPositiveReciprocalStepLastRelation U R i ↔
    ∃ y : ℝ,
      realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
          (fun _ : Fin 1 ↦ epsilon) ∈
        maxwellStepLastDifferenceQuotientRelation U R i ∧
      y * r = 1 ∧ 0 < r := by
  rw [maxwellPositiveReciprocalStepLastRelation,
    mem_maxwellMoveStepToLastLinearEquiv_image_append_iff,
    realEuclideanAppend_scalar_mem_maxwellPositiveReciprocalRelation_iff]
  constructor
  · rintro ⟨y, hy, hyr, hr⟩
    refine ⟨y, ?_, hyr, hr⟩
    exact (mem_maxwellStepLastDifferenceQuotientRelation_append_iff
      U R i x (fun _ : Fin 1 ↦ y)
        (fun _ : Fin 1 ↦ epsilon)).mpr hy
  · rintro ⟨y, hy, hyr, hr⟩
    refine ⟨y, ?_, hyr, hr⟩
    exact (mem_maxwellStepLastDifferenceQuotientRelation_append_iff
      U R i x (fun _ : Fin 1 ↦ y)
        (fun _ : Fin 1 ↦ epsilon)).mp hy

/-- Negative reciprocal analogue of
`realEuclideanAppend_append_mem_maxwellPositiveReciprocalStepLastRelation_iff`.
-/
theorem realEuclideanAppend_append_mem_maxwellNegativeReciprocalStepLastRelation_iff
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (x : RealEuclidean p) (epsilon r : ℝ) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ r))
        (fun _ : Fin 1 ↦ epsilon) ∈
      maxwellNegativeReciprocalStepLastRelation U R i ↔
    ∃ y : ℝ,
      realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
          (fun _ : Fin 1 ↦ epsilon) ∈
        maxwellStepLastDifferenceQuotientRelation U R i ∧
      y * r = 1 ∧ r < 0 := by
  rw [maxwellNegativeReciprocalStepLastRelation,
    mem_maxwellMoveStepToLastLinearEquiv_image_append_iff,
    realEuclideanAppend_scalar_mem_maxwellNegativeReciprocalRelation_iff]
  constructor
  · rintro ⟨y, hy, hyr, hr⟩
    refine ⟨y, ?_, hyr, hr⟩
    exact (mem_maxwellStepLastDifferenceQuotientRelation_append_iff
      U R i x (fun _ : Fin 1 ↦ y)
        (fun _ : Fin 1 ↦ epsilon)).mpr hy
  · rintro ⟨y, hy, hyr, hr⟩
    refine ⟨y, ?_, hyr, hr⟩
    exact (mem_maxwellStepLastDifferenceQuotientRelation_append_iff
      U R i x (fun _ : Fin 1 ↦ y)
        (fun _ : Fin 1 ↦ epsilon)).mp hy

/-! ## Convex local cores and the ordinary IVT -/

/-- Read the translated endpoint of a signed one-sided step.  It is linear
in `(base, positive step parameter)`, which makes the local core convex. -/
def maxwellOneSidedShiftLinearMap {p : ℕ} (i : Fin p)
    (side : MaxwellOneSidedStep) :
    (RealEuclidean p × ℝ) →ₗ[ℝ] RealEuclidean p where
  toFun z := z.1 + (side.sign * z.2) •
    (Pi.single i 1 : RealEuclidean p)
  map_add' z w := by
    ext j
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.smul_apply,
      add_smul]
    ring
  map_smul' c z := by
    ext j
    change c * z.1 j + (side.sign * (c * z.2)) *
        (Pi.single i 1 : RealEuclidean p) j =
      c * (z.1 j + (side.sign * z.2) *
        (Pi.single i 1 : RealEuclidean p) j)
    ring

@[simp]
theorem maxwellOneSidedShiftLinearMap_apply
    {p : ℕ} (i : Fin p) (side : MaxwellOneSidedStep)
    (z : RealEuclidean p × ℝ) :
    maxwellOneSidedShiftLinearMap i side z =
      z.1 + (side.sign * z.2) •
        (Pi.single i 1 : RealEuclidean p) :=
  rfl

/-- A convex punctured half-neighborhood of `(x,0)`.  Both endpoints of
the secant are required to remain in the same ball. -/
def maxwellOneSidedStepCore {p : ℕ}
    (x : RealEuclidean p) (rho : ℝ) (i : Fin p)
    (side : MaxwellOneSidedStep) : Set (RealEuclidean p × ℝ) :=
  (LinearMap.fst ℝ (RealEuclidean p) ℝ) ⁻¹' Metric.ball x rho ∩
    (maxwellOneSidedShiftLinearMap i side) ⁻¹' Metric.ball x rho ∩
      (LinearMap.snd ℝ (RealEuclidean p) ℝ) ⁻¹' Set.Ioi 0

theorem convex_maxwellOneSidedStepCore
    {p : ℕ} (x : RealEuclidean p) (rho : ℝ) (i : Fin p)
    (side : MaxwellOneSidedStep) :
    Convex ℝ (maxwellOneSidedStepCore x rho i side) := by
  exact (((convex_ball x rho).linear_preimage
      (LinearMap.fst ℝ (RealEuclidean p) ℝ)).inter
    ((convex_ball x rho).linear_preimage
      (maxwellOneSidedShiftLinearMap i side))).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage
      (LinearMap.snd ℝ (RealEuclidean p) ℝ))

theorem maxwellOneSidedStepCore_subset_domain
    {p : ℕ} {U : Set (RealEuclidean p)} {x : RealEuclidean p}
    {rho : ℝ} {i : Fin p} {side : MaxwellOneSidedStep}
    (hball : Metric.ball x rho ⊆ U) :
    maxwellOneSidedStepCore x rho i side ⊆
      maxwellOneSidedStepDomain U i side := by
  intro z hz
  exact ⟨hball hz.1.1, hball hz.1.2,
    hz.2⟩

/-- The quotient is continuous on every convex local core contained in the
open representative domain. -/
theorem continuousOn_maxwellOneSidedDifferenceQuotient_stepCore
    {p : ℕ} {U : Set (RealEuclidean p)} {f : RealEuclidean p → ℝ}
    {x : RealEuclidean p} {rho : ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hf : ContinuousOn f U) (hball : Metric.ball x rho ⊆ U) :
    ContinuousOn (maxwellOneSidedDifferenceQuotient f i side)
      (maxwellOneSidedStepCore x rho i side) :=
  (continuousOn_maxwellOneSidedDifferenceQuotient i side hf).mono
    (maxwellOneSidedStepCore_subset_domain hball)

/-- IVT along a segment in an arbitrary convex domain.  This is the finite
stage used before passing to a zero-step cluster. -/
theorem exists_lineMap_eq_of_continuousOn_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set E} {q : E → ℝ}
    (hD : Convex ℝ D) (hq : ContinuousOn q D)
    {u v : E} (hu : u ∈ D) (hv : v ∈ D)
    {y : ℝ} (hy : y ∈ Set.Icc (q u) (q v)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      q (u + t • (v - u)) = y := by
  let path : ℝ → E := fun t ↦ u + t • (v - u)
  have hpath : Continuous path :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmaps : MapsTo path (Set.Icc (0 : ℝ) 1) D := by
    intro t ht
    exact hD.add_smul_sub_mem hu hv ht
  have hqpath : ContinuousOn (fun t ↦ q (path t))
      (Set.Icc (0 : ℝ) 1) :=
    hq.comp hpath.continuousOn hmaps
  have hy' : y ∈ Set.Icc ((fun t ↦ q (path t)) 0)
      ((fun t ↦ q (path t)) 1) := by
    simpa [path] using hy
  obtain ⟨t, ht, hty⟩ :=
    (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hqpath) hy'
  exact ⟨t, ht, hty⟩

/-! ## Coordinates of a step-last approach -/

def maxwellStepLastBase {p : ℕ}
    (w : RealEuclidean ((p + 1) + 1)) : RealEuclidean p :=
  realEuclideanTakeLeft (realEuclideanTakeLeft w)

def maxwellStepLastValue {p : ℕ}
    (w : RealEuclidean ((p + 1) + 1)) : ℝ :=
  realEuclideanTakeRight (realEuclideanTakeLeft w) 0

def maxwellStepLastStep {p : ℕ}
    (w : RealEuclidean ((p + 1) + 1)) : ℝ :=
  realEuclideanTakeRight w 0

@[simp]
theorem maxwellStepLastBase_append {p : ℕ}
    (x : RealEuclidean p) (y epsilon : ℝ) :
    maxwellStepLastBase
      (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
        (fun _ : Fin 1 ↦ epsilon)) = x := by
  simp [maxwellStepLastBase]

@[simp]
theorem maxwellStepLastValue_append {p : ℕ}
    (x : RealEuclidean p) (y epsilon : ℝ) :
    maxwellStepLastValue
      (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
        (fun _ : Fin 1 ↦ epsilon)) = y := by
  simp [maxwellStepLastValue]

@[simp]
theorem maxwellStepLastStep_append {p : ℕ}
    (x : RealEuclidean p) (y epsilon : ℝ) :
    maxwellStepLastStep
      (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
        (fun _ : Fin 1 ↦ epsilon)) = epsilon := by
  simp [maxwellStepLastStep]

theorem realEuclideanAppend_stepLastCoordinates {p : ℕ}
    (w : RealEuclidean ((p + 1) + 1)) :
    realEuclideanAppend
        (realEuclideanAppend (maxwellStepLastBase w)
          (fun _ : Fin 1 ↦ maxwellStepLastValue w))
        (fun _ : Fin 1 ↦ maxwellStepLastStep w) = w := by
  have hvalue : (fun _ : Fin 1 ↦ maxwellStepLastValue w) =
      realEuclideanTakeRight (realEuclideanTakeLeft w) := by
    funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    rfl
  have hstep : (fun _ : Fin 1 ↦ maxwellStepLastStep w) =
      realEuclideanTakeRight w := by
    funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    rfl
  rw [maxwellStepLastBase, hvalue,
    realEuclideanAppend_takeLeft_takeRight, hstep,
    realEuclideanAppend_takeLeft_takeRight]

theorem MaxwellOneSidedStep.sign_mul_self
    (side : MaxwellOneSidedStep) : side.sign * side.sign = 1 := by
  cases side <;> norm_num

theorem MaxwellOneSidedStep.sign_mul_step_pos_iff
    (side : MaxwellOneSidedStep) (epsilon : ℝ) :
    0 < side.sign * epsilon ↔ side.Accepts epsilon := by
  cases side <;> simp [MaxwellOneSidedStep.sign,
    MaxwellOneSidedStep.Accepts]

/-- Normalize a signed approach point to `(base, positive step parameter)`. -/
def maxwellOneSidedApproachSource {p : ℕ}
    (side : MaxwellOneSidedStep)
    (w : RealEuclidean ((p + 1) + 1)) : RealEuclidean p × ℝ :=
  (maxwellStepLastBase w, side.sign * maxwellStepLastStep w)

theorem MaxwellOneSidedSlopeApproach.source_mem_domain_of_representsOn
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    {side : MaxwellOneSidedStep} {x : RealEuclidean p} {y : ℝ}
    (h : MaxwellOneSidedSlopeApproach U R i side x y)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    (n : ℕ) :
    maxwellOneSidedApproachSource side (h.point n) ∈
        maxwellOneSidedStepDomain U i side ∧
      maxwellStepLastValue (h.point n) =
        maxwellOneSidedDifferenceQuotient f i side
          (maxwellOneSidedApproachSource side (h.point n)) := by
  let w := h.point n
  let a := maxwellStepLastBase w
  let value := maxwellStepLastValue w
  let epsilon := maxwellStepLastStep w
  have hw : realEuclideanAppend
        (realEuclideanAppend a (fun _ : Fin 1 ↦ value))
        (fun _ : Fin 1 ↦ epsilon) ∈
      maxwellStepLastDifferenceQuotientRelation U R i := by
    rw [realEuclideanAppend_stepLastCoordinates]
    exact h.point_mem n
  have hgraph :=
    (realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_of_representsOn_iff
      i hrep a epsilon value).mp hw
  have ht : 0 < side.sign * epsilon :=
    (side.sign_mul_step_pos_iff epsilon).mpr (h.step_sign n)
  have hactual : side.sign * (side.sign * epsilon) = epsilon := by
    calc
      side.sign * (side.sign * epsilon) =
          (side.sign * side.sign) * epsilon := by ring
      _ = epsilon := by rw [side.sign_mul_self, one_mul]
  refine ⟨⟨hgraph.1, ?_, ht⟩, ?_⟩
  · change a + (side.sign * (side.sign * epsilon)) •
        (Pi.single i 1 : RealEuclidean p) ∈ U
    rw [← mul_assoc, side.sign_mul_self, one_mul]
    exact hgraph.2.1
  · change value =
      (f (a + (side.sign * (side.sign * epsilon)) •
        (Pi.single i 1 : RealEuclidean p)) - f a) /
          (side.sign * (side.sign * epsilon))
    rw [← mul_assoc, side.sign_mul_self, one_mul]
    simpa only [maxwellRightDifferenceQuotient] using hgraph.2.2.2

theorem continuous_maxwellStepLastBase {p : ℕ} :
    Continuous (maxwellStepLastBase (p := p)) := by
  exact (realEuclideanTakeLeftContinuousLinearMap p 1).continuous.comp
    (realEuclideanTakeLeftContinuousLinearMap (p + 1) 1).continuous

theorem continuous_maxwellStepLastValue {p : ℕ} :
    Continuous (maxwellStepLastValue (p := p)) := by
  let right : RealEuclidean (p + 1) →L[ℝ] RealEuclidean 1 :=
    (realEuclideanTakeRightLinearMap p 1).toContinuousLinearMap
  have hright : Continuous
      (fun w : RealEuclidean ((p + 1) + 1) ↦
        right (realEuclideanTakeLeft w)) :=
    right.continuous.comp
      (realEuclideanTakeLeftContinuousLinearMap (p + 1) 1).continuous
  exact (continuous_apply 0).comp hright

theorem continuous_maxwellStepLastStep {p : ℕ} :
    Continuous (maxwellStepLastStep (p := p)) := by
  let right : RealEuclidean ((p + 1) + 1) →L[ℝ] RealEuclidean 1 :=
    (realEuclideanTakeRightLinearMap (p + 1) 1).toContinuousLinearMap
  exact (continuous_apply 0).comp right.continuous

theorem MaxwellOneSidedSlopeApproach.base_tendsto
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} {side : MaxwellOneSidedStep}
    {x : RealEuclidean p} {y : ℝ}
    (h : MaxwellOneSidedSlopeApproach U R i side x y) :
    Tendsto (fun n ↦ maxwellStepLastBase (h.point n)) atTop (nhds x) := by
  have ht := (continuous_maxwellStepLastBase.tendsto
      (realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
      (fun _ : Fin 1 ↦ 0))).comp h.tendsto_zeroStep
  change Tendsto (fun n ↦ maxwellStepLastBase (h.point n)) atTop
    (nhds (maxwellStepLastBase
      (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
        (fun _ : Fin 1 ↦ 0)))) at ht
  simpa only [maxwellStepLastBase_append] using ht

theorem MaxwellOneSidedSlopeApproach.value_tendsto
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} {side : MaxwellOneSidedStep}
    {x : RealEuclidean p} {y : ℝ}
    (h : MaxwellOneSidedSlopeApproach U R i side x y) :
    Tendsto (fun n ↦ maxwellStepLastValue (h.point n)) atTop (nhds y) := by
  have ht := (continuous_maxwellStepLastValue.tendsto
      (realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
      (fun _ : Fin 1 ↦ 0))).comp h.tendsto_zeroStep
  change Tendsto (fun n ↦ maxwellStepLastValue (h.point n)) atTop
    (nhds (maxwellStepLastValue
      (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
        (fun _ : Fin 1 ↦ 0)))) at ht
  simpa only [maxwellStepLastValue_append] using ht

theorem MaxwellOneSidedSlopeApproach.step_tendsto
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} {side : MaxwellOneSidedStep}
    {x : RealEuclidean p} {y : ℝ}
    (h : MaxwellOneSidedSlopeApproach U R i side x y) :
    Tendsto (fun n ↦ maxwellStepLastStep (h.point n)) atTop (nhds 0) := by
  have ht := (continuous_maxwellStepLastStep.tendsto
      (realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
      (fun _ : Fin 1 ↦ 0))).comp h.tendsto_zeroStep
  change Tendsto (fun n ↦ maxwellStepLastStep (h.point n)) atTop
    (nhds (maxwellStepLastStep
      (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
        (fun _ : Fin 1 ↦ 0)))) at ht
  simpa only [maxwellStepLastStep_append] using ht

theorem MaxwellOneSidedSlopeApproach.source_tendsto
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} {side : MaxwellOneSidedStep}
    {x : RealEuclidean p} {y : ℝ}
    (h : MaxwellOneSidedSlopeApproach U R i side x y) :
    Tendsto (fun n ↦ maxwellOneSidedApproachSource side (h.point n))
      atTop (nhds (x, 0)) := by
  have hsigned : Tendsto
      (fun n ↦ side.sign * maxwellStepLastStep (h.point n))
      atTop (nhds (side.sign * 0)) :=
    tendsto_const_nhds.mul h.step_tendsto
  simpa only [maxwellOneSidedApproachSource, nhds_prod_eq, mul_zero] using
    h.base_tendsto.prodMk hsigned

theorem MaxwellOneSidedSlopeApproach.eventually_source_mem_stepCore
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} {side : MaxwellOneSidedStep}
    {x : RealEuclidean p} {y rho : ℝ}
    (h : MaxwellOneSidedSlopeApproach U R i side x y)
    (hrho : 0 < rho) :
    ∀ᶠ n in atTop,
      maxwellOneSidedApproachSource side (h.point n) ∈
        maxwellOneSidedStepCore x rho i side := by
  let source : ℕ → RealEuclidean p × ℝ :=
    fun n ↦ maxwellOneSidedApproachSource side (h.point n)
  have hbase : Tendsto (fun n ↦ (source n).1) atTop (nhds x) :=
    continuous_fst.tendsto (x, 0) |>.comp h.source_tendsto
  have hshift : Tendsto
      (fun n ↦ maxwellOneSidedShiftLinearMap i side (source n))
      atTop (nhds x) := by
    have ht :=
      ((maxwellOneSidedShiftLinearMap i side).toContinuousLinearMap.continuous
        |>.tendsto (x, 0)).comp h.source_tendsto
    change Tendsto
      (fun n ↦ maxwellOneSidedShiftLinearMap i side (source n)) atTop
      (nhds (maxwellOneSidedShiftLinearMap i side (x, 0))) at ht
    simpa only [maxwellOneSidedShiftLinearMap_apply, mul_zero, zero_smul,
      add_zero] using ht
  have hbaseEventually : ∀ᶠ n in atTop, (source n).1 ∈ Metric.ball x rho :=
    hbase.eventually (Metric.ball_mem_nhds x hrho)
  have hshiftEventually : ∀ᶠ n in atTop,
      maxwellOneSidedShiftLinearMap i side (source n) ∈
        Metric.ball x rho :=
    hshift.eventually (Metric.ball_mem_nhds x hrho)
  filter_upwards [hbaseEventually, hshiftEventually] with n hnbase hnshift
  refine ⟨⟨hnbase, hnshift⟩, ?_⟩
  exact (side.sign_mul_step_pos_iff (maxwellStepLastStep (h.point n))).mpr
    (h.step_sign n)

/-- A varying point on the segment between two convergent sequences has the
same limit when every interpolation parameter lies in `[0,1]`. -/
theorem tendsto_variable_lineMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : ℕ → E} {z : E} {theta : ℕ → ℝ}
    (hu : Tendsto u atTop (nhds z))
    (hv : Tendsto v atTop (nhds z))
    (htheta : ∀ n, theta n ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun n ↦ u n + theta n • (v n - u n))
      atTop (nhds z) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have huEventually : ∀ᶠ n in atTop, u n ∈ Metric.ball z epsilon :=
    hu.eventually (Metric.ball_mem_nhds z hepsilon)
  have hvEventually : ∀ᶠ n in atTop, v n ∈ Metric.ball z epsilon :=
    hv.eventually (Metric.ball_mem_nhds z hepsilon)
  filter_upwards [huEventually, hvEventually] with n hun hvn
  exact (convex_ball z epsilon).add_smul_sub_mem hun hvn (htheta n)

theorem tendsto_stepLastPoint_of_source_tendsto
    {p : ℕ} {source : ℕ → RealEuclidean p × ℝ}
    {x : RealEuclidean p} (side : MaxwellOneSidedStep) (y : ℝ)
    (hsource : Tendsto source atTop (nhds (x, 0))) :
    Tendsto
      (fun n ↦
        realEuclideanAppend
          (realEuclideanAppend (source n).1 (fun _ : Fin 1 ↦ y))
          (fun _ : Fin 1 ↦ side.sign * (source n).2))
      atTop
      (nhds (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
        (fun _ : Fin 1 ↦ 0))) := by
  have hbase : Tendsto (fun n ↦ (source n).1) atTop (nhds x) :=
    continuous_fst.tendsto (x, 0) |>.comp hsource
  have hstep : Tendsto (fun n ↦ (source n).2) atTop (nhds 0) :=
    continuous_snd.tendsto (x, 0) |>.comp hsource
  have hsignedStep : Tendsto (fun n ↦ side.sign * (source n).2)
      atTop (nhds 0) := by
    convert tendsto_const_nhds.mul hstep using 1 <;> simp
  have hsignedStepVector : Tendsto
      (fun n ↦ fun _ : Fin 1 ↦ side.sign * (source n).2)
      atTop (nhds (fun _ : Fin 1 ↦ 0)) := by
    rw [tendsto_pi_nhds]
    intro j
    simpa using hsignedStep
  exact tendsto_realEuclideanAppend
    (tendsto_realEuclideanAppend hbase tendsto_const_nhds)
    hsignedStepVector

/-! ## Finite interval filling at an interior base point -/

/-- Two finite one-sided cluster values over an interior point force every
intermediate finite value.  The proof applies the ordinary IVT on shrinking
convex half-balls before taking the zero-step closure. -/
theorem maxwellOneSidedStepZeroTrace_interval_pointwise_of_continuousOn
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ U)
    {a b : ℝ} (hab : a < b)
    (ha : realEuclideanAppend x (fun _ : Fin 1 ↦ a) ∈
      maxwellOneSidedStepZeroTrace U R i side)
    (hb : realEuclideanAppend x (fun _ : Fin 1 ↦ b) ∈
      maxwellOneSidedStepZeroTrace U R i side) :
    Set.Icc a b ⊆
      {y : ℝ | realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellOneSidedStepZeroTrace U R i side} := by
  intro y hy
  rcases eq_or_lt_of_le hy.1 with hay | hay
  · subst y
    exact ha
  rcases eq_or_lt_of_le hy.2 with hyb | hyb
  · subst b
    exact hb
  obtain ⟨hA⟩ :=
    (mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
      U R i side x a).mp ha
  obtain ⟨hB⟩ :=
    (mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
      U R i side x b).mp hb
  obtain ⟨rho, hrho, hball⟩ := Metric.isOpen_iff.mp hUopen x hx
  have hcoreA := hA.eventually_source_mem_stepCore hrho
  have hcoreB := hB.eventually_source_mem_stepCore hrho
  have hvalueA : ∀ᶠ n in atTop,
      maxwellStepLastValue (hA.point n) < y :=
    hA.value_tendsto.eventually_lt_const hay
  have hvalueB : ∀ᶠ n in atTop,
      y < maxwellStepLastValue (hB.point n) :=
    hB.value_tendsto.eventually_const_lt hyb
  have hEventually : ∀ᶠ n in atTop,
      maxwellOneSidedApproachSource side (hA.point n) ∈
          maxwellOneSidedStepCore x rho i side ∧
      maxwellOneSidedApproachSource side (hB.point n) ∈
          maxwellOneSidedStepCore x rho i side ∧
      maxwellStepLastValue (hA.point n) < y ∧
      y < maxwellStepLastValue (hB.point n) := by
    filter_upwards [hcoreA, hcoreB, hvalueA, hvalueB] with n hAn hBn hayn hybn
    exact ⟨hAn, hBn, hayn, hybn⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventually
  let sourceA : ℕ → RealEuclidean p × ℝ := fun n ↦
    maxwellOneSidedApproachSource side (hA.point (n + N))
  let sourceB : ℕ → RealEuclidean p × ℝ := fun n ↦
    maxwellOneSidedApproachSource side (hB.point (n + N))
  have htail (n : ℕ) := hN (n + N) (by omega)
  have hsourceAcore (n : ℕ) :
      sourceA n ∈ maxwellOneSidedStepCore x rho i side :=
    (htail n).1
  have hsourceBcore (n : ℕ) :
      sourceB n ∈ maxwellOneSidedStepCore x rho i side :=
    (htail n).2.1
  have hsourceAValue (n : ℕ) :
      maxwellOneSidedDifferenceQuotient f i side (sourceA n) =
        maxwellStepLastValue (hA.point (n + N)) := by
    exact (hA.source_mem_domain_of_representsOn hrep (n + N)).2.symm
  have hsourceBValue (n : ℕ) :
      maxwellOneSidedDifferenceQuotient f i side (sourceB n) =
        maxwellStepLastValue (hB.point (n + N)) := by
    exact (hB.source_mem_domain_of_representsOn hrep (n + N)).2.symm
  have hbetween (n : ℕ) : y ∈ Set.Icc
      (maxwellOneSidedDifferenceQuotient f i side (sourceA n))
      (maxwellOneSidedDifferenceQuotient f i side (sourceB n)) := by
    rw [hsourceAValue n, hsourceBValue n]
    exact ⟨le_of_lt (htail n).2.2.1, le_of_lt (htail n).2.2.2⟩
  have hcontinuous :=
    continuousOn_maxwellOneSidedDifferenceQuotient_stepCore
      i side hf hball
  have hexists (n : ℕ) : ∃ t ∈ Set.Icc (0 : ℝ) 1,
      maxwellOneSidedDifferenceQuotient f i side
        (sourceA n + t • (sourceB n - sourceA n)) = y :=
    exists_lineMap_eq_of_continuousOn_convex
      (convex_maxwellOneSidedStepCore x rho i side) hcontinuous
      (hsourceAcore n) (hsourceBcore n) (hbetween n)
  choose theta htheta hthetaValue using hexists
  let sourceY : ℕ → RealEuclidean p × ℝ := fun n ↦
    sourceA n + theta n • (sourceB n - sourceA n)
  have hsourceYcore (n : ℕ) :
      sourceY n ∈ maxwellOneSidedStepCore x rho i side :=
    (convex_maxwellOneSidedStepCore x rho i side).add_smul_sub_mem
      (hsourceAcore n) (hsourceBcore n) (htheta n)
  have hsourceYValue (n : ℕ) :
      y = maxwellOneSidedDifferenceQuotient f i side (sourceY n) :=
    (hthetaValue n).symm
  have hsourceYGraph (n : ℕ) :
      realEuclideanAppend
          (realEuclideanAppend (sourceY n).1 (fun _ : Fin 1 ↦ y))
          (fun _ : Fin 1 ↦ side.sign * (sourceY n).2) ∈
          maxwellStepLastDifferenceQuotientRelation U R i ∧
        0 < (sourceY n).2 := by
    apply
      (realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_oneSided_of_representsOn_iff
        i hrep side (sourceY n).1 (sourceY n).2 y).mpr
    exact ⟨maxwellOneSidedStepCore_subset_domain hball
      (hsourceYcore n), hsourceYValue n⟩
  have hsourceAtendsto : Tendsto sourceA atTop (nhds (x, 0)) := by
    simpa only [sourceA, Function.comp_def] using
      hA.source_tendsto.comp (tendsto_add_atTop_nat N)
  have hsourceBtendsto : Tendsto sourceB atTop (nhds (x, 0)) := by
    simpa only [sourceB, Function.comp_def] using
      hB.source_tendsto.comp (tendsto_add_atTop_nat N)
  have hsourceYtendsto : Tendsto sourceY atTop (nhds (x, 0)) := by
    exact tendsto_variable_lineMap hsourceAtendsto hsourceBtendsto htheta
  apply (mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
    U R i side x y).mpr
  refine ⟨
    { point := fun n ↦
        realEuclideanAppend
          (realEuclideanAppend (sourceY n).1 (fun _ : Fin 1 ↦ y))
          (fun _ : Fin 1 ↦ side.sign * (sourceY n).2)
      point_mem := fun n ↦ (hsourceYGraph n).1
      step_sign := fun n ↦ ?_
      tendsto_zeroStep :=
        tendsto_stepLastPoint_of_source_tendsto side y hsourceYtendsto }⟩
  cases side <;> simpa [MaxwellOneSidedStep.Accepts,
    MaxwellOneSidedStep.sign] using (hsourceYGraph n).2

/-- Global finite interval filling after restricting the trace to the open
base on which the scalar representative is continuous.  This is the honest
global form for an arbitrary open `U`; closure fibers over boundary points
need not satisfy the conclusion when different components approach the same
boundary point. -/
theorem maxwellFiniteSlopeIntervalFibers_restrict_oneSidedTrace_of_continuousOn
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z)) :
    MaxwellFiniteSlopeIntervalFibers
      (maxwellRelationRestrict
        (maxwellOneSidedStepZeroTrace U R i side) U) := by
  intro x a b hab ha hb
  have ha' :=
    (realEuclideanAppend_mem_maxwellRelationRestrict_iff
      (maxwellOneSidedStepZeroTrace U R i side) U x
      (fun _ : Fin 1 ↦ a)).mp ha
  have hb' :=
    (realEuclideanAppend_mem_maxwellRelationRestrict_iff
      (maxwellOneSidedStepZeroTrace U R i side) U x
      (fun _ : Fin 1 ↦ b)).mp hb
  intro y hy
  apply (realEuclideanAppend_mem_maxwellRelationRestrict_iff
    (maxwellOneSidedStepZeroTrace U R i side) U x
    (fun _ : Fin 1 ↦ y)).mpr
  exact ⟨maxwellOneSidedStepZeroTrace_interval_pointwise_of_continuousOn
    i side hUopen hf hrep ha'.2 hab ha'.1 hb'.1 hy, ha'.2⟩

/-- If every finite trace fiber is already based in `U`, the restriction in
the preceding theorem can be removed. -/
theorem maxwellFiniteSlopeIntervalFibers_oneSidedTrace_of_continuousOn
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    (hbase : maxwellRelationDomain
      (maxwellOneSidedStepZeroTrace U R i side) ⊆ U) :
    MaxwellFiniteSlopeIntervalFibers
      (maxwellOneSidedStepZeroTrace U R i side) := by
  intro x a b hab ha hb
  have hx : x ∈ U := hbase ⟨fun _ : Fin 1 ↦ a, ha⟩
  exact maxwellOneSidedStepZeroTrace_interval_pointwise_of_continuousOn
    i side hUopen hf hrep hx hab ha hb

/-! ## The four reciprocal infinity bases -/

/-- The sign of an infinite slope, represented before tracing by a reciprocal
approaching zero through the corresponding side. -/
inductive MaxwellSlopeInfinitySign where
  | positive
  | negative
deriving DecidableEq

/-- The sign condition on a reciprocal coordinate. -/
def MaxwellSlopeInfinitySign.AcceptsReciprocal
    (infinity : MaxwellSlopeInfinitySign) (r : ℝ) : Prop :=
  match infinity with
  | .positive => 0 < r
  | .negative => r < 0

@[simp]
theorem MaxwellSlopeInfinitySign.acceptsReciprocal_positive_iff (r : ℝ) :
    MaxwellSlopeInfinitySign.positive.AcceptsReciprocal r ↔ 0 < r :=
  Iff.rfl

@[simp]
theorem MaxwellSlopeInfinitySign.acceptsReciprocal_negative_iff (r : ℝ) :
    MaxwellSlopeInfinitySign.negative.AcceptsReciprocal r ↔ r < 0 :=
  Iff.rfl

/-- Uniform notation for the positive- and negative-reciprocal step-last
relations. -/
def maxwellOneSidedReciprocalStepLastRelation {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : MaxwellSlopeInfinitySign →
      Set (RealEuclidean ((p + 1) + 1))
  | .positive => maxwellPositiveReciprocalStepLastRelation U R i
  | .negative => maxwellNegativeReciprocalStepLastRelation U R i

/-- Take the reciprocal relation to zero through the selected side of the
actual step. -/
def maxwellOneSidedReciprocalTrace {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (infinity : MaxwellSlopeInfinitySign) : MaxwellRelation p 1 :=
  match side with
  | .positive => charbonnelPositiveZeroTrace
      (maxwellOneSidedReciprocalStepLastRelation U R i infinity)
  | .negative => maxwellNegativeZeroTrace
      (maxwellOneSidedReciprocalStepLastRelation U R i infinity)

/-- Uniform notation for the four bases obtained by first reciprocating the
slope, then tracing the step, and finally setting the reciprocal to zero. -/
def maxwellOneSidedInfinityBase {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (infinity : MaxwellSlopeInfinitySign) : Set (RealEuclidean p) :=
  charbonnelZeroSection
    (maxwellOneSidedReciprocalTrace U R i side infinity)

@[simp]
theorem maxwellOneSidedInfinityBase_positive_positive {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) (i : Fin p) :
    maxwellOneSidedInfinityBase U R i .positive .positive =
      maxwellPositiveStepPositiveInfinityBase U R i :=
  rfl

@[simp]
theorem maxwellOneSidedInfinityBase_positive_negative {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) (i : Fin p) :
    maxwellOneSidedInfinityBase U R i .positive .negative =
      maxwellPositiveStepNegativeInfinityBase U R i :=
  rfl

@[simp]
theorem maxwellOneSidedInfinityBase_negative_positive {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) (i : Fin p) :
    maxwellOneSidedInfinityBase U R i .negative .positive =
      maxwellNegativeStepPositiveInfinityBase U R i :=
  rfl

@[simp]
theorem maxwellOneSidedInfinityBase_negative_negative {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1) (i : Fin p) :
    maxwellOneSidedInfinityBase U R i .negative .negative =
      maxwellNegativeStepNegativeInfinityBase U R i :=
  rfl

/-- Uniform pointwise description of the two reciprocal relations. -/
theorem realEuclideanAppend_append_mem_maxwellOneSidedReciprocalStepLastRelation_iff
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (infinity : MaxwellSlopeInfinitySign)
    (x : RealEuclidean p) (epsilon r : ℝ) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ r))
        (fun _ : Fin 1 ↦ epsilon) ∈
      maxwellOneSidedReciprocalStepLastRelation U R i infinity ↔
    ∃ y : ℝ,
      realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
          (fun _ : Fin 1 ↦ epsilon) ∈
        maxwellStepLastDifferenceQuotientRelation U R i ∧
      y * r = 1 ∧ infinity.AcceptsReciprocal r := by
  cases infinity with
  | positive =>
      exact
        realEuclideanAppend_append_mem_maxwellPositiveReciprocalStepLastRelation_iff
          U R i x epsilon r
  | negative =>
      exact
        realEuclideanAppend_append_mem_maxwellNegativeReciprocalStepLastRelation_iff
          U R i x epsilon r

/-- A reciprocal-graph sequence witnessing one of the four existing
one-sided infinity bases.  Keeping it in the pre-trace relation records both
the nonzero step sign and the reciprocal sign. -/
structure MaxwellOneSidedInfiniteSlopeApproach
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (infinity : MaxwellSlopeInfinitySign) (x : RealEuclidean p) where
  point : ℕ → RealEuclidean ((p + 1) + 1)
  point_mem : ∀ n,
    point n ∈ maxwellOneSidedReciprocalStepLastRelation U R i infinity
  step_sign : ∀ n,
    side.Accepts (point n (Fin.last (p + 1)))
  tendsto_zeroReciprocalStep : Tendsto point atTop
    (nhds (realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ 0))
      (fun _ : Fin 1 ↦ 0)))

/-- Membership in any of the four source-defined infinity bases is exactly a
sequence in the appropriate reciprocal graph, with the actual step kept on
its selected side until after reciprocation. -/
theorem mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (infinity : MaxwellSlopeInfinitySign) (x : RealEuclidean p) :
    x ∈ maxwellOneSidedInfinityBase U R i side infinity ↔
      Nonempty
        (MaxwellOneSidedInfiniteSlopeApproach U R i side infinity x) := by
  cases side with
  | positive =>
      change charbonnelAppendLastCoordinate
          (realEuclideanAppend x (fun _ : Fin 1 ↦ 0)) 0 ∈
          closure (charbonnelPositiveLastPart
            (maxwellOneSidedReciprocalStepLastRelation U R i infinity)) ↔ _
      constructor
      · intro h
        obtain ⟨w, hw, hwlim⟩ := mem_closure_iff_seq_limit.mp h
        refine ⟨
          { point := w
            point_mem := fun n ↦ (hw n).1
            step_sign := fun n ↦ (hw n).2
            tendsto_zeroReciprocalStep := ?_ }⟩
        simpa only [charbonnelAppendLastCoordinate] using hwlim
      · rintro ⟨h⟩
        apply mem_closure_iff_seq_limit.mpr
        refine ⟨h.point, ?_, ?_⟩
        · intro n
          exact ⟨h.point_mem n, h.step_sign n⟩
        · simpa only [charbonnelAppendLastCoordinate] using
            h.tendsto_zeroReciprocalStep
  | negative =>
      rw [maxwellOneSidedInfinityBase, maxwellOneSidedReciprocalTrace,
        maxwellNegativeZeroTrace_eq_zeroSection_closure_negativeLastPart]
      change charbonnelAppendLastCoordinate
          (realEuclideanAppend x (fun _ : Fin 1 ↦ 0)) 0 ∈
          closure (maxwellNegativeLastPart
            (maxwellOneSidedReciprocalStepLastRelation U R i infinity)) ↔ _
      constructor
      · intro h
        obtain ⟨w, hw, hwlim⟩ := mem_closure_iff_seq_limit.mp h
        refine ⟨
          { point := w
            point_mem := fun n ↦ (hw n).1
            step_sign := fun n ↦ (hw n).2
            tendsto_zeroReciprocalStep := ?_ }⟩
        simpa only [charbonnelAppendLastCoordinate] using hwlim
      · rintro ⟨h⟩
        apply mem_closure_iff_seq_limit.mpr
        refine ⟨h.point, ?_, ?_⟩
        · intro n
          exact ⟨h.point_mem n, h.step_sign n⟩
        · simpa only [charbonnelAppendLastCoordinate] using
            h.tendsto_zeroReciprocalStep

/-! ## From reciprocal approaches to divergent ordinary slopes -/

/-- The order filter selected by the sign of infinity. -/
def MaxwellSlopeInfinitySign.divergenceFilter
    (infinity : MaxwellSlopeInfinitySign) : Filter ℝ :=
  match infinity with
  | .positive => atTop
  | .negative => atBot

theorem MaxwellOneSidedInfiniteSlopeApproach.base_tendsto
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} {side : MaxwellOneSidedStep}
    {infinity : MaxwellSlopeInfinitySign} {x : RealEuclidean p}
    (h : MaxwellOneSidedInfiniteSlopeApproach U R i side infinity x) :
    Tendsto (fun n ↦ maxwellStepLastBase (h.point n)) atTop (nhds x) := by
  have ht := (continuous_maxwellStepLastBase.tendsto
      (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ 0))
        (fun _ : Fin 1 ↦ 0))).comp h.tendsto_zeroReciprocalStep
  change Tendsto (fun n ↦ maxwellStepLastBase (h.point n)) atTop
    (nhds (maxwellStepLastBase
      (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ 0))
        (fun _ : Fin 1 ↦ 0)))) at ht
  simpa only [maxwellStepLastBase_append] using ht

theorem MaxwellOneSidedInfiniteSlopeApproach.reciprocal_tendsto
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} {side : MaxwellOneSidedStep}
    {infinity : MaxwellSlopeInfinitySign} {x : RealEuclidean p}
    (h : MaxwellOneSidedInfiniteSlopeApproach U R i side infinity x) :
    Tendsto (fun n ↦ maxwellStepLastValue (h.point n)) atTop
      (nhds 0) := by
  have ht := (continuous_maxwellStepLastValue.tendsto
      (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ 0))
        (fun _ : Fin 1 ↦ 0))).comp h.tendsto_zeroReciprocalStep
  change Tendsto (fun n ↦ maxwellStepLastValue (h.point n)) atTop
    (nhds (maxwellStepLastValue
      (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ 0))
        (fun _ : Fin 1 ↦ 0)))) at ht
  simpa only [maxwellStepLastValue_append] using ht

theorem MaxwellOneSidedInfiniteSlopeApproach.step_tendsto
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} {side : MaxwellOneSidedStep}
    {infinity : MaxwellSlopeInfinitySign} {x : RealEuclidean p}
    (h : MaxwellOneSidedInfiniteSlopeApproach U R i side infinity x) :
    Tendsto (fun n ↦ maxwellStepLastStep (h.point n)) atTop
      (nhds 0) := by
  have ht := (continuous_maxwellStepLastStep.tendsto
      (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ 0))
        (fun _ : Fin 1 ↦ 0))).comp h.tendsto_zeroReciprocalStep
  change Tendsto (fun n ↦ maxwellStepLastStep (h.point n)) atTop
    (nhds (maxwellStepLastStep
      (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ 0))
        (fun _ : Fin 1 ↦ 0)))) at ht
  simpa only [maxwellStepLastStep_append] using ht

theorem MaxwellOneSidedInfiniteSlopeApproach.source_tendsto
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} {side : MaxwellOneSidedStep}
    {infinity : MaxwellSlopeInfinitySign} {x : RealEuclidean p}
    (h : MaxwellOneSidedInfiniteSlopeApproach U R i side infinity x) :
    Tendsto (fun n ↦ maxwellOneSidedApproachSource side (h.point n))
      atTop (nhds (x, 0)) := by
  have hsigned : Tendsto
      (fun n ↦ side.sign * maxwellStepLastStep (h.point n))
      atTop (nhds (side.sign * 0)) :=
    tendsto_const_nhds.mul h.step_tendsto
  simpa only [maxwellOneSidedApproachSource, nhds_prod_eq, mul_zero] using
    h.base_tendsto.prodMk hsigned

/-- An ordinary sequence of nonzero one-sided quotient points whose sources
approach `(x,0)` and whose slopes diverge with the selected sign. -/
structure MaxwellOneSidedDivergentSlopeApproach
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (infinity : MaxwellSlopeInfinitySign) (x : RealEuclidean p) where
  source : ℕ → RealEuclidean p × ℝ
  slope : ℕ → ℝ
  source_tendsto : Tendsto source atTop (nhds (x, 0))
  source_step_pos : ∀ n, 0 < (source n).2
  point_mem : ∀ n,
    realEuclideanAppend
        (realEuclideanAppend (source n).1 (fun _ : Fin 1 ↦ slope n))
        (fun _ : Fin 1 ↦ side.sign * (source n).2) ∈
      maxwellStepLastDifferenceQuotientRelation U R i
  slope_tendsto : Tendsto slope atTop infinity.divergenceFilter

/-- Reciprocation is performed before the zero trace: an infinity-base
witness therefore yields a genuine sequence of ordinary nonzero quotient
points diverging to the corresponding order infinity. -/
def MaxwellOneSidedInfiniteSlopeApproach.toDivergentSlopeApproach
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {i : Fin p} {side : MaxwellOneSidedStep}
    {infinity : MaxwellSlopeInfinitySign} {x : RealEuclidean p}
    (h : MaxwellOneSidedInfiniteSlopeApproach U R i side infinity x) :
    MaxwellOneSidedDivergentSlopeApproach U R i side infinity x := by
  have hreciprocalGraph (n : ℕ) :
      realEuclideanAppend
          (realEuclideanAppend (maxwellStepLastBase (h.point n))
            (fun _ : Fin 1 ↦ maxwellStepLastValue (h.point n)))
          (fun _ : Fin 1 ↦ maxwellStepLastStep (h.point n)) ∈
        maxwellOneSidedReciprocalStepLastRelation U R i infinity := by
    rw [realEuclideanAppend_stepLastCoordinates]
    exact h.point_mem n
  have hwitness (n : ℕ) : ∃ y : ℝ,
      realEuclideanAppend
          (realEuclideanAppend (maxwellStepLastBase (h.point n))
            (fun _ : Fin 1 ↦ y))
          (fun _ : Fin 1 ↦ maxwellStepLastStep (h.point n)) ∈
          maxwellStepLastDifferenceQuotientRelation U R i ∧
        y * maxwellStepLastValue (h.point n) = 1 ∧
        infinity.AcceptsReciprocal
          (maxwellStepLastValue (h.point n)) :=
    (realEuclideanAppend_append_mem_maxwellOneSidedReciprocalStepLastRelation_iff
      U R i infinity (maxwellStepLastBase (h.point n))
      (maxwellStepLastStep (h.point n))
      (maxwellStepLastValue (h.point n))).mp (hreciprocalGraph n)
  choose slope hslopeGraph hslopeMul hslopeReciprocal using hwitness
  let source : ℕ → RealEuclidean p × ℝ :=
    fun n ↦ maxwellOneSidedApproachSource side (h.point n)
  have hslopeInv (n : ℕ) :
      slope n = (maxwellStepLastValue (h.point n))⁻¹ :=
    eq_inv_of_mul_eq_one_left (hslopeMul n)
  refine
    { source := source
      slope := slope
      source_tendsto := ?_
      source_step_pos := ?_
      point_mem := ?_
      slope_tendsto := ?_ }
  · simpa only [source] using h.source_tendsto
  · intro n
    exact
      (side.sign_mul_step_pos_iff (maxwellStepLastStep (h.point n))).mpr
        (h.step_sign n)
  · intro n
    change realEuclideanAppend
        (realEuclideanAppend (maxwellStepLastBase (h.point n))
          (fun _ : Fin 1 ↦ slope n))
        (fun _ : Fin 1 ↦
          side.sign * (side.sign * maxwellStepLastStep (h.point n))) ∈
      maxwellStepLastDifferenceQuotientRelation U R i
    rw [← mul_assoc, side.sign_mul_self, one_mul]
    exact hslopeGraph n
  · cases infinity with
    | positive =>
        have hwithin : Tendsto
            (fun n ↦ maxwellStepLastValue (h.point n)) atTop
            (nhdsWithin 0 (Set.Ioi (0 : ℝ))) :=
          tendsto_nhdsWithin_iff.mpr
            ⟨h.reciprocal_tendsto,
              Filter.Eventually.of_forall (fun n ↦ hslopeReciprocal n)⟩
        exact hwithin.inv_tendsto_nhdsGT_zero.congr'
          (Filter.Eventually.of_forall (fun n ↦ (hslopeInv n).symm))
    | negative =>
        have hwithin : Tendsto
            (fun n ↦ maxwellStepLastValue (h.point n)) atTop
            (nhdsWithin 0 (Set.Iio (0 : ℝ))) :=
          tendsto_nhdsWithin_iff.mpr
            ⟨h.reciprocal_tendsto,
              Filter.Eventually.of_forall (fun n ↦ hslopeReciprocal n)⟩
        exact hwithin.inv_tendsto_nhdsLT_zero.congr'
          (Filter.Eventually.of_forall (fun n ↦ (hslopeInv n).symm))

/-! ## Concrete finite anchors -/

/-- A concrete finite comparison sequence for one side of the ordinary
difference quotient.  This is the extra control genuinely needed at an
infinite cluster: continuity of `f` alone does not rule out every quotient
tending to infinity (for instance a square-root cusp), and a value obtained
by formally substituting a zero step would be invalid. -/
structure MaxwellDirectOneSidedFiniteSlopeAnchor
    {p : ℕ} (U : Set (RealEuclidean p)) (f : RealEuclidean p → ℝ)
    (i : Fin p) (side : MaxwellOneSidedStep)
    (x : RealEuclidean p) (c : ℝ) where
  source : ℕ → RealEuclidean p × ℝ
  source_mem : ∀ n, source n ∈ maxwellOneSidedStepDomain U i side
  source_tendsto : Tendsto source atTop (nhds (x, 0))
  quotient_tendsto : Tendsto
    (fun n ↦ maxwellOneSidedDifferenceQuotient f i side (source n))
    atTop (nhds c)

/-- Assemble a step-last point when both its normalized source and its
possibly varying scalar value converge. -/
theorem tendsto_stepLastPoint_of_source_and_value_tendsto
    {p : ℕ} {source : ℕ → RealEuclidean p × ℝ}
    {value : ℕ → ℝ} {x : RealEuclidean p} {y : ℝ}
    (side : MaxwellOneSidedStep)
    (hsource : Tendsto source atTop (nhds (x, 0)))
    (hvalue : Tendsto value atTop (nhds y)) :
    Tendsto
      (fun n ↦
        realEuclideanAppend
          (realEuclideanAppend (source n).1 (fun _ : Fin 1 ↦ value n))
          (fun _ : Fin 1 ↦ side.sign * (source n).2))
      atTop
      (nhds (realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
        (fun _ : Fin 1 ↦ 0))) := by
  have hbase : Tendsto (fun n ↦ (source n).1) atTop (nhds x) :=
    continuous_fst.tendsto (x, 0) |>.comp hsource
  have hstep : Tendsto (fun n ↦ (source n).2) atTop (nhds 0) :=
    continuous_snd.tendsto (x, 0) |>.comp hsource
  have hvalueVector : Tendsto
      (fun n ↦ fun _ : Fin 1 ↦ value n) atTop
      (nhds (fun _ : Fin 1 ↦ y)) := by
    rw [tendsto_pi_nhds]
    intro j
    simpa using hvalue
  have hsignedStep : Tendsto (fun n ↦ side.sign * (source n).2)
      atTop (nhds 0) := by
    convert tendsto_const_nhds.mul hstep using 1 <;> simp
  have hsignedStepVector : Tendsto
      (fun n ↦ fun _ : Fin 1 ↦ side.sign * (source n).2)
      atTop (nhds (fun _ : Fin 1 ↦ 0)) := by
    rw [tendsto_pi_nhds]
    intro j
    simpa using hsignedStep
  exact tendsto_realEuclideanAppend
    (tendsto_realEuclideanAppend hbase hvalueVector)
    hsignedStepVector

/-- A concrete ordinary finite anchor gives membership in the actual
one-sided zero trace of any relation representing the scalar function. -/
def MaxwellDirectOneSidedFiniteSlopeAnchor.toSlopeApproach
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    {side : MaxwellOneSidedStep} {x : RealEuclidean p} {c : ℝ}
    (h : MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x c)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z)) :
    MaxwellOneSidedSlopeApproach U R i side x c := by
  let value : ℕ → ℝ := fun n ↦
    maxwellOneSidedDifferenceQuotient f i side (h.source n)
  refine
    { point := fun n ↦
        realEuclideanAppend
          (realEuclideanAppend (h.source n).1 (fun _ : Fin 1 ↦ value n))
          (fun _ : Fin 1 ↦ side.sign * (h.source n).2)
      point_mem := ?_
      step_sign := ?_
      tendsto_zeroStep := ?_ }
  · intro n
    exact
      ((realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_oneSided_of_representsOn_iff
        i hrep side (h.source n).1 (h.source n).2 (value n)).mpr
          ⟨h.source_mem n, rfl⟩).1
  · intro n
    cases side <;> simpa [MaxwellOneSidedStep.Accepts,
      MaxwellOneSidedStep.sign] using (h.source_mem n).2.2
  · exact tendsto_stepLastPoint_of_source_and_value_tendsto side
      h.source_tendsto (by simpa only [value] using h.quotient_tendsto)

theorem MaxwellDirectOneSidedFiniteSlopeAnchor.mem_stepZeroTrace
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    {side : MaxwellOneSidedStep} {x : RealEuclidean p} {c : ℝ}
    (h : MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x c)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z)) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ c) ∈
      maxwellOneSidedStepZeroTrace U R i side :=
  (mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
    U R i side x c).mpr ⟨h.toSlopeApproach hrep⟩

theorem MaxwellOneSidedDivergentSlopeApproach.source_mem_domain_of_representsOn
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} {i : Fin p}
    {side : MaxwellOneSidedStep} {infinity : MaxwellSlopeInfinitySign}
    {x : RealEuclidean p}
    (h : MaxwellOneSidedDivergentSlopeApproach U R i side infinity x)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    (n : ℕ) :
    h.source n ∈ maxwellOneSidedStepDomain U i side ∧
      h.slope n =
        maxwellOneSidedDifferenceQuotient f i side (h.source n) := by
  apply
    (realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_oneSided_of_representsOn_iff
      i hrep side (h.source n).1 (h.source n).2 (h.slope n)).mp
  exact ⟨h.point_mem n, h.source_step_pos n⟩

/-- Any positive-step source sequence converging to `(x,0)` eventually lies
in each fixed local convex core. -/
theorem eventually_mem_maxwellOneSidedStepCore_of_tendsto
    {p : ℕ} {x : RealEuclidean p} {rho : ℝ} {i : Fin p}
    {side : MaxwellOneSidedStep}
    {source : ℕ → RealEuclidean p × ℝ}
    (hsource : Tendsto source atTop (nhds (x, 0)))
    (hstep : ∀ n, 0 < (source n).2) (hrho : 0 < rho) :
    ∀ᶠ n in atTop,
      source n ∈ maxwellOneSidedStepCore x rho i side := by
  have hbase : Tendsto (fun n ↦ (source n).1) atTop (nhds x) :=
    continuous_fst.tendsto (x, 0) |>.comp hsource
  have hshift : Tendsto
      (fun n ↦ maxwellOneSidedShiftLinearMap i side (source n))
      atTop (nhds x) := by
    have ht :=
      ((maxwellOneSidedShiftLinearMap i side).toContinuousLinearMap.continuous
        |>.tendsto (x, 0)).comp hsource
    change Tendsto
      (fun n ↦ maxwellOneSidedShiftLinearMap i side (source n)) atTop
      (nhds (maxwellOneSidedShiftLinearMap i side (x, 0))) at ht
    simpa only [maxwellOneSidedShiftLinearMap_apply, mul_zero, zero_smul,
      add_zero] using ht
  have hbaseEventually : ∀ᶠ n in atTop, (source n).1 ∈ Metric.ball x rho :=
    hbase.eventually (Metric.ball_mem_nhds x hrho)
  have hshiftEventually : ∀ᶠ n in atTop,
      maxwellOneSidedShiftLinearMap i side (source n) ∈
        Metric.ball x rho :=
    hshift.eventually (Metric.ball_mem_nhds x hrho)
  filter_upwards [hbaseEventually, hshiftEventually] with n hnbase hnshift
  exact ⟨⟨hnbase, hnshift⟩, hstep n⟩

/-! ## IVT between a finite anchor and a divergent approach -/

/-- A reusable shrinking-core IVT.  Two sequences of valid positive
parameters approach the same zero-step base and their ordinary quotient
values eventually straddle `y`; hence `y` belongs to the genuine one-sided
zero trace. -/
theorem maxwellOneSidedStepZeroTrace_mem_of_straddling_sources
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ U) {y : ℝ}
    {sourceLow sourceHigh : ℕ → RealEuclidean p × ℝ}
    {valueLow valueHigh : ℕ → ℝ}
    (hsourceLow : Tendsto sourceLow atTop (nhds (x, 0)))
    (hsourceHigh : Tendsto sourceHigh atTop (nhds (x, 0)))
    (hstepLow : ∀ n, 0 < (sourceLow n).2)
    (hstepHigh : ∀ n, 0 < (sourceHigh n).2)
    (hLow : ∀ n,
      sourceLow n ∈ maxwellOneSidedStepDomain U i side ∧
        valueLow n =
          maxwellOneSidedDifferenceQuotient f i side (sourceLow n))
    (hHigh : ∀ n,
      sourceHigh n ∈ maxwellOneSidedStepDomain U i side ∧
        valueHigh n =
          maxwellOneSidedDifferenceQuotient f i side (sourceHigh n))
    (hstraddle : ∀ᶠ n in atTop, valueLow n < y ∧ y < valueHigh n) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
      maxwellOneSidedStepZeroTrace U R i side := by
  obtain ⟨rho, hrho, hball⟩ := Metric.isOpen_iff.mp hUopen x hx
  have hcoreLow : ∀ᶠ n in atTop,
      sourceLow n ∈ maxwellOneSidedStepCore x rho i side :=
    eventually_mem_maxwellOneSidedStepCore_of_tendsto
      hsourceLow hstepLow hrho
  have hcoreHigh : ∀ᶠ n in atTop,
      sourceHigh n ∈ maxwellOneSidedStepCore x rho i side :=
    eventually_mem_maxwellOneSidedStepCore_of_tendsto
      hsourceHigh hstepHigh hrho
  have hEventually : ∀ᶠ n in atTop,
      sourceLow n ∈ maxwellOneSidedStepCore x rho i side ∧
      sourceHigh n ∈ maxwellOneSidedStepCore x rho i side ∧
      valueLow n < y ∧ y < valueHigh n := by
    filter_upwards [hcoreLow, hcoreHigh, hstraddle] with n hnLow hnHigh hn
    exact ⟨hnLow, hnHigh, hn⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEventually
  let low : ℕ → RealEuclidean p × ℝ := fun n ↦ sourceLow (n + N)
  let high : ℕ → RealEuclidean p × ℝ := fun n ↦ sourceHigh (n + N)
  have htail (n : ℕ) := hN (n + N) (by omega)
  have hlowCore (n : ℕ) :
      low n ∈ maxwellOneSidedStepCore x rho i side :=
    (htail n).1
  have hhighCore (n : ℕ) :
      high n ∈ maxwellOneSidedStepCore x rho i side :=
    (htail n).2.1
  have hlowValue (n : ℕ) :
      maxwellOneSidedDifferenceQuotient f i side (low n) =
        valueLow (n + N) :=
    (hLow (n + N)).2.symm
  have hhighValue (n : ℕ) :
      maxwellOneSidedDifferenceQuotient f i side (high n) =
        valueHigh (n + N) :=
    (hHigh (n + N)).2.symm
  have hbetween (n : ℕ) : y ∈ Set.Icc
      (maxwellOneSidedDifferenceQuotient f i side (low n))
      (maxwellOneSidedDifferenceQuotient f i side (high n)) := by
    rw [hlowValue n, hhighValue n]
    exact ⟨le_of_lt (htail n).2.2.1, le_of_lt (htail n).2.2.2⟩
  have hcontinuous :=
    continuousOn_maxwellOneSidedDifferenceQuotient_stepCore
      i side hf hball
  have hexists (n : ℕ) : ∃ t ∈ Set.Icc (0 : ℝ) 1,
      maxwellOneSidedDifferenceQuotient f i side
        (low n + t • (high n - low n)) = y :=
    exists_lineMap_eq_of_continuousOn_convex
      (convex_maxwellOneSidedStepCore x rho i side) hcontinuous
      (hlowCore n) (hhighCore n) (hbetween n)
  choose theta htheta hthetaValue using hexists
  let sourceY : ℕ → RealEuclidean p × ℝ := fun n ↦
    low n + theta n • (high n - low n)
  have hsourceYcore (n : ℕ) :
      sourceY n ∈ maxwellOneSidedStepCore x rho i side :=
    (convex_maxwellOneSidedStepCore x rho i side).add_smul_sub_mem
      (hlowCore n) (hhighCore n) (htheta n)
  have hsourceYGraph (n : ℕ) :
      realEuclideanAppend
          (realEuclideanAppend (sourceY n).1 (fun _ : Fin 1 ↦ y))
          (fun _ : Fin 1 ↦ side.sign * (sourceY n).2) ∈
          maxwellStepLastDifferenceQuotientRelation U R i ∧
        0 < (sourceY n).2 := by
    apply
      (realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_oneSided_of_representsOn_iff
        i hrep side (sourceY n).1 (sourceY n).2 y).mpr
    exact ⟨maxwellOneSidedStepCore_subset_domain hball
      (hsourceYcore n), (hthetaValue n).symm⟩
  have hlowTendsto : Tendsto low atTop (nhds (x, 0)) := by
    simpa only [low, Function.comp_def] using
      hsourceLow.comp (tendsto_add_atTop_nat N)
  have hhighTendsto : Tendsto high atTop (nhds (x, 0)) := by
    simpa only [high, Function.comp_def] using
      hsourceHigh.comp (tendsto_add_atTop_nat N)
  have hsourceYTendsto : Tendsto sourceY atTop (nhds (x, 0)) :=
    tendsto_variable_lineMap hlowTendsto hhighTendsto htheta
  apply (mem_maxwellOneSidedStepZeroTrace_iff_nonempty_approach
    U R i side x y).mpr
  refine ⟨
    { point := fun n ↦
        realEuclideanAppend
          (realEuclideanAppend (sourceY n).1 (fun _ : Fin 1 ↦ y))
          (fun _ : Fin 1 ↦ side.sign * (sourceY n).2)
      point_mem := fun n ↦ (hsourceYGraph n).1
      step_sign := fun n ↦ ?_
      tendsto_zeroStep :=
        tendsto_stepLastPoint_of_source_tendsto side y hsourceYTendsto }⟩
  cases side <;> simpa [MaxwellOneSidedStep.Accepts,
    MaxwellOneSidedStep.sign] using (hsourceYGraph n).2

/-- A concrete finite anchor and a positive-infinity reciprocal cluster fill
every finite trace value above the anchor. -/
theorem maxwellOneSidedStepZeroTrace_above_of_positiveInfinity_and_anchor
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ U) {c y : ℝ}
    (hanchor : MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x c)
    (hinfinity : x ∈
      maxwellOneSidedInfinityBase U R i side .positive)
    (hcy : c < y) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
      maxwellOneSidedStepZeroTrace U R i side := by
  obtain ⟨hreciprocal⟩ :=
    (mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
      U R i side .positive x).mp hinfinity
  let hdivergent := hreciprocal.toDivergentSlopeApproach
  have hanchorBelow : ∀ᶠ n in atTop,
      maxwellOneSidedDifferenceQuotient f i side (hanchor.source n) < y :=
    hanchor.quotient_tendsto.eventually_lt_const hcy
  have hdivergentTop : Tendsto hdivergent.slope atTop atTop := by
    simpa only [MaxwellSlopeInfinitySign.divergenceFilter] using
      hdivergent.slope_tendsto
  have hdivergentAbove : ∀ᶠ n in atTop, y < hdivergent.slope n :=
    hdivergentTop.eventually_gt_atTop y
  have hstraddle : ∀ᶠ n in atTop,
      maxwellOneSidedDifferenceQuotient f i side (hanchor.source n) < y ∧
        y < hdivergent.slope n :=
    hanchorBelow.and hdivergentAbove
  exact maxwellOneSidedStepZeroTrace_mem_of_straddling_sources
    i side hUopen hf hrep hx
    hanchor.source_tendsto hdivergent.source_tendsto
    (fun n ↦ (hanchor.source_mem n).2.2)
    hdivergent.source_step_pos
    (fun n ↦ ⟨hanchor.source_mem n, rfl⟩)
    (fun n ↦ hdivergent.source_mem_domain_of_representsOn hrep n)
    hstraddle

/-- A concrete finite anchor and a negative-infinity reciprocal cluster fill
every finite trace value below the anchor. -/
theorem maxwellOneSidedStepZeroTrace_below_of_negativeInfinity_and_anchor
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ U) {c y : ℝ}
    (hanchor : MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x c)
    (hinfinity : x ∈
      maxwellOneSidedInfinityBase U R i side .negative)
    (hyc : y < c) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
      maxwellOneSidedStepZeroTrace U R i side := by
  obtain ⟨hreciprocal⟩ :=
    (mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
      U R i side .negative x).mp hinfinity
  let hdivergent := hreciprocal.toDivergentSlopeApproach
  have hdivergentBot : Tendsto hdivergent.slope atTop atBot := by
    simpa only [MaxwellSlopeInfinitySign.divergenceFilter] using
      hdivergent.slope_tendsto
  have hdivergentBelow : ∀ᶠ n in atTop, hdivergent.slope n < y :=
    hdivergentBot.eventually_lt_atBot y
  have hanchorAbove : ∀ᶠ n in atTop,
      y < maxwellOneSidedDifferenceQuotient f i side (hanchor.source n) :=
    hanchor.quotient_tendsto.eventually_const_lt hyc
  have hstraddle : ∀ᶠ n in atTop,
      hdivergent.slope n < y ∧
        y < maxwellOneSidedDifferenceQuotient f i side (hanchor.source n) :=
    hdivergentBelow.and hanchorAbove
  exact maxwellOneSidedStepZeroTrace_mem_of_straddling_sources
    i side hUopen hf hrep hx
    hdivergent.source_tendsto hanchor.source_tendsto
    hdivergent.source_step_pos
    (fun n ↦ (hanchor.source_mem n).2.2)
    (fun n ↦ hdivergent.source_mem_domain_of_representsOn hrep n)
    (fun n ↦ ⟨hanchor.source_mem n, rfl⟩)
    hstraddle

/-- Positive infinity yields arbitrarily large finite trace values once a
concrete direct finite anchor is supplied. -/
theorem maxwellOneSidedStepZeroTrace_positiveInfinity_unbounded_pointwise
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ U) {c : ℝ}
    (hanchor : MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x c)
    (hinfinity : x ∈
      maxwellOneSidedInfinityBase U R i side .positive) :
    ∀ M : ℝ, ∃ y : ℝ, M < y ∧
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellOneSidedStepZeroTrace U R i side := by
  intro M
  let y := max M c + 1
  have hMy : M < y := by
    dsimp only [y]
    linarith [le_max_left M c]
  have hcy : c < y := by
    dsimp only [y]
    linarith [le_max_right M c]
  exact ⟨y, hMy,
    maxwellOneSidedStepZeroTrace_above_of_positiveInfinity_and_anchor
      i side hUopen hf hrep hx hanchor hinfinity hcy⟩

/-- Negative infinity yields arbitrarily small finite trace values once a
concrete direct finite anchor is supplied. -/
theorem maxwellOneSidedStepZeroTrace_negativeInfinity_unbounded_pointwise
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ U) {c : ℝ}
    (hanchor : MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x c)
    (hinfinity : x ∈
      maxwellOneSidedInfinityBase U R i side .negative) :
    ∀ M : ℝ, ∃ y : ℝ, y < M ∧
      realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellOneSidedStepZeroTrace U R i side := by
  intro M
  let y := min M c - 1
  have hyM : y < M := by
    dsimp only [y]
    linarith [min_le_left M c]
  have hyc : y < c := by
    dsimp only [y]
    linarith [min_le_right M c]
  exact ⟨y, hyM,
    maxwellOneSidedStepZeroTrace_below_of_negativeInfinity_and_anchor
      i side hUopen hf hrep hx hanchor hinfinity hyc⟩

/-! ## Source-shaped one-sided IVT data -/

/-- On an arbitrary open representative domain, the fully honest global
statement restricts every finite and infinite fiber to bases in that domain.
The only additional hypothesis at an infinite fiber is a concrete finite
nonzero-step anchor; no interval-filling or unboundedness conclusion is
assumed. -/
theorem maxwellOneSidedSlopeIVTData_restrict_of_continuousOn_and_anchors
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    {f : RealEuclidean p → ℝ} (i : Fin p)
    (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hf : ContinuousOn f U)
    (hrep : MaxwellRelation.RepresentsOn R U (fun z _ ↦ f z))
    (hpositiveAnchor : ∀ x : RealEuclidean p,
      x ∈ maxwellOneSidedInfinityBase U R i side .positive ∩ U →
      ∃ c : ℝ,
        Nonempty (MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x c))
    (hnegativeAnchor : ∀ x : RealEuclidean p,
      x ∈ maxwellOneSidedInfinityBase U R i side .negative ∩ U →
      ∃ c : ℝ,
        Nonempty (MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x c)) :
    MaxwellOneSidedSlopeIVTData
      (maxwellRelationRestrict
        (maxwellOneSidedStepZeroTrace U R i side) U)
      (maxwellOneSidedInfinityBase U R i side .positive ∩ U)
      (maxwellOneSidedInfinityBase U R i side .negative ∩ U) := by
  refine
    { finite_intermediateValue :=
        maxwellFiniteSlopeIntervalFibers_restrict_oneSidedTrace_of_continuousOn
          i side hUopen hf hrep
      positiveInfinity_unbounded := ?_
      negativeInfinity_unbounded := ?_ }
  · intro x hx M
    obtain ⟨c, ⟨hanchor⟩⟩ := hpositiveAnchor x hx
    obtain ⟨y, hMy, hy⟩ :=
      maxwellOneSidedStepZeroTrace_positiveInfinity_unbounded_pointwise
        i side hUopen hf hrep hx.2 hanchor hx.1 M
    refine ⟨y, hMy, ?_⟩
    exact
      (realEuclideanAppend_mem_maxwellRelationRestrict_iff
        (maxwellOneSidedStepZeroTrace U R i side) U x
        (fun _ : Fin 1 ↦ y)).mpr ⟨hy, hx.2⟩
  · intro x hx M
    obtain ⟨c, ⟨hanchor⟩⟩ := hnegativeAnchor x hx
    obtain ⟨y, hyM, hy⟩ :=
      maxwellOneSidedStepZeroTrace_negativeInfinity_unbounded_pointwise
        i side hUopen hf hrep hx.2 hanchor hx.1 M
    refine ⟨y, hyM, ?_⟩
    exact
      (realEuclideanAppend_mem_maxwellRelationRestrict_iff
        (maxwellOneSidedStepZeroTrace U R i side) U x
        (fun _ : Fin 1 ↦ y)).mpr ⟨hy, hx.2⟩

/-- The unrestricted source-shaped data follows when all three kinds of
closure fibers under consideration are known to be based inside `U`.  These
base-containment premises are necessary: for disconnected open sets,
different components can approach one boundary base with incompatible
finite cluster values. -/
theorem maxwellOneSidedSlopeIVTData_of_continuousOn_and_anchors
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
      maxwellOneSidedInfinityBase U R i side .negative ⊆ U)
    (hpositiveAnchor : ∀ x : RealEuclidean p,
      x ∈ maxwellOneSidedInfinityBase U R i side .positive →
      ∃ c : ℝ,
        Nonempty (MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x c))
    (hnegativeAnchor : ∀ x : RealEuclidean p,
      x ∈ maxwellOneSidedInfinityBase U R i side .negative →
      ∃ c : ℝ,
        Nonempty (MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x c)) :
    MaxwellOneSidedSlopeIVTData
      (maxwellOneSidedStepZeroTrace U R i side)
      (maxwellOneSidedInfinityBase U R i side .positive)
      (maxwellOneSidedInfinityBase U R i side .negative) := by
  refine
    { finite_intermediateValue :=
        maxwellFiniteSlopeIntervalFibers_oneSidedTrace_of_continuousOn
          i side hUopen hf hrep hfiniteBase
      positiveInfinity_unbounded := ?_
      negativeInfinity_unbounded := ?_ }
  · intro x hx M
    obtain ⟨c, ⟨hanchor⟩⟩ := hpositiveAnchor x hx
    exact
      maxwellOneSidedStepZeroTrace_positiveInfinity_unbounded_pointwise
        i side hUopen hf hrep (hpositiveBase hx) hanchor hx M
  · intro x hx M
    obtain ⟨c, ⟨hanchor⟩⟩ := hnegativeAnchor x hx
    exact
      maxwellOneSidedStepZeroTrace_negativeInfinity_unbounded_pointwise
        i side hUopen hf hrep (hnegativeBase hx) hanchor hx M

/-- The preceding concrete hypotheses supply the exact extended interval
filling consumed by the one-sided Fubini reduction. -/
theorem maxwellOneSidedExtendedSlopeIntervalFilling_of_continuousOn_and_anchors
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
      maxwellOneSidedInfinityBase U R i side .negative ⊆ U)
    (hpositiveAnchor : ∀ x : RealEuclidean p,
      x ∈ maxwellOneSidedInfinityBase U R i side .positive →
      ∃ c : ℝ,
        Nonempty (MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x c))
    (hnegativeAnchor : ∀ x : RealEuclidean p,
      x ∈ maxwellOneSidedInfinityBase U R i side .negative →
      ∃ c : ℝ,
        Nonempty (MaxwellDirectOneSidedFiniteSlopeAnchor U f i side x c)) :
    MaxwellExtendedSlopeIntervalFilling
      (maxwellOneSidedStepZeroTrace U R i side)
      (maxwellOneSidedExtendedMultivaluedLocus
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative)) :=
  (maxwellOneSidedSlopeIVTData_of_continuousOn_and_anchors
    i side hUopen hf hrep hfiniteBase hpositiveBase hnegativeBase
    hpositiveAnchor hnegativeAnchor).intervalFilling

end AbelFormalization
