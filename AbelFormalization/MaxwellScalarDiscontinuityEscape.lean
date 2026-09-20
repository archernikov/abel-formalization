import AbelFormalization.MaxwellScalarDiscontinuity
import AbelFormalization.MaxwellLocalFiberCardinality
import AbelFormalization.MaxwellScalarFiberExtrema
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The bounded-gap step in Maxwell--Figueiredo Lemma 2.2.2

This file formalizes the two countable exhaustions and the oriented
closure-fiber incidences in the empty-interior proof of Lemma 2.2.2.
The first exhaustion makes the original scalar function locally bounded.
Local boundedness rules out both reciprocal-zero alternatives.  The second
exhaustion turns a strict gap between the function value and an extremal
closed-graph value into one uniform positive gap.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Bounded-value bases -/

/-- The scalar output coordinate in flat `(x,y)` coordinates. -/
def maxwellScalarOutputIndex (p : ℕ) : Fin (p + 1) :=
  Fin.natAdd p 0

/-- The semialgebraic constraint `-M < y < M` on the scalar output. -/
def maxwellScalarOpenBoundConstraint (p : ℕ) (M : ℝ) :
    Set (RealEuclidean (p + 1)) :=
  {z | 0 < MvPolynomial.eval z
      (MvPolynomial.X (maxwellScalarOutputIndex p) +
        MvPolynomial.C M)} ∩
  {z | 0 < MvPolynomial.eval z
      (MvPolynomial.C M -
        MvPolynomial.X (maxwellScalarOutputIndex p))}

theorem polynomialSignConstructible_maxwellScalarOpenBoundConstraint
    (p : ℕ) (M : ℝ) :
    PolynomialSignConstructible (p + 1)
      (maxwellScalarOpenBoundConstraint p M) :=
  .inter
    (.pos (MvPolynomial.X (maxwellScalarOutputIndex p) +
      MvPolynomial.C M))
    (.pos (MvPolynomial.C M -
      MvPolynomial.X (maxwellScalarOutputIndex p)))

@[simp]
theorem realEuclideanAppend_mem_maxwellScalarOpenBoundConstraint_iff
    {p : ℕ} (x : RealEuclidean p) (y : ℝ) (M : ℝ) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellScalarOpenBoundConstraint p M ↔
      |y| < M := by
  simp only [maxwellScalarOpenBoundConstraint, Set.mem_inter_iff,
    Set.mem_setOf_eq, maxwellScalarOutputIndex,
    map_add, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C,
    realEuclideanAppend_natAdd]
  rw [abs_lt]
  constructor
  · rintro ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hleft, hright⟩
    exact ⟨by linarith, by linarith⟩

/-- Base points in `B` at which `R` has a scalar value of absolute value
strictly less than `M`. -/
def maxwellScalarBoundedValueBase {p : ℕ}
    (B : Set (RealEuclidean p)) (R : MaxwellRelation p 1) (M : ℝ) :
    Set (RealEuclidean p) :=
  realEuclideanExistentialProjection
    (maxwellRelationRestrict R B ∩
      maxwellScalarOpenBoundConstraint p M)

@[simp]
theorem mem_maxwellScalarBoundedValueBase_iff
    {p : ℕ} (B : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) (M : ℝ) (x : RealEuclidean p) :
    x ∈ maxwellScalarBoundedValueBase B R M ↔
      x ∈ B ∧ ∃ y : ℝ,
        realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈ R ∧ |y| < M := by
  change (∃ y : RealEuclidean 1,
    realEuclideanAppend x y ∈ maxwellRelationRestrict R B ∩
      maxwellScalarOpenBoundConstraint p M) ↔ _
  constructor
  · rintro ⟨y, hyR, hyBound⟩
    have hyConst : y = fun _ : Fin 1 ↦ y 0 := by
      funext i
      exact congrArg y (Subsingleton.elim i 0)
    have hrestrict :=
      (realEuclideanAppend_mem_maxwellRelationRestrict_iff
        R B x y).mp hyR
    refine ⟨hrestrict.2, y 0, ?_, ?_⟩
    · simpa only [← hyConst] using hrestrict.1
    · rw [hyConst] at hyBound
      exact (realEuclideanAppend_mem_maxwellScalarOpenBoundConstraint_iff
        x (y 0) M).mp hyBound
  · rintro ⟨hxB, y, hyR, hyBound⟩
    refine ⟨fun _ : Fin 1 ↦ y, ?_, ?_⟩
    · exact (realEuclideanAppend_mem_maxwellRelationRestrict_iff
        R B x (fun _ : Fin 1 ↦ y)).mpr ⟨hyR, hxB⟩
    · exact (realEuclideanAppend_mem_maxwellScalarOpenBoundConstraint_iff
        x y M).mpr hyBound

theorem mem_maxwellScalarBoundedValueBase_functionGraph_iff
    {p : ℕ} {B U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    (hBU : B ⊆ U) (M : ℝ) (x : RealEuclidean p) :
    x ∈ maxwellScalarBoundedValueBase B (maxwellFunctionGraph U f) M ↔
      x ∈ B ∧ |f x 0| < M := by
  rw [mem_maxwellScalarBoundedValueBase_iff]
  constructor
  · rintro ⟨hxB, y, hyGraph, hyBound⟩
    have hy := (realEuclideanAppend_mem_maxwellFunctionGraph_iff
      U f x (fun _ : Fin 1 ↦ y)).mp hyGraph
    have hy0 : y = f x 0 := congrFun hy.2 0
    exact ⟨hxB, by simpa only [hy0] using hyBound⟩
  · rintro ⟨hxB, hxBound⟩
    refine ⟨hxB, f x 0, ?_, hxBound⟩
    apply (realEuclideanAppend_mem_maxwellFunctionGraph_iff
      U f x (fun _ : Fin 1 ↦ f x 0)).mpr
    refine ⟨hBU hxB, ?_⟩
    funext i
    exact congrArg (f x) (Subsingleton.elim i 0) |>.symm

theorem maxwellScalarBoundedValueBase_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hB : B ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) (M : ℝ) :
    maxwellScalarBoundedValueBase B R M ∈ charbonnelClosure S p := by
  have hrestrict : maxwellRelationRestrict R B ∈
      charbonnelClosure S (p + 1) :=
    maxwellRelationRestrict_mem_charbonnelClosure hC hp hB hR
  have hbound : maxwellScalarOpenBoundConstraint p M ∈
      charbonnelClosure S (p + 1) :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_maxwellScalarOpenBoundConstraint p M)
  exact charbonnelClosure_projection hp
    (hC.ws1_inter (by omega) hrestrict hbound)

/-! ## Oriented gaps between two scalar relations -/

/-- The semialgebraic constraint `a + δ < b` on fiber-pair coordinates
`(x,a,b)`. -/
def maxwellScalarUpwardGapConstraint (p : ℕ) (δ : ℝ) :
    Set (RealEuclidean (p + 2)) :=
  {w | 0 < MvPolynomial.eval w
    (MvPolynomial.X (maxwellFiberPairSecondValueIndex p) -
      MvPolynomial.X (maxwellFiberPairFirstValueIndex p) -
      MvPolynomial.C δ)}

theorem polynomialSignConstructible_maxwellScalarUpwardGapConstraint
    (p : ℕ) (δ : ℝ) :
    PolynomialSignConstructible (p + 2)
      (maxwellScalarUpwardGapConstraint p δ) :=
  .pos (MvPolynomial.X (maxwellFiberPairSecondValueIndex p) -
    MvPolynomial.X (maxwellFiberPairFirstValueIndex p) -
    MvPolynomial.C δ)

@[simp]
theorem realEuclideanAppend_mem_maxwellScalarUpwardGapConstraint_iff
    {p : ℕ} (x : RealEuclidean p) (v : RealEuclidean 2) (δ : ℝ) :
    realEuclideanAppend x v ∈
        maxwellScalarUpwardGapConstraint p δ ↔
      v 0 + δ < v 1 := by
  simp only [maxwellScalarUpwardGapConstraint, Set.mem_setOf_eq,
    maxwellFiberPairFirstValueIndex,
    maxwellFiberPairSecondValueIndex, map_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_C,
    realEuclideanAppend_natAdd]
  constructor <;> intro h <;> linarith

/-- Incidence for an `R`-value and a larger `T`-value over one point of
`B`, separated by more than `δ`. -/
def maxwellScalarUpwardGapIncidence {p : ℕ}
    (B : Set (RealEuclidean p))
    (R T : MaxwellRelation p 1) (δ : ℝ) :
    Set (RealEuclidean (p + 2)) :=
  (((realEuclideanTakeLeftLinearMap p 2) ⁻¹' B ∩
      maxwellFiberPairFirstLinearMap p ⁻¹' R) ∩
      maxwellFiberPairSecondLinearMap p ⁻¹' T) ∩
    maxwellScalarUpwardGapConstraint p δ

/-- Base points carrying the oriented gap encoded by
`maxwellScalarUpwardGapIncidence`. -/
def maxwellScalarUpwardGapBase {p : ℕ}
    (B : Set (RealEuclidean p))
    (R T : MaxwellRelation p 1) (δ : ℝ) :
    Set (RealEuclidean p) :=
  realEuclideanExistentialProjection
    (maxwellScalarUpwardGapIncidence B R T δ)

@[simp]
theorem realEuclideanAppend_mem_maxwellScalarUpwardGapIncidence_iff
    {p : ℕ} (B : Set (RealEuclidean p))
    (R T : MaxwellRelation p 1) (x : RealEuclidean p)
    (v : RealEuclidean 2) (δ : ℝ) :
    realEuclideanAppend x v ∈
        maxwellScalarUpwardGapIncidence B R T δ ↔
      x ∈ B ∧
      realEuclideanAppend x (fun _ : Fin 1 ↦ v 0) ∈ R ∧
      realEuclideanAppend x (fun _ : Fin 1 ↦ v 1) ∈ T ∧
      v 0 + δ < v 1 := by
  simp only [maxwellScalarUpwardGapIncidence, Set.mem_inter_iff,
    Set.mem_preimage,
    realEuclideanTakeLeftLinearMap_apply,
    realEuclideanTakeLeft_append,
    maxwellFiberPairFirstLinearMap_append,
    maxwellFiberPairSecondLinearMap_append,
    realEuclideanAppend_mem_maxwellScalarUpwardGapConstraint_iff]
  constructor <;> intro h
  · rcases h with ⟨⟨⟨hx, hR⟩, hT⟩, hgap⟩
    exact ⟨hx, hR, hT, by linarith⟩
  · rcases h with ⟨hx, hR, hT, hgap⟩
    exact ⟨⟨⟨hx, hR⟩, hT⟩, by linarith⟩

@[simp]
theorem mem_maxwellScalarUpwardGapBase_iff
    {p : ℕ} (B : Set (RealEuclidean p))
    (R T : MaxwellRelation p 1) (δ : ℝ) (x : RealEuclidean p) :
    x ∈ maxwellScalarUpwardGapBase B R T δ ↔
      x ∈ B ∧ ∃ a b : ℝ,
        realEuclideanAppend x (fun _ : Fin 1 ↦ a) ∈ R ∧
        realEuclideanAppend x (fun _ : Fin 1 ↦ b) ∈ T ∧
        a + δ < b := by
  change (∃ v : RealEuclidean 2,
    realEuclideanAppend x v ∈
      maxwellScalarUpwardGapIncidence B R T δ) ↔ _
  simp only [realEuclideanAppend_mem_maxwellScalarUpwardGapIncidence_iff]
  constructor
  · rintro ⟨v, hx, hR, hT, hgap⟩
    exact ⟨hx, v 0, v 1, hR, hT, hgap⟩
  · rintro ⟨hx, a, b, hR, hT, hgap⟩
    exact ⟨![a, b], hx, hR, hT, hgap⟩

theorem maxwellScalarUpwardGapBase_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {B : Set (RealEuclidean p)} {R T : MaxwellRelation p 1}
    (hB : B ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hT : T ∈ charbonnelClosure S (p + 1)) (δ : ℝ) :
    maxwellScalarUpwardGapBase B R T δ ∈
      charbonnelClosure S p := by
  have hbase := hC.linear_preimage_mem (by omega) hp hB
    (realEuclideanTakeLeftLinearMap p 2)
  have hfirst := hC.linear_preimage_mem (by omega) (by omega) hR
    (maxwellFiberPairFirstLinearMap p)
  have hsecond := hC.linear_preimage_mem (by omega) (by omega) hT
    (maxwellFiberPairSecondLinearMap p)
  have hgap : maxwellScalarUpwardGapConstraint p δ ∈
      charbonnelClosure S (p + 2) :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_maxwellScalarUpwardGapConstraint p δ)
  exact charbonnelClosure_projection hp
    (hC.ws1_inter (by omega)
      (hC.ws1_inter (by omega)
        (hC.ws1_inter (by omega) hbase hfirst) hsecond) hgap)

/-! ## Two elementary topological facts used by the source proof -/

/-- An ordinary scalar function graph has empty interior, with no
regularity assumption on the function or its domain. -/
theorem maxwellFunctionGraph_interior_eq_empty
    {p : ℕ} (U : Set (RealEuclidean p))
    (f : RealEuclidean p → RealEuclidean 1) :
    interior (maxwellFunctionGraph U f) = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨z, hz⟩
  let x : RealEuclidean p := realEuclideanTakeLeft z
  let y : RealEuclidean 1 := realEuclideanTakeRight z
  have hcanonical : realEuclideanAppend x y = z := by
    exact realEuclideanAppend_takeLeft_takeRight z
  let vertical : RealEuclidean 1 → RealEuclidean (p + 1) :=
    fun v ↦ realEuclideanAppend x v
  have hvertical : Continuous vertical := by
    apply continuous_pi
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa [vertical, realEuclideanAppend] using
        (continuous_const :
          Continuous (fun _ : RealEuclidean 1 ↦ x j))
    · simpa [vertical, realEuclideanAppend] using continuous_apply j
  let O : Set (RealEuclidean 1) :=
    vertical ⁻¹' interior (maxwellFunctionGraph U f)
  have hOopen : IsOpen O := isOpen_interior.preimage hvertical
  have hyO : y ∈ O := by
    change realEuclideanAppend x y ∈
      interior (maxwellFunctionGraph U f)
    rwa [hcanonical]
  have hyValue : y = f x := by
    have hyGraph : realEuclideanAppend x y ∈
        maxwellFunctionGraph U f := interior_subset hyO
    exact (realEuclideanAppend_mem_maxwellFunctionGraph_iff
      U f x y).mp hyGraph |>.2
  have hOsub : O ⊆ ({y} : Set (RealEuclidean 1)) := by
    intro v hv
    have hvGraph : realEuclideanAppend x v ∈
        maxwellFunctionGraph U f := interior_subset hv
    have hvValue := (realEuclideanAppend_mem_maxwellFunctionGraph_iff
      U f x v).mp hvGraph |>.2
    exact Set.mem_singleton_iff.mpr (hvValue.trans hyValue.symm)
  have hOeq : O = ({y} : Set (RealEuclidean 1)) := by
    apply Set.Subset.antisymm hOsub
    exact Set.singleton_subset_iff.mpr hyO
  have hopenSingleton : IsOpen ({y} : Set (RealEuclidean 1)) := by
    rwa [← hOeq]
  exact (not_isOpen_singleton y) hopenSingleton

/-- Closure-interior regularity promotes the elementary empty-interior fact
for a graph to the same fact for its topological closure. -/
theorem maxwellClosureFunctionGraph_interior_eq_empty_of_closureInteriorRegularity
    {S : EuclideanSetFamily}
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    (hgraph : maxwellFunctionGraph U f ∈
      charbonnelClosure S (p + 1)) :
    interior (closure (maxwellFunctionGraph U f)) = ∅ :=
  hregularity (by omega) hgraph
    (maxwellFunctionGraph_interior_eq_empty U f)

/-- Theorem 2.1 supplies the closure-interior regularity used by the
preceding graph lemma. -/
theorem maxwellClosureFunctionGraph_interior_eq_empty_of_theorem21
    {S : EuclideanSetFamily}
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    (hgraph : maxwellFunctionGraph U f ∈
      charbonnelClosure S (p + 1)) :
    interior (closure (maxwellFunctionGraph U f)) = ∅ := by
  apply maxwellClosureFunctionGraph_interior_eq_empty_of_closureInteriorRegularity
    (S := S) (p := p) ?_ hp hgraph
  intro d hd T hT hTInterior
  exact (h21 hd hT).2.1.mp ((h21 hd hT).1.mp hTInterior)

/-- A reciprocal relation cannot accumulate at reciprocal value zero over
an open set on which the original scalar function is bounded. -/
theorem maxwell_not_mem_zeroReciprocalClosure_of_open_bounded
    {p : ℕ} {U B : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    {H : MaxwellRelation p 1} {x : RealEuclidean p} {M : ℝ}
    (hBopen : IsOpen B) (hxB : x ∈ B) (hM : 0 ≤ M)
    (hbounded : ∀ a ∈ B, |f a 0| ≤ M)
    (hH : ∀ (a : RealEuclidean p) (r : ℝ),
      realEuclideanAppend a (fun _ : Fin 1 ↦ r) ∈ H →
        ∃ y : ℝ,
          realEuclideanAppend a (fun _ : Fin 1 ↦ y) ∈
              maxwellFunctionGraph U f ∧
            y * r = 1) :
    realEuclideanAppend x (0 : RealEuclidean 1) ∉ closure H := by
  intro hxClosure
  let leftMap : RealEuclidean (p + 1) →L[ℝ] RealEuclidean p :=
    realEuclideanTakeLeftContinuousLinearMap p 1
  let rightMap : RealEuclidean (p + 1) →L[ℝ] RealEuclidean 1 :=
    (realEuclideanTakeRightLinearMap p 1).toContinuousLinearMap
  let scalar : RealEuclidean (p + 1) → ℝ :=
    fun z ↦ rightMap z 0
  have hscalar : Continuous scalar :=
    (continuous_apply (0 : Fin 1)).comp rightMap.continuous
  let W : Set (RealEuclidean (p + 1)) :=
    leftMap ⁻¹' B ∩ {z | |scalar z| < (M + 1)⁻¹}
  have hWopen : IsOpen W :=
    (hBopen.preimage leftMap.continuous).inter
      (isOpen_lt hscalar.abs continuous_const)
  have hMone : 0 < M + 1 := by linarith
  have hxW : realEuclideanAppend x (0 : RealEuclidean 1) ∈ W := by
    constructor
    · change realEuclideanTakeLeft
          (realEuclideanAppend x (0 : RealEuclidean 1)) ∈ B
      simpa using hxB
    · change |realEuclideanTakeRight
          (realEuclideanAppend x (0 : RealEuclidean 1)) 0| < (M + 1)⁻¹
      simpa using inv_pos.mpr hMone
  obtain ⟨w, hwW, hwH⟩ :=
    mem_closure_iff.mp hxClosure W hWopen hxW
  let a : RealEuclidean p := realEuclideanTakeLeft w
  let r : ℝ := realEuclideanTakeRight w 0
  have hright : realEuclideanTakeRight w = fun _ : Fin 1 ↦ r := by
    funext i
    exact congrArg (realEuclideanTakeRight w) (Subsingleton.elim i 0)
  have hwCanonical : w = realEuclideanAppend a (fun _ : Fin 1 ↦ r) := by
    calc
      w = realEuclideanAppend (realEuclideanTakeLeft w)
          (realEuclideanTakeRight w) :=
        (realEuclideanAppend_takeLeft_takeRight w).symm
      _ = realEuclideanAppend a (fun _ : Fin 1 ↦ r) := by
        rw [hright]
  have haB : a ∈ B := by
    have hleft := hwW.1
    change leftMap w ∈ B at hleft
    simpa [leftMap, a] using hleft
  have hrSmall : |r| < (M + 1)⁻¹ := by
    have hr := hwW.2
    change |scalar w| < (M + 1)⁻¹ at hr
    simpa [scalar, rightMap, r] using hr
  obtain ⟨y, hyGraph, hyr⟩ := hH a r (by
    rw [← hwCanonical]
    exact hwH)
  have hyValue : y = f a 0 := by
    have hvalue := (realEuclideanAppend_mem_maxwellFunctionGraph_iff
      U f a (fun _ : Fin 1 ↦ y)).mp hyGraph |>.2
    exact congrFun hvalue 0
  have hyBound : |y| ≤ M := by
    rw [hyValue]
    exact hbounded a haB
  have hrne : r ≠ 0 := by
    intro hrzero
    rw [hrzero, mul_zero] at hyr
    norm_num at hyr
  have habsrpos : 0 < |r| := abs_pos.mpr hrne
  have hylt : |y| < M + 1 := lt_of_le_of_lt hyBound (by linarith)
  have hfirst : |y| * |r| < (M + 1) * |r| :=
    mul_lt_mul_of_pos_right hylt habsrpos
  have hsecond : (M + 1) * |r| < (M + 1) * (M + 1)⁻¹ :=
    mul_lt_mul_of_pos_left hrSmall hMone
  have hcancel : (M + 1) * (M + 1)⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hMone)
  have hlt : |y| * |r| < 1 := by linarith
  have habsProduct : |y * r| < 1 := by
    rwa [abs_mul]
  rw [hyr, abs_one] at habsProduct
  exact (lt_irrefl (1 : ℝ)) habsProduct

theorem maxwell_not_mem_positiveInfinityBase_of_open_bounded
    {p : ℕ} {U B : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    {x : RealEuclidean p} {M : ℝ}
    (hBopen : IsOpen B) (hxB : x ∈ B) (hM : 0 ≤ M)
    (hbounded : ∀ a ∈ B, |f a 0| ≤ M) :
    x ∉ maxwellPositiveInfinityBase (maxwellFunctionGraph U f) := by
  exact maxwell_not_mem_zeroReciprocalClosure_of_open_bounded
    hBopen hxB hM hbounded (fun a r har ↦ by
      obtain ⟨y, hy, hyr, _hrpos⟩ :=
        (realEuclideanAppend_scalar_mem_maxwellPositiveReciprocalRelation_iff
          (maxwellFunctionGraph U f) a r).mp har
      exact ⟨y, hy, hyr⟩)

theorem maxwell_not_mem_negativeInfinityBase_of_open_bounded
    {p : ℕ} {U B : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    {x : RealEuclidean p} {M : ℝ}
    (hBopen : IsOpen B) (hxB : x ∈ B) (hM : 0 ≤ M)
    (hbounded : ∀ a ∈ B, |f a 0| ≤ M) :
    x ∉ maxwellNegativeInfinityBase (maxwellFunctionGraph U f) := by
  exact maxwell_not_mem_zeroReciprocalClosure_of_open_bounded
    hBopen hxB hM hbounded (fun a r har ↦ by
      obtain ⟨y, hy, hyr, _hrneg⟩ :=
        (realEuclideanAppend_scalar_mem_maxwellNegativeReciprocalRelation_iff
          (maxwellFunctionGraph U f) a r).mp har
      exact ⟨y, hy, hyr⟩)

/-! ## The two countable exhaustions -/

/-- A countable cover of a nonempty open Euclidean set has a member of
nonzero Lebesgue measure.  No measurability assumption is needed for this
null-set argument. -/
theorem exists_index_volume_ne_zero_of_iUnion_eq_open
    {p : ℕ} (B : Set (RealEuclidean p)) (F : ℕ → Set (RealEuclidean p))
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hUnion : ⋃ n, F n = B) :
    ∃ n, (volume : Measure (RealEuclidean p)) (F n) ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  have hunionNull : (volume : Measure (RealEuclidean p)) (⋃ n, F n) = 0 :=
    measure_iUnion_null hnone
  rw [hUnion] at hunionNull
  exact hBopen.measure_ne_zero
    (volume : Measure (RealEuclidean p)) hBnonempty hunionNull

/-- If a countable family of WS6 sets covers a nonempty open set, one
member has nonempty interior. -/
theorem exists_index_interior_nonempty_of_iUnion_eq_open
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    (B : Set (RealEuclidean p)) (F : ℕ → Set (RealEuclidean p))
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hFmem : ∀ n, F n ∈ charbonnelClosure S p)
    (hUnion : ⋃ n, F n = B) :
    ∃ n, (interior (F n)).Nonempty := by
  by_contra hnone
  have hempty : ∀ n, interior (F n) = ∅ := by
    intro n
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hn
    exact hnone ⟨n, hn⟩
  have hmeagre : IsMeagre B := by
    rw [← hUnion]
    exact isMeagre_iUnion fun n ↦
      hC.isMeagre_of_interior_eq_empty hp (hFmem n) (hempty n)
  exact not_isMeagre_of_isOpen hBopen hBnonempty hmeagre

/-- Extract an actual open ball from a set with nonempty interior. -/
theorem exists_openBall_subset_of_interior_nonempty
    {p : ℕ} {A : Set (RealEuclidean p)}
    (hA : (interior A).Nonempty) :
    ∃ x r, 0 < r ∧ Metric.ball x r ⊆ A := by
  obtain ⟨x, hx⟩ := hA
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp isOpen_interior x hx
  exact ⟨x, r, hr, hball.trans interior_subset⟩

/-- The first source exhaustion: on some smaller family-member open ball,
the scalar function has one uniform absolute bound. -/
theorem exists_openBall_scalarFunction_bounded
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {B U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBmem : B ∈ charbonnelClosure S p) (hBU : B ⊆ U)
    (hgraph : maxwellFunctionGraph U f ∈
      charbonnelClosure S (p + 1)) :
    ∃ (M : ℝ) (W : Set (RealEuclidean p)),
      0 < M ∧ IsOpen W ∧ W.Nonempty ∧ W ⊆ B ∧
      W ∈ charbonnelClosure S p ∧
      ∀ x ∈ W, |f x 0| ≤ M := by
  let F : ℕ → Set (RealEuclidean p) := fun n ↦
    maxwellScalarBoundedValueBase B (maxwellFunctionGraph U f)
      ((n : ℝ) + 1)
  have hFmem : ∀ n, F n ∈ charbonnelClosure S p := by
    intro n
    exact maxwellScalarBoundedValueBase_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hBmem hgraph ((n : ℝ) + 1)
  have hUnion : ⋃ n, F n = B := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
      exact ((mem_maxwellScalarBoundedValueBase_functionGraph_iff
        hBU ((n : ℝ) + 1) x).mp hxn).1
    · intro x hxB
      obtain ⟨n, hn⟩ := exists_nat_gt |f x 0|
      apply Set.mem_iUnion.mpr
      refine ⟨n, (mem_maxwellScalarBoundedValueBase_functionGraph_iff
        hBU ((n : ℝ) + 1) x).mpr ⟨hxB, ?_⟩⟩
      linarith
  obtain ⟨n, hnInterior⟩ :=
    exists_index_interior_nonempty_of_iUnion_eq_open
      hC hp B F hBopen hBnonempty hFmem hUnion
  obtain ⟨x, r, hr, hball⟩ :=
    exists_openBall_subset_of_interior_nonempty hnInterior
  let W : Set (RealEuclidean p) := Metric.ball x r
  have hWopen : IsOpen W := Metric.isOpen_ball
  have hWnonempty : W.Nonempty := ⟨x, Metric.mem_ball_self hr⟩
  have hWmem : W ∈ charbonnelClosure S p :=
    hC.ws2_polynomialSign hp
      (polynomialSignConstructible_ball x hr)
  have hWsubsetB : W ⊆ B := by
    intro u hu
    exact ((mem_maxwellScalarBoundedValueBase_functionGraph_iff
      hBU ((n : ℝ) + 1) u).mp (hball hu)).1
  refine ⟨(n : ℝ) + 1, W, by positivity, hWopen, hWnonempty,
    hWsubsetB, hWmem, ?_⟩
  intro u hu
  exact ((mem_maxwellScalarBoundedValueBase_functionGraph_iff
    hBU ((n : ℝ) + 1) u).mp (hball hu)).2.le

/-- The second source exhaustion: a pointwise strict oriented gap on an
open set can be made uniformly positive on a smaller family-member ball. -/
theorem exists_openBall_uniform_maxwellScalarUpwardGap
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {B : Set (RealEuclidean p)} {R T : MaxwellRelation p 1}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBmem : B ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hT : T ∈ charbonnelClosure S (p + 1))
    (hgap : B ⊆ maxwellScalarUpwardGapBase B R T 0) :
    ∃ (k : ℕ) (W : Set (RealEuclidean p)),
      IsOpen W ∧ W.Nonempty ∧ W ⊆ B ∧
      W ∈ charbonnelClosure S p ∧
      W ⊆ maxwellScalarUpwardGapBase B R T
        (1 / ((k : ℝ) + 1)) := by
  let F : ℕ → Set (RealEuclidean p) := fun k ↦
    maxwellScalarUpwardGapBase B R T (1 / ((k : ℝ) + 1))
  have hFmem : ∀ k, F k ∈ charbonnelClosure S p := by
    intro k
    exact maxwellScalarUpwardGapBase_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hBmem hR hT
        (1 / ((k : ℝ) + 1))
  have hUnion : ⋃ k, F k = B := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hxk⟩
      exact (mem_maxwellScalarUpwardGapBase_iff
        B R T (1 / ((k : ℝ) + 1)) x).mp hxk |>.1
    · intro x hxB
      obtain ⟨_hxB, a, b, ha, hb, hab⟩ :=
        (mem_maxwellScalarUpwardGapBase_iff B R T 0 x).mp (hgap hxB)
      have hdifference : 0 < b - a := by linarith
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hdifference
      apply Set.mem_iUnion.mpr
      refine ⟨k, (mem_maxwellScalarUpwardGapBase_iff
        B R T (1 / ((k : ℝ) + 1)) x).mpr
          ⟨hxB, a, b, ha, hb, ?_⟩⟩
      linarith
  obtain ⟨k, hkInterior⟩ :=
    exists_index_interior_nonempty_of_iUnion_eq_open
      hC hp B F hBopen hBnonempty hFmem hUnion
  obtain ⟨x, r, hr, hball⟩ :=
    exists_openBall_subset_of_interior_nonempty hkInterior
  let W : Set (RealEuclidean p) := Metric.ball x r
  have hWopen : IsOpen W := Metric.isOpen_ball
  have hWnonempty : W.Nonempty := ⟨x, Metric.mem_ball_self hr⟩
  have hWmem : W ∈ charbonnelClosure S p :=
    hC.ws2_polynomialSign hp
      (polynomialSignConstructible_ball x hr)
  have hWsubsetGap : W ⊆ F k := hball
  have hWsubsetB : W ⊆ B := by
    intro u hu
    exact (mem_maxwellScalarUpwardGapBase_iff B R T
      (1 / ((k : ℝ) + 1)) u).mp (hWsubsetGap hu) |>.1
  exact ⟨k, W, hWopen, hWnonempty, hWsubsetB, hWmem,
    hWsubsetGap⟩

/-! ## Finite-fiber and two-piece shrinking helpers -/

/-- At a multivalued scalar fiber, every specified fiber value has a
different companion value. -/
theorem exists_ne_mem_maxwellScalarFiber_of_mem_multivalued
    {p : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p} {z : ℝ}
    (hz : z ∈ maxwellScalarFiber R x)
    (hx : x ∈ maxwellMultivaluedLocus R) :
    ∃ y : ℝ, y ∈ maxwellScalarFiber R x ∧ y ≠ z := by
  obtain ⟨y₁, y₂, hy₁, hy₂, hne⟩ := hx
  have hy₁Fiber : y₁ 0 ∈ maxwellScalarFiber R x := by
    change realEuclideanAppend x (fun _ : Fin 1 ↦ y₁ 0) ∈ R
    change realEuclideanAppend x y₁ ∈ R at hy₁
    rw [← realEuclidean_one_eq_const y₁]
    exact hy₁
  have hy₂Fiber : y₂ 0 ∈ maxwellScalarFiber R x := by
    change realEuclideanAppend x (fun _ : Fin 1 ↦ y₂ 0) ∈ R
    change realEuclideanAppend x y₂ ∈ R at hy₂
    rw [← realEuclidean_one_eq_const y₂]
    exact hy₂
  have hcoordinate : y₁ 0 ≠ y₂ 0 := by
    intro heq
    apply hne
    funext i
    simpa only [show i = 0 from Fin.eq_zero i] using heq
  by_cases hy₁z : y₁ 0 = z
  · refine ⟨y₂ 0, hy₂Fiber, ?_⟩
    intro hy₂z
    exact hcoordinate (hy₁z.trans hy₂z.symm)
  · exact ⟨y₁ 0, hy₁Fiber, hy₁z⟩

/-- The scalar coordinate of a function value gives the corresponding
point of its graph. -/
theorem realEuclideanAppend_scalarFunctionValue_mem_maxwellFunctionGraph
    {p : ℕ} {U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    {x : RealEuclidean p} (hx : x ∈ U) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ f x 0) ∈
      maxwellFunctionGraph U f := by
  apply (realEuclideanAppend_mem_maxwellFunctionGraph_iff
    U f x (fun _ : Fin 1 ↦ f x 0)).mpr
  refine ⟨hx, ?_⟩
  funext i
  rw [show i = 0 from Fin.eq_zero i]

/-- Over a multivalued relation containing the graph of `f`, every base
point lies in either the upward or the downward strict-gap locus. -/
theorem maxwellScalarUpwardGapBase_union_downwardGapBase_eq
    {p : ℕ} {B U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    {R : MaxwellRelation p 1}
    (hBU : B ⊆ U)
    (hgraphSubset : maxwellFunctionGraph U f ⊆ R)
    (hmultivalued : ∀ x ∈ B, x ∈ maxwellMultivaluedLocus R) :
    maxwellScalarUpwardGapBase B (maxwellFunctionGraph U f) R 0 ∪
        maxwellScalarUpwardGapBase B R (maxwellFunctionGraph U f) 0 =
      B := by
  apply Set.Subset.antisymm
  · rintro x (hxUp | hxDown)
    · exact (mem_maxwellScalarUpwardGapBase_iff
        B (maxwellFunctionGraph U f) R 0 x).mp hxUp |>.1
    · exact (mem_maxwellScalarUpwardGapBase_iff
        B R (maxwellFunctionGraph U f) 0 x).mp hxDown |>.1
  · intro x hxB
    have hfGraph :=
      realEuclideanAppend_scalarFunctionValue_mem_maxwellFunctionGraph
        (U := U) (f := f) (hBU hxB : x ∈ U)
    have hfFiber : f x 0 ∈ maxwellScalarFiber R x :=
      hgraphSubset hfGraph
    obtain ⟨y, hyFiber, hyne⟩ :=
      exists_ne_mem_maxwellScalarFiber_of_mem_multivalued
        hfFiber (hmultivalued x hxB)
    rcases lt_or_gt_of_ne hyne with hylt | hygt
    · right
      exact (mem_maxwellScalarUpwardGapBase_iff
        B R (maxwellFunctionGraph U f) 0 x).mpr
          ⟨hxB, y, f x 0, hyFiber, hfGraph, by simpa using hylt⟩
    · left
      exact (mem_maxwellScalarUpwardGapBase_iff
        B (maxwellFunctionGraph U f) R 0 x).mpr
          ⟨hxB, f x 0, y, hfGraph, hyFiber, by simpa using hygt⟩

/-- If two family members cover a nonempty open family member, one of them
contains a smaller nonempty open family-member ball. -/
theorem exists_openBall_subset_left_or_right_of_union_eq_open
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {B A D : Set (RealEuclidean p)}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hA : A ∈ charbonnelClosure S p)
    (hD : D ∈ charbonnelClosure S p)
    (hUnion : A ∪ D = B) :
    (∃ W : Set (RealEuclidean p),
      IsOpen W ∧ W.Nonempty ∧ W ∈ charbonnelClosure S p ∧ W ⊆ A) ∨
    (∃ W : Set (RealEuclidean p),
      IsOpen W ∧ W.Nonempty ∧ W ∈ charbonnelClosure S p ∧ W ⊆ D) := by
  by_cases hAinterior : (interior A).Nonempty
  · obtain ⟨x, r, hr, hball⟩ :=
      exists_openBall_subset_of_interior_nonempty hAinterior
    let W : Set (RealEuclidean p) := Metric.ball x r
    left
    exact ⟨W, Metric.isOpen_ball, ⟨x, Metric.mem_ball_self hr⟩,
      hC.ws2_polynomialSign hp
        (polynomialSignConstructible_ball x hr), hball⟩
  · have hAempty : interior A = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hAinterior
    have hDinterior : (interior D).Nonempty := by
      by_contra hDnone
      have hDempty : interior D = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hDnone
      have hmeagre : IsMeagre B := by
        rw [← hUnion]
        exact (hC.isMeagre_of_interior_eq_empty hp hA hAempty).union
          (hC.isMeagre_of_interior_eq_empty hp hD hDempty)
      exact not_isMeagre_of_isOpen hBopen hBnonempty hmeagre
    obtain ⟨x, r, hr, hball⟩ :=
      exists_openBall_subset_of_interior_nonempty hDinterior
    let W : Set (RealEuclidean p) := Metric.ball x r
    right
    exact ⟨W, Metric.isOpen_ball, ⟨x, Metric.mem_ball_self hr⟩,
      hC.ws2_polynomialSign hp
        (polynomialSignConstructible_ball x hr), hball⟩

/-! ## Bounded exact closure fibers on a bad-locus ball -/

/-- The first half of the source construction: after the bounded-value
exhaustion, the reciprocal alternatives disappear.  Lemma 2.2.1 then
shrinks to a ball on which the closure-graph fibers have one fixed positive
finite cardinality and remain multivalued. -/
theorem exists_open_bounded_exact_multivalued_closureFiber
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S))
    (hcard : MaxwellLocalConstantScalarFiberCardinality
      (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    (hgraph : maxwellFunctionGraph U f ∈
      charbonnelClosure S (p + 1))
    (hinterior :
      (interior (maxwellScalarClosureBadLocus U f)).Nonempty) :
    ∃ (M : ℝ) (k : ℕ) (B : Set (RealEuclidean p)),
      0 < M ∧ IsOpen B ∧ B.Nonempty ∧ B ⊆ U ∧
      B ∈ charbonnelClosure S p ∧
      (∀ x ∈ B, |f x 0| ≤ M) ∧
      (∀ x ∈ B, x ∈ maxwellMultivaluedLocus
        (closure (maxwellFunctionGraph U f))) ∧
      ∀ x ∈ B,
        (maxwellScalarFiber
          (closure (maxwellFunctionGraph U f)) x).Finite ∧
        (maxwellScalarFiber
          (closure (maxwellFunctionGraph U f)) x).ncard = k + 1 := by
  obtain ⟨x₀, r₀, hr₀, hballBad⟩ :=
    exists_openBall_subset_of_interior_nonempty hinterior
  let B₀ : Set (RealEuclidean p) := Metric.ball x₀ r₀
  have hB₀open : IsOpen B₀ := Metric.isOpen_ball
  have hB₀nonempty : B₀.Nonempty :=
    ⟨x₀, Metric.mem_ball_self hr₀⟩
  have hB₀mem : B₀ ∈ charbonnelClosure S p :=
    hC.ws2_polynomialSign hp
      (polynomialSignConstructible_ball x₀ hr₀)
  have hB₀U : B₀ ⊆ U := by
    intro x hx
    exact (hballBad hx).1
  obtain ⟨M, B, hM, hBopen, hBnonempty, hBsubsetB₀,
      hBmem, hbounded⟩ :=
    exists_openBall_scalarFunction_bounded hC hp
      hB₀open hB₀nonempty hB₀mem hB₀U hgraph
  have hBU : B ⊆ U := hBsubsetB₀.trans hB₀U
  have hBbad : B ⊆ maxwellScalarClosureBadLocus U f :=
    hBsubsetB₀.trans hballBad
  have hBmultivalued : ∀ x ∈ B,
      x ∈ maxwellMultivaluedLocus
        (closure (maxwellFunctionGraph U f)) := by
    intro x hxB
    have hxBad := hBbad hxB
    rw [maxwellScalarClosureBadLocus] at hxBad
    rcases hxBad.2 with hxMulti | hxInfinity
    · exact hxMulti
    · have hxNotPositive :=
        maxwell_not_mem_positiveInfinityBase_of_open_bounded
          (U := U) hBopen hxB hM.le hbounded
      have hxNotNegative :=
        maxwell_not_mem_negativeInfinityBase_of_open_bounded
          (U := U) hBopen hxB hM.le hbounded
      rcases hxInfinity with hxPositive | hxNegative
      · exact (hxNotPositive hxPositive).elim
      · exact (hxNotNegative hxNegative).elim
  let R : MaxwellRelation p 1 :=
    closure (maxwellFunctionGraph U f)
  have hRmem : R ∈ charbonnelClosure S (p + 1) :=
    charbonnelClosure_topologicalClosure hgraph
  have hRfull : MaxwellHasFullFibersOver B R := by
    intro x hxB
    refine ⟨f x, subset_closure ?_⟩
    exact (realEuclideanAppend_mem_maxwellFunctionGraph_iff
      U f x (f x)).mpr ⟨hBU hxB, rfl⟩
  have hRinterior : interior R = ∅ :=
    maxwellClosureFunctionGraph_interior_eq_empty_of_closureInteriorRegularity
      hregularity hp hgraph
  have hrestrictInterior :
      interior (maxwellRelationRestrict R B) = ∅ := by
    apply interior_eq_empty_of_subset _ hRinterior
    intro z hz
    exact hz.1
  obtain ⟨k, V, hVopen, hVnonempty, hVsubsetB, hVmem,
      hVfiber⟩ :=
    hcard hp hBopen hBnonempty hBmem hRmem hRfull
      hrestrictInterior
  exact ⟨M, k, V, hM, hVopen, hVnonempty,
    hVsubsetB.trans hBU, hVmem,
    fun x hxV ↦ hbounded x (hVsubsetB hxV),
    fun x hxV ↦ hBmultivalued x (hVsubsetB hxV),
    hVfiber⟩

/-! ## Extremal selectors and uniform escape -/

/-- An upward closure-fiber gap on a bounded exact-cardinality base yields
the upward uniform escape witness used in the final Archimedean
contradiction. -/
theorem exists_maxwellScalarUniformEscapeWitness_of_upwardClosureGap
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U B : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    {M : ℝ} {k : ℕ}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBU : B ⊆ U) (hBmem : B ∈ charbonnelClosure S p)
    (hgraph : maxwellFunctionGraph U f ∈
      charbonnelClosure S (p + 1))
    (hbounded : ∀ x ∈ B, |f x 0| ≤ M)
    (hfiber : ∀ x ∈ B,
      (maxwellScalarFiber
        (closure (maxwellFunctionGraph U f)) x).Finite ∧
      (maxwellScalarFiber
        (closure (maxwellFunctionGraph U f)) x).ncard = k + 1)
    (hup : B ⊆ maxwellScalarUpwardGapBase B
      (maxwellFunctionGraph U f)
      (closure (maxwellFunctionGraph U f)) 0) :
    Nonempty (MaxwellScalarUniformEscapeWitness U f) := by
  let R : MaxwellRelation p 1 :=
    closure (maxwellFunctionGraph U f)
  let g : RealEuclidean p → RealEuclidean 1 :=
    maxwellOrderedScalarMaximumSelector R k
  have hRmem : R ∈ charbonnelClosure S (p + 1) :=
    charbonnelClosure_topologicalClosure hgraph
  have hgmem : maxwellFunctionGraph B g ∈
      charbonnelClosure S (p + 1) :=
    maxwellFunctionGraph_orderedScalarMaximumSelector_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hBmem hRmem hfiber
  have hgsubset : maxwellFunctionGraph B g ⊆ R :=
    maxwellFunctionGraph_orderedScalarMaximumSelector_subset hfiber
  have hselectorGap : B ⊆ maxwellScalarUpwardGapBase B
      (maxwellFunctionGraph U f) (maxwellFunctionGraph B g) 0 := by
    intro x hxB
    obtain ⟨_hxB, a, b, haGraph, hbR, hab⟩ :=
      (mem_maxwellScalarUpwardGapBase_iff B
        (maxwellFunctionGraph U f) R 0 x).mp (hup hxB)
    have haValue : a = f x 0 :=
      congrFun ((realEuclideanAppend_mem_maxwellFunctionGraph_iff
        U f x (fun _ : Fin 1 ↦ a)).mp haGraph).2 0
    have hbFiber : b ∈ maxwellScalarFiber R x := hbR
    have hbMaximum :
        b ≤ maxwellOrderedScalarMaximumValue R k x :=
      le_maxwellOrderedScalarMaximumValue_of_mem
        (hfiber x hxB).1 (hfiber x hxB).2 hbFiber
    have hstrict : f x 0 < g x 0 := by
      rw [haValue] at hab
      dsimp only [g, maxwellOrderedScalarMaximumSelector]
      linarith
    have hfGraph :=
      realEuclideanAppend_scalarFunctionValue_mem_maxwellFunctionGraph
        (U := U) (f := f) (hBU hxB : x ∈ U)
    have hgGraph :=
      realEuclideanAppend_scalarFunctionValue_mem_maxwellFunctionGraph
        (U := B) (f := g) hxB
    exact (mem_maxwellScalarUpwardGapBase_iff B
      (maxwellFunctionGraph U f) (maxwellFunctionGraph B g) 0 x).mpr
        ⟨hxB, f x 0, g x 0, hfGraph, hgGraph, by simpa using hstrict⟩
  obtain ⟨j, W, hWopen, hWnonempty, hWsubsetB, _hWmem,
      hWgap⟩ :=
    exists_openBall_uniform_maxwellScalarUpwardGap
      hC hp hBopen hBnonempty hBmem hgraph hgmem hselectorGap
  refine ⟨{
    B := W
    B_nonempty := hWnonempty
    B_subset := hWsubsetB.trans hBU
    M := M
    bounded := fun x hxW ↦ hbounded x (hWsubsetB hxW)
    delta := 1 / ((j : ℝ) + 1)
    delta_pos := by positivity
    escape := Or.inl ?_
  }⟩
  intro x hxW
  obtain ⟨_hxB, a, b, haGraph, hbGraph, hab⟩ :=
    (mem_maxwellScalarUpwardGapBase_iff B
      (maxwellFunctionGraph U f) (maxwellFunctionGraph B g)
      (1 / ((j : ℝ) + 1)) x).mp (hWgap hxW)
  have haValue : a = f x 0 :=
    congrFun ((realEuclideanAppend_mem_maxwellFunctionGraph_iff
      U f x (fun _ : Fin 1 ↦ a)).mp haGraph).2 0
  have hthreshold : f x 0 + 1 / ((j : ℝ) + 1) < b := by
    rwa [haValue] at hab
  have hbClosure : realEuclideanAppend x (fun _ : Fin 1 ↦ b) ∈
      closure (maxwellFunctionGraph U f) :=
    hgsubset hbGraph
  obtain ⟨u, _huU, huW, huAbove⟩ :=
    exists_functionGraph_value_gt_of_mem_closure
      hWopen hxW hbClosure hthreshold
  exact ⟨u, huW, huAbove.le⟩

/-- The downward counterpart, using the minimum of each exact closure
fiber. -/
theorem exists_maxwellScalarUniformEscapeWitness_of_downwardClosureGap
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {U B : Set (RealEuclidean p)}
    {f : RealEuclidean p → RealEuclidean 1}
    {M : ℝ} {k : ℕ}
    (hBopen : IsOpen B) (hBnonempty : B.Nonempty)
    (hBU : B ⊆ U) (hBmem : B ∈ charbonnelClosure S p)
    (hgraph : maxwellFunctionGraph U f ∈
      charbonnelClosure S (p + 1))
    (hbounded : ∀ x ∈ B, |f x 0| ≤ M)
    (hfiber : ∀ x ∈ B,
      (maxwellScalarFiber
        (closure (maxwellFunctionGraph U f)) x).Finite ∧
      (maxwellScalarFiber
        (closure (maxwellFunctionGraph U f)) x).ncard = k + 1)
    (hdown : B ⊆ maxwellScalarUpwardGapBase B
      (closure (maxwellFunctionGraph U f))
      (maxwellFunctionGraph U f) 0) :
    Nonempty (MaxwellScalarUniformEscapeWitness U f) := by
  let R : MaxwellRelation p 1 :=
    closure (maxwellFunctionGraph U f)
  let g : RealEuclidean p → RealEuclidean 1 :=
    maxwellOrderedScalarSelector R k
  have hRmem : R ∈ charbonnelClosure S (p + 1) :=
    charbonnelClosure_topologicalClosure hgraph
  have hgmem : maxwellFunctionGraph B g ∈
      charbonnelClosure S (p + 1) := by
    rw [← maxwellOrderedScalarSelectionGraph_eq_functionGraph hfiber]
    exact maxwellOrderedScalarSelectionGraph_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hBmem hRmem
  have hgsubset : maxwellFunctionGraph B g ⊆ R := by
    rw [← maxwellOrderedScalarSelectionGraph_eq_functionGraph hfiber]
    exact maxwellOrderedScalarSelectionGraph_subset
  have hselectorGap : B ⊆ maxwellScalarUpwardGapBase B
      (maxwellFunctionGraph B g) (maxwellFunctionGraph U f) 0 := by
    intro x hxB
    obtain ⟨_hxB, a, b, haR, hbGraph, hab⟩ :=
      (mem_maxwellScalarUpwardGapBase_iff B R
        (maxwellFunctionGraph U f) 0 x).mp (hdown hxB)
    have hbValue : b = f x 0 :=
      congrFun ((realEuclideanAppend_mem_maxwellFunctionGraph_iff
        U f x (fun _ : Fin 1 ↦ b)).mp hbGraph).2 0
    have haFiber : a ∈ maxwellScalarFiber R x := haR
    have hminimum : maxwellOrderedScalarValue R k x ≤ a :=
      maxwellOrderedScalarValue_le_of_mem
        (hfiber x hxB).1 (hfiber x hxB).2 haFiber
    have hstrict : g x 0 < f x 0 := by
      rw [hbValue] at hab
      dsimp only [g, maxwellOrderedScalarSelector]
      linarith
    have hgGraph :=
      realEuclideanAppend_scalarFunctionValue_mem_maxwellFunctionGraph
        (U := B) (f := g) hxB
    have hfGraph :=
      realEuclideanAppend_scalarFunctionValue_mem_maxwellFunctionGraph
        (U := U) (f := f) (hBU hxB : x ∈ U)
    exact (mem_maxwellScalarUpwardGapBase_iff B
      (maxwellFunctionGraph B g) (maxwellFunctionGraph U f) 0 x).mpr
        ⟨hxB, g x 0, f x 0, hgGraph, hfGraph, by simpa using hstrict⟩
  obtain ⟨j, W, hWopen, hWnonempty, hWsubsetB, _hWmem,
      hWgap⟩ :=
    exists_openBall_uniform_maxwellScalarUpwardGap
      hC hp hBopen hBnonempty hBmem hgmem hgraph hselectorGap
  refine ⟨{
    B := W
    B_nonempty := hWnonempty
    B_subset := hWsubsetB.trans hBU
    M := M
    bounded := fun x hxW ↦ hbounded x (hWsubsetB hxW)
    delta := 1 / ((j : ℝ) + 1)
    delta_pos := by positivity
    escape := Or.inr ?_
  }⟩
  intro x hxW
  obtain ⟨_hxB, a, b, haGraph, hbGraph, hab⟩ :=
    (mem_maxwellScalarUpwardGapBase_iff B
      (maxwellFunctionGraph B g) (maxwellFunctionGraph U f)
      (1 / ((j : ℝ) + 1)) x).mp (hWgap hxW)
  have hbValue : b = f x 0 :=
    congrFun ((realEuclideanAppend_mem_maxwellFunctionGraph_iff
      U f x (fun _ : Fin 1 ↦ b)).mp hbGraph).2 0
  have hthreshold : a < f x 0 - 1 / ((j : ℝ) + 1) := by
    rw [hbValue] at hab
    linarith
  have haClosure : realEuclideanAppend x (fun _ : Fin 1 ↦ a) ∈
      closure (maxwellFunctionGraph U f) :=
    hgsubset haGraph
  obtain ⟨u, _huU, huW, huBelow⟩ :=
    exists_functionGraph_value_lt_of_mem_closure
      hWopen hxW haClosure hthreshold
  refine ⟨u, huW, ?_⟩
  linarith

/-! ## Assembly of Figueiredo--Maxwell Lemma 2.2.2 -/

/-- The full source construction from the local constant-cardinality input:
bounded-value exhaustion, exclusion of reciprocal infinity, exact finite
closure fibers, the upward/downward split, an extremal selector, and a
uniform positive gap. -/
theorem maxwellScalarClosureBadLocusEscapeSelection_of_localCardinality
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S))
    (hcard : MaxwellLocalConstantScalarFiberCardinality
      (charbonnelClosure S)) :
    MaxwellScalarClosureBadLocusEscapeSelection
      (charbonnelClosure S) := by
  intro p hp U f _hU hgraph hinterior
  obtain ⟨M, k, B, _hM, hBopen, hBnonempty, hBU, hBmem,
      hbounded, hmultivalued, hfiber⟩ :=
    exists_open_bounded_exact_multivalued_closureFiber
      hC hregularity hcard hp hgraph hinterior
  let R : MaxwellRelation p 1 :=
    closure (maxwellFunctionGraph U f)
  have hRmem : R ∈ charbonnelClosure S (p + 1) :=
    charbonnelClosure_topologicalClosure hgraph
  have hcover :
      maxwellScalarUpwardGapBase B (maxwellFunctionGraph U f) R 0 ∪
          maxwellScalarUpwardGapBase B R (maxwellFunctionGraph U f) 0 =
        B :=
    maxwellScalarUpwardGapBase_union_downwardGapBase_eq
      hBU subset_closure hmultivalued
  have hupMem : maxwellScalarUpwardGapBase B
      (maxwellFunctionGraph U f) R 0 ∈ charbonnelClosure S p :=
    maxwellScalarUpwardGapBase_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hBmem hgraph hRmem 0
  have hdownMem : maxwellScalarUpwardGapBase B R
      (maxwellFunctionGraph U f) 0 ∈ charbonnelClosure S p :=
    maxwellScalarUpwardGapBase_mem_charbonnelClosure
      hC.toPositiveArityWeakSetStructure hp hBmem hRmem hgraph 0
  rcases exists_openBall_subset_left_or_right_of_union_eq_open
      hC hp hBopen hBnonempty hupMem hdownMem hcover with
    ⟨W, hWopen, hWnonempty, hWmem, hWup⟩ |
      ⟨W, hWopen, hWnonempty, hWmem, hWdown⟩
  · have hWsubsetB : W ⊆ B := by
      intro x hxW
      exact (mem_maxwellScalarUpwardGapBase_iff B
        (maxwellFunctionGraph U f) R 0 x).mp (hWup hxW) |>.1
    have hWgap : W ⊆ maxwellScalarUpwardGapBase W
        (maxwellFunctionGraph U f) R 0 := by
      intro x hxW
      obtain ⟨_hxB, a, b, ha, hb, hab⟩ :=
        (mem_maxwellScalarUpwardGapBase_iff B
          (maxwellFunctionGraph U f) R 0 x).mp (hWup hxW)
      exact (mem_maxwellScalarUpwardGapBase_iff W
        (maxwellFunctionGraph U f) R 0 x).mpr
          ⟨hxW, a, b, ha, hb, hab⟩
    exact exists_maxwellScalarUniformEscapeWitness_of_upwardClosureGap
      hC hp hWopen hWnonempty (hWsubsetB.trans hBU) hWmem
      hgraph (fun x hxW ↦ hbounded x (hWsubsetB hxW))
      (fun x hxW ↦ hfiber x (hWsubsetB hxW)) hWgap
  · have hWsubsetB : W ⊆ B := by
      intro x hxW
      exact (mem_maxwellScalarUpwardGapBase_iff B R
        (maxwellFunctionGraph U f) 0 x).mp (hWdown hxW) |>.1
    have hWgap : W ⊆ maxwellScalarUpwardGapBase W R
        (maxwellFunctionGraph U f) 0 := by
      intro x hxW
      obtain ⟨_hxB, a, b, ha, hb, hab⟩ :=
        (mem_maxwellScalarUpwardGapBase_iff B R
          (maxwellFunctionGraph U f) 0 x).mp (hWdown hxW)
      exact (mem_maxwellScalarUpwardGapBase_iff W R
        (maxwellFunctionGraph U f) 0 x).mpr
          ⟨hxW, a, b, ha, hb, hab⟩
    exact exists_maxwellScalarUniformEscapeWitness_of_downwardClosureGap
      hC hp hWopen hWnonempty (hWsubsetB.trans hBU) hWmem
      hgraph (fun x hxW ↦ hbounded x (hWsubsetB hxW))
      (fun x hxW ↦ hfiber x (hWsubsetB hxW)) hWgap

/-- Lemma 2.2.2's escape-selection step from the weak o-minimal structure
and Theorem 2.1 alone; Lemma 2.2.1 is instantiated internally. -/
theorem maxwellScalarClosureBadLocusEscapeSelection_of_theorem21
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S)) :
    MaxwellScalarClosureBadLocusEscapeSelection
      (charbonnelClosure S) := by
  have hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S) := by
    intro d hd T hT hTInterior
    exact (h21 hd hT).2.1.mp ((h21 hd hT).1.mp hTInterior)
  intro p hp U f hU hgraph hinterior
  exact
    (maxwellScalarClosureBadLocusEscapeSelection_of_localCardinality
      (S := S) hC hregularity
      (maxwellLocalConstantScalarFiberCardinality_of_closureInteriorRegularity
        (S := S) hC hregularity))
      hp U f hU hgraph hinterior

/-- WS5, WS6, and closure-interior regularity suffice for the complete
scalar discontinuity-control theorem. -/
theorem maxwellScalarDiscontinuityControl_of_closureInteriorRegularity
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S)) :
    MaxwellScalarDiscontinuityControl (charbonnelClosure S) :=
  maxwellScalarDiscontinuityControl_of_escapeSelection
    hC.toPositiveArityWeakSetStructure
    (maxwellScalarClosureBadLocusEscapeSelection_of_localCardinality
      hC hregularity
      (maxwellLocalConstantScalarFiberCardinality_of_closureInteriorRegularity
        hC hregularity))

/-- End-to-end scalar discontinuity control, with the metric sequence split
and both source lemmas now instantiated. -/
theorem maxwellScalarDiscontinuityControl_of_theorem21
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S)) :
    MaxwellScalarDiscontinuityControl (charbonnelClosure S) := by
  have hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S) := by
    intro d hd T hT hTInterior
    exact (h21 hd hT).2.1.mp ((h21 hd hT).1.mp hTInterior)
  intro p hp U f hU hgraph
  exact
    (maxwellScalarDiscontinuityControl_of_closureInteriorRegularity
      (S := S) hC hregularity) hp U f hU hgraph

/-- Closure-interior regularity, together with WS5 and WS6, supplies all
inputs to Maxwell's continuous weak-selection theorem. -/
theorem maxwellContinuousWeakSelection_of_closureInteriorRegularity
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure S)) :
    MaxwellContinuousWeakSelection (charbonnelClosure S) :=
  maxwellContinuousWeakSelection_of_sourceInputs
    hC.toPositiveArityWeakSetStructure hregularity
    (maxwellLocalConstantScalarFiberCardinality_of_closureInteriorRegularity
      hC hregularity)
    (maxwellScalarDiscontinuityControl_of_closureInteriorRegularity
      hC hregularity)

/-- Figueiredo--Maxwell Lemma 2.3.1 with both scalar source lemmas
instantiated internally.  Theorem 2.1 supplies the closure-interior
regularity used when the finitely many coordinate discontinuity loci are
removed. -/
theorem maxwellContinuousWeakSelection_of_theorem21
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S)) :
    MaxwellContinuousWeakSelection (charbonnelClosure S) := by
  have hregularity :
      CharbonnelClosureInteriorRegularity (charbonnelClosure S) := by
    intro d hd T hT hTInterior
    have hTNull :
        (volume : Measure (RealEuclidean d)) T = 0 :=
      (h21 hd hT).1.mp hTInterior
    exact (h21 hd hT).2.1.mp hTNull
  intro p q hp hq B R hBopen hBnonempty hBmem hRmem hfull
  exact (maxwellContinuousWeakSelection_of_closureInteriorRegularity
    hC hregularity)
      hp hq hBopen hBnonempty hBmem hRmem hfull

end AbelFormalization
