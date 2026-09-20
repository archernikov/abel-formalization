import AbelFormalization.MaxwellDifferenceQuotientTraceTopology
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Exact zero-step traces for C1 scalar graphs

Figueiredo's Lemma 2.3.9 identifies the zero-step difference-quotient
relation of a continuously differentiable function with the graph of the
corresponding partial derivative.  The earlier topology module proves one
inclusion, namely that a derivative value belongs to the trace.  This file
proves the converse from strict differentiability, then obtains the source
statement from continuity of the Frechet derivative.

The equality is stated after restricting the base to the open domain.  This
is necessary for the present relation-level definitions: closing the quotient
relation can add points over the boundary of the domain, where no derivative
has been prescribed.
-/

noncomputable section

open Set Filter Asymptotics
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- Strict differentiability forces every finite zero-step quotient value at
an interior base point to equal the directional derivative there.  This is
the reverse-inclusion argument in Figueiredo Lemma 2.3.9, expressed without
the source's mean-value intermediate point. -/
theorem maxwellDifferenceQuotientZeroTrace_functionGraph_value_eq_of_hasStrictFDerivAt
    {p : ℕ} {U : Set (RealEuclidean p)}
    {x : RealEuclidean p} {f : RealEuclidean p → ℝ}
    {f' : RealEuclidean p →L[ℝ] ℝ} (i : Fin p) (y : ℝ)
    (hf : HasStrictFDerivAt f f' x)
    (hy : realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
      maxwellDifferenceQuotientZeroTrace U
        (maxwellFunctionGraph U (fun u _ ↦ f u)) i) :
    y = f' (Pi.single i 1 : RealEuclidean p) := by
  let v : RealEuclidean p := Pi.single i 1
  have hyClosure :
      realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ 0))
          (fun _ : Fin 1 ↦ y) ∈
        closure (maxwellDifferenceQuotientRelation U
          (maxwellFunctionGraph U (fun u _ ↦ f u)) i) :=
    (realEuclideanAppend_scalar_mem_maxwellDifferenceQuotientZeroTrace_iff
      U (maxwellFunctionGraph U (fun u _ ↦ f u)) i x y).mp hy
  obtain ⟨w, hwQuotient, hwLimit⟩ :=
    mem_closure_iff_seq_limit.mp hyClosure

  let xepsilon : ℕ → RealEuclidean (p + 1) :=
    fun n ↦ realEuclideanTakeLeft (w n)
  let xseq : ℕ → RealEuclidean p :=
    fun n ↦ realEuclideanTakeLeft (xepsilon n)
  let epsilon : ℕ → ℝ :=
    fun n ↦ realEuclideanTakeRight (xepsilon n) 0
  let slope : ℕ → ℝ :=
    fun n ↦ realEuclideanTakeRight (w n) 0

  have hxepsilonSplit : ∀ n,
      xepsilon n = realEuclideanAppend (xseq n)
        (fun _ : Fin 1 ↦ epsilon n) := by
    intro n
    calc
      xepsilon n = realEuclideanAppend
          (realEuclideanTakeLeft (xepsilon n))
          (realEuclideanTakeRight (xepsilon n)) :=
        (realEuclideanAppend_takeLeft_takeRight (xepsilon n)).symm
      _ = realEuclideanAppend (xseq n)
          (fun _ : Fin 1 ↦ epsilon n) := by
        congr 1
        funext j
        rw [show j = 0 from Fin.eq_zero j]

  have hwSplit : ∀ n,
      w n = realEuclideanAppend
        (realEuclideanAppend (xseq n) (fun _ : Fin 1 ↦ epsilon n))
        (fun _ : Fin 1 ↦ slope n) := by
    intro n
    calc
      w n = realEuclideanAppend
          (realEuclideanTakeLeft (w n))
          (realEuclideanTakeRight (w n)) :=
        (realEuclideanAppend_takeLeft_takeRight (w n)).symm
      _ = realEuclideanAppend (xepsilon n)
          (fun _ : Fin 1 ↦ slope n) := by
        congr 1
        funext j
        rw [show j = 0 from Fin.eq_zero j]
      _ = realEuclideanAppend
          (realEuclideanAppend (xseq n) (fun _ : Fin 1 ↦ epsilon n))
          (fun _ : Fin 1 ↦ slope n) := by
        rw [hxepsilonSplit n]

  have hquotient : ∀ n,
      xseq n ∈ U ∧
      xseq n + epsilon n • v ∈ U ∧
      epsilon n ≠ 0 ∧
      epsilon n * slope n =
        f (xseq n + epsilon n • v) - f (xseq n) := by
    intro n
    have hn := hwQuotient n
    rw [hwSplit n,
      realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_functionGraph_iff]
      at hn
    simpa only [v] using hn

  let outerLeft :
      RealEuclidean ((p + 1) + 1) →L[ℝ] RealEuclidean (p + 1) :=
    (realEuclideanTakeLeftLinearMap (p + 1) 1).toContinuousLinearMap
  let outerRight :
      RealEuclidean ((p + 1) + 1) →L[ℝ] RealEuclidean 1 :=
    (realEuclideanTakeRightLinearMap (p + 1) 1).toContinuousLinearMap
  let innerLeft : RealEuclidean (p + 1) →L[ℝ] RealEuclidean p :=
    (realEuclideanTakeLeftLinearMap p 1).toContinuousLinearMap
  let innerRight : RealEuclidean (p + 1) →L[ℝ] RealEuclidean 1 :=
    (realEuclideanTakeRightLinearMap p 1).toContinuousLinearMap

  have hxepsilonLimit :
      Tendsto xepsilon atTop
        (nhds (realEuclideanAppend x (fun _ : Fin 1 ↦ 0))) := by
    have h := (outerLeft.continuous.tendsto _).comp hwLimit
    simpa [outerLeft, xepsilon, Function.comp_def] using h
  have hxseqLimit : Tendsto xseq atTop (nhds x) := by
    have h := (innerLeft.continuous.tendsto _).comp hxepsilonLimit
    simpa [innerLeft, xseq, Function.comp_def] using h
  have hepsilonVectorLimit :
      Tendsto (fun n ↦ realEuclideanTakeRight (xepsilon n)) atTop
        (nhds (fun _ : Fin 1 ↦ 0)) := by
    have h := (innerRight.continuous.tendsto _).comp hxepsilonLimit
    simpa [innerRight, Function.comp_def] using h
  have hepsilonLimit : Tendsto epsilon atTop (nhds 0) := by
    have h := tendsto_pi_nhds.mp hepsilonVectorLimit 0
    simpa [epsilon] using h
  have hslopeVectorLimit :
      Tendsto (fun n ↦ realEuclideanTakeRight (w n)) atTop
        (nhds (fun _ : Fin 1 ↦ y)) := by
    have h := (outerRight.continuous.tendsto _).comp hwLimit
    simpa [outerRight, Function.comp_def] using h
  have hslopeLimit : Tendsto slope atTop (nhds y) := by
    have h := tendsto_pi_nhds.mp hslopeVectorLimit 0
    simpa [slope] using h

  have hshiftLimit :
      Tendsto (fun n ↦ xseq n + epsilon n • v) atTop (nhds x) := by
    simpa using hxseqLimit.add
      (hepsilonLimit.smul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ v) atTop (nhds v)))
  have hpairLimit :
      Tendsto (fun n ↦
        (xseq n + epsilon n • v, xseq n)) atTop (nhds (x, x)) :=
    hshiftLimit.prodMk_nhds hxseqLimit

  let residual : ℕ → ℝ := fun n ↦
    f (xseq n + epsilon n • v) - f (xseq n) -
      f' ((xseq n + epsilon n • v) - xseq n)
  have hresidualLittleO :
      residual =o[atTop]
        (fun n ↦ (xseq n + epsilon n • v) - xseq n) := by
    simpa [residual, Function.comp_def] using
      hf.isLittleO.comp_tendsto hpairLimit
  have hdisplacementNorm : ∀ n,
      ‖(xseq n + epsilon n • v) - xseq n‖ = ‖epsilon n‖ := by
    intro n
    rw [add_sub_cancel_left, norm_smul, Pi.norm_single, norm_one, mul_one]
  have hresidualLittleOScalar : residual =o[atTop] epsilon := by
    apply IsLittleO.of_norm_right
    exact hresidualLittleO.norm_right.congr_right hdisplacementNorm
  have hresidualRatioLimit :
      Tendsto (fun n ↦ residual n / epsilon n) atTop (nhds 0) :=
    hresidualLittleOScalar.tendsto_div_nhds_zero

  have hratioEq : ∀ n,
      residual n / epsilon n = slope n - f' v := by
    intro n
    have heq := (hquotient n).2.2.2
    have hne := (hquotient n).2.2.1
    have hdisplacement :
        (xseq n + epsilon n • v) - xseq n = epsilon n • v := by
      abel
    dsimp [residual]
    rw [hdisplacement, map_smul, ← heq]
    simp only [smul_eq_mul]
    rw [← mul_sub, mul_div_cancel_left₀ _ hne]
  have hslopeSubLimit :
      Tendsto (fun n ↦ slope n - f' v) atTop (nhds 0) :=
    hresidualRatioLimit.congr'
      (Eventually.of_forall hratioEq)
  have hslopeSubValue :
      Tendsto (fun n ↦ slope n - f' v) atTop (nhds (y - f' v)) :=
    hslopeLimit.sub_const (f' v)
  have hzero : y - f' v = 0 :=
    tendsto_nhds_unique hslopeSubValue hslopeSubLimit
  exact sub_eq_zero.mp hzero

/-- On an open domain, a strictly differentiable scalar function has an
exact, single-valued coordinate zero-step trace over that domain. -/
theorem maxwellDifferenceQuotientZeroTrace_functionGraph_representsOn_of_hasStrictFDerivAt
    {p : ℕ} {U : Set (RealEuclidean p)} (hU : IsOpen U)
    {f : RealEuclidean p → ℝ}
    {f' : RealEuclidean p → RealEuclidean p →L[ℝ] ℝ}
    (hstrict : ∀ x ∈ U, HasStrictFDerivAt f (f' x) x)
    (i : Fin p) :
    MaxwellRelation.RepresentsOn
      (maxwellDifferenceQuotientZeroTrace U
        (maxwellFunctionGraph U (fun u _ ↦ f u)) i)
      U (fun x _ ↦ f' x (Pi.single i 1 : RealEuclidean p)) := by
  intro x hx y
  let value : ℝ := y 0
  have hyValue : y = fun _ : Fin 1 ↦ value := by
    funext j
    rw [show j = 0 from Fin.eq_zero j]
  rw [hyValue]
  constructor
  · intro hy
    have hvalue :=
      maxwellDifferenceQuotientZeroTrace_functionGraph_value_eq_of_hasStrictFDerivAt
        i value (hstrict x hx) hy
    funext j
    simpa [value] using hvalue
  · intro hy
    have hvalue : value = f' x (Pi.single i 1 : RealEuclidean p) := by
      simpa [value] using congrFun hy 0
    rw [hvalue]
    have hfd : fderiv ℝ f x = f' x :=
      (hstrict x hx).hasFDerivAt.fderiv
    simpa only [hfd] using
      (maxwellDifferenceQuotientZeroTrace_functionGraph_fderiv_mem
        hU hx f i (hstrict x hx).differentiableAt)

/-- Figueiredo Lemma 2.3.9 in the project's relation language: if the
Frechet derivative exists on an open set and varies continuously there, the
coordinate zero-step trace represents the corresponding partial derivative. -/
theorem maxwellDifferenceQuotientZeroTrace_functionGraph_representsOn_of_continuous_fderiv
    {p : ℕ} {U : Set (RealEuclidean p)} (hU : IsOpen U)
    {f : RealEuclidean p → ℝ}
    {f' : RealEuclidean p → RealEuclidean p →L[ℝ] ℝ}
    (hder : ∀ x ∈ U, HasFDerivAt f (f' x) x)
    (hcont : ContinuousOn f' U) (i : Fin p) :
    MaxwellRelation.RepresentsOn
      (maxwellDifferenceQuotientZeroTrace U
      (maxwellFunctionGraph U (fun u _ ↦ f u)) i)
      U (fun x _ ↦ f' x (Pi.single i 1 : RealEuclidean p)) := by
  refine
    maxwellDifferenceQuotientZeroTrace_functionGraph_representsOn_of_hasStrictFDerivAt
      hU (f' := f') ?_ i
  intro x hx
  refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt ?_
    ((hcont x hx).continuousAt (hU.mem_nhds hx))
  filter_upwards [hU.mem_nhds hx] with z hz
  exact hder z hz

/-- Equality form of Lemma 2.3.9.  Restricting the trace to `U` discards
possible boundary fibers introduced by taking the ambient closure. -/
theorem maxwellRelationRestrict_differenceQuotientZeroTrace_functionGraph_eq_of_continuous_fderiv
    {p : ℕ} {U : Set (RealEuclidean p)} (hU : IsOpen U)
    {f : RealEuclidean p → ℝ}
    {f' : RealEuclidean p → RealEuclidean p →L[ℝ] ℝ}
    (hder : ∀ x ∈ U, HasFDerivAt f (f' x) x)
    (hcont : ContinuousOn f' U) (i : Fin p) :
    maxwellRelationRestrict
        (maxwellDifferenceQuotientZeroTrace U
          (maxwellFunctionGraph U (fun u _ ↦ f u)) i) U =
      maxwellFunctionGraph U
        (fun x _ ↦ f' x (Pi.single i 1 : RealEuclidean p)) := by
  let trace := maxwellDifferenceQuotientZeroTrace U
    (maxwellFunctionGraph U (fun u _ ↦ f u)) i
  let derivativeGraph : RealEuclidean p → RealEuclidean 1 :=
    fun x _ ↦ f' x (Pi.single i 1 : RealEuclidean p)
  have hrep : MaxwellRelation.RepresentsOn trace U derivativeGraph :=
    maxwellDifferenceQuotientZeroTrace_functionGraph_representsOn_of_continuous_fderiv
      hU hder hcont i
  ext z
  let x : RealEuclidean p := realEuclideanTakeLeft z
  let y : RealEuclidean 1 := realEuclideanTakeRight z
  have hz : z = realEuclideanAppend x y :=
    (realEuclideanAppend_takeLeft_takeRight z).symm
  rw [hz,
    realEuclideanAppend_mem_maxwellRelationRestrict_iff,
    realEuclideanAppend_mem_maxwellFunctionGraph_iff]
  constructor
  · rintro ⟨hyTrace, hx⟩
    exact ⟨hx, (hrep x hx y).mp hyTrace⟩
  · rintro ⟨hx, hy⟩
    exact ⟨(hrep x hx y).mpr hy, hx⟩

end AbelFormalization
