import AbelFormalization.MaxwellOneSidedExtendedIVT
import AbelFormalization.MaxwellChosenInfinitySmallness
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Localized one-sided IVT for Maxwell slopes

The source one-sided slope traces are formed from an arbitrary open domain
`U`.  Their interval-filling argument only uses continuity in a neighborhood
of the base point.  This file records that local form and applies it on the
open complement of the canonical selector's continuity obstruction.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Topology MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Pointwise localization -/

/-- Read a one-sided quotient value from the original-domain relation when
both endpoints lie in a smaller domain on which the relation represents a
function. -/
theorem maxwellOneSidedStepLast_value_eq_of_representsOn_subdomain
    {p : ℕ} {U V : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {f : RealEuclidean p → ℝ}
    (i : Fin p) (side : MaxwellOneSidedStep)
    (hrep : MaxwellRelation.RepresentsOn R V (fun z _ ↦ f z))
    (x : RealEuclidean p) (t y : ℝ)
    (hsourceV : (x, t) ∈ maxwellOneSidedStepDomain V i side)
    (hw : realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
        (fun _ : Fin 1 ↦ side.sign * t) ∈
      maxwellStepLastDifferenceQuotientRelation U R i) :
    y = maxwellOneSidedDifferenceQuotient f i side (x, t) := by
  have hwQuotientU :=
    (mem_maxwellStepLastDifferenceQuotientRelation_append_iff
      U R i x (fun _ : Fin 1 ↦ y)
        (fun _ : Fin 1 ↦ side.sign * t)).mp hw
  have hwRawU :=
    (realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff
      U R i x (side.sign * t) y).mp hwQuotientU
  have hwRawV :
      realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ side.sign * t))
          (fun _ : Fin 1 ↦ y) ∈
        maxwellDifferenceQuotientRelation V R i := by
    apply (realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff
      V R i x (side.sign * t) y).mpr
    exact ⟨hsourceV.1, hsourceV.2.1,
      hwRawU.2.2.1, hwRawU.2.2.2⟩
  have hwV : realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
        (fun _ : Fin 1 ↦ side.sign * t) ∈
      maxwellStepLastDifferenceQuotientRelation V R i :=
    (mem_maxwellStepLastDifferenceQuotientRelation_append_iff
      V R i x (fun _ : Fin 1 ↦ y)
        (fun _ : Fin 1 ↦ side.sign * t)).mpr hwRawV
  exact
    ((realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_oneSided_of_representsOn_iff
      i hrep side x t y).mp ⟨hwV, hsourceV.2.2⟩).2

/-- Conversely, a quotient equation over the smaller represented domain
gives a point of the original-domain quotient relation. -/
theorem maxwellOneSidedStepLast_mem_of_representsOn_subdomain
    {p : ℕ} {U V : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {f : RealEuclidean p → ℝ}
    (i : Fin p) (side : MaxwellOneSidedStep)
    (hVU : V ⊆ U)
    (hrep : MaxwellRelation.RepresentsOn R V (fun z _ ↦ f z))
    (x : RealEuclidean p) (t y : ℝ)
    (hsourceV : (x, t) ∈ maxwellOneSidedStepDomain V i side)
    (hy : y = maxwellOneSidedDifferenceQuotient f i side (x, t)) :
    realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ y))
          (fun _ : Fin 1 ↦ side.sign * t) ∈
        maxwellStepLastDifferenceQuotientRelation U R i ∧ 0 < t := by
  have hwV :=
    (realEuclideanAppend_append_mem_maxwellStepLastDifferenceQuotientRelation_oneSided_of_representsOn_iff
      i hrep side x t y).mpr ⟨hsourceV, hy⟩
  have hwQuotientV :=
    (mem_maxwellStepLastDifferenceQuotientRelation_append_iff
      V R i x (fun _ : Fin 1 ↦ y)
        (fun _ : Fin 1 ↦ side.sign * t)).mp hwV.1
  have hwRawV :=
    (realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff
      V R i x (side.sign * t) y).mp hwQuotientV
  have hwRawU :
      realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ side.sign * t))
          (fun _ : Fin 1 ↦ y) ∈
        maxwellDifferenceQuotientRelation U R i := by
    apply (realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff
      U R i x (side.sign * t) y).mpr
    exact ⟨hVU hwRawV.1, hVU hwRawV.2.1,
      hwRawV.2.2.1, hwRawV.2.2.2⟩
  exact ⟨
    (mem_maxwellStepLastDifferenceQuotientRelation_append_iff
      U R i x (fun _ : Fin 1 ↦ y)
        (fun _ : Fin 1 ↦ side.sign * t)).mpr hwRawU,
    hwV.2⟩

/-- Finite one-sided cluster values satisfy the interval property whenever
the represented function is continuous on an open neighborhood `V` of the
base point contained in the original quotient domain `U`. -/
theorem maxwellOneSidedStepZeroTrace_interval_pointwise_of_continuousOn_neighborhood
    {p : ℕ} {U V : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {f : RealEuclidean p → ℝ}
    (i : Fin p) (side : MaxwellOneSidedStep)
    (hVopen : IsOpen V) (hVU : V ⊆ U) (hf : ContinuousOn f V)
    (hrep : MaxwellRelation.RepresentsOn R V (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ V)
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
  obtain ⟨rho, hrho, hballV⟩ := Metric.isOpen_iff.mp hVopen x hx
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
    symm
    apply maxwellOneSidedStepLast_value_eq_of_representsOn_subdomain
      i side hrep (sourceA n).1 (sourceA n).2
        (maxwellStepLastValue (hA.point (n + N)))
        (maxwellOneSidedStepCore_subset_domain hballV
          (hsourceAcore n))
    change realEuclideanAppend
        (realEuclideanAppend (maxwellStepLastBase (hA.point (n + N)))
          (fun _ : Fin 1 ↦ maxwellStepLastValue (hA.point (n + N))))
        (fun _ : Fin 1 ↦ side.sign *
          (side.sign * maxwellStepLastStep (hA.point (n + N)))) ∈ _
    rw [← mul_assoc, side.sign_mul_self, one_mul,
      realEuclideanAppend_stepLastCoordinates]
    exact hA.point_mem (n + N)
  have hsourceBValue (n : ℕ) :
      maxwellOneSidedDifferenceQuotient f i side (sourceB n) =
        maxwellStepLastValue (hB.point (n + N)) := by
    symm
    apply maxwellOneSidedStepLast_value_eq_of_representsOn_subdomain
      i side hrep (sourceB n).1 (sourceB n).2
        (maxwellStepLastValue (hB.point (n + N)))
        (maxwellOneSidedStepCore_subset_domain hballV
          (hsourceBcore n))
    change realEuclideanAppend
        (realEuclideanAppend (maxwellStepLastBase (hB.point (n + N)))
          (fun _ : Fin 1 ↦ maxwellStepLastValue (hB.point (n + N))))
        (fun _ : Fin 1 ↦ side.sign *
          (side.sign * maxwellStepLastStep (hB.point (n + N)))) ∈ _
    rw [← mul_assoc, side.sign_mul_self, one_mul,
      realEuclideanAppend_stepLastCoordinates]
    exact hB.point_mem (n + N)
  have hbetween (n : ℕ) : y ∈ Set.Icc
      (maxwellOneSidedDifferenceQuotient f i side (sourceA n))
      (maxwellOneSidedDifferenceQuotient f i side (sourceB n)) := by
    rw [hsourceAValue n, hsourceBValue n]
    exact ⟨le_of_lt (htail n).2.2.1, le_of_lt (htail n).2.2.2⟩
  have hcontinuous :=
    continuousOn_maxwellOneSidedDifferenceQuotient_stepCore
      i side hf hballV
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
    exact maxwellOneSidedStepLast_mem_of_representsOn_subdomain
      i side hVU hrep (sourceY n).1 (sourceY n).2 y
      (maxwellOneSidedStepCore_subset_domain hballV
        (hsourceYcore n)) (hsourceYValue n)
  have hsourceAtendsto : Tendsto sourceA atTop (nhds (x, 0)) := by
    simpa only [sourceA, Function.comp_def] using
      hA.source_tendsto.comp (tendsto_add_atTop_nat N)
  have hsourceBtendsto : Tendsto sourceB atTop (nhds (x, 0)) := by
    simpa only [sourceB, Function.comp_def] using
      hB.source_tendsto.comp (tendsto_add_atTop_nat N)
  have hsourceYtendsto : Tendsto sourceY atTop (nhds (x, 0)) :=
    tendsto_variable_lineMap hsourceAtendsto hsourceBtendsto htheta
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

/-- The shrinking-core straddling argument likewise needs continuity only on
an open neighborhood of the common limiting base point. -/
theorem maxwellOneSidedStepZeroTrace_mem_of_straddling_sources_neighborhood
    {p : ℕ} {U V : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {f : RealEuclidean p → ℝ}
    (i : Fin p) (side : MaxwellOneSidedStep)
    (hVopen : IsOpen V) (hVU : V ⊆ U) (hf : ContinuousOn f V)
    (hrep : MaxwellRelation.RepresentsOn R V (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ V) {y : ℝ}
    {sourceLow sourceHigh : ℕ → RealEuclidean p × ℝ}
    {valueLow valueHigh : ℕ → ℝ}
    (hsourceLow : Tendsto sourceLow atTop (nhds (x, 0)))
    (hsourceHigh : Tendsto sourceHigh atTop (nhds (x, 0)))
    (hstepLow : ∀ n, 0 < (sourceLow n).2)
    (hstepHigh : ∀ n, 0 < (sourceHigh n).2)
    (hLow : ∀ n,
      realEuclideanAppend
          (realEuclideanAppend (sourceLow n).1
            (fun _ : Fin 1 ↦ valueLow n))
          (fun _ : Fin 1 ↦ side.sign * (sourceLow n).2) ∈
        maxwellStepLastDifferenceQuotientRelation U R i)
    (hHigh : ∀ n,
      realEuclideanAppend
          (realEuclideanAppend (sourceHigh n).1
            (fun _ : Fin 1 ↦ valueHigh n))
          (fun _ : Fin 1 ↦ side.sign * (sourceHigh n).2) ∈
        maxwellStepLastDifferenceQuotientRelation U R i)
    (hstraddle : ∀ᶠ n in atTop, valueLow n < y ∧ y < valueHigh n) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
      maxwellOneSidedStepZeroTrace U R i side := by
  obtain ⟨rho, hrho, hballV⟩ := Metric.isOpen_iff.mp hVopen x hx
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
        valueLow (n + N) := by
    exact (maxwellOneSidedStepLast_value_eq_of_representsOn_subdomain
      i side hrep (low n).1 (low n).2 (valueLow (n + N))
      (maxwellOneSidedStepCore_subset_domain hballV (hlowCore n))
      (hLow (n + N))).symm
  have hhighValue (n : ℕ) :
      maxwellOneSidedDifferenceQuotient f i side (high n) =
        valueHigh (n + N) := by
    exact (maxwellOneSidedStepLast_value_eq_of_representsOn_subdomain
      i side hrep (high n).1 (high n).2 (valueHigh (n + N))
      (maxwellOneSidedStepCore_subset_domain hballV (hhighCore n))
      (hHigh (n + N))).symm
  have hbetween (n : ℕ) : y ∈ Set.Icc
      (maxwellOneSidedDifferenceQuotient f i side (low n))
      (maxwellOneSidedDifferenceQuotient f i side (high n)) := by
    rw [hlowValue n, hhighValue n]
    exact ⟨le_of_lt (htail n).2.2.1, le_of_lt (htail n).2.2.2⟩
  have hcontinuous :=
    continuousOn_maxwellOneSidedDifferenceQuotient_stepCore
      i side hf hballV
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
    exact maxwellOneSidedStepLast_mem_of_representsOn_subdomain
      i side hVU hrep (sourceY n).1 (sourceY n).2 y
      (maxwellOneSidedStepCore_subset_domain hballV
        (hsourceYcore n)) (hthetaValue n).symm
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

/-! ## Localized extended values -/

theorem maxwellOneSidedStepZeroTrace_above_of_positiveInfinity_and_finiteTrace_neighborhood
    {p : ℕ} {U V : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {f : RealEuclidean p → ℝ}
    (i : Fin p) (side : MaxwellOneSidedStep)
    (hVopen : IsOpen V) (hVU : V ⊆ U) (hf : ContinuousOn f V)
    (hrep : MaxwellRelation.RepresentsOn R V (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ V) {a b : ℝ}
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
  obtain ⟨hreciprocal⟩ :=
    (mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
      U R i side .positive x).mp hinfinity
  let hdivergent := hreciprocal.toDivergentSlopeApproach
  have hfiniteBelow : ∀ᶠ n in atTop,
      maxwellStepLastValue (hfinite.point n) < b :=
    hfinite.value_tendsto.eventually_lt_const hab
  have hdivergentTop : Tendsto hdivergent.slope atTop atTop := by
    simpa only [MaxwellSlopeInfinitySign.divergenceFilter] using
      hdivergent.slope_tendsto
  have hdivergentAbove : ∀ᶠ n in atTop, b < hdivergent.slope n :=
    hdivergentTop.eventually_gt_atTop b
  exact maxwellOneSidedStepZeroTrace_mem_of_straddling_sources_neighborhood
    i side hVopen hVU hf hrep hx
    hfinite.source_tendsto hdivergent.source_tendsto
    (fun n ↦ (side.sign_mul_step_pos_iff
      (maxwellStepLastStep (hfinite.point n))).mpr (hfinite.step_sign n))
    hdivergent.source_step_pos
    (fun n ↦ by
      change realEuclideanAppend
          (realEuclideanAppend (maxwellStepLastBase (hfinite.point n))
            (fun _ : Fin 1 ↦ maxwellStepLastValue (hfinite.point n)))
          (fun _ : Fin 1 ↦ side.sign *
            (side.sign * maxwellStepLastStep (hfinite.point n))) ∈ _
      rw [← mul_assoc, side.sign_mul_self, one_mul,
        realEuclideanAppend_stepLastCoordinates]
      exact hfinite.point_mem n)
    hdivergent.point_mem
    (hfiniteBelow.and hdivergentAbove)

theorem maxwellOneSidedStepZeroTrace_below_of_negativeInfinity_and_finiteTrace_neighborhood
    {p : ℕ} {U V : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {f : RealEuclidean p → ℝ}
    (i : Fin p) (side : MaxwellOneSidedStep)
    (hVopen : IsOpen V) (hVU : V ⊆ U) (hf : ContinuousOn f V)
    (hrep : MaxwellRelation.RepresentsOn R V (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ V) {a b : ℝ}
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
  obtain ⟨hreciprocal⟩ :=
    (mem_maxwellOneSidedInfinityBase_iff_nonempty_approach
      U R i side .negative x).mp hinfinity
  let hdivergent := hreciprocal.toDivergentSlopeApproach
  have hdivergentBot : Tendsto hdivergent.slope atTop atBot := by
    simpa only [MaxwellSlopeInfinitySign.divergenceFilter] using
      hdivergent.slope_tendsto
  have hdivergentBelow : ∀ᶠ n in atTop, hdivergent.slope n < b :=
    hdivergentBot.eventually_lt_atBot b
  have hfiniteAbove : ∀ᶠ n in atTop,
      b < maxwellStepLastValue (hfinite.point n) :=
    hfinite.value_tendsto.eventually_const_lt hba
  exact maxwellOneSidedStepZeroTrace_mem_of_straddling_sources_neighborhood
    i side hVopen hVU hf hrep hx
    hdivergent.source_tendsto hfinite.source_tendsto
    hdivergent.source_step_pos
    (fun n ↦ (side.sign_mul_step_pos_iff
      (maxwellStepLastStep (hfinite.point n))).mpr (hfinite.step_sign n))
    hdivergent.point_mem
    (fun n ↦ by
      change realEuclideanAppend
          (realEuclideanAppend (maxwellStepLastBase (hfinite.point n))
            (fun _ : Fin 1 ↦ maxwellStepLastValue (hfinite.point n)))
          (fun _ : Fin 1 ↦ side.sign *
            (side.sign * maxwellStepLastStep (hfinite.point n))) ∈ _
      rw [← mul_assoc, side.sign_mul_self, one_mul,
        realEuclideanAppend_stepLastCoordinates]
      exact hfinite.point_mem n)
    (hdivergentBelow.and hfiniteAbove)

theorem maxwellOneSidedStepZeroTrace_of_bothInfinities_neighborhood
    {p : ℕ} {U V : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {f : RealEuclidean p → ℝ}
    (i : Fin p) (side : MaxwellOneSidedStep)
    (hVopen : IsOpen V) (hVU : V ⊆ U) (hf : ContinuousOn f V)
    (hrep : MaxwellRelation.RepresentsOn R V (fun z _ ↦ f z))
    {x : RealEuclidean p} (hx : x ∈ V) (y : ℝ)
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
  have hpositiveTop : Tendsto hpositiveDivergent.slope atTop atTop := by
    simpa only [MaxwellSlopeInfinitySign.divergenceFilter] using
      hpositiveDivergent.slope_tendsto
  have hnegativeBot : Tendsto hnegativeDivergent.slope atTop atBot := by
    simpa only [MaxwellSlopeInfinitySign.divergenceFilter] using
      hnegativeDivergent.slope_tendsto
  have hnegativeBelow : ∀ᶠ n in atTop,
      hnegativeDivergent.slope n < y :=
    hnegativeBot.eventually_lt_atBot y
  have hpositiveAbove : ∀ᶠ n in atTop,
      y < hpositiveDivergent.slope n :=
    hpositiveTop.eventually_gt_atTop y
  exact maxwellOneSidedStepZeroTrace_mem_of_straddling_sources_neighborhood
    i side hVopen hVU hf hrep hx
    hnegativeDivergent.source_tendsto
    hpositiveDivergent.source_tendsto
    hnegativeDivergent.source_step_pos
    hpositiveDivergent.source_step_pos
    hnegativeDivergent.point_mem
    hpositiveDivergent.point_mem
    (hnegativeBelow.and hpositiveAbove)

/-! ## Restricted extended IVT -/

/-- Restricting the three extended fibers to an open continuity domain gives
the full source-shaped extended IVT, while the traces themselves remain the
ones formed from the original domain `U`. -/
theorem maxwellOneSidedExtendedSlopeIntermediateValue_restrictBase_of_continuousOn
    {p : ℕ} {U V : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1} {f : RealEuclidean p → ℝ}
    (i : Fin p) (side : MaxwellOneSidedStep)
    (hVopen : IsOpen V) (hVU : V ⊆ U) (hf : ContinuousOn f V)
    (hrep : MaxwellRelation.RepresentsOn R V (fun z _ ↦ f z)) :
    MaxwellExtendedSlopeIntermediateValue
      (maxwellRelationRestrict
        (maxwellOneSidedStepZeroTrace U R i side) V)
      (maxwellOneSidedInfinityBase U R i side .positive ∩ V)
      (maxwellOneSidedInfinityBase U R i side .negative ∩ V) := by
  refine
    { finite_between := ?_
      finite_to_positiveInfinity := ?_
      negativeInfinity_to_finite := ?_
      negativeInfinity_to_positiveInfinity := ?_ }
  · intro x a b hab ha hb
    have ha' :=
      (realEuclideanAppend_mem_maxwellRelationRestrict_iff
        (maxwellOneSidedStepZeroTrace U R i side) V x
        (fun _ : Fin 1 ↦ a)).mp ha
    have hb' :=
      (realEuclideanAppend_mem_maxwellRelationRestrict_iff
        (maxwellOneSidedStepZeroTrace U R i side) V x
        (fun _ : Fin 1 ↦ b)).mp hb
    intro y hy
    apply (realEuclideanAppend_mem_maxwellRelationRestrict_iff
      (maxwellOneSidedStepZeroTrace U R i side) V x
      (fun _ : Fin 1 ↦ y)).mpr
    exact ⟨
      maxwellOneSidedStepZeroTrace_interval_pointwise_of_continuousOn_neighborhood
        i side hVopen hVU hf hrep ha'.2 hab ha'.1 hb'.1 hy,
      ha'.2⟩
  · intro x a b hab ha hx
    rcases eq_or_lt_of_le hab with hEq | hlt
    · subst b
      exact ha
    · apply
        (realEuclideanAppend_mem_maxwellRelationRestrict_iff
          (maxwellOneSidedStepZeroTrace U R i side) V x
          (fun _ : Fin 1 ↦ b)).mpr
      have ha' :=
        (realEuclideanAppend_mem_maxwellRelationRestrict_iff
          (maxwellOneSidedStepZeroTrace U R i side) V x
          (fun _ : Fin 1 ↦ a)).mp ha
      exact ⟨
        maxwellOneSidedStepZeroTrace_above_of_positiveInfinity_and_finiteTrace_neighborhood
          i side hVopen hVU hf hrep hx.2 ha'.1 hx.1 hlt,
        hx.2⟩
  · intro x a b hba ha hx
    rcases eq_or_lt_of_le hba with hEq | hlt
    · subst b
      exact ha
    · apply
        (realEuclideanAppend_mem_maxwellRelationRestrict_iff
          (maxwellOneSidedStepZeroTrace U R i side) V x
          (fun _ : Fin 1 ↦ b)).mpr
      have ha' :=
        (realEuclideanAppend_mem_maxwellRelationRestrict_iff
          (maxwellOneSidedStepZeroTrace U R i side) V x
          (fun _ : Fin 1 ↦ a)).mp ha
      exact ⟨
        maxwellOneSidedStepZeroTrace_below_of_negativeInfinity_and_finiteTrace_neighborhood
          i side hVopen hVU hf hrep hx.2 ha'.1 hx.1 hlt,
        hx.2⟩
  · intro x y hpositive hnegative
    apply
      (realEuclideanAppend_mem_maxwellRelationRestrict_iff
        (maxwellOneSidedStepZeroTrace U R i side) V x
        (fun _ : Fin 1 ↦ y)).mpr
    exact ⟨
      maxwellOneSidedStepZeroTrace_of_bothInfinities_neighborhood
        i side hVopen hVU hf hrep hpositive.2 y hpositive.1 hnegative.1,
      hpositive.2⟩

/-! ## Restriction identities and domain control -/

theorem maxwellOneSidedExtendedMultivaluedLocus_restrict_eq_inter
    {p : ℕ} (G : MaxwellRelation p 1)
    (P N V : Set (RealEuclidean p)) :
    maxwellOneSidedExtendedMultivaluedLocus
        (maxwellRelationRestrict G V) (P ∩ V) (N ∩ V) =
      maxwellOneSidedExtendedMultivaluedLocus G P N ∩ V := by
  ext x
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    have hxV : x ∈ V := by
      cases a with
      | finite y =>
          exact (realEuclideanAppend_mem_maxwellRelationRestrict_iff
            G V x (fun _ : Fin 1 ↦ y)).mp ha |>.2
      | positiveInfinity => exact ha.2
      | negativeInfinity => exact ha.2
    refine ⟨⟨a, b, ?_, ?_, hab⟩, hxV⟩
    · cases a with
      | finite y =>
          exact (realEuclideanAppend_mem_maxwellRelationRestrict_iff
            G V x (fun _ : Fin 1 ↦ y)).mp ha |>.1
      | positiveInfinity => exact ha.1
      | negativeInfinity => exact ha.1
    · cases b with
      | finite y =>
          exact (realEuclideanAppend_mem_maxwellRelationRestrict_iff
            G V x (fun _ : Fin 1 ↦ y)).mp hb |>.1
      | positiveInfinity => exact hb.1
      | negativeInfinity => exact hb.1
  · rintro ⟨⟨a, b, ha, hb, hab⟩, hxV⟩
    refine ⟨a, b, ?_, ?_, hab⟩
    · cases a with
      | finite y =>
          exact (realEuclideanAppend_mem_maxwellRelationRestrict_iff
            G V x (fun _ : Fin 1 ↦ y)).mpr ⟨ha, hxV⟩
      | positiveInfinity => exact ⟨ha, hxV⟩
      | negativeInfinity => exact ⟨ha, hxV⟩
    · cases b with
      | finite y =>
          exact (realEuclideanAppend_mem_maxwellRelationRestrict_iff
            G V x (fun _ : Fin 1 ↦ y)).mpr ⟨hb, hxV⟩
      | positiveInfinity => exact ⟨hb, hxV⟩
      | negativeInfinity => exact ⟨hb, hxV⟩

theorem maxwellOneSidedStepZeroTrace_domain_subset_closure
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep) :
    maxwellRelationDomain (maxwellOneSidedStepZeroTrace U R i side) ⊆
      closure U := by
  intro x hx
  apply maxwellDifferenceQuotientZeroTrace_domain_subset_closure U R i
  rcases hx with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  rw [← maxwellPositiveStepZeroTrace_union_negativeStepZeroTrace U R i]
  cases side with
  | positive => exact Or.inl hy
  | negative => exact Or.inr hy

theorem maxwellOneSidedExtendedMultivaluedLocus_subset_closure_domain
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (side : MaxwellOneSidedStep) :
    maxwellOneSidedExtendedMultivaluedLocus
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative) ⊆
      closure U := by
  rw [maxwellOneSidedExtendedMultivaluedLocus_eq]
  rintro x (hx | hx)
  · exact maxwellOneSidedStepZeroTrace_domain_subset_closure U R i side
      (maxwellMultivaluedLocus_subset_domain _ hx)
  · rcases hx with hx | hx
    · exact maxwellOneSidedStepZeroTrace_domain_subset_closure U R i side hx.1
    · rcases hx with hx | hx
      · exact maxwellOneSidedStepZeroTrace_domain_subset_closure U R i side hx.1
      · exact maxwellOneSidedInfinityBase_subset_closure_domain
          U R i side .positive hx.1

/-! ## Automatic one-sided bad-locus smallness -/

/-- The extended one-sided bad locus is small without a global IVT premise.
The IVT is applied only on the open continuity domain of the canonical
representative; an open-patch argument then absorbs the discarded closed
exceptional set. -/
theorem maxwellOneSidedExtendedSlopeBadLocusSmallness_of_chosenContinuity
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (side : MaxwellOneSidedStep)
    (hUopen : IsOpen U) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunctionOn U R) :
    MaxwellSlopeBaseLocusSmallness S
      (maxwellOneSidedExtendedMultivaluedLocus
        (maxwellOneSidedStepZeroTrace U R i side)
        (maxwellOneSidedInfinityBase U R i side .positive)
        (maxwellOneSidedInfinityBase U R i side .negative)) := by
  let E : Set (RealEuclidean p) :=
    maxwellChosenContinuityExceptionalLocus U R
  let V : Set (RealEuclidean p) := U \ E
  let G : MaxwellRelation p 1 :=
    maxwellOneSidedStepZeroTrace U R i side
  let P : Set (RealEuclidean p) :=
    maxwellOneSidedInfinityBase U R i side .positive
  let N : Set (RealEuclidean p) :=
    maxwellOneSidedInfinityBase U R i side .negative
  let B : Set (RealEuclidean p) :=
    maxwellOneSidedExtendedMultivaluedLocus G P N
  have hp : 0 < p := maxwellFinArity_pos i
  have hcontinuitySmall :=
    maxwellChosenContinuityBadLocusSmallness_of_theorem21
      hC h21 hp hR hRpseudo
  have hEclosed : IsClosed E := by
    exact isClosed_maxwellChosenContinuityExceptionalLocus U R
  have hEempty : interior E = ∅ := by
    exact hcontinuitySmall.exceptionalLocus_interior_eq_empty
  have hVopen : IsOpen V := by
    exact hUopen.sdiff hEclosed
  have hVU : V ⊆ U := inter_subset_left
  have hf : ContinuousOn (maxwellChosenScalarValue R) V := by
    exact hRpseudo.continuousOn_chosenScalarValue_compl_exceptional
  have hVgood : V ⊆ U \ maxwellMultivaluedLocus R := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro hmulti
    apply hx.2
    apply subset_closure
    rcases hmulti with ⟨y₁, y₂, hy₁, hy₂, hne⟩
    exact ⟨hx.1, Or.inl
      ⟨y₁, y₂, subset_closure hy₁, subset_closure hy₂, hne⟩⟩
  have hrep : MaxwellRelation.RepresentsOn R V
      (fun x _ ↦ maxwellChosenScalarValue R x) := by
    exact (hRpseudo.representsOn_maxwellChosenScalarValue_of_subset
      (Set.Subset.rfl : maxwellMultivaluedLocus R ⊆
        maxwellMultivaluedLocus R)).mono hVgood
  have hIVT :=
    maxwellOneSidedExtendedSlopeIntermediateValue_restrictBase_of_continuousOn
      i side hVopen hVU hf hrep
  have hrestrictedFilling := hIVT.intervalFilling
  have hrestrictEq :
      maxwellOneSidedExtendedMultivaluedLocus
          (maxwellRelationRestrict G V) (P ∩ V) (N ∩ V) =
        B ∩ V := by
    exact maxwellOneSidedExtendedMultivaluedLocus_restrict_eq_inter
      G P N V
  have hlocalFilling : MaxwellExtendedSlopeIntervalFilling G (B ∩ V) := by
    intro x hx
    have hx' : x ∈ maxwellOneSidedExtendedMultivaluedLocus
        (maxwellRelationRestrict G V) (P ∩ V) (N ∩ V) := by
      rw [hrestrictEq]
      exact hx
    obtain ⟨a, b, hab, hfill⟩ := hrestrictedFilling x hx'
    refine ⟨a, b, hab, ?_⟩
    intro y hy
    exact (realEuclideanAppend_mem_maxwellRelationRestrict_iff
      G V x (fun _ : Fin 1 ↦ y)).mp (hfill hy) |>.1
  have htrace :=
    maxwellDifferenceQuotientPositiveZeroTraceSmallness_of_pseudofunction
      hC.toPositiveArityWeakSetStructure hmem h21 h22 i hU hR
        hRpseudo.multivalued_null
  have hGclosed : IsClosed G := by
    cases side with
    | positive => exact isClosed_maxwellPositiveStepZeroTrace U R i
    | negative => exact isClosed_maxwellNegativeStepZeroTrace U R i
  have hGnull :
      (volume : Measure (RealEuclidean (p + 1))) G = 0 := by
    cases side with
    | positive => exact htrace.positiveTrace_volume_eq_zero
    | negative => exact htrace.negativeTrace_volume_eq_zero
  have hlocalNull :
      (volume : Measure (RealEuclidean p)) (B ∩ V) = 0 :=
    volume_eq_zero_of_extendedSlopeIntervalFilling
      hGclosed hGnull hlocalFilling
  have hlocalEmpty : interior (B ∩ V) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hne
    have hpos : 0 < (volume : Measure (RealEuclidean p)) (B ∩ V) :=
      MeasureTheory.Measure.measure_pos_of_nonempty_interior
        (volume : Measure (RealEuclidean p)) hne
    rw [hlocalNull] at hpos
    exact (lt_irrefl 0) hpos
  have hBclosure : B ⊆ closure U := by
    exact maxwellOneSidedExtendedMultivaluedLocus_subset_closure_domain
      U R i side
  have hBempty : interior B = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hinterior
    obtain ⟨x, hx⟩ := hinterior
    have hxClosure : x ∈ closure U := hBclosure (interior_subset hx)
    rw [mem_closure_iff] at hxClosure
    obtain ⟨z, hzInterior, hzU⟩ :=
      hxClosure (interior B) isOpen_interior hx
    have hOopen : IsOpen (interior B ∩ U) :=
      isOpen_interior.inter hUopen
    have hOne : (interior B ∩ U).Nonempty :=
      ⟨z, hzInterior, hzU⟩
    obtain ⟨w, epsilon, hepsilon, hball⟩ :=
      exists_ball_subset_diff_of_open_nonempty_of_closed_interior_empty
        hOopen hOne hEclosed hEempty
    have hballLocal : Metric.ball w epsilon ⊆ B ∩ V := by
      intro q hq
      have hq' := hball hq
      exact ⟨interior_subset hq'.1.1, ⟨hq'.1.2, hq'.2⟩⟩
    have hwLocal : w ∈ interior (B ∩ V) :=
      (Metric.isOpen_ball.subset_interior_iff.mpr hballLocal)
        (Metric.mem_ball_self hepsilon)
    rw [hlocalEmpty] at hwLocal
    exact hwLocal
  have hclusters := maxwellOneSidedExtendedSlopeClusterMembership
    hC.toPositiveArityWeakSetStructure hmem i hU hR
  have hBmem : B ∈ charbonnelClosure S p := by
    cases side with
    | positive => exact hclusters.positiveExtendedMultivalued_mem
    | negative => exact hclusters.negativeExtendedMultivalued_mem
  exact maxwellSlopeBaseLocusSmallness_of_interior_eq_empty
    h21 hp hBmem hBempty

/-- Both one-sided applications of Lemma 2.3.3 now follow from the canonical
continuity theorem, with no retained one-sided IVT fields. -/
theorem maxwellOneSidedExtendedSlopeBadLociSmallness_of_chosenContinuity
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hmem : CharbonnelSection5TraceMembership (charbonnelClosure S))
    (h21 : CharbonnelTheorem21 (charbonnelClosure S))
    (h22 : CharbonnelTheorem22 (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hUopen : IsOpen U)
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hRpseudo : IsMaxwellPseudofunctionOn U R) :
    MaxwellOneSidedExtendedSlopeBadLociSmallness S U R i := by
  have htrace :=
    maxwellDifferenceQuotientPositiveZeroTraceSmallness_of_pseudofunction
      hC.toPositiveArityWeakSetStructure hmem h21 h22 i hU hR
        hRpseudo.multivalued_null
  have hclusters := maxwellOneSidedExtendedSlopeClusterMembership
    hC.toPositiveArityWeakSetStructure hmem i hU hR
  exact
    { traceSmallness := htrace
      clusterMembership := hclusters
      positiveBadLocus :=
        maxwellOneSidedExtendedSlopeBadLocusSmallness_of_chosenContinuity
          hC hmem h21 h22 i .positive hUopen hU hR hRpseudo
      negativeBadLocus :=
        maxwellOneSidedExtendedSlopeBadLocusSmallness_of_chosenContinuity
          hC hmem h21 h22 i .negative hUopen hU hR hRpseudo }

end AbelFormalization
