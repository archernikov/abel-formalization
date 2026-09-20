import AbelFormalization.ClusterBalancing
import AbelFormalization.FilteredFiniteHierarchy
import AbelFormalization.SeparatedFiniteRealJetTrace
import AbelFormalization.CrossClusterHierarchy
import AbelFormalization.OrderedClusterBalancingSelection
import Mathlib.Data.List.TakeDrop

/-!
# Analytic hierarchy for one balancing decrement

A `ClusterBalancingPlan` records every individual logarithmic substitution,
but the quantitative-transfer API needs the analytic scale hypotheses at each
individual boundary.  This file supplies that bridge.

For a prefix of the fixed decrement list, the scale is the paper's canonical
full-tuple scale: the maximum of `2` and all inverse-Abel representatives at
that boundary.  At a step, the one-block transfer representative is the
selected representative after its unit decrement.  The balancing trace says
that this coordinate was a current maximum and at least one above the fixed
base.  Separation modulo the integers then shows that the selected
post-decrement representative dominates the logarithm of every coordinate at
the next boundary, hence the logarithm of their finite maximum.

The final theorem packages both structures consumed by quantitative transfer:
`BalancedRealJetTransferHierarchy 0` for the one selected block and
`CrossClusterTransferScaleDomination 0` between the post- and pre-boundary
full-tuple scales.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Finset Function
open scoped Topology

universe u

/-! ## Exact prefix arithmetic -/

/-- Shifting along two concatenated decrement lists is literal composition
of the two corresponding shift operations. -/
@[simp]
theorem clusterShiftedTimes_append
    {ι : Type u} [DecidableEq ι]
    (a : ι → ℝ) (first second : List ι) :
    clusterShiftedTimes a (first ++ second) =
      clusterShiftedTimes (clusterShiftedTimes a first) second := by
  funext i
  simp only [clusterShiftedTimes, List.count_append]
  push_cast
  ring

/-- Appending one occurrence lowers its selected coordinate by exactly one. -/
@[simp]
theorem clusterShiftedTimes_append_singleton_self
    {ι : Type u} [DecidableEq ι]
    (a : ι → ℝ) (steps : List ι) (selected : ι) :
    clusterShiftedTimes a (steps ++ [selected]) selected =
      clusterShiftedTimes a steps selected - 1 := by
  simp [clusterShiftedTimes]
  ring

/-- Appending one occurrence leaves every other coordinate unchanged. -/
@[simp]
theorem clusterShiftedTimes_append_singleton_of_ne
    {ι : Type u} [DecidableEq ι]
    (a : ι → ℝ) (steps : List ι) {selected i : ι}
    (hi : i ≠ selected) :
    clusterShiftedTimes a (steps ++ [selected]) i =
      clusterShiftedTimes a steps i := by
  simp [clusterShiftedTimes, Ne.symm hi]

/-- Additional decrements can only lower a shifted time. -/
theorem clusterShiftedTimes_append_le
    {ι : Type u} [DecidableEq ι]
    (a : ι → ℝ) (first second : List ι) (i : ι) :
    clusterShiftedTimes a (first ++ second) i ≤
      clusterShiftedTimes a first i := by
  change a i - ((first ++ second).count i : ℝ) ≤
    a i - (first.count i : ℝ)
  rw [List.count_append]
  push_cast
  have hcount : 0 ≤ (second.count i : ℝ) := Nat.cast_nonneg _
  linarith

/-- A full balancing trace is below every one of its prefix boundaries. -/
theorem clusterShiftedTimes_le_take
    {ι : Type u} [DecidableEq ι]
    (a : ι → ℝ) (steps : List ι) (r : ℕ) (i : ι) :
    clusterShiftedTimes a steps i ≤
      clusterShiftedTimes a (steps.take r) i := by
  calc
    clusterShiftedTimes a steps i =
        clusterShiftedTimes a (steps.take r ++ steps.drop r) i := by
      rw [List.take_append_drop]
    _ ≤ clusterShiftedTimes a (steps.take r) i :=
      clusterShiftedTimes_append_le a (steps.take r) (steps.drop r) i

/-- The successor prefix consists of the preceding prefix followed by the
selected entry.  This is the list identity synchronizing analytic boundaries
with `individualCentralIdealBoundary`. -/
theorem take_succ_eq_take_append_get
    {ι : Type u} (steps : List ι) (j : Fin steps.length) :
    steps.take j.succ = steps.take j.castSucc ++ [steps.get j] := by
  simpa only [Fin.val_succ, Fin.val_castSucc] using
    (List.take_succ_eq_append_getElem j.isLt).trans
      (congrArg (fun x ↦ steps.take j.castSucc ++ [x])
        (List.get_eq_getElem.symm))

/-! ## Canonical full-tuple boundary scales -/

/-- Abel times at the boundary following the first `r` fixed decrements. -/
def clusterBalancingPrefixTime
    {ι : Type u} [DecidableEq ι]
    (rawTime : ℕ → ι → ℝ) (steps : List ι) (r : ℕ) :
    ι → ℕ → ℝ :=
  fun i n ↦ clusterShiftedTimes (rawTime n) (steps.take r) i

/-- Inverse-Abel representatives at one prefix boundary. -/
def clusterBalancingPrefixValue
    {ι : Type u} [DecidableEq ι]
    (A : ℝ → ℝ) (rawTime : ℕ → ι → ℝ) (steps : List ι) (r : ℕ) :
    ι → ℕ → ℝ :=
  fun i n ↦ inverse A (clusterBalancingPrefixTime rawTime steps r i n)

/-- The unpadded maximum of a finite tuple of boundary representatives. -/
def clusterBalancingPrefixMaximum
    {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : ℝ → ℝ) (rawTime : ℕ → ι → ℝ) (steps : List ι) (r n : ℕ) : ℝ :=
  (Finset.univ.image
    (fun i ↦ clusterBalancingPrefixValue A rawTime steps r i n)).max'
      (by simp)

/-- The paper's canonical scale at a balancing boundary: the full-tuple
maximum, padded below by `2`. -/
def clusterBalancingPrefixScale
    {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : ℝ → ℝ) (rawTime : ℕ → ι → ℝ) (steps : List ι) (r n : ℕ) : ℝ :=
  max 2 (clusterBalancingPrefixMaximum A rawTime steps r n)

/-- Every boundary representative is bounded by the unpadded tuple maximum. -/
theorem clusterBalancingPrefixValue_le_maximum
    {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : ℝ → ℝ) (rawTime : ℕ → ι → ℝ) (steps : List ι)
    (r n : ℕ) (i : ι) :
    clusterBalancingPrefixValue A rawTime steps r i n ≤
      clusterBalancingPrefixMaximum A rawTime steps r n := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Some coordinate attains the unpadded tuple maximum. -/
theorem exists_clusterBalancingPrefixValue_eq_maximum
    {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : ℝ → ℝ) (rawTime : ℕ → ι → ℝ) (steps : List ι)
    (r n : ℕ) :
    ∃ i, clusterBalancingPrefixValue A rawTime steps r i n =
      clusterBalancingPrefixMaximum A rawTime steps r n := by
  have hm := Finset.max'_mem
    (Finset.univ.image
      (fun i ↦ clusterBalancingPrefixValue A rawTime steps r i n))
    (by simp)
  obtain ⟨i, _hi, himax⟩ := Finset.mem_image.mp hm
  exact ⟨i, himax⟩

/-- Every boundary representative is bounded by the padded boundary scale. -/
theorem clusterBalancingPrefixValue_le_scale
    {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : ℝ → ℝ) (rawTime : ℕ → ι → ℝ) (steps : List ι)
    (r n : ℕ) (i : ι) :
    clusterBalancingPrefixValue A rawTime steps r i n ≤
      clusterBalancingPrefixScale A rawTime steps r n :=
  (clusterBalancingPrefixValue_le_maximum A rawTime steps r n i).trans
    (le_max_right _ _)

theorem two_le_clusterBalancingPrefixScale
    {ι : Type u} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : ℝ → ℝ) (rawTime : ℕ → ι → ℝ) (steps : List ι)
    (r n : ℕ) :
    2 ≤ clusterBalancingPrefixScale A rawTime steps r n :=
  le_max_left _ _

/-- The selected one-block representative after step `j`; its Abel time is
written in the source-prefix form used by the real-jet substitution. -/
def clusterBalancingStepValue
    {ι : Type u} [DecidableEq ι]
    (A : ℝ → ℝ) (rawTime : ℕ → ι → ℝ) (steps : List ι)
    (j : Fin steps.length) (n : ℕ) : ℝ :=
  inverse A
    (clusterBalancingPrefixTime rawTime steps j.castSucc (steps.get j) n - 1)

/-- On Abel times, the selected successor boundary is exactly one below its
preceding boundary. -/
theorem clusterBalancingPrefixTime_succ_selected
    {ι : Type u} [DecidableEq ι]
    (rawTime : ℕ → ι → ℝ) (steps : List ι)
    (j : Fin steps.length) (n : ℕ) :
    clusterBalancingPrefixTime rawTime steps j.succ (steps.get j) n =
      clusterBalancingPrefixTime rawTime steps j.castSucc (steps.get j) n - 1 := by
  unfold clusterBalancingPrefixTime
  rw [take_succ_eq_take_append_get]
  exact clusterShiftedTimes_append_singleton_self _ _ _

/-- On Abel times, every unselected coordinate is unchanged at the successor
boundary. -/
theorem clusterBalancingPrefixTime_succ_of_ne
    {ι : Type u} [DecidableEq ι]
    (rawTime : ℕ → ι → ℝ) (steps : List ι)
    (j : Fin steps.length) (n : ℕ) {i : ι}
    (hi : i ≠ steps.get j) :
    clusterBalancingPrefixTime rawTime steps j.succ i n =
      clusterBalancingPrefixTime rawTime steps j.castSucc i n := by
  unfold clusterBalancingPrefixTime
  rw [take_succ_eq_take_append_get]
  exact clusterShiftedTimes_append_singleton_of_ne _ _ hi

/-- The selected coordinate at the post-boundary is exactly the explicit
unit-decrement representative used by the one-block transfer. -/
theorem clusterBalancingPrefixValue_succ_selected
    {ι : Type u} [DecidableEq ι]
    (A : ℝ → ℝ) (rawTime : ℕ → ι → ℝ) (steps : List ι)
    (j : Fin steps.length) (n : ℕ) :
    clusterBalancingPrefixValue A rawTime steps j.succ (steps.get j) n =
      clusterBalancingStepValue A rawTime steps j n := by
  unfold clusterBalancingPrefixValue clusterBalancingStepValue
  rw [clusterBalancingPrefixTime_succ_selected]

/-- Every unselected coordinate is unchanged at the successor boundary. -/
theorem clusterBalancingPrefixValue_succ_of_ne
    {A : ℝ → ℝ} {ι : Type u} [DecidableEq ι]
    (rawTime : ℕ → ι → ℝ) (steps : List ι)
    (j : Fin steps.length) (n : ℕ) {i : ι}
    (hi : i ≠ steps.get j) :
    clusterBalancingPrefixValue A rawTime steps j.succ i n =
      clusterBalancingPrefixValue A rawTime steps j.castSucc i n := by
  unfold clusterBalancingPrefixValue
  rw [clusterBalancingPrefixTime_succ_of_ne rawTime steps j n hi]

/-! ## Pointwise legality of an indexed balancing step -/

namespace ClusterBalancingPlan

variable {ι : Type u} [DecidableEq ι]
variable {a : ι → ℝ} {base : ℝ} {steps : List ι}

private theorem fixedSteps_decomposition
    (p : ClusterBalancingPlan a base) (hsteps : p.steps = steps)
    (j : Fin steps.length) :
    p.steps = steps.take j.castSucc ++ steps.get j ::
      steps.drop j.succ := by
  calc
    p.steps = steps := hsteps
    _ = steps.take j.succ ++ steps.drop j.succ :=
      (List.take_append_drop j.succ steps).symm
    _ = (steps.take j.castSucc ++ [steps.get j]) ++
        steps.drop j.succ := by rw [take_succ_eq_take_append_get]
    _ = steps.take j.castSucc ++ steps.get j ::
        steps.drop j.succ := by simp

/-- At every indexed prefix, the recorded coordinate is a current maximum. -/
theorem prefix_selected_is_currentMaximum
    (p : ClusterBalancingPlan a base) (hsteps : p.steps = steps)
    (j : Fin steps.length) (i : ι) :
    clusterShiftedTimes a (steps.take j.castSucc) i ≤
      clusterShiftedTimes a (steps.take j.castSucc) (steps.get j) := by
  exact p.chosen_is_currentMaximum _ _ _
    (p.fixedSteps_decomposition hsteps j) i

/-- At every indexed prefix, the recorded current maximum is at least one
above the balancing base. -/
theorem prefix_selected_is_oneAboveBase
    (p : ClusterBalancingPlan a base) (hsteps : p.steps = steps)
    (j : Fin steps.length) :
    base + 1 ≤
      clusterShiftedTimes a (steps.take j.castSucc) (steps.get j) := by
  exact p.chosen_is_oneAboveBase _ _ _
    (p.fixedSteps_decomposition hsteps j)

/-- Every prefix boundary remains above the balancing base. -/
theorem base_le_prefix
    (p : ClusterBalancingPlan a base) (hsteps : p.steps = steps)
    (r : ℕ) (i : ι) :
    base ≤ clusterShiftedTimes a (steps.take r) i := by
  have hfinal : base ≤ clusterShiftedTimes a steps i := by
    simpa only [← hsteps] using p.base_le_final i
  exact hfinal.trans (clusterShiftedTimes_le_take a steps r i)

end ClusterBalancingPlan

/-! ## Analytic maximum bridge -/

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- The selected post-decrement representative dominates the logarithm of
the canonical post-boundary scale.  This is the only nontrivial analytic
obligation in the singleton transfer hierarchy.

`hseparated` is exactly the within-cluster separation estimate before any
integer shifts.  The identity
`integerDistance_clusterShiftedTimes_sub` transports it to every prefix.
-/
theorem clusterBalancingStepValue_div_log_postScale_tendsto
    {m : ℕ}
    (rawTime : ℕ → Fin (m + 1) → ℝ)
    (base : ℕ → ℝ)
    (plans : ∀ n, ClusterBalancingPlan (rawTime n) (base n))
    (fixedSteps : List (Fin (m + 1)))
    (hfixedSteps : ∀ n, (plans n).steps = fixedSteps)
    (j : Fin fixedSteps.length)
    {N c : ℝ} (hc : 0 < c) (hN : 5 ≤ N)
    (hbaseTop : Tendsto base atTop atTop)
    (hseparated : ∀ᶠ n in atTop,
      ∀ i k : Fin (m + 1), i ≠ k →
        c / inverse A (base n - N) ≤
          integerDistance (rawTime n i - rawTime n k)) :
    Tendsto (fun n ↦
      clusterBalancingStepValue A rawTime fixedSteps j n /
        Real.log
          (clusterBalancingPrefixScale A rawTime fixedSteps j.succ n))
      atTop atTop := by
  let selected : Fin (m + 1) := fixedSteps.get j
  let beforeTime : Fin (m + 1) → ℕ → ℝ :=
    clusterBalancingPrefixTime rawTime fixedSteps j.castSucc
  let afterValue : Fin (m + 1) → ℕ → ℝ :=
    clusterBalancingPrefixValue A rawTime fixedSteps j.succ
  let u : ℕ → ℝ :=
    clusterBalancingStepValue A rawTime fixedSteps j

  have hselectedMaximum : ∀ n i, beforeTime i n ≤ beforeTime selected n := by
    intro n i
    exact (plans n).prefix_selected_is_currentMaximum
      (hfixedSteps n) j i
  have hselectedAbove : ∀ n, base n + 1 ≤ beforeTime selected n := by
    intro n
    exact (plans n).prefix_selected_is_oneAboveBase (hfixedSteps n) j
  have hbeforeLower : ∀ n i, base n ≤ beforeTime i n := by
    intro n i
    exact (plans n).base_le_prefix (hfixedSteps n) j.castSucc i
  have huTimeTop : Tendsto (fun n ↦ beforeTime selected n - 1)
      atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hbaseTop
    filter_upwards [] with n
    linarith [hselectedAbove n]
  have huTop : Tendsto u atTop atTop := by
    exact hA.inverse_tendsto_atTop.comp huTimeTop

  have hprefixSeparated : ∀ᶠ n in atTop,
      ∀ i k : Fin (m + 1), i ≠ k →
        c / inverse A (base n - N) ≤
          integerDistance (beforeTime i n - beforeTime k n) := by
    filter_upwards [hseparated] with n hn
    intro i k hik
    change c / inverse A (base n - N) ≤ integerDistance
      (clusterShiftedTimes (rawTime n) (fixedSteps.take j.castSucc) i -
        clusterShiftedTimes (rawTime n) (fixedSteps.take j.castSucc) k)
    rw [integerDistance_clusterShiftedTimes_sub]
    exact hn i k hik

  have hselectedStrict : ∀ᶠ n in atTop,
      ∀ i, i ≠ selected → beforeTime i n < beforeTime selected n := by
    filter_upwards [hprefixSeparated] with n hn
    intro i hi
    exact lt_of_le_of_ne (hselectedMaximum n i) (by
      intro heq
      have hzero := (le_integerDistance_iff.mp
        (hn selected i (Ne.symm hi))) 0
      rw [← heq, sub_self] at hzero
      norm_num at hzero
      exact (not_lt_of_ge hzero (div_pos hc (hA.inverse_pos _))))

  have hself : Tendsto (fun n ↦ u n / Real.log (u n)) atTop atTop := by
    let singletonTime : Fin 1 → ℕ → ℝ :=
      fun _ n ↦ beforeTime selected n - 1
    have horder : ∀ᶠ n in atTop,
        StrictAnti (fun i ↦ singletonTime i n) := by
      filter_upwards [] with n
      intro i k hik
      exact (ne_of_lt hik (Subsingleton.elim i k)).elim
    have hlower : ∀ᶠ n in atTop,
        base n - 0 ≤ singletonTime (Fin.last 0) n := by
      filter_upwards [] with n
      dsimp only [singletonTime]
      linarith [hselectedAbove n]
    have hwidth : ∀ᶠ n in atTop,
        singletonTime 0 n - singletonTime (Fin.last 0) n < 1 := by
      filter_upwards [] with n
      simp [singletonTime]
    have hsepOne : ∀ᶠ n in atTop,
        ∀ i k : Fin 1, i ≠ k →
          c / inverse A (base n - N) ≤
            integerDistance (singletonTime i n - singletonTime k n) := by
      filter_upwards [] with n
      intro i k hik
      exact (hik (Subsingleton.elim i k)).elim
    have h := hA.finite_cluster_smallest_div_log_largest_filter
      atTop base singletonTime 0 hc (by simpa using hN) hbaseTop horder
        hlower hwidth hsepOne
    simpa only [singletonTime, Function.iterate_zero_apply,
      Fin.last_zero, u, clusterBalancingStepValue, beforeTime] using h

  have hcoordinate : ∀ i : Fin (m + 1),
      Tendsto (fun n ↦ u n / Real.log (afterValue i n)) atTop atTop := by
    intro i
    by_cases hi : i = selected
    · subst i
      simpa only [afterValue, u, selected,
        clusterBalancingPrefixValue_succ_selected] using hself
    · have hpairOrder : ∀ᶠ n in atTop,
          base n - 1 ≤ beforeTime i n - 1 ∧
            beforeTime i n - 1 < beforeTime selected n - 1 := by
        filter_upwards [hselectedStrict] with n hn
        constructor
        · linarith [hbeforeLower n i]
        · linarith [hn i hi]
      have hpairGap : ∀ᶠ n in atTop,
          c / inverse A (base n - N) ≤
            (beforeTime selected n - 1) - (beforeTime i n - 1) := by
        filter_upwards [hprefixSeparated, hselectedStrict] with n hn hstrict
        have hdist := (le_integerDistance_iff.mp
          (hn selected i (Ne.symm hi))) 0
        have hpos : 0 < beforeTime selected n - beforeTime i n :=
          sub_pos.mpr (hstrict i hi)
        simp only [Int.cast_zero, sub_zero, abs_of_pos hpos] at hdist
        linarith
      have hpair := hA.hierarchy_separation_filter atTop base
        (fun n ↦ beforeTime selected n - 1)
        (fun n ↦ beforeTime i n - 1)
        (D := 1) (N := N) (c := c) hc (by norm_num; exact hN) hbaseTop
          hpairOrder hpairGap 1
      have hbeforeITop : Tendsto (beforeTime i) atTop atTop := by
        apply tendsto_atTop_mono' atTop _ hbaseTop
        filter_upwards [] with n
        exact hbeforeLower n i
      have hlogPos : ∀ᶠ n in atTop,
          0 < Real.log (inverse A (beforeTime i n)) := by
        have hinvTop := hA.inverse_tendsto_atTop.comp hbeforeITop
        have hlarge := hinvTop.eventually (eventually_gt_atTop 1)
        filter_upwards [hlarge] with n hn
        exact Real.log_pos hn
      apply tendsto_atTop_mono' atTop _ hpair
      filter_upwards [hlogPos] with n hlog
      have hlog_le : Real.log (inverse A (beforeTime i n)) ≤
          inverse A (beforeTime i n - 1) := by
        exact (hA.log_inverse_lt_previous (beforeTime i n)).le
      have hmono :
          inverse A (beforeTime selected n - 1) /
              inverse A (beforeTime i n - 1) ≤
            inverse A (beforeTime selected n - 1) /
              Real.log (inverse A (beforeTime i n)) := by
        exact div_le_div_of_nonneg_left (hA.inverse_pos _).le hlog
          hlog_le
      simpa only [afterValue,
        clusterBalancingPrefixValue_succ_of_ne rawTime fixedSteps j n hi,
        clusterBalancingPrefixValue, beforeTime, u,
        clusterBalancingStepValue, Real.rpow_one] using hmono

  apply Filter.tendsto_atTop.2
  intro C
  have hall : ∀ᶠ n in atTop, ∀ i : Fin (m + 1),
      C ≤ u n / Real.log (afterValue i n) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hcoordinate i).eventually (eventually_ge_atTop C)
  have huTwo : ∀ᶠ n in atTop, 2 ≤ u n :=
    huTop.eventually (eventually_ge_atTop 2)
  filter_upwards [hall, huTwo] with n hn hu
  obtain ⟨i, hi⟩ :=
    exists_clusterBalancingPrefixValue_eq_maximum
      A rawTime fixedSteps j.succ n
  have hmaxTwo : 2 ≤
      clusterBalancingPrefixMaximum A rawTime fixedSteps j.succ n := by
    calc
      2 ≤ u n := hu
      _ = afterValue selected n := by
        simp only [afterValue, u, selected,
          clusterBalancingPrefixValue_succ_selected]
      _ ≤ clusterBalancingPrefixMaximum A rawTime fixedSteps j.succ n :=
        clusterBalancingPrefixValue_le_maximum
          A rawTime fixedSteps j.succ n selected
  rw [clusterBalancingPrefixScale, max_eq_right hmaxTwo, ← hi]
  exact hn i

/-- One balancing decrement supplies both hierarchy records used by the
one-block quantitative transfer, with the canonical post- and pre-boundary
full-tuple scales. -/
theorem clusterBalancingStep_transferHierarchies
    {m : ℕ}
    (rawTime : ℕ → Fin (m + 1) → ℝ)
    (base : ℕ → ℝ)
    (plans : ∀ n, ClusterBalancingPlan (rawTime n) (base n))
    (fixedSteps : List (Fin (m + 1)))
    (hfixedSteps : ∀ n, (plans n).steps = fixedSteps)
    (j : Fin fixedSteps.length)
    {N c : ℝ} (hc : 0 < c) (hN : 5 ≤ N)
    (hbaseTop : Tendsto base atTop atTop)
    (hseparated : ∀ᶠ n in atTop,
      ∀ i k : Fin (m + 1), i ≠ k →
        c / inverse A (base n - N) ≤
          integerDistance (rawTime n i - rawTime n k)) :
    BalancedRealJetTransferHierarchy 0
        (fun _ n ↦ clusterBalancingStepValue A rawTime fixedSteps j n)
        (clusterBalancingPrefixScale A rawTime fixedSteps j.succ) ∧
      CrossClusterTransferScaleDomination 0
        (fun _ n ↦ clusterBalancingStepValue A rawTime fixedSteps j n)
        (clusterBalancingPrefixScale A rawTime fixedSteps j.succ)
        (clusterBalancingPrefixScale A rawTime fixedSteps j.castSucc) := by
  let selected : Fin (m + 1) := fixedSteps.get j
  let beforeTime : Fin (m + 1) → ℕ → ℝ :=
    clusterBalancingPrefixTime rawTime fixedSteps j.castSucc
  let u : ℕ → ℝ := clusterBalancingStepValue A rawTime fixedSteps j
  let Rscale : ℕ → ℝ :=
    clusterBalancingPrefixScale A rawTime fixedSteps j.succ
  let Xscale : ℕ → ℝ :=
    clusterBalancingPrefixScale A rawTime fixedSteps j.castSucc

  have hpostTime_le_preTime : ∀ n i,
      clusterBalancingPrefixTime rawTime fixedSteps j.succ i n ≤
        beforeTime i n := by
    intro n i
    change clusterShiftedTimes (rawTime n) (fixedSteps.take j.succ) i ≤
      clusterShiftedTimes (rawTime n) (fixedSteps.take j.castSucc) i
    rw [take_succ_eq_take_append_get]
    exact clusterShiftedTimes_append_le _ _ _ _
  have hpostValue_le_preValue : ∀ n i,
      clusterBalancingPrefixValue A rawTime fixedSteps j.succ i n ≤
        clusterBalancingPrefixValue A rawTime fixedSteps j.castSucc i n := by
    intro n i
    exact hA.inverse_strictMono.monotone (hpostTime_le_preTime n i)
  have hRleX : ∀ n, Rscale n ≤ Xscale n := by
    intro n
    apply max_le (two_le_clusterBalancingPrefixScale
      A rawTime fixedSteps j.castSucc n)
    obtain ⟨i, hi⟩ :=
      exists_clusterBalancingPrefixValue_eq_maximum
        A rawTime fixedSteps j.succ n
    rw [← hi]
    exact (hpostValue_le_preValue n i).trans
      (clusterBalancingPrefixValue_le_scale
        A rawTime fixedSteps j.castSucc n i)
  have hEu : ∀ n, E (u n) ≤ Xscale n := by
    intro n
    have hrecurrence : E
        (clusterBalancingStepValue A rawTime fixedSteps j n) =
        clusterBalancingPrefixValue A rawTime fixedSteps
          j.castSucc selected n := by
      unfold clusterBalancingStepValue clusterBalancingPrefixValue
      calc
        E (inverse A
            (clusterBalancingPrefixTime rawTime fixedSteps j.castSucc
              selected n - 1)) =
            inverse A
              ((clusterBalancingPrefixTime rawTime fixedSteps j.castSucc
                selected n - 1) + 1) := by
          symm
          simpa only [E] using
            hA.inverse_add_one
              (clusterBalancingPrefixTime rawTime fixedSteps j.castSucc
                selected n - 1)
        _ = inverse A
            (clusterBalancingPrefixTime rawTime fixedSteps j.castSucc
              selected n) := by congr 1; ring
    change E (clusterBalancingStepValue A rawTime fixedSteps j n) ≤
      clusterBalancingPrefixScale A rawTime fixedSteps j.castSucc n
    rw [hrecurrence]
    exact clusterBalancingPrefixValue_le_scale
      A rawTime fixedSteps j.castSucc n selected
  constructor
  · refine {
      positive := ?_
      order := ?_
      scale_ge_two := ?_
      adjacent_ratios := ?_
      smallest_div_log_scale := ?_ }
    · intro n i
      exact hA.inverse_pos _
    · filter_upwards [] with n
      change StrictAnti (fun _ : Fin 1 ↦ u n)
      intro i k hik
      exact (ne_of_lt hik (Subsingleton.elim i k)).elim
    · filter_upwards [] with n
      exact two_le_clusterBalancingPrefixScale
        A rawTime fixedSteps j.succ n
    · intro i
      exact Fin.elim0 i
    · exact hA.clusterBalancingStepValue_div_log_postScale_tendsto
        rawTime base plans fixedSteps hfixedSteps j hc hN hbaseTop hseparated
  · refine {
      scale_le := Filter.Eventually.of_forall hRleX
      target_ge_two := ?_
      exponential_le := ?_ }
    · filter_upwards [] with n
      exact two_le_clusterBalancingPrefixScale
        A rawTime fixedSteps j.castSucc n
    · filter_upwards [] with n
      intro i
      simpa only [u] using hEu n

end IsAbel

/-! ## Ordered-cluster specialization -/

namespace RepresentativeClusterSubsequence

/-- Canonical boundary scale for one ordered cluster after the simultaneous
balancing selector has fixed its subsequence and decrement list. -/
def orderedClusterBalancingPrefixScale
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (A : ℝ → ℝ) (φ : ℕ → ℕ)
    (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (r n : ℕ) : ℝ :=
  clusterBalancingPrefixScale A
    (fun q ↦ data.orderedClusterRawTime (φ q) c) fixedSteps r n

/-- Selected post-decrement representative for one fixed ordered-cluster
balancing step. -/
def orderedClusterBalancingStepValue
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (A : ℝ → ℝ) (φ : ℕ → ℕ)
    (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (j : Fin fixedSteps.length) (n : ℕ) : ℝ :=
  clusterBalancingStepValue A
    (fun q ↦ data.orderedClusterRawTime (φ q) c) fixedSteps j n

end RepresentativeClusterSubsequence

/-- Ordered-cluster form of the individual hierarchy bridge.  Its hypotheses
are exactly the outputs/inputs surrounding
`exists_fixed_orderedClusterBalancing_subsequence`: a fixed plan list for the
chosen cluster, divergence of its selected minimum along the further
subsequence, and the within-cluster separation estimate on its canonical
enumeration. -/
theorem IsAbel.orderedClusterBalancingStep_transferHierarchies
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (φ : ℕ → ℕ) (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (plans : ∀ n, ClusterBalancingPlan
      (data.orderedClusterRawTime (φ n) c)
      (data.orderedClusterMinTime c (φ n)))
    (hfixedSteps : ∀ n, (plans n).steps = fixedSteps)
    (j : Fin fixedSteps.length)
    {N separationConstant : ℝ}
    (hseparationConstant : 0 < separationConstant) (hN : 5 ≤ N)
    (hbaseTop : Tendsto
      (fun n ↦ data.orderedClusterMinTime c (φ n)) atTop atTop)
    (hseparated : ∀ᶠ n in atTop,
      ∀ i k : Fin (data.orderedClusterTailSize c + 1), i ≠ k →
        separationConstant /
            inverse A (data.orderedClusterMinTime c (φ n) - N) ≤
          integerDistance
            (data.orderedClusterRawTime (φ n) c i -
              data.orderedClusterRawTime (φ n) c k)) :
    BalancedRealJetTransferHierarchy 0
        (fun _ n ↦ data.orderedClusterBalancingStepValue
          A φ c fixedSteps j n)
        (data.orderedClusterBalancingPrefixScale
          A φ c fixedSteps j.succ) ∧
      CrossClusterTransferScaleDomination 0
        (fun _ n ↦ data.orderedClusterBalancingStepValue
          A φ c fixedSteps j n)
        (data.orderedClusterBalancingPrefixScale
          A φ c fixedSteps j.succ)
        (data.orderedClusterBalancingPrefixScale
          A φ c fixedSteps j.castSucc) := by
  exact hA.clusterBalancingStep_transferHierarchies
    (fun n ↦ data.orderedClusterRawTime (φ n) c)
    (fun n ↦ data.orderedClusterMinTime c (φ n))
    plans fixedSteps hfixedSteps j hseparationConstant hN hbaseTop hseparated

end AbelFormalization
