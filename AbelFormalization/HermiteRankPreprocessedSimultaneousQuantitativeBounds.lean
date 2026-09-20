import AbelFormalization.HermiteRankPreprocessedSimultaneousAnalyticData

/-!
# Polynomial bounds for the concrete Hermite simultaneous segment

The finite analytic construction leaves three families of coordinate bounds:
the first mixed source assignment, the exact assignment after every retained
operation, and the error-free main assignment.  They all follow from the
existing Hermite boundary and Abel asymptotic data.

Positive Abel derivatives tend to zero.  Abel times grow at most
logarithmically, while the final-order position zero dominates every active
center.  Smaller-prefix Hermite coordinates are controlled by the divergent
gap from every earlier ordered cluster to the active cluster.  Consequently
the complete finite analytic simultaneous segment has a canonical choice with
no additional numeric hypotheses.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

namespace RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

variable {ι : Type*} {A : ℝ → ℝ} {m p a : ℕ} [Nonempty (Fin m)]
variable (D : RestrictedBox p)
variable (representative : ι → Fin m)
variable (offset : ι → D.analyticNearClosedBoxSubalgebra)
variable (radius : ℝ)
variable (Fsys : Fin (m + p + a) → RestrictedSource m p a → ℝ)
variable (x : ℕ → RestrictedSource m p a)
variable (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
variable (data : RepresentativeClusterSubsequence
  (fun n i ↦ A ((x n).1.1 i)))
variable (boundary : RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
  D representative offset radius Fsys x w₀ hw₀ data)

/-! ## Active simultaneous centers -/

/-- Every post-log center still diverges after the common quantitative
reindexing. -/
theorem simultaneousQuantitativePostLogScale_tendsto_atTop
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (i : Fin (data.orderedCluster c).card) :
    Tendsto
      (boundary.simultaneousQuantitativePostLogScale D representative offset
        radius Fsys x w₀ hw₀ data hA c r i) atTop atTop := by
  exact (boundary.simultaneousNumericPostLogScale_tendsto_atTop D
    representative offset radius Fsys x w₀ hw₀ data hA c r i).comp
      (boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
        offset radius Fsys x w₀ hw₀ data hA)

/-- Every post-log center is positive. -/
theorem simultaneousQuantitativePostLogScale_pos
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (i : Fin (data.orderedCluster c).card) (n : ℕ) :
    0 < boundary.simultaneousQuantitativePostLogScale D representative offset
      radius Fsys x w₀ hw₀ data hA c r i n :=
  hA.inverse_pos _

/-- Final-order position zero dominates every post-log active center. -/
theorem simultaneousQuantitativePostLogScale_le_boundaryScale
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (i : Fin (data.orderedCluster c).card) (n : ℕ) :
    boundary.simultaneousQuantitativePostLogScale D representative offset
        radius Fsys x w₀ hw₀ data hA c r i n ≤
      boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r + 1) n := by
  let e := data.orderedClusterBalancingToActiveEquiv c
  apply hA.inverse_strictMono.monotone
  apply sub_le_sub_right
  have horder :=
    (boundary.preprocessed.plans
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n) c).antitone_finalTimes_comp_finalOrder
      (Fin.zero_le (e.symm i))
  have hsteps := boundary.preprocessed.plans_steps
    (boundary.simultaneousQuantitativeReindex D representative offset radius
      Fsys x w₀ hw₀ data hA n) c
  have hfinalOrder := boundary.preprocessed.plans_finalOrder
    (boundary.simultaneousQuantitativeReindex D representative offset radius
      Fsys x w₀ hw₀ data hA n) c
  dsimp only [ClusterBalancingPlan.finalTimes, Function.comp_apply] at horder
  rw [hsteps, hfinalOrder] at horder
  simpa only [simultaneousQuantitativePostLogScale,
    simultaneousQuantitativeBoundaryScale, simultaneousQuantitativeRawTime,
    simultaneousNumericRawTime, selectedClusterRawTime,
    RepresentativeClusterSubsequence.orderedClusterSimultaneousPostLogScale,
    RepresentativeClusterSubsequence.orderedClusterPostBalancingFinalOrderTime,
    RepresentativeClusterSubsequence.orderedClusterSimultaneousBoundaryScale,
    e] using horder

/-- Each active post-log center has a linear bound by its canonical next
boundary scale. -/
theorem simultaneousQuantitativePostLogScale_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (i : Fin (data.orderedCluster c).card) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r + 1))
      (boundary.simultaneousQuantitativePostLogScale D representative offset
        radius Fsys x w₀ hw₀ data hA c r i) := by
  refine ⟨1, by norm_num, 1, ?_⟩
  filter_upwards [] with n
  rw [abs_of_pos (boundary.simultaneousQuantitativePostLogScale_pos D
    representative offset radius Fsys x w₀ hw₀ data hA c r i n), pow_one,
    one_mul]
  exact boundary.simultaneousQuantitativePostLogScale_le_boundaryScale D
    representative offset radius Fsys x w₀ hw₀ data hA c r i n

/-! ## Central and main values -/

/-- Every exact central coordinate at operation `r` is polynomially bounded
by simultaneous boundary `r+1`.  Positive derivatives are bounded because
they converge to zero; the Abel-time coordinate uses the logarithmic growth
bound. -/
theorem simultaneousQuantitativeCentralValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (z : CentralPolynomialIndex (Fin (data.orderedCluster c).card)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S))
      (Fin (data.orderedCluster c).card)) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r + 1))
      (fun n ↦ realCentralTransferCentralValue A
        (fun i ↦ boundary.simultaneousQuantitativePostLogScale D representative
          offset radius Fsys x w₀ hw₀ data hA c r i n)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster c).card ↦
            paperRankHermiteHigherCount boundary.S)) z) := by
  rcases z with br | i
  · rcases br with ⟨i, q⟩
    apply (HasPolynomialUpperBound.of_tendsto
      ((hA.tendsto_iteratedDeriv_atTop (q.val + 1)
        (Nat.succ_le_succ (Nat.zero_le q.val))).comp
          (boundary.simultaneousQuantitativePostLogScale_tendsto_atTop D
            representative offset radius Fsys x w₀ hw₀ data hA c r i))).congr
    intro n
    rfl
  · exact abelValue_hasPolynomialUpperBound_of_center_le_scale hA
      (boundary.simultaneousQuantitativePostLogScale D representative offset
        radius Fsys x w₀ hw₀ data hA c r i)
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r + 1))
      (boundary.simultaneousQuantitativePostLogScale_tendsto_atTop D
        representative offset radius Fsys x w₀ hw₀ data hA c r i)
      (Filter.Eventually.of_forall fun n ↦
        boundary.simultaneousQuantitativePostLogScale_le_boundaryScale D
          representative offset radius Fsys x w₀ hw₀ data hA c r i n)
      (boundary.simultaneousQuantitativeBoundaryScale_eventually_ge_one D
        representative offset radius Fsys x w₀ hw₀ data hA c (r + 1))

/-- Literal-cardinality version of the finite Stirling bound for the
error-free main assignment. -/
theorem finiteRealJetMainAssignment_hasPolynomialUpperBound_of_central
    {h : ℕ} (A : ℝ → ℝ) (u : Fin h → ℕ → ℝ) (d : Fin h → ℕ)
    (scale : ℕ → ℝ) (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hcentral : ∀ z : CentralPolynomialIndex (Fin h) d (Fin h),
      HasPolynomialUpperBound atTop scale
        (fun n ↦ realCentralTransferCentralValue A (fun i ↦ u i n) d z))
    (z : ClusterOperationSymbol (Fin h) d) :
    HasPolynomialUpperBound atTop scale
      (finiteRealJetMainAssignment A u d z) := by
  rcases z with i | z
  · apply (HasPolynomialUpperBound.one atTop scale).congr
    intro n
    rfl
  · rcases z with br | i
    · rcases br with ⟨i, r⟩
      have hsum := HasPolynomialUpperBound.finset_sum hscale Finset.univ
        (fun j : Fin (d i) ↦ fun n ↦
          (if j ≤ r then
              (signedStirling (r.val + 1) (j.val + 1) : ℝ)
            else 0) * iteratedDeriv (j.val + 1) A (u i n))
        (fun j _ ↦
          (HasPolynomialUpperBound.const atTop scale
            (if j ≤ r then
                (signedStirling (r.val + 1) (j.val + 1) : ℝ)
              else 0)).mul (hcentral (Sum.inl ⟨i, j⟩)))
      apply hsum.congr
      intro n
      simp only [finiteRealJetMainAssignment, realCentralTransferMainValue,
        realCentralStirlingJet_eq_fin_sum]
    · apply ((hcentral (Sum.inr i)).add hscale
        (HasPolynomialUpperBound.one atTop scale)).congr
      intro n
      rfl

/-- The complete error-free main assignment has its required operationwise
bound. -/
theorem simultaneousQuantitativeMainValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c)
    (z : boundary.SimultaneousAnalyticActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r.val + 1))
      (finiteRealJetMainAssignment A
        (boundary.simultaneousQuantitativePostLogScale D representative offset
          radius Fsys x w₀ hw₀ data hA c r.val)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster c).card ↦
            paperRankHermiteHigherCount boundary.S)) z) := by
  exact finiteRealJetMainAssignment_hasPolynomialUpperBound_of_central A
    (boundary.simultaneousQuantitativePostLogScale D representative offset
      radius Fsys x w₀ hw₀ data hA c r.val)
    (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S))
    (boundary.simultaneousQuantitativeBoundaryScale D representative offset
      radius Fsys x w₀ hw₀ data hA c (r.val + 1))
    (boundary.simultaneousQuantitativeBoundaryScale_eventually_ge_one D
      representative offset radius Fsys x w₀ hw₀ data hA c (r.val + 1))
    (boundary.simultaneousQuantitativeCentralValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data hA c r.val) z

/-! ## Smaller-prefix Hermite values -/

/-- A center belonging to the smaller ordered prefix is copied from the
selected parameter and therefore diverges on the common tail. -/
theorem simultaneousQuantitativeSmallerPrefixCenter_tendsto_atTop
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (b : data.OrderedClusterPrefixBlock c.val) :
    Tendsto (fun n ↦
      (boundary.simultaneousPreLogParameter D representative offset radius Fsys
        x w₀ hw₀ data c r
        (boundary.simultaneousQuantitativeReindex D representative offset radius
          Fsys x w₀ hw₀ data hA n)).1 b.1) atTop atTop := by
  have hnot := orderedClusterPrefixBlock_not_mem_active
    (x := x) (data := data) (c := c) (b := b)
  have hselected := (boundary.selected_representative_tendsto b.1).comp
    (boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
      offset radius Fsys x w₀ hw₀ data hA)
  apply hselected.congr'
  filter_upwards with n
  simpa [simultaneousPreLogParameter, hnot, selectedIndex]

/-- Every earlier-cluster center is eventually smaller than any fixed
simultaneous boundary of the active cluster. -/
theorem simultaneousQuantitativeSmallerPrefixCenter_le_boundaryScale
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r s : ℕ)
    (b : data.OrderedClusterPrefixBlock c.val) :
    ∀ᶠ n in atTop,
      (boundary.simultaneousPreLogParameter D representative offset radius Fsys
          x w₀ hw₀ data c r
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA n)).1 b.1 ≤
        boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c s n := by
  obtain ⟨d, hd, hb⟩ := b.2
  let active : Fin (data.orderedClusterTailSize c + 1) :=
    boundary.preprocessed.fixedOrder c 0
  let center : ℕ → ℝ := fun n ↦
    (boundary.simultaneousPreLogParameter D representative offset radius Fsys x
      w₀ hw₀ data c r
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n)).1 b.1
  let higher : ℕ → ℝ := fun n ↦ data.orderedClusterRawTime
    (boundary.preprocessed.balancingSubsequence
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n)) c active
  let lower : ℕ → ℝ := fun n ↦ A (center n)
  let shift : ℕ := (boundary.preprocessed.fixedSteps c).count active + s
  have hreindex : Tendsto (fun n ↦ boundary.preprocessed.balancingSubsequence
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n)) atTop atTop :=
    boundary.preprocessed.balancingSubsequence_strictMono.tendsto_atTop.comp
      (boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
        offset radius Fsys x w₀ hw₀ data hA)
  have hgap0 := data.tendsto_orderedCluster_gap_atTop hd hb
    (data.orderedClusterEnumeration_mem c active)
  have hnot := orderedClusterPrefixBlock_not_mem_active
    (x := x) (data := data) (c := c) (b := b)
  have hgap : Tendsto (fun n ↦ higher n - lower n) atTop atTop := by
    apply (hgap0.comp hreindex).congr'
    filter_upwards with n
    dsimp only [Function.comp_apply, higher, lower, center]
    rw [show
      (boundary.simultaneousPreLogParameter D representative offset radius Fsys
          x w₀ hw₀ data c r
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA n)).1 b.1 =
        (boundary.selectedTranslatedParameter D representative offset radius
          Fsys x w₀ hw₀ data
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA n)).1 b.1 by
      simp only [simultaneousPreLogParameter, hnot, dite_false]]
    rfl
  have hcenterTop : Tendsto center atTop atTop :=
    boundary.simultaneousQuantitativeSmallerPrefixCenter_tendsto_atTop D
      representative offset radius Fsys x w₀ hw₀ data hA c r b
  have hlower : Tendsto lower atTop atTop := hA.tendsto_atTop.comp hcenterTop
  have hdom := hA.eventually_exp_iterate_inverse_sub_nat_lt_of_gap hgap hlower
    shift 0 0
  have hpositive : ∀ᶠ n in atTop, 0 < center n :=
    hcenterTop.eventually (eventually_gt_atTop 0)
  filter_upwards [hdom, hpositive] with n hn hnpositive
  have hn' : center n < inverse A (higher n - (shift : ℝ)) := by
    simpa only [Function.iterate_zero_apply, Nat.cast_zero, sub_zero, lower,
      hA.inverse_apply hnpositive] using hn
  calc
    (boundary.simultaneousPreLogParameter D representative offset radius Fsys x
        w₀ hw₀ data c r
        (boundary.simultaneousQuantitativeReindex D representative offset radius
          Fsys x w₀ hw₀ data hA n)).1 b.1 = center n := rfl
    _ ≤ inverse A (higher n - (shift : ℝ)) := hn'.le
    _ = boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c s n := by
      unfold simultaneousQuantitativeBoundaryScale
        RepresentativeClusterSubsequence.orderedClusterSimultaneousBoundaryScale
      dsimp only [simultaneousQuantitativeRawTime, simultaneousNumericRawTime,
        selectedClusterRawTime, higher, shift, active]
      congr 1
      unfold clusterShiftedTimes
      push_cast
      ring

/-- Every concrete smaller-prefix Hermite coordinate is polynomially bounded
at every simultaneous boundary. -/
theorem simultaneousQuantitativeAnalyticPrefixValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r s : ℕ)
    (z : boundary.SimultaneousAnalyticPrefixSymbol D representative offset
      radius Fsys x w₀ hw₀ data c) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c s)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r z) := by
  let φ := boundary.simultaneousQuantitativeReindex D representative offset
    radius Fsys x w₀ hw₀ data hA
  let sw : ℕ → PaperRankParameterSpace m p := fun n ↦
    boundary.simultaneousPreLogParameter D representative offset radius Fsys x
      w₀ hw₀ data c r (φ n)
  let scale := boundary.simultaneousQuantitativeBoundaryScale D representative
    offset radius Fsys x w₀ hw₀ data hA c s
  rcases z with b | z
  · refine ⟨1, by norm_num, 1, ?_⟩
    have hpositive : ∀ᶠ n in atTop, 0 < (sw n).1 b.1 :=
      (boundary.simultaneousQuantitativeSmallerPrefixCenter_tendsto_atTop D
        representative offset radius Fsys x w₀ hw₀ data hA c r b).eventually
          (eventually_gt_atTop 0)
    have hle :=
      boundary.simultaneousQuantitativeSmallerPrefixCenter_le_boundaryScale D
        representative offset radius Fsys x w₀ hw₀ data hA c r s b
    filter_upwards [hpositive, hle] with n hnpositive hnle
    change |(sw n).1 b.1| ≤ 1 * scale n ^ (1 : ℕ)
    rw [abs_of_pos hnpositive, pow_one, one_mul]
    exact hnle
  · rcases z with br | b
    · rcases br with ⟨b, q⟩
      apply (hermiteCoefficientValue_hasPolynomialUpperBound
        (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset)
        (boundary.commonRealHermiteData D representative offset radius Fsys x
          w₀ hw₀ data hA).fullHermite
        boundary.B_pos sw b.1
        (finCongr (paperRankHermiteHigherCount_add_one boundary.S) q).succ
        scale
        (boundary.simultaneousQuantitativeBoundaryScale_eventually_ge_one D
          representative offset radius Fsys x w₀ hw₀ data hA c s)
        (boundary.simultaneousQuantitativeSmallerPrefixCenter_tendsto_atTop D
          representative offset radius Fsys x w₀ hw₀ data hA c r b)
        (boundary.simultaneousQuantitativeSmallerPrefixCenter_le_boundaryScale D
          representative offset radius Fsys x w₀ hw₀ data hA c r s b)
        (fun n k ↦ by
          rw [boundary.simultaneousPreLogParameter_box D representative offset
            radius Fsys x w₀ hw₀ data c r (φ n)]
          exact boundary.selectedTranslatedOffset_bound D representative offset
            radius Fsys x w₀ hw₀ data (φ n) k)).congr
      intro n
      rfl
    · apply (hermiteCoefficientValue_hasPolynomialUpperBound
        (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset)
        (boundary.commonRealHermiteData D representative offset radius Fsys x
          w₀ hw₀ data hA).fullHermite
        boundary.B_pos sw b.1 0 scale
        (boundary.simultaneousQuantitativeBoundaryScale_eventually_ge_one D
          representative offset radius Fsys x w₀ hw₀ data hA c s)
        (boundary.simultaneousQuantitativeSmallerPrefixCenter_tendsto_atTop D
          representative offset radius Fsys x w₀ hw₀ data hA c r b)
        (boundary.simultaneousQuantitativeSmallerPrefixCenter_le_boundaryScale D
          representative offset radius Fsys x w₀ hw₀ data hA c r s b)
        (fun n k ↦ by
          rw [boundary.simultaneousPreLogParameter_box D representative offset
            radius Fsys x w₀ hw₀ data c r (φ n)]
          exact boundary.selectedTranslatedOffset_bound D representative offset
            radius Fsys x w₀ hw₀ data (φ n) k)).congr
      intro n
      rfl

/-! ## First mixed source assignment -/

/-- The terminal mixed individual assignment remains polynomially bounded
after inserting the simultaneous common tail and changing to the equal first
simultaneous scale. -/
theorem individualMixedTerminalSymbolValueOnSimultaneousTail_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (z : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedTerminalSymbolValueOnSimultaneousTail D
        representative offset radius Fsys x w₀ hw₀ data hA c z) := by
  let q := boundary.individualMixedTerminalBoundaryIndex D representative offset
    radius Fsys x w₀ hw₀ data c
  let shift : ℕ → ℕ := fun n ↦
    n + boundary.simultaneousQuantitativeTail D representative offset radius
      Fsys x w₀ hw₀ data hA
  have hshift : Tendsto shift atTop atTop := by
    simpa only [shift, Nat.add_comm] using tendsto_add_atTop_nat
      (boundary.simultaneousQuantitativeTail D representative offset radius Fsys
        x w₀ hw₀ data hA)
  have hbound :=
    (boundary.individualMixedBoundarySymbolValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data hA c q z).comp_tendsto
        shift hshift
  obtain ⟨C, hC, P, hbound⟩ := hbound
  refine ⟨C, hC, P, ?_⟩
  have hscaleEventually :=
    boundary.simultaneousQuantitativeBoundaryScale_zero_eventuallyEq_individualMixedTerminal
      D representative offset radius Fsys x w₀ hw₀ data hA c
  filter_upwards [hbound, hscaleEventually] with n hn hscaleEq
  rw [hscaleEq]
  simpa only [Function.comp_apply, shift,
    individualMixedTerminalSymbolValueOnSimultaneousTail,
    individualNumericBoundaryScale, q] using hn

/-- The terminal active assignment in final simultaneous order inherits the
coordinatewise terminal mixed bounds. -/
theorem individualMixedTerminalFinalActiveValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (z : boundary.SimultaneousAnalyticActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedTerminalFinalActiveValue D representative offset
        radius Fsys x w₀ hw₀ data hA c z) := by
  exact boundary.individualMixedTerminalSymbolValueOnSimultaneousTail_hasPolynomialUpperBound
    D representative offset radius Fsys x w₀ hw₀ data hA c
    (boundary.individualMixedTerminalFinalActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c z)

/-- The first simultaneous pre-log active assignment is bounded through its
exact terminal individual compatibility. -/
theorem simultaneousFirstMixedActiveValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (z : boundary.SimultaneousAnalyticActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.simultaneousFirstMixedActiveValue D representative offset radius
        Fsys x w₀ hw₀ data hA c z) := by
  apply (boundary.individualMixedTerminalFinalActiveValue_hasPolynomialUpperBound
    D representative offset radius Fsys x w₀ hw₀ data hA c z).congr
  intro n
  exact (congrFun (congrFun
    (boundary.individualMixedTerminalFinalActiveValue_eq_simultaneousFirstMixed
      D representative offset radius Fsys x w₀ hw₀ data hA c) z) n).symm

/-- Undoing the source translation changes only a free coordinate from
`E u` to `exp u = E u + 1`, so the literal first source assignment is also
bounded. -/
theorem simultaneousQuantitativeAnalyticSourceValue_first_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (z : boundary.SimultaneousAnalyticActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
        offset radius Fsys x w₀ hw₀ data hA c
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.firstCentralStepIndex z) := by
  rcases z with i | z
  · apply ((boundary.simultaneousFirstMixedActiveValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data hA c (Sum.inl i)).add
        (boundary.simultaneousQuantitativeBoundaryScale_eventually_ge_one D
          representative offset radius Fsys x w₀ hw₀ data hA c 0)
        (HasPolynomialUpperBound.one atTop
          (boundary.simultaneousQuantitativeBoundaryScale D representative
            offset radius Fsys x w₀ hw₀ data hA c 0))).congr
    intro n
    simp [simultaneousQuantitativeAnalyticSourceValue,
      simultaneousFirstMixedActiveValue, finiteRealJetActualAssignment,
      simultaneousCentralPreLogActiveAssignment, realCentralTransferActualValue,
      E]
    have hfirst :
        ((boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.firstCentralStepIndex).val + 1 = 1 := rfl
    unfold simultaneousQuantitativePostLogScale
      RepresentativeClusterSubsequence.orderedClusterSimultaneousPostLogScale
    simpa only [hfirst, Nat.cast_one]
  · apply (boundary.simultaneousFirstMixedActiveValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data hA c (Sum.inr z)).congr
    intro n
    rfl

/-- The full outer/inner source assignment at operation zero has its required
boundary-zero bound. -/
theorem simultaneousQuantitativeAnalyticSourceSymbolValue_first_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (z : boundary.SimultaneousAnalyticActiveSymbol D representative offset
        radius Fsys x w₀ hw₀ data c ⊕
      boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
        Fsys x w₀ hw₀ data c) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D
        representative offset radius Fsys x w₀ hw₀ data hA c
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.firstCentralStepIndex z) := by
  rcases z with z | z
  · exact boundary.simultaneousQuantitativeAnalyticSourceValue_first_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c z
  · exact boundary.simultaneousQuantitativeAnalyticPrefixValue_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c 0 0 z

/-! ## Exact following assignments and canonical segment -/

/-- The exact active assignment following operation `r` is polynomially
bounded by boundary `r+1`. -/
theorem simultaneousQuantitativeAnalyticAfterValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (z : boundary.SimultaneousAnalyticActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r + 1))
      (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r z) := by
  rcases z with i | z
  · apply ((boundary.simultaneousQuantitativePostLogScale_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c r i).add
        (boundary.simultaneousQuantitativeBoundaryScale_eventually_ge_one D
          representative offset radius Fsys x w₀ hw₀ data hA c (r + 1))
        (HasPolynomialUpperBound.one atTop
          (boundary.simultaneousQuantitativeBoundaryScale D representative
            offset radius Fsys x w₀ hw₀ data hA c (r + 1)))).congr
    intro n
    simp only [simultaneousQuantitativeAnalyticAfterValue,
      finiteRealJetActualAssignment, realCentralTransferActualValue]
    rw [boundary.simultaneousQuantitativePostLogScale_eq_E_succ D
      representative offset radius Fsys x w₀ hw₀ data hA c r i n]
    simp only [E]
    ring
  · apply (boundary.simultaneousQuantitativeCentralValue_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c r z).congr
    intro n
    exact boundary.simultaneousQuantitativeAnalyticAfterValue_central D
      representative offset radius Fsys x w₀ hw₀ data hA c r z n

/-- The combined exact-successor and smaller-prefix assignment after every
retained operation has its required bound. -/
theorem simultaneousQuantitativeAnalyticAfterSymbolValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c)
    (z : boundary.SimultaneousAnalyticActiveSymbol D representative offset
        radius Fsys x w₀ hw₀ data c ⊕
      boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
        Fsys x w₀ hw₀ data c) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r.val + 1))
      (boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D
        representative offset radius Fsys x w₀ hw₀ data hA c r.val z) := by
  rcases z with z | z
  · exact boundary.simultaneousQuantitativeAnalyticAfterValue_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c r.val z
  · exact boundary.simultaneousQuantitativeAnalyticPrefixValue_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c r.val
        (r.val + 1) z

/-- The canonical finite analytic simultaneous segment, with every residual
coordinate bound discharged from the recovered Hermite data. -/
noncomputable def simultaneousQuantitativeFiniteAnalyticSegmentData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D representative
      offset radius Fsys x w₀ hw₀ data hA c :=
  boundary.simultaneousQuantitativeFiniteAnalyticSegmentDataOfBounds D
    representative offset radius Fsys x w₀ hw₀ data hA c
    (boundary.simultaneousQuantitativeAnalyticSourceSymbolValue_first_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c)
    (boundary.simultaneousQuantitativeAnalyticAfterSymbolValue_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c)
    (boundary.simultaneousQuantitativeMainValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data hA c)

/-- Existence form of the unconditional canonical segment constructor. -/
theorem nonempty_simultaneousQuantitativeFiniteAnalyticSegmentData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    Nonempty
      (boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
        representative offset radius Fsys x w₀ hw₀ data hA c) :=
  ⟨boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D representative
    offset radius Fsys x w₀ hw₀ data hA c⟩

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
