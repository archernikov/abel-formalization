import AbelFormalization.HermiteRankPreprocessedIndividualQuantitativeInputs
import AbelFormalization.TerminalLocalizationAnalyticAdapter
import AbelFormalization.HermiteRankBottomTerminalAnalyticLocalization
import AbelFormalization.OrderedClusterSimultaneousQuantitativeTransfer
import AbelFormalization.LowerDerivativeBounds
import AbelFormalization.HigherDerivatives
import AbelFormalization.Growth

/-!
# Concrete terminal evaluation inputs at the bottom Hermite cluster

The last simultaneous operation of ordered cluster zero is evaluated at its
literal post-log real-jet centers.  This module packages the numerical data
needed by `TerminalLocalizationAnalyticAdapter`: the translated bounded
parameter, retained Abel-time coordinates, the complete terminal symbol
assignment, their polynomial bounds, and inverse-square lower bounds for the
first derivatives.

Everything here is independent of the terminal localization identity.  An
arbitrary cofinal reindexing is allowed so the same tail can be shared with
the simultaneous Hermite jets; taking the identity map recovers the native
balancing subsequence exactly.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped Topology

variable {ι : Type*} {A : ℝ → ℝ} {m p a : ℕ} [Nonempty (Fin m)]

namespace RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

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

/-- Ordered cluster zero, which exists because the representative family is
nonempty. -/
abbrev bottomTerminalCluster
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i))) : Fin data.orderedClusterCount :=
  ⟨0, data.orderedClusterCount_pos_of_nonempty⟩

/-- The constant higher-derivative count used by the bottom cluster. -/
abbrev bottomTerminalHigher :
    Fin (data.orderedCluster
      (bottomTerminalCluster x data)).card → ℕ :=
  fun _ ↦ paperRankHermiteHigherCount boundary.S

/-- Number of retained simultaneous operations after the distinguished first
operation in the bottom cluster. -/
abbrev bottomTerminalExtraSteps : ℕ :=
  (boundary.preprocessed.descent.clusterStage
    (bottomTerminalCluster x data)).certificate.terminalized.extraSteps

/-- The already selected bottom-cluster Abel times, pulled back along a
common cofinal reindexing. -/
def bottomTerminalRawTime (φ : ℕ → ℕ) :
    ℕ → Fin (data.orderedClusterTailSize
      (bottomTerminalCluster x data) + 1) → ℝ :=
  fun n ↦ boundary.selectedClusterRawTime D representative offset radius Fsys
    x w₀ hw₀ data
      (bottomTerminalCluster x data) (φ n)

/-- The translated bounded parameter at which all analytic representatives
are evaluated. -/
def bottomTerminalParameter (φ : ℕ → ℕ) :
    ℕ → RestrictedBoxSpace p :=
  fun n ↦ (boundary.selectedTranslatedParameter D representative offset radius
    Fsys x w₀ hw₀ data (φ n)).2

/-- Post-log centers after the last simultaneous operation of the bottom
cluster. -/
def bottomTerminalCenter (φ : ℕ → ℕ) :
    Fin (data.orderedCluster
      (bottomTerminalCluster x data)).card → ℕ → ℝ :=
  data.orderedClusterSimultaneousPostLogScale
    (bottomTerminalCluster x data) A
    (boundary.bottomTerminalRawTime D representative offset radius Fsys x w₀
      hw₀ data φ)
    (boundary.preprocessed.fixedSteps
      (bottomTerminalCluster x data))
    (boundary.preprocessed.fixedOrder
      (bottomTerminalCluster x data))
    (boundary.bottomTerminalExtraSteps D representative offset radius Fsys x
      w₀ hw₀ data)

/-- The canonical output scale of the last simultaneous operation. -/
def bottomTerminalScale (φ : ℕ → ℕ) : ℕ → ℝ :=
  data.orderedClusterSimultaneousBoundaryScale
    (bottomTerminalCluster x data) A
    (boundary.bottomTerminalRawTime D representative offset radius Fsys x w₀
      hw₀ data φ)
    (boundary.preprocessed.fixedSteps
      (bottomTerminalCluster x data))
    (boundary.preprocessed.fixedOrder
      (bottomTerminalCluster x data))
    (boundary.bottomTerminalExtraSteps D representative offset radius Fsys x
      w₀ hw₀ data + 1)

/-- Retained time-coordinate values at the bottom terminal boundary. -/
def bottomTerminalTimeValue (φ : ℕ → ℕ)
    (i : Fin (data.orderedCluster
      (bottomTerminalCluster x data)).card) : ℕ → ℝ :=
  fun n ↦ A (boundary.bottomTerminalCenter D representative offset radius Fsys
    x w₀ hw₀ data φ i n)

/-- The complete terminal assignment: positive-order Abel derivatives in
each active block and the retained Abel-time coordinates. -/
def bottomTerminalSymbolValue (φ : ℕ → ℕ) :
    TerminalMultiblockSourceIndex
      (data.orderedCluster
        (bottomTerminalCluster x data)).card
      (boundary.bottomTerminalHigher D representative offset radius Fsys x w₀
        hw₀ data)
      (Fin (data.orderedCluster
        (bottomTerminalCluster x data)).card) → ℕ → ℝ :=
  fun z n ↦ realCentralTransferCentralValue A
    (fun i ↦ boundary.bottomTerminalCenter D representative offset radius Fsys
      x w₀ hw₀ data φ i n)
    (terminalTotalDerivativeCount
      (boundary.bottomTerminalHigher D representative offset radius Fsys x w₀
        hw₀ data)) z

/-- Every terminal center diverges after any cofinal reindexing. -/
theorem bottomTerminalCenter_tendsto_atTop
    (hA : IsAbel A) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (i : Fin (data.orderedCluster
      (bottomTerminalCluster x data)).card) :
    Tendsto
      (boundary.bottomTerminalCenter D representative offset radius Fsys x w₀
        hw₀ data φ i) atTop atTop := by
  let c := bottomTerminalCluster x data
  let e := data.orderedClusterBalancingToActiveEquiv c
  let shift : ℝ :=
    (boundary.bottomTerminalExtraSteps D representative offset radius Fsys x
      w₀ hw₀ data + 1 : ℕ)
  apply hA.inverse_tendsto_atTop.comp
  have hmin :=
    (boundary.selectedClusterMinTime_tendsto_atTop D representative offset
      radius Fsys x w₀ hw₀ data hA c).comp hφ
  have hminShift : Tendsto (fun n ↦
      data.orderedClusterMinTime c
        (boundary.preprocessed.balancingSubsequence (φ n)) - shift)
      atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hmin.eventually (eventually_ge_atTop (b + shift))] with n hn
    dsimp only [Function.comp_apply] at hn
    linarith
  apply tendsto_atTop_mono' atTop _ hminShift
  filter_upwards [] with n
  have hbase := (boundary.preprocessed.plans (φ n) c).base_le_final
    (boundary.preprocessed.fixedOrder c (e.symm i))
  have hsteps := boundary.preprocessed.plans_steps (φ n) c
  dsimp only [bottomTerminalCenter, bottomTerminalRawTime,
    RepresentativeClusterSubsequence.orderedClusterSimultaneousPostLogScale,
    RepresentativeClusterSubsequence.orderedClusterPostBalancingFinalOrderTime]
  change data.orderedClusterMinTime c
      (boundary.preprocessed.balancingSubsequence (φ n)) - shift ≤
    clusterShiftedTimes
      (data.orderedClusterRawTime
        (boundary.preprocessed.balancingSubsequence (φ n)) c)
      (boundary.preprocessed.fixedSteps c)
      (boundary.preprocessed.fixedOrder c (e.symm i)) - shift
  rw [← hsteps]
  exact sub_le_sub_right hbase shift

/-- The bounded analytic parameter still tends to the germ basepoint after
any common cofinal reindexing. -/
theorem bottomTerminalParameter_tendsto
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    Tendsto
      (boundary.bottomTerminalParameter D representative offset radius Fsys x
        w₀ hw₀ data φ) atTop (𝓝 (0 : RestrictedBoxSpace p)) := by
  exact (boundary.selectedTranslatedParameter_box_tendsto_zero D
    representative offset radius Fsys x w₀ hw₀ data).comp hφ

/-- Every terminal center is positive, without passing to a tail. -/
theorem bottomTerminalCenter_pos
    (hA : IsAbel A) (φ : ℕ → ℕ)
    (i : Fin (data.orderedCluster
      (bottomTerminalCluster x data)).card) (n : ℕ) :
    0 < boundary.bottomTerminalCenter D representative offset radius Fsys x
      w₀ hw₀ data φ i n := by
  exact hA.inverse_pos _

/-- The final-order maximum dominates every bottom terminal center. -/
theorem bottomTerminalCenter_le_scale
    (hA : IsAbel A) (φ : ℕ → ℕ)
    (i : Fin (data.orderedCluster
      (bottomTerminalCluster x data)).card) (n : ℕ) :
    boundary.bottomTerminalCenter D representative offset radius Fsys x w₀
        hw₀ data φ i n ≤
      boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ n := by
  let c := bottomTerminalCluster x data
  let e := data.orderedClusterBalancingToActiveEquiv c
  apply hA.inverse_strictMono.monotone
  apply sub_le_sub_right
  have horder :=
    (boundary.preprocessed.plans (φ n) c).antitone_finalTimes_comp_finalOrder
      (Fin.zero_le (e.symm i))
  have hsteps := boundary.preprocessed.plans_steps (φ n) c
  have hfinalOrder := boundary.preprocessed.plans_finalOrder (φ n) c
  dsimp only [ClusterBalancingPlan.finalTimes, Function.comp_apply] at horder
  rw [hsteps, hfinalOrder] at horder
  simpa only [bottomTerminalCenter, bottomTerminalScale,
    bottomTerminalRawTime,
    selectedClusterRawTime,
    RepresentativeClusterSubsequence.orderedClusterSimultaneousPostLogScale,
    RepresentativeClusterSubsequence.orderedClusterPostBalancingFinalOrderTime,
    RepresentativeClusterSubsequence.orderedClusterSimultaneousBoundaryScale,
    c, e] using horder

/-- The canonical terminal scale is the center in final position zero. -/
theorem bottomTerminalScale_eq_zeroCenter
    (φ : ℕ → ℕ) (n : ℕ) :
    boundary.bottomTerminalScale D representative offset radius Fsys x w₀ hw₀
        data φ n =
      boundary.bottomTerminalCenter D representative offset radius Fsys x w₀
        hw₀ data φ
          (data.orderedClusterBalancingToActiveEquiv
            (bottomTerminalCluster x data) 0) n := by
  symm
  exact data.orderedClusterSimultaneousPostLogScale_zero_eq_boundaryScale
    (bottomTerminalCluster x data) A
    (boundary.bottomTerminalRawTime D representative offset radius Fsys x w₀
      hw₀ data φ)
    (boundary.preprocessed.fixedSteps (bottomTerminalCluster x data))
    (boundary.preprocessed.fixedOrder (bottomTerminalCluster x data))
    (boundary.bottomTerminalExtraSteps D representative offset radius Fsys x
      w₀ hw₀ data) n

/-- The terminal output scale diverges along every common cofinal
reindexing. -/
theorem bottomTerminalScale_tendsto_atTop
    (hA : IsAbel A) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    Tendsto
      (boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ) atTop atTop := by
  apply (boundary.bottomTerminalCenter_tendsto_atTop D representative offset
    radius Fsys x w₀ hw₀ data hA hφ
      (data.orderedClusterBalancingToActiveEquiv
        (bottomTerminalCluster x data) 0)).congr'
  exact Filter.Eventually.of_forall fun n ↦
    (boundary.bottomTerminalScale_eq_zeroCenter D representative offset radius
      Fsys x w₀ hw₀ data φ n).symm

/-- The terminal output scale is eventually at least one. -/
theorem bottomTerminalScale_eventually_ge_one
    (hA : IsAbel A) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    ∀ᶠ n in atTop,
      1 ≤ boundary.bottomTerminalScale D representative offset radius Fsys x
        w₀ hw₀ data φ n :=
  (boundary.bottomTerminalScale_tendsto_atTop D representative offset radius
    Fsys x w₀ hw₀ data hA hφ).eventually (eventually_ge_atTop 1)

/-- Every retained bottom terminal time coordinate diverges. -/
theorem bottomTerminalTimeValue_tendsto_atTop
    (hA : IsAbel A) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (i : Fin (data.orderedCluster
      (bottomTerminalCluster x data)).card) :
    Tendsto
      (boundary.bottomTerminalTimeValue D representative offset radius Fsys x
        w₀ hw₀ data φ i) atTop atTop := by
  exact hA.tendsto_atTop.comp
    (boundary.bottomTerminalCenter_tendsto_atTop D representative offset radius
      Fsys x w₀ hw₀ data hA hφ i)

/-- In particular, the retained coordinate selected by the nonzero bottom
polynomial diverges. -/
theorem bottomTerminalBottomTime_tendsto_atTop
    (hA : IsAbel A) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    Tendsto
      (boundary.bottomTerminalTimeValue D representative offset radius Fsys x
        w₀ hw₀ data φ boundary.preprocessed.bottomIndex) atTop atTop :=
  boundary.bottomTerminalTimeValue_tendsto_atTop D representative offset radius
    Fsys x w₀ hw₀ data hA hφ boundary.preprocessed.bottomIndex

/-- On a tail, an Abel time is at most its positive inverse-Abel value. -/
theorem eventually_self_le_inverse {A : ℝ → ℝ} (hA : IsAbel A) :
    ∀ᶠ s : ℝ in atTop, s ≤ inverse A s := by
  obtain ⟨threshold, hthreshold⟩ := eventually_affine_lower_bound
    hA.inverse_strictMono.monotone hA.inverse_add_one
    ⟨A 2, by rw [hA.inverse_apply (by norm_num : (0 : ℝ) < 2)]⟩ 0
  filter_upwards [eventually_ge_atTop threshold] with s hs
  have h := hthreshold s hs
  linarith

/-- Every retained Abel-time coordinate has a linear polynomial upper bound
in the canonical terminal scale. -/
theorem bottomTerminalTimeValue_hasPolynomialUpperBound
    (hA : IsAbel A) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (i : Fin (data.orderedCluster
      (bottomTerminalCluster x data)).card) :
    HasPolynomialUpperBound atTop
      (boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ)
      (boundary.bottomTerminalTimeValue D representative offset radius Fsys x
        w₀ hw₀ data φ i) := by
  refine ⟨1, zero_lt_one, 1, ?_⟩
  have htimeTop := boundary.bottomTerminalTimeValue_tendsto_atTop D
    representative offset radius Fsys x w₀ hw₀ data hA hφ i
  have hself := htimeTop.eventually (eventually_self_le_inverse hA)
  have hpositive := htimeTop.eventually (eventually_gt_atTop 0)
  filter_upwards [hself, hpositive] with n hle hpos
  rw [abs_of_pos hpos, one_mul, pow_one]
  calc
    boundary.bottomTerminalTimeValue D representative offset radius Fsys x w₀
        hw₀ data φ i n ≤
        inverse A (boundary.bottomTerminalTimeValue D representative offset
          radius Fsys x w₀ hw₀ data φ i n) := hle
    _ = boundary.bottomTerminalCenter D representative offset radius Fsys x w₀
        hw₀ data φ i n := by
      exact hA.inverse_apply
        (boundary.bottomTerminalCenter_pos D representative offset radius Fsys
          x w₀ hw₀ data hA φ i n)
    _ ≤ boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ n :=
      boundary.bottomTerminalCenter_le_scale D representative offset radius
        Fsys x w₀ hw₀ data hA φ i n

/-- The first derivative in every active block has the inverse-square lower
bound dictated by the canonical terminal scale. -/
theorem bottomTerminalDerivative_hasScalarInversePowerLowerBound
    (hA : IsAbel A) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (i : Fin (data.orderedCluster
      (bottomTerminalCluster x data)).card) :
    HasScalarInversePowerLowerBound atTop
      (boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ)
      (fun n ↦ deriv A
        (boundary.bottomTerminalCenter D representative offset radius Fsys x
          w₀ hw₀ data φ i n)) := by
  refine ⟨1, zero_lt_one, 2, ?_⟩
  have hderiv :=
    (boundary.bottomTerminalCenter_tendsto_atTop D representative offset radius
      Fsys x w₀ hw₀ data hA hφ i).eventually
        hA.eventually_deriv_ge_rpow_neg_two
  filter_upwards [hderiv] with n hn
  have hu : 0 < boundary.bottomTerminalCenter D representative offset radius
      Fsys x w₀ hw₀ data φ i n :=
    boundary.bottomTerminalCenter_pos D representative offset radius Fsys x w₀
      hw₀ data hA φ i n
  have hus : boundary.bottomTerminalCenter D representative offset radius Fsys
      x w₀ hw₀ data φ i n ≤
        boundary.bottomTerminalScale D representative offset radius Fsys x w₀
          hw₀ data φ n :=
    boundary.bottomTerminalCenter_le_scale D representative offset radius Fsys
      x w₀ hw₀ data hA φ i n
  have hsquare :
      (boundary.bottomTerminalCenter D representative offset radius Fsys x w₀
        hw₀ data φ i n) ^ 2 ≤
      (boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ n) ^ 2 :=
    pow_le_pow_left₀ hu.le hus 2
  rw [abs_of_pos (hA.deriv_pos _ hu), one_div]
  calc
    ((boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ n) ^ 2)⁻¹ ≤
        ((boundary.bottomTerminalCenter D representative offset radius Fsys x
          w₀ hw₀ data φ i n) ^ 2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le
        (pow_pos hu 2) hsquare
    _ = (boundary.bottomTerminalCenter D representative offset radius Fsys x
          w₀ hw₀ data φ i n) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hu.le]
      norm_num [Real.rpow_two]
    _ ≤ deriv A
        (boundary.bottomTerminalCenter D representative offset radius Fsys x
          w₀ hw₀ data φ i n) := hn

/-- The complete terminal assignment is polynomially bounded coordinate by
coordinate.  Positive derivatives are actually bounded because they tend to
zero; retained times have the linear bound above. -/
theorem bottomTerminalSymbolValue_hasPolynomialUpperBound
    (hA : IsAbel A) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (z : TerminalMultiblockSourceIndex
      (data.orderedCluster (bottomTerminalCluster x data)).card
      (boundary.bottomTerminalHigher D representative offset radius Fsys x w₀
        hw₀ data)
      (Fin (data.orderedCluster (bottomTerminalCluster x data)).card)) :
    HasPolynomialUpperBound atTop
      (boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ)
      (boundary.bottomTerminalSymbolValue D representative offset radius Fsys x
        w₀ hw₀ data φ z) := by
  rcases z with z | i
  · rcases z with ⟨i, r⟩
    have htendsto := (hA.tendsto_iteratedDeriv_atTop (r.val + 1)
      (Nat.succ_le_succ (Nat.zero_le r.val))).comp
        (boundary.bottomTerminalCenter_tendsto_atTop D representative offset
          radius Fsys x w₀ hw₀ data hA hφ i)
    apply (HasPolynomialUpperBound.of_tendsto htendsto :
      HasPolynomialUpperBound atTop
        (boundary.bottomTerminalScale D representative offset radius Fsys x
          w₀ hw₀ data φ)
        (fun n ↦ iteratedDeriv (r.val + 1) A
          (boundary.bottomTerminalCenter D representative offset radius Fsys x
            w₀ hw₀ data φ i n))).congr
    intro n
    rfl
  · change HasPolynomialUpperBound atTop
      (boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ)
      (boundary.bottomTerminalTimeValue D representative offset radius Fsys x
        w₀ hw₀ data φ i)
    exact boundary.bottomTerminalTimeValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data hA hφ i

/-- The first-derivative projection expected by the analytic localization
adapter inherits the concrete inverse-square lower bound. -/
theorem bottomTerminalFirstDerivative_hasScalarInversePowerLowerBound
    (hA : IsAbel A) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (i : Fin (data.orderedCluster
      (bottomTerminalCluster x data)).card) :
    HasScalarInversePowerLowerBound atTop
      (boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ)
      (TerminalGeneratorBackwardIdentity.AnalyticRepresentativeData.firstDerivativeValue
        (boundary.bottomTerminalSymbolValue D representative offset radius Fsys
          x w₀ hw₀ data φ) i) := by
  have hvalue :
      TerminalGeneratorBackwardIdentity.AnalyticRepresentativeData.firstDerivativeValue
          (boundary.bottomTerminalSymbolValue D representative offset radius
            Fsys x w₀ hw₀ data φ) i =
        fun n ↦ deriv A
          (boundary.bottomTerminalCenter D representative offset radius Fsys x
            w₀ hw₀ data φ i n) := by
    funext n
    change iteratedDeriv 1 A
        (boundary.bottomTerminalCenter D representative offset radius Fsys x w₀
          hw₀ data φ i n) = _
    rw [iteratedDeriv_one]
  rw [hvalue]
  exact boundary.bottomTerminalDerivative_hasScalarInversePowerLowerBound D
    representative offset radius Fsys x w₀ hw₀ data hA hφ i

/-- Adapter-ready numerical facts at the bottom terminal boundary.  The
functions themselves are the canonical definitions above; this record stores
exactly the convergence and quantitative properties consumed by analytic
terminal localization. -/
structure BottomTerminalEvaluationInputs
    (hA : IsAbel A) (φ : ℕ → ℕ) : Prop where
  reindex_tendsto : Tendsto φ atTop atTop
  parameter_tendsto : Tendsto
    (boundary.bottomTerminalParameter D representative offset radius Fsys x w₀
      hw₀ data φ) atTop (𝓝 (0 : RestrictedBoxSpace p))
  center_tendsto : ∀ i, Tendsto
    (boundary.bottomTerminalCenter D representative offset radius Fsys x w₀
      hw₀ data φ i) atTop atTop
  scale_tendsto : Tendsto
    (boundary.bottomTerminalScale D representative offset radius Fsys x w₀ hw₀
      data φ) atTop atTop
  scale_ge_one : ∀ᶠ n in atTop,
    1 ≤ boundary.bottomTerminalScale D representative offset radius Fsys x w₀
      hw₀ data φ n
  center_le_scale : ∀ i n,
    boundary.bottomTerminalCenter D representative offset radius Fsys x w₀ hw₀
        data φ i n ≤
      boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ n
  time_coordinate_bound : ∀ i, HasPolynomialUpperBound atTop
    (boundary.bottomTerminalScale D representative offset radius Fsys x w₀ hw₀
      data φ)
    (boundary.bottomTerminalTimeValue D representative offset radius Fsys x w₀
      hw₀ data φ i)
  bottom_time_tendsto : Tendsto
    (boundary.bottomTerminalTimeValue D representative offset radius Fsys x w₀
      hw₀ data φ boundary.preprocessed.bottomIndex) atTop atTop
  symbol_bound : ∀ z, HasPolynomialUpperBound atTop
    (boundary.bottomTerminalScale D representative offset radius Fsys x w₀ hw₀
      data φ)
    (boundary.bottomTerminalSymbolValue D representative offset radius Fsys x
      w₀ hw₀ data φ z)
  first_derivative_lower : ∀ i, HasScalarInversePowerLowerBound atTop
    (boundary.bottomTerminalScale D representative offset radius Fsys x w₀ hw₀
      data φ)
    (TerminalGeneratorBackwardIdentity.AnalyticRepresentativeData.firstDerivativeValue
      (boundary.bottomTerminalSymbolValue D representative offset radius Fsys x
        w₀ hw₀ data φ) i)

/-- Construct the complete terminal input package after any common cofinal
reindexing. -/
theorem bottomTerminalEvaluationInputs_of_tendsto
    (hA : IsAbel A) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    boundary.BottomTerminalEvaluationInputs D representative offset radius Fsys
      x w₀ hw₀ data hA φ where
  reindex_tendsto := hφ
  parameter_tendsto :=
    boundary.bottomTerminalParameter_tendsto D representative offset radius
      Fsys x w₀ hw₀ data hφ
  center_tendsto := fun i ↦
    boundary.bottomTerminalCenter_tendsto_atTop D representative offset radius
      Fsys x w₀ hw₀ data hA hφ i
  scale_tendsto :=
    boundary.bottomTerminalScale_tendsto_atTop D representative offset radius
      Fsys x w₀ hw₀ data hA hφ
  scale_ge_one :=
    boundary.bottomTerminalScale_eventually_ge_one D representative offset
      radius Fsys x w₀ hw₀ data hA hφ
  center_le_scale := fun i n ↦
    boundary.bottomTerminalCenter_le_scale D representative offset radius Fsys
      x w₀ hw₀ data hA φ i n
  time_coordinate_bound := fun i ↦
    boundary.bottomTerminalTimeValue_hasPolynomialUpperBound D representative
      offset radius Fsys x w₀ hw₀ data hA hφ i
  bottom_time_tendsto :=
    boundary.bottomTerminalBottomTime_tendsto_atTop D representative offset
      radius Fsys x w₀ hw₀ data hA hφ
  symbol_bound := fun z ↦
    boundary.bottomTerminalSymbolValue_hasPolynomialUpperBound D representative
      offset radius Fsys x w₀ hw₀ data hA hφ z
  first_derivative_lower := fun i ↦
    boundary.bottomTerminalFirstDerivative_hasScalarInversePowerLowerBound D
      representative offset radius Fsys x w₀ hw₀ data hA hφ i

/-- Native, unshifted bottom terminal inputs.  These are definitionally
aligned with the current concrete simultaneous-step data. -/
theorem bottomTerminalEvaluationInputs_id (hA : IsAbel A) :
    boundary.BottomTerminalEvaluationInputs D representative offset radius Fsys
      x w₀ hw₀ data hA id :=
  boundary.bottomTerminalEvaluationInputs_of_tendsto D representative offset
    radius Fsys x w₀ hw₀ data hA tendsto_id

/-- Terminal inputs on a shared natural tail. -/
theorem bottomTerminalEvaluationInputs_add (hA : IsAbel A) (N : ℕ) :
    boundary.BottomTerminalEvaluationInputs D representative offset radius Fsys
      x w₀ hw₀ data hA (fun n ↦ n + N) := by
  apply boundary.bottomTerminalEvaluationInputs_of_tendsto D representative
    offset radius Fsys x w₀ hw₀ data hA
  simpa only [Nat.add_comm] using tendsto_add_atTop_nat N

/-- Feed the concrete bottom terminal assignment directly into the finite
analytic terminal-localization bridge.  The localization identity and all
coefficient bounds are supplied internally by the existing analytic adapter. -/
theorem BottomTerminalEvaluationInputs.terminalSourceValue_lower
    {hA : IsAbel A} {φ : ℕ → ℕ}
    (inputs : boundary.BottomTerminalEvaluationInputs D representative offset
      radius Fsys x w₀ hw₀ data hA φ)
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData) :
    HasInversePowerLowerBound atTop
      (boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ)
      ((boundary.preprocessed.bottomTerminalAnalyticChangeData localization).sourceValue
        (boundary.bottomTerminalParameter D representative offset radius Fsys x
          w₀ hw₀ data φ)
        (boundary.bottomTerminalSymbolValue D representative offset radius Fsys
          x w₀ hw₀ data φ)) := by
  apply boundary.preprocessed.bottomTerminalSourceValue_lower localization
    (boundary.bottomTerminalParameter D representative offset radius Fsys x w₀
      hw₀ data φ)
    (boundary.bottomTerminalSymbolValue D representative offset radius Fsys x
      w₀ hw₀ data φ)
    inputs.parameter_tendsto inputs.scale_ge_one inputs.symbol_bound
  · change Tendsto
      (boundary.bottomTerminalTimeValue D representative offset radius Fsys x
        w₀ hw₀ data φ boundary.preprocessed.bottomIndex) atTop atTop
    exact inputs.bottom_time_tendsto
  · intro i
    have hvalue :
        TerminalGeneratorBackwardIdentity.AnalyticRepresentativeData.firstDerivativeValue
            (boundary.bottomTerminalSymbolValue D representative offset radius
              Fsys x w₀ hw₀ data φ) i =
          fun n ↦ boundary.bottomTerminalSymbolValue D representative offset
            radius Fsys x w₀ hw₀ data φ
              (Sum.inl ⟨i, (0 : Fin
                (paperRankHermiteHigherCount boundary.S + 1))⟩) n := rfl
    rw [← hvalue]
    exact inputs.first_derivative_lower i

/-- Concrete localized terminal source-family lower bound after any common
cofinal reindexing. -/
theorem bottomTerminalSourceValue_lower_of_tendsto
    (hA : IsAbel A) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData) :
    HasInversePowerLowerBound atTop
      (boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data φ)
      ((boundary.preprocessed.bottomTerminalAnalyticChangeData localization).sourceValue
        (boundary.bottomTerminalParameter D representative offset radius Fsys x
          w₀ hw₀ data φ)
        (boundary.bottomTerminalSymbolValue D representative offset radius Fsys
          x w₀ hw₀ data φ)) :=
  BottomTerminalEvaluationInputs.terminalSourceValue_lower D representative
    offset radius Fsys x w₀ hw₀ data boundary
    (boundary.bottomTerminalEvaluationInputs_of_tendsto D representative offset
      radius Fsys x w₀ hw₀ data hA hφ) localization

/-- Native unshifted localized terminal source-family lower bound, aligned
definitionally with the simultaneous real-jet sequence. -/
theorem bottomTerminalSourceValue_lower_id
    (hA : IsAbel A)
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData) :
    HasInversePowerLowerBound atTop
      (boundary.bottomTerminalScale D representative offset radius Fsys x w₀
        hw₀ data id)
      ((boundary.preprocessed.bottomTerminalAnalyticChangeData localization).sourceValue
        (boundary.bottomTerminalParameter D representative offset radius Fsys x
          w₀ hw₀ data id)
        (boundary.bottomTerminalSymbolValue D representative offset radius Fsys
          x w₀ hw₀ data id)) :=
  boundary.bottomTerminalSourceValue_lower_of_tendsto D representative offset
    radius Fsys x w₀ hw₀ data hA tendsto_id localization

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
