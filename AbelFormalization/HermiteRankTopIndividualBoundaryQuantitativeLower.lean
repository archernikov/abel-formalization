import AbelFormalization.FiniteAnalyticChangeOfGenerators
import AbelFormalization.HermiteRankOneClusterBackwardPropagation
import AbelFormalization.HermiteRankTopPrefixLowerContradiction

/-!
# The highest individual boundary reaches the Hermite top prefix

After backward propagation through every ordered cluster, the remaining
finite family is boundary zero of the individual trace in the highest
cluster.  Algebraically this is the initial top-prefix ideal.  This module
uses a finite analytic change of generators to replace that family by the
canonical padded Hermite top-prefix generators, then removes the two fixed
quantitative tails and invokes the existing top-prefix contradiction.

No sequence-valued evaluation homomorphism on all analytic germs is used.
The sole residual analytic compatibility is generatorwise and numeric: on
the common tail, the representatives selected by the finite analytic change
must evaluate to the already selected padded top-prefix representatives.
All coefficient representatives, their polynomial bounds, the boundary-side
representative comparison, and the change-of-generators identity are derived
inside this module.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter Set
open scoped Topology

universe u

namespace RepresentativeClusterSubsequence

/-- A dependent preprocessed descent which has reached the top prefix carries
the original initial ideal.  This small endpoint lemma avoids treating the
highest-cluster boundary as a separate algebraic compatibility assumption. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.stageIdeal_eq_initial_of_eq_count
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} {hk : k ≤ data.orderedClusterCount}
    {stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal k hk stageIdeal)
    (hktop : k = data.orderedClusterCount) :
    stageIdeal = hktop.symm ▸ initialIdeal := by
  cases descent with
  | top =>
      cases hktop
      rfl
  | @step k hk nextIdeal tail certificate =>
      omega

end RepresentativeClusterSubsequence

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

noncomputable local instance topIndividualBoundaryBlockDecidableEq
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-! ## The literal highest-cluster ideal -/

/-- Transport the literal top-prefix ideal to the definitionally equal ring
at prefix `c + 1`.  The equality hypothesis records that `c` is the highest
ordered cluster. -/
def topPrefixIdealAtLastCluster
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) :
    Ideal (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
      (paperRankHermiteHigherCount boundary.S) (c.val + 1)) :=
  hc.symm ▸ data.paperRankHermiteTopPrefixIdeal
    (RealAnalyticGerm p) boundary.S boundary.I

/-- The canonical padded top-prefix generators, transported to the highest
cluster's prefix-ring presentation. -/
def topPrefixPaddedGeneratorAtLastCluster
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) :
    Fin (boundary.generatorCount + 1) →
      data.OrderedClusterPrefixRing (RealAnalyticGerm p)
        (paperRankHermiteHigherCount boundary.S) (c.val + 1) :=
  fun j ↦ hc.symm ▸
    data.paperRankHermiteTopPrefixPaddedGenerator boundary.S
      boundary.generator j

/-- The span calculation before specializing the prefix index to a `Fin`
cluster.  Keeping `k` independent is essential for dependent elimination:
the equality `k = orderedClusterCount` can then be eliminated without also
transporting a term of `Fin orderedClusterCount`. -/
theorem topPrefixPaddedGeneratorAtIndex_span
    (k : ℕ) (hk : k = data.orderedClusterCount) :
    Ideal.span (Set.range (fun j ↦ hk.symm ▸
        data.paperRankHermiteTopPrefixPaddedGenerator boundary.S
          boundary.generator j)) =
      (hk.symm ▸ data.paperRankHermiteTopPrefixIdeal
        (RealAnalyticGerm p) boundary.S boundary.I) := by
  subst k
  exact boundary.paddedTopPrefix_span

/-- Transporting the canonical padded family preserves its literal span. -/
theorem topPrefixPaddedGeneratorAtLastCluster_span
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) :
    Ideal.span (Set.range
        (boundary.topPrefixPaddedGeneratorAtLastCluster D representative offset
          radius Fsys x w₀ hw₀ data c hc)) =
      boundary.topPrefixIdealAtLastCluster D representative offset radius Fsys
        x w₀ hw₀ data c hc := by
  exact boundary.topPrefixPaddedGeneratorAtIndex_span D representative offset
    radius Fsys x w₀ hw₀ data (c.val + 1) hc

/-- The incoming ideal of the highest cluster is the original literal
top-prefix ideal, with only the dependent prefix index transported. -/
theorem lastCluster_preprocessingInput_eq_topPrefixIdeal
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) :
    (boundary.preprocessed.descent.clusterStage c).preprocessingInput =
      boundary.topPrefixIdealAtLastCluster D representative offset radius Fsys
        x w₀ hw₀ data c hc := by
  exact
    (boundary.preprocessed.descent.clusterStage c).tail
      |>.stageIdeal_eq_initial_of_eq_count hc

/-- Boundary zero of the highest individual trace is the transported literal
top-prefix ideal. -/
theorem lastCluster_individualBoundaryZeroIdeal_eq_topPrefixIdeal
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) :
    individualCentralIdealBoundary (RealAnalyticGerm p)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        (boundary.individualNumericSteps D representative offset radius Fsys x
          w₀ hw₀ data c)
        (boundary.preprocessed.descent.clusterStage c).preprocessingInput 0 =
      boundary.topPrefixIdealAtLastCluster D representative offset radius Fsys
        x w₀ hw₀ data c hc := by
  rw [individualCentralIdealBoundary_zero]
  exact boundary.lastCluster_preprocessingInput_eq_topPrefixIdeal D
    representative offset radius Fsys x w₀ hw₀ data c hc

/-- The highest individual boundary-zero family lies in the span of the
canonical padded top-prefix family. -/
theorem lastCluster_individualBoundaryZero_span_le_topPrefixPadded
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) :
    Ideal.span (Set.range
        (boundary.individualNumericBoundaryFamily D representative offset
          radius Fsys x w₀ hw₀ data c 0).generator) ≤
      Ideal.span (Set.range
        (boundary.topPrefixPaddedGeneratorAtLastCluster D representative offset
          radius Fsys x w₀ hw₀ data c hc)) := by
  rw [(boundary.individualNumericBoundaryFamily D representative offset radius
      Fsys x w₀ hw₀ data c 0).span_eq,
    boundary.topPrefixPaddedGeneratorAtLastCluster_span D representative offset
      radius Fsys x w₀ hw₀ data c hc,
    boundary.lastCluster_individualBoundaryZeroIdeal_eq_topPrefixIdeal D
      representative offset radius Fsys x w₀ hw₀ data c hc]

/-! ## Finite analytic change and the common tail -/

/-- Finite analytic representatives and a coefficient matrix changing from
the canonical padded top-prefix family to the highest individual boundary-zero
family. -/
noncomputable def topIndividualBoundaryAnalyticChange
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) :
    FiniteAnalyticChangeOfGeneratorsData
      (0 : RestrictedBoxSpace p)
      (boundary.topPrefixPaddedGeneratorAtLastCluster D representative offset
        radius Fsys x w₀ hw₀ data c hc)
      (boundary.individualNumericBoundaryFamily D representative offset radius
        Fsys x w₀ hw₀ data c 0).generator :=
  finiteAnalyticChangeOfGeneratorsDataOfSpan (0 : RestrictedBoxSpace p)
    (boundary.topPrefixPaddedGeneratorAtLastCluster D representative offset
      radius Fsys x w₀ hw₀ data c hc)
    (boundary.individualNumericBoundaryFamily D representative offset radius
      Fsys x w₀ hw₀ data c 0).generator
    (boundary.lastCluster_individualBoundaryZero_span_le_topPrefixPadded D
      representative offset radius Fsys x w₀ hw₀ data c hc)

/-- Total fixed shift already present in a boundary-zero value on the common
individual/simultaneous quantitative tail. -/
def topIndividualCommonTail (hA : IsAbel A) : ℕ :=
  boundary.simultaneousQuantitativeTail D representative offset radius Fsys x
      w₀ hw₀ data hA +
    boundary.individualQuantitativeTail D representative offset radius Fsys x
      w₀ hw₀ data hA

/-- The selected balancing-subsequence index used by the highest individual
boundary on the common tail. -/
def topIndividualCommonSelectedIndex (hA : IsAbel A) (n : ℕ) : ℕ :=
  individualSimultaneousTailShift D representative offset radius Fsys x w₀
      hw₀ data boundary hA n +
    boundary.individualQuantitativeTail D representative offset radius Fsys x
      w₀ hw₀ data hA

@[simp]
theorem topIndividualCommonSelectedIndex_eq_add_tail
    (hA : IsAbel A) (n : ℕ) :
    boundary.topIndividualCommonSelectedIndex D representative offset radius
        Fsys x w₀ hw₀ data hA n =
      n + boundary.topIndividualCommonTail D representative offset radius Fsys
        x w₀ hw₀ data hA := by
  unfold topIndividualCommonSelectedIndex topIndividualCommonTail
    individualSimultaneousTailShift
  omega

/-- The additional simultaneous tail is a cofinal reindexing of `atTop`. -/
theorem topIndividualSimultaneousTailShift_tendsto_atTop
    (hA : IsAbel A) :
    Tendsto
      (individualSimultaneousTailShift D representative offset radius Fsys x
        w₀ hw₀ data boundary hA) atTop atTop := by
  change Tendsto (fun n ↦ n +
    boundary.simultaneousQuantitativeTail D representative offset radius Fsys x
      w₀ hw₀ data hA) atTop atTop
  exact tendsto_add_atTop_nat
    (boundary.simultaneousQuantitativeTail D representative offset radius Fsys x
      w₀ hw₀ data hA)

/-- Analytic parameter used by boundary zero after adding the simultaneous
tail. -/
def topIndividualBoundaryParameterOnCommonTail
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (n : ℕ) :
    RestrictedBoxSpace p :=
  (boundary.individualMixedAnalyticBoundaryData D representative offset radius
    Fsys x w₀ hw₀ data hA c).parameter
      (individualSimultaneousTailShift D representative offset radius Fsys x
        w₀ hw₀ data boundary hA n)

/-- Mixed symbol assignment used by boundary zero on the same tail. -/
def topIndividualBoundarySymbolValueOnCommonTail
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)) → ℕ → ℝ :=
  fun z n ↦
    (boundary.individualMixedAnalyticBoundaryData D representative offset radius
      Fsys x w₀ hw₀ data hA c).symbolValue 0 z
        (individualSimultaneousTailShift D representative offset radius Fsys x
          w₀ hw₀ data boundary hA n)

/-- The self-representative values of the highest individual boundary-zero
family, written directly through its analytic boundary package. -/
def topIndividualBoundaryZeroValueOnCommonTail
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :=
  fun b n ↦
    (boundary.individualMixedAnalyticBoundaryData D representative offset radius
      Fsys x w₀ hw₀ data hA c).boundaryValue 0 b
        (individualSimultaneousTailShift D representative offset radius Fsys x
          w₀ hw₀ data boundary hA n)

@[simp]
theorem topIndividualBoundaryZeroValueOnCommonTail_eq_mixed
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (b) (n : ℕ) :
    boundary.topIndividualBoundaryZeroValueOnCommonTail D representative offset
        radius Fsys x w₀ hw₀ data hA c b n =
      boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0 b n :=
  rfl

/-- The common-tail analytic parameter still tends to the germ base point. -/
theorem topIndividualBoundaryParameterOnCommonTail_tendsto
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    Tendsto
      (boundary.topIndividualBoundaryParameterOnCommonTail D representative
        offset radius Fsys x w₀ hw₀ data hA c)
      atTop (nhds (0 : RestrictedBoxSpace p)) := by
  change Tendsto (fun n ↦
    (boundary.individualMixedAnalyticBoundaryData D representative offset radius
      Fsys x w₀ hw₀ data hA c).parameter
        (individualSimultaneousTailShift D representative offset radius Fsys x
          w₀ hw₀ data boundary hA n)) atTop
      (nhds (0 : RestrictedBoxSpace p))
  exact
    (boundary.individualMixedAnalyticBoundaryData D representative offset radius
      Fsys x w₀ hw₀ data hA c).parameter_tendsto.comp
        (boundary.topIndividualSimultaneousTailShift_tendsto_atTop D
          representative offset radius Fsys x w₀ hw₀ data hA)

/-- Boundary-zero symbols retain their polynomial upper bounds after the
additional simultaneous tail. -/
theorem topIndividualBoundarySymbolValueOnCommonTail_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (z : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))) :
    HasPolynomialUpperBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.topIndividualBoundarySymbolValueOnCommonTail D representative
        offset radius Fsys x w₀ hw₀ data hA c z) := by
  let shift := individualSimultaneousTailShift D representative offset radius
    Fsys x w₀ hw₀ data boundary hA
  have hshift : Tendsto shift atTop atTop :=
    boundary.topIndividualSimultaneousTailShift_tendsto_atTop D representative
      offset radius Fsys x w₀ hw₀ data hA
  have hbound :=
    ((boundary.individualMixedAnalyticBoundaryData D representative offset
      radius Fsys x w₀ hw₀ data hA c).symbol_bound 0 z).comp_tendsto
        shift hshift
  change HasPolynomialUpperBound atTop
    ((boundary.individualNumericBoundaryScale D representative offset radius
      Fsys x w₀ hw₀ data hA c 0) ∘ shift)
    (((boundary.individualMixedAnalyticBoundaryData D representative offset
      radius Fsys x w₀ hw₀ data hA c).symbolValue 0 z) ∘ shift)
  exact hbound

/-- The highest boundary-zero scale is at least one on the common tail. -/
theorem topIndividualBoundaryZeroScaleOnCommonTail_ge_one
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ∀ᶠ n in atTop, 1 ≤
      boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0 n := by
  let shift := individualSimultaneousTailShift D representative offset radius
    Fsys x w₀ hw₀ data boundary hA
  have hshift : Tendsto shift atTop atTop :=
    boundary.topIndividualSimultaneousTailShift_tendsto_atTop D representative
      offset radius Fsys x w₀ hw₀ data hA
  have hge := hshift.eventually
    ((boundary.individualMixedAnalyticBoundaryData D representative offset
      radius Fsys x w₀ hw₀ data hA c).scale_ge_one 0)
  change ∀ᶠ n in atTop, 1 ≤
    boundary.individualNumericBoundaryScale D representative offset radius Fsys
      x w₀ hw₀ data hA c 0 (shift n)
  exact hge

/-- Independently selected representatives of the same boundary-zero
generators agree eventually. -/
theorem eventually_topIndividualBoundaryZeroValue_eq_changeTarget
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) :
    ∀ᶠ n in atTop, ∀ b,
      boundary.topIndividualBoundaryZeroValueOnCommonTail D representative
          offset radius Fsys x w₀ hw₀ data hA c b n =
        (boundary.topIndividualBoundaryAnalyticChange D representative offset
          radius Fsys x w₀ hw₀ data c hc).targetValue
          (boundary.topIndividualBoundaryParameterOnCommonTail D representative
            offset radius Fsys x w₀ hw₀ data hA c)
          (boundary.topIndividualBoundarySymbolValueOnCommonTail D
            representative offset radius Fsys x w₀ hw₀ data hA c) b n := by
  let analytic := boundary.individualMixedAnalyticBoundaryData D representative
    offset radius Fsys x w₀ hw₀ data hA c
  let self := analytic.boundarySelfChange 0
  let change := boundary.topIndividualBoundaryAnalyticChange D representative
    offset radius Fsys x w₀ hw₀ data c hc
  let parameter := boundary.topIndividualBoundaryParameterOnCommonTail D
    representative offset radius Fsys x w₀ hw₀ data hA c
  have hparameter := boundary.topIndividualBoundaryParameterOnCommonTail_tendsto
    D representative offset radius Fsys x w₀ hw₀ data hA c
  have hrepresentative : ∀ᶠ n in atTop, ∀ b,
      self.sourceRepresentative b (parameter n) =
        change.targetRepresentative b (parameter n) := by
    apply Filter.eventually_all.mpr
    intro b
    exact hparameter.eventually
      (analyticPolynomialRepresentatives_eventually_eq
        (0 : RestrictedBoxSpace p) (self.source_germ_eq b)
        (change.target_germ_eq b) rfl)
  filter_upwards [hrepresentative] with n hn
  intro b
  change MvPolynomial.eval
      (fun z ↦
        boundary.topIndividualBoundarySymbolValueOnCommonTail D representative
          offset radius Fsys x w₀ hw₀ data hA c z n)
      (self.sourceRepresentative b (parameter n)) =
    MvPolynomial.eval
      (fun z ↦
        boundary.topIndividualBoundarySymbolValueOnCommonTail D representative
          offset radius Fsys x w₀ hw₀ data hA c z n)
      (change.targetRepresentative b (parameter n))
  rw [hn b]

/-- Numeric values of the literal selected padded top-prefix representatives. -/
def selectedPaddedTopPrefixNumericValue
    (j : Fin (boundary.generatorCount + 1)) (n : ℕ) : ℝ :=
  MvPolynomial.eval
    (data.paperRankHermiteTopPrefixAssignment boundary.S
      (boundary.selectedTopPrefixRetainedAssignment D representative offset
        radius Fsys x w₀ hw₀ data n))
    (data.paperRankHermiteTopPrefixPaddedRepresentative boundary.S
      boundary.representativePolynomial j
      (boundary.selectedTopPrefixBoxParameter D representative offset radius
        Fsys x w₀ hw₀ data n))

/-- The only residual top-boundary analytic seam.  It identifies evaluation
of the canonical padded generators chosen by the finite analytic adapter with
the literal selected Hermite representatives at the same common-tail index.
It contains no change-matrix coefficients or quantitative bounds. -/
structure TopIndividualSelectedPaddedCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) : Prop where
  source_eq_selected : ∀ᶠ n in atTop, ∀ j,
    (boundary.topIndividualBoundaryAnalyticChange D representative offset
      radius Fsys x w₀ hw₀ data c hc).sourceValue
        (boundary.topIndividualBoundaryParameterOnCommonTail D representative
          offset radius Fsys x w₀ hw₀ data hA c)
        (boundary.topIndividualBoundarySymbolValueOnCommonTail D representative
          offset radius Fsys x w₀ hw₀ data hA c) j n =
      boundary.selectedPaddedTopPrefixNumericValue D representative offset
        radius Fsys x w₀ hw₀ data j
        (boundary.topIndividualCommonSelectedIndex D representative offset
          radius Fsys x w₀ hw₀ data hA n)

/-! ## Quantitative transport and contradiction -/

/-- The unshifted incoming scale at boundary zero of cluster `c`. -/
def topIndividualBoundaryZeroScale
    (c : Fin data.orderedClusterCount) : ℕ → ℝ :=
  data.orderedClusterIndividualBoundaryScale A
    boundary.preprocessed.balancingSubsequence c
    (boundary.preprocessed.fixedSteps c) 0

@[simp]
theorem individualMixedBoundaryScaleOnSimultaneousTail_zero_eq_topScale
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (n : ℕ) :
    boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0 n =
      boundary.topIndividualBoundaryZeroScale D representative offset radius
        Fsys x w₀ hw₀ data c
        (boundary.topIndividualCommonSelectedIndex D representative offset
          radius Fsys x w₀ hw₀ data hA n) := by
  rfl

/-- The unshifted highest boundary-zero scale is uniformly at least one. -/
theorem topIndividualBoundaryZeroScale_ge_one
    (c : Fin data.orderedClusterCount) :
    ∀ᶠ n in atTop, 1 ≤
      boundary.topIndividualBoundaryZeroScale D representative offset radius
        Fsys x w₀ hw₀ data c n := by
  exact Filter.Eventually.of_forall fun n ↦ one_le_two.trans
    (two_le_clusterBalancingPrefixScale A
      (fun k ↦ data.orderedClusterRawTime
        (boundary.preprocessed.balancingSubsequence k) c)
      (boundary.preprocessed.fixedSteps c) 0 n)

/-- The finite analytic adapter transports the boundary-zero lower bound to
its chosen canonical padded-source representatives on the common tail. -/
theorem topIndividualAnalyticSource_lower_of_mixedBoundaryZero_lower
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount)
    (hincoming : HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)) :
    HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      ((boundary.topIndividualBoundaryAnalyticChange D representative offset
        radius Fsys x w₀ hw₀ data c hc).sourceValue
          (boundary.topIndividualBoundaryParameterOnCommonTail D representative
            offset radius Fsys x w₀ hw₀ data hA c)
          (boundary.topIndividualBoundarySymbolValueOnCommonTail D
            representative offset radius Fsys x w₀ hw₀ data hA c)) := by
  let change := boundary.topIndividualBoundaryAnalyticChange D representative
    offset radius Fsys x w₀ hw₀ data c hc
  have hboundary : HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.topIndividualBoundaryZeroValueOnCommonTail D representative
        offset radius Fsys x w₀ hw₀ data hA c) := by
    exact hincoming.congr_of_eventually
      (Filter.Eventually.of_forall fun n b ↦
        (boundary.topIndividualBoundaryZeroValueOnCommonTail_eq_mixed D
          representative offset radius Fsys x w₀ hw₀ data hA c b n).symm)
  have htarget := hboundary.congr_of_eventually
    (boundary.eventually_topIndividualBoundaryZeroValue_eq_changeTarget D
      representative offset radius Fsys x w₀ hw₀ data hA c hc)
  exact change.sourceValue_lower_of_targetValue_lower
    (boundary.topIndividualBoundaryParameterOnCommonTail D representative offset
      radius Fsys x w₀ hw₀ data hA c)
    (boundary.topIndividualBoundaryParameterOnCommonTail_tendsto D representative
      offset radius Fsys x w₀ hw₀ data hA c)
    (boundary.topIndividualBoundarySymbolValueOnCommonTail D representative
      offset radius Fsys x w₀ hw₀ data hA c)
    (boundary.topIndividualBoundaryZeroScaleOnCommonTail_ge_one D representative
      offset radius Fsys x w₀ hw₀ data hA c)
    (boundary.topIndividualBoundarySymbolValueOnCommonTail_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c)
    htarget

/-- A lower bound at the highest individual boundary becomes a lower bound
for the literal selected padded top-prefix family, with both fixed tails
removed. -/
theorem selectedPaddedTopPrefix_lower_of_topIndividualBoundaryZero_lower
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount)
    (compatibility : boundary.TopIndividualSelectedPaddedCompatibility D
      representative offset radius Fsys x w₀ hw₀ data hA c hc)
    (hincoming : HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)) :
    HasInversePowerLowerBound atTop
      (boundary.topIndividualBoundaryZeroScale D representative offset radius
        Fsys x w₀ hw₀ data c)
      (boundary.selectedPaddedTopPrefixNumericValue D representative offset
        radius Fsys x w₀ hw₀ data) := by
  have hsource :=
    boundary.topIndividualAnalyticSource_lower_of_mixedBoundaryZero_lower D
      representative offset radius Fsys x w₀ hw₀ data hA c hc hincoming
  have hselected :=
    hsource.congr_of_eventually compatibility.source_eq_selected
  let N := boundary.topIndividualCommonTail D representative offset radius Fsys
    x w₀ hw₀ data hA
  have hselectedScale : HasInversePowerLowerBound atTop
      (fun n ↦ boundary.topIndividualBoundaryZeroScale D representative offset
        radius Fsys x w₀ hw₀ data c
          (boundary.topIndividualCommonSelectedIndex D representative offset
            radius Fsys x w₀ hw₀ data hA n))
      (fun j n ↦ boundary.selectedPaddedTopPrefixNumericValue D representative
        offset radius Fsys x w₀ hw₀ data j
          (boundary.topIndividualCommonSelectedIndex D representative offset
            radius Fsys x w₀ hw₀ data hA n)) :=
    hselected.congr_scale_of_eventually
      (Filter.Eventually.of_forall fun n ↦
        boundary.individualMixedBoundaryScaleOnSimultaneousTail_zero_eq_topScale
          D representative offset radius Fsys x w₀ hw₀ data hA c n)
  have hshifted : HasInversePowerLowerBound atTop
      (fun n ↦ boundary.topIndividualBoundaryZeroScale D representative offset
        radius Fsys x w₀ hw₀ data c (n + N))
      (fun j n ↦ boundary.selectedPaddedTopPrefixNumericValue D representative
        offset radius Fsys x w₀ hw₀ data j (n + N)) := by
    simpa only [N,
      boundary.topIndividualCommonSelectedIndex_eq_add_tail D representative
        offset radius Fsys x w₀ hw₀ data hA] using hselectedScale
  exact (hasInversePowerLowerBound_nat_add_iff N
    (boundary.topIndividualBoundaryZeroScale D representative offset radius
      Fsys x w₀ hw₀ data c)
    (boundary.selectedPaddedTopPrefixNumericValue D representative offset radius
      Fsys x w₀ hw₀ data)).mp hshifted

/-- Final top-prefix contradiction from the lower bound returned by the full
ordered-cluster backward propagation. -/
theorem false_of_topIndividualBoundaryZero_lower
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount)
    (compatibility : boundary.TopIndividualSelectedPaddedCompatibility D
      representative offset radius Fsys x w₀ hw₀ data hA c hc)
    (hincoming : HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)) :
    False := by
  apply boundary.false_of_selectedPaddedTopPrefix_lower D representative offset
    radius Fsys x w₀ hw₀ data
    (boundary.topIndividualBoundaryZeroScale D representative offset radius
      Fsys x w₀ hw₀ data c)
    (boundary.topIndividualBoundaryZeroScale_ge_one D representative offset
      radius Fsys x w₀ hw₀ data c)
  change HasInversePowerLowerBound atTop
    (boundary.topIndividualBoundaryZeroScale D representative offset radius
      Fsys x w₀ hw₀ data c)
    (boundary.selectedPaddedTopPrefixNumericValue D representative offset radius
      Fsys x w₀ hw₀ data)
  exact
    boundary.selectedPaddedTopPrefix_lower_of_topIndividualBoundaryZero_lower D
      representative offset radius Fsys x w₀ hw₀ data hA c hc
      compatibility hincoming

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
