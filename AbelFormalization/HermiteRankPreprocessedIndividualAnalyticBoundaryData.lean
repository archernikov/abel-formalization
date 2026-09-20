import AbelFormalization.FiniteAnalyticChangeOfGenerators
import AbelFormalization.HermiteRankPreprocessedIndividualNumericData

/-!
# Analytic boundary changes for the individual Hermite trace

Every boundary of an individual-decrement trace is the same ideal as the
displayed family immediately before it and the displayed family immediately
after it.  This module turns those span equalities into finite analytic
change-of-generators adapters.  A self-adapter for each boundary fixes one
numeric representative of that boundary family; equality of analytic germs
then reconciles it, eventually, with the independently chosen representatives
in the two adjacent adapters.

The resulting paper-specific constructor fills both numeric boundary
identities and all change-matrix polynomial bounds.  Its only input beyond
the existing Hermite boundary is a polynomially bounded numeric assignment
for the finitely many polynomial symbols at each boundary.  No equality of
flat assignments and no global evaluation homomorphism on analytic germs is
used.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

namespace IndividualCentralDisplayedTraceData

/-- Analytic evaluation data for the ideal boundaries of one displayed
individual trace.  Each boundary has its own padded generating family and
moving symbol assignment, while all analytic coefficients are evaluated at
the same parameter tending to the germ base point. -/
structure AnalyticBoundaryData
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E)
    {Block : Type} [Fintype Block] [DecidableEq Block]
    {d : Block → ℕ} {steps : List Block}
    {I : Ideal
      (MvPolynomial (ClusterOperationSymbol Block d) (AnalyticGermAt x))}
    {traceData : IndividualCentralIdealTraceData
      (AnalyticGermAt x) d steps I}
    (displayed : IndividualCentralDisplayedTraceData
      (AnalyticGermAt x) d steps I traceData)
    (scale : Fin (steps.length + 1) → ℕ → ℝ) where
  boundary : (q : Fin (steps.length + 1)) →
    RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
      (MvPolynomial (ClusterOperationSymbol Block d) (AnalyticGermAt x))
      (individualCentralIdealBoundary (AnalyticGermAt x) d steps I q)
  parameter : ℕ → E
  parameter_tendsto : Tendsto parameter atTop (𝓝 x)
  symbolValue : Fin (steps.length + 1) →
    ClusterOperationSymbol Block d → ℕ → ℝ
  scale_ge_one : ∀ q, ∀ᶠ n in atTop, 1 ≤ scale q n
  symbol_bound : ∀ q z,
    HasPolynomialUpperBound atTop (scale q) (symbolValue q z)

namespace AnalyticBoundaryData

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {x : E}
variable {Block : Type} [Fintype Block] [DecidableEq Block]
variable {d : Block → ℕ} {steps : List Block}
variable {I : Ideal
  (MvPolynomial (ClusterOperationSymbol Block d) (AnalyticGermAt x))}
variable {traceData : IndividualCentralIdealTraceData
  (AnalyticGermAt x) d steps I}
variable {displayed : IndividualCentralDisplayedTraceData
  (AnalyticGermAt x) d steps I traceData}
variable {scale : Fin (steps.length + 1) → ℕ → ℝ}

/-- A self change-of-generators adapter fixes one analytic representative for
each boundary generator.  These representatives are shared by both adjacent
numeric identities below. -/
noncomputable def boundarySelfChange
    (data : AnalyticBoundaryData x displayed scale)
    (q : Fin (steps.length + 1)) :
    FiniteAnalyticChangeOfGeneratorsData x
      (data.boundary q).generator (data.boundary q).generator :=
  finiteAnalyticChangeOfGeneratorsDataOfSpan x
    (data.boundary q).generator (data.boundary q).generator le_rfl

/-- Finite analytic change from the displayed post-step family to the
successor ideal-boundary family. -/
noncomputable def afterBoundaryChange
    (data : AnalyticBoundaryData x displayed scale)
    (j : Fin steps.length) :
    FiniteAnalyticChangeOfGeneratorsData x
      (IndividualCentralTransferData.DisplayedData.afterGenerator
        (AnalyticGermAt x) (displayed.displayed j))
      (data.boundary j.succ).generator :=
  finiteAnalyticChangeOfGeneratorsDataOfSpan x
    (IndividualCentralTransferData.DisplayedData.afterGenerator
      (AnalyticGermAt x) (displayed.displayed j))
    (data.boundary j.succ).generator (by
      rw [(data.boundary j.succ).span_eq,
        displayed.after_span_boundary_succ (AnalyticGermAt x) j])

/-- Finite analytic change from the predecessor ideal-boundary family to the
displayed pre-step family. -/
noncomputable def beforeBoundaryChange
    (data : AnalyticBoundaryData x displayed scale)
    (j : Fin steps.length) :
    FiniteAnalyticChangeOfGeneratorsData x
      (data.boundary j.castSucc).generator
      (IndividualCentralTransferData.DisplayedData.beforeGenerator
        (AnalyticGermAt x) (displayed.displayed j)) :=
  finiteAnalyticChangeOfGeneratorsDataOfSpan x
    (data.boundary j.castSucc).generator
    (IndividualCentralTransferData.DisplayedData.beforeGenerator
      (AnalyticGermAt x) (displayed.displayed j)) (by
      rw [displayed.before_span (AnalyticGermAt x) j,
        (data.boundary j.castSucc).span_eq]
      rfl
    )

/-- Numeric values of the fixed boundary representatives. -/
def boundaryValue (data : AnalyticBoundaryData x displayed scale)
    (q : Fin (steps.length + 1))
    (b : Fin ((data.boundary q).count + 1)) (n : ℕ) : ℝ :=
  (data.boundarySelfChange q).sourceValue data.parameter
    (data.symbolValue q) b n

/-- Numeric values of the displayed post-step representatives. -/
def afterValue (data : AnalyticBoundaryData x displayed scale)
    (j : Fin steps.length)
    (a : Fin ((displayed.displayed j).central.count + 1)) (n : ℕ) : ℝ :=
  (data.afterBoundaryChange j).sourceValue data.parameter
    (data.symbolValue j.succ) a n

/-- Numeric values of the displayed pre-step representatives. -/
def beforeValue (data : AnalyticBoundaryData x displayed scale)
    (j : Fin steps.length)
    (k : Fin ((displayed.displayed j).source.count + 1)) (n : ℕ) : ℝ :=
  (data.beforeBoundaryChange j).targetValue data.parameter
    (data.symbolValue j.castSucc) k n

/-- Evaluated analytic coefficients expressing the successor boundary in the
displayed post-step family. -/
def afterBoundaryCoefficient
    (data : AnalyticBoundaryData x displayed scale)
    (j : Fin steps.length)
    (b : Fin ((data.boundary j.succ).count + 1))
    (a : Fin ((displayed.displayed j).central.count + 1)) (n : ℕ) : ℝ :=
  (data.afterBoundaryChange j).coefficientValue data.parameter
    (data.symbolValue j.succ) b a n

/-- Evaluated analytic coefficients expressing the displayed pre-step family
in the predecessor boundary family. -/
def beforeBoundaryCoefficient
    (data : AnalyticBoundaryData x displayed scale)
    (j : Fin steps.length)
    (k : Fin ((displayed.displayed j).source.count + 1))
    (b : Fin ((data.boundary j.castSucc).count + 1)) (n : ℕ) : ℝ :=
  (data.beforeBoundaryChange j).coefficientValue data.parameter
    (data.symbolValue j.castSucc) k b n

/-- Analyticity of the finite change matrix gives every successor-boundary
coefficient its required polynomial upper bound. -/
theorem afterBoundaryCoefficient_hasPolynomialUpperBound
    (data : AnalyticBoundaryData x displayed scale)
    (j : Fin steps.length)
    (b : Fin ((data.boundary j.succ).count + 1))
    (a : Fin ((displayed.displayed j).central.count + 1)) :
    HasPolynomialUpperBound atTop (scale j.succ)
      (data.afterBoundaryCoefficient j b a) := by
  exact (data.afterBoundaryChange j).coefficientValue_hasPolynomialUpperBound
    data.parameter data.parameter_tendsto (data.symbolValue j.succ)
      (data.scale_ge_one j.succ) (data.symbol_bound j.succ) b a

/-- Analyticity of the finite change matrix gives every predecessor-boundary
coefficient its required polynomial upper bound. -/
theorem beforeBoundaryCoefficient_hasPolynomialUpperBound
    (data : AnalyticBoundaryData x displayed scale)
    (j : Fin steps.length)
    (k : Fin ((displayed.displayed j).source.count + 1))
    (b : Fin ((data.boundary j.castSucc).count + 1)) :
    HasPolynomialUpperBound atTop (scale j.castSucc)
      (data.beforeBoundaryCoefficient j k b) := by
  exact (data.beforeBoundaryChange j).coefficientValue_hasPolynomialUpperBound
    data.parameter data.parameter_tendsto (data.symbolValue j.castSucc)
      (data.scale_ge_one j.castSucc) (data.symbol_bound j.castSucc) k b

/-- The displayed post-step family evaluates eventually to the fixed
successor boundary family.  Equality of the separately chosen target and
self representatives follows from their common analytic germ. -/
theorem eventually_afterBoundaryIdentity
    (data : AnalyticBoundaryData x displayed scale)
    (j : Fin steps.length) :
    ∀ᶠ n in atTop, ∀ b,
      data.boundaryValue j.succ b n =
        ∑ a, data.afterBoundaryCoefficient j b a n *
          data.afterValue j a n := by
  let self := data.boundarySelfChange j.succ
  let change := data.afterBoundaryChange j
  have hrepresentative : ∀ᶠ n in atTop, ∀ b,
      self.sourceRepresentative b (data.parameter n) =
        change.targetRepresentative b (data.parameter n) := by
    apply Filter.eventually_all.mpr
    intro b
    exact data.parameter_tendsto.eventually
      (analyticPolynomialRepresentatives_eventually_eq x
        (self.source_germ_eq b) (change.target_germ_eq b) rfl)
  have hidentity := change.eventually_targetValue_eq_sum
    data.parameter data.parameter_tendsto (data.symbolValue j.succ)
  filter_upwards [hrepresentative, hidentity] with n hrep hid
  intro b
  change MvPolynomial.eval (fun z => data.symbolValue j.succ z n)
      (self.sourceRepresentative b (data.parameter n)) = _
  rw [hrep b]
  exact hid b

/-- The fixed predecessor boundary family evaluates eventually to the
displayed pre-step family.  Equality of the two chosen source representatives
again follows solely from equality of their analytic germs. -/
theorem eventually_beforeBoundaryIdentity
    (data : AnalyticBoundaryData x displayed scale)
    (j : Fin steps.length) :
    ∀ᶠ n in atTop, ∀ k,
      data.beforeValue j k n =
        ∑ b, data.beforeBoundaryCoefficient j k b n *
          data.boundaryValue j.castSucc b n := by
  let self := data.boundarySelfChange j.castSucc
  let change := data.beforeBoundaryChange j
  have hrepresentative : ∀ᶠ n in atTop, ∀ b,
      change.sourceRepresentative b (data.parameter n) =
        self.sourceRepresentative b (data.parameter n) := by
    apply Filter.eventually_all.mpr
    intro b
    exact data.parameter_tendsto.eventually
      (analyticPolynomialRepresentatives_eventually_eq x
        (change.source_germ_eq b) (self.source_germ_eq b) rfl)
  have hidentity := change.eventually_targetValue_eq_sum
    data.parameter data.parameter_tendsto (data.symbolValue j.castSucc)
  filter_upwards [hrepresentative, hidentity] with n hrep hid
  intro k
  rw [show data.beforeValue j k n =
      change.targetValue data.parameter (data.symbolValue j.castSucc) k n by
        rfl]
  rw [hid k]
  apply Finset.sum_congr rfl
  intro b _hb
  congr 1
  change MvPolynomial.eval (fun z => data.symbolValue j.castSucc z n)
      (change.sourceRepresentative b (data.parameter n)) = _
  rw [hrep b]
  rfl

end AnalyticBoundaryData
end IndividualCentralDisplayedTraceData

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

noncomputable local instance individualAnalyticBoundaryBlockDecidableEq
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- The boundary scales used by the numeric individual recursion. -/
abbrev individualNumericBoundaryScale
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :=
  data.orderedClusterIndividualBoundaryScale A
    (boundary.individualQuantitativeSubsequence D representative offset radius
      Fsys x w₀ hw₀ data hA) c (boundary.preprocessed.fixedSteps c)

/-- Canonical padded generators for every ideal boundary of the selected
individual trace. -/
noncomputable def individualNumericBoundaryFamily
    (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1)) :
    RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
        (paperRankHermiteHigherCount boundary.S) (c.val + 1))
      (individualCentralIdealBoundary (RealAnalyticGerm p)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        (boundary.individualNumericSteps D representative offset radius Fsys x
          w₀ hw₀ data c)
        (boundary.preprocessed.descent.clusterStage c).preprocessingInput q) :=
  Classical.choice
    (RepresentativeClusterSubsequence.nonempty_paddedIdealGeneratorFamily _ _)

/-- The shifted selected box parameter used for every analytic coefficient in
the individual recursion. -/
def individualNumericAnalyticParameter
    (hA : IsAbel A) (n : ℕ) : RestrictedBoxSpace p :=
  (boundary.selectedTranslatedParameter D representative offset radius Fsys x
    w₀ hw₀ data
    (n + boundary.individualQuantitativeTail D representative offset radius
      Fsys x w₀ hw₀ data hA)).2

/-- The shifted selected box parameter still tends to the analytic-germ base
point. -/
theorem individualNumericAnalyticParameter_tendsto
    (hA : IsAbel A) :
    Tendsto (boundary.individualNumericAnalyticParameter D representative
      offset radius Fsys x w₀ hw₀ data hA) atTop
      (𝓝 (0 : RestrictedBoxSpace p)) := by
  let Ntail := boundary.individualQuantitativeTail D representative offset
    radius Fsys x w₀ hw₀ data hA
  let shift : ℕ → ℕ := fun n ↦ n + Ntail
  have hshift : Tendsto shift atTop atTop := by
    simpa only [shift, Nat.add_comm] using tendsto_add_atTop_nat Ntail
  exact (boundary.selectedTranslatedParameter_box_tendsto_zero D
    representative offset radius Fsys x w₀ hw₀ data).comp hshift

/-- Package arbitrary polynomially bounded boundary symbol values with the
canonical finite ideal presentations and the actual moving Hermite parameter.
All analytic change matrices are constructed from the displayed span
equalities. -/
noncomputable def individualAnalyticBoundaryData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (symbolValue : Fin ((boundary.individualNumericSteps D representative
      offset radius Fsys x w₀ hw₀ data c).length + 1) →
      ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)) → ℕ → ℝ)
    (hsymbol : ∀ q z,
      HasPolynomialUpperBound atTop
        (boundary.individualNumericBoundaryScale D representative offset radius
          Fsys x w₀ hw₀ data hA c q) (symbolValue q z)) :
    IndividualCentralDisplayedTraceData.AnalyticBoundaryData
      (0 : RestrictedBoxSpace p)
      (boundary.individualNumericDisplayed D representative offset radius Fsys
        x w₀ hw₀ data c)
      (boundary.individualNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data hA c) where
  boundary := boundary.individualNumericBoundaryFamily D representative offset
    radius Fsys x w₀ hw₀ data c
  parameter := boundary.individualNumericAnalyticParameter D representative
    offset radius Fsys x w₀ hw₀ data hA
  parameter_tendsto := boundary.individualNumericAnalyticParameter_tendsto D
    representative offset radius Fsys x w₀ hw₀ data hA
  symbolValue := symbolValue
  scale_ge_one := by
    intro q
    exact Filter.Eventually.of_forall fun n ↦ one_le_two.trans
      (two_le_clusterBalancingPrefixScale A
        (fun k ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA k) c)
        (boundary.preprocessed.fixedSteps c) q.val n)
  symbol_bound := hsymbol

/-- Finite analytic changes of generators discharge the two boundary
identities and both change-matrix bound fields of
`IndividualNumericBoundaryCompatibility`. -/
noncomputable def individualNumericBoundaryCompatibilityOfAnalyticChange
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (symbolValue : Fin ((boundary.individualNumericSteps D representative
      offset radius Fsys x w₀ hw₀ data c).length + 1) →
      ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)) → ℕ → ℝ)
    (hsymbol : ∀ q z,
      HasPolynomialUpperBound atTop
        (boundary.individualNumericBoundaryScale D representative offset radius
          Fsys x w₀ hw₀ data hA c q) (symbolValue q z)) :
    boundary.IndividualNumericBoundaryCompatibility D representative offset
      radius Fsys x w₀ hw₀ data hA c := by
  let analytic := boundary.individualAnalyticBoundaryData D representative
    offset radius Fsys x w₀ hw₀ data hA c symbolValue hsymbol
  exact {
    boundaryCount := fun q ↦ (analytic.boundary q).count
    boundaryValue := analytic.boundaryValue
    afterValue := analytic.afterValue
    beforeValue := analytic.beforeValue
    afterBoundaryCoefficient := analytic.afterBoundaryCoefficient
    beforeBoundaryCoefficient := analytic.beforeBoundaryCoefficient
    afterBoundaryCoefficient_bound := by
      intro j b q
      exact analytic.afterBoundaryCoefficient_hasPolynomialUpperBound j b q
    beforeBoundaryCoefficient_bound := by
      intro j q b
      exact analytic.beforeBoundaryCoefficient_hasPolynomialUpperBound j q b
    afterBoundaryIdentity := fun j ↦ analytic.eventually_afterBoundaryIdentity j
    beforeBoundaryIdentity := fun j ↦ analytic.eventually_beforeBoundaryIdentity j
  }

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
