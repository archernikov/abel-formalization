import AbelFormalization.FiniteAnalyticNestedCoefficientwiseEvaluation
import AbelFormalization.HermiteRankIndividualSimultaneousBoundaryCompatibility

/-!
# Finite analytic data for the Hermite simultaneous segment

The algebraic simultaneous trace already contains finite displayed source and
central families.  This file chooses finite analytic changes from those
families to the canonical sources and central initial forms, and one further
change between every pair of adjacent displayed operations.

The source side is evaluated at the literal mixed/exact source assignment.
The central side is evaluated at the exact source assignment of the following
natural logarithmic step.  On central variables that assignment is exactly the
post-log assignment of the current step.  This convention makes the two sides
of every internal boundary use one literal assignment.  The only residual
numeric inputs to the final constructor are coordinatewise polynomial bounds
for these two concrete assignments and for the error-free main assignment.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter Set
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

/-- Indices of the simultaneous operations retained at one cluster. -/
abbrev SimultaneousAnalyticOperationIndex
    (c : Fin data.orderedClusterCount) :=
  Fin ((boundary.simultaneousNumericStage D representative offset radius Fsys
    x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)

/-- Outer active-cluster symbols at a simultaneous operation. -/
abbrev SimultaneousAnalyticActiveSymbol
    (c : Fin data.orderedClusterCount) :=
  ClusterOperationSymbol
    (Fin (data.orderedCluster c).card)
    (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S))

/-- Inner symbols belonging to the already curried smaller prefix. -/
abbrev SimultaneousAnalyticPrefixSymbol
    (c : Fin data.orderedClusterCount) :=
  ClusterOperationSymbol
    (data.OrderedClusterPrefixBlock c.val)
    (data.orderedClusterPrefixConstantDerivativeCount
      (paperRankHermiteHigherCount boundary.S + 1) c.val)

/-- The selected box parameter on the common individual-plus-simultaneous
tail. -/
def simultaneousQuantitativeAnalyticParameter
    (hA : IsAbel A) (n : ℕ) : RestrictedBoxSpace p :=
  (boundary.selectedTranslatedParameter D representative offset radius Fsys x
    w₀ hw₀ data
    (boundary.simultaneousQuantitativeReindex D representative offset radius
      Fsys x w₀ hw₀ data hA n)).2

/-- The common-tail analytic parameter converges to the germ base point. -/
theorem simultaneousQuantitativeAnalyticParameter_tendsto
    (hA : IsAbel A) :
    Tendsto (boundary.simultaneousQuantitativeAnalyticParameter D representative
      offset radius Fsys x w₀ hw₀ data hA) atTop
      (𝓝 (0 : RestrictedBoxSpace p)) := by
  exact (boundary.selectedTranslatedParameter_box_tendsto_zero D representative
    offset radius Fsys x w₀ hw₀ data).comp
      (boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
        offset radius Fsys x w₀ hw₀ data hA)

/-- The concrete smaller-prefix assignment at operation `r`, on the common
tail. -/
def simultaneousQuantitativeAnalyticPrefixValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ) :
    boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
      Fsys x w₀ hw₀ data c → ℕ → ℝ :=
  fun z n ↦ boundary.simultaneousSmallerPrefixSequenceValue D representative
    offset radius Fsys x w₀ hw₀ data c r z
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n)

/-- The actual active-cluster source assignment of one retained operation. -/
def simultaneousQuantitativeAnalyticSourceValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c) :
    boundary.SimultaneousAnalyticActiveSymbol D representative offset radius
      Fsys x w₀ hw₀ data c → ℕ → ℝ :=
  finiteRealJetActualAssignment
    (boundary.simultaneousQuantitativePostLogScale D representative offset
      radius Fsys x w₀ hw₀ data hA c r.val)
    (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S))
    (boundary.simultaneousQuantitativeOperationJetSequence D representative
      offset radius Fsys x w₀ hw₀ data hA c r)

/-- Exact derivative jets at the following natural simultaneous operation.
This family is defined also after the last retained operation. -/
def simultaneousQuantitativeExactSuccessorJets
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ) :
    ∀ n i, RealCentralJetSubstitutionData A
      (boundary.simultaneousQuantitativePostLogScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r + 1) i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S) i) :=
  fun n i ↦ hA.realDerivativeJetSubstitutionData (hA.inverse_pos _)
    (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S) i)

/-- The exact source assignment immediately following operation `r`.  Its
central coordinates equal the post-log central coordinates of operation
`r`, while its free `q` coordinates are allowed to differ. -/
def simultaneousQuantitativeAnalyticAfterValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ) :
    boundary.SimultaneousAnalyticActiveSymbol D representative offset radius
      Fsys x w₀ hw₀ data c → ℕ → ℝ :=
  finiteRealJetActualAssignment
    (boundary.simultaneousQuantitativePostLogScale D representative offset
      radius Fsys x w₀ hw₀ data hA c (r + 1))
    (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S))
    (boundary.simultaneousQuantitativeExactSuccessorJets D representative offset
      radius Fsys x w₀ hw₀ data hA c r)

/-- Combined outer/inner assignment used by the displayed source change. -/
def simultaneousQuantitativeAnalyticSourceSymbolValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c) :
    boundary.SimultaneousAnalyticActiveSymbol D representative offset radius
        Fsys x w₀ hw₀ data c ⊕
      boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
        Fsys x w₀ hw₀ data c → ℕ → ℝ :=
  Sum.elim
    (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
      offset radius Fsys x w₀ hw₀ data hA c r)
    (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
      offset radius Fsys x w₀ hw₀ data hA c r.val)

/-- Combined assignment used by the displayed central change. -/
def simultaneousQuantitativeAnalyticAfterSymbolValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ) :
    boundary.SimultaneousAnalyticActiveSymbol D representative offset radius
        Fsys x w₀ hw₀ data c ⊕
      boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
        Fsys x w₀ hw₀ data c → ℕ → ℝ :=
  Sum.elim
    (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
      offset radius Fsys x w₀ hw₀ data hA c r)
    (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
      offset radius Fsys x w₀ hw₀ data hA c r)

/-- Canonical central initial form, re-extended by the unused representative
variables so it lies in the same outer ring as the displayed families. -/
def simultaneousQuantitativeCanonicalCentralGenerator
    (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c)
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count) :
    MvPolynomial
      (boundary.SimultaneousAnalyticActiveSymbol D representative offset radius
        Fsys x w₀ hw₀ data c)
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
        (paperRankHermiteHigherCount boundary.S) c.val) :=
  MvPolynomial.rename Sum.inr
    (centralPolynomialPhi
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
        (paperRankHermiteHigherCount boundary.S) c.val)
      (Fin (data.orderedCluster c).card)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S))
      (Fin (data.orderedCluster c).card)
      (centralNormalizedInitialPolynomial
        (centralTransferShear
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S)))
        (((boundary.simultaneousNumericTrace D representative offset radius
          Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q)))

/-- Analytic change from the displayed translated source family to the
canonical source family of one simultaneous operation. -/
noncomputable def simultaneousQuantitativeSourceAnalyticChange
    (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c) :=
  finiteAnalyticNestedChangeOfGeneratorsDataOfSpan
    (0 : RestrictedBoxSpace p)
    ((boundary.simultaneousNumericTrace D representative offset radius Fsys x
      w₀ hw₀ data c).simultaneousDisplayed r).source.generator
    ((boundary.simultaneousNumericTrace D representative offset radius Fsys x
      w₀ hw₀ data c).simultaneous.transferCertificate r).source
    (by
      apply Ideal.span_le.2
      rintro _ ⟨q, rfl⟩
      apply Ideal.mem_span_range_iff_exists_fun.mpr
      refine ⟨((boundary.simultaneousNumericTrace D representative offset radius
        Fsys x w₀ hw₀ data c).simultaneousDisplayed r).identities.sourceCoefficient q, ?_⟩
      exact (((boundary.simultaneousNumericTrace D representative offset radius
        Fsys x w₀ hw₀ data c).simultaneousDisplayed r).identities.source_identity q).symm)

/-- Analytic change from the canonical re-extended central initial forms to
the displayed central family. -/
noncomputable def simultaneousQuantitativeCentralAnalyticChange
    (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c) :=
  finiteAnalyticNestedChangeOfGeneratorsDataOfSpan
    (0 : RestrictedBoxSpace p)
    (boundary.simultaneousQuantitativeCanonicalCentralGenerator D
      representative offset radius Fsys x w₀ hw₀ data c r)
    (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
        (paperRankHermiteHigherCount boundary.S) c.val)
      ((boundary.simultaneousNumericTrace D representative offset radius Fsys x
        w₀ hw₀ data c).simultaneousDisplayed r))
    (by
      apply le_of_eq
      calc
        Ideal.span (Set.range
            (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
              (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
                (paperRankHermiteHigherCount boundary.S) c.val)
              ((boundary.simultaneousNumericTrace D representative offset radius
                Fsys x w₀ hw₀ data c).simultaneousDisplayed r))) =
            unusedPolynomialExtension (Fin (data.orderedCluster c).card)
              ((boundary.simultaneousNumericStage D representative offset radius
                Fsys x w₀ hw₀ data c).certificate.centralTransferOutput r) :=
          ((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data c).simultaneousDisplayed r).after_span _
        _ = unusedPolynomialExtension (Fin (data.orderedCluster c).card)
              (Ideal.span (Set.range (fun q ↦ centralPolynomialPhi
                (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
                  (paperRankHermiteHigherCount boundary.S) c.val)
                (Fin (data.orderedCluster c).card)
                (terminalTotalDerivativeCount (fun _ :
                  Fin (data.orderedCluster c).card ↦
                    paperRankHermiteHigherCount boundary.S))
                (Fin (data.orderedCluster c).card)
                (centralNormalizedInitialPolynomial
                  (centralTransferShear
                    (terminalTotalDerivativeCount (fun _ :
                      Fin (data.orderedCluster c).card ↦
                        paperRankHermiteHigherCount boundary.S)))
                  (((boundary.simultaneousNumericTrace D representative offset
                    radius Fsys x w₀ hw₀ data c).simultaneous.transferCertificate
                      r).source q))))) := by
          rw [((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data c).simultaneous).central_span_eq_output r]
        _ = Ideal.span (Set.range
              (boundary.simultaneousQuantitativeCanonicalCentralGenerator D
                representative offset radius Fsys x w₀ hw₀ data c r)) := by
          symm
          exact span_rename_inr_range_eq_unusedPolynomialExtension _)

/-- Analytic change from one displayed central family to the translated
displayed source family of the following retained operation. -/
noncomputable def simultaneousQuantitativeAdjacentAnalyticChange
    (c : Fin data.orderedClusterCount)
    (i : Fin (boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps) :=
  finiteAnalyticNestedChangeOfGeneratorsDataOfSpan
    (0 : RestrictedBoxSpace p)
    (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
        (paperRankHermiteHigherCount boundary.S) c.val)
      ((boundary.simultaneousNumericTrace D representative offset radius Fsys x
        w₀ hw₀ data c).simultaneousDisplayed i.castSucc))
    ((boundary.simultaneousNumericTrace D representative offset radius Fsys x
      w₀ hw₀ data c).simultaneousDisplayed i.succ).source.generator
    (by
      apply le_of_eq
      let trace := boundary.simultaneousNumericTrace D representative offset
        radius Fsys x w₀ hw₀ data c
      let translate := simultaneousCentralSourceTranslation
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
          (paperRankHermiteHigherCount boundary.S) c.val)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster c).card ↦
            paperRankHermiteHigherCount boundary.S))
      calc
        Ideal.span (Set.range
            (trace.simultaneousDisplayed i.succ).source.generator) =
            ((boundary.simultaneousNumericStage D representative offset radius
              Fsys x w₀ hw₀ data c).certificate.centralTransferInput i.succ).map
              translate.toRingHom := by
          simpa only [trace, translate, simultaneousCentralSourceTranslation]
            using (trace.simultaneousDisplayed i.succ).source.span_eq
        _ = (Ideal.span (Set.range
              (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
                (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
                  (paperRankHermiteHigherCount boundary.S) c.val)
                (trace.simultaneousDisplayed i.castSucc)))).map
              translate.toRingHom := by
          congr 1
          exact ((trace.simultaneousDisplayed i.succ).before_span _).symm.trans
            (trace.simultaneousAfter_span_eq_nextBefore_span i).symm
        _ = Ideal.span (Set.range
              (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
                (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
                  (paperRankHermiteHigherCount boundary.S) c.val)
                (trace.simultaneousDisplayed i.castSucc))) := by
          rw [(trace.simultaneousDisplayed i.castSucc).after_span]
          exact polynomialCoordinateTranslation_unusedPolynomialExtension
            (fun _ : Fin (data.orderedCluster c).card ↦
              (-1 : data.OrderedClusterPrefixRing (RealAnalyticGerm p)
                (paperRankHermiteHigherCount boundary.S) c.val))
            ((boundary.simultaneousNumericStage D representative offset radius
              Fsys x w₀ hw₀ data c).certificate.centralTransferOutput
                i.castSucc))

/-! ## Exact compatibility of consecutive assignments -/

/-- Post-log center `r` is `E` of the following post-log center. -/
theorem simultaneousQuantitativePostLogScale_eq_E_succ
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (i : Fin (data.orderedCluster c).card) (n : ℕ) :
    boundary.simultaneousQuantitativePostLogScale D representative offset
        radius Fsys x w₀ hw₀ data hA c r i n =
      E (boundary.simultaneousQuantitativePostLogScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r + 1) i n) := by
  let t := data.orderedClusterPostBalancingFinalOrderTime c
    (boundary.simultaneousQuantitativeRawTime D representative offset radius
      Fsys x w₀ hw₀ data hA c)
    (boundary.preprocessed.fixedSteps c) (boundary.preprocessed.fixedOrder c)
    i n
  change inverse A (t - (((r + 1 : ℕ) : ℝ))) =
    E (inverse A (t - ((((r + 1) + 1 : ℕ) : ℝ))))
  calc
    inverse A (t - (((r + 1 : ℕ) : ℝ))) =
        inverse A (t - ((((r + 1) + 1 : ℕ) : ℝ)) + 1) := by
      congr 1
      push_cast
      ring
    _ = E (inverse A (t - ((((r + 1) + 1 : ℕ) : ℝ)))) :=
      hA.inverse_add_one _

/-- On central variables, the exact source assignment at natural operation
`r+1` is the post-log assignment at operation `r`. -/
theorem simultaneousQuantitativeAnalyticAfterValue_central
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (z : CentralPolynomialIndex (Fin (data.orderedCluster c).card)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S))
      (Fin (data.orderedCluster c).card)) (n : ℕ) :
    boundary.simultaneousQuantitativeAnalyticAfterValue D representative offset
        radius Fsys x w₀ hw₀ data hA c r (Sum.inr z) n =
      realCentralTransferCentralValue A
        (fun i ↦ boundary.simultaneousQuantitativePostLogScale D representative
          offset radius Fsys x w₀ hw₀ data hA c r i n)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster c).card ↦
            paperRankHermiteHigherCount boundary.S)) z := by
  rcases z with br | i
  · rcases br with ⟨i, q⟩
    simp only [simultaneousQuantitativeAnalyticAfterValue,
      finiteRealJetActualAssignment, realCentralTransferActualValue,
      simultaneousQuantitativeExactSuccessorJets,
      IsAbel.realDerivativeJetSubstitutionData_sourceJet,
      realCentralTransferCentralValue]
    rw [boundary.simultaneousQuantitativePostLogScale_eq_E_succ D
      representative offset radius Fsys x w₀ hw₀ data hA c r i n]
    unfold simultaneousQuantitativePostLogScale
      RepresentativeClusterSubsequence.orderedClusterSimultaneousPostLogScale
    rfl
  · simp only [simultaneousQuantitativeAnalyticAfterValue,
      finiteRealJetActualAssignment, realCentralTransferActualValue,
      realCentralTransferCentralValue]
    rw [boundary.simultaneousQuantitativePostLogScale_eq_E_succ D
      representative offset radius Fsys x w₀ hw₀ data hA c r i n]

/-- Smaller-prefix Hermite values do not depend on the simultaneous operation:
the underlying prefix blocks are disjoint from the active cluster. -/
theorem simultaneousQuantitativeAnalyticPrefixValue_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r s : ℕ)
    (z : boundary.SimultaneousAnalyticPrefixSymbol D representative offset
      radius Fsys x w₀ hw₀ data c) :
    boundary.simultaneousQuantitativeAnalyticPrefixValue D representative offset
        radius Fsys x w₀ hw₀ data hA c r z =
      boundary.simultaneousQuantitativeAnalyticPrefixValue D representative offset
        radius Fsys x w₀ hw₀ data hA c s z := by
  funext n
  simp only [simultaneousQuantitativeAnalyticPrefixValue,
    simultaneousSmallerPrefixSequenceValue,
    RepresentativeClusterSubsequence.paperRankHermiteOrderedClusterSmallerPrefixSequenceValue]
  rcases z with b | z
  · have hnot := orderedClusterPrefixBlock_not_mem_active
      (x := x) (data := data) c b
    simp only [RepresentativeClusterSubsequence.paperRankHermitePrefixValue_free,
      simultaneousPreLogParameter, hnot, dite_false]
  · rcases z with br | b
    · rcases br with ⟨b, q⟩
      have hnot := orderedClusterPrefixBlock_not_mem_active
        (x := x) (data := data) c b
      have he : (paperRankAllCoefficientBlockEquiv m).symm (Sum.inr b.1) = b.1 := by
        apply (paperRankAllCoefficientBlockEquiv m).injective
        simp
      simp only [
        RepresentativeClusterSubsequence.paperRankHermitePrefixValue_positiveDerivative,
        paperRankHermiteCoefficientValue, he, simultaneousPreLogParameter,
        hnot, dite_false]
    · have hnot := orderedClusterPrefixBlock_not_mem_active
        (x := x) (data := data) c b
      have he : (paperRankAllCoefficientBlockEquiv m).symm (Sum.inr b.1) = b.1 := by
        apply (paperRankAllCoefficientBlockEquiv m).injective
        simp
      simp only [RepresentativeClusterSubsequence.paperRankHermitePrefixValue_time,
        paperRankHermiteCoefficientValue, he, simultaneousPreLogParameter,
        hnot, dite_false]

/-- The assignment used by an internal analytic boundary: exact source
coordinates of the next operation and its smaller-prefix values. -/
def simultaneousQuantitativeAdjacentSymbolValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (i : Fin (boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps) :
    boundary.SimultaneousAnalyticActiveSymbol D representative offset radius
        Fsys x w₀ hw₀ data c ⊕
      boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
        Fsys x w₀ hw₀ data c → ℕ → ℝ :=
  Sum.elim
    (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
      offset radius Fsys x w₀ hw₀ data hA c i.val)
    (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
      offset radius Fsys x w₀ hw₀ data hA c (i.val + 1))

/-! ## Numeric values selected by the analytic adapters -/

/-- Displayed source values at one simultaneous operation. -/
def simultaneousQuantitativeAnalyticBeforeValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c) :=
  (boundary.simultaneousQuantitativeSourceAnalyticChange D representative offset
    radius Fsys x w₀ hw₀ data c r).sourceValue
      (boundary.simultaneousQuantitativeAnalyticParameter D representative
        offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r.val)

/-- Coefficients expressing canonical sources in the displayed source
family. -/
def simultaneousQuantitativeAnalyticSourceCoefficient
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c) :=
  (boundary.simultaneousQuantitativeSourceAnalyticChange D representative offset
    radius Fsys x w₀ hw₀ data c r).changeCoefficientValue
      (boundary.simultaneousQuantitativeAnalyticParameter D representative
        offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r.val)

/-- Displayed central values, evaluated at the exact following source
assignment. -/
def simultaneousQuantitativeAnalyticAfterGeneratorValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c) :=
  (boundary.simultaneousQuantitativeCentralAnalyticChange D representative offset
    radius Fsys x w₀ hw₀ data c r).targetValue
      (boundary.simultaneousQuantitativeAnalyticParameter D representative
        offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r.val)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r.val)

/-- Coefficients expressing the displayed central family in canonical central
initial forms. -/
def simultaneousQuantitativeAnalyticCentralCoefficient
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c) :=
  (boundary.simultaneousQuantitativeCentralAnalyticChange D representative offset
    radius Fsys x w₀ hw₀ data c r).changeCoefficientValue
      (boundary.simultaneousQuantitativeAnalyticParameter D representative
        offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r.val)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r.val)

/-- Coefficients at a common internal displayed boundary. -/
def simultaneousQuantitativeAnalyticAdjacentCoefficient
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (i : Fin (boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps) :=
  (boundary.simultaneousQuantitativeAdjacentAnalyticChange D representative
    offset radius Fsys x w₀ hw₀ data c i).changeCoefficientValue
      (boundary.simultaneousQuantitativeAnalyticParameter D representative
        offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
        offset radius Fsys x w₀ hw₀ data hA c i.val)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c (i.val + 1))

/-! ## Source identities and analytic matrix bounds -/

/-- Every simultaneous boundary scale is eventually at least one.  Boundary
zero uses the terminal individual compatibility theorem; a positive boundary
is the zero-position post-log center of the preceding operation. -/
theorem simultaneousQuantitativeBoundaryScale_eventually_ge_one
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ) :
    ∀ᶠ n in atTop, 1 ≤
      boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c r n := by
  by_cases hr : r = 0
  · subst r
    exact (boundary.simultaneousQuantitativeBoundaryScale_zero_tendsto_atTop D
      representative offset radius Fsys x w₀ hw₀ data hA c).eventually
        (eventually_ge_atTop 1)
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
    have hcenter :=
      (boundary.simultaneousNumericPostLogScale_tendsto_atTop D representative
        offset radius Fsys x w₀ hw₀ data hA c s
        (data.orderedClusterBalancingToActiveEquiv c 0)).comp
          (boundary.simultaneousQuantitativeReindex_tendsto_atTop D
            representative offset radius Fsys x w₀ hw₀ data hA)
    have hcenterOne := hcenter.eventually (eventually_ge_atTop 1)
    filter_upwards [hcenterOne] with n hn
    change 1 ≤ boundary.simultaneousQuantitativePostLogScale D representative
      offset radius Fsys x w₀ hw₀ data hA c s
        (data.orderedClusterBalancingToActiveEquiv c 0) n at hn
    have hzero :
        boundary.simultaneousQuantitativePostLogScale D representative offset
            radius Fsys x w₀ hw₀ data hA c s
              (data.orderedClusterBalancingToActiveEquiv c 0) n =
          boundary.simultaneousQuantitativeBoundaryScale D representative offset
            radius Fsys x w₀ hw₀ data hA c (s + 1) n := by
      exact data.orderedClusterSimultaneousPostLogScale_zero_eq_boundaryScale c A
        (boundary.simultaneousQuantitativeRawTime D representative offset radius
          Fsys x w₀ hw₀ data hA c)
        (boundary.preprocessed.fixedSteps c) (boundary.preprocessed.fixedOrder c)
        s n
    rw [hzero] at hn
    exact hn

/-- The target representative selected by the source adapter is eventually
the support-local coefficientwise source evaluation. -/
theorem eventually_simultaneousQuantitativeAnalyticCanonicalSourceValue_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c)
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count) :
    ∀ᶠ n in atTop,
      (boundary.simultaneousQuantitativeSourceAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data c r).targetValue
          (boundary.simultaneousQuantitativeAnalyticParameter D representative
            offset radius Fsys x w₀ hw₀ data hA)
          (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
            offset radius Fsys x w₀ hw₀ data hA c r)
          (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
            offset radius Fsys x w₀ hw₀ data hA c r.val) q n =
        ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseSourceEvaluation
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S))
          (boundary.simultaneousQuantitativeSourceCoefficientValue D
            representative offset radius Fsys x w₀ hw₀ data hA c r
            coefficients q)
          (boundary.simultaneousQuantitativePostLogScale D representative offset
            radius Fsys x w₀ hw₀ data hA c r.val)
          (boundary.simultaneousQuantitativeOperationJetSequence D representative
            offset radius Fsys x w₀ hw₀ data hA c r)
          (((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q)
          n := by
  let parameter := boundary.simultaneousQuantitativeAnalyticParameter D
    representative offset radius Fsys x w₀ hw₀ data hA
  let outerValue := boundary.simultaneousQuantitativeAnalyticSourceValue D
    representative offset radius Fsys x w₀ hw₀ data hA c r
  let coefficientValue :=
    boundary.simultaneousQuantitativeAnalyticPrefixValue D representative offset
      radius Fsys x w₀ hw₀ data hA c r.val
  have hraw :=
    boundary.eventually_flattenedRepresentativeEvaluation_eq_simultaneousCoefficientwiseSource
      D representative offset radius Fsys x w₀ hw₀ data hA c r coefficients q
      ((boundary.simultaneousQuantitativeSourceAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data c r).targetRepresentative q)
      ((boundary.simultaneousQuantitativeSourceAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data c r).target_germ_eq q)
      (boundary.simultaneousQuantitativePostLogScale D representative offset
        radius Fsys x w₀ hw₀ data hA c r.val)
      (boundary.simultaneousQuantitativeOperationJetSequence D representative
        offset radius Fsys x w₀ hw₀ data hA c r)
  filter_upwards [hraw] with n hn
  change MvPolynomial.eval
      (fun z ↦ Sum.elim outerValue coefficientValue z n)
      ((boundary.simultaneousQuantitativeSourceAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data c r).targetRepresentative q
          (parameter n)) = _
  have heta : (fun z ↦ Sum.elim outerValue coefficientValue z n) =
      Sum.elim (fun z ↦ outerValue z n) (fun z ↦ coefficientValue z n) := by
    funext z
    rcases z with z | z <;> rfl
  rw [heta]
  exact hn

/-- The source-side analytic adapter supplies the exact numeric identity
required by one simultaneous quantitative step. -/
theorem eventually_simultaneousQuantitativeAnalyticSourceIdentity
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c)
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r) :
    ∀ᶠ n in atTop, ∀ q,
      ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseSourceEvaluation
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S))
          (boundary.simultaneousQuantitativeSourceCoefficientValue D
            representative offset radius Fsys x w₀ hw₀ data hA c r
            coefficients q)
          (boundary.simultaneousQuantitativePostLogScale D representative offset
            radius Fsys x w₀ hw₀ data hA c r.val)
          (boundary.simultaneousQuantitativeOperationJetSequence D representative
            offset radius Fsys x w₀ hw₀ data hA c r)
          (((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q)
          n =
        ∑ k, boundary.simultaneousQuantitativeAnalyticSourceCoefficient D
            representative offset radius Fsys x w₀ hw₀ data hA c r q k n *
          boundary.simultaneousQuantitativeAnalyticBeforeValue D representative
            offset radius Fsys x w₀ hw₀ data hA c r k n := by
  have hchange :=
    (boundary.simultaneousQuantitativeSourceAnalyticChange D representative offset
      radius Fsys x w₀ hw₀ data c r).eventually_targetValue_eq_sum
        (boundary.simultaneousQuantitativeAnalyticParameter D representative
          offset radius Fsys x w₀ hw₀ data hA)
        (boundary.simultaneousQuantitativeAnalyticParameter_tendsto D
          representative offset radius Fsys x w₀ hw₀ data hA)
        (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
          offset radius Fsys x w₀ hw₀ data hA c r)
        (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
          offset radius Fsys x w₀ hw₀ data hA c r.val)
  have hcomparison : ∀ᶠ n in atTop, ∀ q,
      (boundary.simultaneousQuantitativeSourceAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data c r).targetValue
          (boundary.simultaneousQuantitativeAnalyticParameter D representative
            offset radius Fsys x w₀ hw₀ data hA)
          (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
            offset radius Fsys x w₀ hw₀ data hA c r)
          (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
            offset radius Fsys x w₀ hw₀ data hA c r.val) q n =
        ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseSourceEvaluation
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S))
          (boundary.simultaneousQuantitativeSourceCoefficientValue D
            representative offset radius Fsys x w₀ hw₀ data hA c r
            coefficients q)
          (boundary.simultaneousQuantitativePostLogScale D representative offset
            radius Fsys x w₀ hw₀ data hA c r.val)
          (boundary.simultaneousQuantitativeOperationJetSequence D representative
            offset radius Fsys x w₀ hw₀ data hA c r)
          (((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q)
          n := by
    apply Filter.eventually_all.mpr
    intro q
    exact boundary.eventually_simultaneousQuantitativeAnalyticCanonicalSourceValue_eq
      D representative offset radius Fsys x w₀ hw₀ data hA c r coefficients q
  filter_upwards [hchange, hcomparison] with n hn hcompare
  intro q
  rw [← hcompare q]
  simpa only [simultaneousQuantitativeAnalyticSourceCoefficient,
    simultaneousQuantitativeAnalyticBeforeValue] using hn q

/-- The source representative of the central adapter is eventually the
support-local coefficientwise central initial value. -/
theorem eventually_simultaneousQuantitativeAnalyticCanonicalCentralValue_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c)
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count) :
    ∀ᶠ n in atTop,
      (boundary.simultaneousQuantitativeCentralAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data c r).sourceValue
          (boundary.simultaneousQuantitativeAnalyticParameter D representative
            offset radius Fsys x w₀ hw₀ data hA)
          (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
            offset radius Fsys x w₀ hw₀ data hA c r.val)
          (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
            offset radius Fsys x w₀ hw₀ data hA c r.val) q n =
        ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseCentralEvaluation
          A
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S))
          (boundary.simultaneousQuantitativeSourceCoefficientValue D
            representative offset radius Fsys x w₀ hw₀ data hA c r
            coefficients q)
          (boundary.simultaneousQuantitativePostLogScale D representative offset
            radius Fsys x w₀ hw₀ data hA c r.val)
          (((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q)
          n := by
  let P := ((boundary.simultaneousNumericTrace D representative offset radius
    Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q
  let parameter := boundary.simultaneousQuantitativeAnalyticParameter D
    representative offset radius Fsys x w₀ hw₀ data hA
  let outerValue := boundary.simultaneousQuantitativeAnalyticAfterValue D
    representative offset radius Fsys x w₀ hw₀ data hA c r.val
  let coefficientValue :=
    boundary.simultaneousQuantitativeAnalyticPrefixValue D representative offset
      radius Fsys x w₀ hw₀ data hA c r.val
  let u := boundary.simultaneousQuantitativePostLogScale D representative offset
    radius Fsys x w₀ hw₀ data hA c r.val
  have hgeneric :=
    eventually_flattenedCentralRepresentativeEvaluation_eq_coefficientwise
      A
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S)) P
      ((boundary.simultaneousQuantitativeCentralAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data c r).sourceRepresentative q)
      ((boundary.simultaneousQuantitativeCentralAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data c r).source_germ_eq q)
      (boundary.simultaneousSupportedCoefficientRepresentative D representative
        offset radius Fsys x w₀ hw₀ data c r coefficients q)
      (boundary.simultaneousSupportedCoefficientRepresentative_germ_eq D
        representative offset radius Fsys x w₀ hw₀ data c r coefficients q)
      parameter
      (boundary.simultaneousQuantitativeAnalyticParameter_tendsto D
        representative offset radius Fsys x w₀ hw₀ data hA)
      outerValue coefficientValue u
      (fun n z ↦
        boundary.simultaneousQuantitativeAnalyticAfterValue_central D
          representative offset radius Fsys x w₀ hw₀ data hA c r.val z n)
  filter_upwards [hgeneric] with n hn
  change MvPolynomial.eval
      (fun z ↦ Sum.elim outerValue coefficientValue z n)
      ((boundary.simultaneousQuantitativeCentralAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data c r).sourceRepresentative q
          (parameter n)) = _
  have heta : (fun z ↦ Sum.elim outerValue coefficientValue z n) =
      Sum.elim (fun z ↦ outerValue z n) (fun z ↦ coefficientValue z n) := by
    funext z
    rcases z with z | z <;> rfl
  rw [heta]
  rw [hn]
  unfold ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseCentralEvaluation
    finiteSupportInitialEvaluation
  apply Finset.sum_congr rfl
  intro e he
  dsimp only [P, parameter, coefficientValue, u]
  congr 1
  change nestedSupportedCoefficientValue
      (((boundary.simultaneousNumericTrace D representative offset radius Fsys
        x w₀ hw₀ data c).simultaneous.transferCertificate r).source q)
      (boundary.simultaneousSupportedCoefficientRepresentative D representative
        offset radius Fsys x w₀ hw₀ data c r coefficients q)
      (boundary.simultaneousQuantitativeAnalyticParameter D representative offset
        radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r.val) e n =
    boundary.simultaneousQuantitativeSourceCoefficientValue D representative
      offset radius Fsys x w₀ hw₀ data hA c r coefficients q e n
  exact boundary.nestedSupportedCoefficientValue_eq_simultaneousQuantitative D
    representative offset radius Fsys x w₀ hw₀ data hA c r coefficients q e n

/-- The central analytic adapter supplies the exact numeric identity required
by one simultaneous quantitative step. -/
theorem eventually_simultaneousQuantitativeAnalyticCentralIdentity
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c)
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r) :
    ∀ᶠ n in atTop, ∀ b,
      boundary.simultaneousQuantitativeAnalyticAfterGeneratorValue D
          representative offset radius Fsys x w₀ hw₀ data hA c r b n =
        ∑ q, boundary.simultaneousQuantitativeAnalyticCentralCoefficient D
            representative offset radius Fsys x w₀ hw₀ data hA c r b q n *
          ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseCentralEvaluation
            A
            (terminalTotalDerivativeCount (fun _ :
              Fin (data.orderedCluster c).card ↦
                paperRankHermiteHigherCount boundary.S))
            (boundary.simultaneousQuantitativeSourceCoefficientValue D
              representative offset radius Fsys x w₀ hw₀ data hA c r
              coefficients q)
            (boundary.simultaneousQuantitativePostLogScale D representative offset
              radius Fsys x w₀ hw₀ data hA c r.val)
            (((boundary.simultaneousNumericTrace D representative offset radius
              Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q)
            n := by
  have hchange :=
    (boundary.simultaneousQuantitativeCentralAnalyticChange D representative
      offset radius Fsys x w₀ hw₀ data c r).eventually_targetValue_eq_sum
        (boundary.simultaneousQuantitativeAnalyticParameter D representative
          offset radius Fsys x w₀ hw₀ data hA)
        (boundary.simultaneousQuantitativeAnalyticParameter_tendsto D
          representative offset radius Fsys x w₀ hw₀ data hA)
        (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
          offset radius Fsys x w₀ hw₀ data hA c r.val)
        (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
          offset radius Fsys x w₀ hw₀ data hA c r.val)
  have hcomparison : ∀ᶠ n in atTop, ∀ q,
      (boundary.simultaneousQuantitativeCentralAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data c r).sourceValue
          (boundary.simultaneousQuantitativeAnalyticParameter D representative
            offset radius Fsys x w₀ hw₀ data hA)
          (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
            offset radius Fsys x w₀ hw₀ data hA c r.val)
          (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
            offset radius Fsys x w₀ hw₀ data hA c r.val) q n =
        ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseCentralEvaluation
          A
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S))
          (boundary.simultaneousQuantitativeSourceCoefficientValue D
            representative offset radius Fsys x w₀ hw₀ data hA c r
            coefficients q)
          (boundary.simultaneousQuantitativePostLogScale D representative offset
            radius Fsys x w₀ hw₀ data hA c r.val)
          (((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q)
          n := by
    apply Filter.eventually_all.mpr
    intro q
    exact boundary.eventually_simultaneousQuantitativeAnalyticCanonicalCentralValue_eq
      D representative offset radius Fsys x w₀ hw₀ data hA c r coefficients q
  filter_upwards [hchange, hcomparison] with n hn hcompare
  intro b
  simpa only [simultaneousQuantitativeAnalyticAfterGeneratorValue,
    simultaneousQuantitativeAnalyticCentralCoefficient, hcompare] using hn b

/-- Analyticity bounds the displayed-source change matrix from bounds for the
literal source assignment and smaller-prefix assignment. -/
theorem simultaneousQuantitativeAnalyticSourceCoefficient_bound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c)
    (hsource : ∀ z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c r.val)
        (boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c r z))
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count)
    (k : Fin (((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneousDisplayed r).source.count + 1)) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c r.val)
      (boundary.simultaneousQuantitativeAnalyticSourceCoefficient D
        representative offset radius Fsys x w₀ hw₀ data hA c r q k) := by
  apply (boundary.simultaneousQuantitativeSourceAnalyticChange D representative
    offset radius Fsys x w₀ hw₀ data c r).changeCoefficientValue_hasPolynomialUpperBound
      (boundary.simultaneousQuantitativeAnalyticParameter D representative
        offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticParameter_tendsto D
        representative offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r.val)
      (boundary.simultaneousQuantitativeBoundaryScale_eventually_ge_one D
        representative offset radius Fsys x w₀ hw₀ data hA c r.val)
  · intro z
    exact hsource (Sum.inl z)
  · intro z
    exact hsource (Sum.inr z)

/-- At a positive retained operation the op-sensitive source assignment is
the exact derivative assignment.  Hence the next retained source assignment
is literally the exact following assignment chosen at the preceding
boundary. -/
theorem simultaneousQuantitativeAnalyticSourceValue_succ
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (i : Fin (boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps) :
    boundary.simultaneousQuantitativeAnalyticSourceValue D representative offset
        radius Fsys x w₀ hw₀ data hA c i.succ =
      boundary.simultaneousQuantitativeAnalyticAfterValue D representative offset
        radius Fsys x w₀ hw₀ data hA c i.val := by
  funext z n
  rcases z with q | z
  · rfl
  · rcases z with br | q
    · rcases br with ⟨b, j⟩
      let φ := boundary.simultaneousQuantitativeReindex D representative offset
        radius Fsys x w₀ hw₀ data hA
      have hu : ∀ n k,
          (boundary.commonRealHermiteData D representative offset radius Fsys x
              w₀ hw₀ data hA).u0 <
            boundary.simultaneousReindexedPostLogScale D representative offset
              radius Fsys x w₀ hw₀ data c φ (i.val + 1) k n := by
        intro n k
        simpa only [φ, simultaneousReindexedPostLogScale_apply, Fin.val_succ]
          using boundary.simultaneousQuantitativePostLogScale_gt D
            representative offset radius Fsys x w₀ hw₀ data hA c i.succ k n
      simp only [simultaneousQuantitativeAnalyticSourceValue,
        simultaneousQuantitativeAnalyticAfterValue,
        finiteRealJetActualAssignment, realCentralTransferActualValue,
        simultaneousQuantitativeOperationJetSequence, Fin.val_succ]
      rw [boundary.simultaneousReindexedOperationJetSequence_sourceJet_of_pos D
        representative offset radius Fsys x w₀ hw₀ data hA c φ (i.val + 1)
        (Nat.succ_pos i.val) hu n b j]
      simp only [simultaneousQuantitativeExactSuccessorJets,
        IsAbel.realDerivativeJetSubstitutionData_sourceJet]
      have hscale :
          boundary.simultaneousReindexedPostLogScale D representative offset
              radius Fsys x w₀ hw₀ data c φ (i.val + 1) b n =
            boundary.simultaneousQuantitativePostLogScale D representative offset
              radius Fsys x w₀ hw₀ data hA c (i.val + 1) b n := by
        rw [boundary.simultaneousReindexedPostLogScale_apply D representative
          offset radius Fsys x w₀ hw₀ data c φ (i.val + 1) b n]
        rfl
      rw [hscale]
      unfold simultaneousQuantitativePostLogScale
        RepresentativeClusterSubsequence.orderedClusterSimultaneousPostLogScale
      rfl
    · rfl

/-- The combined next-source assignment is the assignment used by the
adjacent analytic change. -/
theorem simultaneousQuantitativeAnalyticSourceSymbolValue_succ
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (i : Fin (boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps) :
    boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D representative
        offset radius Fsys x w₀ hw₀ data hA c i.succ =
      boundary.simultaneousQuantitativeAdjacentSymbolValue D representative
        offset radius Fsys x w₀ hw₀ data hA c i := by
  funext z
  rcases z with z | z
  · exact congrFun
      (boundary.simultaneousQuantitativeAnalyticSourceValue_succ D
        representative offset radius Fsys x w₀ hw₀ data hA c i) z
  · rfl

/-- Analyticity bounds the central change matrix from bounds for the exact
following source assignment and the current smaller-prefix assignment. -/
theorem simultaneousQuantitativeAnalyticCentralCoefficient_bound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c)
    (hafter : ∀ z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c (r.val + 1))
        (boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c r.val z))
    (b : Fin (((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneousDisplayed r).central.count + 1))
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (r.val + 1))
      (boundary.simultaneousQuantitativeAnalyticCentralCoefficient D
        representative offset radius Fsys x w₀ hw₀ data hA c r b q) := by
  apply (boundary.simultaneousQuantitativeCentralAnalyticChange D representative
    offset radius Fsys x w₀ hw₀ data c r).changeCoefficientValue_hasPolynomialUpperBound
      (boundary.simultaneousQuantitativeAnalyticParameter D representative
        offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticParameter_tendsto D
        representative offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r.val)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r.val)
      (boundary.simultaneousQuantitativeBoundaryScale_eventually_ge_one D
        representative offset radius Fsys x w₀ hw₀ data hA c (r.val + 1))
  · intro z
    exact hafter (Sum.inl z)
  · intro z
    exact hafter (Sum.inr z)

/-- Analyticity bounds every internal-boundary matrix.  The smaller-prefix
assignment at `i+1` is rewritten to the one at `i` by its automatic
operation-independence. -/
theorem simultaneousQuantitativeAnalyticAdjacentCoefficient_bound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hafter : ∀
      (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
        radius Fsys x w₀ hw₀ data c) z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c (r.val + 1))
        (boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c r.val z))
    (i : Fin (boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps)
    (k : Fin (((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneousDisplayed i.succ).source.count + 1))
    (b : Fin (((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneousDisplayed i.castSucc).central.count + 1)) :
    HasPolynomialUpperBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c (i.val + 1))
      (boundary.simultaneousQuantitativeAnalyticAdjacentCoefficient D
        representative offset radius Fsys x w₀ hw₀ data hA c i k b) := by
  apply (boundary.simultaneousQuantitativeAdjacentAnalyticChange D representative
    offset radius Fsys x w₀ hw₀ data c i).changeCoefficientValue_hasPolynomialUpperBound
      (boundary.simultaneousQuantitativeAnalyticParameter D representative
        offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticParameter_tendsto D
        representative offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
        offset radius Fsys x w₀ hw₀ data hA c i.val)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c (i.val + 1))
      (boundary.simultaneousQuantitativeBoundaryScale_eventually_ge_one D
        representative offset radius Fsys x w₀ hw₀ data hA c (i.val + 1))
  · intro z
    exact hafter i.castSucc (Sum.inl z)
  · intro z
    apply (hafter i.castSucc (Sum.inr z)).congr
    intro n
    simpa only [simultaneousQuantitativeAnalyticAfterSymbolValue,
      Sum.elim_inr] using congrFun
      (boundary.simultaneousQuantitativeAnalyticPrefixValue_eq D representative
        offset radius Fsys x w₀ hw₀ data hA c (i.val + 1)
          i.castSucc.val z) n

/-- The two combined assignments used at an internal boundary agree. -/
theorem simultaneousQuantitativeAdjacentSymbolValue_eq_after
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (i : Fin (boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps) :
    boundary.simultaneousQuantitativeAdjacentSymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c i =
      boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D representative
        offset radius Fsys x w₀ hw₀ data hA c i.val := by
  funext z n
  rcases z with z | z
  · change boundary.simultaneousQuantitativeAnalyticAfterValue D representative
        offset radius Fsys x w₀ hw₀ data hA c i.val z n =
      boundary.simultaneousQuantitativeAnalyticAfterValue D representative
        offset radius Fsys x w₀ hw₀ data hA c i.val z n
    rfl
  · change boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c (i.val + 1) z n =
      boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c i.val z n
    exact congrFun
      (boundary.simultaneousQuantitativeAnalyticPrefixValue_eq D
        representative offset radius Fsys x w₀ hw₀ data hA c (i.val + 1)
        i.val z) n

/-- Bounds at the first source boundary and at every exact following
assignment give source-assignment bounds at all retained operations. -/
theorem simultaneousQuantitativeAnalyticSourceSymbolValue_bound_of_first
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hfirst : ∀ z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c 0)
        (boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c
          (boundary.simultaneousNumericStage D representative offset radius Fsys
            x w₀ hw₀ data c).certificate.firstCentralStepIndex z))
    (hafter : ∀
      (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
        radius Fsys x w₀ hw₀ data c) z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c (r.val + 1))
        (boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c r.val z)) :
    ∀ (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c) z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c r.val)
        (boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c r z) := by
  intro r z
  by_cases hr : r.val = 0
  · have hr' : r =
        (boundary.simultaneousNumericStage D representative offset radius Fsys x
          w₀ hw₀ data c).certificate.firstCentralStepIndex := Fin.ext hr
    subst r
    exact hfirst z
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hr
    have hklt : k <
        (boundary.simultaneousNumericStage D representative offset radius Fsys x
          w₀ hw₀ data c).certificate.terminalized.extraSteps := by
      omega
    let i : Fin (boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps :=
      ⟨k, hklt⟩
    have hr' : r = i.succ := Fin.ext hk
    subst r
    apply (hafter i.castSucc z).congr
    intro n
    have hsource :=
      boundary.simultaneousQuantitativeAnalyticSourceSymbolValue_succ D
        representative offset radius Fsys x w₀ hw₀ data hA c i
    have hadjacent :=
      boundary.simultaneousQuantitativeAdjacentSymbolValue_eq_after D
        representative offset radius Fsys x w₀ hw₀ data hA c i
    exact congrFun (congrFun (hsource.trans hadjacent) z) n

/-- The adjacent analytic change supplies all internal displayed-boundary
identities.  Independently selected analytic representatives are reconciled
by equality of their polynomial-valued germs. -/
theorem eventually_simultaneousQuantitativeAnalyticAdjacentIdentity
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (i : Fin (boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps) :
    ∀ᶠ n in atTop, ∀ k,
      boundary.simultaneousQuantitativeAnalyticBeforeValue D representative
          offset radius Fsys x w₀ hw₀ data hA c i.succ k n =
        ∑ b, boundary.simultaneousQuantitativeAnalyticAdjacentCoefficient D
            representative offset radius Fsys x w₀ hw₀ data hA c i k b n *
          boundary.simultaneousQuantitativeAnalyticAfterGeneratorValue D
            representative offset radius Fsys x w₀ hw₀ data hA c i.castSucc b n := by
  let parameter := boundary.simultaneousQuantitativeAnalyticParameter D
    representative offset radius Fsys x w₀ hw₀ data hA
  let sourceChange := boundary.simultaneousQuantitativeSourceAnalyticChange D
    representative offset radius Fsys x w₀ hw₀ data c i.succ
  let centralChange := boundary.simultaneousQuantitativeCentralAnalyticChange D
    representative offset radius Fsys x w₀ hw₀ data c i.castSucc
  let adjacent := boundary.simultaneousQuantitativeAdjacentAnalyticChange D
    representative offset radius Fsys x w₀ hw₀ data c i
  have hbeforeRepresentative : ∀ᶠ n in atTop, ∀ k,
      sourceChange.sourceRepresentative k (parameter n) =
        adjacent.targetRepresentative k (parameter n) := by
    apply Filter.eventually_all.mpr
    intro k
    exact (boundary.simultaneousQuantitativeAnalyticParameter_tendsto D
      representative offset radius Fsys x w₀ hw₀ data hA).eventually
        (analyticPolynomialRepresentatives_eventually_eq
          (0 : RestrictedBoxSpace p) (sourceChange.source_germ_eq k)
          (adjacent.target_germ_eq k) rfl)
  have hafterRepresentative : ∀ᶠ n in atTop, ∀ b,
      adjacent.sourceRepresentative b (parameter n) =
        centralChange.targetRepresentative b (parameter n) := by
    apply Filter.eventually_all.mpr
    intro b
    exact (boundary.simultaneousQuantitativeAnalyticParameter_tendsto D
      representative offset radius Fsys x w₀ hw₀ data hA).eventually
        (analyticPolynomialRepresentatives_eventually_eq
          (0 : RestrictedBoxSpace p) (adjacent.source_germ_eq b)
          (centralChange.target_germ_eq b) rfl)
  have hchange := adjacent.eventually_targetValue_eq_sum parameter
    (boundary.simultaneousQuantitativeAnalyticParameter_tendsto D
      representative offset radius Fsys x w₀ hw₀ data hA)
    (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
      offset radius Fsys x w₀ hw₀ data hA c i.val)
    (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
      offset radius Fsys x w₀ hw₀ data hA c (i.val + 1))
  filter_upwards [hbeforeRepresentative, hafterRepresentative, hchange] with
      n hbefore hafter hid
  intro k
  change MvPolynomial.eval
      (boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D
        representative offset radius Fsys x w₀ hw₀ data hA c i.succ · n)
      (sourceChange.sourceRepresentative k (parameter n)) = _
  rw [boundary.simultaneousQuantitativeAnalyticSourceSymbolValue_succ D
    representative offset radius Fsys x w₀ hw₀ data hA c i]
  rw [hbefore k]
  change adjacent.targetValue parameter
      (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
        offset radius Fsys x w₀ hw₀ data hA c i.val)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c (i.val + 1)) k n = _
  rw [hid k]
  apply Finset.sum_congr rfl
  intro b _hb
  congr 1
  change adjacent.sourceValue parameter
      (boundary.simultaneousQuantitativeAnalyticAfterValue D representative
        offset radius Fsys x w₀ hw₀ data hA c i.val)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c (i.val + 1)) b n = _
  change MvPolynomial.eval
      (boundary.simultaneousQuantitativeAdjacentSymbolValue D representative
        offset radius Fsys x w₀ hw₀ data hA c i · n)
      (adjacent.sourceRepresentative b (parameter n)) = _
  rw [hafter b]
  rw [boundary.simultaneousQuantitativeAdjacentSymbolValue_eq_after D
    representative offset radius Fsys x w₀ hw₀ data hA c i]
  rfl

/-! ## Canonical finite analytic packages -/

/-- Build the complete finite analytic change for one simultaneous operation.
All representatives, change matrices, and eventual identities are selected
canonically above.  The only inputs are polynomial bounds for the concrete
first source assignment and for the concrete exact assignments following the
retained operations. -/
noncomputable def simultaneousQuantitativeFiniteAnalyticChangeDataOfBounds
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hfirst : ∀ z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c 0)
        (boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c
          (boundary.simultaneousNumericStage D representative offset radius Fsys
            x w₀ hw₀ data c).certificate.firstCentralStepIndex z))
    (hafter : ∀
      (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
        radius Fsys x w₀ hw₀ data c) z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c (r.val + 1))
        (boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c r.val z))
    (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
      radius Fsys x w₀ hw₀ data c) :
    boundary.SimultaneousQuantitativeFiniteAnalyticChangeData D representative
      offset radius Fsys x w₀ hw₀ data hA c r
      (boundary.simultaneousSourceCoefficientDataChoice D representative offset
        radius Fsys x w₀ hw₀ data c r) := by
  have hsource :=
    boundary.simultaneousQuantitativeAnalyticSourceSymbolValue_bound_of_first D
      representative offset radius Fsys x w₀ hw₀ data hA c hfirst hafter
  refine {
    afterValue :=
      boundary.simultaneousQuantitativeAnalyticAfterGeneratorValue D
        representative offset radius Fsys x w₀ hw₀ data hA c r
    centralCoefficient :=
      boundary.simultaneousQuantitativeAnalyticCentralCoefficient D
        representative offset radius Fsys x w₀ hw₀ data hA c r
    beforeValue :=
      boundary.simultaneousQuantitativeAnalyticBeforeValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r
    sourceCoefficient :=
      boundary.simultaneousQuantitativeAnalyticSourceCoefficient D
        representative offset radius Fsys x w₀ hw₀ data hA c r
    central_identity :=
      boundary.eventually_simultaneousQuantitativeAnalyticCentralIdentity D
        representative offset radius Fsys x w₀ hw₀ data hA c r
        (boundary.simultaneousSourceCoefficientDataChoice D representative
          offset radius Fsys x w₀ hw₀ data c r)
    central_coefficient_bound := ?_
    source_identity :=
      boundary.eventually_simultaneousQuantitativeAnalyticSourceIdentity D
        representative offset radius Fsys x w₀ hw₀ data hA c r
        (boundary.simultaneousSourceCoefficientDataChoice D representative
          offset radius Fsys x w₀ hw₀ data c r)
    source_coefficient_bound := ?_ }
  · intro b q
    exact boundary.simultaneousQuantitativeAnalyticCentralCoefficient_bound D
      representative offset radius Fsys x w₀ hw₀ data hA c r (hafter r) b q
  · intro q k
    exact boundary.simultaneousQuantitativeAnalyticSourceCoefficient_bound D
      representative offset radius Fsys x w₀ hw₀ data hA c r (hsource r) q k

/-- Canonical finite analytic data for the full simultaneous segment.  The
source bound at every positive operation is obtained from the preceding exact
assignment, so callers provide it only once at operation zero.  The error-free
main-assignment bound remains an explicit numeric input because it is not a
consequence of finite analytic change of generators. -/
noncomputable def simultaneousQuantitativeFiniteAnalyticSegmentDataOfBounds
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hfirst : ∀ z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c 0)
        (boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c
          (boundary.simultaneousNumericStage D representative offset radius Fsys
            x w₀ hw₀ data c).certificate.firstCentralStepIndex z))
    (hafter : ∀
      (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
        radius Fsys x w₀ hw₀ data c) z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c (r.val + 1))
        (boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c r.val z))
    (hmain : ∀
      (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
        radius Fsys x w₀ hw₀ data c) z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c (r.val + 1))
        (finiteRealJetMainAssignment A
          (boundary.simultaneousQuantitativePostLogScale D representative offset
            radius Fsys x w₀ hw₀ data hA c r.val)
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S)) z)) :
    boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D representative
      offset radius Fsys x w₀ hw₀ data hA c := by
  refine {
    coefficients := fun r ↦
      boundary.simultaneousSourceCoefficientDataChoice D representative offset
        radius Fsys x w₀ hw₀ data c r
    smaller_bound := ?_
    main_bound := hmain
    change := fun r ↦
      boundary.simultaneousQuantitativeFiniteAnalyticChangeDataOfBounds D
        representative offset radius Fsys x w₀ hw₀ data hA c hfirst hafter r
    adjacentCoefficient :=
      boundary.simultaneousQuantitativeAnalyticAdjacentCoefficient D
        representative offset radius Fsys x w₀ hw₀ data hA c
    adjacent_coefficient_bound := ?_
    adjacent_identity := ?_ }
  · intro r z
    apply (hafter r (Sum.inr z)).congr
    intro n
    rfl
  · intro i k b
    exact boundary.simultaneousQuantitativeAnalyticAdjacentCoefficient_bound D
      representative offset radius Fsys x w₀ hw₀ data hA c hafter i k b
  · intro i
    exact boundary.eventually_simultaneousQuantitativeAnalyticAdjacentIdentity D
      representative offset radius Fsys x w₀ hw₀ data hA c i

/-- Existence form of the canonical segment constructor, convenient for
downstream APIs which quantify over a simultaneous numeric segment. -/
theorem nonempty_simultaneousQuantitativeFiniteAnalyticSegmentData_of_bounds
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hfirst : ∀ z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c 0)
        (boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c
          (boundary.simultaneousNumericStage D representative offset radius Fsys
            x w₀ hw₀ data c).certificate.firstCentralStepIndex z))
    (hafter : ∀
      (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
        radius Fsys x w₀ hw₀ data c) z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c (r.val + 1))
        (boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c r.val z))
    (hmain : ∀
      (r : boundary.SimultaneousAnalyticOperationIndex D representative offset
        radius Fsys x w₀ hw₀ data c) z,
      HasPolynomialUpperBound atTop
        (boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c (r.val + 1))
        (finiteRealJetMainAssignment A
          (boundary.simultaneousQuantitativePostLogScale D representative offset
            radius Fsys x w₀ hw₀ data hA c r.val)
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S)) z)) :
    Nonempty
      (boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
        representative offset radius Fsys x w₀ hw₀ data hA c) :=
  ⟨boundary.simultaneousQuantitativeFiniteAnalyticSegmentDataOfBounds D
    representative offset radius Fsys x w₀ hw₀ data hA c hfirst hafter hmain⟩

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
