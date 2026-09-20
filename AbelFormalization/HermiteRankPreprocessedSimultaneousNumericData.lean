import AbelFormalization.HermiteRankPreprocessedIndividualQuantitativeInputs
import AbelFormalization.OrderedClusterSimultaneousNumericQuantitativeTransfer

/-!
# Numeric simultaneous data for the preprocessed Hermite boundary

The coefficient ring of a simultaneous cluster operation is itself a
smaller-prefix polynomial ring over real analytic germs.  Only finitely many
of those coefficient polynomials occur in the supports of the canonical
source family.  We evaluate common analytic representatives of precisely
that finite family along the concrete translated Hermite parameter and the
concrete smaller-prefix assignment.

The resulting coefficient sequences feed the numeric simultaneous transfer
without defining a sequence-valued homomorphism on all analytic germs.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

namespace RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
namespace FiniteMovingCoefficientData

/-- Evaluate one polynomial-valued analytic representative along a parameter
sequence and a moving assignment of its polynomial symbols. -/
def polynomialValueAlong
    {p : ℕ} {κ σ : Type} [Finite κ]
    {polynomial : κ → MvPolynomial σ (RealAnalyticGerm p)}
    (coefficients : FiniteMovingCoefficientData polynomial)
    (parameter : ℕ → RestrictedBoxSpace p)
    (symbolValue : σ → ℕ → ℝ) (i : κ) (n : ℕ) : ℝ :=
  MvPolynomial.eval (fun z ↦ symbolValue z n)
    (coefficients.representative i (parameter n))

/-- Analyticity of the finitely many representative coefficients and bounds
for the moving polynomial symbols give a bound for the whole evaluated
coefficient polynomial. -/
theorem polynomialValueAlong_hasPolynomialUpperBound
    {p : ℕ} {κ σ : Type} [Finite κ]
    {polynomial : κ → MvPolynomial σ (RealAnalyticGerm p)}
    (coefficients : FiniteMovingCoefficientData polynomial)
    (parameter : ℕ → RestrictedBoxSpace p)
    (hparameter : Tendsto parameter atTop
      (𝓝 (0 : RestrictedBoxSpace p)))
    (symbolValue : σ → ℕ → ℝ) (scale : ℕ → ℝ)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hsymbol : ∀ z,
      HasPolynomialUpperBound atTop scale (symbolValue z))
    (i : κ) :
    HasPolynomialUpperBound atTop scale
      (coefficients.polynomialValueAlong parameter symbolValue i) := by
  exact analyticMvPolynomialEvaluation_hasPolynomialUpperBound
    (coefficients.representative i) (polynomial i).support
    coefficients.neighborhood (0 : RestrictedBoxSpace p)
    coefficients.origin_mem parameter hparameter
    (coefficients.support_subset i)
    (fun e _ ↦ coefficients.coefficient_analytic i e)
    symbolValue hscale hsymbol

end FiniteMovingCoefficientData

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

/-- The algebraic stage at one cluster of the selected paper trace. -/
abbrev simultaneousNumericStage (c : Fin data.orderedClusterCount) :=
  boundary.preprocessed.descent.clusterStage c

/-- The chosen displayed transfer data at one cluster. -/
abbrev simultaneousNumericTrace (c : Fin data.orderedClusterCount) :=
  boundary.preprocessed.transferTrace.stage c

/-- Supported coefficients of all canonical source polynomials at one
simultaneous operation.  This is finite although the ambient monomial type is
not. -/
abbrev SimultaneousSourceCoefficientIndex
    (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) :=
  Sigma fun q : Fin ((boundary.simultaneousNumericTrace D representative
    offset radius Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count ↦
    {e // e ∈ (((boundary.simultaneousNumericTrace D representative offset
      radius Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q).support}

/-- The smaller-prefix coefficient polynomial named by a supported outer
monomial of a canonical simultaneous source. -/
def simultaneousSourceCoefficientPolynomial
    (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (qe : boundary.SimultaneousSourceCoefficientIndex D representative offset
      radius Fsys x w₀ hw₀ data c r) :
    data.OrderedClusterPrefixRing (RealAnalyticGerm p)
      (paperRankHermiteHigherCount boundary.S) c.val :=
  ((boundary.simultaneousNumericTrace D representative offset radius Fsys x
    w₀ hw₀ data c).simultaneous.transferCertificate r).source qe.1 |>.coeff qe.2

/-- A common finite moving representative family for the actual supported
coefficient polynomials of one simultaneous step. -/
abbrev SimultaneousSourceCoefficientData
    (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) :=
  FiniteMovingCoefficientData
    (boundary.simultaneousSourceCoefficientPolynomial D representative offset
      radius Fsys x w₀ hw₀ data c r)

/-- Such a finite supported-coefficient family always has common analytic
representatives. -/
theorem nonempty_simultaneousSourceCoefficientData
    (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) :
    Nonempty (boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r) := by
  exact nonempty_finiteMovingCoefficientData
    (boundary.simultaneousSourceCoefficientPolynomial D representative offset
      radius Fsys x w₀ hw₀ data c r)

/-- Numeric value of one outer coefficient.  On the actual support it is the
evaluation of its moving analytic representative at the concrete
smaller-prefix Hermite assignment; outside the support it is zero. -/
def simultaneousSourceCoefficientValue
    (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset
      radius Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count)
    (e : ClusterOperationSymbol
      (Fin (data.orderedCluster c).card)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S)) →₀ ℕ)
    (n : ℕ) : ℝ :=
  if he : e ∈ (((boundary.simultaneousNumericTrace D representative offset
      radius Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q).support then
    coefficients.polynomialValueAlong
      (fun k ↦ (boundary.selectedTranslatedParameter D representative offset
        radius Fsys x w₀ hw₀ data k).2)
      (boundary.simultaneousSmallerPrefixSequenceValue D representative offset
        radius Fsys x w₀ hw₀ data c r.val)
      ⟨q, ⟨e, he⟩⟩ n
  else 0

/-- The constructed coefficient value is polynomially bounded on every
actual canonical-source support, assuming only bounds for the concrete
smaller-prefix coordinates. -/
theorem simultaneousSourceCoefficientValue_hasPolynomialUpperBound
    (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (scale : ℕ → ℝ) (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hsmaller : ∀ z, HasPolynomialUpperBound atTop scale
      (boundary.simultaneousSmallerPrefixSequenceValue D representative offset
        radius Fsys x w₀ hw₀ data c r.val z))
    (q : Fin ((boundary.simultaneousNumericTrace D representative offset
      radius Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).count)
    (e : ClusterOperationSymbol
      (Fin (data.orderedCluster c).card)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S)) →₀ ℕ)
    (he : e ∈ (((boundary.simultaneousNumericTrace D representative offset
      radius Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q).support) :
    HasPolynomialUpperBound atTop scale
        (boundary.simultaneousSourceCoefficientValue D representative offset
        radius Fsys x w₀ hw₀ data c r coefficients q e) := by
  refine (coefficients.polynomialValueAlong_hasPolynomialUpperBound
    (fun k ↦ (boundary.selectedTranslatedParameter D representative offset
      radius Fsys x w₀ hw₀ data k).2)
    (boundary.selectedTranslatedParameter_box_tendsto_zero D representative
      offset radius Fsys x w₀ hw₀ data)
    (boundary.simultaneousSmallerPrefixSequenceValue D representative offset
      radius Fsys x w₀ hw₀ data c r.val) scale hscale hsmaller
    ⟨q, ⟨e, he⟩⟩).congr ?_
  intro n
  rw [simultaneousSourceCoefficientValue, dite_eq_left he]

/-- A canonical choice of common representatives for the finitely many
supported coefficients at a simultaneous operation. -/
noncomputable def simultaneousSourceCoefficientDataChoice
    (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) :
    boundary.SimultaneousSourceCoefficientData D representative offset radius
      Fsys x w₀ hw₀ data c r :=
  Classical.choice
    (boundary.nonempty_simultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)

/-- The literal unshifted raw-time sequence selected by preprocessing. -/
abbrev simultaneousNumericRawTime (c : Fin data.orderedClusterCount) :=
  boundary.selectedClusterRawTime D representative offset radius Fsys x w₀
    hw₀ data c

/-- Canonical post-log scale at an unshifted simultaneous operation. -/
abbrev simultaneousNumericPostLogScale
    (c : Fin data.orderedClusterCount) (r : ℕ) :=
  boundary.simultaneousPostLogScale D representative offset radius Fsys x w₀
    hw₀ data c r

/-- Canonical boundary scale before `r` simultaneous decrements. -/
abbrev simultaneousNumericBoundaryScale
    (c : Fin data.orderedClusterCount) (r : ℕ) :=
  data.orderedClusterSimultaneousBoundaryScale c A
    (boundary.simultaneousNumericRawTime D representative offset radius Fsys x
      w₀ hw₀ data c) (boundary.preprocessed.fixedSteps c)
    (boundary.preprocessed.fixedOrder c) r

/-- The concrete Hermite jet family, cast only across the definitional
paper-rank derivative-count identity expected by the algebraic trace. -/
def simultaneousNumericRealJetSequence
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousNumericPostLogScale D representative offset radius
          Fsys x w₀ hw₀ data c r i n) :
    ∀ n i, RealCentralJetSubstitutionData A
      (boundary.simultaneousNumericPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c r i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S) i) := by
  intro n i
  exact castRealCentralJetSubstitutionData
    (boundary.simultaneousRealJetSequence D representative offset radius Fsys
      x w₀ hw₀ data hA c r hu n i) rfl
    (by
      simpa only [terminalTotalDerivativeCount] using
        (paperRankHermiteHigherCount_add_one boundary.S).symm)

/-- The real-jet mode forced by the actual history of the ordered-cluster
trace.  At the first simultaneous operation, a block already touched by an
individual balancing step carries exact derivatives, while an untouched
block still carries its original Hermite jet.  Every later simultaneous
operation starts from the exact central output of its predecessor and hence
uses exact derivative jets in every block. -/
def simultaneousNumericOperationJetSequence
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousNumericPostLogScale D representative offset radius
          Fsys x w₀ hw₀ data c r i n) :
    ∀ n i, RealCentralJetSubstitutionData A
      (boundary.simultaneousNumericPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c r i n)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S) i) := by
  intro n i
  by_cases hr : r = 0
  · by_cases htouched :
        boundary.preprocessed.fixedOrder c
            ((data.orderedClusterBalancingToActiveEquiv c).symm i) ∈
          boundary.preprocessed.fixedSteps c
    · exact hA.realDerivativeJetSubstitutionData (hA.inverse_pos _)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster c).card ↦
            paperRankHermiteHigherCount boundary.S) i)
    · exact boundary.simultaneousNumericRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c r hu n i
  · exact hA.realDerivativeJetSubstitutionData (hA.inverse_pos _)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S) i)

/-- The op-sensitive jet error is the Hermite error only for an untouched
block at the first simultaneous operation; all other errors vanish exactly. -/
theorem simultaneousNumericOperationJetSequence_error_superpolynomialDecay_of_hierarchy
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousNumericPostLogScale D representative offset radius
          Fsys x w₀ hw₀ data c r i n)
    (R : ℕ → ℝ) {tail : ℕ}
    (card_eq : tail + 1 = (data.orderedCluster c).card)
    (hierarchy : BalancedRealJetTransferHierarchy tail
      (fun i n ↦ boundary.simultaneousNumericPostLogScale D representative
        offset radius Fsys x w₀ hw₀ data c r (finCongr card_eq i) n) R)
    (i : Fin (data.orderedCluster c).card)
    (q : Fin (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S) i)) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n ↦ (boundary.simultaneousNumericOperationJetSequence D
        representative offset radius Fsys x w₀ hw₀ data hA c r hu n i).error q) := by
  by_cases hr : r = 0
  · subst r
    by_cases htouched :
        boundary.preprocessed.fixedOrder c
            ((data.orderedClusterBalancingToActiveEquiv c).symm i) ∈
          boundary.preprocessed.fixedSteps c
    · apply (Asymptotics.superpolynomialDecay_zero atTop R).congr
      intro n
      simp [simultaneousNumericOperationJetSequence, htouched]
    · let q' : Fin (paperRankHermitePositiveDerivativeCount boundary.S) :=
        Fin.cast (paperRankHermiteHigherCount_add_one boundary.S) q
      have herror :=
        boundary.simultaneousRealJetSequence_error_superpolynomialDecay_of_hierarchy
          D representative offset radius Fsys x w₀ hw₀ data hA c 0 hu R
          card_eq hierarchy i q'
      apply herror.congr
      intro n
      simp [simultaneousNumericOperationJetSequence, htouched,
        simultaneousNumericRealJetSequence, q']
  · apply (Asymptotics.superpolynomialDecay_zero atTop R).congr
    intro n
    simp [simultaneousNumericOperationJetSequence, hr]

/-- The two finite evaluated changes of generators surrounding one concrete
Hermite simultaneous operation.  These are the only analytic compatibility
seams: every coefficient value is numeric, and both identities are required
only eventually along the selected parameter sequence. -/
structure SimultaneousFiniteAnalyticChangeData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousNumericPostLogScale D representative offset radius
          Fsys x w₀ hw₀ data c r.val i n) where
  afterValue : Fin (((boundary.simultaneousNumericTrace D representative
    offset radius Fsys x w₀ hw₀ data c).simultaneousDisplayed r).central.count + 1) →
      ℕ → ℝ
  centralCoefficient :
    Fin (((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneousDisplayed r).central.count + 1) →
    Fin ((boundary.simultaneousNumericTrace D representative offset radius Fsys
      x w₀ hw₀ data c).simultaneous.transferCertificate r).count → ℕ → ℝ
  beforeValue : Fin (((boundary.simultaneousNumericTrace D representative
    offset radius Fsys x w₀ hw₀ data c).simultaneousDisplayed r).source.count + 1) →
      ℕ → ℝ
  sourceCoefficient :
    Fin ((boundary.simultaneousNumericTrace D representative offset radius Fsys
      x w₀ hw₀ data c).simultaneous.transferCertificate r).count →
    Fin (((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneousDisplayed r).source.count + 1) →
      ℕ → ℝ
  central_identity : ∀ᶠ n in atTop, ∀ b,
    afterValue b n =
      ∑ q, centralCoefficient b q n *
        ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseCentralEvaluation
          A
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S))
          (boundary.simultaneousSourceCoefficientValue D representative offset
            radius Fsys x w₀ hw₀ data c r coefficients q)
          (boundary.simultaneousNumericPostLogScale D representative offset
            radius Fsys x w₀ hw₀ data c r.val)
          (((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q) n
  central_coefficient_bound : ∀ b q,
    HasPolynomialUpperBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c (r.val + 1))
      (centralCoefficient b q)
  source_identity : ∀ᶠ n in atTop, ∀ q,
    ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseSourceEvaluation
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S))
          (boundary.simultaneousSourceCoefficientValue D representative offset
            radius Fsys x w₀ hw₀ data c r coefficients q)
          (boundary.simultaneousNumericPostLogScale D representative offset
            radius Fsys x w₀ hw₀ data c r.val)
          (boundary.simultaneousNumericOperationJetSequence D representative offset
            radius Fsys x w₀ hw₀ data hA c r.val hu)
          (((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data c).simultaneous.transferCertificate r).source q) n =
      ∑ k, sourceCoefficient q k n * beforeValue k n
  source_coefficient_bound : ∀ q k,
    HasPolynomialUpperBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c r.val)
      (sourceCoefficient q k)

/-- The balancing and separation data of the selected preprocessing stage
give the two hierarchy records required by the numeric simultaneous step,
without any reindexing of the selected sequence. -/
theorem simultaneousNumericTransferHierarchies
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (r : ℕ)
    (hN : (((r + 6 : ℕ) : ℝ)) ≤ separation.N c) :
    FiniteRealJetTransferHierarchies (data.orderedCluster c).card
      (boundary.simultaneousNumericPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c r)
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c (r + 1))
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c r) := by
  exact hA.orderedClusterSimultaneousStep_transferHierarchies data c
    (boundary.simultaneousNumericRawTime D representative offset radius Fsys x
      w₀ hw₀ data c)
    (fun n ↦ data.orderedClusterMinTime c
      (boundary.preprocessed.balancingSubsequence n))
    (fun n ↦ boundary.preprocessed.plans n c)
    (boundary.preprocessed.fixedSteps c) (boundary.preprocessed.fixedOrder c)
    (fun n ↦ boundary.preprocessed.plans_steps n c)
    (fun n ↦ boundary.preprocessed.plans_finalOrder n c) r
    (separation.separationConstant_pos c) hN
    (boundary.selectedClusterMinTime_tendsto_atTop D representative offset
      radius Fsys x w₀ hw₀ data hA c) (separation.separated c)

/-- The generic numeric simultaneous-step package specialized to the
selected paper stage and its literal unshifted raw-time sequence. -/
abbrev HermiteSimultaneousNumericQuantitativeData
    (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) :=
  RepresentativeClusterSubsequence.OrderedClusterPreprocessedAlgebraicStage.FullTransferTraceData.SimultaneousNumericQuantitativeData
    (boundary.simultaneousNumericTrace D representative offset radius Fsys x
      w₀ hw₀ data c) A
    (boundary.simultaneousNumericRawTime D representative offset radius Fsys x
      w₀ hw₀ data c) r

/-- Construct every numeric input of one concrete Hermite simultaneous step.
The source coefficients and Hermite error estimates are discharged here;
the caller supplies bounds for the concrete smaller-prefix and main
coordinates and the two finite analytic changes of displayed generators. -/
noncomputable def hermiteSimultaneousNumericQuantitativeData
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (hN : (((r.val + 6 : ℕ) : ℝ)) ≤ separation.N c)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousNumericPostLogScale D representative offset radius
          Fsys x w₀ hw₀ data c r.val i n)
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (hsmaller : ∀ z, HasPolynomialUpperBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c (r.val + 1))
      (boundary.simultaneousSmallerPrefixSequenceValue D representative offset
        radius Fsys x w₀ hw₀ data c r.val z))
    (hmain : ∀ z, HasPolynomialUpperBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c (r.val + 1))
      (finiteRealJetMainAssignment A
        (boundary.simultaneousNumericPostLogScale D representative offset radius
          Fsys x w₀ hw₀ data c r.val)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster c).card ↦
            paperRankHermiteHigherCount boundary.S)) z))
    (change : boundary.SimultaneousFiniteAnalyticChangeData D representative
      offset radius Fsys x w₀ hw₀ data hA c r coefficients hu) :
    boundary.HermiteSimultaneousNumericQuantitativeData D representative offset
      radius Fsys x w₀ hw₀ data c r := by
  let hierarchies := boundary.simultaneousNumericTransferHierarchies D
    representative offset radius Fsys x w₀ hw₀ data separation hA c r.val hN
  have hscale : ∀ᶠ n in atTop,
      1 ≤ boundary.simultaneousNumericBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data c (r.val + 1) n :=
    hierarchies.scale_ge_two.mono fun _ hn ↦ one_le_two.trans hn
  refine {
    coefficientValue := boundary.simultaneousSourceCoefficientValue D
      representative offset radius Fsys x w₀ hw₀ data c r coefficients
    jets := boundary.simultaneousNumericOperationJetSequence D representative offset
      radius Fsys x w₀ hw₀ data hA c r.val hu
    afterValue := change.afterValue
    centralCoefficient := change.centralCoefficient
    beforeValue := change.beforeValue
    sourceCoefficient := change.sourceCoefficient
    coefficient_bound := ?_
    main_bound := hmain
    jet_error := ?_
    central_identity := change.central_identity
    central_coefficient_bound := change.central_coefficient_bound
    source_identity := change.source_identity
    source_coefficient_bound := change.source_coefficient_bound
  }
  · intro q e he
    exact boundary.simultaneousSourceCoefficientValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data c r coefficients
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c (r.val + 1)) hscale hsmaller q e he
  · intro i q
    rcases hierarchies with ⟨tail, card_eq, hierarchy, _domination⟩
    exact boundary.simultaneousNumericOperationJetSequence_error_superpolynomialDecay_of_hierarchy
      D representative offset radius Fsys x w₀ hw₀ data hA c r.val hu
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c (r.val + 1)) card_eq hierarchy i q

/-- Backward quantitative propagation through one actual preprocessed
Hermite simultaneous operation.  The operation index and all sequences are
unshifted, so the result is definitionally compatible with the terminal
boundary at the last simultaneous operation. -/
theorem hermiteSimultaneousBeforeValue_lower_of_afterValue_lower
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (r : Fin ((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
    (hN : (((r.val + 6 : ℕ) : ℝ)) ≤ separation.N c)
    (hu : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousNumericPostLogScale D representative offset radius
          Fsys x w₀ hw₀ data c r.val i n)
    (coefficients : boundary.SimultaneousSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c r)
    (hsmaller : ∀ z, HasPolynomialUpperBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c (r.val + 1))
      (boundary.simultaneousSmallerPrefixSequenceValue D representative offset
        radius Fsys x w₀ hw₀ data c r.val z))
    (hmain : ∀ z, HasPolynomialUpperBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c (r.val + 1))
      (finiteRealJetMainAssignment A
        (boundary.simultaneousNumericPostLogScale D representative offset radius
          Fsys x w₀ hw₀ data c r.val)
        (terminalTotalDerivativeCount (fun _ :
          Fin (data.orderedCluster c).card ↦
            paperRankHermiteHigherCount boundary.S)) z))
    (change : boundary.SimultaneousFiniteAnalyticChangeData D representative
      offset radius Fsys x w₀ hw₀ data hA c r coefficients hu)
    (hafter : HasInversePowerLowerBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c (r.val + 1)) change.afterValue) :
    HasInversePowerLowerBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c r.val) change.beforeValue := by
  let step := boundary.hermiteSimultaneousNumericQuantitativeData D
    representative offset radius Fsys x w₀ hw₀ data separation hA c r hN hu
      coefficients hsmaller hmain change
  exact (boundary.simultaneousNumericTrace D representative offset radius Fsys
    x w₀ hw₀ data c).simultaneousBeforeValue_lower_of_afterValue_lower_numeric_of_data
      r hA
      (boundary.simultaneousNumericRawTime D representative offset radius Fsys x
        w₀ hw₀ data c)
      (fun n ↦ data.orderedClusterMinTime c
        (boundary.preprocessed.balancingSubsequence n))
      (fun n ↦ boundary.preprocessed.plans n c)
      (fun n ↦ boundary.preprocessed.plans_steps n c)
      (fun n ↦ boundary.preprocessed.plans_finalOrder n c)
      (separation.separationConstant_pos c) hN
      (boundary.selectedClusterMinTime_tendsto_atTop D representative offset
        radius Fsys x w₀ hw₀ data hA c) (separation.separated c) step hafter

/-- Concrete Hermite inputs for the whole simultaneous segment.  The
pointwise records are the two finite analytic changes at each displayed
operation.  The single additional eventual identity changes the numeric
family across each retained internal boundary. -/
structure SimultaneousFiniteAnalyticSegmentData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) where
  hu : (r : Fin ((boundary.simultaneousNumericStage D representative offset
    radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) →
    ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
        w₀ hw₀ data hA).u0 <
        boundary.simultaneousNumericPostLogScale D representative offset radius
          Fsys x w₀ hw₀ data c r.val i n
  coefficients : (r : Fin ((boundary.simultaneousNumericStage D representative
    offset radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) →
    boundary.SimultaneousSourceCoefficientData D representative offset radius
      Fsys x w₀ hw₀ data c r
  smaller_bound : ∀ (r : Fin ((boundary.simultaneousNumericStage D
    representative offset radius Fsys x w₀ hw₀ data
    c).certificate.terminalized.extraSteps + 1)) z,
    HasPolynomialUpperBound atTop
    (boundary.simultaneousNumericBoundaryScale D representative offset radius
      Fsys x w₀ hw₀ data c (r.val + 1))
    (boundary.simultaneousSmallerPrefixSequenceValue D representative offset
      radius Fsys x w₀ hw₀ data c r.val z)
  main_bound : ∀ (r : Fin ((boundary.simultaneousNumericStage D
    representative offset radius Fsys x w₀ hw₀ data
    c).certificate.terminalized.extraSteps + 1)) z,
    HasPolynomialUpperBound atTop
    (boundary.simultaneousNumericBoundaryScale D representative offset radius
      Fsys x w₀ hw₀ data c (r.val + 1))
    (finiteRealJetMainAssignment A
      (boundary.simultaneousNumericPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c r.val)
      (terminalTotalDerivativeCount (fun _ :
        Fin (data.orderedCluster c).card ↦
          paperRankHermiteHigherCount boundary.S)) z)
  change : (r : Fin ((boundary.simultaneousNumericStage D representative offset
    radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) →
    boundary.SimultaneousFiniteAnalyticChangeData D representative offset radius
      Fsys x w₀ hw₀ data hA c r (coefficients r) (hu r)
  adjacentCoefficient :
    (i : Fin (boundary.simultaneousNumericStage D representative offset radius
      Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps) →
    Fin (((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneousDisplayed i.succ).source.count + 1) →
    Fin (((boundary.simultaneousNumericTrace D representative offset radius
      Fsys x w₀ hw₀ data c).simultaneousDisplayed i.castSucc).central.count + 1) →
      ℕ → ℝ
  adjacent_coefficient_bound : ∀ i k b,
    HasPolynomialUpperBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c (i.val + 1))
      (adjacentCoefficient i k b)
  adjacent_identity : ∀ i, ∀ᶠ n in atTop, ∀ k,
    (change i.succ).beforeValue k n =
      ∑ b, adjacentCoefficient i k b n *
        (change i.castSucc).afterValue b n

/-- The generic numeric segment package specialized to the literal selected
paper sequence. -/
abbrev HermiteSimultaneousNumericSegmentQuantitativeData
    (c : Fin data.orderedClusterCount) :=
  RepresentativeClusterSubsequence.OrderedClusterPreprocessedAlgebraicStage.FullTransferTraceData.SimultaneousNumericSegmentQuantitativeData
    (boundary.simultaneousNumericTrace D representative offset radius Fsys x
      w₀ hw₀ data c) A
    (boundary.simultaneousNumericRawTime D representative offset radius Fsys x
      w₀ hw₀ data c)

/-- Build the complete numeric simultaneous segment pointwise from concrete
Hermite steps.  The global margin supplies every operation-specific margin,
including the first operation when there are no extra retained steps. -/
noncomputable def hermiteSimultaneousNumericSegmentQuantitativeData
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hN : (((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 6 :
        ℕ) : ℝ) ≤ separation.N c)
    (segment : boundary.SimultaneousFiniteAnalyticSegmentData D representative
      offset radius Fsys x w₀ hw₀ data hA c) :
    boundary.HermiteSimultaneousNumericSegmentQuantitativeData D representative
      offset radius Fsys x w₀ hw₀ data c := by
  let step : (r : Fin ((boundary.simultaneousNumericStage D representative
      offset radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1)) →
      boundary.HermiteSimultaneousNumericQuantitativeData D representative
        offset radius Fsys x w₀ hw₀ data c r := fun r ↦
    boundary.hermiteSimultaneousNumericQuantitativeData D representative offset
      radius Fsys x w₀ hw₀ data separation hA c r (by
        calc
          ((r.val + 6 : ℕ) : ℝ) ≤
              (((boundary.simultaneousNumericStage D representative offset
                radius Fsys x w₀ hw₀ data
                c).certificate.terminalized.extraSteps + 6 : ℕ) : ℝ) := by
            exact_mod_cast Nat.add_le_add_right
              (Nat.le_of_lt_succ r.isLt) 6
          _ ≤ separation.N c := hN)
      (segment.hu r) (segment.coefficients r) (segment.smaller_bound r)
      (segment.main_bound r) (segment.change r)
  refine {
    step := step
    adjacentCoefficient := segment.adjacentCoefficient
    adjacent_coefficient_bound := segment.adjacent_coefficient_bound
    adjacent_identity := ?_
  }
  intro i
  simpa only [step, hermiteSimultaneousNumericQuantitativeData] using
    segment.adjacent_identity i

/-- Propagate a lower bound from the final concrete Hermite simultaneous
output through every extra retained operation and the first simultaneous
operation.  The generic recursion handles `extraSteps = 0` without a
separate hypothesis or case split. -/
theorem hermiteSimultaneousFirstBeforeValue_lower_of_terminalAfterValue_lower
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hN : (((boundary.simultaneousNumericStage D representative offset
      radius Fsys x w₀ hw₀ data c).certificate.terminalized.extraSteps + 6 :
        ℕ) : ℝ) ≤ separation.N c)
    (segment : boundary.SimultaneousFiniteAnalyticSegmentData D representative
      offset radius Fsys x w₀ hw₀ data hA c)
    (hterminal : HasInversePowerLowerBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c
        ((boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
      (segment.change (Fin.last
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.terminalized.extraSteps)).afterValue) :
    HasInversePowerLowerBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c 0)
      (segment.change
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.firstCentralStepIndex).beforeValue := by
  let numeric := boundary.hermiteSimultaneousNumericSegmentQuantitativeData D
    representative offset radius Fsys x w₀ hw₀ data separation hA c hN
      segment
  have hterminal' : HasInversePowerLowerBound atTop
      (boundary.simultaneousNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data c
        ((boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.terminalized.extraSteps + 1))
      (numeric.step (Fin.last
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.terminalized.extraSteps)).afterValue := by
    simpa only [numeric, hermiteSimultaneousNumericSegmentQuantitativeData,
      hermiteSimultaneousNumericQuantitativeData] using hterminal
  have hresult := (boundary.simultaneousNumericTrace D representative offset
    radius Fsys x w₀ hw₀ data c).firstBeforeValue_lower_of_terminalAfterValue_lower_numeric
      hA
      (boundary.simultaneousNumericRawTime D representative offset radius Fsys x
        w₀ hw₀ data c)
      (fun n ↦ data.orderedClusterMinTime c
        (boundary.preprocessed.balancingSubsequence n))
      (fun n ↦ boundary.preprocessed.plans n c)
      (fun n ↦ boundary.preprocessed.plans_steps n c)
      (fun n ↦ boundary.preprocessed.plans_finalOrder n c)
      (separation.separationConstant_pos c) hN
      (boundary.selectedClusterMinTime_tendsto_atTop D representative offset
        radius Fsys x w₀ hw₀ data hA c) (separation.separated c) numeric
      hterminal'
  simpa only [numeric, hermiteSimultaneousNumericSegmentQuantitativeData,
    hermiteSimultaneousNumericQuantitativeData] using hresult

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
