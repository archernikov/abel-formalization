import AbelFormalization.HermiteRankPreprocessedRealJetData
import AbelFormalization.OrderedClusterPreprocessedQuantitativeTrace

/-!
# Individual quantitative inputs for the preprocessed Hermite boundary

This module turns the concrete real-Hermite jets on every fixed individual
balancing step into the `IndividualQuantitativeInputs` consumed by the full
preprocessed trace.  A single common tail makes every Hermite scale exceed
the threshold in the common strip lemma.

The generic ring-homomorphic trace is instantiated below at the honest germ
basepoint, while a separate finite representative package supplies moving
coefficient values without asserting a global moving germ homomorphism.  The
final exact-boundary constructor is deliberately conditional: literal
Hermite assignments do not generally provide its adjacent assignment
equality.  `HermiteRankPreprocessedIndividualNumericData` records the exact
Hermite-error obstruction and gives the production coefficientwise boundary
interface used for the moving application.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped Topology BigOperators

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

/-- The translated bounded parameter selected by preprocessing tends to the
origin, as required by analytic coefficient representatives. -/
theorem selectedTranslatedParameter_box_tendsto_zero :
    Tendsto (fun n ↦
      (boundary.selectedTranslatedParameter D representative offset radius
        Fsys x w₀ hw₀ data n).2) atTop (𝓝 0) := by
  simpa only [selectedTranslatedParameter, selectedIndex] using
    tendsto_restrictedSourceTranslateToZero_box_zero w₀
      (fun n ↦ x (data.subsequence
        (boundary.preprocessed.balancingSubsequence n)))
      boundary.selected_parameter_tendsto

/-- Every selected cluster minimum diverges along the balancing subsequence. -/
theorem selectedClusterMinTime_tendsto_atTop
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    Tendsto (fun n ↦ data.orderedClusterMinTime c
      (boundary.preprocessed.balancingSubsequence n)) atTop atTop := by
  change Tendsto (fun n ↦ A
    ((x (data.subsequence
      (boundary.preprocessed.balancingSubsequence n))).1.1
        (data.orderedClusterFirst c))) atTop atTop
  exact hA.tendsto_atTop.comp
    (boundary.selected_representative_tendsto (data.orderedClusterFirst c))

/-- The within-cluster arithmetic separation data used by every individual
balancing hierarchy.  Cluster-minimum divergence is already forced by the
selected Hermite boundary and is therefore not repeated here. -/
structure IndividualSeparationData where
  separationConstant : Fin data.orderedClusterCount → ℝ
  N : Fin data.orderedClusterCount → ℝ
  separationConstant_pos : ∀ c, 0 < separationConstant c
  five_le_N : ∀ c, 5 ≤ N c
  separated : ∀ c, ∀ᶠ n in atTop,
    ∀ i k : Fin (data.orderedClusterTailSize c + 1), i ≠ k →
      separationConstant c /
          inverse A (data.orderedClusterMinTime c
            (boundary.preprocessed.balancingSubsequence n) - N c) ≤
        integerDistance
          (data.orderedClusterRawTime
              (boundary.preprocessed.balancingSubsequence n) c i -
            data.orderedClusterRawTime
              (boundary.preprocessed.balancingSubsequence n) c k)

/-- The hierarchy and pre-boundary domination attached to an unshifted fixed
individual step. -/
theorem individual_transferHierarchies
    (separation : boundary.IndividualSeparationData
      D representative offset radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    BalancedRealJetTransferHierarchy 0
        (boundary.individualPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c j)
        (data.orderedClusterBalancingPrefixScale A
          boundary.preprocessed.balancingSubsequence c
          (boundary.preprocessed.fixedSteps c) j.succ) ∧
      CrossClusterTransferScaleDomination 0
        (boundary.individualPostLogScale D representative offset radius Fsys x
          w₀ hw₀ data c j)
        (data.orderedClusterBalancingPrefixScale A
          boundary.preprocessed.balancingSubsequence c
          (boundary.preprocessed.fixedSteps c) j.succ)
        (data.orderedClusterBalancingPrefixScale A
          boundary.preprocessed.balancingSubsequence c
          (boundary.preprocessed.fixedSteps c) j.castSucc) := by
  exact hA.orderedClusterBalancingStep_transferHierarchies data
    boundary.preprocessed.balancingSubsequence c
    (boundary.preprocessed.fixedSteps c)
    (fun n ↦ boundary.preprocessed.plans n c)
    (fun n ↦ boundary.preprocessed.plans_steps n c) j
    (separation.separationConstant_pos c) (separation.five_le_N c)
    (boundary.selectedClusterMinTime_tendsto_atTop D representative offset
      radius Fsys x w₀ hw₀ data hA c)
    (separation.separated c)

/-- Every individual post-log scale itself tends to infinity. -/
theorem individualPostLogScale_tendsto_atTop
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) (i : Fin 1) :
    Tendsto (boundary.individualPostLogScale D representative offset radius
      Fsys x w₀ hw₀ data c j i) atTop atTop := by
  unfold individualPostLogScale
  rw [show data.orderedClusterIndividualPostLogScale c A
      (boundary.selectedClusterRawTime D representative offset radius Fsys x
        w₀ hw₀ data c) (boundary.preprocessed.fixedSteps c) j i =
      fun n ↦ inverse A
        (clusterShiftedTimes
          (data.orderedClusterRawTime
            (boundary.preprocessed.balancingSubsequence n) c)
          ((boundary.preprocessed.fixedSteps c).take j.castSucc)
          ((boundary.preprocessed.fixedSteps c).get j) - 1) by
    funext n
    exact data.orderedClusterIndividualPostLogScale_apply c A
      (boundary.selectedClusterRawTime D representative offset radius Fsys x
        w₀ hw₀ data c) (boundary.preprocessed.fixedSteps c) j i n]
  apply hA.inverse_tendsto_atTop.comp
  apply tendsto_atTop_mono' atTop _
    (boundary.selectedClusterMinTime_tendsto_atTop D representative offset
      radius Fsys x w₀ hw₀ data hA c)
  filter_upwards [] with n
  have hselected :=
    (boundary.preprocessed.plans n c).prefix_selected_is_oneAboveBase
      (boundary.preprocessed.plans_steps n c) j
  change data.orderedClusterMinTime c
      (boundary.preprocessed.balancingSubsequence n) + 1 ≤
    clusterShiftedTimes
      (data.orderedClusterRawTime
        (boundary.preprocessed.balancingSubsequence n) c)
      ((boundary.preprocessed.fixedSteps c).take j.castSucc)
      ((boundary.preprocessed.fixedSteps c).get j) at hselected
  linarith

/-- Dependent index of all fixed individual operations. -/
abbrev IndividualStepIndex :=
  Sigma fun c : Fin data.orderedClusterCount ↦
    Fin (boundary.preprocessed.fixedSteps c).length

/-- All individual post-log scales viewed as one finite dependent family. -/
def individualPostLogScaleFamily
    (cj : boundary.IndividualStepIndex D representative offset radius Fsys x
      w₀ hw₀ data) (n : ℕ) : ℝ :=
  boundary.individualPostLogScale D representative offset radius Fsys x w₀
    hw₀ data cj.1 cj.2 0 n

/-- Every member of the dependent post-log scale family diverges. -/
theorem individualPostLogScaleFamily_tendsto_atTop
    (hA : IsAbel A)
    (cj : boundary.IndividualStepIndex D representative offset radius Fsys x
      w₀ hw₀ data) :
    Tendsto (boundary.individualPostLogScaleFamily D representative offset
      radius Fsys x w₀ hw₀ data cj) atTop atTop := by
  exact boundary.individualPostLogScale_tendsto_atTop D representative offset
    radius Fsys x w₀ hw₀ data hA cj.1 cj.2 0

/-- A common tail exists for the Hermite threshold at every cluster and
every fixed individual step. -/
theorem exists_individualQuantitativeTail (hA : IsAbel A) :
    ∃ N : ℕ, ∀ n
      (cj : boundary.IndividualStepIndex D representative offset radius Fsys x
        w₀ hw₀ data),
      (boundary.commonRealHermiteData D representative offset radius Fsys x
          w₀ hw₀ data hA).u0 <
        boundary.individualPostLogScaleFamily D representative offset radius
          Fsys x w₀ hw₀ data cj (n + N) := by
  exact exists_uniform_nat_tail_gt
    (boundary.individualPostLogScaleFamily D representative offset radius Fsys
      x w₀ hw₀ data)
    (boundary.individualPostLogScaleFamily_tendsto_atTop D representative
      offset radius Fsys x w₀ hw₀ data hA)
    (boundary.commonRealHermiteData D representative offset radius Fsys x w₀
      hw₀ data hA).u0

/-- One chosen tail works for the whole dependent individual-step family. -/
def individualQuantitativeTail (hA : IsAbel A) : ℕ :=
  Classical.choose (boundary.exists_individualQuantitativeTail D representative
    offset radius Fsys x w₀ hw₀ data hA)

/-- Specification of the chosen common individual tail. -/
theorem individualQuantitativeTail_spec
    (hA : IsAbel A) (n : ℕ)
    (cj : boundary.IndividualStepIndex D representative offset radius Fsys x
      w₀ hw₀ data) :
    (boundary.commonRealHermiteData D representative offset radius Fsys x w₀
        hw₀ data hA).u0 <
      boundary.individualPostLogScaleFamily D representative offset radius Fsys
        x w₀ hw₀ data cj
        (n + boundary.individualQuantitativeTail D representative offset radius
          Fsys x w₀ hw₀ data hA) :=
  Classical.choose_spec (boundary.exists_individualQuantitativeTail D
    representative offset radius Fsys x w₀ hw₀ data hA) n cj

/-- The fixed balancing subsequence after dropping the common Hermite tail. -/
def individualQuantitativeSubsequence (hA : IsAbel A) (n : ℕ) : ℕ :=
  boundary.preprocessed.balancingSubsequence
    (n + boundary.individualQuantitativeTail D representative offset radius
      Fsys x w₀ hw₀ data hA)

/-- Every shifted individual scale exceeds the common Hermite threshold. -/
theorem individualQuantitativePostLogScale_gt
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (n : ℕ) (i : Fin 1) :
    (boundary.commonRealHermiteData D representative offset radius Fsys x w₀
        hw₀ data hA).u0 <
      boundary.individualPostLogScale D representative offset radius Fsys x
        w₀ hw₀ data c j i
        (n + boundary.individualQuantitativeTail D representative offset
          radius Fsys x w₀ hw₀ data hA) := by
  have h := boundary.individualQuantitativeTail_spec D representative offset
    radius Fsys x w₀ hw₀ data hA n ⟨c, j⟩
  simpa only [individualPostLogScaleFamily, Subsingleton.elim i 0] using h

/-- The singleton derivative count selected from the paper prefix is the
positive Hermite derivative count. -/
theorem individualQuantitativeStepDerivativeCount_eq
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    data.orderedClusterQuantitativeStepDerivativeCount
        (paperRankHermiteHigherCount boundary.S) c
        (boundary.preprocessed.fixedSteps c) j =
      fun _ : Fin 1 ↦ paperRankHermitePositiveDerivativeCount boundary.S := by
  funext i
  simp [RepresentativeClusterSubsequence.orderedClusterQuantitativeStepDerivativeCount,
    selectedBlockDerivativeCount,
    RepresentativeClusterSubsequence.orderedClusterPrefixConstantDerivativeCount,
    paperRankHermiteHigherCount_add_one]

@[simp]
theorem individualQuantitativeStepDerivativeCount_apply
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) (i : Fin 1) :
    data.orderedClusterQuantitativeStepDerivativeCount
        (paperRankHermiteHigherCount boundary.S) c
        (boundary.preprocessed.fixedSteps c) j i =
      paperRankHermitePositiveDerivativeCount boundary.S := by
  exact congrFun (boundary.individualQuantitativeStepDerivativeCount_eq D
    representative offset radius Fsys x w₀ hw₀ data c j) i

/-- Canonical real-Hermite jets after the common quantitative tail. -/
def individualQuantitativeRealJetSequence
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    ∀ n i, RealCentralJetSubstitutionData A
      (boundary.individualPostLogScale D representative offset radius Fsys x
        w₀ hw₀ data c j i
        (n + boundary.individualQuantitativeTail D representative offset
          radius Fsys x w₀ hw₀ data hA))
      (paperRankHermitePositiveDerivativeCount boundary.S) :=
  (boundary.commonRealHermiteData D representative offset radius Fsys x w₀
    hw₀ data hA).fullHermite.paperRankRealJetSequence
      (D.translateToZero w₀) representative
      (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B_pos
      (boundary.individualSelectedBlock D representative offset radius Fsys x
        w₀ hw₀ data c j)
      (fun i n ↦ boundary.individualPostLogScale D representative offset radius
        Fsys x w₀ hw₀ data c j i
          (n + boundary.individualQuantitativeTail D representative offset
            radius Fsys x w₀ hw₀ data hA))
      (fun n i ↦ boundary.individualQuantitativePostLogScale_gt D
        representative offset radius Fsys x w₀ hw₀ data hA c j n i)
      (fun n ↦ (boundary.selectedTranslatedParameter D representative offset
        radius Fsys x w₀ hw₀ data
          (n + boundary.individualQuantitativeTail D representative offset
            radius Fsys x w₀ hw₀ data hA)).2)
      (fun n k ↦ boundary.selectedTranslatedOffset_bound D representative
        offset radius Fsys x w₀ hw₀ data
          (n + boundary.individualQuantitativeTail D representative offset
            radius Fsys x w₀ hw₀ data hA) k)

/-- Every shifted source jet is exactly the corresponding paper Hermite
coefficient at the actual pre-log parameter. -/
theorem individualQuantitativeRealJetSequence_sourceJet_eq_coefficientValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (n : ℕ) (i : Fin 1)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    (boundary.individualQuantitativeRealJetSequence D representative offset
      radius Fsys x w₀ hw₀ data hA c j n i).sourceJet r =
      paperRankHermiteCoefficientValue (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        boundary.B (fun _ ↦ boundary.Fbranch)
        (boundary.individualPreLogParameter D representative offset radius Fsys
          x w₀ hw₀ data c j
          (n + boundary.individualQuantitativeTail D representative offset
            radius Fsys x w₀ hw₀ data hA))
        (Sum.inr (boundary.individualSelectedBlock D representative offset
          radius Fsys x w₀ hw₀ data c j i))
        (paperRankHermitePositiveCoefficientIndex boundary.S
          (Sum.inr (boundary.individualSelectedBlock D representative offset
            radius Fsys x w₀ hw₀ data c j i)) r) := by
  unfold individualQuantitativeRealJetSequence
  apply FullHermiteLemmaSpec.paperRankRealJetSequence_sourceJet_eq_coefficientValue
  · intro q k
    exact boundary.individualPreLogParameter_selected_center D representative
      offset radius Fsys x w₀ hw₀ data hA c j k
        (q + boundary.individualQuantitativeTail D representative offset radius
          Fsys x w₀ hw₀ data hA)
  · intro q
    exact boundary.individualPreLogParameter_box D representative offset radius
      Fsys x w₀ hw₀ data c j
        (q + boundary.individualQuantitativeTail D representative offset radius
          Fsys x w₀ hw₀ data hA)

/-- The shifted balancing plans are the plans used by the final quantitative
input package. -/
def individualQuantitativePlans
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (n : ℕ) :
    ClusterBalancingPlan
      (data.orderedClusterRawTime
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA n) c)
      (data.orderedClusterMinTime c
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA n)) :=
  boundary.preprocessed.plans
    (n + boundary.individualQuantitativeTail D representative offset radius
      Fsys x w₀ hw₀ data hA) c

/-- The individual hierarchy and domination after the common tail, stated at
the exact scales used by `IndividualQuantitativeInputs`. -/
theorem individualQuantitative_transferHierarchies
    (separation : boundary.IndividualSeparationData
      D representative offset radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    BalancedRealJetTransferHierarchy 0
        (fun i n ↦ boundary.individualPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c j i
          (n + boundary.individualQuantitativeTail D representative offset
            radius Fsys x w₀ hw₀ data hA))
        (data.orderedClusterBalancingPrefixScale A
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA) c
          (boundary.preprocessed.fixedSteps c) j.succ) ∧
      CrossClusterTransferScaleDomination 0
        (fun i n ↦ boundary.individualPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c j i
          (n + boundary.individualQuantitativeTail D representative offset
            radius Fsys x w₀ hw₀ data hA))
        (data.orderedClusterBalancingPrefixScale A
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA) c
          (boundary.preprocessed.fixedSteps c) j.succ)
        (data.orderedClusterBalancingPrefixScale A
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA) c
          (boundary.preprocessed.fixedSteps c) j.castSucc) := by
  let Ntail := boundary.individualQuantitativeTail D representative offset
    radius Fsys x w₀ hw₀ data hA
  let shift : ℕ → ℕ := fun n ↦ n + Ntail
  have hshift : Tendsto shift atTop atTop := by
    simpa only [shift, Nat.add_comm] using tendsto_add_atTop_nat Ntail
  apply hA.orderedClusterBalancingStep_transferHierarchies data
    (boundary.individualQuantitativeSubsequence D representative offset radius
      Fsys x w₀ hw₀ data hA) c (boundary.preprocessed.fixedSteps c)
    (boundary.individualQuantitativePlans D representative offset radius Fsys x
      w₀ hw₀ data hA c)
    (fun n ↦ boundary.preprocessed.plans_steps (shift n) c) j
    (separation.separationConstant_pos c) (separation.five_le_N c)
    ((boundary.selectedClusterMinTime_tendsto_atTop D representative offset
      radius Fsys x w₀ hw₀ data hA c).comp hshift)
  exact hshift.eventually (separation.separated c)

/-- Every concrete shifted Hermite error has the precise decay required by
the individual quantitative trace. -/
theorem individualQuantitativeRealJetSequence_error_superpolynomialDecay
    (separation : boundary.IndividualSeparationData
      D representative offset radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) (i : Fin 1)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    Asymptotics.SuperpolynomialDecay atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (fun n ↦ (boundary.individualQuantitativeRealJetSequence D representative
        offset radius Fsys x w₀ hw₀ data hA c j n i).error r) := by
  let hierarchy := (boundary.individualQuantitative_transferHierarchies D
    representative offset radius Fsys x w₀ hw₀ data separation hA c j).1
  unfold individualQuantitativeRealJetSequence
  apply FullHermiteLemmaSpec.paperRankRealJetSequence_error_superpolynomialDecay
  · exact hierarchy.scale_ge_two
  · intro k
    exact tendsto_scaleCoordinate_div_log_atTop_of_strictAnti
      _ _ hierarchy.order hierarchy.scale_ge_two
        hierarchy.smallest_div_log_scale k

/-! ## Coefficient evaluation: concrete basepoint hom and finite adapter -/

/-- The canonical honest coefficient-ring hom evaluates every analytic germ
at its basepoint and regards the result as a constant real sequence. -/
def analyticGermBasepointSequenceHom :
    RealAnalyticGerm p →+* (ℕ → ℝ) :=
  (Pi.constRingHom ℕ ℝ).comp
    (analyticGermValueAlgHom (0 : RestrictedBoxSpace p)).toRingHom

@[simp]
theorem analyticGermBasepointSequenceHom_apply
    (g : RealAnalyticGerm p) (n : ℕ) :
    analyticGermBasepointSequenceHom (p := p) g n =
      analyticGermValue (0 : RestrictedBoxSpace p) g :=
  rfl

/-- Basepoint coefficient evaluation is polynomially bounded at every scale. -/
theorem analyticGermBasepointSequenceHom_hasPolynomialUpperBound
    (scale : ℕ → ℝ) (g : RealAnalyticGerm p) :
    HasPolynomialUpperBound atTop scale
      (analyticGermBasepointSequenceHom (p := p) g) := by
  apply (HasPolynomialUpperBound.const atTop scale
    (analyticGermValue (0 : RestrictedBoxSpace p) g)).congr
  intro n
  rfl

/-- Finite analytic representatives provide the moving coefficient values
needed by coefficientwise transfer without pretending that pointwise
evaluation of every germ is a global ring homomorphism. -/
structure FiniteMovingCoefficientData
    {κ σ : Type*} [Finite κ]
    (polynomial : κ → MvPolynomial σ (RealAnalyticGerm p)) where
  representative : κ → RestrictedBoxSpace p → MvPolynomial σ ℝ
  neighborhood : _root_.Set (RestrictedBoxSpace p)
  neighborhood_open : IsOpen neighborhood
  origin_mem : (0 : RestrictedBoxSpace p) ∈ neighborhood
  support_subset : ∀ i w,
    (representative i w).support ⊆ (polynomial i).support
  coefficient_analytic : ∀ i e,
    AnalyticOnNhd ℝ (fun w ↦ (representative i w).coeff e) neighborhood
  germ_eq : ∀ i,
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (polynomial i) =
      (representative i : Germ (𝓝 (0 : RestrictedBoxSpace p))
        (MvPolynomial σ ℝ))

/-- Every finite polynomial family over real analytic germs has a moving
coefficient adapter on one common neighborhood. -/
theorem nonempty_finiteMovingCoefficientData
    {κ σ : Type*} [Finite κ]
    (polynomial : κ → MvPolynomial σ (RealAnalyticGerm p)) :
    Nonempty (FiniteMovingCoefficientData polynomial) := by
  obtain ⟨representative, neighborhood, hopen, horigin, hsupport,
      hanalytic, hgerm⟩ := exists_analyticPolynomialRepresentatives
        (0 : RestrictedBoxSpace p) polynomial
  exact ⟨{
    representative := representative
    neighborhood := neighborhood
    neighborhood_open := hopen
    origin_mem := horigin
    support_subset := hsupport
    coefficient_analytic := hanalytic
    germ_eq := hgerm
  }⟩

/-- Moving values of one supported coefficient along the common Hermite
tail. -/
def FiniteMovingCoefficientData.coefficientValue
    {κ σ : Type*} [Finite κ]
    {polynomial : κ → MvPolynomial σ (RealAnalyticGerm p)}
    (coefficients : FiniteMovingCoefficientData polynomial)
    (hA : IsAbel A) (i : κ) (e : σ →₀ ℕ) (n : ℕ) : ℝ :=
  (coefficients.representative i
    (boundary.selectedTranslatedParameter D representative offset radius Fsys
      x w₀ hw₀ data
      (n + boundary.individualQuantitativeTail D representative offset radius
        Fsys x w₀ hw₀ data hA)).2).coeff e

/-- Every coefficient in the actual finite supports has a polynomial upper
bound along the moving parameter sequence. -/
theorem FiniteMovingCoefficientData.coefficientValue_hasPolynomialUpperBound
    {κ σ : Type*} [Finite κ]
    {polynomial : κ → MvPolynomial σ (RealAnalyticGerm p)}
    (coefficients : FiniteMovingCoefficientData polynomial)
    (hA : IsAbel A) (scale : ℕ → ℝ) (i : κ) (e : σ →₀ ℕ)
    (_he : e ∈ (polynomial i).support) :
    HasPolynomialUpperBound atTop scale
      (coefficients.coefficientValue D representative offset radius Fsys x w₀
        hw₀ data boundary hA i e) := by
  let Ntail := boundary.individualQuantitativeTail D representative offset
    radius Fsys x w₀ hw₀ data hA
  let shift : ℕ → ℕ := fun n ↦ n + Ntail
  have hshift : Tendsto shift atTop atTop := by
    simpa only [shift, Nat.add_comm] using tendsto_add_atTop_nat Ntail
  have hbox : Tendsto (fun n ↦
      (boundary.selectedTranslatedParameter D representative offset radius
        Fsys x w₀ hw₀ data (shift n)).2) atTop (𝓝 0) :=
    (boundary.selectedTranslatedParameter_box_tendsto_zero D representative
      offset radius Fsys x w₀ hw₀ data).comp hshift
  apply (HasPolynomialUpperBound.of_analyticOnNhd_comp coefficients.origin_mem
    (coefficients.coefficient_analytic i e) hbox).congr
  intro n
  rfl

/-! ## Trace-typed jets and coherent individual boundaries -/

noncomputable local instance individualQuantitativeBlockDecidableEq
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- Transport a real central jet across equal scale and derivative-count
indices while retaining explicit access to its source and error fields. -/
def castRealCentralJetSubstitutionData
    {A : ℝ → ℝ} {u u' : ℝ} {d d' : ℕ}
    (J : RealCentralJetSubstitutionData A u d)
    (hu : u = u') (hd : d = d') :
    RealCentralJetSubstitutionData A u' d' := by
  subst u'
  subst d'
  exact J

@[simp]
theorem castRealCentralJetSubstitutionData_error
    {A : ℝ → ℝ} {u u' : ℝ} {d d' : ℕ}
    (J : RealCentralJetSubstitutionData A u d)
    (hu : u = u') (hd : d = d') (r : Fin d') :
    (castRealCentralJetSubstitutionData J hu hd).error r =
      J.error (Fin.cast hd.symm r) := by
  subst u'
  subst d'
  rfl

/-- The trace expression for the shifted post-log scale is definitionally
the tail of the concrete Hermite scale. -/
@[simp]
theorem individualQuantitativePostLogScale_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (i : Fin 1) (n : ℕ) :
    data.orderedClusterIndividualPostLogScale c A
        (fun q ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA q) c)
        (boundary.preprocessed.fixedSteps c) j i n =
      boundary.individualPostLogScale D representative offset radius Fsys x w₀
        hw₀ data c j i
        (n + boundary.individualQuantitativeTail D representative offset radius
          Fsys x w₀ hw₀ data hA) := by
  rfl

/-- The shifted Hermite jets with the derivative-count expression expected
literally by the ordered-cluster quantitative trace. -/
def individualQuantitativeTraceJets
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    ∀ n i, RealCentralJetSubstitutionData A
      (data.orderedClusterIndividualPostLogScale c A
        (fun q ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA q) c)
        (boundary.preprocessed.fixedSteps c) j i n)
      (data.orderedClusterQuantitativeStepDerivativeCount
        (paperRankHermiteHigherCount boundary.S) c
        (boundary.preprocessed.fixedSteps c) j i) :=
  fun n i ↦ castRealCentralJetSubstitutionData
    (boundary.individualQuantitativeRealJetSequence D representative
      offset radius Fsys x w₀ hw₀ data hA c j n i)
      (boundary.individualQuantitativePostLogScale_eq D representative offset
        radius Fsys x w₀ hw₀ data hA c j i n).symm
      (boundary.individualQuantitativeStepDerivativeCount_apply D
        representative offset radius Fsys x w₀ hw₀ data c j i).symm

/-- The exact boundary chain still needed to concatenate individual
operations.  The active-source equation ties every step to the concrete
Hermite jets above; the successor equation is the genuinely additional
adjacent-step coherence.  Polynomial bounds are required only for the shared
flat boundary coordinates. -/
structure IndividualBoundaryChain (hA : IsAbel A) where
  value : (c : Fin data.orderedClusterCount) →
    Fin ((data.orderedClusterPrefixIndividualSteps c
      (boundary.preprocessed.fixedSteps c)).length + 1) →
    ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)) → ℕ → ℝ
  pre_active : ∀ c
      (j : Fin (boundary.preprocessed.fixedSteps c).length),
    selectedBlockActiveAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c
          (boundary.preprocessed.fixedSteps c) j)
        (value c
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j).castSucc) =
      individualCentralPreLogActiveAssignment
        (data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA q) c)
          (boundary.preprocessed.fixedSteps c) j)
        (data.orderedClusterQuantitativeStepDerivativeCount
          (paperRankHermiteHigherCount boundary.S) c
          (boundary.preprocessed.fixedSteps c) j)
        (boundary.individualQuantitativeTraceJets D representative offset radius
          Fsys x w₀ hw₀ data hA c j)
  post_eq : ∀ c
      (j : Fin (boundary.preprocessed.fixedSteps c).length),
    value c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ =
      data.orderedClusterIndividualPostLogFlatAssignment
        (paperRankHermiteHigherCount boundary.S) c A
        (fun q ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA q) c)
        (boundary.preprocessed.fixedSteps c) j
        (value c
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j).castSucc)
  coordinate_bound : ∀ c q z,
    HasPolynomialUpperBound atTop
      (data.orderedClusterIndividualBoundaryScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) q)
      (value c q z)
  incoming_coordinate_bound : ∀ c
      (j : Fin (boundary.preprocessed.fixedSteps c).length) z,
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (value c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc z)

/-- The boundary datum consumed by one cluster's displayed individual trace,
constructed from the narrow coherent chain. -/
def IndividualBoundaryChain.boundaryData
    (hA : IsAbel A)
    (chain : boundary.IndividualBoundaryChain D representative offset radius
      Fsys x w₀ hw₀ data hA)
    (c : Fin data.orderedClusterCount) :
    data.OrderedClusterIndividualQuantitativeBoundaryData
      (paperRankHermiteHigherCount boundary.S) c A
      (boundary.individualQuantitativeSubsequence D representative offset radius
        Fsys x w₀ hw₀ data hA) (boundary.preprocessed.fixedSteps c) where
  value := chain.value c
  baseValue := fun j ↦ chain.value c
    (data.orderedClusterIndividualStepIndexEquiv c
      (boundary.preprocessed.fixedSteps c) j).castSucc
  jets := fun j ↦ boundary.individualQuantitativeTraceJets D representative
    offset radius Fsys x w₀ hw₀ data hA c j
  pre_eq := by
    intro j
    exact (data.orderedClusterIndividualPreLogFlatAssignment_eq_base
      (paperRankHermiteHigherCount boundary.S) c
      (fun q ↦ data.orderedClusterRawTime
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA q) c)
      (boundary.preprocessed.fixedSteps c) j
      (chain.value c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc)
      (boundary.individualQuantitativeTraceJets D representative offset radius
        Fsys x w₀ hw₀ data hA c j)
      (chain.pre_active c j)).symm
  post_eq := fun j ↦ chain.post_eq c j

/-- The base assignment at each individual operation is just its incoming
shared boundary, so its coordinate bounds require no additional hypothesis. -/
theorem IndividualBoundaryChain.baseValue_hasPolynomialUpperBound
    (hA : IsAbel A)
    (chain : boundary.IndividualBoundaryChain D representative offset radius
      Fsys x w₀ hw₀ data hA)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (z : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      ((chain.boundaryData D representative offset radius Fsys x w₀ hw₀ data
        boundary hA c).baseValue j z) := by
  simpa only [IndividualBoundaryChain.boundaryData] using
    chain.incoming_coordinate_bound c j z

/-- Restricting a polynomially bounded flat boundary to any selected active
block preserves the bound literally. -/
theorem IndividualBoundaryChain.activeValue_hasPolynomialUpperBound
    (hA : IsAbel A)
    (chain : boundary.IndividualBoundaryChain D representative offset radius
      Fsys x w₀ hw₀ data hA)
    (c : Fin data.orderedClusterCount)
    (q : Fin ((data.orderedClusterPrefixIndividualSteps c
      (boundary.preprocessed.fixedSteps c)).length + 1))
    (selected : data.OrderedClusterPrefixBlock (c.val + 1))
    (z : ClusterOperationSymbol (Fin 1)
      (selectedBlockDerivativeCount
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        selected)) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterIndividualBoundaryScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) q)
      (selectedBlockActiveAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        selected (chain.value c q) z) := by
  unfold selectedBlockActiveAssignment
  exact chain.coordinate_bound c q _

/-- The exact post-boundary identity turns the flat-boundary coordinate
bounds into bounds for every central derivative and time coordinate. -/
theorem IndividualBoundaryChain.centralValue_hasPolynomialUpperBound
    (hA : IsAbel A)
    (chain : boundary.IndividualBoundaryChain D representative offset radius
      Fsys x w₀ hw₀ data hA)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (z : CentralPolynomialIndex (Fin 1)
      (data.orderedClusterQuantitativeStepDerivativeCount
        (paperRankHermiteHigherCount boundary.S) c
        (boundary.preprocessed.fixedSteps c) j) (Fin 1)) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (fun n ↦ realCentralTransferCentralValue A
        (fun i ↦ data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative
              offset radius Fsys x w₀ hw₀ data hA q) c)
          (boundary.preprocessed.fixedSteps c) j i n)
        (data.orderedClusterQuantitativeStepDerivativeCount
          (paperRankHermiteHigherCount boundary.S) c
          (boundary.preprocessed.fixedSteps c) j) z) := by
  let step := data.orderedClusterIndividualStepIndexEquiv c
    (boundary.preprocessed.fixedSteps c) j
  let d := data.orderedClusterPrefixConstantDerivativeCount
    (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  have hactive := chain.activeValue_hasPolynomialUpperBound D representative
    offset radius Fsys x w₀ hw₀ data boundary hA c step.succ selected
      (Sum.inr z)
  have hpost : selectedBlockActiveAssignment d selected
      (chain.value c step.succ) =
        individualCentralPostLogActiveAssignment A
          (data.orderedClusterIndividualPostLogScale c A
            (fun q ↦ data.orderedClusterRawTime
              (boundary.individualQuantitativeSubsequence D representative
                offset radius Fsys x w₀ hw₀ data hA q) c)
            (boundary.preprocessed.fixedSteps c) j)
          (data.orderedClusterQuantitativeStepDerivativeCount
            (paperRankHermiteHigherCount boundary.S) c
            (boundary.preprocessed.fixedSteps c) j) := by
    dsimp only [d, selected, step]
    rw [chain.post_eq c j]
    exact data.selectedBlockActiveAssignment_orderedClusterIndividualPostLog
      (paperRankHermiteHigherCount boundary.S) c A
      (fun q ↦ data.orderedClusterRawTime
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA q) c)
      (boundary.preprocessed.fixedSteps c) j
      (chain.value c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc)
  apply hactive.congr
  intro n
  simpa only [individualCentralPostLogActiveAssignment_central] using
    (congrFun (congrFun hpost (Sum.inr z)) n).symm

/-- A finite Stirling change of coordinates and the time translation by one
preserve polynomial upper bounds for the error-free main assignment. -/
theorem realJetMainAssignment_hasPolynomialUpperBound_of_central
    {m : ℕ} (A : ℝ → ℝ) (u : Fin (m + 1) → ℕ → ℝ)
    (d : Fin (m + 1) → ℕ)
    (scale : ℕ → ℝ) (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hcentral : ∀ z : CentralPolynomialIndex (Fin (m + 1)) d (Fin (m + 1)),
      HasPolynomialUpperBound atTop scale
        (fun n ↦ realCentralTransferCentralValue A (fun i ↦ u i n) d z))
    (z : RealJetTransferIndex m d) :
    HasPolynomialUpperBound atTop scale
      (realJetMainAssignment A u d z) := by
  rcases z with i | z
  · apply (HasPolynomialUpperBound.one atTop scale).congr
    intro n
    rfl
  · rcases z with z | i
    · rcases z with ⟨i, r⟩
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
      simp only [realJetMainAssignment, realCentralTransferMainValue,
        realCentralStirlingJet_eq_fin_sum]
    · apply ((hcentral (Sum.inr i)).add hscale
        (HasPolynomialUpperBound.one atTop scale)).congr
      intro n
      rfl

/-- The concrete main assignment is bounded by the post-boundary scale. -/
theorem IndividualBoundaryChain.mainValue_hasPolynomialUpperBound
    (hA : IsAbel A)
    (chain : boundary.IndividualBoundaryChain D representative offset radius
      Fsys x w₀ hw₀ data hA)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (z : RealJetTransferIndex 0
      (data.orderedClusterQuantitativeStepDerivativeCount
        (paperRankHermiteHigherCount boundary.S) c
        (boundary.preprocessed.fixedSteps c) j)) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (realJetMainAssignment A
        (data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative
              offset radius Fsys x w₀ hw₀ data hA q) c)
          (boundary.preprocessed.fixedSteps c) j)
        (data.orderedClusterQuantitativeStepDerivativeCount
          (paperRankHermiteHigherCount boundary.S) c
          (boundary.preprocessed.fixedSteps c) j) z) := by
  apply realJetMainAssignment_hasPolynomialUpperBound_of_central
  · exact Filter.Eventually.of_forall fun n ↦ one_le_two.trans
      (two_le_clusterBalancingPrefixScale A
        (fun q ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA q) c)
        (boundary.preprocessed.fixedSteps c) j.succ n)
  · exact chain.centralValue_hasPolynomialUpperBound D representative offset
      radius Fsys x w₀ hw₀ data boundary hA c j

/-- Exact pre-boundary compatibility bounds every literal source coordinate.
The representative coordinate uses `exp u = E u + 1`; all derivative and
time coordinates are already literal coordinates of the active pre-boundary. -/
theorem IndividualBoundaryChain.sourceValue_hasPolynomialUpperBound
    (hA : IsAbel A)
    (chain : boundary.IndividualBoundaryChain D representative offset radius
      Fsys x w₀ hw₀ data hA)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (z : RealJetTransferIndex 0
      (data.orderedClusterQuantitativeStepDerivativeCount
        (paperRankHermiteHigherCount boundary.S) c
        (boundary.preprocessed.fixedSteps c) j)) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.castSucc)
      (realJetActualAssignment
        (data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative
              offset radius Fsys x w₀ hw₀ data hA q) c)
          (boundary.preprocessed.fixedSteps c) j)
        (data.orderedClusterQuantitativeStepDerivativeCount
          (paperRankHermiteHigherCount boundary.S) c
          (boundary.preprocessed.fixedSteps c) j)
        (boundary.individualQuantitativeTraceJets D representative offset
          radius Fsys x w₀ hw₀ data hA c j) z) := by
  let step := data.orderedClusterIndividualStepIndexEquiv c
    (boundary.preprocessed.fixedSteps c) j
  let d := data.orderedClusterPrefixConstantDerivativeCount
    (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  let u := data.orderedClusterIndividualPostLogScale c A
    (fun q ↦ data.orderedClusterRawTime
      (boundary.individualQuantitativeSubsequence D representative offset
        radius Fsys x w₀ hw₀ data hA q) c)
    (boundary.preprocessed.fixedSteps c) j
  let d₁ := data.orderedClusterQuantitativeStepDerivativeCount
    (paperRankHermiteHigherCount boundary.S) c
    (boundary.preprocessed.fixedSteps c) j
  let jets := boundary.individualQuantitativeTraceJets D representative offset
    radius Fsys x w₀ hw₀ data hA c j
  have hpre : selectedBlockActiveAssignment d selected
      (chain.value c step.castSucc) =
        individualCentralPreLogActiveAssignment u d₁ jets := by
    exact chain.pre_active c j
  have hscale : ∀ᶠ n in atTop,
      1 ≤ data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.castSucc n :=
    Filter.Eventually.of_forall fun n ↦ one_le_two.trans
      (two_le_clusterBalancingPrefixScale A
        (fun q ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA q) c)
        (boundary.preprocessed.fixedSteps c) j.castSucc n)
  rcases z with i | z
  · have hin := chain.activeValue_hasPolynomialUpperBound D representative
      offset radius Fsys x w₀ hw₀ data boundary hA c step.castSucc selected
        (Sum.inl i)
    have hin' : HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA) c
          (boundary.preprocessed.fixedSteps c) j.castSucc)
        (selectedBlockActiveAssignment d selected
          (chain.value c step.castSucc) (Sum.inl i)) := by
      simpa only [step,
        RepresentativeClusterSubsequence.orderedClusterIndividualBoundaryScale,
        Fin.val_castSucc,
        RepresentativeClusterSubsequence.orderedClusterIndividualStepIndexEquiv_apply_val]
        using hin
    apply (hin'.add hscale
      (HasPolynomialUpperBound.one atTop _)).congr
    intro n
    have hi := congrFun (congrFun hpre (Sum.inl i)) n
    change Real.exp (u i n) =
      selectedBlockActiveAssignment d selected
        (chain.value c step.castSucc) (Sum.inl i) n + 1
    rw [hi]
    simp only [individualCentralPreLogActiveAssignment_q, E]
    ring
  · have hin := chain.activeValue_hasPolynomialUpperBound D representative
      offset radius Fsys x w₀ hw₀ data boundary hA c step.castSucc selected
        (Sum.inr z)
    have hin' : HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA) c
          (boundary.preprocessed.fixedSteps c) j.castSucc)
        (selectedBlockActiveAssignment d selected
          (chain.value c step.castSucc) (Sum.inr z)) := by
      simpa only [step,
        RepresentativeClusterSubsequence.orderedClusterIndividualBoundaryScale,
        Fin.val_castSucc,
        RepresentativeClusterSubsequence.orderedClusterIndividualStepIndexEquiv_apply_val]
        using hin
    apply hin'.congr
    intro n
    simpa only [realJetActualAssignment,
      individualCentralPreLogActiveAssignment_central] using
      (congrFun (congrFun hpre (Sum.inr z)) n).symm

/-- The jets stored in the coherent boundary are the concrete shifted
Hermite jets, so their error estimate is exactly the hierarchy estimate
proved above. -/
theorem IndividualBoundaryChain.jetError_superpolynomialDecay
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A)
    (chain : boundary.IndividualBoundaryChain D representative offset radius
      Fsys x w₀ hw₀ data hA)
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (i : Fin 1)
    (r : Fin (data.orderedClusterQuantitativeStepDerivativeCount
      (paperRankHermiteHigherCount boundary.S) c
      (boundary.preprocessed.fixedSteps c) j i)) :
    Asymptotics.SuperpolynomialDecay atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (fun n ↦ ((chain.boundaryData D representative offset radius Fsys x w₀
        hw₀ data boundary hA c).jets j n i).error r) := by
  let hd := boundary.individualQuantitativeStepDerivativeCount_apply D
    representative offset radius Fsys x w₀ hw₀ data c j i
  let r' : Fin (paperRankHermitePositiveDerivativeCount boundary.S) :=
    Fin.cast hd r
  have herr :=
    boundary.individualQuantitativeRealJetSequence_error_superpolynomialDecay
      D representative offset radius Fsys x w₀ hw₀ data separation hA c j i r'
  apply herr.congr
  intro n
  simp only [IndividualBoundaryChain.boundaryData,
    individualQuantitativeTraceJets,
    castRealCentralJetSubstitutionData_error]
  congr

/-- The complete generic individual-trace input supplied by the concrete
Hermite jets and a coherent boundary chain.  The coefficient homomorphism is
the honest basepoint evaluation; moving evaluations of the finitely many
paper coefficients are carried separately by `FiniteMovingCoefficientData`. -/
noncomputable def IndividualBoundaryChain.basepointQuantitativeInputs
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A)
    (chain : boundary.IndividualBoundaryChain D representative offset radius
      Fsys x w₀ hw₀ data hA) :
    RepresentativeClusterSubsequence.OrderedClusterPreprocessedAlgebraicDescent.IndividualQuantitativeInputs
      (RealAnalyticGerm p) data
      (paperRankHermiteHigherCount boundary.S)
      boundary.preprocessed.fixedSteps A
      (boundary.individualQuantitativeSubsequence D representative offset
        radius Fsys x w₀ hw₀ data hA)
      (analyticGermBasepointSequenceHom (p := p)) where
  boundary := fun c ↦ chain.boundaryData D representative offset radius Fsys x
    w₀ hw₀ data boundary hA c
  plans := boundary.individualQuantitativePlans D representative offset radius
    Fsys x w₀ hw₀ data hA
  fixed_steps := by
    intro c n
    exact boundary.preprocessed.plans_steps
      (n + boundary.individualQuantitativeTail D representative offset radius
        Fsys x w₀ hw₀ data hA) c
  separationConstant := separation.separationConstant
  N := separation.N
  separationConstant_pos := separation.separationConstant_pos
  five_le_N := separation.five_le_N
  base_tendsto := by
    intro c
    let Ntail := boundary.individualQuantitativeTail D representative offset
      radius Fsys x w₀ hw₀ data hA
    let shift : ℕ → ℕ := fun n ↦ n + Ntail
    have hshift : Tendsto shift atTop atTop := by
      simpa only [shift, Nat.add_comm] using tendsto_add_atTop_nat Ntail
    exact (boundary.selectedClusterMinTime_tendsto_atTop D representative
      offset radius Fsys x w₀ hw₀ data hA c).comp hshift
  separated := by
    intro c
    let Ntail := boundary.individualQuantitativeTail D representative offset
      radius Fsys x w₀ hw₀ data hA
    let shift : ℕ → ℕ := fun n ↦ n + Ntail
    have hshift : Tendsto shift atTop atTop := by
      simpa only [shift, Nat.add_comm] using tendsto_add_atTop_nat Ntail
    exact hshift.eventually (separation.separated c)
  coefficient_bound := by
    intro c q g
    exact analyticGermBasepointSequenceHom_hasPolynomialUpperBound
      (data.orderedClusterIndividualBoundaryScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) q) g
  boundary_coordinate_bound := chain.coordinate_bound
  base_coordinate_bound := by
    intro c j z
    exact chain.baseValue_hasPolynomialUpperBound D representative offset radius
      Fsys x w₀ hw₀ data boundary hA c j z
  main_bound := by
    intro c j z
    exact chain.mainValue_hasPolynomialUpperBound D representative offset radius
      Fsys x w₀ hw₀ data boundary hA c j z
  central_coordinate_bound := by
    intro c j z
    exact chain.centralValue_hasPolynomialUpperBound D representative offset
      radius Fsys x w₀ hw₀ data boundary hA c j z
  source_coordinate_bound := by
    intro c j z
    simpa only [IndividualBoundaryChain.boundaryData] using
      chain.sourceValue_hasPolynomialUpperBound D representative offset radius
        Fsys x w₀ hw₀ data boundary hA c j z
  jet_error := by
    intro c j i r
    exact chain.jetError_superpolynomialDecay D representative offset radius
      Fsys x w₀ hw₀ data boundary separation hA c j i r

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
