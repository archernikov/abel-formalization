import AbelFormalization.HermiteRankTopPrefixSequenceBoundary
import AbelFormalization.OrderedClusterBalancingSelection
import AbelFormalization.OrderedClusterPreprocessedAlgebraicDescentTraceData
import AbelFormalization.OrderedClusterPreprocessedBottomPolynomial

/-!
# Full-Hermite sequence boundary with individual cluster preprocessing

This module upgrades the full-Hermite top-prefix boundary to the descent in
which every ordered cluster is individually balanced before its simultaneous
central reduction.  It reuses the existing Hermite/rank boundary theorem,
chooses the fixed balancing plans on one further subsequence, constructs the
preprocessed real-analytic-germ descent, chooses its flattened transfer trace,
and extracts the nonzero bottom time polynomial.

The selected operation trace is dependent: its individual and simultaneous
certificates retain the literal prefix coefficient rings supplied by
`OrderedClusterPreprocessedAlgebraicDescent.FullTransferTraceData`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

open Filter Set
open scoped Topology Polynomial

namespace AbelFormalization

variable {ι : Type*}

namespace RepresentativeClusterSubsequence

/-- The complete preprocessing, algebraic descent, flattened transfer trace,
and terminal polynomial attached to a full-Hermite top-prefix ideal. -/
structure PaperRankHermiteTopPrefixPreprocessedTraceData
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))) where
  balancingBound : ℕ
  balancingSubsequence : ℕ → ℕ
  fixedSteps : data.OrderedClusterIndividualStepPlan
  fixedOrder : data.OrderedClusterFinalOrderPlan
  plans : ∀ n (c : Fin data.orderedClusterCount),
    ClusterBalancingPlan
      (data.orderedClusterRawTime (balancingSubsequence n) c)
      (data.orderedClusterMinTime c (balancingSubsequence n))
  balancingSubsequence_strictMono : StrictMono balancingSubsequence
  selectedSubsequence_strictMono :
    StrictMono (data.subsequence ∘ balancingSubsequence)
  cluster_bounds : ∀ c n i,
    data.orderedClusterMinTime c n ≤ data.orderedClusterRawTime n c i ∧
      data.orderedClusterRawTime n c i ≤
        data.orderedClusterMinTime c n + (balancingBound : ℝ)
  fixedSteps_length_le : ∀ c, (fixedSteps c).length ≤
    (data.orderedClusterTailSize c + 1) *
      (⌊(balancingBound : ℝ)⌋₊ + 1)
  plans_steps : ∀ n c, (plans n c).steps = fixedSteps c
  plans_finalOrder : ∀ n c, (plans n c).finalOrder = fixedOrder c
  finalIdeal : Ideal (data.OrderedClusterPrefixRing
    (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0)
  descent : OrderedClusterPreprocessedAlgebraicDescent
    (RealAnalyticGerm p) data (paperRankHermiteHigherCount S)
    fixedSteps fixedOrder
    (data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I)
    0 (Nat.zero_le _) finalIdeal
  transferTrace : descent.FullTransferTraceData
  bottomIndex : Fin (data.orderedCluster
    ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
  bottomPolynomial : ℝ[X]
  bottomPolynomial_ne : bottomPolynomial ≠ 0
  bottomEmbedding_ne :
    scalarUnivariateEmbedding ℝ
      (data.OrderedClusterPrefixRing
        (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0)
      bottomIndex bottomPolynomial ≠ 0
  bottomEmbedding_mem :
    scalarUnivariateEmbedding ℝ
      (data.OrderedClusterPrefixRing
        (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0)
      bottomIndex bottomPolynomial ∈
        (descent.stageAt 0 data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.timeIdeal

/-- Choose the fixed balancing subsequence, preprocessed descent, full
flattened transfer trace, and bottom polynomial from a top-prefix rank ideal
of the required height. -/
theorem nonempty_paperRankHermiteTopPrefixPreprocessedTraceData
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (S : Finset (ι × ℕ))
    (I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p)))
    (hheight : ((p + m : ℕ) : ENat) ≤ I.height) :
    Nonempty (data.PaperRankHermiteTopPrefixPreprocessedTraceData S I) := by
  classical
  obtain ⟨balancingBound, balancingSubsequence, fixedSteps, fixedOrder,
      plans, hsubsequence, hbounds, hlength, hsteps, horder⟩ :=
    data.exists_fixed_orderedClusterBalancing_subsequence
  have hinitialHeight : ((p + m : ℕ) : ENat) ≤
      (data.paperRankHermiteTopPrefixIdeal
        (RealAnalyticGerm p) S I).height := by
    rw [data.paperRankHermiteTopPrefixIdeal_height (RealAnalyticGerm p) S I]
    exact hheight
  obtain ⟨finalIdeal, ⟨descent⟩⟩ :=
    data.exists_orderedClusterPreprocessedAlgebraicDescent_realAnalyticGerm
      (paperRankHermiteHigherCount S) fixedSteps fixedOrder
      (data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I)
  let transferTrace := Classical.choice descent.nonempty_fullTransferTraceData
  obtain ⟨bottomIndex, bottomPolynomial, hPolynomial, hEmbedding,
      hMembership⟩ :=
    data.exists_bottom_preprocessed_timePolynomial_at_stage descent
      data.orderedClusterCount_pos_of_nonempty hinitialHeight
  exact ⟨{
    balancingBound := balancingBound
    balancingSubsequence := balancingSubsequence
    fixedSteps := fixedSteps
    fixedOrder := fixedOrder
    plans := plans
    balancingSubsequence_strictMono := hsubsequence
    selectedSubsequence_strictMono :=
      data.strictMono_subsequence.comp hsubsequence
    cluster_bounds := hbounds
    fixedSteps_length_le := hlength
    plans_steps := hsteps
    plans_finalOrder := horder
    finalIdeal := finalIdeal
    descent := descent
    transferTrace := transferTrace
    bottomIndex := bottomIndex
    bottomPolynomial := bottomPolynomial
    bottomPolynomial_ne := hPolynomial
    bottomEmbedding_ne := hEmbedding
    bottomEmbedding_mem := hMembership
  }⟩

end RepresentativeClusterSubsequence

/-- The corrected Hermite/rank sequence boundary together with the fixed
individual balancing subsequence, the preprocessed descent, its full flattened
trace, and its nonzero bottom time polynomial. -/
structure RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
    {A : ℝ → ℝ} {m p a : ℕ} [Nonempty (Fin m)]
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (radius : ℝ)
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (x : ℕ → RestrictedSource m p a)
    (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i))) where
  S : Finset (ι × ℕ)
  Q : Fin (m + p + a) →
    MvPolynomial (PaperRankSymbols m a S.card)
      D.analyticNearClosedBoxSubalgebra
  B : ℝ
  Xstrip : ℝ
  K : ℝ
  K0 : ℝ
  Fbranch : ℂ → ℂ
  I : Ideal (MvPolynomial
    (PaperRankRetainedSymbols m
      (m * (paperRankHermitePositiveDerivativeCount S + 1)))
    (RealAnalyticGerm p))
  generatorCount : ℕ
  generator : Fin generatorCount → MvPolynomial
    (PaperRankRetainedSymbols m
      (m * (paperRankHermitePositiveDerivativeCount S + 1)))
    (RealAnalyticGerm p)
  representativePolynomial : Fin generatorCount →
    RestrictedBoxSpace p → MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ
  coefficientNeighborhood : Set (RestrictedBoxSpace p)
  polynomial_value_eq : ∀ r,
    restrictedPaperPolynomialValue A D representative offset
      (restrictedJetEnumeration S) (Q r) = F r
  B_pos : 0 < B
  Xstrip_gt_one : 1 < Xstrip
  branch_analytic :
    AnalyticOnNhd ℂ Fbranch (rightHalfStrip Xstrip (B + 2))
  branch_real : ∀ t : ℝ, Xstrip < t → Fbranch (t : ℂ) = (A t : ℂ)
  hermiteFamily : AbelHermiteFamilySpec A B
    (paperRankHermiteNodeMultiplicity S) (Xstrip + B + 3) K K0
      (fun _ ↦ Fbranch)
  offset_bound : ∀ w ∈ D.closedBox, ∀ j : Fin S.card,
    |(offset (restrictedJetEnumeration S j).1 :
      RestrictedBoxSpace p → ℝ) w| ≤ B
  rankIdeal_eq :
    I = jacobianEliminationIdeal a
      (fun r ↦ restrictedPaperGermPolynomial (D.translateToZero w₀)
        (D.zero_mem_closedBox_translateToZero hw₀)
        (hermiteBeforeRankPolynomialFamily (D.translateToZero w₀)
          representative (restrictedOffsetTranslateToZero w₀ offset) S
          (fun q ↦ restrictedPaperPolynomialTranslateToZero D w₀ (Q q)) r))
      (analyticGermFormalDerivations p)
  rankHeight : ((m + p : ℕ) : ENat) ≤ I.height
  generator_span : Ideal.span (Set.range generator) = I
  coefficientNeighborhood_open : IsOpen coefficientNeighborhood
  origin_mem_coefficientNeighborhood :
    (0 : RestrictedBoxSpace p) ∈ coefficientNeighborhood
  representative_support : ∀ j w,
    (representativePolynomial j w).support ⊆ (generator j).support
  representative_coeff_analytic : ∀ j d,
    AnalyticOnNhd ℝ (fun w ↦ (representativePolynomial j w).coeff d)
      coefficientNeighborhood
  generator_germ : ∀ j,
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p) (generator j) =
      (representativePolynomial j : Germ (nhds (0 : RestrictedBoxSpace p))
        (MvPolynomial
          (PaperRankRetainedSymbols m
            (m * (paperRankHermitePositiveDerivativeCount S + 1))) ℝ))
  rank_vanish : ∀ᶠ n in atTop, ∀ j,
    MvPolynomial.eval
      (paperRankRetainedArgument
        (paperRankFullHermiteSmoothValue (D.translateToZero w₀)
          representative (restrictedOffsetTranslateToZero w₀ offset) S
          B Fbranch)
        (restrictedSourceTranslateToZero w₀ (x n)))
      (representativePolynomial j
        (restrictedSourceTranslateToZero w₀ (x n)).1.2) = 0
  topPrefix_height :
    (data.paperRankHermiteTopPrefixIdeal
      (RealAnalyticGerm p) S I).height = I.height
  topPrefix_span :
    Ideal.span (Set.range (fun j ↦
      data.paperRankHermiteTopPrefixAlgEquiv
        (RealAnalyticGerm p) S (generator j))) =
      data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I
  topPrefix_germ : ∀ j,
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (data.paperRankHermiteTopPrefixAlgEquiv
          (RealAnalyticGerm p) S (generator j)) =
      (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixRepresentative
        data S (representativePolynomial j) :
          Germ (nhds (0 : RestrictedBoxSpace p))
            (data.OrderedClusterPrefixRing ℝ
              (paperRankHermiteHigherCount S) data.orderedClusterCount))
  topPrefix_evaluation : ∀ j w
      (v : PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)) → ℝ),
    MvPolynomial.eval
      (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixAssignment
        data S v)
      (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixRepresentative
        data S (representativePolynomial j) w) =
      MvPolynomial.eval v (representativePolynomial j w)
  topPrefix_vanish : ∀ᶠ n in atTop, ∀ j,
    MvPolynomial.eval
      (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixAssignment
        data S
        (paperRankRetainedArgument
          (paperRankFullHermiteSmoothValue (D.translateToZero w₀)
            representative (restrictedOffsetTranslateToZero w₀ offset) S
            B Fbranch)
          (restrictedSourceTranslateToZero w₀ (x n))))
      (RepresentativeClusterSubsequence.paperRankHermiteTopPrefixRepresentative
        data S (representativePolynomial j)
          (restrictedSourceTranslateToZero w₀ (x n)).1.2) = 0
  preprocessed :
    data.PaperRankHermiteTopPrefixPreprocessedTraceData S I
  selected_regularZero : ∀ n,
    x (data.subsequence (preprocessed.balancingSubsequence n)) ∈
      regularZeroSet (restrictedBaseOpenDomain D radius) (constraintMap F)
  selected_parameter_tendsto :
    Tendsto (fun n ↦
      (x (data.subsequence (preprocessed.balancingSubsequence n))).1.2)
      atTop (nhds w₀)
  selected_representative_tendsto : ∀ i,
    Tendsto (fun n ↦
      (x (data.subsequence (preprocessed.balancingSubsequence n))).1.1 i)
      atTop atTop
  paddedTopPrefix_span :
    Ideal.span (Set.range
      (data.paperRankHermiteTopPrefixPaddedGenerator S generator)) =
      data.paperRankHermiteTopPrefixIdeal (RealAnalyticGerm p) S I
  paddedTopPrefix_germ : ∀ j,
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (data.paperRankHermiteTopPrefixPaddedGenerator S generator j) =
      (data.paperRankHermiteTopPrefixPaddedRepresentative S
        representativePolynomial j :
          Germ (nhds (0 : RestrictedBoxSpace p))
            (data.OrderedClusterPrefixRing ℝ
              (paperRankHermiteHigherCount S) data.orderedClusterCount))
  paddedTopPrefix_selected_vanish : ∀ᶠ n in atTop, ∀ j,
    MvPolynomial.eval
      (data.paperRankHermiteTopPrefixAssignment S
        (paperRankRetainedArgument
          (paperRankFullHermiteSmoothValue (D.translateToZero w₀)
            representative (restrictedOffsetTranslateToZero w₀ offset) S
            B Fbranch)
          (restrictedSourceTranslateToZero w₀
            (x (data.subsequence
              (preprocessed.balancingSubsequence n))))))
      (data.paperRankHermiteTopPrefixPaddedRepresentative S
        representativePolynomial j
        (restrictedSourceTranslateToZero w₀
          (x (data.subsequence
            (preprocessed.balancingSubsequence n)))).1.2) = 0

/-- Upgrade the corrected full-Hermite top-prefix sequence boundary to the
fixed individually preprocessed descent and its full flattened transfer
trace.  All analytic and reindexing facts are inherited from the existing
boundary theorem; the padded boundary is obtained from its dedicated spec. -/
theorem IsAbel.exists_restrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} [Nonempty (Fin m)]
    (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (radius : ℝ)
    (F : Fin (m + p + a) → RestrictedSource m p a → ℝ)
    (hF : ∀ i, F i ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset))
    (x : ℕ → RestrictedSource m p a)
    (hx : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D radius) (constraintMap F))
    (hxrepresentative : ∀ i,
      Tendsto (fun n ↦ (x n).1.1 i) atTop atTop)
    (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
    (hxlim : Tendsto (fun n ↦ (x n).1.2) atTop (nhds w₀))
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i))) :
    Nonempty (RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
      D representative offset radius F x w₀ hw₀ data) := by
  classical
  have oldBoundary :=
    hA.exists_restrictedBaseHermiteRankTopPrefixSequenceBoundary
      D representative offset radius F hF x hx hxrepresentative
      w₀ hw₀ hxlim data
  dsimp only at oldBoundary
  obtain ⟨S, Q, B, Xstrip, K, K0, Fbranch, I, generatorCount,
      generator, representativePolynomial, coefficientNeighborhood,
      _oldNextIdeal, _oldTail, _oldCertificate, _oldIndex, _oldPolynomial,
      hQ, hB, hXstrip, hFbranch, hreal, hHermite, hbound, hI, hheight,
      hspan, hWopen, h0W, hsupport, hanalytic, hG, hvanish,
      htopHeight, htopSpan, htopGerm, htopEval, htopVanish,
      _hOldPolynomial, _hOldEmbedding, _hOldMembership⟩ := oldBoundary
  have hheight' : ((p + m : ℕ) : ENat) ≤ I.height := by
    simpa only [Nat.add_comm] using hheight
  let preprocessed := Classical.choice
    (data.nonempty_paperRankHermiteTopPrefixPreprocessedTraceData
      S I hheight')
  obtain ⟨hpaddedSpan, hpaddedGerm, hpaddedVanish⟩ :=
    data.paperRankHermiteTopPrefixPaddedFamily_spec S I generator
      representativePolynomial
      (fun n ↦ paperRankRetainedArgument
        (paperRankFullHermiteSmoothValue (D.translateToZero w₀)
          representative (restrictedOffsetTranslateToZero w₀ offset) S
          B Fbranch)
        (restrictedSourceTranslateToZero w₀ (x n)))
      (fun n ↦ (restrictedSourceTranslateToZero w₀ (x n)).1.2)
      hspan hG hvanish
  have hselectedTendsto : Tendsto
      (data.subsequence ∘ preprocessed.balancingSubsequence) atTop atTop :=
    preprocessed.selectedSubsequence_strictMono.tendsto_atTop
  have hpaddedSelected : ∀ᶠ n in atTop, ∀ j,
      MvPolynomial.eval
        (data.paperRankHermiteTopPrefixAssignment S
          (paperRankRetainedArgument
            (paperRankFullHermiteSmoothValue (D.translateToZero w₀)
              representative (restrictedOffsetTranslateToZero w₀ offset) S
              B Fbranch)
            (restrictedSourceTranslateToZero w₀
              (x (data.subsequence
                (preprocessed.balancingSubsequence n))))))
        (data.paperRankHermiteTopPrefixPaddedRepresentative S
          representativePolynomial j
          (restrictedSourceTranslateToZero w₀
            (x (data.subsequence
              (preprocessed.balancingSubsequence n)))).1.2) = 0 := by
    simpa only [Function.comp_apply] using
      hselectedTendsto.eventually hpaddedVanish
  refine ⟨{
    S := S
    Q := Q
    B := B
    Xstrip := Xstrip
    K := K
    K0 := K0
    Fbranch := Fbranch
    I := I
    generatorCount := generatorCount
    generator := generator
    representativePolynomial := representativePolynomial
    coefficientNeighborhood := coefficientNeighborhood
    polynomial_value_eq := hQ
    B_pos := hB
    Xstrip_gt_one := hXstrip
    branch_analytic := hFbranch
    branch_real := hreal
    hermiteFamily := hHermite
    offset_bound := hbound
    rankIdeal_eq := hI
    rankHeight := hheight
    generator_span := hspan
    coefficientNeighborhood_open := hWopen
    origin_mem_coefficientNeighborhood := h0W
    representative_support := hsupport
    representative_coeff_analytic := hanalytic
    generator_germ := hG
    rank_vanish := hvanish
    topPrefix_height := htopHeight
    topPrefix_span := htopSpan
    topPrefix_germ := htopGerm
    topPrefix_evaluation := htopEval
    topPrefix_vanish := htopVanish
    preprocessed := preprocessed
    selected_regularZero := fun n ↦
      hx (data.subsequence (preprocessed.balancingSubsequence n))
    selected_parameter_tendsto := ?_
    selected_representative_tendsto := ?_
    paddedTopPrefix_span := hpaddedSpan
    paddedTopPrefix_germ := hpaddedGerm
    paddedTopPrefix_selected_vanish := hpaddedSelected
  }⟩
  · simpa only [Function.comp_def] using hxlim.comp hselectedTendsto
  · intro i
    simpa only [Function.comp_def] using
      (hxrepresentative i).comp hselectedTendsto

end AbelFormalization
