import AbelFormalization.HermiteRankPreprocessedIndividualMixedBoundary
import AbelFormalization.HermiteRankPreprocessedSimultaneousQuantitativeTail

/-!
# Compatibility of the individual terminal and first simultaneous boundaries

The individual balancing segment is written in the literal flat ordered-prefix
variables.  The simultaneous segment first curries the active cluster out of
that prefix and then relabels it by the balancing plan's final order.  This
module records the exact numeric compatibility across those two coordinate
changes.

At the terminal individual boundary, a block carries exact derivatives iff its
balancing coordinate occurs in the fixed decrement list.  After final-order
relabeling this is precisely `simultaneousBlockTouchedByIndividualSteps`, the
case split used by operation zero's op-sensitive simultaneous jet.  Untouched
blocks use the same common real-Hermite datum on both sides.  The additional
simultaneous tail is inserted into the individual boundary, so both sides are
evaluated at `simultaneousQuantitativeReindex`.

No evaluation homomorphism on all real-analytic germs is used here.  The output
is equality of the literal symbol assignments; finite analytic representative
data can consume it coefficientwise.
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

noncomputable local instance individualSimultaneousBoundaryBlockDecidableEq
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- The last boundary of the literal individual decrement trace. -/
abbrev individualMixedTerminalBoundaryIndex
    (c : Fin data.orderedClusterCount) :
    Fin ((boundary.individualNumericSteps D representative offset radius Fsys x
      w₀ hw₀ data c).length + 1) :=
  Fin.last (boundary.individualNumericSteps D representative offset radius Fsys
    x w₀ hw₀ data c).length

/-- At the last boundary, `processed` means membership in the complete
literal individual step list. -/
@[simp]
theorem individualMixedBoundaryProcessed_terminal_iff
    (c : Fin data.orderedClusterCount)
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) :
    boundary.individualMixedBoundaryProcessed D representative offset radius
        Fsys x w₀ hw₀ data c
        (boundary.individualMixedTerminalBoundaryIndex D representative offset
          radius Fsys x w₀ hw₀ data c) b ↔
      b ∈ boundary.individualNumericSteps D representative offset radius Fsys x
        w₀ hw₀ data c := by
  change b ∈
      (data.orderedClusterPrefixIndividualSteps c
        (boundary.preprocessed.fixedSteps c)).take
          (data.orderedClusterPrefixIndividualSteps c
            (boundary.preprocessed.fixedSteps c)).length ↔
    b ∈ data.orderedClusterPrefixIndividualSteps c
      (boundary.preprocessed.fixedSteps c)
  rw [List.take_length]

/-- A literal active block is processed at the terminal boundary exactly when
its balancing coordinate occurs in the fixed decrement list. -/
theorem individualMixedBoundaryProcessed_terminal_balancingBlock_iff
    (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    boundary.individualMixedBoundaryProcessed D representative offset radius
        Fsys x w₀ hw₀ data c
        (boundary.individualMixedTerminalBoundaryIndex D representative offset
          radius Fsys x w₀ hw₀ data c)
        (data.orderedClusterBalancingPrefixBlock c i) ↔
      i ∈ boundary.preprocessed.fixedSteps c := by
  rw [boundary.individualMixedBoundaryProcessed_terminal_iff D representative
    offset radius Fsys x w₀ hw₀ data]
  change data.orderedClusterBalancingPrefixBlock c i ∈
      (boundary.preprocessed.fixedSteps c).map
        (data.orderedClusterBalancingPrefixBlock c) ↔ _
  constructor
  · intro hmem
    obtain ⟨j, hj, hji⟩ := List.mem_map.mp hmem
    have hsplit :
        (Sum.inl (data.orderedClusterBalancingToActiveEquiv c j) :
          Fin (data.orderedCluster c).card ⊕
            data.OrderedClusterPrefixBlock c.val) =
          (Sum.inl (data.orderedClusterBalancingToActiveEquiv c i) :
            Fin (data.orderedCluster c).card ⊕
              data.OrderedClusterPrefixBlock c.val) := by
      simpa only [data.orderedClusterBalancingPrefixBlock_split] using
        congrArg (data.orderedClusterPrefixSuccEquiv c) hji
    have hactive : data.orderedClusterBalancingToActiveEquiv c j =
        data.orderedClusterBalancingToActiveEquiv c i :=
      Sum.inl.inj hsplit
    have hji' : j = i :=
      (data.orderedClusterBalancingToActiveEquiv c).injective hactive
    simpa [hji'] using hj
  · intro hi
    exact List.mem_map.mpr ⟨i, hi, rfl⟩

/-- A smaller-prefix block never belongs to the active cluster's individual
decrement list. -/
theorem individualMixedBoundaryProcessed_terminal_smaller_false
    (c : Fin data.orderedClusterCount)
    (b : data.OrderedClusterPrefixBlock c.val) :
    ¬ boundary.individualMixedBoundaryProcessed D representative offset radius
        Fsys x w₀ hw₀ data c
        (boundary.individualMixedTerminalBoundaryIndex D representative offset
          radius Fsys x w₀ hw₀ data c)
        ((data.orderedClusterPrefixSuccEquiv c).symm (Sum.inr b)) := by
  rw [boundary.individualMixedBoundaryProcessed_terminal_iff D representative
    offset radius Fsys x w₀ hw₀ data]
  change (data.orderedClusterPrefixSuccEquiv c).symm (Sum.inr b) ∉
    (boundary.preprocessed.fixedSteps c).map
      (data.orderedClusterBalancingPrefixBlock c)
  intro hmem
  obtain ⟨i, _hi, hib⟩ := List.mem_map.mp hmem
  have hsplit := congrArg (data.orderedClusterPrefixSuccEquiv c) hib
  simp only [data.orderedClusterBalancingPrefixBlock_split,
    Equiv.apply_symm_apply] at hsplit
  cases hsplit

/-- The smaller-prefix injection preserves the underlying representative
block. -/
@[simp]
theorem orderedClusterPrefixSuccEquiv_symm_inr_val
    (c : Fin data.orderedClusterCount)
    (b : data.OrderedClusterPrefixBlock c.val) :
    ((data.orderedClusterPrefixSuccEquiv c).symm (Sum.inr b)).1 = b.1 :=
  rfl

/-- The literal active-prefix block occupying final simultaneous position
`i`. -/
def individualMixedTerminalFinalBlock
    (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedCluster c).card) :
    data.OrderedClusterPrefixBlock (c.val + 1) :=
  data.orderedClusterBalancingPrefixBlock c
    (boundary.preprocessed.fixedOrder c
      ((data.orderedClusterBalancingToActiveEquiv c).symm i))

@[simp]
theorem individualMixedTerminalFinalBlock_val
    (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedCluster c).card) :
    (boundary.individualMixedTerminalFinalBlock D representative offset radius
      Fsys x w₀ hw₀ data c i).1 =
      boundary.simultaneousSelectedBlock D representative offset radius Fsys x
        w₀ hw₀ data c i :=
  rfl

/-- The explicit terminal block is the smaller-prefix splitting preimage of
the corresponding final-order active position. -/
theorem individualMixedTerminalFinalBlock_eq_finalPositionBlock
    (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedCluster c).card) :
    boundary.individualMixedTerminalFinalBlock D representative offset radius
        Fsys x w₀ hw₀ data c i =
      (data.orderedClusterPrefixSuccEquiv c).symm
        (Sum.inl (data.orderedClusterFinalPositionEquiv c
          (boundary.preprocessed.fixedOrder c) i)) := by
  apply (data.orderedClusterPrefixSuccEquiv c).injective
  simp [individualMixedTerminalFinalBlock,
    RepresentativeClusterSubsequence.orderedClusterFinalPositionEquiv]

/-- The terminal processed predicate in final active order is exactly the
op-sensitive predicate used by simultaneous operation zero. -/
theorem individualMixedBoundaryProcessed_terminal_finalBlock_iff
    (c : Fin data.orderedClusterCount)
    (i : Fin (data.orderedCluster c).card) :
    boundary.individualMixedBoundaryProcessed D representative offset radius
        Fsys x w₀ hw₀ data c
        (boundary.individualMixedTerminalBoundaryIndex D representative offset
          radius Fsys x w₀ hw₀ data c)
        (boundary.individualMixedTerminalFinalBlock D representative offset
          radius Fsys x w₀ hw₀ data c i) ↔
      boundary.simultaneousBlockTouchedByIndividualSteps D representative
        offset radius Fsys x w₀ hw₀ data c i := by
  exact boundary.individualMixedBoundaryProcessed_terminal_balancingBlock_iff
    D representative offset radius Fsys x w₀ hw₀ data c _

/-- The terminal individual paper parameter, reindexed by the additional
simultaneous tail. -/
def individualMixedTerminalParameterOnSimultaneousTail
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (n : ℕ) :
    PaperRankParameterSpace m p :=
  boundary.individualHermiteBoundaryParameter D representative offset radius
    Fsys x w₀ hw₀ data hA c
    (boundary.individualMixedTerminalBoundaryIndex D representative offset
      radius Fsys x w₀ hw₀ data c)
    (n + boundary.simultaneousQuantitativeTail D representative offset radius
      Fsys x w₀ hw₀ data hA)

/-- The terminal individual parameter and operation zero's simultaneous
pre-log parameter are literally the same after the common two-part tail. -/
theorem individualMixedTerminalParameterOnSimultaneousTail_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (n : ℕ) :
    boundary.individualMixedTerminalParameterOnSimultaneousTail D
        representative offset radius Fsys x w₀ hw₀ data hA c n =
      boundary.simultaneousPreLogParameter D representative offset radius Fsys
        x w₀ hw₀ data c 0
        (boundary.simultaneousQuantitativeReindex D representative offset radius
          Fsys x w₀ hw₀ data hA n) := by
  unfold individualMixedTerminalParameterOnSimultaneousTail
    individualHermiteBoundaryParameter simultaneousQuantitativeReindex
  have hindex :
      (n + boundary.simultaneousQuantitativeTail D representative offset radius
          Fsys x w₀ hw₀ data hA) +
          boundary.individualQuantitativeTail D representative offset radius
            Fsys x w₀ hw₀ data hA =
        (n + boundary.individualQuantitativeTail D representative offset radius
          Fsys x w₀ hw₀ data hA) +
          boundary.simultaneousQuantitativeTail D representative offset radius
            Fsys x w₀ hw₀ data hA := by
    omega
  rw [hindex]
  apply Prod.ext
  · funext block
    by_cases hblock : block ∈ data.orderedCluster c
    · simp [clusterPrefixParameter, simultaneousPreLogParameter, hblock,
        individualMixedTerminalBoundaryIndex, individualNumericSteps,
        RepresentativeClusterSubsequence.orderedClusterPrefixIndividualSteps]
    · simp [clusterPrefixParameter, simultaneousPreLogParameter, hblock]
  · rfl

/-- The terminal mixed flat assignment, shifted by the extra simultaneous
tail so that it uses the common selected index. -/
def individualMixedTerminalSymbolValueOnSimultaneousTail
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)) → ℕ → ℝ :=
  fun z n ↦
    boundary.individualMixedBoundarySymbolValue D representative offset radius
      Fsys x w₀ hw₀ data hA c
      (boundary.individualMixedTerminalBoundaryIndex D representative offset
        radius Fsys x w₀ hw₀ data c) z
      (n + boundary.simultaneousQuantitativeTail D representative offset radius
        Fsys x w₀ hw₀ data hA)

/-- Embed a symbol in final simultaneous active order back into the literal
flat prefix block which occupies that final position. -/
def individualMixedTerminalFinalActiveSymbol
    (c : Fin data.orderedClusterCount) :
    ClusterOperationSymbol (Fin (data.orderedCluster c).card)
        (terminalTotalDerivativeCount (fun _ ↦
          paperRankHermiteHigherCount boundary.S)) →
      ClusterOperationSymbol
        (data.OrderedClusterPrefixBlock (c.val + 1))
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
  | Sum.inl i =>
      Sum.inl (boundary.individualMixedTerminalFinalBlock D representative
        offset radius Fsys x w₀ hw₀ data c i)
  | Sum.inr (Sum.inl ⟨i, r⟩) =>
      Sum.inr (Sum.inl
        ⟨boundary.individualMixedTerminalFinalBlock D representative offset
          radius Fsys x w₀ hw₀ data c i, r⟩)
  | Sum.inr (Sum.inr i) =>
      Sum.inr (Sum.inr
        (boundary.individualMixedTerminalFinalBlock D representative offset
          radius Fsys x w₀ hw₀ data c i))

/-- The terminal individual active assignment after the cluster's final-order
transport. -/
def individualMixedTerminalFinalActiveValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ClusterOperationSymbol (Fin (data.orderedCluster c).card)
        (terminalTotalDerivativeCount (fun _ ↦
          paperRankHermiteHigherCount boundary.S)) → ℕ → ℝ :=
  fun z ↦ boundary.individualMixedTerminalSymbolValueOnSimultaneousTail D
    representative offset radius Fsys x w₀ hw₀ data hA c
    (boundary.individualMixedTerminalFinalActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c z)

/-- The common-tail operation-zero active assignment with the op-sensitive
mixed/exact jet family. -/
abbrev simultaneousFirstMixedActiveValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :=
  simultaneousCentralPreLogActiveAssignment
    (boundary.simultaneousQuantitativePostLogScale D representative offset
      radius Fsys x w₀ hw₀ data hA c 0)
    (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S))
    (boundary.simultaneousQuantitativeOperationJetSequence D representative
      offset radius Fsys x w₀ hw₀ data hA c
      (boundary.simultaneousNumericStage D representative offset radius Fsys x
        w₀ hw₀ data c).certificate.firstCentralStepIndex)

/-- The fresh operation-zero jet at an untouched block evaluates to the
Hermite coefficient of the simultaneous pre-log parameter. -/
theorem simultaneousFirstFreshSourceJet_eq_coefficientValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (n : ℕ) (i : Fin (data.orderedCluster c).card)
    (r : Fin (paperRankHermiteHigherCount boundary.S + 1)) :
    (boundary.simultaneousReindexedFreshRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c
        (boundary.simultaneousQuantitativeReindex D representative offset radius
          Fsys x w₀ hw₀ data hA) 0
        (fun q k ↦ boundary.simultaneousQuantitativePostLogScale_gt D
          representative offset radius Fsys x w₀ hw₀ data hA c
          (boundary.simultaneousNumericStage D representative offset radius
            Fsys x w₀ hw₀ data c).certificate.firstCentralStepIndex k q)
        n i).sourceJet r =
      paperRankHermiteCoefficientValue (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        boundary.B (fun _ ↦ boundary.Fbranch)
        (boundary.simultaneousPreLogParameter D representative offset radius
          Fsys x w₀ hw₀ data c 0
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA n))
        ((Sum.inr (boundary.simultaneousSelectedBlock D representative offset
          radius Fsys x w₀ hw₀ data c i)) : Fin 0 ⊕ Fin m)
        (paperRankHermitePositiveCoefficientIndex boundary.S
          ((Sum.inr (boundary.simultaneousSelectedBlock D representative offset
            radius Fsys x w₀ hw₀ data c i)) : Fin 0 ⊕ Fin m)
          (finCongr (paperRankHermiteHigherCount_add_one boundary.S) r)) := by
  let H := (boundary.commonRealHermiteData D representative offset radius Fsys
    x w₀ hw₀ data hA).fullHermite
  let r' : Fin (paperRankHermitePositiveDerivativeCount boundary.S) :=
    finCongr (paperRankHermiteHigherCount_add_one boundary.S) r
  have hsource := H.paperRankRealJetSequence_sourceJet_eq_coefficientValue
    (D.translateToZero w₀) representative
    (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B_pos
    (boundary.simultaneousSelectedBlock D representative offset radius Fsys x
      w₀ hw₀ data c)
    (boundary.simultaneousReindexedPostLogScale D representative offset radius
      Fsys x w₀ hw₀ data c
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA) 0)
    (fun q k ↦ boundary.simultaneousQuantitativePostLogScale_gt D
      representative offset radius Fsys x w₀ hw₀ data hA c
      (boundary.simultaneousNumericStage D representative offset radius Fsys x
        w₀ hw₀ data c).certificate.firstCentralStepIndex k q)
    (fun q ↦ (boundary.selectedTranslatedParameter D representative offset
      radius Fsys x w₀ hw₀ data
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA q)).2)
    (fun q k ↦ boundary.selectedTranslatedOffset_bound D representative offset
      radius Fsys x w₀ hw₀ data
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA q) k)
    (fun q ↦ boundary.simultaneousPreLogParameter D representative offset radius
      Fsys x w₀ hw₀ data c 0
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA q))
    (fun q k ↦ boundary.simultaneousPreLogParameter_center D representative
      offset radius Fsys x w₀ hw₀ data hA c 0
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA q) k)
    (fun q ↦ boundary.simultaneousPreLogParameter_box D representative offset
      radius Fsys x w₀ hw₀ data c 0
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA q))
    n i r'
  unfold simultaneousReindexedFreshRealJetSequence
  rw [castRealCentralJetSubstitutionData_sourceJet]
  simpa [r'] using hsource

/-- After final-order transport, the terminal individual active assignment is
exactly operation zero's op-sensitive simultaneous pre-log assignment. -/
theorem individualMixedTerminalFinalActiveValue_eq_simultaneousFirstMixed
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    boundary.individualMixedTerminalFinalActiveValue D representative offset
        radius Fsys x w₀ hw₀ data hA c =
      boundary.simultaneousFirstMixedActiveValue D representative offset radius
        Fsys x w₀ hw₀ data hA c := by
  let φ := boundary.simultaneousQuantitativeReindex D representative offset
    radius Fsys x w₀ hw₀ data hA
  have huFirst : ∀ n i,
      (boundary.commonRealHermiteData D representative offset radius Fsys x
          w₀ hw₀ data hA).u0 <
        boundary.simultaneousReindexedPostLogScale D representative offset
          radius Fsys x w₀ hw₀ data c φ 0 i n := by
    intro n i
    simpa only [φ, simultaneousReindexedPostLogScale_apply,
      ClusterAlgebraicReductionCertificate.firstCentralStepIndex] using
      boundary.simultaneousQuantitativePostLogScale_gt D representative offset
        radius Fsys x w₀ hw₀ data hA c
        (boundary.simultaneousNumericStage D representative offset radius Fsys x
          w₀ hw₀ data c).certificate.firstCentralStepIndex i n
  funext z n
  rcases z with i | z
  · change
      (boundary.individualMixedTerminalParameterOnSimultaneousTail D
        representative offset radius Fsys x w₀ hw₀ data hA c n).1
          (boundary.simultaneousSelectedBlock D representative offset radius
            Fsys x w₀ hw₀ data c i) = _
    rw [boundary.individualMixedTerminalParameterOnSimultaneousTail_eq D
      representative offset radius Fsys x w₀ hw₀ data hA c n]
    exact boundary.simultaneousPreLogParameter_center D representative offset
      radius Fsys x w₀ hw₀ data hA c 0
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n) i
  · rcases z with ir | i
    · rcases ir with ⟨i, r⟩
      change (if boundary.individualMixedBoundaryProcessed D representative
          offset radius Fsys x w₀ hw₀ data c
          (boundary.individualMixedTerminalBoundaryIndex D representative offset
            radius Fsys x w₀ hw₀ data c)
          (boundary.individualMixedTerminalFinalBlock D representative offset
            radius Fsys x w₀ hw₀ data c i) then
            iteratedDeriv (r.val + 1) A
              ((boundary.individualMixedTerminalParameterOnSimultaneousTail D
                representative offset radius Fsys x w₀ hw₀ data hA c n).1
                (boundary.simultaneousSelectedBlock D representative offset
                  radius Fsys x w₀ hw₀ data c i))
          else
            boundary.individualHermiteBoundarySymbolValue D representative
              offset radius Fsys x w₀ hw₀ data hA c
              (boundary.individualMixedTerminalBoundaryIndex D representative
                offset radius Fsys x w₀ hw₀ data c)
              (Sum.inr (Sum.inl
                ⟨boundary.individualMixedTerminalFinalBlock D representative
                  offset radius Fsys x w₀ hw₀ data c i, r⟩))
              (n + boundary.simultaneousQuantitativeTail D representative offset
                radius Fsys x w₀ hw₀ data hA)) = _
      by_cases htouched : boundary.simultaneousBlockTouchedByIndividualSteps D
          representative offset radius Fsys x w₀ hw₀ data c i
      · rw [if_pos ((boundary.individualMixedBoundaryProcessed_terminal_finalBlock_iff
          D representative offset radius Fsys x w₀ hw₀ data c i).2 htouched)]
        change _ =
          (boundary.simultaneousReindexedOperationJetSequence D representative
            offset radius Fsys x w₀ hw₀ data hA c φ 0 huFirst n i).sourceJet r
        rw [boundary.simultaneousReindexedOperationJetSequence_first_sourceJet_of_touched
          D representative offset radius Fsys x w₀ hw₀ data hA c φ
          huFirst n i htouched r]
        rw [boundary.individualMixedTerminalParameterOnSimultaneousTail_eq D
          representative offset radius Fsys x w₀ hw₀ data hA c n]
        rw [boundary.simultaneousPreLogParameter_center D representative offset
          radius Fsys x w₀ hw₀ data hA c 0
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA n) i]
        simpa only [φ, simultaneousReindexedPostLogScale_apply]
      · have hnotProcessed :
            ¬ boundary.individualMixedBoundaryProcessed D representative
              offset radius Fsys x w₀ hw₀ data c
              (boundary.individualMixedTerminalBoundaryIndex D representative
                offset radius Fsys x w₀ hw₀ data c)
              (boundary.individualMixedTerminalFinalBlock D representative
                offset radius Fsys x w₀ hw₀ data c i) :=
          (not_congr
            (boundary.individualMixedBoundaryProcessed_terminal_finalBlock_iff D
              representative offset radius Fsys x w₀ hw₀ data c i)).2
            htouched
        rw [if_neg hnotProcessed]
        rw [boundary.individualHermiteBoundarySymbolValue_positiveDerivative D
          representative offset radius Fsys x w₀ hw₀ data hA c
          (boundary.individualMixedTerminalBoundaryIndex D representative offset
            radius Fsys x w₀ hw₀ data c)
          (boundary.individualMixedTerminalFinalBlock D representative offset
            radius Fsys x w₀ hw₀ data c i) r]
        rw [boundary.individualMixedTerminalFinalBlock_val D representative
          offset radius Fsys x w₀ hw₀ data c i]
        have hparameter :
            boundary.individualHermiteBoundaryParameter D representative offset
                radius Fsys x w₀ hw₀ data hA c
                (boundary.individualMixedTerminalBoundaryIndex D representative
                  offset radius Fsys x w₀ hw₀ data c)
                (n + boundary.simultaneousQuantitativeTail D representative
                  offset radius Fsys x w₀ hw₀ data hA) =
              boundary.simultaneousPreLogParameter D representative offset radius
                Fsys x w₀ hw₀ data c 0
                (boundary.simultaneousQuantitativeReindex D representative offset
                  radius Fsys x w₀ hw₀ data hA n) :=
          boundary.individualMixedTerminalParameterOnSimultaneousTail_eq D
            representative offset radius Fsys x w₀ hw₀ data hA c n
        rw [hparameter]
        change _ =
          (boundary.simultaneousReindexedOperationJetSequence D representative
            offset radius Fsys x w₀ hw₀ data hA c φ 0 huFirst n i).sourceJet r
        rw [boundary.simultaneousReindexedOperationJetSequence_first_eq_fresh_of_untouched
          D representative offset radius Fsys x w₀ hw₀ data hA c φ
          huFirst n i htouched]
        let r' : Fin (paperRankHermitePositiveDerivativeCount boundary.S) :=
          finCongr (paperRankHermiteHigherCount_add_one boundary.S) r
        have hindex :
            (finCongr (paperRankHermiteHigherCount_add_one boundary.S) r).succ =
              paperRankHermitePositiveCoefficientIndex boundary.S
                ((Sum.inr (boundary.simultaneousSelectedBlock D representative
                  offset radius Fsys x w₀ hw₀ data c i)) : Fin 0 ⊕ Fin m)
                r' := by
          apply Fin.ext
          rfl
        rw [hindex]
        simpa only [φ, r'] using
          (boundary.simultaneousFirstFreshSourceJet_eq_coefficientValue D
            representative offset radius Fsys x w₀ hw₀ data hA c n i r).symm
    · change A
        ((boundary.individualMixedTerminalParameterOnSimultaneousTail D
          representative offset radius Fsys x w₀ hw₀ data hA c n).1
          (boundary.simultaneousSelectedBlock D representative offset radius
            Fsys x w₀ hw₀ data c i)) = _
      rw [boundary.individualMixedTerminalParameterOnSimultaneousTail_eq D
        representative offset radius Fsys x w₀ hw₀ data hA c n]
      rw [boundary.simultaneousPreLogParameter_center D representative offset
        radius Fsys x w₀ hw₀ data hA c 0
        (boundary.simultaneousQuantitativeReindex D representative offset radius
          Fsys x w₀ hw₀ data hA n) i]
      simp [simultaneousFirstMixedActiveValue,
        simultaneousCentralPreLogActiveAssignment,
        realCentralTransferActualValue]
      unfold simultaneousPostLogScale
      rw [data.orderedClusterSimultaneousPostLogScale_zero]
      rfl

/-- A block in the smaller ordered prefix is disjoint from the active
cluster. -/
theorem orderedClusterPrefixBlock_not_mem_active
    (c : Fin data.orderedClusterCount)
    (b : data.OrderedClusterPrefixBlock c.val) :
    b.1 ∉ data.orderedCluster c := by
  obtain ⟨d, hd, hbd⟩ := b.2
  intro hbc
  exact Finset.disjoint_left.mp
    (data.orderedCluster_disjoint (ne_of_lt hd)) hbd hbc

/-- Every smaller-prefix center in the first simultaneous parameter eventually
lies beyond the Hermite family's real-agreement threshold. -/
theorem eventually_simultaneousFirstSmallerPrefixCenter_gt
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (b : data.OrderedClusterPrefixBlock c.val) :
    ∀ᶠ n in atTop,
      boundary.Xstrip + boundary.B + 3 <
        (boundary.simultaneousPreLogParameter D representative offset radius
          Fsys x w₀ hw₀ data c 0
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA n)).1 b.1 := by
  have htendsto := (boundary.selected_representative_tendsto b.1).comp
    (boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
      offset radius Fsys x w₀ hw₀ data hA)
  have hnotmem : b.1 ∉ data.orderedCluster c := by
    obtain ⟨d, hd, hbd⟩ := b.2
    intro hbc
    exact Finset.disjoint_left.mp
      (data.orderedCluster_disjoint (ne_of_lt hd)) hbd hbc
  apply (htendsto.eventually
    (eventually_gt_atTop (boundary.Xstrip + boundary.B + 3))).mono
  intro n hn
  simpa [simultaneousPreLogParameter, hnotmem, selectedIndex] using hn

/-- Above the stored Hermite threshold, coefficient zero on a smaller-prefix
block is the exact Abel time value. -/
theorem simultaneousFirstSmallerPrefix_time_eq_exact_of_threshold
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (b : data.OrderedClusterPrefixBlock c.val) (n : ℕ)
    (hcenter : boundary.Xstrip + boundary.B + 3 <
      (boundary.simultaneousPreLogParameter D representative offset radius Fsys
        x w₀ hw₀ data c 0
        (boundary.simultaneousQuantitativeReindex D representative offset radius
          Fsys x w₀ hw₀ data hA n)).1 b.1) :
    boundary.simultaneousSmallerPrefixSequenceValue D representative offset
        radius Fsys x w₀ hw₀ data c 0 (Sum.inr (Sum.inr b))
        (boundary.simultaneousQuantitativeReindex D representative offset radius
          Fsys x w₀ hw₀ data hA n) =
      A ((boundary.simultaneousPreLogParameter D representative offset radius
        Fsys x w₀ hw₀ data c 0
        (boundary.simultaneousQuantitativeReindex D representative offset radius
          Fsys x w₀ hw₀ data hA n)).1 b.1) := by
  let sw := boundary.simultaneousPreLogParameter D representative offset radius
    Fsys x w₀ hw₀ data c 0
    (boundary.simultaneousQuantitativeReindex D representative offset radius
      Fsys x w₀ hw₀ data hA n)
  let nodes : Option (Fin boundary.S.card) → ℂ := fun node ↦
    (paperRankHermiteNodes (D.translateToZero w₀) representative
      (restrictedOffsetTranslateToZero w₀ offset) boundary.S b.1 sw.2 node : ℂ)
  have hoffset : ∀ k : Fin boundary.S.card,
      |(restrictedOffsetTranslateToZero w₀ offset
          (restrictedJetEnumeration boundary.S k).1 :
          RestrictedBoxSpace p → ℝ) sw.2| ≤ boundary.B := by
    intro k
    dsimp only [sw]
    rw [boundary.simultaneousPreLogParameter_box D representative offset radius
      Fsys x w₀ hw₀ data]
    exact boundary.selectedTranslatedOffset_bound D representative offset radius
      Fsys x w₀ hw₀ data
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n) k
  have hnodes : nodes ∈ hermiteNodeNeighborhood boundary.B := by
    exact paperRankHermiteNodes_mem_hermiteNodeNeighborhood
      (D.translateToZero w₀) representative
      (restrictedOffsetTranslateToZero w₀ offset) boundary.S
      boundary.hermiteFamily boundary.B_pos sw.2 hoffset b.1
  have hconstant := boundary.hermiteFamily.constant_coefficient (sw.1 b.1)
    hcenter nodes hnodes (none : Option (Fin boundary.S.card))
    (by simp [nodes, paperRankHermiteNodes])
    (by simp [paperRankHermiteNodeMultiplicity])
  change RepresentativeClusterSubsequence.paperRankHermitePrefixValue data
      (D.translateToZero w₀) representative
      (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
      boundary.Fbranch sw c.val (Sum.inr (Sum.inr b)) = A (sw.1 b.1)
  rw [RepresentativeClusterSubsequence.paperRankHermitePrefixValue_time]
  change
    (abelHermiteCoeff (fun _ ↦ boundary.Fbranch) boundary.B
      (paperRankHermiteNodeMultiplicity boundary.S) (sw.1 b.1) nodes 0).re =
      A (sw.1 b.1)
  rw [hconstant]
  simp

/-- The terminal individual smaller-prefix assignment is eventually the common
coefficient-symbol assignment used by simultaneous operation zero.  The only
non-pointwise coordinate is coefficient zero: the individual mixed state
stores `A(center)` while the Hermite assignment stores its coefficient-zero
formula, and `hermiteFamily.constant_coefficient` identifies them beyond the
stored threshold. -/
theorem individualMixedTerminalCoefficientValue_eventuallyEq_simultaneousFirst
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ∀ᶠ n in atTop, ∀ z,
      RepresentativeClusterSubsequence.orderedClusterPrefixCoefficientAssignment
          data c (paperRankHermiteHigherCount boundary.S + 1)
          (boundary.individualMixedTerminalSymbolValueOnSimultaneousTail D
            representative offset radius Fsys x w₀ hw₀ data hA c) z n =
        boundary.simultaneousSmallerPrefixSequenceValue D representative offset
          radius Fsys x w₀ hw₀ data c 0 z
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA n) := by
  apply Filter.eventually_all.mpr
  intro z
  rcases z with b | z
  · apply Filter.Eventually.of_forall
    intro n
    rw [RepresentativeClusterSubsequence.orderedClusterPrefixCoefficientAssignment_free]
    unfold individualMixedTerminalSymbolValueOnSimultaneousTail
    rw [boundary.individualMixedBoundarySymbolValue_free D representative offset
      radius Fsys x w₀ hw₀ data]
    simp only [orderedClusterPrefixSuccEquiv_symm_inr_val]
    have hparameter :
        boundary.individualHermiteBoundaryParameter D representative offset
            radius Fsys x w₀ hw₀ data hA c
            (boundary.individualMixedTerminalBoundaryIndex D representative
              offset radius Fsys x w₀ hw₀ data c)
            (n + boundary.simultaneousQuantitativeTail D representative offset
              radius Fsys x w₀ hw₀ data hA) =
          boundary.simultaneousPreLogParameter D representative offset radius
            Fsys x w₀ hw₀ data c 0
            (boundary.simultaneousQuantitativeReindex D representative offset
              radius Fsys x w₀ hw₀ data hA n) :=
      boundary.individualMixedTerminalParameterOnSimultaneousTail_eq D
        representative offset radius Fsys x w₀ hw₀ data hA c n
    rw [hparameter]
    rfl
  · rcases z with br | b
    · rcases br with ⟨b, r⟩
      apply Filter.Eventually.of_forall
      intro n
      rw [RepresentativeClusterSubsequence.orderedClusterPrefixCoefficientAssignment_derivative]
      unfold individualMixedTerminalSymbolValueOnSimultaneousTail
      simp only [individualMixedBoundarySymbolValue,
        boundary.individualMixedBoundaryProcessed_terminal_smaller_false D
          representative offset radius Fsys x w₀ hw₀ data c b, if_false]
      rw [boundary.individualHermiteBoundarySymbolValue_positiveDerivative D
        representative offset radius Fsys x w₀ hw₀ data hA c]
      simp only [orderedClusterPrefixSuccEquiv_symm_inr_val]
      have hparameter :
          boundary.individualHermiteBoundaryParameter D representative offset
              radius Fsys x w₀ hw₀ data hA c
              (boundary.individualMixedTerminalBoundaryIndex D representative
                offset radius Fsys x w₀ hw₀ data c)
              (n + boundary.simultaneousQuantitativeTail D representative offset
                radius Fsys x w₀ hw₀ data hA) =
            boundary.simultaneousPreLogParameter D representative offset radius
              Fsys x w₀ hw₀ data c 0
              (boundary.simultaneousQuantitativeReindex D representative offset
                radius Fsys x w₀ hw₀ data hA n) :=
        boundary.individualMixedTerminalParameterOnSimultaneousTail_eq D
          representative offset radius Fsys x w₀ hw₀ data hA c n
      rw [hparameter]
      rfl
    · filter_upwards [boundary.eventually_simultaneousFirstSmallerPrefixCenter_gt
          D representative offset radius Fsys x w₀ hw₀ data hA c b] with n hn
      rw [RepresentativeClusterSubsequence.orderedClusterPrefixCoefficientAssignment_time]
      unfold individualMixedTerminalSymbolValueOnSimultaneousTail
      rw [boundary.individualMixedBoundarySymbolValue_time D representative
        offset radius Fsys x w₀ hw₀ data]
      simp only [orderedClusterPrefixSuccEquiv_symm_inr_val]
      have hparameter :
          boundary.individualHermiteBoundaryParameter D representative offset
              radius Fsys x w₀ hw₀ data hA c
              (boundary.individualMixedTerminalBoundaryIndex D representative
                offset radius Fsys x w₀ hw₀ data c)
              (n + boundary.simultaneousQuantitativeTail D representative offset
                radius Fsys x w₀ hw₀ data hA) =
            boundary.simultaneousPreLogParameter D representative offset radius
              Fsys x w₀ hw₀ data c 0
              (boundary.simultaneousQuantitativeReindex D representative offset
                radius Fsys x w₀ hw₀ data hA n) :=
        boundary.individualMixedTerminalParameterOnSimultaneousTail_eq D
          representative offset radius Fsys x w₀ hw₀ data hA c n
      rw [hparameter]
      exact (boundary.simultaneousFirstSmallerPrefix_time_eq_exact_of_threshold
        D representative offset radius Fsys x w₀ hw₀ data hA c b n hn).symm

/-! ## Equality of the two canonical boundary scales -/

/-- Once the padding by `2` is inactive, the full-prefix balancing scale is
the inverse-Abel value in final-order position zero.  The balancing plan
orders the final Abel times decreasingly, and `inverse A` is increasing. -/
private theorem clusterBalancingPrefixScale_length_eq_finalOrder_zero
    {k : ℕ} (hA : IsAbel A)
    (rawTime : ℕ → Fin (k + 1) → ℝ)
    (fixedSteps : List (Fin (k + 1)))
    (fixedOrder : Equiv.Perm (Fin (k + 1)))
    (n : ℕ) (base : ℝ)
    (plan : ClusterBalancingPlan (rawTime n) base)
    (hsteps : plan.steps = fixedSteps)
    (horder : plan.finalOrder = fixedOrder)
    (htwo : 2 ≤ inverse A
      (clusterShiftedTimes (rawTime n) fixedSteps (fixedOrder 0))) :
    clusterBalancingPrefixScale A rawTime fixedSteps fixedSteps.length n =
      inverse A
        (clusterShiftedTimes (rawTime n) fixedSteps (fixedOrder 0)) := by
  have hselected_le_max :
      inverse A
          (clusterShiftedTimes (rawTime n) fixedSteps (fixedOrder 0)) ≤
        clusterBalancingPrefixMaximum A rawTime fixedSteps
          fixedSteps.length n := by
    simpa only [clusterBalancingPrefixValue, clusterBalancingPrefixTime,
      List.take_length] using
      clusterBalancingPrefixValue_le_maximum A rawTime fixedSteps
        fixedSteps.length n (fixedOrder 0)
  rw [clusterBalancingPrefixScale,
    max_eq_right (htwo.trans hselected_le_max)]
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hy
    have hfinal := plan.antitone_finalTimes_comp_finalOrder
      (Fin.zero_le ((plan.finalOrder).symm i))
    simp only [Function.comp_apply, Equiv.apply_symm_apply,
      ClusterBalancingPlan.finalTimes] at hfinal
    rw [hsteps, horder] at hfinal
    exact hA.inverse_strictMono.monotone (by
      simpa only [clusterBalancingPrefixTime, List.take_length] using hfinal)
  · exact hselected_le_max

/-- The simultaneous boundary-zero scale diverges on the common
individual-plus-simultaneous tail. -/
theorem simultaneousQuantitativeBoundaryScale_zero_tendsto_atTop
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    Tendsto
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA c 0) atTop atTop := by
  let phi := boundary.simultaneousQuantitativeReindex D representative offset
    radius Fsys x w₀ hw₀ data hA
  have hresult : Tendsto (fun n ↦ inverse A
      (clusterShiftedTimes
        (data.orderedClusterRawTime
          (boundary.preprocessed.balancingSubsequence (phi n)) c)
        (boundary.preprocessed.fixedSteps c)
        (boundary.preprocessed.fixedOrder c 0))) atTop atTop := by
    apply hA.inverse_tendsto_atTop.comp
    have hmin :=
      (boundary.selectedClusterMinTime_tendsto_atTop D representative offset
        radius Fsys x w₀ hw₀ data hA c).comp
        (boundary.simultaneousQuantitativeReindex_tendsto_atTop D
          representative offset radius Fsys x w₀ hw₀ data hA)
    apply tendsto_atTop_mono' atTop _ hmin
    filter_upwards [] with n
    have hbase := (boundary.preprocessed.plans (phi n) c).base_le_final
      (boundary.preprocessed.fixedOrder c 0)
    have hsteps := boundary.preprocessed.plans_steps (phi n) c
    change data.orderedClusterMinTime c
        (boundary.preprocessed.balancingSubsequence (phi n)) ≤
      clusterShiftedTimes
        (data.orderedClusterRawTime
          (boundary.preprocessed.balancingSubsequence (phi n)) c)
        (boundary.preprocessed.fixedSteps c)
        (boundary.preprocessed.fixedOrder c 0)
    rw [← hsteps]
    exact hbase
  unfold simultaneousQuantitativeBoundaryScale
  unfold RepresentativeClusterSubsequence.orderedClusterSimultaneousBoundaryScale
  simpa only [simultaneousQuantitativeRawTime, simultaneousNumericRawTime,
    selectedClusterRawTime, simultaneousQuantitativeReindex, Nat.cast_zero,
    sub_zero, phi] using hresult

/-- The first simultaneous boundary scale and the terminal individual mixed
boundary scale agree eventually on their common two-part tail.  Final-order
position zero realizes the full-tuple maximum, and divergence eventually
removes the individual scale's padding by `2`. -/
theorem simultaneousQuantitativeBoundaryScale_zero_eventuallyEq_individualMixedTerminal
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ∀ᶠ n in atTop,
      boundary.simultaneousQuantitativeBoundaryScale D representative offset
          radius Fsys x w₀ hw₀ data hA c 0 n =
        data.orderedClusterIndividualBoundaryScale A
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA) c
          (boundary.preprocessed.fixedSteps c)
          (boundary.individualMixedTerminalBoundaryIndex D representative
            offset radius Fsys x w₀ hw₀ data c)
          (n + boundary.simultaneousQuantitativeTail D representative offset
            radius Fsys x w₀ hw₀ data hA) := by
  have htwo : ∀ᶠ n in atTop,
      2 ≤ boundary.simultaneousQuantitativeBoundaryScale D representative
        offset radius Fsys x w₀ hw₀ data hA c 0 n :=
    (boundary.simultaneousQuantitativeBoundaryScale_zero_tendsto_atTop D
      representative offset radius Fsys x w₀ hw₀ data hA c).eventually
        (eventually_ge_atTop 2)
  filter_upwards [htwo] with n hn
  let individualTail := boundary.individualQuantitativeTail D representative
    offset radius Fsys x w₀ hw₀ data hA
  let simultaneousTail := boundary.simultaneousQuantitativeTail D representative
    offset radius Fsys x w₀ hw₀ data hA
  let q := n + simultaneousTail
  let rawTime : ℕ → Fin (data.orderedClusterTailSize c + 1) → ℝ :=
    fun r ↦ data.orderedClusterRawTime
      (boundary.individualQuantitativeSubsequence D representative offset
        radius Fsys x w₀ hw₀ data hA r) c
  have hterminalVal :
      (boundary.individualMixedTerminalBoundaryIndex D representative offset
        radius Fsys x w₀ hw₀ data c).val =
        (boundary.preprocessed.fixedSteps c).length := by
    change (data.orderedClusterPrefixIndividualSteps c
      (boundary.preprocessed.fixedSteps c)).length =
        (boundary.preprocessed.fixedSteps c).length
    exact data.orderedClusterPrefixIndividualSteps_length c
      (boundary.preprocessed.fixedSteps c)
  have htwo' : 2 ≤ inverse A
      (clusterShiftedTimes (rawTime q) (boundary.preprocessed.fixedSteps c)
        (boundary.preprocessed.fixedOrder c 0)) := by
    simpa only [rawTime, q, individualQuantitativeSubsequence,
      simultaneousQuantitativeBoundaryScale, simultaneousQuantitativeRawTime,
      simultaneousNumericRawTime, selectedClusterRawTime,
      simultaneousQuantitativeReindex,
      RepresentativeClusterSubsequence.orderedClusterSimultaneousBoundaryScale,
      Nat.cast_zero, sub_zero, individualTail, simultaneousTail,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hn
  have hfull := clusterBalancingPrefixScale_length_eq_finalOrder_zero hA
    rawTime (boundary.preprocessed.fixedSteps c)
    (boundary.preprocessed.fixedOrder c) q
    (data.orderedClusterMinTime c
      (boundary.preprocessed.balancingSubsequence (q + individualTail)))
    (boundary.preprocessed.plans (q + individualTail) c)
    (boundary.preprocessed.plans_steps (q + individualTail) c)
    (boundary.preprocessed.plans_finalOrder (q + individualTail) c) htwo'
  simpa only [rawTime, q, individualQuantitativeSubsequence,
    simultaneousQuantitativeBoundaryScale, simultaneousQuantitativeRawTime,
    simultaneousNumericRawTime, selectedClusterRawTime,
    simultaneousQuantitativeReindex,
    RepresentativeClusterSubsequence.orderedClusterSimultaneousBoundaryScale,
    RepresentativeClusterSubsequence.orderedClusterIndividualBoundaryScale,
    RepresentativeClusterSubsequence.orderedClusterBalancingPrefixScale,
    hterminalVal,
    Nat.cast_zero, sub_zero, individualTail, simultaneousTail,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfull.symm

/-- The complete assignment compatibility needed to concatenate the terminal
individual boundary with the first simultaneous operation.  Both fields are
theorems here; downstream coefficientwise adapters can depend on this compact
record rather than repeat the coordinate analysis. -/
structure IndividualSimultaneousBoundaryCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) : Prop where
  active :
    boundary.individualMixedTerminalFinalActiveValue D representative offset
        radius Fsys x w₀ hw₀ data hA c =
      boundary.simultaneousFirstMixedActiveValue D representative offset radius
        Fsys x w₀ hw₀ data hA c
  coefficient : ∀ᶠ n in atTop, ∀ z,
    RepresentativeClusterSubsequence.orderedClusterPrefixCoefficientAssignment
        data c (paperRankHermiteHigherCount boundary.S + 1)
        (boundary.individualMixedTerminalSymbolValueOnSimultaneousTail D
          representative offset radius Fsys x w₀ hw₀ data hA c) z n =
      boundary.simultaneousSmallerPrefixSequenceValue D representative offset
        radius Fsys x w₀ hw₀ data c 0 z
        (boundary.simultaneousQuantitativeReindex D representative offset radius
          Fsys x w₀ hw₀ data hA n)

/-- Canonical compatibility of the two concrete paper boundaries. -/
def individualSimultaneousBoundaryCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    boundary.IndividualSimultaneousBoundaryCompatibility D representative
      offset radius Fsys x w₀ hw₀ data hA c where
  active :=
    boundary.individualMixedTerminalFinalActiveValue_eq_simultaneousFirstMixed
      D representative offset radius Fsys x w₀ hw₀ data hA c
  coefficient :=
    boundary.individualMixedTerminalCoefficientValue_eventuallyEq_simultaneousFirst
      D representative offset radius Fsys x w₀ hw₀ data hA c

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
