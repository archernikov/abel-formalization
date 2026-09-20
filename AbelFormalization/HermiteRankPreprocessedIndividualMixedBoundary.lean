import AbelFormalization.HermiteRankPreprocessedIndividualBoundaryValues
import AbelFormalization.HigherDerivatives

/-!
# Recursively mixed boundaries for individual Hermite decrements

A fresh Hermite family is the correct source jet only until its block is
decremented for the first time.  Every decrement replaces that block by the
exact central derivative family at the new inverse-Abel center.  Thus a
boundary which composes through the whole fixed list must mix untouched
Hermite blocks with exact derivative blocks already encountered by the list.

This file records that state invariant without a global evaluation map on
analytic germs.  It also chooses the corresponding source jet at every step:
Hermite at a first occurrence and the error-free exact derivative jet at a
repeated occurrence.
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

/-- Transporting the dependent derivative-count index carries a source-jet
coordinate by the inverse equality, just as for the existing error accessor. -/
@[simp]
theorem castRealCentralJetSubstitutionData_sourceJet
    {u u' : ℝ} {d d' : ℕ}
    (J : RealCentralJetSubstitutionData A u d)
    (hu : u = u') (hd : d = d') (r : Fin d') :
    (castRealCentralJetSubstitutionData J hu hd).sourceJet r =
      J.sourceJet (Fin.cast hd.symm r) := by
  subst u'
  subst d'
  rfl

noncomputable local instance individualMixedBoundaryBlockDecidableEq
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- An active-prefix block has already been decremented at boundary `q` when
it occurs in the first `q` literal individual steps. -/
def individualMixedBoundaryProcessed
    (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) : Prop :=
  b ∈ (boundary.individualNumericSteps D representative offset radius Fsys x
    w₀ hw₀ data c).take q.val

instance individualMixedBoundaryProcessed_decidable
    (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) :
    Decidable (boundary.individualMixedBoundaryProcessed D representative
      offset radius Fsys x w₀ hw₀ data c q b) :=
  Classical.dec _

/-- A step is repeated exactly when its literal selected block already occurs
in the preceding trace prefix. -/
def individualMixedStepIsRepeated
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) : Prop :=
    boundary.individualMixedBoundaryProcessed D representative offset radius
        Fsys x w₀ hw₀ data c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc
        (data.orderedClusterIndividualSelectedBlock c
          (boundary.preprocessed.fixedSteps c) j)

instance individualMixedStepIsRepeated_decidable
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    Decidable (boundary.individualMixedStepIsRepeated D representative offset
      radius Fsys x w₀ hw₀ data c j) :=
  Classical.dec _

/-- The block selected at a step belongs to the processed set at the
successor boundary. -/
theorem individualMixedBoundaryProcessed_succ_selected
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    boundary.individualMixedBoundaryProcessed D representative offset radius
        Fsys x w₀ hw₀ data c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ
        (data.orderedClusterIndividualSelectedBlock c
          (boundary.preprocessed.fixedSteps c) j) := by
  unfold individualMixedBoundaryProcessed
  rw [take_succ_eq_take_append_get]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Adding the selected block changes no other block's processed status. -/
theorem individualMixedBoundaryProcessed_succ_iff_of_ne
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (b : data.OrderedClusterPrefixBlock (c.val + 1))
    (hb : b ≠ data.orderedClusterIndividualSelectedBlock c
      (boundary.preprocessed.fixedSteps c) j) :
    boundary.individualMixedBoundaryProcessed D representative offset radius
        Fsys x w₀ hw₀ data c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ b ↔
      boundary.individualMixedBoundaryProcessed D representative offset radius
        Fsys x w₀ hw₀ data c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc b := by
  unfold individualMixedBoundaryProcessed
  rw [take_succ_eq_take_append_get, List.mem_append, List.mem_singleton]
  exact or_iff_left hb

/-- The mixed flat boundary keeps Hermite coefficients on blocks not yet
selected, and keeps exact derivatives on blocks already selected.  Its time
coordinate is the exact Abel time at the current center, which is the state
used by every central step. -/
def individualMixedBoundarySymbolValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1)) :
    ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)) → ℕ → ℝ
  | Sum.inl b, n =>
      (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 b.1
  | Sum.inr (Sum.inl ⟨b, r⟩), n =>
      if boundary.individualMixedBoundaryProcessed D representative offset
          radius Fsys x w₀ hw₀ data c q b then
        iteratedDeriv (r.val + 1) A
          ((boundary.individualHermiteBoundaryParameter D representative offset
            radius Fsys x w₀ hw₀ data hA c q n).1 b.1)
      else
        boundary.individualHermiteBoundarySymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c q
          (Sum.inr (Sum.inl ⟨b, r⟩)) n
  | Sum.inr (Sum.inr b), n =>
      A ((boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 b.1)

@[simp]
theorem individualMixedBoundarySymbolValue_free
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) (n : ℕ) :
    boundary.individualMixedBoundarySymbolValue D representative offset radius
        Fsys x w₀ hw₀ data hA c q (Sum.inl b) n =
      (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 b.1 :=
  rfl

@[simp]
theorem individualMixedBoundarySymbolValue_time
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) (n : ℕ) :
    boundary.individualMixedBoundarySymbolValue D representative offset radius
        Fsys x w₀ hw₀ data hA c q (Sum.inr (Sum.inr b)) n =
      A ((boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 b.1) :=
  rfl

/-- Selected-block restriction reads the representative coordinate of the
same literal block. -/
@[simp]
theorem selectedBlockActiveAssignment_individualMixedBoundary_free
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (selected : data.OrderedClusterPrefixBlock (c.val + 1))
    (i : Fin 1) (n : ℕ) :
    selectedBlockActiveAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        selected
        (boundary.individualMixedBoundarySymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c q) (Sum.inl i) n =
      (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 selected.1 := by
  fin_cases i
  rfl

/-- Selected-block restriction reads the mixed positive derivative coordinate
of the same literal block. -/
@[simp]
theorem selectedBlockActiveAssignment_individualMixedBoundary_derivative
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (selected : data.OrderedClusterPrefixBlock (c.val + 1))
    (i : Fin 1)
    (r : Fin (selectedBlockDerivativeCount
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)) selected i))
    (n : ℕ) :
    selectedBlockActiveAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        selected
        (boundary.individualMixedBoundarySymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c q)
        (Sum.inr (Sum.inl ⟨i, r⟩)) n =
      if boundary.individualMixedBoundaryProcessed D representative offset
          radius Fsys x w₀ hw₀ data c q selected then
        iteratedDeriv (r.val + 1) A
          ((boundary.individualHermiteBoundaryParameter D representative offset
            radius Fsys x w₀ hw₀ data hA c q n).1 selected.1)
      else
        boundary.individualHermiteBoundarySymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c q
          (Sum.inr (Sum.inl ⟨selected, r⟩)) n := by
  fin_cases i
  let d := data.orderedClusterPrefixConstantDerivativeCount
    (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)
  have hsymbol :
      (selectedBlockSplitOperationEquiv d selected).symm
          ((splitClusterBlockSymbolEquiv (Fin 1) (RemainingBlock selected)
            (selectedBlockDerivativeCount d selected)
            (remainingBlockDerivativeCount d selected)).symm
            (Sum.inl (Sum.inr (Sum.inl ⟨0, r⟩)))) =
        Sum.inr (Sum.inl ⟨selected, r⟩) := by
    apply (selectedBlockSplitOperationEquiv d selected).injective
    rw [Equiv.apply_symm_apply]
    have hbase : (selectedBlockSumEquiv selected).symm selected =
        Sum.inl (0 : Fin 1) := by
      simp [selectedBlockSumEquiv]
    simp [selectedBlockSplitOperationEquiv, clusterOperationSymbolEquiv,
      splitClusterBlockSymbolEquiv, selectedBlockSumEquiv,
      selectedBlockDerivativeCount, d]
    change
      (⟨Sum.inl (0 : Fin 1), r⟩ :
        Σ b : Fin 1 ⊕ RemainingBlock selected,
          Fin (Sum.elim (selectedBlockDerivativeCount d selected)
            (remainingBlockDerivativeCount d selected) b)) =
      ⟨(selectedBlockSumEquiv selected).symm selected, _⟩
    apply Sigma.ext
    · exact hbase.symm
    · have hmotive :
          selectedBlockDerivativeCount d selected 0 =
            Sum.elim (selectedBlockDerivativeCount d selected)
              (remainingBlockDerivativeCount d selected)
              ((selectedBlockSumEquiv selected).symm selected) := by
        rw [hbase]
        rfl
      apply (Fin.heq_ext_iff hmotive).2
      rfl
  unfold selectedBlockActiveAssignment
  change boundary.individualMixedBoundarySymbolValue D representative offset
      radius Fsys x w₀ hw₀ data hA c q
      ((selectedBlockSplitOperationEquiv d selected).symm
        ((splitClusterBlockSymbolEquiv (Fin 1) (RemainingBlock selected)
          (selectedBlockDerivativeCount d selected)
          (remainingBlockDerivativeCount d selected)).symm
          (Sum.inl (Sum.inr (Sum.inl ⟨0, r⟩))))) n = _
  rw [hsymbol]
  rfl

/-- Selected-block restriction reads the exact time coordinate of the same
literal block. -/
@[simp]
theorem selectedBlockActiveAssignment_individualMixedBoundary_time
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (selected : data.OrderedClusterPrefixBlock (c.val + 1))
    (i : Fin 1) (n : ℕ) :
    selectedBlockActiveAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        selected
        (boundary.individualMixedBoundarySymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c q)
        (Sum.inr (Sum.inr i)) n =
      A ((boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 selected.1) := by
  fin_cases i
  rfl

/-- The source jet used by the mixed recursion.  A first occurrence uses the
actual paper Hermite jet.  Every repeated occurrence uses the exact derivative
jet because the previous occurrence has already installed exact coordinates. -/
def individualMixedRealJetSequence
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    ∀ n i, RealCentralJetSubstitutionData A
      (boundary.individualPostLogScale D representative offset radius Fsys x
        w₀ hw₀ data c j i
        (n + boundary.individualQuantitativeTail D representative offset
          radius Fsys x w₀ hw₀ data hA))
      (paperRankHermitePositiveDerivativeCount boundary.S) :=
  fun n i ↦
    if boundary.individualMixedStepIsRepeated D representative offset radius
        Fsys x w₀ hw₀ data c j then
      hA.realDerivativeJetSubstitutionData
        (u := boundary.individualPostLogScale D representative offset radius
          Fsys x w₀ hw₀ data c j i
          (n + boundary.individualQuantitativeTail D representative offset
            radius Fsys x w₀ hw₀ data hA))
        (hA.inverse_pos _)
        (paperRankHermitePositiveDerivativeCount boundary.S)
    else
      boundary.individualQuantitativeRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c j n i

/-- At a repeated block the mixed source datum is definitionally the exact
derivative jet. -/
theorem individualMixedRealJetSequence_eq_exact
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (hrepeat : boundary.individualMixedStepIsRepeated D representative offset
      radius Fsys x w₀ hw₀ data c j) (n : ℕ) (i : Fin 1) :
    boundary.individualMixedRealJetSequence D representative offset radius
        Fsys x w₀ hw₀ data hA c j n i =
      hA.realDerivativeJetSubstitutionData
        (u := boundary.individualPostLogScale D representative offset radius
          Fsys x w₀ hw₀ data c j i
          (n + boundary.individualQuantitativeTail D representative offset
            radius Fsys x w₀ hw₀ data hA))
        (hA.inverse_pos _)
        (paperRankHermitePositiveDerivativeCount boundary.S) := by
  unfold individualMixedRealJetSequence
  rw [if_pos hrepeat]

/-- At a first occurrence the mixed source datum is the existing paper
Hermite jet. -/
theorem individualMixedRealJetSequence_eq_hermite
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (hfirst : ¬ boundary.individualMixedStepIsRepeated D representative offset
      radius Fsys x w₀ hw₀ data c j) (n : ℕ) (i : Fin 1) :
    boundary.individualMixedRealJetSequence D representative offset radius
        Fsys x w₀ hw₀ data hA c j n i =
      boundary.individualQuantitativeRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c j n i := by
  unfold individualMixedRealJetSequence
  rw [if_neg hfirst]

/-- The mixed jets with the scale and derivative-count expressions used
literally by the ordered-cluster trace. -/
def individualMixedTraceJets
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
    (boundary.individualMixedRealJetSequence D representative offset radius
      Fsys x w₀ hw₀ data hA c j n i)
    (boundary.individualQuantitativePostLogScale_eq D representative offset
      radius Fsys x w₀ hw₀ data hA c j i n).symm
    (boundary.individualQuantitativeStepDerivativeCount_apply D representative
      offset radius Fsys x w₀ hw₀ data c j i).symm

/-- The paper parameter underlying the predecessor mixed boundary is the
existing pre-log parameter at the common quantitative tail. -/
theorem individualHermiteBoundaryParameter_beforeStep
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) (n : ℕ) :
    boundary.individualHermiteBoundaryParameter D representative offset radius
        Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc n =
      boundary.individualPreLogParameter D representative offset radius Fsys x
        w₀ hw₀ data c j
        (n + boundary.individualQuantitativeTail D representative offset radius
          Fsys x w₀ hw₀ data hA) := by
  unfold individualHermiteBoundaryParameter individualPreLogParameter
  simp only [Fin.val_castSucc,
    RepresentativeClusterSubsequence.orderedClusterIndividualStepIndexEquiv_apply_val]

/-- The selected center at the successor boundary is the literal post-log
scale of that step. -/
theorem individualMixedBoundary_selectedCenter_afterStep
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (i : Fin 1) (n : ℕ) :
    (boundary.individualHermiteBoundaryParameter D representative offset radius
        Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ n).1
        (data.orderedClusterIndividualSelectedBlock c
          (boundary.preprocessed.fixedSteps c) j).1 =
      data.orderedClusterIndividualPostLogScale c A
        (fun q ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA q) c)
        (boundary.preprocessed.fixedSteps c) j i n := by
  rw [data.orderedClusterIndividualSelectedBlock_eq]
  simp only [data.orderedClusterBalancingPrefixBlock_val]
  rw [boundary.individualHermiteBoundaryParameter_activeCenter D representative
    offset radius Fsys x w₀ hw₀ data hA]
  rw [data.orderedClusterIndividualPostLogScale_apply]
  simpa only [Fin.val_succ, clusterBalancingStepValue,
    clusterBalancingPrefixTime,
    RepresentativeClusterSubsequence.orderedClusterIndividualStepIndexEquiv_apply_val,
    Subsingleton.elim i 0] using
      clusterBalancingPrefixValue_succ_selected A
        (fun q ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA q) c)
        (boundary.preprocessed.fixedSteps c) j n

/-- Every block distinct from the selected block keeps the same center across
one individual decrement. -/
theorem individualHermiteBoundaryParameter_center_succ_eq_of_ne
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (b : data.OrderedClusterPrefixBlock (c.val + 1))
    (hb : b ≠ data.orderedClusterIndividualSelectedBlock c
      (boundary.preprocessed.fixedSteps c) j) (n : ℕ) :
    (boundary.individualHermiteBoundaryParameter D representative offset radius
        Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ n).1 b.1 =
      (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc n).1 b.1 := by
  obtain ⟨d, hd, hbd⟩ := b.2
  by_cases hdc : d = c
  · subst d
    let k := balancingIndexOfMem x data c b.1 hbd
    have hk : k ≠ (boundary.preprocessed.fixedSteps c).get j := by
      intro hk
      apply hb
      apply Subtype.ext
      calc
        b.1 = data.orderedClusterEnumeration c k :=
          (orderedClusterEnumeration_balancingIndexOfMem x data c b.1 hbd).symm
        _ = data.orderedClusterEnumeration c
            ((boundary.preprocessed.fixedSteps c).get j) := congrArg _ hk
        _ = (data.orderedClusterIndividualSelectedBlock c
            (boundary.preprocessed.fixedSteps c) j).1 := by
          rw [data.orderedClusterIndividualSelectedBlock_eq]
          rfl
    rw [← orderedClusterEnumeration_balancingIndexOfMem x data c b.1 hbd]
    rw [boundary.individualHermiteBoundaryParameter_activeCenter D representative
      offset radius Fsys x w₀ hw₀ data hA,
      boundary.individualHermiteBoundaryParameter_activeCenter D representative
        offset radius Fsys x w₀ hw₀ data hA]
    simpa only [Fin.val_succ, Fin.val_castSucc,
      RepresentativeClusterSubsequence.orderedClusterIndividualStepIndexEquiv_apply_val]
      using clusterBalancingPrefixValue_succ_of_ne
        (A := A)
        (fun q ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA q) c)
        (boundary.preprocessed.fixedSteps c) j n hk
  · have hdc' : d < c := by
      change d.val < c.val
      omega
    have hnot : b.1 ∉ data.orderedCluster c := by
      intro hc
      exact Finset.disjoint_left.mp
        (data.orderedCluster_disjoint (ne_of_lt hdc')) hbd hc
    rw [boundary.individualHermiteBoundaryParameter_inactiveCenter D
      representative offset radius Fsys x w₀ hw₀ data hA c _ b.1 hnot n,
      boundary.individualHermiteBoundaryParameter_inactiveCenter D
        representative offset radius Fsys x w₀ hw₀ data hA c _ b.1 hnot n]

/-- The bounded parameter coordinate is independent of the individual prefix
boundary. -/
theorem individualHermiteBoundaryParameter_box_succ_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) (n : ℕ) :
    (boundary.individualHermiteBoundaryParameter D representative offset radius
        Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ n).2 =
      (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc n).2 := by
  rfl

/-- An untouched block's Hermite coefficient is unchanged by a decrement in
a different block: its center and the common bounded parameter are unchanged. -/
theorem individualHermiteBoundarySymbolValue_derivative_succ_eq_of_ne
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (b : data.OrderedClusterPrefixBlock (c.val + 1))
    (hb : b ≠ data.orderedClusterIndividualSelectedBlock c
      (boundary.preprocessed.fixedSteps c) j)
    (r : Fin (paperRankHermiteHigherCount boundary.S + 1)) :
    boundary.individualHermiteBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ
        (Sum.inr (Sum.inl ⟨b, r⟩)) =
      boundary.individualHermiteBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc
        (Sum.inr (Sum.inl ⟨b, r⟩)) := by
  funext n
  rw [boundary.individualHermiteBoundarySymbolValue_positiveDerivative D
    representative offset radius Fsys x w₀ hw₀ data hA,
    boundary.individualHermiteBoundarySymbolValue_positiveDerivative D
      representative offset radius Fsys x w₀ hw₀ data hA]
  have he : (paperRankAllCoefficientBlockEquiv m).symm (Sum.inr b.1) = b.1 := by
    apply (paperRankAllCoefficientBlockEquiv m).injective
    simp
  simp only [paperRankHermiteCoefficientValue, he]
  rw [boundary.individualHermiteBoundaryParameter_center_succ_eq_of_ne D
      representative offset radius Fsys x w₀ hw₀ data hA c j b hb n,
    boundary.individualHermiteBoundaryParameter_box_succ_eq D representative
      offset radius Fsys x w₀ hw₀ data hA c j n]

/-- A distinct block's representative coordinate is unchanged at one mixed
successor boundary. -/
theorem individualMixedBoundarySymbolValue_free_succ_eq_of_ne
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (b : data.OrderedClusterPrefixBlock (c.val + 1))
    (hb : b ≠ data.orderedClusterIndividualSelectedBlock c
      (boundary.preprocessed.fixedSteps c) j) :
    boundary.individualMixedBoundarySymbolValue D representative offset radius
        Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ (Sum.inl b) =
      boundary.individualMixedBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc (Sum.inl b) := by
  funext n
  exact boundary.individualHermiteBoundaryParameter_center_succ_eq_of_ne D
    representative offset radius Fsys x w₀ hw₀ data hA c j b hb n

/-- A distinct block's mixed positive derivative coordinate is unchanged at
one successor boundary. -/
theorem individualMixedBoundarySymbolValue_derivative_succ_eq_of_ne
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (b : data.OrderedClusterPrefixBlock (c.val + 1))
    (hb : b ≠ data.orderedClusterIndividualSelectedBlock c
      (boundary.preprocessed.fixedSteps c) j)
    (r : Fin (paperRankHermiteHigherCount boundary.S + 1)) :
    boundary.individualMixedBoundarySymbolValue D representative offset radius
        Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ
        (Sum.inr (Sum.inl ⟨b, r⟩)) =
      boundary.individualMixedBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc
        (Sum.inr (Sum.inl ⟨b, r⟩)) := by
  funext n
  change (if boundary.individualMixedBoundaryProcessed D representative offset
        radius Fsys x w₀ hw₀ data c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ b then
      iteratedDeriv (r.val + 1) A
        ((boundary.individualHermiteBoundaryParameter D representative offset
          radius Fsys x w₀ hw₀ data hA c
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j).succ n).1 b.1)
    else boundary.individualHermiteBoundarySymbolValue D representative offset
      radius Fsys x w₀ hw₀ data hA c
      (data.orderedClusterIndividualStepIndexEquiv c
        (boundary.preprocessed.fixedSteps c) j).succ
      (Sum.inr (Sum.inl ⟨b, r⟩)) n) = _
  have hprocessedIff :=
    boundary.individualMixedBoundaryProcessed_succ_iff_of_ne D representative
      offset radius Fsys x w₀ hw₀ data c j b hb
  by_cases hprocessed : boundary.individualMixedBoundaryProcessed D
      representative offset radius Fsys x w₀ hw₀ data c
      (data.orderedClusterIndividualStepIndexEquiv c
        (boundary.preprocessed.fixedSteps c) j).castSucc b
  · have hprocessedSucc := hprocessedIff.mpr hprocessed
    simp only [if_pos hprocessed, if_pos hprocessedSucc]
    rw [boundary.individualHermiteBoundaryParameter_center_succ_eq_of_ne D
      representative offset radius Fsys x w₀ hw₀ data hA c j b hb n]
    simp only [individualMixedBoundarySymbolValue, if_pos hprocessed]
  · have hprocessedSucc : ¬ boundary.individualMixedBoundaryProcessed D
        representative offset radius Fsys x w₀ hw₀ data c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ b :=
      fun hs ↦ hprocessed (hprocessedIff.mp hs)
    simp only [if_neg hprocessed, if_neg hprocessedSucc]
    rw [individualMixedBoundarySymbolValue, if_neg hprocessed]
    exact congrFun
      (boundary.individualHermiteBoundarySymbolValue_derivative_succ_eq_of_ne D
        representative offset radius Fsys x w₀ hw₀ data hA c j b hb r) n

/-- A distinct block's exact time coordinate is unchanged at one successor
boundary. -/
theorem individualMixedBoundarySymbolValue_time_succ_eq_of_ne
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (b : data.OrderedClusterPrefixBlock (c.val + 1))
    (hb : b ≠ data.orderedClusterIndividualSelectedBlock c
      (boundary.preprocessed.fixedSteps c) j) :
    boundary.individualMixedBoundarySymbolValue D representative offset radius
        Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ
        (Sum.inr (Sum.inr b)) =
      boundary.individualMixedBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc
        (Sum.inr (Sum.inr b)) := by
  funext n
  change A ((boundary.individualHermiteBoundaryParameter D representative offset
    radius Fsys x w₀ hw₀ data hA c
    (data.orderedClusterIndividualStepIndexEquiv c
      (boundary.preprocessed.fixedSteps c) j).succ n).1 b.1) =
    A ((boundary.individualHermiteBoundaryParameter D representative offset
      radius Fsys x w₀ hw₀ data hA c
      (data.orderedClusterIndividualStepIndexEquiv c
        (boundary.preprocessed.fixedSteps c) j).castSucc n).1 b.1)
  rw [boundary.individualHermiteBoundaryParameter_center_succ_eq_of_ne D
    representative offset radius Fsys x w₀ hw₀ data hA c j b hb n]

/-- The selected predecessor center is `E` of the post-log scale used by the
mixed trace jet. -/
theorem individualMixedBoundary_selectedCenter_beforeStep
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (i : Fin 1) (n : ℕ) :
    (boundary.individualHermiteBoundaryParameter D representative offset radius
        Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc n).1
        (data.orderedClusterIndividualSelectedBlock c
          (boundary.preprocessed.fixedSteps c) j).1 =
      E (data.orderedClusterIndividualPostLogScale c A
        (fun q ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA q) c)
        (boundary.preprocessed.fixedSteps c) j i n) := by
  rw [boundary.individualHermiteBoundaryParameter_beforeStep D representative
    offset radius Fsys x w₀ hw₀ data hA c j n]
  change
    (boundary.individualPreLogParameter D representative offset radius Fsys x
      w₀ hw₀ data c j
      (n + boundary.individualQuantitativeTail D representative offset radius
        Fsys x w₀ hw₀ data hA)).1
        (boundary.individualSelectedBlock D representative offset radius Fsys x
          w₀ hw₀ data c j i) = _
  have hcenter := boundary.individualPreLogParameter_selected_center D
    representative offset radius Fsys x w₀ hw₀ data hA c j i
      (n + boundary.individualQuantitativeTail D representative offset radius
        Fsys x w₀ hw₀ data hA)
  exact hcenter.trans (congrArg E
    (boundary.individualQuantitativePostLogScale_eq D representative offset
      radius Fsys x w₀ hw₀ data hA c j i n).symm)

/-- The predecessor mixed boundary restricts to the exact source assignment
for the first/repeated jet chosen at that step. -/
theorem selectedBlockActiveAssignment_individualMixedBoundary_beforeStep
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    selectedBlockActiveAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c
          (boundary.preprocessed.fixedSteps c) j)
        (boundary.individualMixedBoundarySymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c
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
        (boundary.individualMixedTraceJets D representative offset radius Fsys
          x w₀ hw₀ data hA c j) := by
  let q := (data.orderedClusterIndividualStepIndexEquiv c
    (boundary.preprocessed.fixedSteps c) j).castSucc
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  funext z n
  rcases z with i | z
  · rw [boundary.selectedBlockActiveAssignment_individualMixedBoundary_free D
      representative offset radius Fsys x w₀ hw₀ data hA c q selected i n,
      individualCentralPreLogActiveAssignment_q]
    exact boundary.individualMixedBoundary_selectedCenter_beforeStep D
      representative offset radius Fsys x w₀ hw₀ data hA c j i n
  · rcases z with ir | i
    · rcases ir with ⟨i, r⟩
      rw [boundary.selectedBlockActiveAssignment_individualMixedBoundary_derivative
        D representative offset radius Fsys x w₀ hw₀ data hA c q selected i r n]
      change (if boundary.individualMixedStepIsRepeated D representative offset
          radius Fsys x w₀ hw₀ data c j then
            iteratedDeriv (r.val + 1) A
              ((boundary.individualHermiteBoundaryParameter D representative
                offset radius Fsys x w₀ hw₀ data hA c q n).1 selected.1)
          else
            boundary.individualHermiteBoundarySymbolValue D representative offset
              radius Fsys x w₀ hw₀ data hA c q
              (Sum.inr (Sum.inl ⟨selected, r⟩)) n) =
        (boundary.individualMixedTraceJets D representative offset radius Fsys x
          w₀ hw₀ data hA c j n i).sourceJet r
      dsimp only [q, selected]
      by_cases hrepeat : boundary.individualMixedStepIsRepeated D representative
          offset radius Fsys x w₀ hw₀ data c j
      · rw [if_pos hrepeat]
        rw [boundary.individualMixedBoundary_selectedCenter_beforeStep D
          representative offset radius Fsys x w₀ hw₀ data hA c j i n]
        unfold individualMixedTraceJets
        rw [boundary.individualMixedRealJetSequence_eq_exact D representative
          offset radius Fsys x w₀ hw₀ data hA c j hrepeat n i]
        rw [castRealCentralJetSubstitutionData_sourceJet]
        rw [boundary.individualQuantitativePostLogScale_eq D representative
          offset radius Fsys x w₀ hw₀ data hA c j i n]
        simpa only [Fin.coe_cast] using
          (hA.realDerivativeJetSubstitutionData_sourceJet
            (u := boundary.individualPostLogScale D representative offset radius
              Fsys x w₀ hw₀ data c j i
              (n + boundary.individualQuantitativeTail D representative offset
                radius Fsys x w₀ hw₀ data hA))
            (hA.inverse_pos _)
            (paperRankHermitePositiveDerivativeCount boundary.S)
            (Fin.cast
              (boundary.individualQuantitativeStepDerivativeCount_apply D
                representative offset radius Fsys x w₀ hw₀ data c j i) r)).symm
      · rw [if_neg hrepeat]
        unfold individualMixedTraceJets
        rw [boundary.individualMixedRealJetSequence_eq_hermite D representative
          offset radius Fsys x w₀ hw₀ data hA c j hrepeat n i]
        rw [castRealCentralJetSubstitutionData_sourceJet]
        let hd := boundary.individualQuantitativeStepDerivativeCount_apply D
          representative offset radius Fsys x w₀ hw₀ data c j i
        let r' : Fin (paperRankHermitePositiveDerivativeCount boundary.S) :=
          Fin.cast hd r
        have hsource :=
          boundary.individualQuantitativeRealJetSequence_sourceJet_eq_coefficientValue
            D representative offset radius Fsys x w₀ hw₀ data hA c j n i r'
        have hselected :
            boundary.individualSelectedBlock D representative offset radius Fsys
                x w₀ hw₀ data c j i =
              (data.orderedClusterIndividualSelectedBlock c
                (boundary.preprocessed.fixedSteps c) j).1 := by
          rfl
        have hindex :
            paperRankHermitePositiveCoefficientIndex boundary.S
                (Sum.inr (boundary.individualSelectedBlock D representative
                  offset radius Fsys x w₀ hw₀ data c j i) :
                  Fin 0 ⊕ Fin m) r' =
              (finCongr (paperRankHermiteHigherCount_add_one boundary.S) r).succ := by
          apply Fin.ext
          rfl
        rw [boundary.individualHermiteBoundarySymbolValue_positiveDerivative D
          representative offset radius Fsys x w₀ hw₀ data hA c
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j).castSucc
          (data.orderedClusterIndividualSelectedBlock c
            (boundary.preprocessed.fixedSteps c) j) r n]
        rw [boundary.individualHermiteBoundaryParameter_beforeStep D
          representative offset radius Fsys x w₀ hw₀ data hA c j n]
        rw [← hselected, ← hindex]
        simpa only [castRealCentralJetSubstitutionData, r', hd] using hsource.symm
    · rw [boundary.selectedBlockActiveAssignment_individualMixedBoundary_time D
        representative offset radius Fsys x w₀ hw₀ data hA c q selected i n]
      change A ((boundary.individualHermiteBoundaryParameter D representative
          offset radius Fsys x w₀ hw₀ data hA c q n).1 selected.1) =
        A (E (data.orderedClusterIndividualPostLogScale c A
          (fun k ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA k) c)
          (boundary.preprocessed.fixedSteps c) j i n))
      rw [boundary.individualMixedBoundary_selectedCenter_beforeStep D
        representative offset radius Fsys x w₀ hw₀ data hA c j i n]

/-- At the successor boundary the selected block is exactly the central
post-log assignment.  In particular, a repeated selection remains exact. -/
theorem selectedBlockActiveAssignment_individualMixedBoundary_afterStep
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    selectedBlockActiveAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c
          (boundary.preprocessed.fixedSteps c) j)
        (boundary.individualMixedBoundarySymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j).succ) =
      individualCentralPostLogActiveAssignment A
        (data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA q) c)
          (boundary.preprocessed.fixedSteps c) j)
        (data.orderedClusterQuantitativeStepDerivativeCount
          (paperRankHermiteHigherCount boundary.S) c
          (boundary.preprocessed.fixedSteps c) j) := by
  let q := (data.orderedClusterIndividualStepIndexEquiv c
    (boundary.preprocessed.fixedSteps c) j).succ
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  have hprocessed : boundary.individualMixedBoundaryProcessed D representative
      offset radius Fsys x w₀ hw₀ data c q selected :=
    boundary.individualMixedBoundaryProcessed_succ_selected D representative
      offset radius Fsys x w₀ hw₀ data c j
  funext z n
  rcases z with i | z
  · rw [boundary.selectedBlockActiveAssignment_individualMixedBoundary_free D
      representative offset radius Fsys x w₀ hw₀ data hA c q selected i n,
      individualCentralPostLogActiveAssignment_q]
    exact boundary.individualMixedBoundary_selectedCenter_afterStep D
      representative offset radius Fsys x w₀ hw₀ data hA c j i n
  · rcases z with ir | i
    · rcases ir with ⟨i, r⟩
      rw [boundary.selectedBlockActiveAssignment_individualMixedBoundary_derivative
        D representative offset radius Fsys x w₀ hw₀ data hA c q selected i r n,
        if_pos hprocessed]
      change iteratedDeriv (r.val + 1) A
          ((boundary.individualHermiteBoundaryParameter D representative offset
            radius Fsys x w₀ hw₀ data hA c q n).1 selected.1) =
        iteratedDeriv (r.val + 1) A
          (data.orderedClusterIndividualPostLogScale c A
            (fun k ↦ data.orderedClusterRawTime
              (boundary.individualQuantitativeSubsequence D representative offset
                radius Fsys x w₀ hw₀ data hA k) c)
            (boundary.preprocessed.fixedSteps c) j i n)
      rw [boundary.individualMixedBoundary_selectedCenter_afterStep D
        representative offset radius Fsys x w₀ hw₀ data hA c j i n]
    · rw [boundary.selectedBlockActiveAssignment_individualMixedBoundary_time D
        representative offset radius Fsys x w₀ hw₀ data hA c q selected i n]
      change A ((boundary.individualHermiteBoundaryParameter D representative
          offset radius Fsys x w₀ hw₀ data hA c q n).1 selected.1) =
        A (data.orderedClusterIndividualPostLogScale c A
          (fun k ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA k) c)
          (boundary.preprocessed.fixedSteps c) j i n)
      rw [boundary.individualMixedBoundary_selectedCenter_afterStep D
        representative offset radius Fsys x w₀ hw₀ data hA c j i n]

/-- The mixed jet has the required superpolynomial error: it is the existing
Hermite estimate at a first occurrence and identically zero thereafter. -/
theorem individualMixedRealJetSequence_error_superpolynomialDecay
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) (i : Fin 1)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    Asymptotics.SuperpolynomialDecay atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (fun n ↦ (boundary.individualMixedRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c j n i).error r) := by
  by_cases hrepeat : boundary.individualMixedStepIsRepeated D representative
      offset radius Fsys x w₀ hw₀ data c j
  · have hzero : (fun n ↦
        (boundary.individualMixedRealJetSequence D representative offset radius
          Fsys x w₀ hw₀ data hA c j n i).error r) = fun _ ↦ 0 := by
      funext n
      rw [boundary.individualMixedRealJetSequence_eq_exact D representative
        offset radius Fsys x w₀ hw₀ data hA c j hrepeat n i]
      exact hA.realDerivativeJetSubstitutionData_error
        (hA.inverse_pos _) _ r
    rw [hzero]
    exact Asymptotics.superpolynomialDecay_zero atTop _
  · apply (boundary.individualQuantitativeRealJetSequence_error_superpolynomialDecay
        D representative offset radius Fsys x w₀ hw₀ data separation hA c j i r).congr
    intro n
    rw [boundary.individualMixedRealJetSequence_eq_hermite D representative
      offset radius Fsys x w₀ hw₀ data hA c j hrepeat n i]

/-- The same estimate with the derivative-count expression used literally by
the displayed individual trace. -/
theorem individualMixedTraceJets_error_superpolynomialDecay
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) (i : Fin 1)
    (r : Fin (data.orderedClusterQuantitativeStepDerivativeCount
      (paperRankHermiteHigherCount boundary.S) c
      (boundary.preprocessed.fixedSteps c) j i)) :
    Asymptotics.SuperpolynomialDecay atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (fun n ↦ (boundary.individualMixedTraceJets D representative offset
        radius Fsys x w₀ hw₀ data hA c j n i).error r) := by
  let hd := boundary.individualQuantitativeStepDerivativeCount_apply D
    representative offset radius Fsys x w₀ hw₀ data c j i
  let r' : Fin (paperRankHermitePositiveDerivativeCount boundary.S) :=
    Fin.cast hd r
  have herr :=
    boundary.individualMixedRealJetSequence_error_superpolynomialDecay D
      representative offset radius Fsys x w₀ hw₀ data separation hA c j i r'
  apply herr.congr
  intro n
  simp only [individualMixedTraceJets,
    castRealCentralJetSubstitutionData_error]
  congr

/-! ## Polynomial bounds and finite analytic boundary data -/

/-- Abel time at a center tending to infinity is polynomially bounded by any
eventually larger scale.  The logarithmic upper bound for an Abel function is
the only growth input. -/
theorem abelValue_hasPolynomialUpperBound_of_center_le_scale
    (hA : IsAbel A) (center scale : ℕ → ℝ)
    (hcenter : Tendsto center atTop atTop)
    (hle : ∀ᶠ n in atTop, center n ≤ scale n)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n) :
    HasPolynomialUpperBound atTop scale (fun n ↦ A (center n)) := by
  obtain ⟨R, C, hR, hupper⟩ := hA.exists_log_upper_bound
  refine ⟨|C| + 1, by positivity, 1, ?_⟩
  have hcenterR : ∀ᶠ n in atTop, R ≤ center n :=
    hcenter.eventually (eventually_ge_atTop R)
  have hcenterOne : ∀ᶠ n in atTop, 1 ≤ center n :=
    hcenter.eventually (eventually_ge_atTop 1)
  filter_upwards [hcenterR, hcenterOne, hle, hscale] with n hnR hnOne hnle hnscale
  rw [abs_of_nonneg (hA.nonneg_of_one_le hnOne), pow_one]
  calc
    A (center n) ≤ Real.log (center n) + C := hupper _ hnR
    _ ≤ center n + |C| := by
      exact add_le_add (Real.log_le_self (by linarith)) (le_abs_self C)
    _ ≤ (|C| + 1) * scale n := by
      nlinarith [abs_nonneg C]

/-- Every coordinate of the recursively mixed boundary has a polynomial upper
bound at its exact boundary scale. -/
theorem individualMixedBoundarySymbolValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (z : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))) :
    HasPolynomialUpperBound atTop
      (boundary.individualNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data hA c q)
      (boundary.individualMixedBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c q z) := by
  rcases z with b | z
  · exact boundary.individualHermiteBoundarySymbolValue_free_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c q b
  · rcases z with br | b
    · rcases br with ⟨b, r⟩
      by_cases hprocessed : boundary.individualMixedBoundaryProcessed D
          representative offset radius Fsys x w₀ hw₀ data c q b
      · have htendsto := (hA.tendsto_iteratedDeriv_atTop (r.val + 1)
          (Nat.succ_le_succ (Nat.zero_le r.val))).comp
            (boundary.individualHermiteBoundaryParameter_center_tendsto_atTop D
              representative offset radius Fsys x w₀ hw₀ data hA c q b)
        apply (HasPolynomialUpperBound.of_tendsto htendsto).congr
        intro n
        simp only [individualMixedBoundarySymbolValue, if_pos hprocessed,
          Function.comp_apply]
      · apply (boundary.individualHermiteBoundarySymbolValue_positiveDerivative_hasPolynomialUpperBound
          D representative offset radius Fsys x w₀ hw₀ data hA c q b r).congr
        intro n
        simp only [individualMixedBoundarySymbolValue, if_neg hprocessed]
    · apply (abelValue_hasPolynomialUpperBound_of_center_le_scale hA
        (fun n ↦ (boundary.individualHermiteBoundaryParameter D representative
          offset radius Fsys x w₀ hw₀ data hA c q n).1 b.1)
        (boundary.individualNumericBoundaryScale D representative offset radius
          Fsys x w₀ hw₀ data hA c q) ?_ ?_ ?_).congr
      · intro n
        rfl
      · exact boundary.individualHermiteBoundaryParameter_center_tendsto_atTop D
          representative offset radius Fsys x w₀ hw₀ data hA c q b
      · exact boundary.individualHermiteBoundaryParameter_center_le_scale D
          representative offset radius Fsys x w₀ hw₀ data hA c q b
      · exact Filter.Eventually.of_forall fun n ↦ one_le_two.trans
          (two_le_clusterBalancingPrefixScale A
            (fun k ↦ data.orderedClusterRawTime
              (boundary.individualQuantitativeSubsequence D representative offset
                radius Fsys x w₀ hw₀ data hA k) c)
            (boundary.preprocessed.fixedSteps c) q.val n)

/-- Canonical finite analytic boundary data evaluated at the recursively mixed
state. -/
noncomputable def individualMixedAnalyticBoundaryData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    IndividualCentralDisplayedTraceData.AnalyticBoundaryData
      (0 : RestrictedBoxSpace p)
      (boundary.individualNumericDisplayed D representative offset radius Fsys
        x w₀ hw₀ data c)
      (boundary.individualNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data hA c) :=
  boundary.individualAnalyticBoundaryData D representative offset radius Fsys
    x w₀ hw₀ data hA c
    (boundary.individualMixedBoundarySymbolValue D representative offset
      radius Fsys x w₀ hw₀ data hA c)
    (fun q z ↦
      boundary.individualMixedBoundarySymbolValue_hasPolynomialUpperBound D
        representative offset radius Fsys x w₀ hw₀ data hA c q z)

/-- The finite change-of-generators boundary recursion specialized to the
recursively mixed state. -/
noncomputable def individualMixedNumericBoundaryCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    boundary.IndividualNumericBoundaryCompatibility D representative offset
      radius Fsys x w₀ hw₀ data hA c :=
  boundary.individualNumericBoundaryCompatibilityOfAnalyticChange D
    representative offset radius Fsys x w₀ hw₀ data hA c
    (boundary.individualMixedBoundarySymbolValue D representative offset
      radius Fsys x w₀ hw₀ data hA c)
    (fun q z ↦
      boundary.individualMixedBoundarySymbolValue_hasPolynomialUpperBound D
        representative offset radius Fsys x w₀ hw₀ data hA c q z)

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
