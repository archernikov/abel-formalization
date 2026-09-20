import AbelFormalization.HermiteRankTopIndividualBoundaryQuantitativeLower

/-!
# Canonical compatibility at the highest individual boundary

At boundary zero of the highest ordered cluster, no individual decrement has
yet been performed.  Its recursively mixed assignment is therefore the
ordinary Hermite assignment.  On a common eventual tail, the active-cluster
centers are also the original selected centers: the zero-length balancing
prefix leaves every Abel time unchanged, and `inverse A (A x) = x` once the
selected centers are positive.

This identifies the highest individual boundary with the literal selected
padded top-prefix family.  Equality of the independently chosen analytic
polynomial representatives follows from equality of their analytic germs.
Consequently the compatibility record left abstract by
`HermiteRankTopIndividualBoundaryQuantitativeLower` has a canonical
constructor and carries no additional analytic hypothesis.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter Set
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

noncomputable local instance topIndividualCompatibilityBlockDecidableEq
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-! ## The zero-prefix parameter -/

/-- Removing no balancing steps recovers the selected translated parameter,
provided its finitely many representative coordinates are positive. -/
theorem clusterPrefixParameter_zero_eq_selectedTranslated_of_pos
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (n : ℕ)
    (hpos : ∀ i : Fin m, 0 <
      (boundary.selectedTranslatedParameter D representative offset radius
        Fsys x w₀ hw₀ data n).1 i) :
    boundary.clusterPrefixParameter D representative offset radius Fsys x w₀
        hw₀ data c 0 n =
      boundary.selectedTranslatedParameter D representative offset radius Fsys
        x w₀ hw₀ data n := by
  classical
  apply Prod.ext
  · funext block
    by_cases hblock : block ∈ data.orderedCluster c
    · simp only [clusterPrefixParameter, hblock, dite_true, List.take_zero,
        clusterShiftedTimes_nil]
      have hraw :
          boundary.selectedClusterRawTime D representative offset radius Fsys x
              w₀ hw₀ data c n
              (balancingIndexOfMem x data c block hblock) =
            A ((boundary.selectedTranslatedParameter D representative offset
              radius Fsys x w₀ hw₀ data n).1 block) := by
        unfold selectedClusterRawTime
          RepresentativeClusterSubsequence.orderedClusterRawTime
        rw [orderedClusterEnumeration_balancingIndexOfMem x data c block hblock]
        rfl
      rw [hraw, hA.inverse_apply (hpos block)]
    · simp only [clusterPrefixParameter, hblock, dite_false]
  · rfl

/-- The fixed common-tail index used by the top bridge is cofinal. -/
theorem topIndividualCommonSelectedIndex_tendsto_atTop
    (hA : IsAbel A) :
    Tendsto
      (boundary.topIndividualCommonSelectedIndex D representative offset radius
        Fsys x w₀ hw₀ data hA) atTop atTop := by
  let N := boundary.topIndividualCommonTail D representative offset radius Fsys
    x w₀ hw₀ data hA
  have h := tendsto_add_atTop_nat N
  apply h.congr'
  exact Filter.Eventually.of_forall fun n ↦
    (boundary.topIndividualCommonSelectedIndex_eq_add_tail D representative
      offset radius Fsys x w₀ hw₀ data hA n).symm

/-- At boundary zero, the highest individual parameter is eventually the
selected translated paper parameter at the same common-tail index. -/
theorem individualHermiteBoundaryParameter_zero_on_commonTail_eventuallyEq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ∀ᶠ n in atTop,
      boundary.individualHermiteBoundaryParameter D representative offset
          radius Fsys x w₀ hw₀ data hA c 0
          (individualSimultaneousTailShift D representative offset radius Fsys
            x w₀ hw₀ data boundary hA n) =
        boundary.selectedTranslatedParameter D representative offset radius
          Fsys x w₀ hw₀ data
          (boundary.topIndividualCommonSelectedIndex D representative offset
            radius Fsys x w₀ hw₀ data hA n) := by
  have hindex := boundary.topIndividualCommonSelectedIndex_tendsto_atTop D
    representative offset radius Fsys x w₀ hw₀ data hA
  have hpos : ∀ᶠ n in atTop, ∀ i : Fin m, 0 <
      (boundary.selectedTranslatedParameter D representative offset radius Fsys
        x w₀ hw₀ data
        (boundary.topIndividualCommonSelectedIndex D representative offset
          radius Fsys x w₀ hw₀ data hA n)).1 i := by
    apply Filter.eventually_all.mpr
    intro i
    have hi := (boundary.selected_representative_tendsto i).comp hindex
    simpa only [selectedTranslatedParameter_representative, Function.comp_apply,
      selectedIndex] using
      hi.eventually (eventually_gt_atTop 0)
  filter_upwards [hpos] with n hn
  change boundary.clusterPrefixParameter D representative offset radius Fsys x
      w₀ hw₀ data c 0
        (boundary.topIndividualCommonSelectedIndex D representative offset
          radius Fsys x w₀ hw₀ data hA n) = _
  exact boundary.clusterPrefixParameter_zero_eq_selectedTranslated_of_pos D
    representative offset radius Fsys x w₀ hw₀ data hA c _ hn

/-- The analytic coefficient parameter in the top bridge is exactly the box
coordinate of the selected top-prefix parameter at the common-tail index. -/
theorem topIndividualBoundaryParameterOnCommonTail_eq_selectedTopPrefixBox
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (n : ℕ) :
    boundary.topIndividualBoundaryParameterOnCommonTail D representative offset
        radius Fsys x w₀ hw₀ data hA c n =
      boundary.selectedTopPrefixBoxParameter D representative offset radius Fsys
        x w₀ hw₀ data
        (boundary.topIndividualCommonSelectedIndex D representative offset
          radius Fsys x w₀ hw₀ data hA n) := by
  rfl

/-! ## Boundary-zero symbols -/

/-- At boundary zero, no block has yet been processed by the individual
decrement trace. -/
@[simp]
theorem individualMixedBoundaryProcessed_zero_false
    (c : Fin data.orderedClusterCount)
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) :
    ¬ boundary.individualMixedBoundaryProcessed D representative offset radius
      Fsys x w₀ hw₀ data c 0 b := by
  simp [individualMixedBoundaryProcessed]

/-- Once a boundary center is beyond the common Hermite threshold, its
coefficient-zero coordinate is exactly the Abel time at that center. -/
theorem individualHermiteBoundarySymbolValue_time_eq_exact_of_threshold
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) (n : ℕ)
    (hcenter : boundary.Xstrip + boundary.B + 3 <
      (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 b.1) :
    boundary.individualHermiteBoundarySymbolValue D representative offset radius
        Fsys x w₀ hw₀ data hA c q (Sum.inr (Sum.inr b)) n =
      A ((boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 b.1) := by
  let sw := boundary.individualHermiteBoundaryParameter D representative offset
    radius Fsys x w₀ hw₀ data hA c q n
  let nodes : Option (Fin boundary.S.card) → ℂ := fun node ↦
    (paperRankHermiteNodes (D.translateToZero w₀) representative
      (restrictedOffsetTranslateToZero w₀ offset) boundary.S b.1 sw.2 node : ℂ)
  have hoffset : ∀ k : Fin boundary.S.card,
      |(restrictedOffsetTranslateToZero w₀ offset
          (restrictedJetEnumeration boundary.S k).1 :
          RestrictedBoxSpace p → ℝ) sw.2| ≤ boundary.B := by
    intro k
    dsimp only [sw]
    rw [boundary.individualHermiteBoundaryParameter_box D representative offset
      radius Fsys x w₀ hw₀ data]
    exact boundary.selectedTranslatedOffset_bound D representative offset radius
      Fsys x w₀ hw₀ data
      (n + boundary.individualQuantitativeTail D representative offset radius
        Fsys x w₀ hw₀ data hA) k
  have hnodes : nodes ∈ hermiteNodeNeighborhood boundary.B := by
    exact paperRankHermiteNodes_mem_hermiteNodeNeighborhood
      (D.translateToZero w₀) representative
      (restrictedOffsetTranslateToZero w₀ offset) boundary.S
      boundary.hermiteFamily boundary.B_pos sw.2 hoffset b.1
  have hconstant := boundary.hermiteFamily.constant_coefficient (sw.1 b.1)
    hcenter nodes hnodes (none : Option (Fin boundary.S.card))
    (by simp [nodes, paperRankHermiteNodes])
    (by simp [paperRankHermiteNodeMultiplicity])
  rw [boundary.individualHermiteBoundarySymbolValue_time D representative
    offset radius Fsys x w₀ hw₀ data]
  change
    (abelHermiteCoeff (fun _ ↦ boundary.Fbranch) boundary.B
      (paperRankHermiteNodeMultiplicity boundary.S) (sw.1 b.1) nodes 0).re =
        A (sw.1 b.1)
  rw [hconstant]
  simp

/-- Before any decrement, the recursively mixed assignment eventually agrees
with the ordinary Hermite prefix assignment in every coordinate. -/
theorem individualMixedBoundarySymbolValue_zero_eventuallyEq_hermite
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ∀ᶠ n in atTop, ∀ z,
      boundary.individualMixedBoundarySymbolValue D representative offset radius
          Fsys x w₀ hw₀ data hA c 0 z n =
        boundary.individualHermiteBoundarySymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c 0 z n := by
  apply Filter.eventually_all.mpr
  intro z
  rcases z with b | z
  · exact Filter.Eventually.of_forall fun _ ↦ rfl
  · rcases z with br | b
    · rcases br with ⟨b, r⟩
      apply Filter.Eventually.of_forall
      intro n
      simp only [individualMixedBoundarySymbolValue,
        boundary.individualMixedBoundaryProcessed_zero_false D representative
          offset radius Fsys x w₀ hw₀ data c b, if_false]
    · have hcenter :=
        (boundary.individualHermiteBoundaryParameter_center_tendsto_atTop D
          representative offset radius Fsys x w₀ hw₀ data hA c 0 b).eventually
          (eventually_gt_atTop (boundary.Xstrip + boundary.B + 3))
      filter_upwards [hcenter] with n hn
      rw [boundary.individualMixedBoundarySymbolValue_time D representative
        offset radius Fsys x w₀ hw₀ data]
      exact (boundary.individualHermiteBoundarySymbolValue_time_eq_exact_of_threshold
        D representative offset radius Fsys x w₀ hw₀ data hA c 0 b n hn).symm

/-! ## The literal top-prefix assignment -/

/-- A cast-free description of the top-prefix symbol equivalence.  The
original definition first uses the `higher + 1` flat Hermite count and then
transports its domain along `paperRankHermiteHigherCount_add_one`.  Choosing
the equal positive-derivative count from the start moves that transport into
the derivative-coordinate equivalence, where its action is explicit. -/
theorem paperRankHermiteTopPrefixSymbolEquiv_eq_direct :
    data.paperRankHermiteTopPrefixSymbolEquiv boundary.S =
      (paperRankRetainedFlatHermiteEquiv m
        (paperRankHermitePositiveDerivativeCount boundary.S)).trans
        (clusterOperationSymbolEquiv
          data.orderedClusterPrefixTopEquiv
          (fun _ : Fin m =>
            paperRankHermitePositiveDerivativeCount boundary.S)
          (data.orderedClusterPrefixConstantDerivativeCount
            (paperRankHermiteHigherCount boundary.S + 1)
            data.orderedClusterCount)
          (fun _ => (paperRankHermiteHigherCount_add_one boundary.S).symm)) := by
  rfl

/-- The direct top-prefix symbol equivalence sends a free coordinate to the
same representative block in the full ordered prefix. -/
@[simp]
theorem paperRankHermiteTopPrefixSymbolEquiv_apply_free
    (i : Fin m) :
    data.paperRankHermiteTopPrefixSymbolEquiv boundary.S (Sum.inl i) =
      Sum.inl (data.orderedClusterPrefixTopEquiv i) := by
  rw [paperRankHermiteTopPrefixSymbolEquiv_eq_direct,
    Equiv.trans_apply, paperRankRetainedFlatHermiteEquiv_apply_free,
    clusterOperationSymbolEquiv_apply_q]

/-- A positive-derivative coordinate in the full prefix is the image of its
flat retained coordinate under the top-prefix equivalence. -/
theorem paperRankHermiteTopPrefixSymbolEquiv_apply_positiveDerivative
    (b : data.OrderedClusterPrefixBlock data.orderedClusterCount)
    (r : Fin (paperRankHermiteHigherCount boundary.S + 1)) :
    data.paperRankHermiteTopPrefixSymbolEquiv boundary.S
        ((paperRankRetainedFlatHermiteEquiv m
          (paperRankHermitePositiveDerivativeCount boundary.S)).symm
          (Sum.inr (Sum.inl
            ⟨b.1, finCongr
              (paperRankHermiteHigherCount_add_one boundary.S) r⟩))) =
      Sum.inr (Sum.inl ⟨b, r⟩) := by
  rw [paperRankHermiteTopPrefixSymbolEquiv_eq_direct,
    Equiv.trans_apply, Equiv.apply_symm_apply,
    clusterOperationSymbolEquiv_apply_derivative]
  apply congrArg Sum.inr
  apply congrArg Sum.inl
  apply Sigma.ext
  · exact Subtype.ext rfl
  · apply (Fin.heq_ext_iff (by simp)).2
    rfl

/-- A retained time coordinate in the full prefix is the image of its flat
retained coordinate under the top-prefix equivalence. -/
theorem paperRankHermiteTopPrefixSymbolEquiv_apply_time
    (b : data.OrderedClusterPrefixBlock data.orderedClusterCount) :
    data.paperRankHermiteTopPrefixSymbolEquiv boundary.S
        ((paperRankRetainedFlatHermiteEquiv m
          (paperRankHermitePositiveDerivativeCount boundary.S)).symm
          (Sum.inr (Sum.inr b.1))) =
      Sum.inr (Sum.inr b) := by
  rw [paperRankHermiteTopPrefixSymbolEquiv_eq_direct,
    Equiv.trans_apply, Equiv.apply_symm_apply,
    clusterOperationSymbolEquiv_apply_time]
  exact congrArg (fun z => Sum.inr (Sum.inr z)) (Subtype.ext rfl)

/-- Prefix Hermite assignments transport definitionally along equality of the
natural prefix index.  Keeping `k` independent makes the equality eliminable
without transporting a `Fin orderedClusterCount`. -/
theorem paperRankHermitePrefixValue_transport_to_top
    (k : ℕ) (hk : k = data.orderedClusterCount)
    (sw : PaperRankParameterSpace m p) :
    RepresentativeClusterSubsequence.paperRankHermitePrefixValue data
        (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
        boundary.Fbranch sw k =
      hk.symm ▸
        RepresentativeClusterSubsequence.paperRankHermitePrefixValue data
          (D.translateToZero w₀) representative
          (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
          boundary.Fbranch sw data.orderedClusterCount := by
  subst k
  rfl

/-- The arbitrary-prefix Hermite assignment at the full prefix is the same
assignment as the retained-variable top-prefix transport. -/
theorem paperRankHermitePrefixValue_top_eq_topPrefixValue
    (sw : PaperRankParameterSpace m p) :
    RepresentativeClusterSubsequence.paperRankHermitePrefixValue data
        (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
        boundary.Fbranch sw data.orderedClusterCount =
      RepresentativeClusterSubsequence.paperRankHermiteTopPrefixValue data
        (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
        boundary.Fbranch sw := by
  funext z
  rcases z with b | z
  · rw [RepresentativeClusterSubsequence.paperRankHermitePrefixValue_free]
    have h := RepresentativeClusterSubsequence.paperRankHermiteTopPrefixValue_free
      data (D.translateToZero w₀) representative
      (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
      boundary.Fbranch sw b.1
    rw [paperRankHermiteTopPrefixSymbolEquiv_apply_free] at h
    have hb : data.orderedClusterPrefixTopEquiv b.1 = b := Subtype.ext rfl
    rw [hb] at h
    exact h.symm
  · rcases z with br | b
    · rcases br with ⟨b, r⟩
      rw [RepresentativeClusterSubsequence.paperRankHermitePrefixValue_positiveDerivative]
      have h :=
        RepresentativeClusterSubsequence.paperRankHermiteTopPrefixValue_positiveDerivative
          data (D.translateToZero w₀) representative
          (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
          boundary.Fbranch sw b.1
          (finCongr (paperRankHermiteHigherCount_add_one boundary.S) r)
      rw [paperRankHermiteTopPrefixSymbolEquiv_apply_positiveDerivative] at h
      simpa only using h.symm
    · rw [RepresentativeClusterSubsequence.paperRankHermitePrefixValue_time]
      have h := RepresentativeClusterSubsequence.paperRankHermiteTopPrefixValue_time
        data (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
        boundary.Fbranch sw b.1
      rw [paperRankHermiteTopPrefixSymbolEquiv_apply_time] at h
      simpa only using h.symm

/-- The selected retained assignment is exactly the full Hermite retained
assignment at `selectedTranslatedParameter`. -/
theorem selectedTopPrefixRetainedAssignment_eq_fullHermite
    (n : ℕ) :
    boundary.selectedTopPrefixRetainedAssignment D representative offset radius
        Fsys x w₀ hw₀ data n =
      paperRankFullHermiteRetainedValue (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
        boundary.Fbranch
        (boundary.selectedTranslatedParameter D representative offset radius
          Fsys x w₀ hw₀ data n) := by
  rw [selectedTopPrefixRetainedAssignment,
    paperRankRetainedArgument_fullHermiteSmoothValue]
  rfl

/-- At the full prefix, the selected prefix assignment is literally the
top-prefix assignment used by the padded vanishing theorem. -/
theorem selectedTopPrefixSequenceValue_eq_topPrefixAssignment
    (n : ℕ) :
    (fun z ↦ boundary.selectedTopPrefixSequenceValue D representative offset
      radius Fsys x w₀ hw₀ data z n) =
      data.paperRankHermiteTopPrefixAssignment boundary.S
        (boundary.selectedTopPrefixRetainedAssignment D representative offset
          radius Fsys x w₀ hw₀ data n) := by
  rw [boundary.selectedTopPrefixRetainedAssignment_eq_fullHermite D
    representative offset radius Fsys x w₀ hw₀ data n]
  change RepresentativeClusterSubsequence.paperRankHermitePrefixValue data
      (D.translateToZero w₀) representative
      (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
      boundary.Fbranch
      (boundary.selectedTranslatedParameter D representative offset radius Fsys
        x w₀ hw₀ data n) data.orderedClusterCount = _
  exact boundary.paperRankHermitePrefixValue_top_eq_topPrefixValue D
    representative offset radius Fsys x w₀ hw₀ data _

/-- Transport the selected top-prefix assignment to the definitionally equal
prefix-ring presentation of the highest `Fin` cluster. -/
def selectedTopPrefixAssignmentAtLastCluster
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) (n : ℕ) :
    ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)) → ℝ :=
  hc.symm ▸ data.paperRankHermiteTopPrefixAssignment boundary.S
    (boundary.selectedTopPrefixRetainedAssignment D representative offset radius
      Fsys x w₀ hw₀ data n)

/-- Congruence underneath the dependent transport from the literal top prefix
to an equal natural prefix index. -/
theorem orderedClusterPrefixAssignment_transport_congr
    (k : ℕ) (hk : k = data.orderedClusterCount)
    (v w : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock data.orderedClusterCount)
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1)
        data.orderedClusterCount) → ℝ)
    (hvw : v = w) :
    (hk.symm ▸ v) = (hk.symm ▸ w) := by
  subst k
  exact hvw

/-- Boundary-zero on the highest cluster eventually has exactly the selected
top-prefix symbol assignment, transported only along `c + 1 = count`. -/
theorem topIndividualBoundarySymbolValueOnCommonTail_eventuallyEq_selected
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) :
    ∀ᶠ n in atTop,
      (fun z ↦ boundary.topIndividualBoundarySymbolValueOnCommonTail D
        representative offset radius Fsys x w₀ hw₀ data hA c z n) =
      boundary.selectedTopPrefixAssignmentAtLastCluster D representative offset
        radius Fsys x w₀ hw₀ data c hc
        (boundary.topIndividualCommonSelectedIndex D representative offset
          radius Fsys x w₀ hw₀ data hA n) := by
  let shift := individualSimultaneousTailShift D representative offset radius
    Fsys x w₀ hw₀ data boundary hA
  have hshift : Tendsto shift atTop atTop :=
    boundary.topIndividualSimultaneousTailShift_tendsto_atTop D representative
      offset radius Fsys x w₀ hw₀ data hA
  have hmixed := hshift.eventually
    (boundary.individualMixedBoundarySymbolValue_zero_eventuallyEq_hermite D
      representative offset radius Fsys x w₀ hw₀ data hA c)
  have hparameter :=
    boundary.individualHermiteBoundaryParameter_zero_on_commonTail_eventuallyEq
      D representative offset radius Fsys x w₀ hw₀ data hA c
  filter_upwards [hmixed, hparameter] with n hmix hparam
  dsimp only [shift] at hmix hparam
  change (fun z ↦
      boundary.individualMixedBoundarySymbolValue D representative offset radius
        Fsys x w₀ hw₀ data hA c 0 z
          (individualSimultaneousTailShift D representative offset radius Fsys
            x w₀ hw₀ data boundary hA n)) = _
  calc
    (fun z ↦ boundary.individualMixedBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c 0 z
          (individualSimultaneousTailShift D representative offset radius Fsys
            x w₀ hw₀ data boundary hA n)) =
        (fun z ↦ boundary.individualHermiteBoundarySymbolValue D representative
          offset radius Fsys x w₀ hw₀ data hA c 0 z
            (individualSimultaneousTailShift D representative offset radius Fsys
              x w₀ hw₀ data boundary hA n)) := funext hmix
    _ = RepresentativeClusterSubsequence.paperRankHermitePrefixValue data
          (D.translateToZero w₀) representative
          (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
          boundary.Fbranch
          (boundary.selectedTranslatedParameter D representative offset radius
            Fsys x w₀ hw₀ data
            (boundary.topIndividualCommonSelectedIndex D representative offset
              radius Fsys x w₀ hw₀ data hA n)) (c.val + 1) := by
        unfold individualHermiteBoundarySymbolValue
          RepresentativeClusterSubsequence.paperRankHermiteOrderedClusterPrefixSequenceValue
        rw [hparam]
    _ = hc.symm ▸
          RepresentativeClusterSubsequence.paperRankHermitePrefixValue data
            (D.translateToZero w₀) representative
            (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
            boundary.Fbranch
            (boundary.selectedTranslatedParameter D representative offset
              radius Fsys x w₀ hw₀ data
              (boundary.topIndividualCommonSelectedIndex D representative offset
                radius Fsys x w₀ hw₀ data hA n))
            data.orderedClusterCount :=
        boundary.paperRankHermitePrefixValue_transport_to_top D representative
          offset radius Fsys x w₀ hw₀ data (c.val + 1) hc _
    _ = boundary.selectedTopPrefixAssignmentAtLastCluster D representative
          offset radius Fsys x w₀ hw₀ data c hc
          (boundary.topIndividualCommonSelectedIndex D representative offset
            radius Fsys x w₀ hw₀ data hA n) := by
        unfold selectedTopPrefixAssignmentAtLastCluster
        apply boundary.orderedClusterPrefixAssignment_transport_congr D
          representative offset radius Fsys x w₀ hw₀ data (c.val + 1) hc
        calc
          RepresentativeClusterSubsequence.paperRankHermitePrefixValue data
              (D.translateToZero w₀) representative
              (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
              boundary.Fbranch
              (boundary.selectedTranslatedParameter D representative offset
                radius Fsys x w₀ hw₀ data
                (boundary.topIndividualCommonSelectedIndex D representative
                  offset radius Fsys x w₀ hw₀ data hA n))
              data.orderedClusterCount =
            RepresentativeClusterSubsequence.paperRankHermiteTopPrefixValue data
              (D.translateToZero w₀) representative
              (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
              boundary.Fbranch
              (boundary.selectedTranslatedParameter D representative offset
                radius Fsys x w₀ hw₀ data
                (boundary.topIndividualCommonSelectedIndex D representative
                  offset radius Fsys x w₀ hw₀ data hA n)) :=
            boundary.paperRankHermitePrefixValue_top_eq_topPrefixValue D
              representative offset radius Fsys x w₀ hw₀ data _
          _ = data.paperRankHermiteTopPrefixAssignment boundary.S
              (boundary.selectedTopPrefixRetainedAssignment D representative
                offset radius Fsys x w₀ hw₀ data
                (boundary.topIndividualCommonSelectedIndex D representative
                  offset radius Fsys x w₀ hw₀ data hA n)) := by
            rw [boundary.selectedTopPrefixRetainedAssignment_eq_fullHermite D
              representative offset radius Fsys x w₀ hw₀ data]
            rfl

/-! ## Canonical representatives and evaluation -/

/-- Transport the literal padded top-prefix representative to an arbitrary
definitionally equal natural prefix index. -/
def topPrefixPaddedRepresentativeAtIndex
    (k : ℕ) (hk : k = data.orderedClusterCount)
    (j : Fin (boundary.generatorCount + 1)) :
    RestrictedBoxSpace p →
      data.OrderedClusterPrefixRing ℝ (paperRankHermiteHigherCount boundary.S) k :=
  fun w ↦ hk.symm ▸
    data.paperRankHermiteTopPrefixPaddedRepresentative boundary.S
      boundary.representativePolynomial j w

/-- The transported canonical representative has the transported padded
generator as its analytic germ. -/
theorem topPrefixPaddedGeneratorAtIndex_germ
    (k : ℕ) (hk : k = data.orderedClusterCount)
    (j : Fin (boundary.generatorCount + 1)) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (hk.symm ▸ data.paperRankHermiteTopPrefixPaddedGenerator boundary.S
          boundary.generator j) =
      (boundary.topPrefixPaddedRepresentativeAtIndex D representative offset
        radius Fsys x w₀ hw₀ data k hk j :
        Germ (nhds (0 : RestrictedBoxSpace p))
          (data.OrderedClusterPrefixRing ℝ
            (paperRankHermiteHigherCount boundary.S) k)) := by
  subst k
  change analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
      (data.paperRankHermiteTopPrefixPaddedGenerator boundary.S
        boundary.generator j) =
    (data.paperRankHermiteTopPrefixPaddedRepresentative boundary.S
      boundary.representativePolynomial j :
      Germ (nhds (0 : RestrictedBoxSpace p))
        (data.OrderedClusterPrefixRing ℝ
          (paperRankHermiteHigherCount boundary.S)
          data.orderedClusterCount))
  exact boundary.paddedTopPrefix_germ j

/-- Canonical padded representatives in the highest-cluster presentation. -/
def topPrefixPaddedRepresentativeAtLastCluster
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount)
    (j : Fin (boundary.generatorCount + 1)) :
    RestrictedBoxSpace p →
      data.OrderedClusterPrefixRing ℝ (paperRankHermiteHigherCount boundary.S)
        (c.val + 1) :=
  boundary.topPrefixPaddedRepresentativeAtIndex D representative offset radius
    Fsys x w₀ hw₀ data (c.val + 1) hc j

/-- The source representatives selected by the finite analytic adapter agree
eventually with the canonical transported padded representatives. -/
theorem eventually_topIndividualChangeSourceRepresentative_eq_padded
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) :
    ∀ᶠ n in atTop, ∀ j,
      (boundary.topIndividualBoundaryAnalyticChange D representative offset
        radius Fsys x w₀ hw₀ data c hc).sourceRepresentative j
          (boundary.topIndividualBoundaryParameterOnCommonTail D representative
            offset radius Fsys x w₀ hw₀ data hA c n) =
        boundary.topPrefixPaddedRepresentativeAtLastCluster D representative
          offset radius Fsys x w₀ hw₀ data c hc j
          (boundary.topIndividualBoundaryParameterOnCommonTail D representative
            offset radius Fsys x w₀ hw₀ data hA c n) := by
  apply Filter.eventually_all.mpr
  intro j
  exact (boundary.topIndividualBoundaryParameterOnCommonTail_tendsto D
    representative offset radius Fsys x w₀ hw₀ data hA c).eventually
      (analyticPolynomialRepresentatives_eventually_eq
        (0 : RestrictedBoxSpace p)
        ((boundary.topIndividualBoundaryAnalyticChange D representative offset
          radius Fsys x w₀ hw₀ data c hc).source_germ_eq j)
        (boundary.topPrefixPaddedGeneratorAtIndex_germ D representative offset
          radius Fsys x w₀ hw₀ data (c.val + 1) hc j)
        rfl)

/-- Simultaneously transporting a prefix polynomial and its assignment along
an equality of natural prefix indices preserves evaluation. -/
theorem eval_transport_orderedClusterPrefix
    (k : ℕ) (hk : k = data.orderedClusterCount)
    (v : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock data.orderedClusterCount)
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1)
        data.orderedClusterCount) → ℝ)
    (P : data.OrderedClusterPrefixRing ℝ
      (paperRankHermiteHigherCount boundary.S) data.orderedClusterCount) :
    MvPolynomial.eval (hk.symm ▸ v) (hk.symm ▸ P) =
      MvPolynomial.eval v P := by
  subst k
  rfl

/-- The residual top-boundary compatibility is canonically inhabited. -/
noncomputable def topIndividualSelectedPaddedCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) :
    boundary.TopIndividualSelectedPaddedCompatibility D representative offset
      radius Fsys x w₀ hw₀ data hA c hc where
  source_eq_selected := by
    have hrepresentative :=
      boundary.eventually_topIndividualChangeSourceRepresentative_eq_padded D
        representative offset radius Fsys x w₀ hw₀ data hA c hc
    have hvalue :=
      boundary.topIndividualBoundarySymbolValueOnCommonTail_eventuallyEq_selected
        D representative offset radius Fsys x w₀ hw₀ data hA c hc
    filter_upwards [hrepresentative, hvalue] with n hrep hassignment
    intro j
    change MvPolynomial.eval
        (fun z ↦ boundary.topIndividualBoundarySymbolValueOnCommonTail D
          representative offset radius Fsys x w₀ hw₀ data hA c z n)
        ((boundary.topIndividualBoundaryAnalyticChange D representative offset
          radius Fsys x w₀ hw₀ data c hc).sourceRepresentative j
          (boundary.topIndividualBoundaryParameterOnCommonTail D representative
            offset radius Fsys x w₀ hw₀ data hA c n)) = _
    rw [hrep j,
      boundary.topIndividualBoundaryParameterOnCommonTail_eq_selectedTopPrefixBox
        D representative offset radius Fsys x w₀ hw₀ data hA c n,
      hassignment]
    exact boundary.eval_transport_orderedClusterPrefix D representative offset
      radius Fsys x w₀ hw₀ data (c.val + 1) hc
      (data.paperRankHermiteTopPrefixAssignment boundary.S
        (boundary.selectedTopPrefixRetainedAssignment D representative offset
          radius Fsys x w₀ hw₀ data
          (boundary.topIndividualCommonSelectedIndex D representative offset
            radius Fsys x w₀ hw₀ data hA n)))
      (data.paperRankHermiteTopPrefixPaddedRepresentative boundary.S
        boundary.representativePolynomial j
        (boundary.selectedTopPrefixBoxParameter D representative offset radius
          Fsys x w₀ hw₀ data
          (boundary.topIndividualCommonSelectedIndex D representative offset
            radius Fsys x w₀ hw₀ data hA n)))

/-- Proposition-form convenience wrapper for clients that only need
inhabitation of the compatibility record. -/
theorem nonempty_topIndividualSelectedPaddedCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount) :
    Nonempty (boundary.TopIndividualSelectedPaddedCompatibility D representative
      offset radius Fsys x w₀ hw₀ data hA c hc) :=
  ⟨boundary.topIndividualSelectedPaddedCompatibility D representative offset
    radius Fsys x w₀ hw₀ data hA c hc⟩

/-- Compatibility-free form of the final quantitative transport into the
literal selected padded top-prefix family. -/
theorem selectedPaddedTopPrefix_lower_of_topIndividualBoundaryZero_lower_auto
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount)
    (hincoming : HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)) :
    HasInversePowerLowerBound atTop
      (boundary.topIndividualBoundaryZeroScale D representative offset radius
        Fsys x w₀ hw₀ data c)
      (boundary.selectedPaddedTopPrefixNumericValue D representative offset
        radius Fsys x w₀ hw₀ data) :=
  boundary.selectedPaddedTopPrefix_lower_of_topIndividualBoundaryZero_lower D
    representative offset radius Fsys x w₀ hw₀ data hA c hc
    (boundary.topIndividualSelectedPaddedCompatibility D representative offset
      radius Fsys x w₀ hw₀ data hA c hc) hincoming

/-- The final contradiction after all ordered clusters, with the former
top-boundary compatibility filled canonically. -/
theorem false_of_topIndividualBoundaryZero_lower_auto
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 = data.orderedClusterCount)
    (hincoming : HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)) :
    False :=
  boundary.false_of_topIndividualBoundaryZero_lower D representative offset
    radius Fsys x w₀ hw₀ data hA c hc
    (boundary.topIndividualSelectedPaddedCompatibility D representative offset
      radius Fsys x w₀ hw₀ data hA c hc) hincoming

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
