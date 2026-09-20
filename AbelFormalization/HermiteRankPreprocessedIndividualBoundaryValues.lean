import AbelFormalization.HermiteRankPreprocessedIndividualAnalyticBoundaryData

/-!
# Concrete Hermite symbol values at individual trace boundaries

At the boundary following the first `q` fixed individual decrements, the
representative coordinates in the active cluster are the corresponding
inverse-Abel prefix values.  Every earlier cluster and the bounded parameter
are copied from the selected translated paper parameter.  Evaluating the
common Hermite family at this parameter gives one literal symbol assignment
for every ideal boundary.

This module proves polynomial upper bounds for all those symbols at the
canonical boundary scale.  Active-cluster bounds come from the balancing
maximum, while earlier-cluster bounds use the divergent gap between ordered
clusters.  The resulting assignment discharges the final symbol-bound premise
of the finite analytic change-of-generators adapter.
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

noncomputable local instance individualBoundaryValueBlockDecidableEq
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- Converting a literal active-cluster member to its balancing coordinate
and back recovers the member. -/
@[simp]
theorem orderedClusterEnumeration_balancingIndexOfMem
    (c : Fin data.orderedClusterCount) (block : Fin m)
    (hblock : block ∈ data.orderedCluster c) :
    data.orderedClusterEnumeration c
        (balancingIndexOfMem x data c block hblock) = block := by
  unfold balancingIndexOfMem
    RepresentativeClusterSubsequence.orderedClusterEnumeration
    RepresentativeClusterSubsequence.orderedClusterBalancingToActiveEquiv
  simp

/-- The actual paper parameter at individual ideal boundary `q`, after the
common quantitative tail. -/
def individualHermiteBoundaryParameter
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1)) (n : ℕ) :
    PaperRankParameterSpace m p :=
  boundary.clusterPrefixParameter D representative offset radius Fsys x w₀
    hw₀ data c q.val
      (n + boundary.individualQuantitativeTail D representative offset radius
        Fsys x w₀ hw₀ data hA)

@[simp]
theorem individualHermiteBoundaryParameter_box
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1)) (n : ℕ) :
    (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).2 =
      (boundary.selectedTranslatedParameter D representative offset radius
        Fsys x w₀ hw₀ data
        (n + boundary.individualQuantitativeTail D representative offset
          radius Fsys x w₀ hw₀ data hA)).2 := by
  exact boundary.clusterPrefixParameter_box D representative offset radius Fsys
    x w₀ hw₀ data c q.val
      (n + boundary.individualQuantitativeTail D representative offset radius
        Fsys x w₀ hw₀ data hA)

/-- The concrete full Hermite assignment at individual ideal boundary `q`. -/
def individualHermiteBoundarySymbolValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1)) :
    ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)) → ℕ → ℝ :=
  data.paperRankHermiteOrderedClusterPrefixSequenceValue c
    (D.translateToZero w₀) representative
    (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
    boundary.Fbranch
    (boundary.individualHermiteBoundaryParameter D representative offset
      radius Fsys x w₀ hw₀ data hA c q)

/-- Active centers are exactly the canonical balancing-prefix values. -/
@[simp]
theorem individualHermiteBoundaryParameter_activeCenter
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (i : Fin (data.orderedClusterTailSize c + 1)) (n : ℕ) :
    (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1
        (data.orderedClusterEnumeration c i) =
      clusterBalancingPrefixValue A
        (fun k ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA k) c)
        (boundary.preprocessed.fixedSteps c) q.val i n := by
  rw [individualHermiteBoundaryParameter,
    boundary.clusterPrefixParameter_enumeration D representative offset radius
      Fsys x w₀ hw₀ data]
  rfl

/-- Every active center at a fixed boundary still tends to infinity. -/
theorem individualHermiteBoundaryParameter_activeCenter_tendsto_atTop
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    Tendsto (fun n ↦
      (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1
        (data.orderedClusterEnumeration c i)) atTop atTop := by
  let Ntail := boundary.individualQuantitativeTail D representative offset
    radius Fsys x w₀ hw₀ data hA
  let shift : ℕ → ℕ := fun n ↦ n + Ntail
  have hshift : Tendsto shift atTop atTop := by
    simpa only [shift, Nat.add_comm] using tendsto_add_atTop_nat Ntail
  have hmin : Tendsto (fun n ↦ data.orderedClusterMinTime c
      (boundary.individualQuantitativeSubsequence D representative offset
        radius Fsys x w₀ hw₀ data hA n)) atTop atTop := by
    simpa [individualQuantitativeSubsequence, Function.comp_def, shift,
      Ntail] using
      (boundary.selectedClusterMinTime_tendsto_atTop D representative offset
        radius Fsys x w₀ hw₀ data hA c).comp hshift
  apply tendsto_atTop_mono' atTop _ (hA.inverse_tendsto_atTop.comp hmin)
  filter_upwards with n
  rw [boundary.individualHermiteBoundaryParameter_activeCenter D
    representative offset radius Fsys x w₀ hw₀ data hA c q i n]
  apply hA.inverse_strictMono.monotone
  exact (boundary.preprocessed.plans (n + Ntail) c).base_le_prefix
    (boundary.preprocessed.plans_steps (n + Ntail) c) q.val i

/-- Every active center is pointwise bounded by the canonical boundary
maximum. -/
theorem individualHermiteBoundaryParameter_activeCenter_le_scale
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (i : Fin (data.orderedClusterTailSize c + 1)) (n : ℕ) :
    (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1
        (data.orderedClusterEnumeration c i) ≤
      boundary.individualNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data hA c q n := by
  rw [boundary.individualHermiteBoundaryParameter_activeCenter D
    representative offset radius Fsys x w₀ hw₀ data hA c q i n]
  exact clusterBalancingPrefixValue_le_scale A
    (fun k ↦ data.orderedClusterRawTime
      (boundary.individualQuantitativeSubsequence D representative offset
        radius Fsys x w₀ hw₀ data hA k) c)
    (boundary.preprocessed.fixedSteps c) q.val n i

/-- A block outside the active cluster is copied unchanged from the selected
translated paper parameter. -/
theorem individualHermiteBoundaryParameter_inactiveCenter
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (block : Fin m) (hblock : block ∉ data.orderedCluster c) (n : ℕ) :
    (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 block =
      (boundary.selectedTranslatedParameter D representative offset radius
        Fsys x w₀ hw₀ data
        (n + boundary.individualQuantitativeTail D representative offset
          radius Fsys x w₀ hw₀ data hA)).1 block := by
  simp [individualHermiteBoundaryParameter, clusterPrefixParameter, hblock]

/-- Every copied earlier-cluster center tends to infinity. -/
theorem individualHermiteBoundaryParameter_inactiveCenter_tendsto_atTop
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (block : Fin m) (hblock : block ∉ data.orderedCluster c) :
    Tendsto (fun n ↦
      (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 block) atTop atTop := by
  let Ntail := boundary.individualQuantitativeTail D representative offset
    radius Fsys x w₀ hw₀ data hA
  let shift : ℕ → ℕ := fun n ↦ n + Ntail
  have hshift : Tendsto shift atTop atTop := by
    simpa only [shift, Nat.add_comm] using tendsto_add_atTop_nat Ntail
  have hselected := (boundary.selected_representative_tendsto block).comp hshift
  apply hselected.congr'
  filter_upwards with n
  rw [boundary.individualHermiteBoundaryParameter_inactiveCenter D
    representative offset radius Fsys x w₀ hw₀ data hA c q block hblock n]
  rfl

/-- A center copied from a strictly earlier ordered cluster is eventually
bounded by the active cluster's balancing scale. -/
theorem individualHermiteBoundaryParameter_earlierCenter_le_scale
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (d : Fin data.orderedClusterCount) (hd : d < c)
    (block : Fin m) (hblock : block ∈ data.orderedCluster d) :
    ∀ᶠ n in atTop,
      (boundary.individualHermiteBoundaryParameter D representative offset
          radius Fsys x w₀ hw₀ data hA c q n).1 block ≤
        boundary.individualNumericBoundaryScale D representative offset radius
          Fsys x w₀ hw₀ data hA c q n := by
  have hnot : block ∉ data.orderedCluster c := by
    intro hc
    exact Finset.disjoint_left.mp
      (data.orderedCluster_disjoint (ne_of_lt hd)) hblock hc
  let active : Fin (data.orderedClusterTailSize c + 1) := 0
  let activeBlock : Fin m := data.orderedClusterEnumeration c active
  let center : ℕ → ℝ := fun n ↦
    (boundary.individualHermiteBoundaryParameter D representative offset
      radius Fsys x w₀ hw₀ data hA c q n).1 block
  let higher : ℕ → ℝ := fun n ↦ data.orderedClusterRawTime
    (boundary.individualQuantitativeSubsequence D representative offset radius
      Fsys x w₀ hw₀ data hA n) c active
  let lower : ℕ → ℝ := fun n ↦ A (center n)
  let higherShift : ℕ → ℕ := fun _ ↦
    ((boundary.preprocessed.fixedSteps c).take q.val).count active
  let lowerShift : ℕ → ℕ := fun _ ↦ 0
  let Ntail := boundary.individualQuantitativeTail D representative offset
    radius Fsys x w₀ hw₀ data hA
  let shift : ℕ → ℕ := fun n ↦ n + Ntail
  have hshift : Tendsto shift atTop atTop := by
    simpa only [shift, Nat.add_comm] using tendsto_add_atTop_nat Ntail
  have hreindex : Tendsto
      (boundary.individualQuantitativeSubsequence D representative offset
        radius Fsys x w₀ hw₀ data hA) atTop atTop := by
    unfold individualQuantitativeSubsequence
    exact boundary.preprocessed.balancingSubsequence_strictMono.tendsto_atTop.comp
      hshift
  have hgap0 := data.tendsto_orderedCluster_gap_atTop hd hblock
    (data.orderedClusterEnumeration_mem c active)
  have hgap : Tendsto (fun n ↦ higher n - lower n) atTop atTop := by
    apply (hgap0.comp hreindex).congr'
    filter_upwards with n
    dsimp only [Function.comp_apply, higher, lower]
    rw [show center n =
        (boundary.selectedTranslatedParameter D representative offset radius
          Fsys x w₀ hw₀ data
          (n + boundary.individualQuantitativeTail D representative offset
            radius Fsys x w₀ hw₀ data hA)).1 block by
      exact boundary.individualHermiteBoundaryParameter_inactiveCenter D
        representative offset radius Fsys x w₀ hw₀ data hA c q block hnot n]
    rfl
  have hcenterTop : Tendsto center atTop atTop :=
    boundary.individualHermiteBoundaryParameter_inactiveCenter_tendsto_atTop D
      representative offset radius Fsys x w₀ hw₀ data hA c q block hnot
  have hlower : Tendsto lower atTop atTop := hA.tendsto_atTop.comp hcenterTop
  have hhigherShift : ∀ᶠ n in atTop,
      higherShift n ≤ (boundary.preprocessed.fixedSteps c).length := by
    filter_upwards with n
    exact (List.count_le_length).trans <| by
      rw [List.length_take]
      exact Nat.min_le_right _ _
  have hlowerShift : ∀ᶠ n in atTop, lowerShift n ≤ 0 := by
    filter_upwards with n
    exact le_rfl
  have hdom := hA.eventually_exp_iterate_inverse_shift_lt_of_gap hgap hlower
    higherShift lowerShift (boundary.preprocessed.fixedSteps c).length 0 0
    hhigherShift hlowerShift
  have hpositive : ∀ᶠ n in atTop, 0 < center n :=
    hcenterTop.eventually (eventually_gt_atTop 0)
  filter_upwards [hdom, hpositive] with n hn hnpositive
  have hn' : center n <
      inverse A (higher n - (higherShift n : ℝ)) := by
    simpa only [Function.iterate_zero_apply, lowerShift, Nat.cast_zero,
      sub_zero, lower, hA.inverse_apply hnpositive] using hn
  calc
    (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 block = center n := rfl
    _ ≤ inverse A (higher n - (higherShift n : ℝ)) := hn'.le
    _ = (boundary.individualHermiteBoundaryParameter D representative offset
          radius Fsys x w₀ hw₀ data hA c q n).1 activeBlock := by
      rw [boundary.individualHermiteBoundaryParameter_activeCenter D
        representative offset radius Fsys x w₀ hw₀ data hA c q active n]
      rfl
    _ ≤ boundary.individualNumericBoundaryScale D representative offset radius
          Fsys x w₀ hw₀ data hA c q n :=
      boundary.individualHermiteBoundaryParameter_activeCenter_le_scale D
        representative offset radius Fsys x w₀ hw₀ data hA c q active n

/-- Every block center in the `(c+1)`-prefix tends to infinity. -/
theorem individualHermiteBoundaryParameter_center_tendsto_atTop
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) :
    Tendsto (fun n ↦
      (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 b.1) atTop atTop := by
  obtain ⟨d, hd, hb⟩ := b.2
  by_cases hdc : d = c
  · subst d
    let i := balancingIndexOfMem x data c b.1 hb
    simpa only [i,
      orderedClusterEnumeration_balancingIndexOfMem x data c b.1 hb] using
      boundary.individualHermiteBoundaryParameter_activeCenter_tendsto_atTop D
        representative offset radius Fsys x w₀ hw₀ data hA c q i
  · have hdc' : d < c := by
      change d.val < c.val
      omega
    have hnot : b.1 ∉ data.orderedCluster c := by
      intro hc
      exact Finset.disjoint_left.mp
        (data.orderedCluster_disjoint (ne_of_lt hdc')) hb hc
    exact boundary.individualHermiteBoundaryParameter_inactiveCenter_tendsto_atTop
      D representative offset radius Fsys x w₀ hw₀ data hA c q b.1 hnot

/-- Every block center in the `(c+1)`-prefix is eventually bounded by the
canonical individual boundary scale. -/
theorem individualHermiteBoundaryParameter_center_le_scale
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) :
    ∀ᶠ n in atTop,
      (boundary.individualHermiteBoundaryParameter D representative offset
          radius Fsys x w₀ hw₀ data hA c q n).1 b.1 ≤
        boundary.individualNumericBoundaryScale D representative offset radius
          Fsys x w₀ hw₀ data hA c q n := by
  obtain ⟨d, hd, hb⟩ := b.2
  by_cases hdc : d = c
  · subst d
    let i := balancingIndexOfMem x data c b.1 hb
    filter_upwards with n
    simpa only [i,
      orderedClusterEnumeration_balancingIndexOfMem x data c b.1 hb] using
      boundary.individualHermiteBoundaryParameter_activeCenter_le_scale D
        representative offset radius Fsys x w₀ hw₀ data hA c q i n
  · have hdc' : d < c := by
      change d.val < c.val
      omega
    exact boundary.individualHermiteBoundaryParameter_earlierCenter_le_scale D
      representative offset radius Fsys x w₀ hw₀ data hA c q d hdc' b.1 hb

@[simp]
theorem individualHermiteBoundarySymbolValue_free
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) (n : ℕ) :
    boundary.individualHermiteBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c q (Sum.inl b) n =
      (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 b.1 := by
  rfl

@[simp]
theorem individualHermiteBoundarySymbolValue_positiveDerivative
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1))
    (r : Fin (paperRankHermiteHigherCount boundary.S + 1)) (n : ℕ) :
    boundary.individualHermiteBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c q
        (Sum.inr (Sum.inl ⟨b, r⟩)) n =
      paperRankHermiteCoefficientValue (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        boundary.B (fun _ ↦ boundary.Fbranch)
        (boundary.individualHermiteBoundaryParameter D representative offset
          radius Fsys x w₀ hw₀ data hA c q n)
        (Sum.inr b.1)
        (finCongr (paperRankHermiteHigherCount_add_one boundary.S) r).succ := by
  rfl

@[simp]
theorem individualHermiteBoundarySymbolValue_time
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) (n : ℕ) :
    boundary.individualHermiteBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c q (Sum.inr (Sum.inr b)) n =
      paperRankHermiteCoefficientValue (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        boundary.B (fun _ ↦ boundary.Fbranch)
        (boundary.individualHermiteBoundaryParameter D representative offset
          radius Fsys x w₀ hw₀ data hA c q n)
        (Sum.inr b.1) 0 := by
  rfl

/-- The common Hermite coefficient estimate, stated directly for a moving
paper parameter.  This includes coefficient zero (the time symbol), which is
not part of the positive source-jet tuple. -/
theorem hermiteCoefficientValue_hasPolynomialUpperBound
    {S : Finset (ι × ℕ)}
    {X0 K K0 u0 ε Kr B : ℝ} {F : ℂ → ℂ}
    (H : FullHermiteLemmaSpec A B (paperRankHermiteNodeMultiplicity S)
      X0 K K0 u0 ε Kr (fun _ ↦ F) F)
    (hB : 0 < B)
    (sw : ℕ → PaperRankParameterSpace m p) (block : Fin m)
    (j : Fin (Sum.elim
      (paperRankHermiteBlockDerivativeCount S (Fin 0))
      (paperRankHermiteBlockDerivativeCount S (Fin m))
      (Sum.inr block) + 1))
    (scale : ℕ → ℝ)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hcenterTop : Tendsto (fun n ↦ (sw n).1 block) atTop atTop)
    (hcenter_le : ∀ᶠ n in atTop, (sw n).1 block ≤ scale n)
    (hoffset : ∀ n (k : Fin S.card),
      |(offset (restrictedJetEnumeration S k).1 :
        RestrictedBoxSpace p → ℝ) (sw n).2| ≤ B) :
    HasPolynomialUpperBound atTop scale (fun n ↦
      paperRankHermiteCoefficientValue D representative offset S
        (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
        B (fun _ ↦ F) (sw n) (Sum.inr block) j) := by
  refine ⟨2 * K0, mul_pos (by norm_num) H.family.coefficientConstant_pos,
    1, ?_⟩
  have hthreshold : ∀ᶠ n in atTop, X0 < (sw n).1 block :=
    hcenterTop.eventually (eventually_gt_atTop X0)
  filter_upwards [hscale, hcenter_le, hthreshold] with n hnscale hncenter
      hnthreshold
  let nodes : Option (Fin S.card) → ℂ := fun node ↦
    (paperRankHermiteNodes D representative offset S block (sw n).2 node : ℂ)
  have hnodes : nodes ∈ hermiteNodeNeighborhood B :=
    paperRankHermiteNodes_mem_hermiteNodeNeighborhood D representative offset S
      H.family hB (sw n).2 (hoffset n) block
  have hj : j.val < totalMultiplicity (paperRankHermiteNodeMultiplicity S) := by
    simpa [paperRankHermiteBlockDerivativeCount,
      paperRankHermitePositiveDerivativeCount_add_one] using j.isLt
  have hcoeff := H.family.coefficient_bound ((sw n).1 block) hnthreshold
    nodes hnodes j.val hj
  change
    |(abelHermiteCoeff (fun _ ↦ F) B (paperRankHermiteNodeMultiplicity S)
      ((sw n).1 block) nodes j.val).re| ≤
        (2 * K0) * scale n ^ (1 : ℕ)
  exact (Complex.abs_re_le_norm _).trans <| hcoeff.trans <| calc
    K0 * (1 + (sw n).1 block) ≤ K0 * (2 * scale n) := by
      apply mul_le_mul_of_nonneg_left _ H.family.coefficientConstant_pos.le
      linarith
    _ = (2 * K0) * scale n ^ (1 : ℕ) := by ring

/-- Each representative coordinate of the concrete Hermite boundary is
polynomially bounded at its canonical boundary scale. -/
theorem individualHermiteBoundarySymbolValue_free_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) :
    HasPolynomialUpperBound atTop
      (boundary.individualNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data hA c q)
      (boundary.individualHermiteBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c q (Sum.inl b)) := by
  refine ⟨1, by norm_num, 1, ?_⟩
  have hpositive : ∀ᶠ n in atTop,
      0 < (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c q n).1 b.1 :=
    (boundary.individualHermiteBoundaryParameter_center_tendsto_atTop D
      representative offset radius Fsys x w₀ hw₀ data hA c q b).eventually
        (eventually_gt_atTop 0)
  have hle := boundary.individualHermiteBoundaryParameter_center_le_scale D
    representative offset radius Fsys x w₀ hw₀ data hA c q b
  filter_upwards [hpositive, hle] with n hnpositive hnle
  rw [boundary.individualHermiteBoundarySymbolValue_free D representative
    offset radius Fsys x w₀ hw₀ data hA c q b n,
    abs_of_pos hnpositive, pow_one, one_mul]
  exact hnle

/-- Each positive Hermite coefficient coordinate of the concrete boundary is
polynomially bounded at its canonical boundary scale. -/
theorem individualHermiteBoundarySymbolValue_positiveDerivative_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1))
    (r : Fin (paperRankHermiteHigherCount boundary.S + 1)) :
    HasPolynomialUpperBound atTop
      (boundary.individualNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data hA c q)
      (boundary.individualHermiteBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c q
        (Sum.inr (Sum.inl ⟨b, r⟩))) := by
  let H := (boundary.commonRealHermiteData D representative offset radius Fsys
    x w₀ hw₀ data hA).fullHermite
  apply (hermiteCoefficientValue_hasPolynomialUpperBound (D.translateToZero w₀)
    representative (restrictedOffsetTranslateToZero w₀ offset) H
    boundary.B_pos
    (boundary.individualHermiteBoundaryParameter D representative offset radius
      Fsys x w₀ hw₀ data hA c q) b.1
    (finCongr (paperRankHermiteHigherCount_add_one boundary.S) r).succ
    (boundary.individualNumericBoundaryScale D representative offset radius
      Fsys x w₀ hw₀ data hA c q) ?_ ?_ ?_ ?_).congr
  · intro n
    exact (boundary.individualHermiteBoundarySymbolValue_positiveDerivative D
      representative offset radius Fsys x w₀ hw₀ data hA c q b r n).symm
  · exact Filter.Eventually.of_forall fun n ↦ one_le_two.trans
      (two_le_clusterBalancingPrefixScale A
        (fun k ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA k) c)
        (boundary.preprocessed.fixedSteps c) q.val n)
  · exact boundary.individualHermiteBoundaryParameter_center_tendsto_atTop D
      representative offset radius Fsys x w₀ hw₀ data hA c q b
  · exact boundary.individualHermiteBoundaryParameter_center_le_scale D
      representative offset radius Fsys x w₀ hw₀ data hA c q b
  · intro n k
    rw [boundary.individualHermiteBoundaryParameter_box D representative offset
      radius Fsys x w₀ hw₀ data hA c q n]
    exact boundary.selectedTranslatedOffset_bound D representative offset radius
      Fsys x w₀ hw₀ data
        (n + boundary.individualQuantitativeTail D representative offset radius
          Fsys x w₀ hw₀ data hA) k

/-- The Hermite coefficient-zero (time) coordinate of every prefix block is
polynomially bounded at the same boundary scale. -/
theorem individualHermiteBoundarySymbolValue_time_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (q : Fin ((boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length + 1))
    (b : data.OrderedClusterPrefixBlock (c.val + 1)) :
    HasPolynomialUpperBound atTop
      (boundary.individualNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data hA c q)
      (boundary.individualHermiteBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c q (Sum.inr (Sum.inr b))) := by
  let H := (boundary.commonRealHermiteData D representative offset radius Fsys
    x w₀ hw₀ data hA).fullHermite
  apply (hermiteCoefficientValue_hasPolynomialUpperBound (D.translateToZero w₀)
    representative (restrictedOffsetTranslateToZero w₀ offset) H
    boundary.B_pos
    (boundary.individualHermiteBoundaryParameter D representative offset radius
      Fsys x w₀ hw₀ data hA c q) b.1 0
    (boundary.individualNumericBoundaryScale D representative offset radius
      Fsys x w₀ hw₀ data hA c q) ?_ ?_ ?_ ?_).congr
  · intro n
    exact (boundary.individualHermiteBoundarySymbolValue_time D representative
      offset radius Fsys x w₀ hw₀ data hA c q b n).symm
  · exact Filter.Eventually.of_forall fun n ↦ one_le_two.trans
      (two_le_clusterBalancingPrefixScale A
        (fun k ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA k) c)
        (boundary.preprocessed.fixedSteps c) q.val n)
  · exact boundary.individualHermiteBoundaryParameter_center_tendsto_atTop D
      representative offset radius Fsys x w₀ hw₀ data hA c q b
  · exact boundary.individualHermiteBoundaryParameter_center_le_scale D
      representative offset radius Fsys x w₀ hw₀ data hA c q b
  · intro n k
    rw [boundary.individualHermiteBoundaryParameter_box D representative offset
      radius Fsys x w₀ hw₀ data hA c q n]
    exact boundary.selectedTranslatedOffset_bound D representative offset radius
      Fsys x w₀ hw₀ data
        (n + boundary.individualQuantitativeTail D representative offset radius
          Fsys x w₀ hw₀ data hA) k

/-- Every symbol of the concrete Hermite assignment is polynomially bounded
at its exact ideal-boundary scale. -/
theorem individualHermiteBoundarySymbolValue_hasPolynomialUpperBound
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
      (boundary.individualHermiteBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c q z) := by
  rcases z with b | z
  · exact boundary.individualHermiteBoundarySymbolValue_free_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c q b
  · rcases z with br | b
    · rcases br with ⟨b, r⟩
      exact boundary.individualHermiteBoundarySymbolValue_positiveDerivative_hasPolynomialUpperBound
        D representative offset radius Fsys x w₀ hw₀ data hA c q b r
    · exact boundary.individualHermiteBoundarySymbolValue_time_hasPolynomialUpperBound
        D representative offset radius Fsys x w₀ hw₀ data hA c q b

/-- The concrete Hermite assignment together with the canonical finite ideal
presentations and moving analytic parameter. -/
noncomputable def individualHermiteAnalyticBoundaryData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    IndividualCentralDisplayedTraceData.AnalyticBoundaryData
      (0 : RestrictedBoxSpace p)
      (boundary.individualNumericDisplayed D representative offset radius Fsys
        x w₀ hw₀ data c)
      (boundary.individualNumericBoundaryScale D representative offset radius
        Fsys x w₀ hw₀ data hA c) :=
  boundary.individualAnalyticBoundaryData D representative offset radius Fsys
    x w₀ hw₀ data hA c
    (boundary.individualHermiteBoundarySymbolValue D representative offset
      radius Fsys x w₀ hw₀ data hA c)
    (fun q z ↦
      boundary.individualHermiteBoundarySymbolValue_hasPolynomialUpperBound D
        representative offset radius Fsys x w₀ hw₀ data hA c q z)

/-- Fully instantiated finite numeric boundary compatibility for the concrete
Hermite prefix assignment.  There are no remaining symbol-bound premises. -/
noncomputable def individualHermiteNumericBoundaryCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    boundary.IndividualNumericBoundaryCompatibility D representative offset
      radius Fsys x w₀ hw₀ data hA c :=
  boundary.individualNumericBoundaryCompatibilityOfAnalyticChange D
    representative offset radius Fsys x w₀ hw₀ data hA c
    (boundary.individualHermiteBoundarySymbolValue D representative offset
      radius Fsys x w₀ hw₀ data hA c)
    (fun q z ↦
      boundary.individualHermiteBoundarySymbolValue_hasPolynomialUpperBound D
        representative offset radius Fsys x w₀ hw₀ data hA c q z)

/-- At the predecessor boundary of step `j`, the shared boundary assignment
is exactly the concrete pre-log Hermite assignment, reindexed by the common
quantitative tail. -/
theorem individualHermiteBoundarySymbolValue_beforeStep
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    boundary.individualHermiteBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc =
      fun z n ↦ boundary.individualPreLogPrefixSequenceValue D representative
        offset radius Fsys x w₀ hw₀ data c j z
        (n + boundary.individualQuantitativeTail D representative offset radius
          Fsys x w₀ hw₀ data hA) := by
  funext z n
  unfold individualHermiteBoundarySymbolValue
    individualHermiteBoundaryParameter individualPreLogPrefixSequenceValue
  simp only [Fin.val_castSucc,
    RepresentativeClusterSubsequence.orderedClusterIndividualStepIndexEquiv_apply_val]
  rfl

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
