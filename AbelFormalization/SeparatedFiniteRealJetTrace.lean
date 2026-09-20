import AbelFormalization.SeparatedDenominatorStep
import AbelFormalization.ClusterBalancing
import AbelFormalization.CrossClusterHierarchy

/-!
# Finite separated-cluster trace from real-jet transfer

This scratch module constructs every step of a finite
`SeparatedClustersBackwardTrace` by an actual call to the maintained real-jet
quantitative-transfer theorem followed by the maintained terminal
localization bridge.  The fixed polynomial localization identities are
selected independently of all sequence and scale data.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Set
open scoped BigOperators Topology

universe u

/-- Padding a possibly empty finite generating family by one leading zero
does not change the ideal it spans.  The padded family is indexed by
`Fin (c+1)`, hence is automatically nonempty for quantitative lower bounds. -/
theorem Ideal.span_range_finCons_zero
    {S : Type u} [CommRing S] {c : ℕ} (g : Fin c → S) :
    Ideal.span (Set.range (Fin.cons 0 g)) = Ideal.span (Set.range g) := by
  apply le_antisymm
  · apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · apply Ideal.subset_span
      exact ⟨j, by simp⟩
  · apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    apply Ideal.subset_span
    exact ⟨Fin.succ i, by simp⟩

/-- Distance to the integers is unchanged after subtracting an integer. -/
theorem integerDistance_sub_intCast (x : ℝ) (q : ℤ) :
    integerDistance (x - q) = integerDistance x := by
  apply le_antisymm
  · rw [le_integerDistance_iff]
    intro z
    have hz :=
      (le_integerDistance_iff.mp
        (le_refl (integerDistance (x - q)))) (z - q)
    convert hz using 1 <;> push_cast <;> ring_nf
  · rw [le_integerDistance_iff]
    intro z
    have hz :=
      (le_integerDistance_iff.mp
        (le_refl (integerDistance x))) (z + q)
    convert hz using 1 <;> push_cast <;> ring_nf

/-- Balancing shifts each coordinate by an integer, hence preserves the
integer distance of every pair exactly. -/
theorem integerDistance_clusterShiftedTimes_sub
    {ι : Type u} [DecidableEq ι]
    (a : ι → ℝ) (steps : List ι) (i j : ι) :
    integerDistance
        (clusterShiftedTimes a steps i - clusterShiftedTimes a steps j) =
      integerDistance (a i - a j) := by
  let q : ℤ := (steps.count i : ℤ) - (steps.count j : ℤ)
  rw [show clusterShiftedTimes a steps i - clusterShiftedTimes a steps j =
      (a i - a j) - (q : ℝ) by
    dsimp [clusterShiftedTimes, q]
    push_cast
    ring]
  exact integerDistance_sub_intCast (a i - a j) q

/-- Precisely the five scale-hierarchy inputs to real-jet quantitative
transfer which follow from a balanced separated cluster. -/
structure BalancedRealJetTransferHierarchy
    (m : ℕ) (u : Fin (m + 1) → ℕ → ℝ) (Rscale : ℕ → ℝ) : Prop where
  positive : ∀ n i, 0 < u i n
  order : ∀ᶠ n in atTop, StrictAnti (fun i => u i n)
  scale_ge_two : ∀ᶠ n in atTop, 2 ≤ Rscale n
  adjacent_ratios : ∀ i : Fin m,
    Tendsto (fun n => u i.castSucc n / u i.succ n) atTop atTop
  smallest_div_log_scale :
    Tendsto (fun n => u (Fin.last m) n / Real.log (Rscale n))
      atTop atTop

/-- The two cross-cluster scale comparisons used by one quantitative
transfer after its internal balanced hierarchy has been constructed. -/
structure CrossClusterTransferScaleDomination
    (m : ℕ) (u : Fin (m + 1) → ℕ → ℝ)
    (Rscale Xscale : ℕ → ℝ) : Prop where
  scale_le : ∀ᶠ n in atTop, Rscale n ≤ Xscale n
  target_ge_two : ∀ᶠ n in atTop, 2 ≤ Xscale n
  exponential_le : ∀ᶠ n in atTop, ∀ i, E (u i n) ≤ Xscale n

/-- A divergent gap from every member of a smaller cluster to one higher
time supplies both the scale comparison and every exponential-coordinate
bound required by real-jet quantitative transfer. -/
theorem IsAbel.crossCluster_transferScaleDomination
    {A : ℝ → ℝ} (hA : IsAbel A) {m : ℕ}
    (higherTime : ℕ → ℝ) (lowerTime : Fin (m + 1) → ℕ → ℝ)
    (higherShift lowerShift : ℕ)
    (hgap : ∀ i,
      Tendsto (fun n => higherTime n - lowerTime i n) atTop atTop)
    (hlower : ∀ i, Tendsto (lowerTime i) atTop atTop) :
    CrossClusterTransferScaleDomination m
      (fun i n => L^[lowerShift] (inverse A (lowerTime i n)))
      (fun n => L^[lowerShift] (inverse A (lowerTime 0 n)))
      (fun n => inverse A (higherTime n - higherShift)) := by
  have hE : ∀ᶠ n in atTop, ∀ i : Fin (m + 1),
      E (L^[lowerShift] (inverse A (lowerTime i n))) <
        inverse A (higherTime n - higherShift) := by
    apply Filter.eventually_all.mpr
    intro i
    have hi := hA.eventually_E_iterate_inverse_sub_nat_lt_of_gap
      (hgap i) higherShift lowerShift 1
    filter_upwards [hi] with n hn
    simpa only [Function.iterate_one, hA.L_iterate_inverse] using hn
  have hhigher : Tendsto higherTime atTop atTop := by
    apply tendsto_atTop_mono' atTop _ (hlower 0)
    filter_upwards [(hgap 0).eventually (eventually_ge_atTop 0)] with n hn
    linarith
  have hhigherShifted : Tendsto
      (fun n => higherTime n - (higherShift : ℝ)) atTop atTop :=
    tendsto_sub_natCast_atTop_of_bounded hhigher
      (fun _ => higherShift) higherShift
      (Filter.Eventually.of_forall fun _ => le_rfl)
  have hXtop : Tendsto
      (fun n => inverse A (higherTime n - higherShift)) atTop atTop := by
    change Tendsto
      (fun n => inverse A (higherTime n - (higherShift : ℝ))) atTop atTop
    exact hA.inverse_tendsto_atTop.comp hhigherShifted
  refine {
    scale_le := ?_
    target_ge_two := hXtop.eventually (eventually_ge_atTop 2)
    exponential_le := hE.mono (fun _ hn i => (hn i).le)
  }
  filter_upwards [hE] with n hn
  exact (lt_E (by
    rw [hA.L_iterate_inverse]
    exact hA.inverse_pos _)).le.trans (hn 0).le

/-- Fixed balancing data plus the paper's separation estimate construct all
ordering and internal scale-hierarchy hypotheses for one real-jet transfer.
The comparison scale is the largest balanced representative after the fixed
number of logarithmic substitutions. -/
theorem IsAbel.balanced_realJetTransferHierarchy
    {A : ℝ → ℝ} (hA : IsAbel A) {m : ℕ}
    (rawTime : ℕ → Fin (m + 1) → ℝ)
    (base commonTime : ℕ → ℝ)
    (plans : ∀ n, ClusterBalancingPlan (rawTime n) (base n))
    (fixedOrder : Equiv.Perm (Fin (m + 1)))
    (hfixedOrder : ∀ n, (plans n).finalOrder = fixedOrder)
    (k : ℕ) {D N c : ℝ}
    (hc : 0 < c) (hN : D + k + 5 ≤ N)
    (ht : Tendsto commonTime atTop atTop)
    (hbaseLower : ∀ᶠ n in atTop,
      commonTime n - D ≤ base n)
    (hseparated : ∀ᶠ n in atTop,
      ∀ i j : Fin (m + 1), i ≠ j →
        c / inverse A (commonTime n - N) ≤
          integerDistance (rawTime n i - rawTime n j)) :
    BalancedRealJetTransferHierarchy m
      (fun i n =>
        L^[k] (inverse A ((plans n).finalTimes (fixedOrder i))))
      (fun n =>
        L^[k] (inverse A ((plans n).finalTimes (fixedOrder 0)))) := by
  let balanced : Fin (m + 1) → ℕ → ℝ :=
    fun i n => (plans n).finalTimes (fixedOrder i)
  have hseparatedPos : ∀ᶠ n in atTop,
      ∀ i j : Fin (m + 1), i ≠ j →
        0 < integerDistance (rawTime n i - rawTime n j) := by
    filter_upwards [hseparated] with n hn
    intro i j hij
    exact (div_pos hc (hA.inverse_pos _)).trans_le (hn i j hij)
  have hbalancedOrder : ∀ᶠ n in atTop,
      StrictAnti (fun i => balanced i n) := by
    filter_upwards [hseparatedPos] with n hn
    have hp := (plans n).strictAnti_finalTimes_comp_finalOrder_of_separated hn
    change StrictAnti ((plans n).finalTimes ∘ fixedOrder)
    rw [← hfixedOrder n]
    exact hp
  have hbalancedLower : ∀ᶠ n in atTop,
      commonTime n - D ≤ balanced (Fin.last m) n := by
    filter_upwards [hbaseLower] with n hn
    exact hn.trans ((plans n).base_le_final (fixedOrder (Fin.last m)))
  have hbalancedWidth : ∀ᶠ n in atTop,
      balanced 0 n - balanced (Fin.last m) n < 1 := by
    filter_upwards [] with n
    exact (plans n).final_sub_lt_one
      (fixedOrder 0) (fixedOrder (Fin.last m))
  have hbalancedSeparated : ∀ᶠ n in atTop,
      ∀ i j : Fin (m + 1), i ≠ j →
        c / inverse A (commonTime n - N) ≤
          integerDistance (balanced i n - balanced j n) := by
    filter_upwards [hseparated] with n hn
    intro i j hij
    change c / inverse A (commonTime n - N) ≤ integerDistance
      (clusterShiftedTimes (rawTime n) (plans n).steps (fixedOrder i) -
        clusterShiftedTimes (rawTime n) (plans n).steps (fixedOrder j))
    rw [integerDistance_clusterShiftedTimes_sub]
    exact hn (fixedOrder i) (fixedOrder j) (fixedOrder.injective.ne hij)
  have hhierarchy := hA.finite_cluster_hierarchy_filter atTop commonTime
    balanced k hc hN ht hbalancedOrder hbalancedLower hbalancedWidth
      hbalancedSeparated
  have hpositive : ∀ n i,
      0 < L^[k] (inverse A (balanced i n)) := by
    intro n i
    rw [hA.L_iterate_inverse]
    exact hA.inverse_pos _
  have horder : ∀ᶠ n in atTop,
      StrictAnti (fun i => L^[k] (inverse A (balanced i n))) := by
    filter_upwards [hbalancedOrder] with n hn
    intro i j hij
    change L^[k] (inverse A (balanced j n)) <
      L^[k] (inverse A (balanced i n))
    rw [hA.L_iterate_inverse, hA.L_iterate_inverse]
    exact hA.inverse_strictMono (sub_lt_sub_right (hn hij) k)
  have hbalancedZero : Tendsto (fun n => balanced 0 n - k) atTop atTop := by
    have hsub : Tendsto (fun y : ℝ => y - (D + k)) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro C
      filter_upwards [eventually_ge_atTop (C + (D + k))] with y hy
      linarith
    apply tendsto_atTop_mono' atTop _
      (hsub.comp ht)
    filter_upwards [hbalancedLower, hbalancedOrder] with n hnLower hnOrder
    have hlast := hnOrder.antitone (Fin.le_last (0 : Fin (m + 1)))
    change commonTime n - (D + k) ≤ balanced 0 n - k
    linarith
  have hRtop : Tendsto
      (fun n => L^[k] (inverse A (balanced 0 n))) atTop atTop := by
    have hinv := hA.inverse_tendsto_atTop.comp hbalancedZero
    change Tendsto (fun n => inverse A (balanced 0 n - k)) atTop atTop at hinv
    simpa only [hA.L_iterate_inverse] using hinv
  refine {
    positive := hpositive
    order := horder
    scale_ge_two := hRtop.eventually (eventually_ge_atTop 2)
    adjacent_ratios := hhierarchy.1
    smallest_div_log_scale := hhierarchy.2
  }

/-- Evaluation of the displayed terminal generators at one stage. -/
def separatedTerminalGeneratorValue
    {R : Type u} [CommRing R]
    (generatorCount : ℕ → ℕ)
    (h : ℕ → ℕ) (higher : ∀ j, Fin (h j) → ℕ)
    (terminalGenerator : ∀ j,
      Fin (generatorCount j + 1) →
        TerminalMultiblockSourceRing R (h j) (higher j) (Fin (h j)))
    (eval : ∀ j, ℕ →
      TerminalMultiblockSourceRing R (h j) (higher j) (Fin (h j)) →+* ℝ)
    (j : ℕ) : Fin (generatorCount j + 1) → ℕ → ℝ :=
  fun a n => eval j n (terminalGenerator j a)

/-- The algebraic localization witnesses for all stages can be chosen before
any evaluation, subsequence, scale, or analytic estimate is introduced. -/
theorem nonempty_terminalGeneratorBackwardIdentity_family
    {R : Type u} [CommRing R]
    (h : ℕ → ℕ) (higher : ∀ j, Fin (h j) → ℕ)
    (Q : ∀ j, Ideal (CentralPolynomial R (Fin (h j))
      (terminalTotalDerivativeCount (higher j)) (Fin (h j))))
    (certificate : ∀ j,
      TerminalizedClusterCertificate R (h j) (higher j) (Q j))
    (generatorCount : ℕ → ℕ)
    (contractedGenerator : ∀ j,
      Fin (generatorCount (j + 1) + 1) → MvPolynomial (Fin (h j)) R)
    (terminalGenerator : ∀ j,
      Fin (generatorCount j + 1) →
        TerminalMultiblockSourceRing R (h j) (higher j) (Fin (h j)))
    (hcontracted : ∀ j,
      Ideal.span (Set.range (contractedGenerator j)) =
        (certificate j).timeIdeal)
    (hterminal : ∀ j,
      Ideal.span (Set.range (terminalGenerator j)) =
        (certificate j).terminalIdeal) :
    Nonempty (∀ j,
      TerminalGeneratorBackwardIdentity R (higher j) (certificate j)
        (contractedGenerator j) (terminalGenerator j)) := by
  let data : ∀ j,
      TerminalGeneratorBackwardIdentity R (higher j) (certificate j)
        (contractedGenerator j) (terminalGenerator j) :=
    fun j => Classical.choice
      ((certificate j).nonempty_terminalGeneratorBackwardIdentity
        (contractedGenerator j) (terminalGenerator j)
        (hcontracted j) (hterminal j))
  exact ⟨data⟩

/-- A finite family of genuine real-jet-transfer/localization operations
assembles into the backward trace used by the separated-cluster reduction.

At stage `j`, the lower bound at stage `j+1` is used as the central-generator
lower bound.  Quantitative transfer yields a lower bound for the evaluated
contracted time generators, and the fixed localization identity then yields
the displayed terminal family at stage `j`.
-/
theorem separatedClustersBackwardTrace_of_realJet_transfer_family
    {R : Type u} [CommRing R]
    (clusterCount : ℕ)
    (generatorCount : ℕ → ℕ)
    (h : ℕ → ℕ) (higher : ∀ j, Fin (h j) → ℕ)
    (Q : ∀ j, Ideal (CentralPolynomial R (Fin (h j))
      (terminalTotalDerivativeCount (higher j)) (Fin (h j))))
    (clusterCertificate : ∀ j,
      TerminalizedClusterCertificate R (h j) (higher j) (Q j))
    (contractedGenerator : ∀ j,
      Fin (generatorCount (j + 1) + 1) → MvPolynomial (Fin (h j)) R)
    (terminalGenerator : ∀ j,
      Fin (generatorCount j + 1) →
        TerminalMultiblockSourceRing R (h j) (higher j) (Fin (h j)))
    (identityData : ∀ j,
      TerminalGeneratorBackwardIdentity R (higher j)
        (clusterCertificate j) (contractedGenerator j)
        (terminalGenerator j))
    (eval : ∀ j, ℕ →
      TerminalMultiblockSourceRing R (h j) (higher j) (Fin (h j)) →+* ℝ)
    (stageScale : ℕ → ℕ → ℝ)
    (m : ℕ) (d : Fin (m + 1) → ℕ)
    (I : ∀ j, Ideal (MvPolynomial (RealJetTransferIndex m d) R))
    (transferCertificate : ∀ j,
      CentralQuantitativeTransferCertificate R
        (Fin (m + 1)) (Fin (m + 1)) d (m + 1)
        (centralTransferShear d) (I j))
    (hcount : ∀ j, Nonempty (Fin (transferCertificate j).count))
    {A : ℝ → ℝ} (hA : IsAbel A)
    {Param : Type} [NormedAddCommGroup Param] [NormedSpace ℝ Param]
    (w : ℕ → ℕ → Param) (x₀ : ℕ → Param) (U : ℕ → Set Param)
    (hx₀U : ∀ j, x₀ j ∈ U j)
    (hw : ∀ j, Tendsto (w j) atTop (𝓝 (x₀ j)))
    (coefficientRepresentative : ∀ j,
      Fin (transferCertificate j).count →
        (RealJetTransferIndex m d →₀ ℕ) → Param → ℝ)
    (hcoefficientAnalytic : ∀ j a e,
      e ∈ ((transferCertificate j).source a).support →
        AnalyticOnNhd ℝ (coefficientRepresentative j a e) (U j))
    (u : ℕ → Fin (m + 1) → ℕ → ℝ)
    (jets : ∀ j n i,
      RealCentralJetSubstitutionData A (u j i n) (d i))
    (internalHierarchy : ∀ j, j < clusterCount →
      BalancedRealJetTransferHierarchy m (u j) (stageScale (j + 1)))
    (crossDomination : ∀ j, j < clusterCount →
      CrossClusterTransferScaleDomination m (u j)
        (stageScale (j + 1)) (stageScale j))
    (centralCoefficient : ∀ j,
      Fin (generatorCount (j + 1) + 1) →
        Fin (transferCertificate j).count → Param → ℝ)
    (sourceCoefficient : ∀ j,
      Fin (transferCertificate j).count →
        Fin (generatorCount (j + 1) + 1) → Param → ℝ)
    (hcentralCoefficientAnalytic : ∀ j b a,
      AnalyticOnNhd ℝ (centralCoefficient j b a) (U j))
    (hsourceCoefficientAnalytic : ∀ j a k,
      AnalyticOnNhd ℝ (sourceCoefficient j a k) (U j))
    (Pweight : ℕ → ℕ)
    (hweight : ∀ j, j < clusterCount →
      ∀ a : Fin (transferCertificate j).count,
        (∑ i, abs
          (coefficientwiseLeastWeight
            (centralLaurentWeight (centralTransferShear d))
            ((transferCertificate j).source a) i : ℝ)) ≤
              (Pweight j : ℝ))
    (hmainBound : ∀ j, j < clusterCount → ∀ x,
      HasPolynomialUpperBound atTop (stageScale (j + 1))
        (realJetMainAssignment A (u j) d x))
    (hperturbedBound : ∀ j, j < clusterCount → ∀ x,
      HasPolynomialUpperBound atTop (stageScale (j + 1))
        (realJetPerturbedAssignment (u j) d (jets j) x))
    (hcoordinateError : ∀ j, j < clusterCount → ∀ x,
      Asymptotics.SuperpolynomialDecay atTop (stageScale (j + 1))
        (fun n => realCentralTransferCoordinateError (jets j n) x))
    (hcentralIdentity : ∀ j, j < clusterCount →
      ∀ᶠ n in atTop, ∀ b : Fin (generatorCount (j + 1) + 1),
        separatedTerminalGeneratorValue generatorCount h higher
            terminalGenerator eval (j + 1) b n =
          ∑ a, centralCoefficient j b a (w j n) *
            realJetCoefficientwiseCentralEvaluation A d
              (fun e n => coefficientRepresentative j a e (w j n))
              (u j) ((transferCertificate j).source a) n)
    (hsourceIdentity : ∀ j, j < clusterCount →
      ∀ᶠ n in atTop, ∀ a : Fin (transferCertificate j).count,
        realJetCoefficientwiseSourceEvaluation d
            (fun e n => coefficientRepresentative j a e (w j n))
            (u j) (jets j) ((transferCertificate j).source a) n =
          ∑ k, sourceCoefficient j a k (w j n) *
            eval j n
              (terminalMultiblockRetainedSourceHom R (Fin (h j))
                (h j) (higher j) (contractedGenerator j k)))
    (hfirst : ∀ j, j < clusterCount → ∀ i : Fin (h j),
      HasScalarInversePowerLowerBound atTop (stageScale j)
        (fun n => eval j n
          (MvPolynomial.X
            (Sum.inl ⟨i, (0 : Fin (higher j i + 1))⟩))))
    (hlocalizationCoefficient : ∀ j, j < clusterCount → ∀ a k,
      HasPolynomialUpperBound atTop (stageScale j)
        (fun n => eval j n ((identityData j).coefficient a k))) :
    SeparatedClustersBackwardTrace atTop clusterCount generatorCount
      stageScale
      (separatedTerminalGeneratorValue generatorCount h higher
        terminalGenerator eval) := by
  refine ⟨?_⟩
  intro j hj hnext
  letI : Nonempty (Fin (transferCertificate j).count) := hcount j
  let internal := internalHierarchy j hj
  let cross := crossDomination j hj
  exact (identityData j).terminal_lower_of_realJet_transfer
    (eval j) d (I j) (transferCertificate j) hA
    (w j) (x₀ j) (U j) (hx₀U j) (hw j)
    (coefficientRepresentative j) (hcoefficientAnalytic j)
    (u j) internal.positive (jets j)
    (stageScale (j + 1)) (stageScale j)
    (separatedTerminalGeneratorValue generatorCount h higher
      terminalGenerator eval (j + 1))
    (centralCoefficient j) (sourceCoefficient j)
    (hcentralCoefficientAnalytic j) (hsourceCoefficientAnalytic j)
    internal.order
    (Filter.Eventually.of_forall fun n => internal.positive n (Fin.last m))
    internal.scale_ge_two internal.adjacent_ratios
    internal.smallest_div_log_scale cross.scale_le
    cross.target_ge_two cross.exponential_le
    (Pweight j) (hweight j hj) (hmainBound j hj)
    (hperturbedBound j hj) (hcoordinateError j hj)
    (hcentralIdentity j hj) hnext (hsourceIdentity j hj)
    (hfirst j hj) (hlocalizationCoefficient j hj)

end AbelFormalization
