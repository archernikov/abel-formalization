import AbelFormalization.RestrictedPairMergeCompressedCoordinates

/-!
# One terminal tower for the denominator-cleared pair-merge system
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- The derivative numerator and denominator for one exceptional graph label
are generated directly over the enlarged common base. -/
theorem exists_tower_restrictedPairMergeExceptionalDerivativeData_commonBase
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    (d r : ℕ) :
    let base := restrictedPairMergeCompressedCommonBase
      (a := a) A D representative offset i j S
    let u := restrictedPairMergeExceptionalGraphTargetArgument
      (a := a) D representative i j S t
    ∃ T : FiniteExponentialTower base d,
      (fun z ↦ iteratedAbelDerivativeDenominator d r (u z)) ∈ T.level d ∧
      (fun z ↦ iteratedAbelDerivativeNumerator A d r (u z)) ∈ T.level d := by
  dsimp only
  let base := restrictedPairMergeCompressedCommonBase
    (a := a) A D representative offset i j S
  let u := restrictedPairMergeExceptionalGraphTargetArgument
    (a := a) D representative i j S t
  have hu : u ∈ base := by
    let G₀ := restrictedPairMergeExceptionalGraphAbelJetGenerators
      (a := a) A D representative i j S
    have hu₀ := restrictedPairMergeExceptionalGraphTargetArgument_mem_base
      (a := a) A D representative i j S t
    exact restrictedExpressionBase_mono
      (restrictedPairMergeExceptionalGraphBox D
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
      (fun f hf ↦ Or.inr hf) hu₀
  let T := iterateETower base u d hu
  have hjet : ∀ q : ℕ,
      (fun z ↦ iteratedDeriv q A (u z)) ∈ T.level d := by
    intro q
    exact T.base_mem_level
      (restrictedPairMergeExceptionalGraphTargetJet_mem_commonBase
        (a := a) A D representative offset i j S t q) d
  have horbit : ∀ e < d,
      (fun z ↦ Real.exp (E^[e] (u z))) ∈ T.level d := by
    intro e he
    have hg := T.generator_mem_level_of_lt (⟨e, he⟩ : Fin d) he
    change (fun z ↦ Real.exp (E^[e] (u z))) ∈ T.level d at hg
    exact hg
  have hden := iteratedAbelDerivativeDenominator_mem_subalgebra_bounded
    (T.level d) u d (fun e he q ↦
      realExp_nat_mul_mem_subalgebra (T.level d)
        (fun z ↦ E^[e] (u z)) (horbit e he) q) r
  have hnum := iteratedAbelDerivativeNumerator_mem_subalgebra_bounded_of_exp_orbit
    (T.level d) A u hjet d horbit r
  exact ⟨T, hden, hnum⟩

/-- All exceptional derivative data through the maximum order actually used
by the compressed family lie in one explicitly concatenated common-base
tower. -/
theorem exists_commonTower_restrictedPairMergeExceptionalDerivativeData_commonBase
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
    let R := restrictedPairMergeExceptionalOrderBound S
    ∃ l : ℕ, ∃ T : RestrictedExpressionTower
        (restrictedPairMergeExceptionalGraphBox D N)
        (restrictedPairMergeExceptionalCommonJetGenerators
          (a := a) A D representative offset i j S) (ell := l),
      (∀ t : Fin N, ∀ r ≤ R,
        (fun z ↦ iteratedAbelDerivativeDenominator
          (restrictedPairMergeExceptionalDepth representative K k i
            (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t))
          r (restrictedPairMergeExceptionalGraphTargetArgument
            (a := a) D representative i j S t z)) ∈ T.level l) ∧
      ∀ t : Fin N, ∀ r ≤ R,
        (fun z ↦ iteratedAbelDerivativeNumerator A
          (restrictedPairMergeExceptionalDepth representative K k i
            (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t))
          r (restrictedPairMergeExceptionalGraphTargetArgument
            (a := a) D representative i j S t z)) ∈ T.level l := by
  dsimp only
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let R := restrictedPairMergeExceptionalOrderBound S
  let base := restrictedPairMergeCompressedCommonBase
    (a := a) A D representative offset i j S
  let datum := restrictedPairMergeExceptionalDerivativeDatum
    (a := a) A D representative K k i j S
  have hdatum : ∀ h : (Fin N × Fin (R + 1)) × Bool,
      ∃ l : ℕ, ∃ T : FiniteExponentialTower base l,
        datum h ∈ T.level l := by
    intro h
    let d := restrictedPairMergeExceptionalDepth representative K k i
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S h.1.1)
    obtain ⟨T, hden, hnum⟩ :=
      exists_tower_restrictedPairMergeExceptionalDerivativeData_commonBase
        (a := a) A D representative offset i j S h.1.1 d h.1.2.val
    refine ⟨d, T, ?_⟩
    cases hb : h.2 with
    | false =>
        change (if h.2 then _ else _) ∈ T.level d
        rw [hb]
        exact hden
    | true =>
        change (if h.2 then _ else _) ∈ T.level d
        rw [hb]
        exact hnum
  obtain ⟨l, T, hT⟩ :=
    exists_common_finiteExponentialTower base datum hdatum
  refine ⟨l, T, ?_, ?_⟩
  · intro t r hr
    let r' : Fin (R + 1) := ⟨r, Nat.lt_succ_of_le hr⟩
    have hm := hT ((t, r'), false)
    simpa [datum, restrictedPairMergeExceptionalDerivativeDatum] using hm
  · intro t r hr
    let r' : Fin (R + 1) := ⟨r, Nat.lt_succ_of_le hr⟩
    have hm := hT ((t, r'), true)
    simpa [datum, restrictedPairMergeExceptionalDerivativeDatum] using hm

/-- One exceptional graph equation has an explicit two-orbit tower directly
over the enlarged common base. -/
theorem exists_tower_restrictedPairMergeExceptionalGraphEquation_commonBase
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    let d := restrictedPairMergeExceptionalDepth representative K k i
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)
    ∃ T : FiniteExponentialTower
        (restrictedPairMergeCompressedCommonBase
          (a := a) A D representative offset i j S) (d + d),
      restrictedPairMergeExceptionalRestrictedGraphEquation
        D representative offset K k i j S t ∈ T.level (d + d) := by
  dsimp only
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let G₀ := restrictedPairMergeExceptionalGraphAbelJetGenerators
    (a := a) A D representative i j S
  let base₀ := restrictedExpressionBase
    (restrictedPairMergeExceptionalGraphBox D N) G₀
  let base := restrictedPairMergeCompressedCommonBase
    (a := a) A D representative offset i j S
  have hbase : base₀ ≤ base :=
    restrictedExpressionBase_mono
      (restrictedPairMergeExceptionalGraphBox D N) (fun f hf ↦ Or.inr hf)
  let d := restrictedPairMergeExceptionalDepth representative K k i
    (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)
  let v := restrictedPairMergeExceptionalGraphBaseArgument
    (p := p) (a := a) representative i j S t
  let eta := restrictedWCoordinate (m := m + 1) (a := a)
    (Fin.natAdd (p + 1) t)
  let b : RestrictedPairMergeExceptionalGraphSource
      (p := p) (a := a) representative i j S → ℝ :=
    fun z ↦
      (restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ)
        (restrictedPairMergeExceptionalGraphBoxDropCLM p N z.1.2)
  have hv : v ∈ base := hbase
    (restrictedPairMergeExceptionalGraphBaseArgument_mem_base
      (a := a) A D representative i j S t)
  have heta : eta ∈ base :=
    restrictedWCoordinate_mem_base
      (restrictedPairMergeExceptionalGraphBox D N)
      (restrictedPairMergeExceptionalCommonJetGenerators
        (a := a) A D representative offset i j S) _
  have hb : b ∈ base := hbase
    (restrictedPairMergeExceptionalOldOffset_graphPullback_mem_base
      (a := a) A D representative offset i j S t)
  have hveta : v + eta ∈ base := base.add_mem hv heta
  let T₁ := iterateETower base (v + eta) d hveta
  have hv₁ : v ∈ T₁.level d := T₁.base_mem_level hv d
  let T₂ := iterateETower (T₁.level d) v d hv₁
  let T := T₁.append T₂
  refine ⟨T, ?_⟩
  have hfirst₀ := iterateE_mem_iterateETower_terminal base (v + eta) d hveta
  have hfirstD : (fun z ↦ E^[d] ((v + eta) z)) ∈ T.level d := by
    rw [show T.level d = T₁.level d by
      exact FiniteExponentialTower.append_level_left T₁ T₂ d le_rfl]
    exact hfirst₀
  have hfirst : (fun z ↦ E^[d] ((v + eta) z)) ∈ T.level (d + d) :=
    T.level_mono (Nat.le_add_right d d) hfirstD
  have hsecond₀ := iterateE_mem_iterateETower_terminal (T₁.level d) v d hv₁
  have hsecond : (fun z ↦ E^[d] (v z)) ∈ T.level (d + d) := by
    rw [show T.level (d + d) = T₂.level d by
      exact FiniteExponentialTower.append_level_right T₁ T₂ d]
    exact hsecond₀
  have hbT : b ∈ T.level (d + d) := T.base_mem_level hb (d + d)
  have hmem := (T.level (d + d)).sub_mem
    ((T.level (d + d)).sub_mem hfirst hsecond) hbT
  change (fun z ↦ E^[d] (v z + eta z) - E^[d] (v z) - b z) ∈ T.level (d + d)
  change (fun z ↦ E^[d] (v z + eta z) - E^[d] (v z) - b z) ∈ T.level (d + d) at hmem
  exact hmem

/-- Explicit finite concatenation puts all graph equations in one
common-base tower. -/
theorem exists_commonTower_restrictedPairMergeExceptionalGraphEquations_commonBase
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
    ∃ l : ℕ, ∃ T : RestrictedExpressionTower
        (restrictedPairMergeExceptionalGraphBox D N)
        (restrictedPairMergeExceptionalCommonJetGenerators
          (a := a) A D representative offset i j S) (ell := l),
      ∀ t : Fin N,
        restrictedPairMergeExceptionalRestrictedGraphEquation
          D representative offset K k i j S t ∈ T.level l := by
  dsimp only
  let base := restrictedPairMergeCompressedCommonBase
    (a := a) A D representative offset i j S
  apply exists_common_finiteExponentialTower base
    (restrictedPairMergeExceptionalRestrictedGraphEquation
      D representative offset K k i j S)
  intro t
  let d := restrictedPairMergeExceptionalDepth representative K k i
    (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)
  obtain ⟨T, hT⟩ :=
    exists_tower_restrictedPairMergeExceptionalGraphEquation_commonBase
      (a := a) A D representative offset K k i j S t
  exact ⟨d + d, T, hT⟩

/-- The finitely many pulled representative-coordinate symbols lie in one
common-base tower. -/
theorem exists_commonTower_restrictedPairMergeOldFreeSymbols_commonBase
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    ∃ l : ℕ, ∃ T : RestrictedExpressionTower
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
        (restrictedPairMergeExceptionalCommonJetGenerators
          (a := a) A D representative offset i j S) (ell := l),
      ∀ u : Fin ((m + 1) + 1),
        restrictedPairMergeCompressedOldSymbol A D representative offset K k i j S
          (Sum.inr (Sum.inl u)) ∈ T.level l := by
  let base := restrictedPairMergeCompressedCommonBase
    (a := a) A D representative offset i j S
  exact exists_common_finiteExponentialTower base
    (fun u : Fin ((m + 1) + 1) ↦
      restrictedPairMergeCompressedOldSymbol A D representative offset K k i j S
        (Sum.inr (Sum.inl u)))
    (exists_tower_restrictedPairMergeCompressedOldFreeSymbol
      A D representative offset K k i j S)

/-- The derivative-data tower and coordinate tower concatenate to one tower
containing every per-symbol denominator and numerator. -/
theorem exists_commonTower_restrictedPairMergeCompressedSymbolData
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    ∃ l : ℕ, ∃ T : RestrictedExpressionTower
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
        (restrictedPairMergeExceptionalCommonJetGenerators
          (a := a) A D representative offset i j S) (ell := l),
      (∀ s, restrictedPairMergeCompressedSymbolDenominator
          A D representative offset K k i j S s ∈ T.level l) ∧
      ∀ s, restrictedPairMergeCompressedSymbolNumerator
          A D representative offset K k i j S s ∈ T.level l := by
  classical
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let base := restrictedPairMergeCompressedCommonBase
    (a := a) A D representative offset i j S
  obtain ⟨ld, Td, hdenD, hnumD⟩ :=
    exists_commonTower_restrictedPairMergeExceptionalDerivativeData_commonBase
      (a := a) A D representative offset K k i j S
  obtain ⟨lf, Tf, hfree⟩ :=
    exists_commonTower_restrictedPairMergeOldFreeSymbols_commonBase
      (a := a) A D representative offset K k i j S
  let T := Td.appendSameBase Tf
  have hden : ∀ s, restrictedPairMergeCompressedSymbolDenominator
      A D representative offset K k i j S s ∈ T.level (ld + lf) := by
    intro s
    rcases s with y | s
    · simpa [restrictedPairMergeCompressedSymbolDenominator] using
        T.base_mem_level base.one_mem (ld + lf)
    · rcases s with u | v
      · simpa [restrictedPairMergeCompressedSymbolDenominator] using
          T.base_mem_level base.one_mem (ld + lf)
      · by_cases hv : representative (restrictedJetEnumeration S v).1 = i ∨
            representative (restrictedJetEnumeration S v).1 = i.succAbove j
        · let t := restrictedPairMergeSelectedExceptionalIndex
            representative i j S v hv
          have hr := restrictedJetEnumeration_order_le_exceptionalOrderBound S v
          have hm := hdenD t (restrictedJetEnumeration S v).2 hr
          have ht : restrictedPairMergeExceptionalOffsetEnumeration
              representative i j S t = (restrictedJetEnumeration S v).1 := by
            dsimp [t]
            exact restrictedPairMergeExceptionalOffsetEnumeration_selectedIndex
              representative i j S v hv
          rw [ht] at hm
          apply Td.mem_appendSameBase_left Tf
          simp only [restrictedPairMergeCompressedSymbolDenominator, hv, dite_true]
          exact hm
        · simpa [restrictedPairMergeCompressedSymbolDenominator, hv] using
            T.base_mem_level base.one_mem (ld + lf)
  have hnum : ∀ s, restrictedPairMergeCompressedSymbolNumerator
      A D representative offset K k i j S s ∈ T.level (ld + lf) := by
    intro s
    rcases s with y | s
    · exact T.base_mem_level
        (restrictedPairMergeCompressedOldAuxSymbol_mem_commonBase
          A D representative offset K k i j S y) (ld + lf)
    · rcases s with u | v
      · exact Td.mem_appendSameBase_right Tf (hfree u)
      · by_cases hv : representative (restrictedJetEnumeration S v).1 = i ∨
            representative (restrictedJetEnumeration S v).1 = i.succAbove j
        · let t := restrictedPairMergeSelectedExceptionalIndex
            representative i j S v hv
          have hr := restrictedJetEnumeration_order_le_exceptionalOrderBound S v
          have hm := hnumD t (restrictedJetEnumeration S v).2 hr
          have ht : restrictedPairMergeExceptionalOffsetEnumeration
              representative i j S t = (restrictedJetEnumeration S v).1 := by
            dsimp [t]
            exact restrictedPairMergeExceptionalOffsetEnumeration_selectedIndex
              representative i j S v hv
          rw [ht] at hm
          apply Td.mem_appendSameBase_left Tf
          simp only [restrictedPairMergeCompressedSymbolNumerator, hv, dite_true]
          exact hm
        · have hm :=
            restrictedPairMergeCompressedOldSelectedSymbol_mem_commonBase_of_not_exceptional
              (a := a) A D representative offset K k i j S v hv
          simpa only [restrictedPairMergeCompressedSymbolNumerator, hv, dite_false] using
            T.base_mem_level hm (ld + lf)
  exact ⟨ld + lf, T, hden, hnum⟩

/-- The transformed system appends one graph equation for each exceptional
offset label to the denominator-cleared old square family. -/
def restrictedPairMergeDenominatorClearedAugmentedEquationFamily
    (A : ℝ → ℝ) {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    Fin (n + (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) →
      RestrictedPairMergeExceptionalGraphSource
        (p := p) (a := a) representative i j S → ℝ :=
  Fin.addCases
    (restrictedPairMergeDenominatorClearedCompressedEquation
      A D representative offset K k i j S Q)
    (restrictedPairMergeExceptionalRestrictedGraphEquation
      D representative offset K k i j S)

/-- Terminal-level membership of the full denominator-cleared transformed
square system: cleared old rows followed by all exceptional graph rows. -/
theorem exists_commonTower_restrictedPairMergeDenominatorClearedAugmentedEquationFamily
    (A : ℝ → ℝ) {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    ∃ l : ℕ, ∃ T : RestrictedExpressionTower
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
        (restrictedPairMergeExceptionalCommonJetGenerators
          (a := a) A D representative offset i j S) (ell := l),
      ∀ e, restrictedPairMergeDenominatorClearedAugmentedEquationFamily
        A D representative offset K k i j S Q e ∈ T.level l := by
  classical
  let base := restrictedPairMergeCompressedCommonBase
    (a := a) A D representative offset i j S
  obtain ⟨ldata, Tdata, hden, hnum⟩ :=
    exists_commonTower_restrictedPairMergeCompressedSymbolData
      (a := a) A D representative offset K k i j S
  obtain ⟨lgraph, Tgraph, hgraph⟩ :=
    exists_commonTower_restrictedPairMergeExceptionalGraphEquations_commonBase
      (a := a) A D representative offset K k i j S
  let T := Tdata.appendSameBase Tgraph
  have hdenT : ∀ s, restrictedPairMergeCompressedSymbolDenominator
      A D representative offset K k i j S s ∈ T.level (ldata + lgraph) := by
    intro s
    exact Tdata.mem_appendSameBase_left Tgraph (hden s)
  have hnumT : ∀ s, restrictedPairMergeCompressedSymbolNumerator
      A D representative offset K k i j S s ∈ T.level (ldata + lgraph) := by
    intro s
    exact Tdata.mem_appendSameBase_left Tgraph (hnum s)
  have hgraphT : ∀ t,
      restrictedPairMergeExceptionalRestrictedGraphEquation
        D representative offset K k i j S t ∈ T.level (ldata + lgraph) := by
    intro t
    exact Tdata.mem_appendSameBase_right Tgraph (hgraph t)
  have hrow : ∀ row, restrictedPairMergeDenominatorClearedCompressedEquation
      A D representative offset K k i j S Q row ∈ T.level (ldata + lgraph) := by
    intro row
    apply finiteCommonDenominatorMvPolynomialFamilyEval_mem_subalgebra
      (T.level (ldata + lgraph))
      (restrictedPairMergeExceptionalCoefficientRingHom
        (a := a) D representative i j S)
      (restrictedPairMergeCompressedSymbolDenominator
        A D representative offset K k i j S)
      (restrictedPairMergeCompressedSymbolNumerator
        A D representative offset K k i j S) Q
    · intro row' d hd
      exact T.base_mem_level
        (restrictedPairMergeExceptionalCoefficientRingHom_mem_commonBase
          A D representative offset i j S ((Q row').coeff d))
        (ldata + lgraph)
    · exact hdenT
    · exact hnumT
  refine ⟨ldata + lgraph, T, ?_⟩
  intro e
  refine Fin.addCases (fun row ↦ ?_) (fun t ↦ ?_) e
  · simpa [restrictedPairMergeDenominatorClearedAugmentedEquationFamily] using hrow row
  · simpa [restrictedPairMergeDenominatorClearedAugmentedEquationFamily] using hgraphT t

/-- End-to-end finite compression and terminal-tower package for an old
finite base equation family. -/
theorem exists_restrictedPairMergeDenominatorClearedCompressedSystem
    (A : ℝ → ℝ) {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (F : Fin n → RestrictedSource ((m + 1) + 1) p a → ℝ)
    (hF : ∀ row, F row ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)) :
    ∃ S : Finset (ι × ℕ),
      ∃ Q : Fin n → MvPolynomial (PaperRankSymbols ((m + 1) + 1) a S.card)
          (RestrictedBox.analyticNearClosedBoxSubalgebra D),
      ∃ C : Finset (RestrictedBox.analyticNearClosedBoxSubalgebra D),
        (∀ row d, d ∈ (Q row).support → (Q row).coeff d ∈ C) ∧
        (∀ row, restrictedPaperPolynomialValue A D representative offset
          (restrictedJetEnumeration S) (Q row) = F row) ∧
        ∃ l : ℕ, ∃ T : RestrictedExpressionTower
            (restrictedPairMergeExceptionalGraphBox D
              (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
            (restrictedPairMergeExceptionalCommonJetGenerators
              (a := a) A D representative offset i j S) (ell := l),
          ∀ e, restrictedPairMergeDenominatorClearedAugmentedEquationFamily
            A D representative offset K k i j S Q e ∈ T.level l := by
  obtain ⟨S, Q, C, hC, hQ, hsupport⟩ :=
    exists_pairMergeFiniteEquationJetSupport
      A D representative offset i j F hF
  obtain ⟨l, T, hT⟩ :=
    exists_commonTower_restrictedPairMergeDenominatorClearedAugmentedEquationFamily
      (a := a) A D representative offset K k i j S Q
  exact ⟨S, Q, C, hC, hQ, l, T, hT⟩

end AbelFormalization
