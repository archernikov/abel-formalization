import AbelFormalization.RestrictedPairMergeExceptionalCommonTower
import AbelFormalization.MvPolynomialDenominatorClearing
import AbelFormalization.FiniteCommonDenominatorPolynomial

/-!
# A common denominator and common tower for a compressed pair-merge system
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- The canonical graph-coordinate label corresponding to a selected
exceptional jet. -/
noncomputable def restrictedPairMergeSelectedExceptionalIndex
    {m : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) (v : Fin S.card)
    (hv : representative (restrictedJetEnumeration S v).1 = i ∨
      representative (restrictedJetEnumeration S v).1 = i.succAbove j) :
    Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card := by
  classical
  let qr := restrictedJetEnumeration S v
  have hqr : qr ∈ S := by
    change (S.equivFin.symm v).1 ∈ S
    exact (S.equivFin.symm v).2
  exact (restrictedPairMergeExceptionalOffsetSupport representative i j S).equivFin
    ⟨qr.1, (mem_restrictedPairMergeExceptionalOffsetSupport_iff
      representative i j S qr.1).2 ⟨⟨qr.2, hqr⟩, hv⟩⟩

@[simp]
theorem restrictedPairMergeExceptionalOffsetEnumeration_selectedIndex
    {m : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) (v : Fin S.card)
    (hv : representative (restrictedJetEnumeration S v).1 = i ∨
      representative (restrictedJetEnumeration S v).1 = i.succAbove j) :
    restrictedPairMergeExceptionalOffsetEnumeration representative i j S
        (restrictedPairMergeSelectedExceptionalIndex representative i j S v hv) =
      (restrictedJetEnumeration S v).1 := by
  classical
  simp [restrictedPairMergeExceptionalOffsetEnumeration,
    restrictedPairMergeSelectedExceptionalIndex]

/-- The enlarged source carrying the finite exceptional graph block. -/
abbrev RestrictedPairMergeExceptionalGraphSource
    {m p a : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :=
  RestrictedSource (m + 1)
    ((p + 1) +
      (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) a

/-- The common enlarged base containing ordinary pulled jets and standard
jets attached to all exceptional graph coordinates. -/
abbrev restrictedPairMergeCompressedCommonBase
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :=
  restrictedExpressionBase
    (restrictedPairMergeExceptionalGraphBox D
      (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    (restrictedPairMergeExceptionalCommonJetGenerators
      (a := a) A D representative offset i j S)

private def zeroFiniteExponentialTower
    {X : Type*} (base : Subalgebra ℝ (X → ℝ)) :
    FiniteExponentialTower base 0 where
  exponent := fun e ↦ Fin.elim0 e
  exponent_mem_level := fun e ↦ Fin.elim0 e

private theorem exists_tower_of_mem_base
    {X : Type*} (base : Subalgebra ℝ (X → ℝ))
    {f : X → ℝ} (hf : f ∈ base) :
    ∃ l : ℕ, ∃ T : FiniteExponentialTower base l,
      f ∈ T.level l := by
  let T := zeroFiniteExponentialTower base
  exact ⟨0, T, T.base_mem_level hf 0⟩

/-- Analytic coefficients of the compressed old system, pulled first to the
pair box and then to the finite exceptional graph box. -/
def restrictedPairMergeExceptionalCoefficientRingHom
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    RestrictedBox.analyticNearClosedBoxSubalgebra D →+*
      (RestrictedPairMergeExceptionalGraphSource
        (p := p) (a := a) representative i j S → ℝ) where
  toFun c z :=
    (D.pullbackPairMergeExceptionalGraph
      (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
      (D.pullbackSnoc (-1) 1 (by norm_num) c) :
      RestrictedBoxSpace
        ((p + 1) +
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) → ℝ)
      z.1.2
  map_zero' := by funext z; rfl
  map_one' := by funext z; rfl
  map_add' c d := by funext z; rfl
  map_mul' c d := by funext z; rfl

/-- The original compressed symbol assignment after pair merge, regarded as
a function on the graph source by forgetting the graph block. -/
def restrictedPairMergeCompressedOldSymbol
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    PaperRankSymbols ((m + 1) + 1) a S.card →
      RestrictedPairMergeExceptionalGraphSource
        (p := p) (a := a) representative i j S → ℝ :=
  fun s z ↦ paperRankSymbolArgument
    (restrictedSelectedAbelJets A representative offset
      (restrictedJetEnumeration S))
    (restrictedPairMergeSourceMap K k i j
      (restrictedPairMergeExceptionalGraphDrop z)) s

/-- Per-symbol denominator.  Only selected jets carried by the pivot or its
retained partner receive a nontrivial positive denominator. -/
def restrictedPairMergeCompressedSymbolDenominator
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    PaperRankSymbols ((m + 1) + 1) a S.card →
      RestrictedPairMergeExceptionalGraphSource
        (p := p) (a := a) representative i j S → ℝ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr v) =>
      if hv : representative (restrictedJetEnumeration S v).1 = i ∨
          representative (restrictedJetEnumeration S v).1 = i.succAbove j then
        let t := restrictedPairMergeSelectedExceptionalIndex representative i j S v hv
        let d := restrictedPairMergeExceptionalDepth representative K k i
          (restrictedJetEnumeration S v).1
        let r := (restrictedJetEnumeration S v).2
        fun z ↦ iteratedAbelDerivativeDenominator d r
          (restrictedPairMergeExceptionalGraphTargetArgument
            (a := a) D representative i j S t z)
      else 1

/-- Per-symbol numerator, written without division.  Exceptional selected
jets use the iterated derivative numerator; every other symbol is unchanged. -/
def restrictedPairMergeCompressedSymbolNumerator
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    PaperRankSymbols ((m + 1) + 1) a S.card →
      RestrictedPairMergeExceptionalGraphSource
        (p := p) (a := a) representative i j S → ℝ
  | s@(Sum.inl _) => restrictedPairMergeCompressedOldSymbol
      A D representative offset K k i j S s
  | s@(Sum.inr (Sum.inl _)) => restrictedPairMergeCompressedOldSymbol
      A D representative offset K k i j S s
  | s@(Sum.inr (Sum.inr v)) =>
      if hv : representative (restrictedJetEnumeration S v).1 = i ∨
          representative (restrictedJetEnumeration S v).1 = i.succAbove j then
        let t := restrictedPairMergeSelectedExceptionalIndex representative i j S v hv
        let d := restrictedPairMergeExceptionalDepth representative K k i
          (restrictedJetEnumeration S v).1
        let r := (restrictedJetEnumeration S v).2
        fun z ↦ iteratedAbelDerivativeNumerator A d r
          (restrictedPairMergeExceptionalGraphTargetArgument
            (a := a) D representative i j S t z)
      else restrictedPairMergeCompressedOldSymbol
        A D representative offset K k i j S s

/-- On the finite graph, an exceptional selected old jet is exactly the
uniform pivot/partner exceptional jet. -/
theorem restrictedPairMergeCompressedOldSelectedSymbol_on_graphLift
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) (v : Fin S.card)
    (hv : representative (restrictedJetEnumeration S v).1 = i ∨
      representative (restrictedJetEnumeration S v).1 = i.succAbove j)
    (x : RestrictedSource (m + 1) (p + 1) a) :
    restrictedPairMergeCompressedOldSymbol A D representative offset K k i j S
        (Sum.inr (Sum.inr v))
        (restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S x) =
      restrictedPairMergeExceptionalJet A D representative offset K k i j
        (restrictedJetEnumeration S v).1
        (restrictedJetEnumeration S v).2 x := by
  let q := (restrictedJetEnumeration S v).1
  let r := (restrictedJetEnumeration S v).2
  have hdrop : restrictedPairMergeExceptionalGraphDrop
      (restrictedPairMergeExceptionalFiniteGraphLift
        D representative offset K k i j S x) = x := by
    simp [restrictedPairMergeExceptionalFiniteGraphLift]
  rcases hv with hq | hq
  · let qp : RestrictedPivotOffsetIndex representative i := ⟨q, hq⟩
    calc
      restrictedPairMergeCompressedOldSymbol A D representative offset K k i j S
          (Sum.inr (Sum.inr v))
          (restrictedPairMergeExceptionalFiniteGraphLift
            D representative offset K k i j S x) =
          functionPrecompAlgHom
            (restrictedPairMergeSourceMap (p := p) (a := a) K k i j)
            (restrictedAbelJet A (representative q)
              (offset q : RestrictedBoxSpace p → ℝ) r) x := by
                simp [restrictedPairMergeCompressedOldSymbol, restrictedSelectedAbelJets, q, r, hdrop]
      _ = restrictedPairMergePivotJet A D offset K k j q r x :=
        congrFun (precomp_restrictedAbelJet_pairMerge_pivot
          A D representative offset K k i j qp r) x
      _ = restrictedPairMergeExceptionalJet A D representative offset K k i j
          q r x := congrFun
        (restrictedPairMergeExceptionalJet_eq_pivot
          A D representative offset K k i j q hq r).symm x
  · have hqi : representative q ≠ i := by
      rw [hq]
      exact Fin.succAbove_ne i j
    let qr : RestrictedRetainedOffsetIndex representative i := ⟨q, hqi⟩
    have hrj : restrictedReclassifiedRepresentative representative i qr = j := by
      apply Fin.succAbove_right_injective
      rw [succAbove_restrictedReclassifiedRepresentative, hq]
    let qp : RestrictedPairMergePartnerOffsetIndex representative i j :=
      ⟨qr, hrj⟩
    calc
      restrictedPairMergeCompressedOldSymbol A D representative offset K k i j S
          (Sum.inr (Sum.inr v))
          (restrictedPairMergeExceptionalFiniteGraphLift
            D representative offset K k i j S x) =
          functionPrecompAlgHom
            (restrictedPairMergeSourceMap (p := p) (a := a) K k i j)
            (restrictedAbelJet A (representative q)
              (offset q : RestrictedBoxSpace p → ℝ) r) x := by
                simp [restrictedPairMergeCompressedOldSymbol, restrictedSelectedAbelJets, q, r, hdrop]
      _ = restrictedPairMergePartnerJet A D offset K j q r x :=
        congrFun (precomp_restrictedAbelJet_pairMerge_partner
          A D representative offset K k i j qp r) x
      _ = restrictedPairMergeExceptionalJet A D representative offset K k i j
          q r x := congrFun
        (restrictedPairMergeExceptionalJet_eq_partner
          A D representative offset K k i j q hq r).symm x

/-- Every compressed symbol has its stated denominator identity on the
finite exceptional graph tail. -/
theorem IsAbel.restrictedPairMergeCompressedSymbol_denominator_mul
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t, ∀ w ∈ (restrictedPairMergeBox D).closedBox,
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (s : PaperRankSymbols ((m + 1) + 1) a S.card) :
    restrictedPairMergeCompressedSymbolDenominator
        A D representative offset K k i j S s
        (restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S x) *
      restrictedPairMergeCompressedOldSymbol
        A D representative offset K k i j S s
        (restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S x) =
    restrictedPairMergeCompressedSymbolNumerator
        A D representative offset K k i j S s
        (restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S x) := by
  rcases s with y | s
  · simp [restrictedPairMergeCompressedSymbolDenominator,
      restrictedPairMergeCompressedSymbolNumerator]
  · rcases s with u | v
    · simp [restrictedPairMergeCompressedSymbolDenominator,
        restrictedPairMergeCompressedSymbolNumerator]
    · by_cases hv : representative (restrictedJetEnumeration S v).1 = i ∨
          representative (restrictedJetEnumeration S v).1 = i.succAbove j
      · let t := restrictedPairMergeSelectedExceptionalIndex
          representative i j S v hv
        have hid := hA.restrictedPairMergeExceptionalJet_denominator_mul_eq_numerator
          D representative offset (k := k) hK i j S t
          (restrictedJetEnumeration S v).2 (hB t) (hbB t) x (htail t) hw
        rw [restrictedPairMergeCompressedOldSelectedSymbol_on_graphLift
          A D representative offset K k i j S v hv x]
        simpa [restrictedPairMergeCompressedSymbolDenominator,
          restrictedPairMergeCompressedSymbolNumerator, hv, t] using hid
      · simp [restrictedPairMergeCompressedSymbolDenominator,
          restrictedPairMergeCompressedSymbolNumerator, hv]

/-- The denominator-cleared compressed equation family on the enlarged
graph source. -/
def restrictedPairMergeDenominatorClearedCompressedEquation
    (A : ℝ → ℝ) {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    Fin n → RestrictedPairMergeExceptionalGraphSource
      (p := p) (a := a) representative i j S → ℝ :=
  finiteCommonDenominatorMvPolynomialFamilyEval
    (restrictedPairMergeExceptionalCoefficientRingHom
      (a := a) D representative i j S)
    (restrictedPairMergeCompressedSymbolDenominator
      A D representative offset K k i j S)
    (restrictedPairMergeCompressedSymbolNumerator
      A D representative offset K k i j S) Q

theorem restrictedPairMergeCompressedSymbolDenominator_pos
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (s : PaperRankSymbols ((m + 1) + 1) a S.card)
    (z : RestrictedPairMergeExceptionalGraphSource
      (p := p) (a := a) representative i j S) :
    0 < restrictedPairMergeCompressedSymbolDenominator
      A D representative offset K k i j S s z := by
  rcases s with y | s
  · simp [restrictedPairMergeCompressedSymbolDenominator]
  · rcases s with u | v
    · simp [restrictedPairMergeCompressedSymbolDenominator]
    · by_cases hv : representative (restrictedJetEnumeration S v).1 = i ∨
          representative (restrictedJetEnumeration S v).1 = i.succAbove j
      · simp only [restrictedPairMergeCompressedSymbolDenominator, hv,
          dite_true]
        exact restrictedPairMergeExceptionalJet_denominator_pos
          D representative i j S
          (restrictedPairMergeSelectedExceptionalIndex representative i j S v hv)
          (restrictedPairMergeExceptionalDepth representative K k i
            (restrictedJetEnumeration S v).1)
          (restrictedJetEnumeration S v).2 z
      · simp [restrictedPairMergeCompressedSymbolDenominator, hv]

theorem restrictedPairMergeCompressedCommonDenominator_pos
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (z : RestrictedPairMergeExceptionalGraphSource
      (p := p) (a := a) representative i j S) :
    0 < finiteCommonDenominator
      (fun s : PaperRankSymbols ((m + 1) + 1) a S.card ↦
        restrictedPairMergeCompressedSymbolDenominator
          A D representative offset K k i j S s z) :=
  finiteCommonDenominator_pos _ fun s ↦
    restrictedPairMergeCompressedSymbolDenominator_pos
      A D representative offset K k i j S s z

/-- A selected jet outside the pivot/partner pair is one of the ordinary
special generators in the common enlarged base. -/
theorem restrictedPairMergeCompressedOldSelectedSymbol_mem_commonBase_of_not_exceptional
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) (v : Fin S.card)
    (hv : ¬ (representative (restrictedJetEnumeration S v).1 = i ∨
      representative (restrictedJetEnumeration S v).1 = i.succAbove j)) :
    restrictedPairMergeCompressedOldSymbol A D representative offset K k i j S
        (Sum.inr (Sum.inr v)) ∈
      restrictedExpressionBase
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
        (restrictedPairMergeExceptionalCommonJetGenerators
          (a := a) A D representative offset i j S) := by
  let q := (restrictedJetEnumeration S v).1
  let r := (restrictedJetEnumeration S v).2
  have hqi : representative q ≠ i := fun h ↦ hv (Or.inl h)
  let qr : RestrictedRetainedOffsetIndex representative i := ⟨q, hqi⟩
  have hrj : restrictedReclassifiedRepresentative representative i qr ≠ j := by
    intro h
    apply hv
    right
    rw [← h, succAbove_restrictedReclassifiedRepresentative]
  let qo : RestrictedPairMergeOrdinaryOffsetIndex representative i j := ⟨qr, hrj⟩
  let f := restrictedAbelJet (a := a) A
    (restrictedPairMergeOrdinaryRepresentative representative i j qo)
    (restrictedPairMergeOrdinaryOffset D representative offset i j qo :
      RestrictedBoxSpace (p + 1) → ℝ) r
  have hf : f ∈ restrictedPairMergeOrdinaryAbelJetGenerators
      (a := a) A D representative offset i j := by
    exact ⟨(qo, r), rfl⟩
  have hgraph : functionPrecompAlgHom
      (restrictedPairMergeExceptionalGraphDrop
        (m := m) (p := p) (a := a)
        (N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card))
      f ∈ restrictedPairMergeOrdinaryGraphJetGenerators
        A D representative offset i j S := ⟨f, hf, rfl⟩
  have hmem := specialGenerator_mem_base
    (D := restrictedPairMergeExceptionalGraphBox D
      (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    (specialGenerators := restrictedPairMergeExceptionalCommonJetGenerators
      (a := a) A D representative offset i j S)
    (f := functionPrecompAlgHom
      (restrictedPairMergeExceptionalGraphDrop
        (m := m) (p := p) (a := a)
        (N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)) f)
    (Or.inl hgraph :
      functionPrecompAlgHom
        (restrictedPairMergeExceptionalGraphDrop
          (m := m) (p := p) (a := a)
          (N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card))
        f ∈ restrictedPairMergeExceptionalCommonJetGenerators
          (a := a) A D representative offset i j S)
  have hord := precomp_restrictedAbelJet_pairMerge_ordinary
    (a := a) A D representative offset K k i j qo r
  convert hmem using 1
  funext z
  have hz := congrFun hord (restrictedPairMergeExceptionalGraphDrop z)
  simpa [restrictedPairMergeCompressedOldSymbol,
    restrictedSelectedAbelJets, q, r, f] using hz

/-- Every analytic coefficient in the old compressed family stays in the
fixed part of the common enlarged base. -/
theorem restrictedPairMergeExceptionalCoefficientRingHom_mem_commonBase
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (c : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    restrictedPairMergeExceptionalCoefficientRingHom
        (a := a) D representative i j S c ∈
      restrictedExpressionBase
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
        (restrictedPairMergeExceptionalCommonJetGenerators
          (a := a) A D representative offset i j S) := by
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let c' := D.pullbackPairMergeExceptionalGraph N
    (D.pullbackSnoc (-1) 1 (by norm_num) c)
  have hc := restrictedBoxCoefficientPullback_mem_base
    (m := m + 1) (a := a)
    (restrictedPairMergeExceptionalGraphBox D N)
    (restrictedPairMergeExceptionalCommonJetGenerators
      (a := a) A D representative offset i j S) c'
  exact hc

/-- Pulled auxiliary symbols already belong to the common enlarged base. -/
theorem restrictedPairMergeCompressedOldAuxSymbol_mem_commonBase
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) (y : Fin a) :
    restrictedPairMergeCompressedOldSymbol A D representative offset K k i j S
        (Sum.inl y) ∈
      restrictedPairMergeCompressedCommonBase A D representative offset i j S := by
  have hy := restrictedAuxCoordinate_mem_base
    (restrictedPairMergeExceptionalGraphBox D
      (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    (restrictedPairMergeExceptionalCommonJetGenerators
      (a := a) A D representative offset i j S) y
  convert hy using 1
  funext z
  rfl

/-- Each pulled old representative coordinate lies in a finite tower over
the common enlarged base.  The pivot and partner use their two explicit
finite iterate orbits; every other coordinate is already in the base. -/
theorem exists_tower_restrictedPairMergeCompressedOldFreeSymbol
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) (u : Fin ((m + 1) + 1)) :
    ∃ l : ℕ, ∃ T : FiniteExponentialTower
        (restrictedPairMergeCompressedCommonBase
          (a := a) A D representative offset i j S) l,
      restrictedPairMergeCompressedOldSymbol A D representative offset K k i j S
        (Sum.inr (Sum.inl u)) ∈ T.level l := by
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let base := restrictedPairMergeCompressedCommonBase
    (a := a) A D representative offset i j S
  by_cases hu : u = i
  · let ux : RestrictedPairMergeExceptionalGraphSource
        (p := p) (a := a) representative i j S → ℝ :=
      fun z ↦ z.1.1 j + z.1.2 (Fin.castAdd N (Fin.last p))
    have hux : ux ∈ base := by
      exact base.add_mem
        (restrictedSCoordinate_mem_base
          (restrictedPairMergeExceptionalGraphBox D N)
          (restrictedPairMergeExceptionalCommonJetGenerators
            (a := a) A D representative offset i j S) j)
        (restrictedWCoordinate_mem_base
          (restrictedPairMergeExceptionalGraphBox D N)
          (restrictedPairMergeExceptionalCommonJetGenerators
            (a := a) A D representative offset i j S)
          (Fin.castAdd N (Fin.last p)))
    let T := iterateETower base ux (K + k) hux
    refine ⟨K + k, T, ?_⟩
    have hterminal := iterateE_mem_iterateETower_terminal base ux (K + k) hux
    convert hterminal using 1
    funext z
    simp [restrictedPairMergeCompressedOldSymbol, hu, ux,
      restrictedPairMergeExceptionalGraphDrop, N]
  · let qr : RestrictedRetainedOffsetIndex (fun _ : Fin ((m + 1) + 1) ↦ u) i :=
      ⟨0, hu⟩
    let r : Fin (m + 1) := restrictedReclassifiedRepresentative
      (fun _ : Fin ((m + 1) + 1) ↦ u) i qr
    have hur : i.succAbove r = u := by
      exact succAbove_restrictedReclassifiedRepresentative
        (fun _ : Fin ((m + 1) + 1) ↦ u) i qr
    by_cases hrj : r = j
    · let us : RestrictedPairMergeExceptionalGraphSource
          (p := p) (a := a) representative i j S → ℝ := fun z ↦ z.1.1 j
      have hus : us ∈ base := restrictedSCoordinate_mem_base
        (restrictedPairMergeExceptionalGraphBox D N)
        (restrictedPairMergeExceptionalCommonJetGenerators
          (a := a) A D representative offset i j S) j
      let T := iterateETower base us K hus
      refine ⟨K, T, ?_⟩
      have hterminal := iterateE_mem_iterateETower_terminal base us K hus
      convert hterminal using 1
      funext z
      rw [← hur, hrj]
      simp [restrictedPairMergeCompressedOldSymbol, us,
        restrictedPairMergeExceptionalGraphDrop]
    · have hbase : (fun z : RestrictedPairMergeExceptionalGraphSource
          (p := p) (a := a) representative i j S ↦ z.1.1 r) ∈ base :=
        restrictedSCoordinate_mem_base
          (restrictedPairMergeExceptionalGraphBox D N)
          (restrictedPairMergeExceptionalCommonJetGenerators
            (a := a) A D representative offset i j S) r
      apply exists_tower_of_mem_base base
      convert hbase using 1
      funext z
      rw [← hur]
      simp [restrictedPairMergeCompressedOldSymbol,
        restrictedPairMergeExceptionalGraphDrop, hrj]

@[simp]
theorem restrictedPairMergeCompressedOldSymbol_on_graphLift
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (s : PaperRankSymbols ((m + 1) + 1) a S.card) :
    restrictedPairMergeCompressedOldSymbol A D representative offset K k i j S s
        (restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S x) =
      paperRankSymbolArgument
        (restrictedSelectedAbelJets A representative offset
          (restrictedJetEnumeration S))
        (restrictedPairMergeSourceMap K k i j x) s := by
  simp [restrictedPairMergeCompressedOldSymbol,
    restrictedPairMergeExceptionalFiniteGraphLift]

@[simp]
theorem restrictedPairMergeExceptionalCoefficientRingHom_on_graphLift
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (c : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (x : RestrictedSource (m + 1) (p + 1) a) :
    restrictedPairMergeExceptionalCoefficientRingHom
        (a := a) D representative i j S c
        (restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S x) =
      subalgebraPointEval
        (RestrictedBox.analyticNearClosedBoxSubalgebra D)
        (restrictedPairMergeSourceMap K k i j x).1.2 c := by
  apply congrArg (c : RestrictedBoxSpace p → ℝ)
  funext q
  simp [restrictedPairMergeExceptionalCoefficientRingHom,
    restrictedPairMergeExceptionalFiniteGraphLift,
    restrictedPairMergeSourceMap_box]

/-- On the quantitative graph tail, every denominator-cleared compressed row
is exactly a positive common power times the original pulled equation. -/
theorem IsAbel.restrictedPairMergeDenominatorClearedCompressedEquation_on_graphLift
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (F : Fin n → RestrictedSource ((m + 1) + 1) p a → ℝ)
    (hQ : ∀ row, restrictedPaperPolynomialValue A D representative offset
      (restrictedJetEnumeration S) (Q row) = F row)
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t, ∀ w ∈ (restrictedPairMergeBox D).closedBox,
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (row : Fin n) :
    let z := restrictedPairMergeExceptionalFiniteGraphLift
      D representative offset K k i j S x
    finiteCommonDenominator
        (fun s : PaperRankSymbols ((m + 1) + 1) a S.card ↦
          restrictedPairMergeCompressedSymbolDenominator
            A D representative offset K k i j S s z) ^
        mvPolynomialFamilyTotalDegree Q *
      F row (restrictedPairMergeSourceMap K k i j x) =
    restrictedPairMergeDenominatorClearedCompressedEquation
      A D representative offset K k i j S Q row z := by
  dsimp only
  let z := restrictedPairMergeExceptionalFiniteGraphLift
    D representative offset K k i j S x
  let den := fun s : PaperRankSymbols ((m + 1) + 1) a S.card ↦
    restrictedPairMergeCompressedSymbolDenominator
      A D representative offset K k i j S s z
  let num := fun s : PaperRankSymbols ((m + 1) + 1) a S.card ↦
    restrictedPairMergeCompressedSymbolNumerator
      A D representative offset K k i j S s z
  let old := fun s : PaperRankSymbols ((m + 1) + 1) a S.card ↦
    restrictedPairMergeCompressedOldSymbol
      A D representative offset K k i j S s z
  have hcoordinate : ∀ s, den s * old s = num s := by
    intro s
    exact hA.restrictedPairMergeCompressedSymbol_denominator_mul
      D representative offset hK i j S B hB hbB x htail hw s
  have hclear := finiteCommonDenominator_family_pow_mul_eval₂_eq
    (subalgebraPointEval
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)
      (restrictedPairMergeSourceMap K k i j x).1.2)
    den num old Q hcoordinate row
  have hvalue := congrFun (hQ row) (restrictedPairMergeSourceMap K k i j x)
  rw [← hvalue]
  unfold restrictedPaperPolynomialValue
  simpa [restrictedPairMergeDenominatorClearedCompressedEquation,
    finiteCommonDenominatorMvPolynomialFamilyEval,
    finiteCommonDenominatorMvPolynomialEval,
    denominatorClearedMvPolynomialEval, finiteCommonDenominator,
    finiteCommonClearedNumerator, den, num, old, z] using hclear

/-- A single finite index type for every denominator and numerator function
which must be put into the common tower. -/
def restrictedPairMergeCompressedSymbolDatum
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    (PaperRankSymbols ((m + 1) + 1) a S.card × Bool) →
      RestrictedPairMergeExceptionalGraphSource
        (p := p) (a := a) representative i j S → ℝ :=
  fun sb ↦ if sb.2 then
    restrictedPairMergeCompressedSymbolNumerator
      A D representative offset K k i j S sb.1
  else restrictedPairMergeCompressedSymbolDenominator
      A D representative offset K k i j S sb.1

end AbelFormalization
