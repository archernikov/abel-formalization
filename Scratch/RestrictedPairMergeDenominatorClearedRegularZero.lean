import AbelFormalization.RestrictedPairMergeCompressedSystemTower
import AbelFormalization.RestrictedPairMergeExceptionalFlatSystem
import AbelFormalization.RestrictedTowerDifferentiability

/-!
# Regular zeros of the denominator-cleared exceptional pair system
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- Labels for the ordinary lower-representative jets and for the appended
exceptional graph jets in one standard restricted Abel family. -/
abbrev RestrictedPairMergeCommonJetIndex
    {m : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :=
  RestrictedPairMergeOrdinaryOffsetIndex representative i j ⊕
    Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card

/-- Representative assignment for the common enlarged Abel family. -/
def restrictedPairMergeCommonJetRepresentative
    {m : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    RestrictedPairMergeCommonJetIndex representative i j S → Fin (m + 1)
  | Sum.inl q => restrictedPairMergeOrdinaryRepresentative representative i j q
  | Sum.inr _ => j

/-- Offset assignment for the common enlarged Abel family. -/
def restrictedPairMergeCommonJetOffset
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    RestrictedPairMergeCommonJetIndex representative i j S →
      RestrictedBox.analyticNearClosedBoxSubalgebra
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
  | Sum.inl q =>
      D.pullbackPairMergeExceptionalGraph
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
        (restrictedPairMergeOrdinaryOffset D representative offset i j q)
  | Sum.inr t =>
      restrictedPairMergeExceptionalGraphTargetOffset D representative i j S t

/-- The generator union used by the compressed common tower is contained in
one standard restricted Abel-jet generator family. -/
theorem restrictedPairMergeExceptionalCommonJetGenerators_subset_common
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    restrictedPairMergeExceptionalCommonJetGenerators
        (a := a) A D representative offset i j S ⊆
      restrictedAbelJetGenerators (a := a) A
        (restrictedPairMergeCommonJetRepresentative representative i j S)
        (restrictedPairMergeCommonJetOffset D representative offset i j S) := by
  intro f hf
  rcases hf with hf | hf
  · rcases hf with ⟨g, hg, rfl⟩
    rcases hg with ⟨qr, rfl⟩
    refine ⟨(Sum.inl qr.1, qr.2), ?_⟩
    funext z
    rfl
  · rcases hf with ⟨tr, rfl⟩
    exact ⟨(Sum.inr tr.1, tr.2), rfl⟩

/-- The common generator union is exactly the standard restricted Abel family
indexed by ordinary labels and exceptional graph labels. -/
theorem restrictedPairMergeExceptionalCommonJetGenerators_eq_common
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    restrictedPairMergeExceptionalCommonJetGenerators
        (a := a) A D representative offset i j S =
      restrictedAbelJetGenerators (a := a) A
        (restrictedPairMergeCommonJetRepresentative representative i j S)
        (restrictedPairMergeCommonJetOffset D representative offset i j S) := by
  apply Set.Subset.antisymm
  · exact restrictedPairMergeExceptionalCommonJetGenerators_subset_common
      (a := a) A D representative offset i j S
  · intro f hf
    rcases hf with ⟨⟨q | t, r⟩, rfl⟩
    · apply Or.inl
      refine ⟨restrictedAbelJet A
          (restrictedPairMergeOrdinaryRepresentative representative i j q)
          (restrictedPairMergeOrdinaryOffset D representative offset i j q :
            RestrictedBoxSpace (p + 1) → ℝ) r, ?_, ?_⟩
      · exact ⟨(q, r), rfl⟩
      · funext z
        rfl
    · exact Or.inr ⟨(t, r), rfl⟩

/-- An ordinary common-family argument on the graph lift is the corresponding
old Abel argument after the pair source map. -/
theorem restrictedPairMergeCommonJetArgument_inl_graphLift
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (q : RestrictedPairMergeOrdinaryOffsetIndex representative i j)
    (x : RestrictedSource (m + 1) (p + 1) a) :
    restrictedAbelArgument
        (restrictedPairMergeCommonJetRepresentative representative i j S
          (Sum.inl q))
        (restrictedPairMergeCommonJetOffset D representative offset i j S
          (Sum.inl q) :
            RestrictedBoxSpace
              ((p + 1) +
                (restrictedPairMergeExceptionalOffsetSupport
                  representative i j S).card) → ℝ)
        (restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S x) =
      restrictedAbelArgument (representative q.1.1)
        (offset q.1.1 : RestrictedBoxSpace p → ℝ)
        (restrictedPairMergeSourceMap K k i j x) := by
  rw [restrictedAbelArgument_apply, restrictedAbelArgument_apply]
  simp only [
    restrictedPairMergeCommonJetRepresentative,
    restrictedPairMergeCommonJetOffset,
    RestrictedBox.pullbackPairMergeExceptionalGraph_apply,
    restrictedPairMergeExceptionalFiniteGraphLift,
    restrictedPairMergeExceptionalGraphLift]
  rw [← succAbove_restrictedReclassifiedRepresentative representative i q.1,
    restrictedPairMergeSourceMap_other K k i j
      (restrictedReclassifiedRepresentative representative i q.1) q.2]
  congr 1
  apply congrArg (offset q.1.1 : RestrictedBoxSpace p → ℝ)
  funext r
  simp only [restrictedBoxInitCLM_apply,
    restrictedPairMergeExceptionalGraphBoxDropCLM_apply,
    Fin.addCases_left, restrictedPairMergeSourceMap_box]

/-- Quantitative graph-tail points lie in the positive domain of the single
common restricted Abel family. -/
theorem restrictedPairMergeExceptionalFiniteGraphLift_mem_commonJetDomain
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (holdDomain : restrictedPairMergeSourceMap K k i j x ∈
      restrictedAbelJetDomain (a := a) D representative offset)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x) :
    restrictedPairMergeExceptionalFiniteGraphLift
        D representative offset K k i j S x ∈
      restrictedAbelJetDomain
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
        (restrictedPairMergeCommonJetRepresentative representative i j S)
        (restrictedPairMergeCommonJetOffset D representative offset i j S) := by
  let z := restrictedPairMergeExceptionalFiniteGraphLift
    D representative offset K k i j S x
  have hzopen := (restrictedPairMergeExceptionalFiniteGraphLift_spec
    D representative offset (K := K) (k := k) hK i j S B hB hbB x hw htail).1
  refine ⟨(restrictedPairMergeExceptionalGraphBox D _).openBox_subset_closedBox hzopen, ?_⟩
  intro q
  rcases q with q | t
  · rw [restrictedPairMergeCommonJetArgument_inl_graphLift
      D representative offset K k i j S q x]
    exact holdDomain.2 q.1.1
  · exact restrictedPairMergeExceptionalGraphTargetArgument_lift_pos
      D representative offset (K := K) (k := k) hK i j S t
        (hB t) (hbB t) x (htail t) hw

/-- Terminal common-tower membership supplies differentiability of the whole
denominator-cleared augmented square map on its common Abel domain. -/
theorem IsAbel.differentiableAt_constraintMap_restrictedPairMergeDenominatorClearedAugmented
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial
      (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    {z : RestrictedPairMergeExceptionalGraphSource
      (p := p) (a := a) representative i j S}
    (hz : z ∈ restrictedAbelJetDomain
      (restrictedPairMergeExceptionalGraphBox D
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
      (restrictedPairMergeCommonJetRepresentative representative i j S)
      (restrictedPairMergeCommonJetOffset D representative offset i j S)) :
    DifferentiableAt ℝ
      (constraintMap
        (restrictedPairMergeDenominatorClearedAugmentedEquationFamily
          A D representative offset K k i j S Q)) z := by
  have hex :=
    exists_commonTower_restrictedPairMergeDenominatorClearedAugmentedEquationFamily
      (a := a) A D representative offset K k i j S Q
  rw [restrictedPairMergeExceptionalCommonJetGenerators_eq_common
    (a := a) A D representative offset i j S] at hex
  obtain ⟨l, T, hT⟩ := hex
  apply differentiableAt_pi.mpr
  intro e
  exact hA.differentiableAt_of_mem_restrictedAbelTower_level
    (restrictedPairMergeCommonJetRepresentative representative i j S)
    (restrictedPairMergeCommonJetOffset D representative offset i j S)
    T (hT e) hz

/-- The cleared old-equation block is differentiable wherever the augmented
family is differentiable. -/
theorem IsAbel.differentiableAt_constraintMap_restrictedPairMergeDenominatorClearedCompressed
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial
      (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    {z : RestrictedPairMergeExceptionalGraphSource
      (p := p) (a := a) representative i j S}
    (hz : z ∈ restrictedAbelJetDomain
      (restrictedPairMergeExceptionalGraphBox D
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
      (restrictedPairMergeCommonJetRepresentative representative i j S)
      (restrictedPairMergeCommonJetOffset D representative offset i j S)) :
    DifferentiableAt ℝ
      (constraintMap
        (restrictedPairMergeDenominatorClearedCompressedEquation
          A D representative offset K k i j S Q)) z := by
  have haug :=
    hA.differentiableAt_constraintMap_restrictedPairMergeDenominatorClearedAugmented
      D representative offset K k i j S Q hz
  apply differentiableAt_pi.mpr
  intro row
  have hrow := differentiableAt_pi.mp haug
    (Fin.castAdd
      (restrictedPairMergeExceptionalOffsetSupport representative i j S).card row)
  simpa [constraintMap,
    restrictedPairMergeDenominatorClearedAugmentedEquationFamily] using hrow

/-! ## Generic row scaling over an arbitrary finite-dimensional source -/

/-- At a common zero, coordinatewise multiplication of an output tuple has
the expected diagonal derivative for any normed source. -/
theorem fderiv_coordinatewise_mul_at_zero_of_source
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {F d : E → (Fin n → ℝ)} {x : E}
    (hF : DifferentiableAt ℝ F x) (hd : DifferentiableAt ℝ d x)
    (hzero : F x = 0) :
    fderiv ℝ (fun y i ↦ d y i * F y i) x =
      (coordinatewiseMulCLM (d x)).comp (fderiv ℝ F x) := by
  have hFi : ∀ i, DifferentiableAt ℝ (fun y ↦ F y i) x := fun i ↦
    differentiableAt_pi.mp hF i
  have hdi : ∀ i, DifferentiableAt ℝ (fun y ↦ d y i) x := fun i ↦
    differentiableAt_pi.mp hd i
  have hpi : fderiv ℝ (fun y i ↦ d y i * F y i) x =
      ContinuousLinearMap.pi (fun i ↦
        fderiv ℝ (fun y ↦ d y i * F y i) x) :=
    fderiv_pi (fun i ↦ (hdi i).mul (hFi i))
  rw [hpi]
  ext v i
  rw [ContinuousLinearMap.pi_apply]
  have hmul := fderiv_mul (hdi i) (hFi i)
  have hfun : (fun y ↦ d y i * F y i) =
      (fun y ↦ d y i) * (fun y ↦ F y i) := by
    funext y
    rfl
  rw [hfun, hmul]
  simp only [add_apply, smul_apply,
    smul_eq_mul, ContinuousLinearMap.comp_apply,
    coordinatewiseMulCLM_apply]
  rw [fderiv_apply hF i, fderiv_apply hd i]
  simp [hzero]

/-- A nonzero diagonal output equivalence preserves surjectivity of a map
from any normed source. -/
theorem surjective_coordinatewiseMulCLM_comp_iff_of_source
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0)
    (D : E →L[ℝ] (Fin n → ℝ)) :
    Function.Surjective ((coordinatewiseMulCLM c).comp D) ↔
      Function.Surjective D := by
  rw [← coordinatewiseMulEquiv_toContinuousLinearMap c hc]
  constructor
  · intro h z
    obtain ⟨v, hv⟩ := h (coordinatewiseMulEquiv c hc z)
    change coordinatewiseMulEquiv c hc (D v) =
      coordinatewiseMulEquiv c hc z at hv
    exact ⟨v, (coordinatewiseMulEquiv c hc).injective hv⟩
  · intro h
    exact (coordinatewiseMulEquiv c hc).surjective.comp h

/-- Nonvanishing differentiable row scaling preserves regular zeros for an
arbitrary normed source. -/
theorem mem_regularZeroSet_coordinatewise_mul_of_source_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {Omega : Set E}
    {F d : E → (Fin n → ℝ)} {x : E}
    (hF : DifferentiableAt ℝ F x) (hd : DifferentiableAt ℝ d x)
    (hdne : ∀ i, d x i ≠ 0) :
    x ∈ regularZeroSet Omega (fun y i ↦ d y i * F y i) ↔
      x ∈ regularZeroSet Omega F := by
  constructor
  · rintro ⟨hxOmega, hxzero, hxsurj⟩
    have hFzero : F x = 0 := by
      funext i
      have hi := congr_fun hxzero i
      simp only [Pi.zero_apply] at hi
      exact (mul_eq_zero.mp hi).resolve_left (hdne i)
    refine ⟨hxOmega, hFzero, ?_⟩
    rw [fderiv_coordinatewise_mul_at_zero_of_source hF hd hFzero,
      surjective_coordinatewiseMulCLM_comp_iff_of_source (d x) hdne] at hxsurj
    exact hxsurj
  · rintro ⟨hxOmega, hxzero, hxsurj⟩
    refine ⟨hxOmega, ?_, ?_⟩
    · funext i
      simp [hxzero]
    · rw [fderiv_coordinatewise_mul_at_zero_of_source hF hd hxzero,
        surjective_coordinatewiseMulCLM_comp_iff_of_source (d x) hdne]
      exact hxsurj

/-! ## The common scale and its graph-tail identity -/

/-- The positive scalar used uniformly to clear every old equation row. -/
def restrictedPairMergeCompressedCommonScale
    (A : ℝ → ℝ) {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial
      (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    RestrictedPairMergeExceptionalGraphSource
      (p := p) (a := a) representative i j S → ℝ :=
  fun z ↦
    finiteCommonDenominator
        (fun s : PaperRankSymbols ((m + 1) + 1) a S.card ↦
          restrictedPairMergeCompressedSymbolDenominator
            A D representative offset K k i j S s z) ^
      mvPolynomialFamilyTotalDegree Q

theorem restrictedPairMergeCompressedCommonScale_pos
    (A : ℝ → ℝ) {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial
      (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (z : RestrictedPairMergeExceptionalGraphSource
      (p := p) (a := a) representative i j S) :
    0 < restrictedPairMergeCompressedCommonScale
      A D representative offset K k i j S Q z := by
  exact pow_pos
    (restrictedPairMergeCompressedCommonDenominator_pos
      A D representative offset K k i j S z) _

/-- The common scalar is differentiable on the common Abel domain. -/
theorem IsAbel.differentiableAt_restrictedPairMergeCompressedCommonScale
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial
      (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    {z : RestrictedPairMergeExceptionalGraphSource
      (p := p) (a := a) representative i j S}
    (hz : z ∈ restrictedAbelJetDomain
      (restrictedPairMergeExceptionalGraphBox D
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
      (restrictedPairMergeCommonJetRepresentative representative i j S)
      (restrictedPairMergeCommonJetOffset D representative offset i j S)) :
    DifferentiableAt ℝ
      (restrictedPairMergeCompressedCommonScale
        A D representative offset K k i j S Q) z := by
  have hex := exists_commonTower_restrictedPairMergeCompressedSymbolData
    (a := a) A D representative offset K k i j S
  rw [restrictedPairMergeExceptionalCommonJetGenerators_eq_common
    (a := a) A D representative offset i j S] at hex
  obtain ⟨l, T, hden, _hnum⟩ := hex
  have hcommon : finiteCommonDenominator
      (restrictedPairMergeCompressedSymbolDenominator
        A D representative offset K k i j S) ∈ T.level l :=
    finiteCommonDenominator_mem_subalgebra (T.level l)
      (restrictedPairMergeCompressedSymbolDenominator
        A D representative offset K k i j S) hden
  have hscaleEq : restrictedPairMergeCompressedCommonScale
      A D representative offset K k i j S Q =
      finiteCommonDenominator
          (restrictedPairMergeCompressedSymbolDenominator
            A D representative offset K k i j S) ^
        mvPolynomialFamilyTotalDegree Q := by
    funext z
    simp [restrictedPairMergeCompressedCommonScale,
      finiteCommonDenominator]
  have hscale : restrictedPairMergeCompressedCommonScale
      A D representative offset K k i j S Q ∈ T.level l := by
    rw [hscaleEq]
    exact (T.level l).pow_mem hcommon (mvPolynomialFamilyTotalDegree Q)
  exact hA.differentiableAt_of_mem_restrictedAbelTower_level
    (restrictedPairMergeCommonJetRepresentative representative i j S)
    (restrictedPairMergeCommonJetOffset D representative offset i j S)
    T hscale hz

/-- On the quantitative graph tail, each cleared row is the common positive
scale times its original, unreindexed old equation. -/
theorem IsAbel.restrictedPairMergeDenominatorClearedCompressedEquation_on_graphLift_eq_scale_mul
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial
      (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (F : Fin n → RestrictedSource ((m + 1) + 1) p a → ℝ)
    (hQ : ∀ row, restrictedPaperPolynomialValue A D representative offset
      (restrictedJetEnumeration S) (Q row) = F row)
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (row : Fin n) :
    restrictedPairMergeDenominatorClearedCompressedEquation
        A D representative offset K k i j S Q row
        (restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S x) =
      restrictedPairMergeCompressedCommonScale
          A D representative offset K k i j S Q
          (restrictedPairMergeExceptionalFiniteGraphLift
            D representative offset K k i j S x) *
        F row (restrictedPairMergeSourceMap K k i j x) := by
  symm
  exact hA.restrictedPairMergeDenominatorClearedCompressedEquation_on_graphLift
    D representative offset hK i j S Q F hQ B hB hbB x htail hw row

/-- The cleared graph substitution and the uniformly scaled old pullback
agree on a whole neighborhood of every quantitative tail point. -/
theorem IsAbel.eventuallyEq_constraintMap_denominatorCleared_on_graphLift
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial
      (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (F : Fin n → RestrictedSource ((m + 1) + 1) p a → ℝ)
    (hQ : ∀ row, restrictedPaperPolynomialValue A D representative offset
      (restrictedJetEnumeration S) (Q row) = F row)
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox) :
    (fun y ↦ constraintMap
        (restrictedPairMergeDenominatorClearedCompressedEquation
          A D representative offset K k i j S Q)
        (restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S y)) =ᶠ[𝓝 x]
      (fun y row ↦
        restrictedPairMergeCompressedCommonScale
            A D representative offset K k i j S Q
            (restrictedPairMergeExceptionalFiniteGraphLift
              D representative offset K k i j S y) *
          F row (restrictedPairMergeSourceMap K k i j y)) := by
  have hboxContinuous : ContinuousAt
      (fun y : RestrictedSource (m + 1) (p + 1) a ↦ y.1.2) x := by
    fun_prop
  have hbox : ∀ᶠ y in 𝓝 x,
      y.1.2 ∈ (restrictedPairMergeBox D).openBox :=
    hboxContinuous ((restrictedPairMergeBox D).isOpen_openBox.mem_nhds hw)
  have htails : ∀ᶠ y in 𝓝 x, ∀ t,
      B t + 2 < restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) y := by
    apply Filter.eventually_all.mpr
    intro t
    have hbaseContinuous : ContinuousAt
        (restrictedPairMergeExceptionalBaseArgument representative i j
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)) x :=
      (differentiable_restrictedPairMergeExceptionalBaseArgument
        (p := p) (a := a) representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)).continuous.continuousAt
    exact hbaseContinuous (isOpen_Ioi.mem_nhds (htail t))
  filter_upwards [hbox, htails] with y hy hytail
  funext row
  exact hA.restrictedPairMergeDenominatorClearedCompressedEquation_on_graphLift_eq_scale_mul
    D representative offset hK i j S Q F hQ B hB hbB y hytail hy row

/-- The finite graph section is differentiable on the simultaneous
quantitative tail. -/
theorem differentiableAt_restrictedPairMergeExceptionalFiniteGraphLift
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x) :
    DifferentiableAt ℝ
      (restrictedPairMergeExceptionalFiniteGraphLift
        D representative offset K k i j S) x := by
  let eta := restrictedPairMergeExceptionalVectorShift
    (a := a) D representative offset K k i j S
  have heta : DifferentiableAt ℝ eta x :=
    differentiableAt_restrictedPairMergeExceptionalVectorShift
      D representative offset hK i j S B hB hbB x hw htail
  let e := restrictedPairMergeExceptionalGraphContinuousLinearEquiv
    (m := m) (p := p) (a := a)
    (N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
  have heq : restrictedPairMergeExceptionalFiniteGraphLift
      D representative offset K k i j S =
      e.symm ∘ (fun y ↦ (y, eta y)) := by
    funext y
    apply e.injective
    simp [e, eta, restrictedPairMergeExceptionalFiniteGraphLift]
    rfl
  rw [heq]
  exact e.symm.differentiableAt.comp x (differentiableAt_id.prodMk heta)

/-- The common positive scale pulled back to the finite graph section is
differentiable at every common-domain quantitative-tail point. -/
theorem IsAbel.differentiableAt_restrictedPairMergeCompressedCommonScale_on_graphLift
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial
      (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (holdDomain : restrictedPairMergeSourceMap K k i j x ∈
      restrictedAbelJetDomain (a := a) D representative offset)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x) :
    DifferentiableAt ℝ
      (fun y ↦ restrictedPairMergeCompressedCommonScale
        A D representative offset K k i j S Q
        (restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S y)) x := by
  have hzDomain :=
    restrictedPairMergeExceptionalFiniteGraphLift_mem_commonJetDomain
      D representative offset hK i j S B hB hbB x holdDomain hw htail
  exact (hA.differentiableAt_restrictedPairMergeCompressedCommonScale
    D representative offset K k i j S Q hzDomain).comp x
      (differentiableAt_restrictedPairMergeExceptionalFiniteGraphLift
        D representative offset hK i j S B hB hbB x hw htail)

/-- After restricting to the exceptional graph, denominator clearing
preserves regular-zero membership in the lower source. -/
theorem IsAbel.mem_regularZeroSet_denominatorCleared_graphSubstitution_iff
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (Q : Fin n → MvPolynomial
      (PaperRankSymbols ((m + 1) + 1) a S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D))
    (F : Fin n → RestrictedSource ((m + 1) + 1) p a → ℝ)
    (hQ : ∀ row, restrictedPaperPolynomialValue A D representative offset
      (restrictedJetEnumeration S) (Q row) = F row)
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (Omega : Set (RestrictedSource (m + 1) (p + 1) a))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (holdDomain : restrictedPairMergeSourceMap K k i j x ∈
      restrictedAbelJetDomain (a := a) D representative offset)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x)
    (hFdiff : DifferentiableAt ℝ (constraintMap F)
      (restrictedPairMergeSourceMap K k i j x)) :
    x ∈ regularZeroSet Omega
        (fun y ↦ constraintMap
          (restrictedPairMergeDenominatorClearedCompressedEquation
            A D representative offset K k i j S Q)
          (restrictedPairMergeExceptionalFiniteGraphLift
            D representative offset K k i j S y)) ↔
      x ∈ regularZeroSet Omega
        (constraintMap F ∘ restrictedPairMergeSourceMap K k i j) := by
  let scale : RestrictedSource (m + 1) (p + 1) a → ℝ := fun y ↦
    restrictedPairMergeCompressedCommonScale
      A D representative offset K k i j S Q
      (restrictedPairMergeExceptionalFiniteGraphLift
        D representative offset K k i j S y)
  let d : RestrictedSource (m + 1) (p + 1) a → (Fin n → ℝ) :=
    fun y _ ↦ scale y
  let old : RestrictedSource (m + 1) (p + 1) a → (Fin n → ℝ) :=
    constraintMap F ∘ restrictedPairMergeSourceMap K k i j
  have heq := hA.eventuallyEq_constraintMap_denominatorCleared_on_graphLift
    D representative offset (K := K) (k := k) hK i j S Q F hQ B hB hbB x htail hw
  have heq' :
      (fun y ↦ constraintMap
        (restrictedPairMergeDenominatorClearedCompressedEquation
          A D representative offset K k i j S Q)
        (restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S y)) =ᶠ[𝓝 x]
        (fun y row ↦ d y row * old y row) := by
    simpa only [d, scale, old, Function.comp_apply, constraintMap] using heq
  have hlocal :
      (x ∈ regularZeroSet Omega
          (fun y ↦ constraintMap
            (restrictedPairMergeDenominatorClearedCompressedEquation
              A D representative offset K k i j S Q)
            (restrictedPairMergeExceptionalFiniteGraphLift
              D representative offset K k i j S y))) ↔
        x ∈ regularZeroSet Omega (fun y row ↦ d y row * old y row) := by
    simp only [regularZeroSet, Set.mem_ofPred_eq]
    have hval :
        constraintMap
            (restrictedPairMergeDenominatorClearedCompressedEquation
              A D representative offset K k i j S Q)
            (restrictedPairMergeExceptionalFiniteGraphLift
              D representative offset K k i j S x) =
          (fun row ↦ d x row * old x row) := by
      simpa only using heq'.self_of_nhds
    have hderiv :
        fderiv ℝ
            (fun y ↦ constraintMap
              (restrictedPairMergeDenominatorClearedCompressedEquation
                A D representative offset K k i j S Q)
              (restrictedPairMergeExceptionalFiniteGraphLift
                D representative offset K k i j S y)) x =
          fderiv ℝ (fun y row ↦ d y row * old y row) x :=
      heq'.fderiv_eq
    constructor
    · rintro ⟨hx, hzero, hsurj⟩
      refine ⟨hx, ?_, ?_⟩
      · exact hval ▸ hzero
      · exact hderiv ▸ hsurj
    · rintro ⟨hx, hzero, hsurj⟩
      refine ⟨hx, ?_, ?_⟩
      · exact hval.symm ▸ hzero
      · exact hderiv.symm ▸ hsurj
  have holdDiff : DifferentiableAt ℝ old x :=
    hFdiff.comp x
      (((contDiff_restrictedPairMergeSourceMap
        (p := p) (a := a) K k i j).differentiable (by simp)).differentiableAt)
  have hscaleDiff : DifferentiableAt ℝ scale x :=
    hA.differentiableAt_restrictedPairMergeCompressedCommonScale_on_graphLift
      D representative offset hK i j S Q B hB hbB x holdDomain hw htail
  have hdDiff : DifferentiableAt ℝ d x := by
    apply differentiableAt_pi.mpr
    intro row
    exact hscaleDiff
  have hdne : ∀ row, d x row ≠ 0 := by
    intro row
    exact (restrictedPairMergeCompressedCommonScale_pos
      A D representative offset K k i j S Q
      (restrictedPairMergeExceptionalFiniteGraphLift
        D representative offset K k i j S x)).ne'
  exact hlocal.trans
    (mem_regularZeroSet_coordinatewise_mul_of_source_iff
      holdDiff hdDiff hdne)

end AbelFormalization
