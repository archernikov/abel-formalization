import AbelFormalization.RegularZeroTranslation
import AbelFormalization.RestrictedExpressionBaseAnalyticPolynomial
import AbelFormalization.RestrictedClosedJetDomain

/-!
# Translation of the bounded restricted coordinates

The rank argument is naturally based at the limit of the bounded-coordinate
sequence.  This file translates that limit to zero, while transporting the
restricted box, its analytic coefficient algebra, the shifted Abel offsets,
the base expression algebra, and regular-zero systems.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

namespace RestrictedBox

/-- Translate a restricted box by subtracting `w₀` from both endpoints. -/
def translateToZero {p : ℕ} (D : RestrictedBox p)
    (w₀ : RestrictedBoxSpace p) : RestrictedBox p where
  lower := D.lower - w₀
  upper := D.upper - w₀
  lower_lt_upper := by
    intro i
    exact sub_lt_sub_right (D.lower_lt_upper i) (w₀ i)

@[simp]
theorem translateToZero_lower {p : ℕ} (D : RestrictedBox p)
    (w₀ : RestrictedBoxSpace p) (i : Fin p) :
    (D.translateToZero w₀).lower i = D.lower i - w₀ i :=
  rfl

@[simp]
theorem translateToZero_upper {p : ℕ} (D : RestrictedBox p)
    (w₀ : RestrictedBoxSpace p) (i : Fin p) :
    (D.translateToZero w₀).upper i = D.upper i - w₀ i :=
  rfl

/-- Add the old base point back to a translated bounded coordinate. -/
def translateFromZero {p : ℕ} (w₀ : RestrictedBoxSpace p) :
    RestrictedBoxSpace p → RestrictedBoxSpace p :=
  fun w ↦ w + w₀

@[simp]
theorem translateFromZero_apply {p : ℕ} (w₀ w : RestrictedBoxSpace p)
    (i : Fin p) : translateFromZero w₀ w i = w i + w₀ i :=
  rfl

@[simp]
theorem translateFromZero_zero {p : ℕ} (w₀ : RestrictedBoxSpace p) :
    translateFromZero w₀ 0 = w₀ := by
  ext i
  simp [translateFromZero]

theorem mem_openBox_translateToZero_iff {p : ℕ} (D : RestrictedBox p)
    (w₀ w : RestrictedBoxSpace p) :
    w ∈ (D.translateToZero w₀).openBox ↔
      translateFromZero w₀ w ∈ D.openBox := by
  rw [(D.translateToZero w₀).mem_openBox, D.mem_openBox]
  constructor
  · intro hw i
    specialize hw i
    constructor <;> dsimp [translateFromZero] at * <;> linarith
  · intro hw i
    specialize hw i
    constructor <;> dsimp [translateFromZero] at * <;> linarith

theorem mem_closedBox_translateToZero_iff {p : ℕ} (D : RestrictedBox p)
    (w₀ w : RestrictedBoxSpace p) :
    w ∈ (D.translateToZero w₀).closedBox ↔
      translateFromZero w₀ w ∈ D.closedBox := by
  rw [(D.translateToZero w₀).mem_closedBox, D.mem_closedBox]
  constructor
  · intro hw i
    specialize hw i
    constructor <;> dsimp [translateFromZero] at * <;> linarith
  · intro hw i
    specialize hw i
    constructor <;> dsimp [translateFromZero] at * <;> linarith

theorem zero_mem_closedBox_translateToZero {p : ℕ} (D : RestrictedBox p)
    {w₀ : RestrictedBoxSpace p} (hw₀ : w₀ ∈ D.closedBox) :
    (0 : RestrictedBoxSpace p) ∈ (D.translateToZero w₀).closedBox := by
  rw [mem_closedBox_translateToZero_iff]
  simpa using hw₀

/-- Translate an analytic coefficient representative to the new box. -/
def translateCoefficientToZero {p : ℕ} (D : RestrictedBox p)
    (w₀ : RestrictedBoxSpace p)
    (c : D.analyticNearClosedBoxSubalgebra) :
    (D.translateToZero w₀).analyticNearClosedBoxSubalgebra := by
  refine ⟨fun w ↦ (c : RestrictedBoxSpace p → ℝ) (translateFromZero w₀ w), ?_⟩
  change (D.translateToZero w₀).AnalyticNearClosedBox
    (fun w ↦ (c : RestrictedBoxSpace p → ℝ) (translateFromZero w₀ w))
  rw [(D.translateToZero w₀).analyticNearClosedBox_iff]
  intro w hw
  have hold : translateFromZero w₀ w ∈ D.closedBox :=
    (mem_closedBox_translateToZero_iff D w₀ w).mp hw
  have hc : AnalyticAt ℝ (c : RestrictedBoxSpace p → ℝ)
      (translateFromZero w₀ w) :=
    (D.analyticNearClosedBox_iff.mp c.property) _ hold
  have htranslate : AnalyticAt ℝ (translateFromZero w₀) w := by
    change AnalyticAt ℝ (fun z : RestrictedBoxSpace p ↦ z + w₀) w
    exact analyticAt_id.add analyticAt_const
  exact hc.comp htranslate

@[simp]
theorem translateCoefficientToZero_apply {p : ℕ} (D : RestrictedBox p)
    (w₀ : RestrictedBoxSpace p)
    (c : D.analyticNearClosedBoxSubalgebra) (w : RestrictedBoxSpace p) :
    (D.translateCoefficientToZero w₀ c : RestrictedBoxSpace p → ℝ) w =
      (c : RestrictedBoxSpace p → ℝ) (w + w₀) :=
  rfl

/-- Translation is an algebra homomorphism between the two coefficient
algebras. -/
def translateCoefficientToZeroAlgHom {p : ℕ} (D : RestrictedBox p)
    (w₀ : RestrictedBoxSpace p) :
    D.analyticNearClosedBoxSubalgebra →ₐ[ℝ]
      (D.translateToZero w₀).analyticNearClosedBoxSubalgebra where
  toFun := D.translateCoefficientToZero w₀
  map_one' := by
    apply Subtype.ext
    funext w
    simp [translateCoefficientToZero]
  map_mul' c d := by
    apply Subtype.ext
    funext w
    simp [translateCoefficientToZero]
  map_zero' := by
    apply Subtype.ext
    funext w
    simp [translateCoefficientToZero]
  map_add' c d := by
    apply Subtype.ext
    funext w
    simp [translateCoefficientToZero]
  commutes' r := by
    apply Subtype.ext
    funext w
    simp [translateCoefficientToZero]

@[simp]
theorem translateCoefficientToZeroAlgHom_apply {p : ℕ}
    (D : RestrictedBox p) (w₀ : RestrictedBoxSpace p)
    (c : D.analyticNearClosedBoxSubalgebra) :
    D.translateCoefficientToZeroAlgHom w₀ c =
      D.translateCoefficientToZero w₀ c :=
  rfl

end RestrictedBox

/-- Translate only the bounded coordinate of a restricted source point. -/
def restrictedSourceTranslateFromZero {m p a : ℕ}
    (w₀ : RestrictedBoxSpace p) :
    RestrictedSource m p a → RestrictedSource m p a :=
  fun x ↦ ((x.1.1, RestrictedBox.translateFromZero w₀ x.1.2), x.2)

/-- The vector whose addition translates only the bounded coordinate. -/
def restrictedSourceBoxTranslationVector {m p a : ℕ}
    (w₀ : RestrictedBoxSpace p) : RestrictedSource m p a :=
  ((0, w₀), 0)

/-- Subtract the old bounded base point, leaving all other source
coordinates unchanged. -/
def restrictedSourceTranslateToZero {m p a : ℕ}
    (w₀ : RestrictedBoxSpace p) :
    RestrictedSource m p a → RestrictedSource m p a :=
  fun x ↦ ((x.1.1, x.1.2 - w₀), x.2)

@[simp]
theorem restrictedSourceTranslateFromZero_toZero {m p a : ℕ}
    (w₀ : RestrictedBoxSpace p) (x : RestrictedSource m p a) :
    restrictedSourceTranslateFromZero w₀
        (restrictedSourceTranslateToZero w₀ x) = x := by
  ext i <;> simp [restrictedSourceTranslateFromZero,
    restrictedSourceTranslateToZero, RestrictedBox.translateFromZero]

@[simp]
theorem restrictedSourceTranslateToZero_fromZero {m p a : ℕ}
    (w₀ : RestrictedBoxSpace p) (x : RestrictedSource m p a) :
    restrictedSourceTranslateToZero w₀
        (restrictedSourceTranslateFromZero w₀ x) = x := by
  ext i <;> simp [restrictedSourceTranslateFromZero,
    restrictedSourceTranslateToZero, RestrictedBox.translateFromZero]

@[simp]
theorem restrictedSourceTranslateFromZero_eq_add {m p a : ℕ}
    (w₀ : RestrictedBoxSpace p) (x : RestrictedSource m p a) :
    restrictedSourceTranslateFromZero w₀ x =
      x + restrictedSourceBoxTranslationVector w₀ := by
  ext i <;> simp [restrictedSourceTranslateFromZero,
    restrictedSourceBoxTranslationVector, RestrictedBox.translateFromZero]

theorem preimage_restrictedBaseOpenDomain_translateToZero
    {m p a : ℕ} (D : RestrictedBox p) (R : ℝ)
    (w₀ : RestrictedBoxSpace p) :
    restrictedSourceTranslateFromZero w₀ ⁻¹'
        restrictedBaseOpenDomain (m := m) (a := a) D R =
      restrictedBaseOpenDomain (D.translateToZero w₀) R := by
  ext x
  simp only [Set.mem_preimage, restrictedBaseOpenDomain,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hs, hw⟩
    exact ⟨hs, (D.mem_openBox_translateToZero_iff w₀ x.1.2).mpr hw⟩
  · rintro ⟨hs, hw⟩
    exact ⟨hs, (D.mem_openBox_translateToZero_iff w₀ x.1.2).mp hw⟩

theorem preimage_restrictedBaseClosedDomain_translateToZero
    {m p a : ℕ} (D : RestrictedBox p) (R : ℝ)
    (w₀ : RestrictedBoxSpace p) :
    restrictedSourceTranslateFromZero w₀ ⁻¹'
        restrictedBaseClosedDomain (m := m) (a := a) D R =
      restrictedBaseClosedDomain (D.translateToZero w₀) R := by
  ext x
  simp only [Set.mem_preimage, restrictedBaseClosedDomain,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hs, hw⟩
    exact ⟨hs, (D.mem_closedBox_translateToZero_iff w₀ x.1.2).mpr hw⟩
  · rintro ⟨hs, hw⟩
    exact ⟨hs, (D.mem_closedBox_translateToZero_iff w₀ x.1.2).mp hw⟩

/-- Translate every named analytic offset. -/
def restrictedOffsetTranslateToZero {p : ℕ} {D : RestrictedBox p}
    (w₀ : RestrictedBoxSpace p)
    (offset : ι → D.analyticNearClosedBoxSubalgebra) :
    ι → (D.translateToZero w₀).analyticNearClosedBoxSubalgebra :=
  fun k ↦ D.translateCoefficientToZero w₀ (offset k)

@[simp]
theorem restrictedAbelArgument_translateFromZero
    {m p a : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (w₀ : RestrictedBoxSpace p) (k : ι)
    (x : RestrictedSource m p a) :
    restrictedAbelArgument (representative k)
        (restrictedOffsetTranslateToZero w₀ offset k :
          RestrictedBoxSpace p → ℝ) x =
      restrictedAbelArgument (representative k)
        (offset k : RestrictedBoxSpace p → ℝ)
        (restrictedSourceTranslateFromZero w₀ x) := by
  change x.1.1 (representative k) +
      (offset k : RestrictedBoxSpace p → ℝ) (x.1.2 + w₀) =
    x.1.1 (representative k) +
      (offset k : RestrictedBoxSpace p → ℝ) (x.1.2 + w₀)
  rfl

@[simp]
theorem restrictedAbelJet_translateFromZero
    (A : ℝ → ℝ) {m p a : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (w₀ : RestrictedBoxSpace p) (k : ι) (r : ℕ)
    (x : RestrictedSource m p a) :
    restrictedAbelJet A (representative k)
        (restrictedOffsetTranslateToZero w₀ offset k :
          RestrictedBoxSpace p → ℝ) r x =
      restrictedAbelJet A (representative k)
        (offset k : RestrictedBoxSpace p → ℝ) r
        (restrictedSourceTranslateFromZero w₀ x) := by
  change iteratedDeriv r A
      (x.1.1 (representative k) +
        (offset k : RestrictedBoxSpace p → ℝ) (x.1.2 + w₀)) =
    iteratedDeriv r A
      (x.1.1 (representative k) +
        (offset k : RestrictedBoxSpace p → ℝ) (x.1.2 + w₀))
  rfl

theorem preimage_restrictedAbelJetDomain_translateToZero
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (w₀ : RestrictedBoxSpace p) :
    restrictedSourceTranslateFromZero w₀ ⁻¹'
        restrictedAbelJetDomain (a := a) D representative offset =
      restrictedAbelJetDomain (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) := by
  ext x
  simp only [Set.mem_preimage, restrictedAbelJetDomain, Set.mem_inter_iff,
    restrictedClosedBoxCylinder, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hw, hpos⟩
    refine ⟨(D.mem_closedBox_translateToZero_iff w₀ x.1.2).mpr hw, ?_⟩
    intro k
    rw [restrictedAbelArgument_translateFromZero]
    exact hpos k
  · rintro ⟨hw, hpos⟩
    refine ⟨(D.mem_closedBox_translateToZero_iff w₀ x.1.2).mp hw, ?_⟩
    intro k
    rw [← restrictedAbelArgument_translateFromZero
      representative offset w₀ k x]
    exact hpos k

/-- The admissible closed-domain inclusion survives translation to the
bounded limit. -/
theorem restrictedBaseClosedDomain_subset_AbelJetDomain_translateToZero
    {m p a : ℕ} (D : RestrictedBox p) (R : ℝ)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (w₀ : RestrictedBoxSpace p)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset) :
    restrictedBaseClosedDomain (m := m) (a := a)
        (D.translateToZero w₀) R ⊆
      restrictedAbelJetDomain (a := a) (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) := by
  intro x hx
  have hxold : restrictedSourceTranslateFromZero w₀ x ∈
      restrictedBaseClosedDomain (m := m) (a := a) D R := by
    have hmem : x ∈ restrictedSourceTranslateFromZero w₀ ⁻¹'
        restrictedBaseClosedDomain (m := m) (a := a) D R := by
      rw [preimage_restrictedBaseClosedDomain_translateToZero]
      exact hx
    exact hmem
  have hold := hDomain hxold
  have hmem : x ∈ restrictedSourceTranslateFromZero w₀ ⁻¹'
      restrictedAbelJetDomain (a := a) D representative offset := hold
  rw [preimage_restrictedAbelJetDomain_translateToZero] at hmem
  exact hmem

/-! ## Translation of the restricted expression base -/

/-- Every polynomial representative over the restricted coefficient algebra
evaluates to an element of the restricted expression base. -/
theorem restrictedBasePolynomialValue_mem_base
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (P : MvPolynomial (RestrictedBasePolynomialSymbol ι m a)
      D.analyticNearClosedBoxSubalgebra) :
    restrictedBasePolynomialValue A D representative offset P ∈
      restrictedExpressionBase D
        (restrictedAbelJetGenerators (a := a) A representative offset) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [restrictedBasePolynomialValue_C]
      exact restrictedBoxCoefficientPullback_mem_base D _ c
  | add P Q hP hQ =>
      rw [restrictedBasePolynomialValue_add]
      exact (restrictedExpressionBase D
        (restrictedAbelJetGenerators (a := a) A representative offset)).add_mem hP hQ
  | mul_X P z hP =>
      rw [restrictedBasePolynomialValue_mul]
      apply (restrictedExpressionBase D
        (restrictedAbelJetGenerators (a := a) A representative offset)).mul_mem hP
      rcases z with k | z
      · rw [restrictedBasePolynomialValue_X_aux]
        exact restrictedAuxCoordinate_mem_base D _ k
      · rcases z with i | kr
        · rw [restrictedBasePolynomialValue_X_s]
          exact restrictedSCoordinate_mem_base D _ i
        · rw [restrictedBasePolynomialValue_X_jet]
          apply specialGenerator_mem_base D
          exact ⟨kr, rfl⟩

/-- Map a polynomial representative through translation of its analytic
coefficients. -/
def restrictedBasePolynomialTranslateToZero
    {m p a : ℕ} (D : RestrictedBox p) (w₀ : RestrictedBoxSpace p)
    (P : MvPolynomial (RestrictedBasePolynomialSymbol ι m a)
      D.analyticNearClosedBoxSubalgebra) :
    MvPolynomial (RestrictedBasePolynomialSymbol ι m a)
      (D.translateToZero w₀).analyticNearClosedBoxSubalgebra :=
  MvPolynomial.map (D.translateCoefficientToZeroAlgHom w₀).toRingHom P

theorem restrictedBasePolynomialSymbolValue_translateFromZero
    (A : ℝ → ℝ) {m p a : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (w₀ : RestrictedBoxSpace p) (x : RestrictedSource m p a) :
    restrictedBasePolynomialSymbolValue A representative
        (restrictedOffsetTranslateToZero w₀ offset) x =
      restrictedBasePolynomialSymbolValue A representative offset
        (restrictedSourceTranslateFromZero w₀ x) := by
  funext z
  rcases z with k | z
  · rfl
  · rcases z with i | kr
    · rfl
    · exact restrictedAbelJet_translateFromZero
        A representative offset w₀ kr.1 kr.2 x

theorem subalgebraPointEval_translateCoefficientToZero
    {p : ℕ} (D : RestrictedBox p) (w₀ w : RestrictedBoxSpace p) :
    (subalgebraPointEval
        (D.translateToZero w₀).analyticNearClosedBoxSubalgebra w).comp
        (D.translateCoefficientToZeroAlgHom w₀).toRingHom =
      subalgebraPointEval D.analyticNearClosedBoxSubalgebra
        (RestrictedBox.translateFromZero w₀ w) := by
  ext c
  rfl

/-- Translating the polynomial coefficients and offsets gives exactly the
pullback of the original represented function along bounded-coordinate
translation. -/
theorem restrictedBasePolynomialValue_translateToZero
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (w₀ : RestrictedBoxSpace p)
    (P : MvPolynomial (RestrictedBasePolynomialSymbol ι m a)
      D.analyticNearClosedBoxSubalgebra) :
    restrictedBasePolynomialValue A (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset)
        (restrictedBasePolynomialTranslateToZero D w₀ P) =
      fun x ↦ restrictedBasePolynomialValue A D representative offset P
        (restrictedSourceTranslateFromZero w₀ x) := by
  funext x
  unfold restrictedBasePolynomialValue restrictedBasePolynomialTranslateToZero
  rw [MvPolynomial.eval₂_map]
  rw [subalgebraPointEval_translateCoefficientToZero]
  rw [restrictedBasePolynomialSymbolValue_translateFromZero]
  have hxw : (restrictedSourceTranslateFromZero w₀ x).1.2 =
      RestrictedBox.translateFromZero w₀ x.1.2 := rfl
  rw [hxw]

/-- Pullback by bounded-coordinate translation preserves membership in the
restricted Abel expression base. -/
theorem restrictedExpressionBase_precomp_translateFromZero
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → D.analyticNearClosedBoxSubalgebra)
    (w₀ : RestrictedBoxSpace p)
    {f : RestrictedSource m p a → ℝ}
    (hf : f ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)) :
    (fun x ↦ f (restrictedSourceTranslateFromZero w₀ x)) ∈
      restrictedExpressionBase (D.translateToZero w₀)
        (restrictedAbelJetGenerators (a := a) A representative
          (restrictedOffsetTranslateToZero w₀ offset)) := by
  obtain ⟨P, hP⟩ := exists_restrictedBasePolynomialValue_eq_of_mem
    A D representative offset hf
  rw [← hP, ← restrictedBasePolynomialValue_translateToZero]
  exact restrictedBasePolynomialValue_mem_base A (D.translateToZero w₀)
    representative (restrictedOffsetTranslateToZero w₀ offset)
    (restrictedBasePolynomialTranslateToZero D w₀ P)

/-! ## Translation of equation systems and regular zeros -/

/-- Precompose every equation with bounded-coordinate translation. -/
def restrictedEquationFamilyTranslateToZero
    {m p a n : ℕ} (w₀ : RestrictedBoxSpace p)
    (F : Fin n → RestrictedSource m p a → ℝ) :
    Fin n → RestrictedSource m p a → ℝ :=
  fun i x ↦ F i (restrictedSourceTranslateFromZero w₀ x)

@[simp]
theorem constraintMap_restrictedEquationFamilyTranslateToZero
    {m p a n : ℕ} (w₀ : RestrictedBoxSpace p)
    (F : Fin n → RestrictedSource m p a → ℝ)
    (x : RestrictedSource m p a) :
    constraintMap (restrictedEquationFamilyTranslateToZero w₀ F) x =
      constraintMap F (restrictedSourceTranslateFromZero w₀ x) :=
  rfl

theorem regularZeroSet_restrictedEquationFamilyTranslateToZero
    {m p a n : ℕ} (D : RestrictedBox p) (R : ℝ)
    (w₀ : RestrictedBoxSpace p)
    (F : Fin n → RestrictedSource m p a → ℝ) :
    regularZeroSet (restrictedBaseOpenDomain (D.translateToZero w₀) R)
        (constraintMap (restrictedEquationFamilyTranslateToZero w₀ F)) =
      restrictedSourceTranslateFromZero w₀ ⁻¹'
        regularZeroSet (restrictedBaseOpenDomain D R) (constraintMap F) := by
  let c : RestrictedSource m p a := restrictedSourceBoxTranslationVector w₀
  have hsource : restrictedSourceTranslateFromZero w₀ = fun x ↦ x + c := by
    funext x
    exact restrictedSourceTranslateFromZero_eq_add w₀ x
  have hmap : constraintMap (restrictedEquationFamilyTranslateToZero w₀ F) =
      fun x ↦ constraintMap F (x + c) := by
    funext x i
    change F i (restrictedSourceTranslateFromZero w₀ x) = F i (x + c)
    rw [congrFun hsource x]
  rw [← preimage_restrictedBaseOpenDomain_translateToZero D R w₀]
  rw [hsource]
  rw [hmap]
  exact regularZeroSet_preimage_add_right c
    (restrictedBaseOpenDomain D R) (constraintMap F)

theorem finite_regularZeroSet_restrictedEquationFamilyTranslateToZero_iff
    {m p a n : ℕ} (D : RestrictedBox p) (R : ℝ)
    (w₀ : RestrictedBoxSpace p)
    (F : Fin n → RestrictedSource m p a → ℝ) :
    (regularZeroSet (restrictedBaseOpenDomain (D.translateToZero w₀) R)
      (constraintMap (restrictedEquationFamilyTranslateToZero w₀ F))).Finite ↔
      (regularZeroSet (restrictedBaseOpenDomain D R)
        (constraintMap F)).Finite := by
  rw [regularZeroSet_restrictedEquationFamilyTranslateToZero]
  constructor
  · intro h
    apply h.of_preimage
    intro x
    refine ⟨((x.1.1, x.1.2 - w₀), x.2), ?_⟩
    ext i <;> simp [restrictedSourceTranslateFromZero,
      RestrictedBox.translateFromZero]
  · intro h
    exact Set.Finite.preimage
      (Set.injOn_of_injective (fun x y hxy ↦ by
        have := congrArg (fun z : RestrictedSource m p a ↦
          ((z.1.1, z.1.2 - w₀), z.2)) hxy
        simpa [restrictedSourceTranslateFromZero,
          RestrictedBox.translateFromZero] using this)) h

/-- A regular zero of the original system becomes a regular zero of the
translated system after subtracting the bounded base point. -/
theorem mem_regularZeroSet_restrictedEquationFamilyTranslateToZero
    {m p a n : ℕ} (D : RestrictedBox p) (R : ℝ)
    (w₀ : RestrictedBoxSpace p)
    (F : Fin n → RestrictedSource m p a → ℝ)
    {x : RestrictedSource m p a}
    (hx : x ∈ regularZeroSet (restrictedBaseOpenDomain D R)
      (constraintMap F)) :
    restrictedSourceTranslateToZero w₀ x ∈
      regularZeroSet (restrictedBaseOpenDomain (D.translateToZero w₀) R)
        (constraintMap (restrictedEquationFamilyTranslateToZero w₀ F)) := by
  rw [regularZeroSet_restrictedEquationFamilyTranslateToZero]
  change restrictedSourceTranslateFromZero w₀
      (restrictedSourceTranslateToZero w₀ x) ∈
    regularZeroSet (restrictedBaseOpenDomain D R) (constraintMap F)
  simpa only [restrictedSourceTranslateFromZero_toZero] using hx

/-- Translating a bounded-coordinate sequence which converges to `w₀`
produces a bounded-coordinate sequence converging to zero. -/
theorem tendsto_restrictedSourceTranslateToZero_box_zero
    {m p a : ℕ} (w₀ : RestrictedBoxSpace p)
    (x : ℕ → RestrictedSource m p a)
    (hx : Filter.Tendsto (fun n ↦ (x n).1.2) Filter.atTop (𝓝 w₀)) :
    Filter.Tendsto
      (fun n ↦ (restrictedSourceTranslateToZero w₀ (x n)).1.2)
      Filter.atTop (𝓝 0) := by
  have hconst : Filter.Tendsto (fun _ : ℕ ↦ w₀) Filter.atTop (𝓝 w₀) :=
    tendsto_const_nhds
  have hsub := hx.sub hconst
  simpa [restrictedSourceTranslateToZero] using hsub

/-- Source translation is injective, so it preserves injective sequences. -/
theorem restrictedSourceTranslateToZero_injective {m p a : ℕ}
    (w₀ : RestrictedBoxSpace p) :
    Function.Injective
      (restrictedSourceTranslateToZero (m := m) (a := a) w₀) := by
  intro x y hxy
  have := congrArg (restrictedSourceTranslateFromZero
    (m := m) (a := a) w₀) hxy
  simpa only [restrictedSourceTranslateFromZero_toZero] using this

end AbelFormalization
