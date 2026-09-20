import AbelFormalization.LionLemma4RegularMinorCover

/-!
# Assembling the section leaves in Lion's Lemma 4

Once the radial parameter has the transversality/rank-selection property,
Lion's finitely many coefficient leaves cover the critical trace.  A target
which is regular both on the original leaf and on every coefficient leaf
then has the required component-section property.  This file proves that
last geometric assembly exactly; the remaining analytic work is to prove
that the two regular-value conditions hold on a full set of parameters.
-/

noncomputable section

open Set Function MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

namespace LionCarpetedLeaf

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)} {n q p : ℕ}

/-- A target value at which `g` is submersive on a carpeted leaf.  The
appended derivative is the coordinate form of the derivative of `g`
restricted to the leaf tangent space. -/
def IsRegularTarget
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (t : RealEuclidean p) : Prop :=
  ∀ x ∈ L.carrier, g x = t →
    Function.Surjective (fderiv ℝ (L.definingTupleAppend g) x)

/-- Values attained at a critical point of `g` restricted to the leaf. -/
def criticalTargetSet
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p) : Set (RealEuclidean p) :=
  {t | ∃ x ∈ L.carrier, g x = t ∧
    ¬Function.Surjective (fderiv ℝ (L.definingTupleAppend g) x)}

theorem not_mem_criticalTargetSet_iff_isRegularTarget
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (t : RealEuclidean p) :
    t ∉ L.criticalTargetSet g ↔ L.IsRegularTarget g t := by
  simp only [criticalTargetSet, Set.mem_ofPred_eq, not_exists, not_and,
    IsRegularTarget]
  aesop

theorem mem_regularLocus_of_isRegularTarget
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    {t : RealEuclidean p} (ht : L.IsRegularTarget g t)
    {x : RealEuclidean n} (hx : x ∈ L.carrier) (hgx : g x = t) :
    x ∈ L.regularLocus g := by
  exact ⟨hx.1, ht x hx hgx⟩

/-- At a regular target, passing from a leaf to the regular leaf of `g`
does not change that fiber. -/
theorem regularLeaf_fiber_eq_of_isRegularTarget
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (t : RealEuclidean p) (ht : L.IsRegularTarget g t) :
    (L.regularLeaf hG hsmooth hderiv g hg).fiber g t = L.fiber g t := by
  ext x
  rw [fiber, fiber, regularLeaf_carrier_eq_inter_regularLocus]
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨hx, _hxreg⟩, hgx⟩
    exact ⟨hx, hgx⟩
  · rintro ⟨hx, hgx⟩
    exact ⟨⟨hx, L.mem_regularLocus_of_isRegularTarget g ht hx hgx⟩, hgx⟩

private theorem carrier_castCodimension
    {r s : ℕ} (e : r = s) (K : LionCarpetedLeaf G n r) :
    (cast (congrArg (LionCarpetedLeaf G n) e) K).carrier = K.carrier := by
  cases e
  rfl

/-- Every coefficient leaf is a subleaf of the original leaf. -/
theorem selectedCriticalCoefficientLeaf_carrier_subset
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    (selection : CriticalCoefficientSelection n q p) :
    (L.selectedCriticalCoefficientLeaf
      hG hsmooth hderiv g hg center hheight hdim selection).carrier ⊆
      L.carrier := by
  intro x hx
  unfold selectedCriticalCoefficientLeaf at hx
  rw [carrier_castCodimension
    (criticalCoefficientLeaf_codimension hdim)
    (L.selectedCriticalCoefficientLeafRaw
      hG hsmooth hderiv g hg center hheight selection)] at hx
  rw [selectedCriticalCoefficientLeafRaw,
    L.regularZeroSectionLeaf_carrier hG hsmooth hderiv
      (L.selectedCriticalCoefficientTuple g center height selection)
      (L.selectedCriticalCoefficientTuple_mem
        hG hderiv g hg center hheight selection)] at hx
  exact hx.1

/-- The final leaf `Z_i` in Lion's Lemma 4 is the regular part of one
coefficient leaf for the map `g`. -/
def selectedCriticalSectionLeaf
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    (selection : CriticalCoefficientSelection n q p) :
    LionCarpetedLeaf G n (n - p) :=
  (L.selectedCriticalCoefficientLeaf
    hG hsmooth hderiv g hg center hheight hdim selection).regularLeaf
      hG hsmooth hderiv g hg

/-- Every final section leaf lies in the original leaf. -/
theorem selectedCriticalSectionLeaf_carrier_subset
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    (selection : CriticalCoefficientSelection n q p) :
    (L.selectedCriticalSectionLeaf
      hG hsmooth hderiv g hg center hheight hdim selection).carrier ⊆
      L.carrier := by
  intro x hx
  have hxcoeff : x ∈ (L.selectedCriticalCoefficientLeaf
      hG hsmooth hderiv g hg center hheight hdim selection).carrier := by
    rw [selectedCriticalSectionLeaf,
      regularLeaf_carrier_eq_inter_regularLocus] at hx
    exact hx.1
  exact L.selectedCriticalCoefficientLeaf_carrier_subset
    hG hsmooth hderiv g hg center hheight hdim selection hxcoeff

/-- At a target regular on a coefficient leaf, every point of that leaf's
fiber belongs to the corresponding final section leaf. -/
theorem mem_selectedCriticalSectionLeaf_of_regularTarget
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    (selection : CriticalCoefficientSelection n q p)
    {t : RealEuclidean p}
    (ht : (L.selectedCriticalCoefficientLeaf
      hG hsmooth hderiv g hg center hheight hdim selection).IsRegularTarget g t)
    {x : RealEuclidean n}
    (hx : x ∈ (L.selectedCriticalCoefficientLeaf
      hG hsmooth hderiv g hg center hheight hdim selection).carrier)
    (hgx : g x = t) :
    x ∈ (L.selectedCriticalSectionLeaf
      hG hsmooth hderiv g hg center hheight hdim selection).carrier := by
  rw [selectedCriticalSectionLeaf,
    regularLeaf_carrier_eq_inter_regularLocus]
  exact ⟨hx,
    (L.selectedCriticalCoefficientLeaf
      hG hsmooth hderiv g hg center hheight hdim selection)
        |>.mem_regularLocus_of_isRegularTarget g ht hx hgx⟩

/-- The targets which are regular on the original leaf and simultaneously
on every member of the finite coefficient-leaf family. -/
def lemma4GoodTargetSet
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n) : Set (RealEuclidean p) :=
  (L.criticalTargetSet g)ᶜ ∩
    ⋂ selection : CriticalCoefficientSelection n q p,
      ((L.selectedCriticalCoefficientLeaf
        hG hsmooth hderiv g hg center hheight hdim selection)
          |>.criticalTargetSet g)ᶜ

theorem mem_lemma4GoodTargetSet_iff
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n) (t : RealEuclidean p) :
    t ∈ L.lemma4GoodTargetSet
        hG hsmooth hderiv g hg center hheight hdim ↔
      L.IsRegularTarget g t ∧
        ∀ selection : CriticalCoefficientSelection n q p,
          (L.selectedCriticalCoefficientLeaf
            hG hsmooth hderiv g hg center hheight hdim selection)
              |>.IsRegularTarget g t := by
  rw [lemma4GoodTargetSet, Set.mem_inter_iff, Set.mem_compl_iff,
    L.not_mem_criticalTargetSet_iff_isRegularTarget]
  simp only [Set.mem_iInter, Set.mem_compl_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro selection
  exact (L.selectedCriticalCoefficientLeaf
    hG hsmooth hderiv g hg center hheight hdim selection)
      |>.not_mem_criticalTargetSet_iff_isRegularTarget g t

/-- If rectangular Morse--Sard makes the original and all selected-leaf
critical target sets null, the simultaneous good-target set is full in the
measure-theoretic sense used by Lion. -/
theorem volume_compl_lemma4GoodTargetSet_eq_zero
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    (hnullL : volume (L.criticalTargetSet g) = 0)
    (hnullSections : ∀ selection : CriticalCoefficientSelection n q p,
      volume ((L.selectedCriticalCoefficientLeaf
        hG hsmooth hderiv g hg center hheight hdim selection)
          |>.criticalTargetSet g) = 0) :
    volume (L.lemma4GoodTargetSet
      hG hsmooth hderiv g hg center hheight hdim)ᶜ = 0 := by
  rw [lemma4GoodTargetSet, compl_inter, compl_compl,
    measure_union_null_iff]
  refine ⟨hnullL, ?_⟩
  rw [compl_iInter]
  apply measure_iUnion_null
  intro selection
  simpa only [compl_compl] using hnullSections selection

/-- The complete geometric conclusion of Lion's Lemma 4 after the two Sard
choices.  Every connected component of the original regular fiber meets one
of the finitely indexed final section leaves. -/
theorem exists_selectedCriticalSectionLeaf_point_in_connectedComponent
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    (hselection :
      L.HasCriticalTraceRegularCoefficientSelection g center height)
    (t : RealEuclidean p) (htL : L.IsRegularTarget g t)
    (htSections : ∀ selection : CriticalCoefficientSelection n q p,
      (L.selectedCriticalCoefficientLeaf
        hG hsmooth hderiv g hg center hheight hdim selection)
          |>.IsRegularTarget g t)
    (x : L.fiber g t) :
    ∃ selection : CriticalCoefficientSelection n q p,
      ∃ y : L.fiber g t,
        y ∈ connectedComponent x ∧
          (y : RealEuclidean n) ∈
            (L.selectedCriticalSectionLeaf
              hG hsmooth hderiv g hg center hheight hdim selection).carrier := by
  let K := L.criticalLeaf hG hsmooth hderiv center hheight g hg
  have hKfiber : K.fiber g t = L.fiber g t := by
    ext z
    rw [fiber, fiber,
      L.criticalLeaf_carrier hG hsmooth hderiv center hheight g hg]
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨hz, _hzreg⟩, hgz⟩
      exact ⟨hz, hgz⟩
    · rintro ⟨hz, hgz⟩
      exact ⟨⟨hz, L.mem_regularLocus_of_isRegularTarget g htL hz hgz⟩, hgz⟩
  let xK : K.fiber g t := ⟨x, hKfiber.symm ▸ x.property⟩
  obtain ⟨yK, hycomponent, hytrace⟩ :=
    L.exists_criticalTrace_point_in_connectedComponent
      hG hsmooth hderiv g hg center hheight t xK
  obtain ⟨selection, hselectedSurj⟩ :=
    hselection (yK : RealEuclidean n) hytrace
  have hyCoeff : (yK : RealEuclidean n) ∈
      (L.selectedCriticalCoefficientLeaf
        hG hsmooth hderiv g hg center hheight hdim selection).carrier :=
    L.mem_selectedCriticalCoefficientLeaf_of_mem_criticalTrace
      hG hsmooth hderiv g hg center hheight hdim selection
      hytrace hselectedSurj
  have hyg : g (yK : RealEuclidean n) = t := yK.property.2
  have hySection : (yK : RealEuclidean n) ∈
      (L.selectedCriticalSectionLeaf
        hG hsmooth hderiv g hg center hheight hdim selection).carrier :=
    L.mem_selectedCriticalSectionLeaf_of_regularTarget
      hG hsmooth hderiv g hg center hheight hdim selection
      (htSections selection) hyCoeff hyg
  have hyLprop : (yK : RealEuclidean n) ∈ L.fiber g t :=
    hKfiber ▸ yK.property
  let inclusion : K.fiber g t → L.fiber g t := fun z ↦
    ⟨z, hKfiber ▸ z.property⟩
  have hinclusion : Continuous inclusion := by
    exact Continuous.subtype_mk continuous_subtype_val _
  have hycomponentL : inclusion yK ∈ connectedComponent (inclusion xK) :=
    hinclusion.mapsTo_connectedComponent xK hycomponent
  refine ⟨selection, ⟨(yK : RealEuclidean n), hyLprop⟩, ?_, hySection⟩
  simpa only [inclusion, xK] using hycomponentL

/-- Good-target-set form of the component-section conclusion. -/
theorem exists_selectedCriticalSectionLeaf_point_in_connectedComponent_of_mem_good
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n)
    (hselection :
      L.HasCriticalTraceRegularCoefficientSelection g center height)
    (t : RealEuclidean p)
    (ht : t ∈ L.lemma4GoodTargetSet
      hG hsmooth hderiv g hg center hheight hdim)
    (x : L.fiber g t) :
    ∃ selection : CriticalCoefficientSelection n q p,
      ∃ y : L.fiber g t,
        y ∈ connectedComponent x ∧
          (y : RealEuclidean n) ∈
            (L.selectedCriticalSectionLeaf
              hG hsmooth hderiv g hg center hheight hdim selection).carrier := by
  have hregular := (L.mem_lemma4GoodTargetSet_iff
    hG hsmooth hderiv g hg center hheight hdim t).mp ht
  exact L.exists_selectedCriticalSectionLeaf_point_in_connectedComponent
    hG hsmooth hderiv g hg center hheight hdim hselection t
      hregular.1 hregular.2 x

end LionCarpetedLeaf

end AbelFormalization
