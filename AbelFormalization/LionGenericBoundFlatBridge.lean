import AbelFormalization.LionLowDimensionalImageNullity
import AbelFormalization.LionTheorem7FlatCompactificationBridge
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# From the numerical Theorem 7' bound to Lion's flat full parameter sets

A conull subset of the flat Euclidean target pulls back to a conull subset
of the product coordinates `(eta, epsilon, T)`.  Fubini then shrinks this to
the nested full set used in Lion's Lemma 6.  This file composes that fact
with the numerical Theorem 7' induction.
-/

noncomputable section

open Set Function MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-- The one-coordinate linear equivalence used in the flat target. -/
def lionScalarVectorLinearEquiv : ℝ ≃ₗ[ℝ] RealEuclidean 1 :=
  (LinearEquiv.funUnique (Fin 1) ℝ ℝ).symm

/-- Forget the `L²` norm while retaining the coordinates of the Euclidean
 target. -/
def lionEuclideanOfLpLinearEquiv (p : ℕ) :
    EuclideanSpace ℝ (Fin p) ≃ₗ[ℝ] RealEuclidean p :=
  WithLp.linearEquiv 2 ℝ (RealEuclidean p)

/-- Flatten `(epsilon,T)` into the final `1+p` coordinate block. -/
def lionFlatInnerTargetLinearEquiv (p : ℕ) :
    (ℝ × EuclideanSpace ℝ (Fin p)) ≃ₗ[ℝ] RealEuclidean (1 + p) :=
  (lionScalarVectorLinearEquiv.prodCongr
      (lionEuclideanOfLpLinearEquiv p)).trans
    (realEuclideanAppendLinearEquiv 1 p)

/-- The product-to-flat-coordinate equivalence underlying
 `lionFlatCompactificationParameterTarget`. -/
def lionFlatParameterTargetLinearEquiv (p : ℕ) :
    (ℝ × (ℝ × EuclideanSpace ℝ (Fin p))) ≃ₗ[ℝ]
      RealEuclidean (1 + (1 + p)) :=
  (lionScalarVectorLinearEquiv.prodCongr
      (lionFlatInnerTargetLinearEquiv p)).trans
    (realEuclideanAppendLinearEquiv 1 (1 + p))

theorem lionFlatParameterTargetLinearEquiv_apply (p : ℕ) :
    (lionFlatParameterTargetLinearEquiv p :
      (ℝ × (ℝ × EuclideanSpace ℝ (Fin p))) →
        RealEuclidean (1 + (1 + p))) =
      lionFlatCompactificationParameterTarget := by
  funext w
  simp only [lionFlatParameterTargetLinearEquiv,
    lionFlatInnerTargetLinearEquiv, lionScalarVectorLinearEquiv,
    lionEuclideanOfLpLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, realEuclideanAppendLinearEquiv,
    lionFlatCompactificationParameterTarget]
  congr 1

/-- A null set in the flat coordinate target has null preimage in Lion's
 product parameter coordinates. -/
theorem volume_lionFlatParameterTarget_preimage_eq_zero
    {p : ℕ} {S : Set (RealEuclidean (1 + (1 + p)))}
    (hS : (volume : Measure (RealEuclidean (1 + (1 + p)))) S = 0) :
    (volume : Measure (ℝ × (ℝ × EuclideanSpace ℝ (Fin p))))
      (lionFlatCompactificationParameterTarget ⁻¹' S) = 0 := by
  let innerHaar :
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin p))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  letI :
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin p))).IsAddHaarMeasure :=
    innerHaar
  let domainHaar :
      (volume : Measure
        (ℝ × (ℝ × EuclideanSpace ℝ (Fin p)))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  letI :
      (volume : Measure
        (ℝ × (ℝ × EuclideanSpace ℝ (Fin p)))).IsAddHaarMeasure :=
    domainHaar
  let e := lionFlatParameterTargetLinearEquiv p
  let ec := e.toContinuousLinearEquiv
  let em := ec.toHomeomorph.toMeasurableEquiv
  have hmap :
      (Measure.map e volume) S = volume (e ⁻¹' S) := by
    exact em.map_apply S
  have hpre : (volume : Measure
      (ℝ × (ℝ × EuclideanSpace ℝ (Fin p)))) (e ⁻¹' S) = 0 := by
    rw [← hmap]
    let _ : (Measure.map e volume).IsAddHaarMeasure :=
      Measure.MapLinearEquiv.isAddHaarMeasure volume e
    let _ : SigmaFinite (Measure.map e volume) := inferInstance
    have hac : Measure.map e volume ≪
        (volume : Measure (RealEuclidean (1 + (1 + p)))) :=
      Measure.absolutelyContinuous_isAddHaarMeasure _ _
    exact hac hS
  rw [← lionFlatParameterTargetLinearEquiv_apply p]
  exact hpre

/-- A conull product parameter set is full in Lion's nested, fiberwise
 measure-theoretic sense. -/
theorem isLionFullFlatEuclideanParameterSet_of_volume_compl_eq_zero
    {p : ℕ}
    {R : Set (ℝ × (ℝ × EuclideanSpace ℝ (Fin p)))}
    (hR : (volume : Measure
      (ℝ × (ℝ × EuclideanSpace ℝ (Fin p)))) Rᶜ = 0) :
    IsLionFullFlatEuclideanParameterSet R := by
  have hprod :
      ((volume : Measure ℝ).prod
        (volume : Measure (ℝ × EuclideanSpace ℝ (Fin p)))) Rᶜ = 0 := by
    simpa only [← Measure.volume_eq_prod] using hR
  have hae :
      (fun eta : ℝ ↦
        (volume : Measure (ℝ × EuclideanSpace ℝ (Fin p)))
          (Prod.mk eta ⁻¹' Rᶜ)) =ᵐ[volume] 0 :=
    Measure.measure_ae_null_of_prod_null hprod
  let etaSet : Set ℝ := {eta |
    (volume : Measure (ℝ × EuclideanSpace ℝ (Fin p)))
      (Prod.mk eta ⁻¹' Rᶜ) = 0}
  have hetaMem : etaSet ∈ ae (volume : Measure ℝ) := hae
  refine ⟨etaSet, mem_ae_iff.mp hetaMem, ?_⟩
  intro eta heta
  have hetaNull :
      (volume : Measure (ℝ × EuclideanSpace ℝ (Fin p)))
        (Prod.mk eta ⁻¹' Rᶜ) = 0 := heta
  have heq : (lionParameterFiber R eta)ᶜ =
      Prod.mk eta ⁻¹' Rᶜ := by
    ext w
    simp [lionParameterFiber]
  rw [heq]
  exact hetaNull

/-- The numerical Theorem 7' induction supplies the full generic bounds for
 all standard flat compactifications. -/
theorem hasLionFullGenericFlatCompactificationBoundsForFamily_of_morseSard_radialSelections
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    (hMS : ∀ {a b : ℕ}, b ≤ a →
      ∀ H : RealEuclidean a → RealEuclidean b,
        ContDiff ℝ (a - b + 1 : ℕ) H →
          volume (standardJacobianCriticalValueSet H) = 0)
    (hselect : HasLionLemma4RadialSelections G) :
    HasLionFullGenericFlatCompactificationBoundsForFamily G := by
  intro a p g hg
  let F := lionFlatCompactificationMap (lionStandardCarpet a) g
  have hF : FunctionTupleInFamily G F :=
    hG.lionStandardFlatCompactificationMap_mem g hg
  let L := lionWholeSpaceStandardLeaf hG (a + (1 + (1 + p)))
  obtain ⟨output⟩ := exists_lionGenericFiberBound
    hG hsmooth hderiv hzero hMS
      (hasLionLowDimensionalImageNullity hsmooth) hselect L F hF (by omega)
  let R : Set (ℝ × (ℝ × EuclideanSpace ℝ (Fin p))) :=
    lionFlatCompactificationParameterTarget ⁻¹' output.goodTargets
  have hRcompl : (volume : Measure
      (ℝ × (ℝ × EuclideanSpace ℝ (Fin p)))) Rᶜ = 0 := by
    have heq : Rᶜ = lionFlatCompactificationParameterTarget ⁻¹'
        output.goodTargetsᶜ := by
      ext w
      simp [R]
    rw [heq]
    exact volume_lionFlatParameterTarget_preimage_eq_zero
      output.goodTargets_conull
  refine ⟨output.bound, R,
    isLionFullFlatEuclideanParameterSet_of_volume_compl_eq_zero hRcompl, ?_⟩
  intro w hw
  have hbound := output.component_bound
    (lionFlatCompactificationParameterTarget w) hw
  have hfiber : L.fiber F (lionFlatCompactificationParameterTarget w) =
      F ⁻¹' {lionFlatCompactificationParameterTarget w} := by
    ext x
    simp only [LionCarpetedLeaf.fiber, Set.mem_ofPred_eq,
      Set.mem_preimage, Set.mem_singleton_iff]
    rw [show L.carrier = Set.univ by
      exact lionWholeSpaceStandardLeaf_carrier hG _]
    simp
  rw [hfiber] at hbound
  exact hbound

/-- The proved smooth rectangular Morse--Sard theorem supplies the full
generic bounds for all standard flat compactifications. -/
theorem hasLionFullGenericFlatCompactificationBoundsForFamily_of_radialSelections
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    (hselect : HasLionLemma4RadialSelections G) :
    HasLionFullGenericFlatCompactificationBoundsForFamily G := by
  intro a p g hg
  let F := lionFlatCompactificationMap (lionStandardCarpet a) g
  have hF : FunctionTupleInFamily G F :=
    hG.lionStandardFlatCompactificationMap_mem g hg
  let L := lionWholeSpaceStandardLeaf hG (a + (1 + (1 + p)))
  obtain ⟨output⟩ := exists_lionGenericFiberBound_of_contDiff_top
    hG hsmooth hderiv hzero
      (hasLionLowDimensionalImageNullity hsmooth) hselect L F hF (by omega)
  let R : Set (ℝ × (ℝ × EuclideanSpace ℝ (Fin p))) :=
    lionFlatCompactificationParameterTarget ⁻¹' output.goodTargets
  have hRcompl : (volume : Measure
      (ℝ × (ℝ × EuclideanSpace ℝ (Fin p)))) Rᶜ = 0 := by
    have heq : Rᶜ = lionFlatCompactificationParameterTarget ⁻¹'
        output.goodTargetsᶜ := by
      ext w
      simp [R]
    rw [heq]
    exact volume_lionFlatParameterTarget_preimage_eq_zero
      output.goodTargets_conull
  refine ⟨output.bound, R,
    isLionFullFlatEuclideanParameterSet_of_volume_compl_eq_zero hRcompl, ?_⟩
  intro w hw
  have hbound := output.component_bound
    (lionFlatCompactificationParameterTarget w) hw
  have hfiber : L.fiber F (lionFlatCompactificationParameterTarget w) =
      F ⁻¹' {lionFlatCompactificationParameterTarget w} := by
    ext x
    simp only [LionCarpetedLeaf.fiber, Set.mem_ofPred_eq,
      Set.mem_preimage, Set.mem_singleton_iff]
    rw [show L.carrier = Set.univ by
      exact lionWholeSpaceStandardLeaf_carrier hG _]
    simp
  rw [hfiber] at hbound
  exact hbound

/-- Direct family-level endpoint of the completed numerical Theorem 7'
 induction and Lion's flat compactification lemma. -/
theorem hasUniformFiberFiniteness_of_morseSard_radialSelections
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    (hMS : ∀ {a b : ℕ}, b ≤ a →
      ∀ H : RealEuclidean a → RealEuclidean b,
        ContDiff ℝ (a - b + 1 : ℕ) H →
          volume (standardJacobianCriticalValueSet H) = 0)
    (hselect : HasLionLemma4RadialSelections G) :
    HasUniformFiberFiniteness G := by
  apply hasUniformFiberFiniteness_of_lionFullGenericFlatCompactification
    hsmooth
  exact
    hasLionFullGenericFlatCompactificationBoundsForFamily_of_morseSard_radialSelections
      hG hsmooth hderiv hzero hMS hselect

/-- Direct family-level endpoint with rectangular Morse--Sard discharged by
the proved smooth theorem. -/
theorem hasUniformFiberFiniteness_of_radialSelections
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    (hselect : HasLionLemma4RadialSelections G) :
    HasUniformFiberFiniteness G := by
  apply hasUniformFiberFiniteness_of_lionFullGenericFlatCompactification
    hsmooth
  exact
    hasLionFullGenericFlatCompactificationBoundsForFamily_of_radialSelections
      hG hsmooth hderiv hzero hselect

end AbelFormalization
