import AbelFormalization.CharbonnelDescriptionAlgebra
import AbelFormalization.ClosedZeroSetCharbonnelBridge
import AbelFormalization.GeneralCodimensionRegularComponents
import AbelFormalization.LionUniformRegularFiberEncoding

/-!
# A fixed square encoding for globally submersive family maps

This file implements the part of Lion's fixed-square reduction that is
available for a rectangular map whose derivative is surjective everywhere.
The one square map records a squared-distance center in its target, so it is
independent of the original fiber target.  A center may still be selected
separately for each fiber.

This does not treat singular fibers.  Extending the construction through a
finite rank-stratum reduction, with one fixed family map and one uniform
bound, remains a separate obligation.
-/

noncomputable section

open Set Function
open scoped BigOperators ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-! ## Flattening a parameter-recording square map -/

/-- Concatenation as a continuous linear equivalence. -/
def realEuclideanAppendContinuousLinearEquiv (n m : ℕ) :
    (RealEuclidean n × RealEuclidean m) ≃L[ℝ] RealEuclidean (n + m) :=
  (realEuclideanAppendLinearEquiv n m).toContinuousLinearEquiv

@[simp]
theorem realEuclideanAppendContinuousLinearEquiv_apply
    {n m : ℕ} (p : RealEuclidean n × RealEuclidean m) :
    realEuclideanAppendContinuousLinearEquiv n m p =
      realEuclideanAppend p.1 p.2 :=
  rfl

@[simp]
theorem realEuclideanAppendContinuousLinearEquiv_symm_apply
    {n m : ℕ} (v : RealEuclidean (n + m)) :
    (realEuclideanAppendContinuousLinearEquiv n m).symm v =
      (realEuclideanTakeLeft v, realEuclideanTakeRight v) :=
  rfl

/-- Flatten a square map on `ℝⁿ × ℝᵐ` after recording the parameter in the
output. -/
def flatParameterRecordingMap {n m : ℕ}
    (f : (RealEuclidean n × RealEuclidean m) → RealEuclidean n) :
    RealEuclidean (n + m) → RealEuclidean (n + m) :=
  let E := realEuclideanAppendContinuousLinearEquiv n m
  E ∘ parameterRecordingMap f ∘ E.symm

@[simp]
theorem flatParameterRecordingMap_append
    {n m : ℕ}
    (f : (RealEuclidean n × RealEuclidean m) → RealEuclidean n)
    (x : RealEuclidean n) (p : RealEuclidean m) :
    flatParameterRecordingMap f (realEuclideanAppend x p) =
      realEuclideanAppend (f (x, p)) p := by
  simp [flatParameterRecordingMap, Function.comp_def, parameterRecordingMap]

/-- Global `C¹` regularity survives flattening and recording the parameter. -/
theorem contDiff_flatParameterRecordingMap
    {n m : ℕ}
    {f : (RealEuclidean n × RealEuclidean m) → RealEuclidean n}
    (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (flatParameterRecordingMap f) := by
  let E := realEuclideanAppendContinuousLinearEquiv n m
  have hrecord : ContDiff ℝ 1 (parameterRecordingMap f) := by
    exact hf.prodMk contDiff_snd
  exact E.contDiff.comp (hrecord.comp E.symm.contDiff)

/-- If the derivative in the non-parameter variable is onto, the flattened
parameter-recording square map has onto derivative. -/
theorem surjective_fderiv_flatParameterRecordingMap
    {n m : ℕ}
    {f : (RealEuclidean n × RealEuclidean m) → RealEuclidean n}
    {p : RealEuclidean n × RealEuclidean m}
    (hf : DifferentiableAt ℝ f p)
    (hpartial : Function.Surjective (fstPartial (fderiv ℝ f p))) :
    Function.Surjective
      (fderiv ℝ (flatParameterRecordingMap f)
        (realEuclideanAppend p.1 p.2)) := by
  let E := realEuclideanAppendContinuousLinearEquiv n m
  have hrecord : Function.Surjective
      (fderiv ℝ (parameterRecordingMap f) p) :=
    surjective_fderiv_parameterRecordingMap_of_surjective_fstPartial
      hf hpartial
  have hderiv :
      fderiv ℝ (flatParameterRecordingMap f) (E p) =
        (E : (RealEuclidean n × RealEuclidean m) →L[ℝ]
          RealEuclidean (n + m)).comp
          ((fderiv ℝ (parameterRecordingMap f) p).comp
            (E.symm : RealEuclidean (n + m) →L[ℝ]
              (RealEuclidean n × RealEuclidean m))) := by
    change fderiv ℝ (E ∘ parameterRecordingMap f ∘ E.symm) (E p) = _
    rw [E.comp_fderiv, E.symm.comp_right_fderiv, E.symm_apply_apply]
  rw [show realEuclideanAppend p.1 p.2 = E p by rfl, hderiv]
  exact E.surjective.comp (hrecord.comp E.symm.surjective)

/-! ## The parameter-recording Lagrange map -/

/-- The fixed square map whose first block is the Lagrange critical family
and whose last block records the squared-distance center. -/
def lagrangeParameterRecordingSquareMap {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) :
    RealEuclidean ((a + k) + a) → RealEuclidean ((a + k) + a) :=
  flatParameterRecordingMap (lagrangeSquaredDistanceCriticalFamily H)

@[simp]
theorem lagrangeParameterRecordingSquareMap_append
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (z : RealEuclidean (a + k)) (center : RealEuclidean a) :
    lagrangeParameterRecordingSquareMap H
        (realEuclideanAppend z center) =
      realEuclideanAppend
        (lagrangeCriticalSystemMap H
          (standardSquaredDistance center) z)
        center := by
  simp [lagrangeParameterRecordingSquareMap,
    lagrangeSquaredDistanceCriticalFamily]

@[simp]
theorem lagrangeParameterRecordingSquareMap_stationarity
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (v : RealEuclidean ((a + k) + a)) (j : Fin a) :
    lagrangeParameterRecordingSquareMap H v
        (Fin.castAdd a (Fin.castAdd k j)) =
      lagrangeStationarityEquation H
          (standardSquaredDistance (0 : RealEuclidean a)) j
          (realEuclideanTakeLeft v) -
        2 * realEuclideanTakeRight v j := by
  calc
    lagrangeParameterRecordingSquareMap H v
        (Fin.castAdd a (Fin.castAdd k j)) =
      lagrangeParameterRecordingSquareMap H
          (realEuclideanAppend (realEuclideanTakeLeft v)
            (realEuclideanTakeRight v))
          (Fin.castAdd a (Fin.castAdd k j)) := by
        rw [realEuclideanAppend_takeLeft_takeRight]
    _ = lagrangeStationarityEquation H
          (standardSquaredDistance (0 : RealEuclidean a)) j
          (realEuclideanTakeLeft v) -
        2 * realEuclideanTakeRight v j := by
      simp only [lagrangeParameterRecordingSquareMap_append,
        realEuclideanAppend_castAdd,
        lagrangeCriticalSystemMap_apply_castAdd,
        lagrangeStationarityEquation_standardSquaredDistance_apply,
        lagrangePrimalProjection_apply, Pi.zero_apply]
      ring

@[simp]
theorem lagrangeParameterRecordingSquareMap_constraint
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (v : RealEuclidean ((a + k) + a)) (i : Fin k) :
    lagrangeParameterRecordingSquareMap H v
        (Fin.castAdd a (Fin.natAdd a i)) =
      H i (lagrangePrimalProjection a k (realEuclideanTakeLeft v)) := by
  simp [lagrangeParameterRecordingSquareMap, flatParameterRecordingMap,
    parameterRecordingMap, Function.comp_def,
    lagrangeSquaredDistanceCriticalFamily, lagrangeConstraintEquation]

@[simp]
theorem lagrangeParameterRecordingSquareMap_center
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (v : RealEuclidean ((a + k) + a)) (j : Fin a) :
    lagrangeParameterRecordingSquareMap H v
        (Fin.natAdd (a + k) j) =
      realEuclideanTakeRight v j := by
  simp [lagrangeParameterRecordingSquareMap, flatParameterRecordingMap,
    parameterRecordingMap, Function.comp_def]

/-- The recorded-center square tuple belongs to the same family as the raw
constraints.  In particular its source is fixed independently of the fiber
target. -/
theorem IsGeometricFunctionFamily.lagrangeParameterRecordingSquareMap_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (hHmem : ∀ i, H i ∈ G a) :
    FunctionTupleInFamily G (lagrangeParameterRecordingSquareMap H) := by
  intro q
  refine Fin.addCases (fun j ↦ ?_) (fun c ↦ ?_) q
  · refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) j
    · let pull : RealEuclidean ((a + k) + a) →ₗ[ℝ]
          RealEuclidean (a + k) :=
        realEuclideanTakeLeftLinearMap (a + k) a
      have hcenterZero :
          lagrangeStationarityEquation H
              (standardSquaredDistance (0 : RealEuclidean a)) j ∈
            G (a + k) := by
        have hsquareMem :
            standardSquaredDistance (0 : RealEuclidean a) ∈ G a := by
          simpa [standardSquaredDistance] using
            (hG.standardSquaredDistance_mem (0 : RealEuclidean a))
        exact hG.lagrangeStationarityEquation_mem hderiv H
          (standardSquaredDistance (0 : RealEuclidean a)) hHmem hsquareMem j
      have hstationarity :
          (fun v : RealEuclidean ((a + k) + a) ↦
            lagrangeStationarityEquation H
              (standardSquaredDistance (0 : RealEuclidean a)) j
              (realEuclideanTakeLeft v)) ∈ G ((a + k) + a) := by
        change (lagrangeStationarityEquation H
            (standardSquaredDistance (0 : RealEuclidean a)) j ∘
          pull.toAffineMap) ∈ G ((a + k) + a)
        exact hG.affine_comp hcenterZero pull.toAffineMap
      have hcenter :
          (fun v : RealEuclidean ((a + k) + a) ↦
            2 * realEuclideanTakeRight v j) ∈ G ((a + k) + a) := by
        have hcoordinate :
            (fun v : RealEuclidean ((a + k) + a) ↦
              v (Fin.natAdd (a + k) j)) ∈ G ((a + k) + a) := by
          simpa using hG.polynomial
            (MvPolynomial.X (Fin.natAdd (a + k) j))
        have hconstant := hG.const_mem
          (n := (a + k) + a) (2 : ℝ)
        have hmul := hG.mul hconstant hcoordinate
        change (fun v : RealEuclidean ((a + k) + a) ↦
          2 * v (Fin.natAdd (a + k) j)) ∈ G ((a + k) + a) at hmul
        simpa only [realEuclideanTakeRight] using hmul
      have hresult := hG.sub_mem hstationarity hcenter
      change (fun v : RealEuclidean ((a + k) + a) ↦
        lagrangeStationarityEquation H
          (standardSquaredDistance (0 : RealEuclidean a)) j
          (realEuclideanTakeLeft v) -
        2 * realEuclideanTakeRight v j) ∈ G ((a + k) + a) at hresult
      simpa only [lagrangeParameterRecordingSquareMap_stationarity] using hresult
    · let pull : RealEuclidean ((a + k) + a) →ₗ[ℝ]
          RealEuclidean a :=
        (lagrangePrimalProjection a k).comp
          (realEuclideanTakeLeftLinearMap (a + k) a)
      have hconstraint :
          (fun v : RealEuclidean ((a + k) + a) ↦
            H i (lagrangePrimalProjection a k (realEuclideanTakeLeft v))) ∈
          G ((a + k) + a) := by
        change (H i ∘ pull.toAffineMap) ∈ G ((a + k) + a)
        exact hG.affine_comp (hHmem i) pull.toAffineMap
      simpa only [lagrangeParameterRecordingSquareMap_constraint] using
        hconstraint
  · have hcoordinate :
        (fun v : RealEuclidean ((a + k) + a) ↦
          v (Fin.natAdd (a + k) c)) ∈ G ((a + k) + a) := by
      simpa using hG.polynomial
        (MvPolynomial.X (Fin.natAdd (a + k) c))
    simpa only [lagrangeParameterRecordingSquareMap_center,
      realEuclideanTakeRight] using hcoordinate

/-! ## Choosing a center at each raw fiber target -/

/-- On a globally submersive constraint map, a squared-distance center can
be selected for each raw target `t` so that every Lagrange critical point
over that target is regular.  The constraints themselves remain `H_i`,
independent of `t`; this is the key to obtaining one recorded-center map. -/
theorem exists_center_regular_lagrangeCriticalSystem_at_target
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (hH : ∀ i, ContDiff ℝ 2 (H i))
    (hsurj : ∀ x : RealEuclidean a,
      (constraintFDeriv H x).range = ⊤)
    (t : RealEuclidean k) :
    ∃ center : RealEuclidean a,
      ∀ z : RealEuclidean (a + k),
        lagrangeCriticalSystemMap H
            (standardSquaredDistance center) z =
          realEuclideanAppend (0 : RealEuclidean a) t →
        (fderiv ℝ (lagrangeCriticalSystemMap H
          (standardSquaredDistance center)) z).range = ⊤ := by
  let Phi := lagrangeSquaredDistanceCriticalFamily H
  let target : RealEuclidean (a + k) :=
    realEuclideanAppend (0 : RealEuclidean a) t
  let S : Set (RealEuclidean (a + k) × RealEuclidean a) :=
    {p | Phi p = target}
  have hPhiGlobal : ContDiff ℝ 1 Phi :=
    contDiff_lagrangeSquaredDistanceCriticalFamily H hH
  have hPhi : ∀ p ∈ S, ContDiffAt ℝ 1 Phi p := by
    intro p _hp
    exact hPhiGlobal.contDiffAt
  have hSurj : ∀ p ∈ S,
      (fderiv ℝ Phi p).range = ⊤ := by
    intro p _hp
    exact lagrangeSquaredDistanceCriticalFamily_fderiv_range_eq_top
      H p.1 p.2
      (hPhiGlobal.differentiable (by norm_num) p)
      (fun i ↦ ((hH i).differentiable (by norm_num)).differentiableAt)
      (hsurj (lagrangePrimalProjection a k p.1))
  obtain ⟨center, hcenter⟩ := exists_parameter_with_regular_fixed_slice
    Phi S target hPhi rfl (fun p hp ↦ hp) hSurj
  refine ⟨center, ?_⟩
  intro z hz
  have hzS : (z, center) ∈ S := by
    change Phi (z, center) = target
    change lagrangeCriticalSystemMap H
      (standardSquaredDistance center) z =
      realEuclideanAppend (0 : RealEuclidean a) t
    exact hz
  have hfixed := hcenter (z, center) hzS rfl
  have hfamily : DifferentiableAt ℝ Phi (z, center) :=
    (hPhiGlobal.differentiable (by norm_num)).differentiableAt
  rw [fderiv_lagrangeSquaredDistanceCriticalFamily_fixed_center
    H z center hfamily]
  exact hfixed

/-! ## Componentwise critical points at a nonzero constraint target -/

/-- The raw Lagrange system at target `(0,t)` is exactly feasibility at
`t` together with the stationarity covector equation. -/
theorem lagrangeCriticalSystemMap_append_eq_target_iff
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (rho : RealEuclideanFunction a) (x : RealEuclidean a)
    (lambda t : RealEuclidean k) :
    lagrangeCriticalSystemMap H rho (realEuclideanAppend x lambda) =
        realEuclideanAppend (0 : RealEuclidean a) t ↔
      (∀ i, H i x = t i) ∧
        lagrangeStationarityCovector H rho x lambda = 0 := by
  constructor
  · intro hsystem
    have hconstraint : ∀ i, H i x = t i := by
      intro i
      have hi := congrFun hsystem (Fin.natAdd a i)
      simpa only [lagrangeCriticalSystemMap_apply_natAdd,
        lagrangeConstraintEquation_append,
        realEuclideanAppend_natAdd] using hi
    have hstationarity : ∀ j,
        lagrangeStationarityEquation H rho j
          (realEuclideanAppend x lambda) = 0 := by
      intro j
      have hj := congrFun hsystem (Fin.castAdd k j)
      simpa only [lagrangeCriticalSystemMap_apply_castAdd,
        realEuclideanAppend_castAdd, Pi.zero_apply] using hj
    exact ⟨hconstraint,
      (lagrangeStationarityEquations_zero_iff_covector_eq_zero
        H rho x lambda).mp hstationarity⟩
  · rintro ⟨hconstraint, hstationarity⟩
    funext q
    refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) q
    · rw [lagrangeCriticalSystemMap_apply_castAdd,
        lagrangeStationarityEquation_append_eq_covector_apply,
        hstationarity]
      simp
    · simpa only [lagrangeCriticalSystemMap_apply_natAdd,
        lagrangeConstraintEquation_append,
        realEuclideanAppend_natAdd] using hconstraint i

end AbelFormalization
