import AbelFormalization.GeneralCodimensionLagrange
import AbelFormalization.CountableParametricChartCover
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Generic squared-distance centers for the general Lagrange system

For `k` regular constraints on `ℝ^a`, this file treats the center of squared
distance as a parameter in the augmented Lagrange system on `(x, lambda)`.
The total family is a submersion above the zero constraint locus: primal
variation controls the `k` constraint rows, while center variation controls
all `a` stationarity rows.  The existing parametric Sard argument therefore
supplies a center for which every zero of the fixed-center square system is
regular.

This is a regularity statement for critical-system zeros.  It does not assert
that the zero set is finite or that any component bound is uniform.
-/

noncomputable section

open Set Function Filter
open scoped BigOperators Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-! ## The center-parameter family -/

/-- Continuous-linear form of the primal projection from augmented
`(x, lambda)` coordinates. -/
def lagrangePrimalProjectionCLM (a k : ℕ) :
    RealEuclidean (a + k) →L[ℝ] RealEuclidean a :=
  (lagrangePrimalProjection a k).toContinuousLinearMap

@[simp]
theorem lagrangePrimalProjectionCLM_apply {a k : ℕ}
    (z : RealEuclidean (a + k)) :
    lagrangePrimalProjectionCLM a k z = lagrangePrimalProjection a k z :=
  rfl

/-- The augmented Lagrange system with the squared-distance center exposed as
a parameter. -/
def lagrangeSquaredDistanceCriticalFamily {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) :
    (RealEuclidean (a + k) × RealEuclidean a) → RealEuclidean (a + k) :=
  fun p ↦ lagrangeCriticalSystemMap H (standardSquaredDistance p.2) p.1

@[simp]
theorem lagrangeStationarityEquation_standardSquaredDistance_apply
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (center : RealEuclidean a) (z : RealEuclidean (a + k)) (j : Fin a) :
    lagrangeStationarityEquation H (standardSquaredDistance center) j z =
      2 * (lagrangePrimalProjection a k z j - center j) -
        ∑ i, lagrangeMultiplierCoordinate (a := a) i z *
          fderiv ℝ (H i) (lagrangePrimalProjection a k z)
            (Pi.single j 1) := by
  simp [lagrangeStationarityEquation, lagrangePulledCoordinateFDeriv]

@[simp]
theorem lagrangeSquaredDistanceCriticalFamily_castAdd
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (p : RealEuclidean (a + k) × RealEuclidean a) (j : Fin a) :
    lagrangeSquaredDistanceCriticalFamily H p (Fin.castAdd k j) =
      2 * (lagrangePrimalProjection a k p.1 j - p.2 j) -
        ∑ i, lagrangeMultiplierCoordinate (a := a) i p.1 *
          fderiv ℝ (H i) (lagrangePrimalProjection a k p.1)
            (Pi.single j 1) := by
  simp [lagrangeSquaredDistanceCriticalFamily]

@[simp]
theorem lagrangeSquaredDistanceCriticalFamily_natAdd
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (p : RealEuclidean (a + k) × RealEuclidean a) (i : Fin k) :
    lagrangeSquaredDistanceCriticalFamily H p (Fin.natAdd a i) =
      H i (lagrangePrimalProjection a k p.1) := by
  simp [lagrangeSquaredDistanceCriticalFamily, lagrangeConstraintEquation]

/-- The center derivative of the total family.  It is `-2` times the identity
on the stationarity rows and zero on the constraint rows. -/
def lagrangeSquaredDistanceCriticalFamilyCenterDerivative (a k : ℕ) :
    RealEuclidean a →L[ℝ] RealEuclidean (a + k) :=
  ContinuousLinearMap.pi (fun q ↦
    Fin.addCases
      (fun j ↦ (2 : ℝ) •
        -(ContinuousLinearMap.proj j : RealEuclidean a →L[ℝ] ℝ))
      (fun _ ↦ 0) q)

@[simp]
theorem lagrangeSquaredDistanceCriticalFamilyCenterDerivative_castAdd
    {a k : ℕ} (dc : RealEuclidean a) (j : Fin a) :
    lagrangeSquaredDistanceCriticalFamilyCenterDerivative a k dc
        (Fin.castAdd k j) =
      -(2 * dc j) := by
  simp [lagrangeSquaredDistanceCriticalFamilyCenterDerivative]

@[simp]
theorem lagrangeSquaredDistanceCriticalFamilyCenterDerivative_natAdd
    {a k : ℕ} (dc : RealEuclidean a) (i : Fin k) :
    lagrangeSquaredDistanceCriticalFamilyCenterDerivative a k dc
        (Fin.natAdd a i) = 0 := by
  simp [lagrangeSquaredDistanceCriticalFamilyCenterDerivative]

/-- Center differentiation is explicit and needs no regularity hypothesis on
the constraints. -/
theorem hasStrictFDerivAt_lagrangeSquaredDistanceCriticalFamily_center
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (z : RealEuclidean (a + k)) (center : RealEuclidean a) :
    HasStrictFDerivAt
      (fun c ↦ lagrangeSquaredDistanceCriticalFamily H (z, c))
      (lagrangeSquaredDistanceCriticalFamilyCenterDerivative a k) center := by
  apply hasStrictFDerivAt_pi.mpr
  intro q
  refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) q
  · let x : RealEuclidean a := lagrangePrimalProjection a k z
    let constant : ℝ :=
      ∑ i, lagrangeMultiplierCoordinate (a := a) i z *
        fderiv ℝ (H i) x (Pi.single j 1)
    have hcoord : HasStrictFDerivAt (fun c : RealEuclidean a ↦ c j)
        (ContinuousLinearMap.proj j : RealEuclidean a →L[ℝ] ℝ) center :=
      (ContinuousLinearMap.proj j :
        RealEuclidean a →L[ℝ] ℝ).hasStrictFDerivAt
    have h := ((hcoord.const_sub (x j)).const_mul 2).sub_const constant
    simpa [x, constant,
      lagrangeSquaredDistanceCriticalFamilyCenterDerivative, smul_smul] using h
  · simpa [lagrangeSquaredDistanceCriticalFamilyCenterDerivative] using
      (hasStrictFDerivAt_const
        (H i (lagrangePrimalProjection a k z)) center)

/-! ## Smoothness and total submersivity -/

/-- Two derivatives of the constraints give one derivative of the total
center-parameter family. -/
theorem contDiff_lagrangeSquaredDistanceCriticalFamily
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (hH : ∀ i, ContDiff ℝ 2 (H i)) :
    ContDiff ℝ 1 (lagrangeSquaredDistanceCriticalFamily H) := by
  let P := lagrangePrimalProjectionCLM a k
  have hprimal : ContDiff ℝ 1
      (fun p : RealEuclidean (a + k) × RealEuclidean a ↦ P p.1) :=
    P.contDiff.comp contDiff_fst
  rw [contDiff_pi]
  intro q
  refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) q
  · rw [show (fun p : RealEuclidean (a + k) × RealEuclidean a ↦
        lagrangeSquaredDistanceCriticalFamily H p (Fin.castAdd k j)) =
      fun p ↦ 2 * (P p.1 j - p.2 j) -
        ∑ i, lagrangeMultiplierCoordinate (a := a) i p.1 *
          fderiv ℝ (H i) (P p.1) (Pi.single j 1) by
      funext p
      simp [P]]
    have hxcoord : ContDiff ℝ 1
        (fun p : RealEuclidean (a + k) × RealEuclidean a ↦ P p.1 j) := by
      exact (ContinuousLinearMap.proj j).contDiff.comp hprimal
    have hcentercoord : ContDiff ℝ 1
        (fun p : RealEuclidean (a + k) × RealEuclidean a ↦ p.2 j) := by
      exact (ContinuousLinearMap.proj j :
        RealEuclidean a →L[ℝ] ℝ).contDiff.comp contDiff_snd
    apply (contDiff_const.mul (hxcoord.sub hcentercoord)).sub
    apply ContDiff.sum
    intro t ht
    have hmultiplier : ContDiff ℝ 1
        (fun p : RealEuclidean (a + k) × RealEuclidean a ↦
          lagrangeMultiplierCoordinate (a := a) t p.1) := by
      exact (ContinuousLinearMap.proj (Fin.natAdd a t) :
        RealEuclidean (a + k) →L[ℝ] ℝ).contDiff.comp contDiff_fst
    have hconstraintDerivative : ContDiff ℝ 1
        (fun p : RealEuclidean (a + k) × RealEuclidean a ↦
          fderiv ℝ (H t) (P p.1) (Pi.single j 1)) := by
      have hbase : ContDiff ℝ 1
          (fun x : RealEuclidean a ↦
            fderiv ℝ (H t) x (Pi.single j 1)) :=
        ((hH t).fderiv_right (by norm_num)).clm_apply contDiff_const
      exact hbase.comp hprimal
    exact hmultiplier.mul hconstraintDerivative
  · rw [show (fun p : RealEuclidean (a + k) × RealEuclidean a ↦
        lagrangeSquaredDistanceCriticalFamily H p (Fin.natAdd a i)) =
      fun p ↦ H i (P p.1) by
      funext p
      simp [P]]
    exact ((hH i).of_le (by norm_num)).comp hprimal

/-- Restricting the total family to a fixed center recovers the square
Lagrange map. -/
theorem lagrangeSquaredDistanceCriticalFamily_fixed_center
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (center : RealEuclidean a) :
    (fun z ↦ lagrangeSquaredDistanceCriticalFamily H (z, center)) =
      lagrangeCriticalSystemMap H (standardSquaredDistance center) :=
  rfl

/-- The derivative of a fixed-center system is the primal partial derivative
of the total family. -/
theorem fderiv_lagrangeSquaredDistanceCriticalFamily_fixed_center
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (z : RealEuclidean (a + k)) (center : RealEuclidean a)
    (hfamily : DifferentiableAt ℝ
      (lagrangeSquaredDistanceCriticalFamily H) (z, center)) :
    fderiv ℝ (lagrangeCriticalSystemMap H
      (standardSquaredDistance center)) z =
      fstPartial
        (fderiv ℝ (lagrangeSquaredDistanceCriticalFamily H) (z, center)) := by
  let I : RealEuclidean (a + k) →L[ℝ]
      (RealEuclidean (a + k) × RealEuclidean a) :=
    ContinuousLinearMap.inl ℝ (RealEuclidean (a + k)) (RealEuclidean a)
  have hins : HasFDerivAt (fun w : RealEuclidean (a + k) ↦ (w, center)) I z :=
    hasFDerivAt_prodMk_left z center
  have hcomp := hfamily.hasFDerivAt.comp z hins
  have hcomp' : HasFDerivAt
      (fun w ↦ lagrangeSquaredDistanceCriticalFamily H (w, center))
      ((fderiv ℝ (lagrangeSquaredDistanceCriticalFamily H) (z, center)).comp I)
      z := by
    simpa [Function.comp_def] using hcomp
  rw [lagrangeSquaredDistanceCriticalFamily_fixed_center] at hcomp'
  simpa [fstPartial, I] using hcomp'.fderiv

/-- At a feasible point with surjective constraint derivative, the joint
`((x, lambda), center)` family derivative is surjective. -/
theorem lagrangeSquaredDistanceCriticalFamily_fderiv_range_eq_top
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (z : RealEuclidean (a + k)) (center : RealEuclidean a)
    (hfamily : DifferentiableAt ℝ
      (lagrangeSquaredDistanceCriticalFamily H) (z, center))
    (hH : ∀ i, DifferentiableAt ℝ (H i)
      (lagrangePrimalProjection a k z))
    (hsurj : (constraintFDeriv H
      (lagrangePrimalProjection a k z)).range = ⊤) :
    (fderiv ℝ (lagrangeSquaredDistanceCriticalFamily H)
      (z, center)).range = ⊤ := by
  let L := fderiv ℝ (lagrangeSquaredDistanceCriticalFamily H) (z, center)
  let C := lagrangeSquaredDistanceCriticalFamilyCenterDerivative a k
  let I : RealEuclidean a →L[ℝ]
      (RealEuclidean (a + k) × RealEuclidean a) :=
    (0 : RealEuclidean a →L[ℝ] RealEuclidean (a + k)).prod
      (ContinuousLinearMap.id ℝ (RealEuclidean a))
  have hins : HasFDerivAt
      (fun c : RealEuclidean a ↦ (z, c)) I center := by
    simpa [I] using (hasFDerivAt_const (𝕜 := ℝ) z center).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) center)
  have hsliceFull : HasFDerivAt
      (fun c ↦ lagrangeSquaredDistanceCriticalFamily H (z, c))
      (L.comp I) center := by
    simpa [L, Function.comp_def] using hfamily.hasFDerivAt.comp center hins
  have hsliceExplicit : HasFDerivAt
      (fun c ↦ lagrangeSquaredDistanceCriticalFamily H (z, c)) C center :=
    (hasStrictFDerivAt_lagrangeSquaredDistanceCriticalFamily_center
      H z center).hasFDerivAt
  have hcenterDerivative : L.comp I = C :=
    hsliceFull.unique hsliceExplicit
  rw [LinearMap.range_eq_top]
  intro y
  let yH : RealEuclidean k := fun i ↦ y (Fin.natAdd a i)
  obtain ⟨dx, hdx⟩ := LinearMap.range_eq_top.mp hsurj yH
  let dz : RealEuclidean (a + k) :=
    realEuclideanAppend dx (0 : RealEuclidean k)
  let w : RealEuclidean (a + k) := L (dz, 0)
  let dc : RealEuclidean a :=
    fun j ↦ (w (Fin.castAdd k j) - y (Fin.castAdd k j)) / 2
  refine ⟨(dz, dc), ?_⟩
  have hcenterApply : L (0, dc) = C dc := by
    have h := congrArg
      (fun T : RealEuclidean a →L[ℝ] RealEuclidean (a + k) ↦ T dc)
      hcenterDerivative
    simpa [I] using h
  have hconstraintCoord : ∀ i : Fin k,
      w (Fin.natAdd a i) = y (Fin.natAdd a i) := by
    intro i
    let P := lagrangePrimalProjectionCLM a k
    have hcomponent :=
      fderiv_apply hfamily (Fin.natAdd a i)
    have hHi : HasFDerivAt
        (fun p : RealEuclidean (a + k) × RealEuclidean a ↦ H i (P p.1))
        ((fderiv ℝ (H i) (lagrangePrimalProjection a k z)).comp
          (P.comp (ContinuousLinearMap.fst ℝ
            (RealEuclidean (a + k)) (RealEuclidean a)))) (z, center) := by
      exact (hH i).hasFDerivAt.comp (z, center)
        (P.comp (ContinuousLinearMap.fst ℝ
          (RealEuclidean (a + k)) (RealEuclidean a))).hasFDerivAt
    have hcomponent' :
        (ContinuousLinearMap.proj (Fin.natAdd a i)).comp L =
          (fderiv ℝ (H i) (lagrangePrimalProjection a k z)).comp
            (P.comp (ContinuousLinearMap.fst ℝ
              (RealEuclidean (a + k)) (RealEuclidean a))) := by
      rw [← hcomponent]
      have hfun :
          (fun p ↦ lagrangeSquaredDistanceCriticalFamily H p
            (Fin.natAdd a i)) =
            fun p ↦ H i (P p.1) := by
        funext p
        simp [P]
      rw [hfun]
      exact hHi.fderiv
    have happ := congrArg
      (fun T : (RealEuclidean (a + k) × RealEuclidean a) →L[ℝ] ℝ ↦
        T (dz, 0)) hcomponent'
    have hdxi := congrFun hdx i
    have happ' : w (Fin.natAdd a i) =
        fderiv ℝ (H i) (lagrangePrimalProjection a k z) dx := by
      simpa [w, L, P, dz] using happ
    have hdxi' :
        fderiv ℝ (H i) (lagrangePrimalProjection a k z) dx =
          y (Fin.natAdd a i) := by
      simpa [constraintFDeriv, yH] using hdxi
    exact happ'.trans hdxi'
  rw [show (dz, dc) = (dz, 0) + (0, dc) by ext <;> simp, map_add]
  change L (dz, 0) + L (0, dc) = y
  rw [hcenterApply]
  funext q
  refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) q
  · change w (Fin.castAdd k j) + C dc (Fin.castAdd k j) =
      y (Fin.castAdd k j)
    rw [lagrangeSquaredDistanceCriticalFamilyCenterDerivative_castAdd]
    dsimp [dc]
    ring
  · change w (Fin.natAdd a i) + C dc (Fin.natAdd a i) =
      y (Fin.natAdd a i)
    rw [lagrangeSquaredDistanceCriticalFamilyCenterDerivative_natAdd,
      add_zero]
    exact hconstraintCoord i

/-! ## Generic regular fixed center -/

/-- A globally `C²` regular constraint system admits a squared-distance
center for which every zero of its augmented Lagrange system is regular. -/
theorem exists_standardSquaredDistanceCenter_regular_lagrangeCriticalSystem
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (hH : ∀ i, ContDiff ℝ 2 (H i))
    (hconstraint : ∀ x : RealEuclidean a, (∀ i, H i x = 0) →
      (constraintFDeriv H x).range = ⊤) :
    ∃ center : RealEuclidean a, ∀ z : RealEuclidean (a + k),
      lagrangeCriticalSystemMap H (standardSquaredDistance center) z = 0 →
      (fderiv ℝ (lagrangeCriticalSystemMap H
        (standardSquaredDistance center)) z).range = ⊤ := by
  let Phi := lagrangeSquaredDistanceCriticalFamily H
  let S : Set (RealEuclidean (a + k) × RealEuclidean a) :=
    {p | Phi p = 0}
  have hPhiGlobal : ContDiff ℝ 1 Phi :=
    contDiff_lagrangeSquaredDistanceCriticalFamily H hH
  have hPhi : ∀ p ∈ S, ContDiffAt ℝ 1 Phi p := by
    intro p hp
    exact hPhiGlobal.contDiffAt
  have hSurj : ∀ p ∈ S, (fderiv ℝ Phi p).range = ⊤ := by
    intro p hp
    have hzero : ∀ i, H i (lagrangePrimalProjection a k p.1) = 0 := by
      intro i
      have hi := congrFun hp (Fin.natAdd a i)
      simpa [Phi] using hi
    apply lagrangeSquaredDistanceCriticalFamily_fderiv_range_eq_top
      H p.1 p.2
    · exact hPhiGlobal.differentiable (by norm_num) p
    · intro i
      exact ((hH i).differentiable (by norm_num)).differentiableAt
    · exact hconstraint (lagrangePrimalProjection a k p.1) hzero
  obtain ⟨center, hcenter⟩ := exists_parameter_with_regular_fixed_slice
    Phi S 0 hPhi rfl (fun p hp ↦ hp) hSurj
  refine ⟨center, ?_⟩
  intro z hz
  have hzS : (z, center) ∈ S := by
    change Phi (z, center) = 0
    change lagrangeCriticalSystemMap H
      (standardSquaredDistance center) z = 0
    exact hz
  have hfixed := hcenter (z, center) hzS rfl
  have hfamily : DifferentiableAt ℝ Phi (z, center) :=
    (hPhiGlobal.differentiable (by norm_num)).differentiableAt
  rw [fderiv_lagrangeSquaredDistanceCriticalFamily_fixed_center
    H z center hfamily]
  exact hfixed

/-- Family-valued specialization of the generic-center theorem. -/
theorem IsEverywhereSmoothFunctionFamily.exists_standardSquaredDistanceCenter_regular_lagrangeCriticalSystem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (hHmem : ∀ i, H i ∈ G a)
    (hconstraint : ∀ x : RealEuclidean a, (∀ i, H i x = 0) →
      (constraintFDeriv H x).range = ⊤) :
    ∃ center : RealEuclidean a, ∀ z : RealEuclidean (a + k),
      lagrangeCriticalSystemMap H (standardSquaredDistance center) z = 0 →
      (fderiv ℝ (lagrangeCriticalSystemMap H
        (standardSquaredDistance center)) z).range = ⊤ := by
  apply AbelFormalization.exists_standardSquaredDistanceCenter_regular_lagrangeCriticalSystem
    (H := H)
  · intro i
    exact (hsmooth a (H i) (hHmem i)).of_le (by norm_num)
  · exact hconstraint

end AbelFormalization
