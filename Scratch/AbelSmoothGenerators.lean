import AbelFormalization.Stirling
import AbelFormalization.SmoothGeometricFamily
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth Abel generators

The functions `Cr A r` are the manuscript's globally
analytic generators

`C_r(x) = A^(r)(1 + x^2)`.

This file also records their derivative formula and its pullback along an
affine real-valued map on a finite-dimensional real coordinate space.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The manuscript's globally defined generator `C_r(x) = A^(r)(1+x^2)`. -/
def Cr (A : ℝ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv r A (1 + x ^ 2)

@[simp]
theorem Cr_zero (A : ℝ → ℝ) :
    Cr A 0 = C0 A := by
  funext x
  simp [Cr, C0]

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- Every manuscript generator `C_r` is analytic at every real point. -/
theorem analyticAt_Cr (r : ℕ) (x : ℝ) :
    AnalyticAt ℝ (Cr A r) x := by
  have hp : 0 < 1 + x ^ 2 := by positivity
  have hg : AnalyticAt ℝ (fun y : ℝ ↦ 1 + y ^ 2) x := by fun_prop
  change AnalyticAt ℝ
    ((iteratedDeriv r A) ∘ (fun y : ℝ ↦ 1 + y ^ 2)) x
  rw [iteratedDeriv_eq_iterate]
  exact ((hA.analytic.iterated_deriv r) (1 + x ^ 2) hp).comp
    (f := fun y : ℝ ↦ 1 + y ^ 2) hg

/-- Every manuscript generator `C_r` is analytic on the whole real line. -/
theorem analyticOnNhd_Cr (r : ℕ) :
    AnalyticOnNhd ℝ (Cr A r) Set.univ := by
  intro x _
  exact hA.analyticAt_Cr r x

/-- Every manuscript generator `C_r` is globally smooth. -/
theorem contDiff_Cr (r : ℕ) :
    ContDiff ℝ ∞ (Cr A r) :=
  (hA.analyticOnNhd_Cr r).contDiff

/-- The exact one-variable derivative formula `C_r' = 2 x C_(r+1)`. -/
theorem hasDerivAt_Cr (r : ℕ) (x : ℝ) :
    HasDerivAt (Cr A r)
      (2 * x * Cr A (r + 1) x) x := by
  have hp : 0 < 1 + x ^ 2 := by positivity
  have hinner : HasDerivAt (fun y : ℝ ↦ 1 + y ^ 2) (2 * x) x := by
    simpa only [Nat.cast_ofNat, Nat.reduceSubDiff, pow_one] using
      (hasDerivAt_pow 2 x).const_add 1
  change HasDerivAt
    ((iteratedDeriv r A) ∘ (fun y : ℝ ↦ 1 + y ^ 2))
      (2 * x * iteratedDeriv (r + 1) A (1 + x ^ 2)) x
  simpa only [mul_comm] using
    (hA.hasDerivAt_iteratedDeriv r hp).comp x hinner

/-- Pointwise derivative form of `C_r' = 2 x C_(r+1)`. -/
theorem deriv_Cr (r : ℕ) (x : ℝ) :
    deriv (Cr A r) x = 2 * x * Cr A (r + 1) x :=
  (hA.hasDerivAt_Cr r x).deriv

end IsAbel

/-! ## Affine pullbacks -/

/-- An affine map from one of the project's finite real coordinate spaces,
equipped with its automatic continuity. -/
def continuousAffineMapOfRealEuclidean {m : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ℓ : RealEuclidean m →ᵃ[ℝ] F) :
    RealEuclidean m →ᴬ[ℝ] F :=
  ⟨ℓ, ℓ.continuous_of_finiteDimensional⟩

@[simp]
theorem continuousAffineMapOfRealEuclidean_apply {m : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ℓ : RealEuclidean m →ᵃ[ℝ] F)
    (x : RealEuclidean m) :
    continuousAffineMapOfRealEuclidean ℓ x = ℓ x :=
  rfl

@[simp]
theorem continuousAffineMapOfRealEuclidean_contLinear_apply
    {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ℓ : RealEuclidean m →ᵃ[ℝ] F)
    (v : RealEuclidean m) :
    (continuousAffineMapOfRealEuclidean ℓ).contLinear v = ℓ.linear v :=
  rfl

/-- Affine maps from finite real coordinate spaces to complete real normed
spaces are analytic everywhere. -/
theorem analyticAt_realEuclideanAffineMap
    {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (ℓ : RealEuclidean m →ᵃ[ℝ] F)
    (x : RealEuclidean m) : AnalyticAt ℝ ℓ x := by
  rw [ℓ.decomp]
  simpa only [LinearMap.coe_toContinuousLinearMap'] using
    (ℓ.linear.toContinuousLinearMap.analyticAt x).add analyticAt_const

/-- The Fréchet derivative of an affine map is its linear part. -/
theorem fderiv_realEuclideanAffineMap_apply
    {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ℓ : RealEuclidean m →ᵃ[ℝ] F)
    (x v : RealEuclidean m) :
    fderiv ℝ ℓ x v = ℓ.linear v := by
  let ℓc := continuousAffineMapOfRealEuclidean ℓ
  have h : HasFDerivAt ℓc ℓc.contLinear x := ℓc.hasFDerivAt
  change fderiv ℝ (ℓc : RealEuclidean m → F) x v = ℓc.contLinear v
  rw [h.fderiv]

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- An affine pullback of any `C_r` is analytic on all of coordinate space. -/
theorem analyticOnNhd_Cr_comp_affine {n : ℕ}
    (r : ℕ) (ℓ : RealEuclidean n →ᵃ[ℝ] ℝ) :
    AnalyticOnNhd ℝ (Cr A r ∘ ℓ) Set.univ := by
  intro x _
  exact (hA.analyticAt_Cr r (ℓ x)).comp
    (f := ℓ) (analyticAt_realEuclideanAffineMap ℓ x)

/-- An affine pullback of any `C_r` is globally smooth. -/
theorem contDiff_Cr_comp_affine {n : ℕ}
    (r : ℕ) (ℓ : RealEuclidean n →ᵃ[ℝ] ℝ) :
    ContDiff ℝ ∞ (Cr A r ∘ ℓ) :=
  (hA.analyticOnNhd_Cr_comp_affine r ℓ).contDiff

/-- Full Fréchet derivative formula for an affine pullback of `C_r`. -/
theorem hasFDerivAt_Cr_comp_affine {n : ℕ}
    (r : ℕ) (ℓ : RealEuclidean n →ᵃ[ℝ] ℝ)
    (x : RealEuclidean n) :
    HasFDerivAt (Cr A r ∘ ℓ)
      ((2 * ℓ x * Cr A (r + 1) (ℓ x)) •
        ℓ.linear.toContinuousLinearMap) x := by
  let ℓc := continuousAffineMapOfRealEuclidean ℓ
  change HasFDerivAt
    (Cr A r ∘ (ℓc : RealEuclidean n → ℝ))
      ((2 * ℓc x * Cr A (r + 1) (ℓc x)) •
        ℓc.contLinear) x
  exact (hA.hasDerivAt_Cr r (ℓc x)).comp_hasFDerivAt
    x (ℓc.hasFDerivAt (x := x))

/-- The affine-pullback derivative evaluated in an arbitrary direction. -/
theorem fderiv_Cr_comp_affine_apply {n : ℕ}
    (r : ℕ) (ℓ : RealEuclidean n →ᵃ[ℝ] ℝ)
    (x v : RealEuclidean n) :
    fderiv ℝ (Cr A r ∘ ℓ) x v =
      2 * ℓ x * Cr A (r + 1) (ℓ x) * ℓ.linear v := by
  rw [(hA.hasFDerivAt_Cr_comp_affine r ℓ x).fderiv]
  rfl

/-- Coordinate form of the manuscript identity
`∂_j(C_r ∘ ℓ) = 2 ℓ (∂_j ℓ) (C_(r+1) ∘ ℓ)`. -/
theorem fderiv_Cr_comp_affine_single {n : ℕ}
    (r : ℕ) (ℓ : RealEuclidean n →ᵃ[ℝ] ℝ)
    (j : Fin n) (x : RealEuclidean n) :
    fderiv ℝ (Cr A r ∘ ℓ) x (Pi.single j 1) =
      2 * ℓ x * fderiv ℝ ℓ x (Pi.single j 1) *
        Cr A (r + 1) (ℓ x) := by
  rw [hA.fderiv_Cr_comp_affine_apply,
    fderiv_realEuclideanAffineMap_apply]
  ring

end IsAbel

end AbelFormalization
