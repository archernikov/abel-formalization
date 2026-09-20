import AbelFormalization.SquaredDistanceProper
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def basisCoordinateCLM {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) (i : Fin n) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (LinearEquiv.toContinuousLinearEquiv basis.equivFun).toContinuousLinearMap

@[simp]
theorem basisCoordinateCLM_apply {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) (i : Fin n) (x : E) :
    basisCoordinateCLM basis i x = basis.equivFun x i :=
  rfl

def algebraicSquaredDistanceDerivative {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) (center : Fin n → ℝ) (x : E) :
    E →L[ℝ] ℝ :=
  ∑ i, (2 * (basis.equivFun x i - center i)) •
    basisCoordinateCLM basis i

theorem hasStrictFDerivAt_algebraicSquaredDistance_basis {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) (center : Fin n → ℝ) (x : E) :
    HasStrictFDerivAt
      (algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) center)
      (algebraicSquaredDistanceDerivative basis center x) x := by
  rw [show algebraicSquaredDistance
      (fun i x ↦ basis.equivFun x i) center =
      fun x ↦ ∑ i, (basis.equivFun x i - center i) ^ 2 by
    funext y
    exact algebraicSquaredDistance_apply _ _ y]
  have hterm : ∀ i ∈ Finset.univ,
      HasStrictFDerivAt (fun y : E ↦ (basis.equivFun y i - center i) ^ 2)
        ((2 * (basis.equivFun x i - center i)) •
          basisCoordinateCLM basis i) x := by
    intro i hi
    have hcoord : HasStrictFDerivAt (fun y : E ↦ basis.equivFun y i)
        (basisCoordinateCLM basis i) x :=
      (basisCoordinateCLM basis i).hasStrictFDerivAt
    have hsub : HasStrictFDerivAt (fun y : E ↦ basis.equivFun y i - center i)
        (basisCoordinateCLM basis i) x := by
      simpa using hcoord.sub_const (center i)
    simpa only [Nat.reduceSubDiff, pow_one, nsmul_eq_mul, Nat.cast_ofNat,
      basisCoordinateCLM_apply] using hsub.pow 2
  simpa only [algebraicSquaredDistanceDerivative] using
    HasStrictFDerivAt.fun_sum hterm

theorem hasFDerivAt_algebraicSquaredDistance_basis {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) (center : Fin n → ℝ) (x : E) :
    HasFDerivAt
      (algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) center)
      (algebraicSquaredDistanceDerivative basis center x) x :=
  (hasStrictFDerivAt_algebraicSquaredDistance_basis basis center x).hasFDerivAt

@[simp]
theorem fderiv_algebraicSquaredDistance_basis_apply {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) (center : Fin n → ℝ)
    (x v : E) :
    fderiv ℝ
      (algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) center) x v =
      ∑ i, 2 * (basis.equivFun x i - center i) * basis.equivFun v i := by
  rw [(hasFDerivAt_algebraicSquaredDistance_basis basis center x).fderiv]
  simp [algebraicSquaredDistanceDerivative]

end AbelFormalization
