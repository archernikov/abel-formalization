import AbelFormalization.CofactorTangentNonzero
import AbelFormalization.SquaredDistanceCriticalDeterminant
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Variation of the critical determinant with the squared-distance center

At a fixed ambient point, the critical determinant for squared distance is
affine in its center.  Its center derivative is the nonzero functional dual
to the cofactor tangent whenever the constraints are regular.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def squaredDistanceCenterDerivative {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) (v : E) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, (2 * basis.equivFun v i) • -(ContinuousLinearMap.proj i)

@[simp]
theorem squaredDistanceCenterDerivative_apply {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) (v : E) (c : Fin n → ℝ) :
    squaredDistanceCenterDerivative basis v c =
      ∑ i, -(2 * basis.equivFun v i * c i) := by
  simp [squaredDistanceCenterDerivative]

variable [FiniteDimensional ℝ E]

theorem hasStrictFDerivAt_criticalDeterminant_center {r : ℕ}
    (H : Fin r → E → ℝ) (rho : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (x : E) (center : Fin (r + 1) → ℝ) :
    HasStrictFDerivAt
      (fun c ↦ criticalDeterminant H
        (algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) c)
        basis x)
      (squaredDistanceCenterDerivative basis
        (criticalCofactorTangent H rho basis x)) center := by
  rw [show (fun c ↦ criticalDeterminant H
      (algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) c)
      basis x) =
      fun c ↦ ∑ i, 2 * (basis.equivFun x i - c i) *
        basis.equivFun (criticalCofactorTangent H rho basis x) i by
    funext c
    exact criticalDeterminant_algebraicSquaredDistance_basis
      H rho basis c x]
  have hterm : ∀ i ∈ Finset.univ,
      HasStrictFDerivAt
        (fun c : Fin (r + 1) → ℝ ↦
          2 * (basis.equivFun x i - c i) *
            basis.equivFun (criticalCofactorTangent H rho basis x) i)
        ((2 * basis.equivFun
          (criticalCofactorTangent H rho basis x) i) • -(
            (ContinuousLinearMap.proj i :
              (Fin (r + 1) → ℝ) →L[ℝ] ℝ))) center := by
    intro i hi
    have hcoord : HasStrictFDerivAt (fun c : Fin (r + 1) → ℝ ↦ c i)
        (ContinuousLinearMap.proj i :
          (Fin (r + 1) → ℝ) →L[ℝ] ℝ) center :=
      (ContinuousLinearMap.proj i :
        (Fin (r + 1) → ℝ) →L[ℝ] ℝ).hasStrictFDerivAt
    have h := ((hcoord.const_sub (basis.equivFun x i)).const_mul 2).mul_const
      (basis.equivFun (criticalCofactorTangent H rho basis x) i)
    simpa only [smul_smul, mul_comm] using h
  simpa only [squaredDistanceCenterDerivative] using
    HasStrictFDerivAt.fun_sum hterm

theorem squaredDistanceCenterDerivative_range_eq_top {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) {v : E} (hv : v ≠ 0) :
    (squaredDistanceCenterDerivative basis v).range = ⊤ := by
  classical
  apply Module.Dual.range_eq_top_of_ne_zero
  have hrepr : basis.equivFun v ≠ 0 := by
    simpa using (basis.equivFun.injective.ne_iff).mpr hv
  obtain ⟨i, hi⟩ : ∃ i, basis.equivFun v i ≠ 0 := by
    by_contra h
    apply hrepr
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  intro hzero
  have happ := congrArg
    (fun L : (Fin n → ℝ) →ₗ[ℝ] ℝ ↦ L (Pi.single i 1)) hzero
  have heval : squaredDistanceCenterDerivative basis v (Pi.single i 1) =
      -(2 * basis.equivFun v i) := by
    rw [squaredDistanceCenterDerivative_apply]
    rw [Fintype.sum_eq_single i]
    · simp
    · intro j hji
      simp [hji]
  have happ' : -(2 * basis.equivFun v i) = 0 := by
    rw [← heval]
    exact happ
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  apply hi
  exact (mul_eq_zero.mp (neg_eq_zero.mp happ')).resolve_left htwo

theorem criticalDeterminant_centerDerivative_range_eq_top_of_surjective
    {r : ℕ} (H : Fin r → E → ℝ) (rho : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : E)
    (hsurj : (constraintFDeriv H x).range = ⊤) :
    (squaredDistanceCenterDerivative basis
      (criticalCofactorTangent H rho basis x)).range = ⊤ :=
  squaredDistanceCenterDerivative_range_eq_top basis
    (criticalCofactorTangent_ne_zero_of_surjective H rho x basis hsurj)

end AbelFormalization
