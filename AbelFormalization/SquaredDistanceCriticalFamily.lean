import AbelFormalization.SquaredDistanceCenterVariation
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The parameterized squared-distance critical system

This file treats the center of squared distance as a parameter.  It computes
the derivative in the center direction and proves that the joint system in
the ambient point and center is a submersion wherever the original
codimension-one constraint system is regular.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def squaredDistanceCriticalFamily {r : ℕ}
    (H : Fin r → E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) :
    E × (Fin (r + 1) → ℝ) → Fin (r + 1) → ℝ :=
  fun p ↦ criticalSystemMap H
    (fun x ↦ criticalDeterminant H
      (algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) p.2)
      basis x) p.1

@[simp]
theorem squaredDistanceCriticalFamily_castSucc {r : ℕ}
    (H : Fin r → E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (p : E × (Fin (r + 1) → ℝ)) (i : Fin r) :
    squaredDistanceCriticalFamily H basis p i.castSucc = H i p.1 := by
  simp [squaredDistanceCriticalFamily, criticalSystemMap_apply_castSucc]

@[simp]
theorem squaredDistanceCriticalFamily_last {r : ℕ}
    (H : Fin r → E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (p : E × (Fin (r + 1) → ℝ)) :
    squaredDistanceCriticalFamily H basis p (Fin.last r) =
      criticalDeterminant H
        (algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) p.2)
        basis p.1 := by
  simp [squaredDistanceCriticalFamily, criticalSystemMap_apply_last]

def squaredDistanceCriticalFamilyCenterDerivative {r : ℕ}
    (H : Fin r → E → ℝ) (rho : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : E) :
    (Fin (r + 1) → ℝ) →L[ℝ] (Fin (r + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun i ↦
    Fin.lastCases
      (squaredDistanceCenterDerivative basis
        (criticalCofactorTangent H rho basis x))
      (fun _ ↦ 0) i)

@[simp]
theorem squaredDistanceCriticalFamilyCenterDerivative_castSucc {r : ℕ}
    (H : Fin r → E → ℝ) (rho : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : E)
    (c : Fin (r + 1) → ℝ) (i : Fin r) :
    squaredDistanceCriticalFamilyCenterDerivative H rho basis x c i.castSucc = 0 := by
  simp [squaredDistanceCriticalFamilyCenterDerivative]

@[simp]
theorem squaredDistanceCriticalFamilyCenterDerivative_last {r : ℕ}
    (H : Fin r → E → ℝ) (rho : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : E)
    (c : Fin (r + 1) → ℝ) :
    squaredDistanceCriticalFamilyCenterDerivative H rho basis x c (Fin.last r) =
      squaredDistanceCenterDerivative basis
        (criticalCofactorTangent H rho basis x) c := by
  simp [squaredDistanceCriticalFamilyCenterDerivative]

variable [FiniteDimensional ℝ E]

theorem hasStrictFDerivAt_squaredDistanceCriticalFamily_center {r : ℕ}
    (H : Fin r → E → ℝ) (rho : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (x : E) (center : Fin (r + 1) → ℝ) :
    HasStrictFDerivAt
      (fun c ↦ squaredDistanceCriticalFamily H basis (x, c))
      (squaredDistanceCriticalFamilyCenterDerivative H rho basis x) center := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa using hasStrictFDerivAt_criticalDeterminant_center
      H rho basis x center
  · simpa using (hasStrictFDerivAt_const (H j x) center)

theorem exists_centerDirection_criticalFamily_eq_single_last {r : ℕ}
    (H : Fin r → E → ℝ) (rho : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : E)
    (hsurj : (constraintFDeriv H x).range = ⊤) (a : ℝ) :
    ∃ dc : Fin (r + 1) → ℝ,
      squaredDistanceCriticalFamilyCenterDerivative H rho basis x dc =
        Pi.single (Fin.last r) a := by
  obtain ⟨dc, hdc⟩ := LinearMap.range_eq_top.mp
    (criticalDeterminant_centerDerivative_range_eq_top_of_surjective
      H rho basis x hsurj) a
  refine ⟨dc, ?_⟩
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa using hdc
  · simp

theorem squaredDistanceCriticalFamily_fderiv_range_eq_top {r : ℕ}
    (H : Fin r → E → ℝ) (rho : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (x : E) (center : Fin (r + 1) → ℝ)
    (hfamily : DifferentiableAt ℝ
      (squaredDistanceCriticalFamily H basis) (x, center))
    (hH : ∀ i, DifferentiableAt ℝ (H i) x)
    (hsurj : (constraintFDeriv H x).range = ⊤) :
    (fderiv ℝ (squaredDistanceCriticalFamily H basis) (x, center)).range = ⊤ := by
  let L := fderiv ℝ (squaredDistanceCriticalFamily H basis) (x, center)
  let C := squaredDistanceCriticalFamilyCenterDerivative H rho basis x
  let I : (Fin (r + 1) → ℝ) →L[ℝ]
      E × (Fin (r + 1) → ℝ) :=
    (0 : (Fin (r + 1) → ℝ) →L[ℝ] E).prod
      (ContinuousLinearMap.id ℝ (Fin (r + 1) → ℝ))
  have hins : HasFDerivAt (fun c : Fin (r + 1) → ℝ ↦ (x, c))
      I center := by
    simpa [I] using (hasFDerivAt_const (𝕜 := ℝ) x center).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) center)
  have hsliceFull : HasFDerivAt
      (fun c ↦ squaredDistanceCriticalFamily H basis (x, c))
      (L.comp I) center := by
    simpa [L, Function.comp_def] using hfamily.hasFDerivAt.comp center hins
  have hsliceExplicit : HasFDerivAt
      (fun c ↦ squaredDistanceCriticalFamily H basis (x, c)) C center :=
    (hasStrictFDerivAt_squaredDistanceCriticalFamily_center
      H rho basis x center).hasFDerivAt
  have hcenterDerivative :
      L.comp I = C :=
    hsliceFull.unique hsliceExplicit
  rw [LinearMap.range_eq_top]
  intro y
  let yH : Fin r → ℝ := fun i ↦ y i.castSucc
  obtain ⟨dx, hdx⟩ := LinearMap.range_eq_top.mp hsurj yH
  let w : Fin (r + 1) → ℝ := L (dx, 0)
  obtain ⟨dc, hdc⟩ :=
    exists_centerDirection_criticalFamily_eq_single_last
      H rho basis x hsurj (y (Fin.last r) - w (Fin.last r))
  refine ⟨(dx, dc), ?_⟩
  have hcenterApply : L (0, dc) = C dc := by
    have := congrArg
      (fun T : (Fin (r + 1) → ℝ) →L[ℝ] (Fin (r + 1) → ℝ) ↦ T dc)
      hcenterDerivative
    simpa [I] using this
  have hxcoord : ∀ i : Fin r, w i.castSucc = y i.castSucc := by
    intro i
    have hcomponent := fderiv_apply hfamily i.castSucc
    have hHi : HasFDerivAt (fun p : E × (Fin (r + 1) → ℝ) ↦ H i p.1)
        ((fderiv ℝ (H i) x).comp
          (ContinuousLinearMap.fst ℝ E (Fin (r + 1) → ℝ))) (x, center) :=
      (hH i).hasFDerivAt.comp (x, center) hasFDerivAt_fst
    have hcomponent' :
        (ContinuousLinearMap.proj i.castSucc).comp L =
          (fderiv ℝ (H i) x).comp
            (ContinuousLinearMap.fst ℝ E (Fin (r + 1) → ℝ)) := by
      rw [← hcomponent]
      have hfun :
          (fun p ↦ squaredDistanceCriticalFamily H basis p i.castSucc) =
            fun p ↦ H i p.1 := by
        funext p
        exact squaredDistanceCriticalFamily_castSucc H basis p i
      rw [hfun]
      exact hHi.fderiv
    have happ := congrArg
      (fun T : (E × (Fin (r + 1) → ℝ)) →L[ℝ] ℝ ↦ T (dx, 0))
      hcomponent'
    have hdxi := congrFun hdx i
    simpa [w, L, C, constraintFDeriv, yH] using happ.trans hdxi
  rw [show (dx, dc) = (dx, 0) + (0, dc) by ext <;> simp, map_add]
  change L (dx, 0) + L (0, dc) = y
  rw [hcenterApply, hdc]
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [w]
  · simpa [w] using hxcoord j

end AbelFormalization
