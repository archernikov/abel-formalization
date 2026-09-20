import AbelFormalization.RestrictedSourceCoordinates
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Properness of squared distance in basis coordinates

A finite-dimensional basis identifies the source with a Euclidean space.
The algebraic sum of squared coordinate differences is therefore ordinary
squared Euclidean distance, whose sublevel sets are compact.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite-dimensional basis followed by the canonical `L²` realization
of its coefficient vector. -/
def basisEuclideanContinuousLinearEquiv {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  basis.equivFun.toContinuousLinearEquiv.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm

@[simp]
theorem basisEuclideanContinuousLinearEquiv_apply {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) (x : E) (i : Fin n) :
    (basisEuclideanContinuousLinearEquiv basis x).ofLp i =
      basis.equivFun x i := by
  rfl

/-- A coordinate tuple regarded as a point of Euclidean space. -/
def euclideanCenter {n : ℕ} (center : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm center

@[simp]
theorem euclideanCenter_apply {n : ℕ} (center : Fin n → ℝ) (i : Fin n) :
    (euclideanCenter center).ofLp i = center i := by
  rfl

/-- Algebraic squared distance in basis coordinates is squared Euclidean
distance after the canonical continuous linear equivalence. -/
theorem algebraicSquaredDistance_basis_eq_dist_sq {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) (center : Fin n → ℝ) (x : E) :
    algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) center x =
      dist (basisEuclideanContinuousLinearEquiv basis x)
        (euclideanCenter center) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [algebraicSquaredDistance, Real.dist_eq, sq_abs]

/-- Every sublevel of algebraic squared distance in basis coordinates is
compact. -/
theorem isCompact_algebraicSquaredDistance_basis_sublevel {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) (center : Fin n → ℝ) (R : ℝ) :
    IsCompact {x : E |
      algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) center x ≤ R} := by
  by_cases hR : 0 ≤ R
  · have hset : {x : E |
        algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) center x ≤ R} =
        basisEuclideanContinuousLinearEquiv basis ⁻¹'
          Metric.closedBall (euclideanCenter center) (Real.sqrt R) := by
      ext x
      rw [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall,
        algebraicSquaredDistance_basis_eq_dist_sq]
      constructor
      · intro hx
        nlinarith [Real.sqrt_nonneg R, Real.sq_sqrt hR]
      · intro hx
        have hd : 0 ≤ dist (basisEuclideanContinuousLinearEquiv basis x)
            (euclideanCenter center) := dist_nonneg
        nlinarith [Real.sqrt_nonneg R, Real.sq_sqrt hR]
    rw [hset]
    exact (basisEuclideanContinuousLinearEquiv basis).toHomeomorph.isCompact_preimage.mpr
      (isCompact_closedBall _ _)
  · have hset : {x : E |
        algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) center x ≤ R} =
        ∅ := by
      ext x
      rw [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      apply iff_false_intro
      intro hx
      have hnonneg : 0 ≤ algebraicSquaredDistance
          (fun i x ↦ basis.equivFun x i) center x := by
        rw [algebraicSquaredDistance_apply]
        apply Finset.sum_nonneg
        intro i hi
        exact sq_nonneg _
      linarith
    rw [hset]
    exact isCompact_empty

/-- The manuscript's explicit `s,w,y` coordinate squared distance has
compact sublevels. -/
theorem isCompact_restrictedSourceSquaredDistance_sublevel
    (m p a : ℕ) (center : Fin ((m + p) + a) → ℝ) (R : ℝ) :
    IsCompact {x : RestrictedSource m p a |
      algebraicSquaredDistance (restrictedSourceCoordinates m p a)
        center x ≤ R} := by
  have hcoordinate :
      (fun i x ↦ (restrictedSourceBasis m p a).equivFun x i) =
        restrictedSourceCoordinates m p a := by
    funext i x
    exact restrictedSourceBasis_equivFun_apply m p a x i
  rw [← hcoordinate]
  exact isCompact_algebraicSquaredDistance_basis_sublevel
    (restrictedSourceBasis m p a) center R

end AbelFormalization
