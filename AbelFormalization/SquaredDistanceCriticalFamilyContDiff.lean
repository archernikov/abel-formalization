import AbelFormalization.CountableParametricChartCover
import AbelFormalization.SquaredDistanceCriticalDeterminant
import AbelFormalization.SquaredDistanceCriticalFamily
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem contDiffAt_matrix_det {n : ℕ∞ω}
    (M : E → Matrix κ κ ℝ) (x : E)
    (hM : ∀ i j, ContDiffAt ℝ n (fun y => M y i j) x) :
    ContDiffAt ℝ n (fun y => Matrix.det (M y)) x := by
  simp_rw [Matrix.det_apply']
  apply ContDiffAt.sum
  intro sigma hsigma
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i hi
  exact hM (sigma i) i

theorem contDiffAt_lastRowCofactor {r : ℕ} {n : ℕ∞ω}
    (M : E → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) (x : E)
    (hM : ∀ i j, ContDiffAt ℝ n (fun y => M y i j) x)
    (j : Fin (r + 1)) :
    ContDiffAt ℝ n (fun y => lastRowCofactor (M y) j) x := by
  unfold lastRowCofactor
  rw [show (fun y => (zeroLastRow (M y)).adjugate j (Fin.last r)) =
      fun y => (-1 : ℝ) ^ ((Fin.last r : ℕ) + (j : ℕ)) *
        ((zeroLastRow (M y)).submatrix
          (Fin.succAbove (Fin.last r)) (Fin.succAbove j)).det by
    funext y
    exact Matrix.adjugate_fin_succ_eq_det_submatrix
      (zeroLastRow (M y)) j (Fin.last r)]
  apply contDiffAt_const.mul
  apply contDiffAt_matrix_det
  intro i k
  simp only [Matrix.submatrix_apply, zeroLastRow, Matrix.updateRow_apply]
  split
  · fun_prop
  · exact hM _ _

theorem contDiffAt_criticalCofactorTangent {r : ℕ} {n : ℕ∞ω}
    (H : Fin r → E → ℝ) (rho : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : E)
    (hH : ∀ i, ContDiffAt ℝ (n + 1) (H i) x)
    (hrho : ContDiffAt ℝ (n + 1) rho x) :
    ContDiffAt ℝ n (fun y => criticalCofactorTangent H rho basis y) x := by
  unfold criticalCofactorTangent
  apply ContDiffAt.sum
  intro j hj
  apply (contDiffAt_lastRowCofactor
    (fun y => criticalJacobianMatrix H rho basis y) x ?_ j).smul contDiffAt_const
  intro i k
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp only [criticalJacobianMatrix, functionTupleSnoc_last]
    exact (hrho.fderiv_right (le_refl (n + 1))).clm_apply contDiffAt_const
  · simp only [criticalJacobianMatrix, functionTupleSnoc_castSucc]
    exact ((hH a).fderiv_right (le_refl (n + 1))).clm_apply contDiffAt_const

variable [FiniteDimensional ℝ E]

theorem contDiffAt_squaredDistanceCriticalFamily {r : ℕ}
    (H : Fin r → E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (x : E) (center : Fin (r + 1) → ℝ)
    (hH : ∀ i, ContDiffAt ℝ 2 (H i) x) :
    ContDiffAt ℝ 1 (squaredDistanceCriticalFamily H basis) (x, center) := by
  apply contDiffAt_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [squaredDistanceCriticalFamily_last]
    rw [show (fun p : E × (Fin (r + 1) → ℝ) =>
        criticalDeterminant H
          (algebraicSquaredDistance (fun i x ↦ basis.equivFun x i) p.2)
          basis p.1) =
        fun p => ∑ i, 2 * (basis.equivFun p.1 i - p.2 i) *
          basis.equivFun
            (criticalCofactorTangent H (fun _ => 0) basis p.1) i by
      funext p
      exact criticalDeterminant_algebraicSquaredDistance_basis
        H (fun _ => 0) basis p.2 p.1]
    have hcof : ContDiffAt ℝ 1
        (fun y => criticalCofactorTangent H (fun _ => 0) basis y) x := by
      apply contDiffAt_criticalCofactorTangent
      · intro k
        exact (hH k).of_le (by norm_num)
      · fun_prop
    apply ContDiffAt.sum
    intro k hk
    have hcofFst : ContDiffAt ℝ 1
        (fun p : E × (Fin (r + 1) → ℝ) =>
          criticalCofactorTangent H (fun _ => 0) basis p.1) (x, center) := by
      exact hcof.fst'
    have hcofLift : ContDiffAt ℝ 1
        (fun p : E × (Fin (r + 1) → ℝ) =>
          basis.equivFun
            (criticalCofactorTangent H (fun _ => 0) basis p.1) k)
        (x, center) := by
      change ContDiffAt ℝ 1
        (fun p : E × (Fin (r + 1) → ℝ) =>
          LinearMap.toContinuousLinearMap (basis.coord k)
            (criticalCofactorTangent H (fun _ => 0) basis p.1)) (x, center)
      exact contDiffAt_const.clm_apply
        hcofFst
    have hxcoord : ContDiffAt ℝ 1
        (fun p : E × (Fin (r + 1) → ℝ) => basis.equivFun p.1 k)
        (x, center) := by
      change ContDiffAt ℝ 1
        (fun p : E × (Fin (r + 1) → ℝ) =>
          LinearMap.toContinuousLinearMap (basis.coord k) p.1) (x, center)
      exact contDiffAt_const.clm_apply contDiffAt_fst
    have hcentercoord : ContDiffAt ℝ 1
        (fun p : E × (Fin (r + 1) → ℝ) => p.2 k) (x, center) := by
      let ev : (Fin (r + 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj k
      change ContDiffAt ℝ 1 (fun p : E × (Fin (r + 1) → ℝ) => ev p.2) (x, center)
      exact ev.contDiff.contDiffAt.snd'
    apply (contDiffAt_const.mul (hxcoord.sub hcentercoord)).mul
    exact hcofLift
  · simp only [squaredDistanceCriticalFamily_castSucc]
    exact ((hH j).of_le (by norm_num)).comp (x, center) contDiffAt_fst

end AbelFormalization
