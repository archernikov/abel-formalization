import AbelFormalization.ExponentialAdjunctionGeometry
import Mathlib.LinearAlgebra.Matrix.Adjugate

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Replace the last row of a square successor matrix by zero. -/
def zeroLastRow {R : Type*} [Zero R] {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  M.updateRow (Fin.last r) 0

/-- Cofactor vector dual to the final row. -/
def lastRowCofactor {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R) : Fin (r + 1) → R :=
  fun j ↦ (zeroLastRow M).adjugate j (Fin.last r)

theorem lastRowCofactor_annihilates_castSucc_row
    {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (i : Fin r) :
    ∑ j, M i.castSucc j * lastRowCofactor M j = 0 := by
  have h := congrArg (fun N : Matrix (Fin (r + 1)) (Fin (r + 1)) R ↦
      N i.castSucc (Fin.last r)) (Matrix.mul_adjugate (zeroLastRow M))
  simpa [Matrix.mul_apply, lastRowCofactor, zeroLastRow,
    Matrix.one_apply, Fin.castSucc_ne_last] using h

theorem det_eq_lastRow_mul_lastRowCofactor
    {R : Type*} [CommRing R] {r : ℕ}
    (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    M.det = ∑ j, M (Fin.last r) j * lastRowCofactor M j := by
  rw [Matrix.det_succ_row M (Fin.last r)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [lastRowCofactor, Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [zeroLastRow, Matrix.submatrix_updateRow_succAbove]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The square directional Jacobian with the constraint rows followed by the
objective row. -/
def criticalJacobianMatrix {r : ℕ} (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
  fun i j ↦ fderiv ℝ (functionTupleSnoc H ρ i) x (basis j)

/-- The cofactor tangent obtained from the constraint rows of the critical
Jacobian.  Zeroing the last row before taking cofactors makes this independent
of the objective row. -/
def criticalCofactorTangent {r : ℕ} (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E) : E :=
  ∑ j, lastRowCofactor (criticalJacobianMatrix H ρ basis x) j • basis j

theorem zeroLastRow_criticalJacobianMatrix_eq
    {r : ℕ} (H : Fin r → E → ℝ) (ρ σ : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E) :
    zeroLastRow (criticalJacobianMatrix H ρ basis x) =
      zeroLastRow (criticalJacobianMatrix H σ basis x) := by
  ext i j
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · simp [zeroLastRow]
  · simp [zeroLastRow, criticalJacobianMatrix]

theorem criticalCofactorTangent_independent_objective
    {r : ℕ} (H : Fin r → E → ℝ) (ρ σ : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E) :
    criticalCofactorTangent H ρ basis x =
      criticalCofactorTangent H σ basis x := by
  unfold criticalCofactorTangent lastRowCofactor
  rw [zeroLastRow_criticalJacobianMatrix_eq H ρ σ basis x]

theorem fderiv_constraint_criticalCofactorTangent_eq_zero
    {r : ℕ} (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E) (i : Fin r) :
    fderiv ℝ (H i) x (criticalCofactorTangent H ρ basis x) = 0 := by
  rw [criticalCofactorTangent, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  simpa only [criticalJacobianMatrix, functionTupleSnoc_castSucc,
    mul_comm] using
      lastRowCofactor_annihilates_castSucc_row
        (criticalJacobianMatrix H ρ basis x) i

theorem criticalDeterminant_eq_fderiv_criticalCofactorTangent
    {r : ℕ} (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E) :
    criticalDeterminant H ρ basis x =
      fderiv ℝ ρ x (criticalCofactorTangent H ρ basis x) := by
  rw [criticalCofactorTangent, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  rw [criticalDeterminant]
  change (criticalJacobianMatrix H ρ basis x).det = _
  simpa only [criticalJacobianMatrix, functionTupleSnoc_last, mul_comm] using
    det_eq_lastRow_mul_lastRowCofactor (criticalJacobianMatrix H ρ basis x)

theorem criticalDeterminant_eq_fderiv_criticalCofactorTangent_of_aux
    {r : ℕ} (H : Fin r → E → ℝ) (ρ f : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E) :
    criticalDeterminant H f basis x =
      fderiv ℝ f x (criticalCofactorTangent H ρ basis x) := by
  rw [criticalCofactorTangent_independent_objective H ρ f basis x]
  exact criticalDeterminant_eq_fderiv_criticalCofactorTangent H f basis x

theorem criticalCofactorTangent_ne_zero_of_criticalDeterminant_ne_zero
    {r : ℕ} (H : Fin r → E → ℝ) (ρ f : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E)
    (hdet : criticalDeterminant H f basis x ≠ 0) :
    criticalCofactorTangent H ρ basis x ≠ 0 := by
  intro hzero
  apply hdet
  rw [criticalDeterminant_eq_fderiv_criticalCofactorTangent_of_aux
    H ρ f basis x, hzero, map_zero]

theorem criticalCofactorTangent_mem_constraintFDeriv_ker
    {r : ℕ} (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E) :
    criticalCofactorTangent H ρ basis x ∈ (constraintFDeriv H x).ker := by
  rw [LinearMap.mem_ker]
  ext i
  exact fderiv_constraint_criticalCofactorTangent_eq_zero H ρ basis x i

theorem constraintFDeriv_ker_eq_span_criticalCofactorTangent
    {r : ℕ} [FiniteDimensional ℝ E]
    (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E)
    (hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ))
    (hsurj : (constraintFDeriv H x).range = ⊤)
    (hτ : criticalCofactorTangent H ρ basis x ≠ 0) :
    (constraintFDeriv H x).ker =
      ℝ ∙ criticalCofactorTangent H ρ basis x := by
  apply eq_span_singleton_of_mem_of_finrank_eq_one
  · have hrank := (constraintFDeriv H x).finrank_range_add_finrank_ker
    have hsource : Module.finrank ℝ E = r + 1 := by
      simpa using hdim
    rw [hsurj, finrank_top, hsource] at hrank
    simpa using hrank
  · exact criticalCofactorTangent_mem_constraintFDeriv_ker H ρ basis x
  · exact hτ

theorem constraintFDeriv_ker_eq_span_criticalCofactorTangent_of_det_ne_zero
    {r : ℕ} [FiniteDimensional ℝ E]
    (H : Fin r → E → ℝ) (ρ f : E → ℝ)
    (basis : Fin (r + 1) → E) (x : E)
    (hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ))
    (hsurj : (constraintFDeriv H x).range = ⊤)
    (hdet : criticalDeterminant H f basis x ≠ 0) :
    (constraintFDeriv H x).ker =
      ℝ ∙ criticalCofactorTangent H ρ basis x :=
  constraintFDeriv_ker_eq_span_criticalCofactorTangent
    H ρ basis x hdim hsurj
      (criticalCofactorTangent_ne_zero_of_criticalDeterminant_ne_zero
        H ρ f basis x hdet)

end AbelFormalization
