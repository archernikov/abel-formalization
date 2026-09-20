import AbelFormalization.ExponentialAdjunctionJacobian
import AbelFormalization.DirectionalJacobian

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Directional closure constructs a lower-level expression agreeing with the
manuscript's global determinant `J(x,Y)` on the working domain. -/
theorem exists_exponentialAdjunctionJacobianExpression {n : ℕ}
    (B : Subalgebra ℝ ((E × ℝ) → ℝ)) (Omega : Set (E × ℝ))
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E)
    (hF : ∀ i, (fun p ↦ Ftilde p i) ∈ B)
    (hg : (fun p : E × ℝ ↦ g p.1) ∈ B)
    (hY : (fun p : E × ℝ ↦ p.2) ∈ B)
    (hclosed : ∀ j, DirectionallyClosedOn B Omega (graphProductBasis basis j))
    (hgdiff : ∀ p ∈ Omega, DifferentiableAt ℝ g p.1) :
    ∃ J : E × ℝ → ℝ, J ∈ B ∧
      ∀ p ∈ Omega, J p = exponentialAdjunctionJacobian Ftilde g basis p := by
  let G : Fin (n + 1) → E × ℝ → ℝ :=
    functionTupleSnoc (fun i p ↦ Ftilde p i) (fun p ↦ g p.1)
  have hG : ∀ i, G i ∈ B := by
    apply functionTupleSnoc_mem_subalgebra
    · exact hF
    · exact hg
  obtain ⟨D, hDmem, hD⟩ :=
    exists_directionalDerivativeMatrix B Omega (graphProductBasis basis) G
      hG hclosed
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ((E × ℝ) → ℝ) :=
    fun i j ↦ Fin.lastCases
      (Fin.lastCases (fun _ ↦ 1)
        (fun k ↦ -(fun p : E × ℝ ↦ p.2) * D (Fin.last n) k.castSucc) j)
      (fun h ↦ D h.castSucc j) i
  have hM : ∀ i j, M i j ∈ B := by
    intro i j
    refine Fin.lastCases ?_ (fun h ↦ ?_) i
    · refine Fin.lastCases ?_ (fun k ↦ ?_) j
      · simp only [M, Fin.lastCases_last]
        change (1 : (E × ℝ) → ℝ) ∈ B
        exact B.one_mem
      · simpa [M] using
          B.mul_mem (B.neg_mem hY) (hDmem (Fin.last n) k.castSucc)
    · simpa [M] using hDmem h.castSucc j
  refine ⟨M.det, matrix_det_mem_subalgebra B M hM, ?_⟩
  intro p hp
  rw [matrix_det_apply_function]
  unfold exponentialAdjunctionJacobian
  congr 1
  funext i j
  refine Fin.lastCases ?_ (fun h ↦ ?_) i
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp [M, exponentialAdjunctionJacobianMatrix]
    · simp only [M, exponentialAdjunctionJacobianMatrix,
        Fin.lastCases_last, Fin.lastCases_castSucc]
      change -p.2 * D (Fin.last n) k.castSucc p =
        -p.2 * fderiv ℝ g p.1 (basis k)
      have hDlast := (hD p hp (Fin.last n) k.castSucc).2
      simp only [G, functionTupleSnoc_last] at hDlast
      rw [hDlast]
      have hgcomp : HasFDerivAt (fun q : E × ℝ ↦ g q.1)
          ((fderiv ℝ g p.1).comp (ContinuousLinearMap.fst ℝ E ℝ)) p :=
        (hgdiff p hp).hasFDerivAt.comp p
          (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt
      have happ := congrArg
        (fun L : (E × ℝ) →L[ℝ] ℝ ↦ L (basis k, 0)) hgcomp.fderiv
      rw [graphProductBasis_castSucc]
      rw [happ]
      simp
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simpa [M, exponentialAdjunctionJacobianMatrix, G] using
        (hD p hp h.castSucc (Fin.last n)).2
    · simpa [M, exponentialAdjunctionJacobianMatrix, G] using
        (hD p hp h.castSucc k.castSucc).2

end AbelFormalization
