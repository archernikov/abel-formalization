import AbelFormalization.ExponentialLogComparisonGlobal

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original constraints, the reciprocal graph equation, and a final
comparison equation, in the row order used on the closed curve. -/
def denominatorComparisonProductSystem {r : ℕ}
    (H : Fin r → E → ℝ) (q h : E → ℝ) :
    Fin ((r + 1) + 1) → E × ℝ → ℝ :=
  functionTupleSnoc
    (functionTupleSnoc
      (fun i p ↦ H i p.1)
      (fun p ↦ p.2 * q p.1 - 1))
    (fun p ↦ h p.1)

theorem constraintFDeriv_denominatorComparisonProductSystem_surjective
    {r : ℕ} (H : Fin r → E → ℝ) (q h : E → ℝ)
    (x : E) (z : ℝ)
    (hH : ∀ i, DifferentiableAt ℝ (H i) x)
    (hq : DifferentiableAt ℝ q x) (hh : DifferentiableAt ℝ h x)
    (hsurj : (constraintFDeriv (functionTupleSnoc H h) x).range = ⊤)
    (hqne : q x ≠ 0) :
    (constraintFDeriv (denominatorComparisonProductSystem H q h)
      (x, z)).range = ⊤ := by
  rw [LinearMap.range_eq_top] at hsurj ⊢
  intro w
  let wOld : Fin (r + 1) → ℝ :=
    fun i ↦ Fin.lastCases (w (Fin.last (r + 1)))
      (fun j ↦ w j.castSucc.castSucc) i
  obtain ⟨v, hv⟩ := hsurj wOld
  let t : ℝ :=
    (w (Fin.castSucc (Fin.last r)) - z * fderiv ℝ q x v) / q x
  refine ⟨(v, t), ?_⟩
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [constraintFDeriv]
    change fderiv ℝ
      (denominatorComparisonProductSystem H q h (Fin.last (r + 1)))
        (x, z) (v, t) = w (Fin.last (r + 1))
    rw [denominatorComparisonProductSystem, functionTupleSnoc_last]
    have htop := hh.hasFDerivAt.comp (x, z)
      (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt
    have htopEq : (fun p : E × ℝ ↦ h p.1) =
        h ∘ (ContinuousLinearMap.fst ℝ E ℝ) := rfl
    rw [htopEq, htop.fderiv]
    have hj := congrFun hv (Fin.last r)
    simpa [constraintFDeriv, wOld] using hj
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · rw [constraintFDeriv]
      change fderiv ℝ
        (denominatorComparisonProductSystem H q h
          (Fin.castSucc (Fin.last r))) (x, z) (v, t) =
        w (Fin.castSucc (Fin.last r))
      rw [denominatorComparisonProductSystem, functionTupleSnoc_castSucc,
        functionTupleSnoc_last]
      have hsnd : HasFDerivAt (fun p : E × ℝ ↦ p.2)
          (ContinuousLinearMap.snd ℝ E ℝ) (x, z) :=
        (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
      have hqcomp : HasFDerivAt (fun p : E × ℝ ↦ q p.1)
          ((fderiv ℝ q x).comp (ContinuousLinearMap.fst ℝ E ℝ)) (x, z) :=
        hq.hasFDerivAt.comp (x, z)
          (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt
      have hbottomEq : (fun p : E × ℝ ↦ p.2 * q p.1 - 1) =
          fun p ↦ ((fun y : E × ℝ ↦ y.2) *
            (fun y : E × ℝ ↦ q y.1)) p - 1 := rfl
      rw [hbottomEq, ((hsnd.mul hqcomp).sub_const (1 : ℝ)).fderiv]
      simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
        smul_eq_mul]
      dsimp [t]
      field_simp
      ring
    · rw [constraintFDeriv]
      change fderiv ℝ
        (denominatorComparisonProductSystem H q h k.castSucc.castSucc)
          (x, z) (v, t) = w k.castSucc.castSucc
      rw [denominatorComparisonProductSystem, functionTupleSnoc_castSucc,
        functionTupleSnoc_castSucc]
      have htop := (hH k).hasFDerivAt.comp (x, z)
        (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt
      have htopEq : (fun p : E × ℝ ↦ H k p.1) =
          H k ∘ (ContinuousLinearMap.fst ℝ E ℝ) := rfl
      rw [htopEq, htop.fderiv]
      have hk := congrFun hv k.castSucc
      simpa [constraintFDeriv, wOld] using hk

end AbelFormalization
