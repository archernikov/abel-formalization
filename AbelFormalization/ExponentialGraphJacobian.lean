import AbelFormalization.ExponentialGraphRegularLift
import AbelFormalization.JacobianBasis
import Mathlib.LinearAlgebra.Basis.Prod

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Split a successor tuple into its initial coordinates and final coordinate. -/
def finSnocContinuousLinearEquiv (n : ℕ) :
    ((Fin n → ℝ) × ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) where
  toFun p := Fin.lastCases p.2 p.1
  invFun v := (fun i ↦ v i.castSucc, v (Fin.last n))
  left_inv p := by
    apply Prod.ext
    · funext i
      simp
    · simp
  right_inv v := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  map_add' p q := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  map_smul' c p := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have heq :
          (fun p : (Fin n → ℝ) × ℝ ↦ Fin.lastCases p.2 p.1 (Fin.last n)) =
            fun p ↦ p.2 := by
        funext p
        simp
      rw [heq]
      exact continuous_snd
    · have heq :
          (fun p : (Fin n → ℝ) × ℝ ↦ Fin.lastCases p.2 p.1 j.castSucc) =
            fun p ↦ p.1 j := by
        funext p
        simp
      rw [heq]
      exact (continuous_apply j).comp continuous_fst
  continuous_invFun := by
    exact (continuous_pi fun i ↦ continuous_apply i.castSucc).prodMk
      (continuous_apply (Fin.last n))

@[simp]
theorem finSnocContinuousLinearEquiv_castSucc (n : ℕ)
    (p : (Fin n → ℝ) × ℝ) (i : Fin n) :
    finSnocContinuousLinearEquiv n p i.castSucc = p.1 i := by
  simp [finSnocContinuousLinearEquiv]

@[simp]
theorem finSnocContinuousLinearEquiv_last (n : ℕ)
    (p : (Fin n → ℝ) × ℝ) :
    finSnocContinuousLinearEquiv n p (Fin.last n) = p.2 := by
  simp [finSnocContinuousLinearEquiv]

/-- Product basis ordered with all old directions first and the fresh graph
direction last. -/
def graphProductBasis {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {n : ℕ} (basis : Module.Basis (Fin n) ℝ E) :
    Module.Basis (Fin (n + 1)) ℝ (E × ℝ) :=
  (basis.prod (Module.Basis.singleton (Fin 1) ℝ)).reindex finSumFinEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp]
theorem graphProductBasis_castSucc {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) (i : Fin n) :
    graphProductBasis basis i.castSucc = (basis i, 0) := by
  rw [graphProductBasis, Module.Basis.reindex_apply,
    finSumFinEquiv_symm_apply_castSucc, Module.Basis.prod_apply,
    Sum.elim_inl, LinearMap.coe_inl, Function.comp_apply]

@[simp]
theorem graphProductBasis_last {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) :
    graphProductBasis basis (Fin.last n) = (0, 1) := by
  rw [graphProductBasis, Module.Basis.reindex_apply,
    finSumFinEquiv_symm_last, Module.Basis.prod_apply,
    Sum.elim_inr, LinearMap.coe_inr, Function.comp_apply,
    Module.Basis.singleton_apply]

/-- Scalar-coordinate form of the lifted exponential graph system. -/
def exponentialGraphLiftTuple {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ) :
    Fin (n + 1) → E × ℝ → ℝ :=
  functionTupleSnoc (fun i p ↦ Ftilde p i)
    (fun p ↦ p.2 - Real.exp (g p.1))

theorem constraintMap_exponentialGraphLiftTuple {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ) :
    constraintMap (exponentialGraphLiftTuple Ftilde g) =
      fun p ↦ finSnocContinuousLinearEquiv n
        (exponentialGraphLiftSystem Ftilde g p) := by
  funext p i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;>
    simp [constraintMap, exponentialGraphLiftTuple,
      exponentialGraphLiftSystem, graphLiftSystem]

theorem fderiv_constraintMap_eq_constraintFDeriv {n : ℕ}
    (H : Fin n → E → ℝ) (p : E)
    (hH : ∀ i, DifferentiableAt ℝ (H i) p) :
    fderiv ℝ (constraintMap H) p = constraintFDeriv H p := by
  change fderiv ℝ (fun x i ↦ H i x) p =
    ContinuousLinearMap.pi (fun i ↦ fderiv ℝ (H i) p)
  exact fderiv_pi hH

theorem fderiv_constraintMap_exponentialGraphLiftTuple {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ) (p : E × ℝ)
    (hG : DifferentiableAt ℝ (exponentialGraphLiftSystem Ftilde g) p) :
    fderiv ℝ (constraintMap (exponentialGraphLiftTuple Ftilde g)) p =
      (finSnocContinuousLinearEquiv n :
        ((Fin n → ℝ) × ℝ) →L[ℝ] (Fin (n + 1) → ℝ)).comp
        (fderiv ℝ (exponentialGraphLiftSystem Ftilde g) p) := by
  have hcomp :=
    (finSnocContinuousLinearEquiv n).hasFDerivAt.comp p hG.hasFDerivAt
  rw [constraintMap_exponentialGraphLiftTuple]
  exact hcomp.fderiv

theorem surjective_constraintFDeriv_exponentialGraphLiftTuple {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ) (p : E × ℝ)
    (hG : DifferentiableAt ℝ (exponentialGraphLiftSystem Ftilde g) p)
    (hsurj : Function.Surjective
      (fderiv ℝ (exponentialGraphLiftSystem Ftilde g) p)) :
    Function.Surjective
      (constraintFDeriv (exponentialGraphLiftTuple Ftilde g) p) := by
  have hcomp :=
    (finSnocContinuousLinearEquiv n).hasFDerivAt.comp p hG.hasFDerivAt
  have htupleMap : DifferentiableAt ℝ
      (constraintMap (exponentialGraphLiftTuple Ftilde g)) p := by
    rw [constraintMap_exponentialGraphLiftTuple]
    exact hcomp.differentiableAt
  have htuple : ∀ i, DifferentiableAt ℝ
      (exponentialGraphLiftTuple Ftilde g i) p := by
    intro i
    simpa only [Function.comp_def, constraintMap] using
      (differentiableAt_apply i
        (constraintMap (exponentialGraphLiftTuple Ftilde g) p)).comp
          p htupleMap
  rw [← fderiv_constraintMap_eq_constraintFDeriv
    (exponentialGraphLiftTuple Ftilde g) p htuple]
  rw [fderiv_constraintMap_exponentialGraphLiftTuple Ftilde g p hG]
  exact (finSnocContinuousLinearEquiv n).surjective.comp hsurj

theorem surjective_exponentialGraphLiftSystem_of_constraintFDeriv {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ) (p : E × ℝ)
    (hG : DifferentiableAt ℝ (exponentialGraphLiftSystem Ftilde g) p)
    (hsurj : Function.Surjective
      (constraintFDeriv (exponentialGraphLiftTuple Ftilde g) p)) :
    Function.Surjective
      (fderiv ℝ (exponentialGraphLiftSystem Ftilde g) p) := by
  have hcomp :=
    (finSnocContinuousLinearEquiv n).hasFDerivAt.comp p hG.hasFDerivAt
  have htupleMap : DifferentiableAt ℝ
      (constraintMap (exponentialGraphLiftTuple Ftilde g)) p := by
    rw [constraintMap_exponentialGraphLiftTuple]
    exact hcomp.differentiableAt
  have htuple : ∀ i, DifferentiableAt ℝ
      (exponentialGraphLiftTuple Ftilde g i) p := by
    intro i
    simpa only [Function.comp_def, constraintMap] using
      (differentiableAt_apply i
        (constraintMap (exponentialGraphLiftTuple Ftilde g) p)).comp
          p htupleMap
  have htupleSurj : Function.Surjective
      (fderiv ℝ (constraintMap (exponentialGraphLiftTuple Ftilde g)) p) := by
    rw [fderiv_constraintMap_eq_constraintFDeriv
      (exponentialGraphLiftTuple Ftilde g) p htuple]
    exact hsurj
  rw [fderiv_constraintMap_exponentialGraphLiftTuple Ftilde g p hG]
    at htupleSurj
  intro y
  obtain ⟨v, hv⟩ := htupleSurj (finSnocContinuousLinearEquiv n y)
  refine ⟨v, (finSnocContinuousLinearEquiv n).injective ?_⟩
  exact hv

/-- The manuscript's square Jacobian after adjoining the final exponential
as a graph variable. -/
def exponentialGraphJacobian {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (p : E × ℝ) : ℝ :=
  criticalDeterminant (fun i q ↦ Ftilde q i)
    (fun q ↦ q.2 - Real.exp (g q.1)) (graphProductBasis basis) p

theorem exponentialGraphJacobian_eq_det_constraintJacobian {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (p : E × ℝ) :
    exponentialGraphJacobian Ftilde g basis p =
      (constraintJacobianInBasis (exponentialGraphLiftTuple Ftilde g)
        (graphProductBasis basis) p).det := by
  rfl

theorem exponentialGraphJacobian_ne_zero_of_surjective {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (p : E × ℝ)
    (hG : DifferentiableAt ℝ (exponentialGraphLiftSystem Ftilde g) p)
    (hsurj : Function.Surjective
      (fderiv ℝ (exponentialGraphLiftSystem Ftilde g) p)) :
    exponentialGraphJacobian Ftilde g basis p ≠ 0 := by
  rw [exponentialGraphJacobian_eq_det_constraintJacobian]
  exact (constraintJacobianInBasis_det_ne_zero_iff_surjective
    (exponentialGraphLiftTuple Ftilde g) (graphProductBasis basis) p).mpr
      (LinearMap.range_eq_top.mpr
        (surjective_constraintFDeriv_exponentialGraphLiftTuple
          Ftilde g p hG hsurj))

theorem exponentialGraphJacobian_ne_zero_iff_surjective {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (p : E × ℝ)
    (hG : DifferentiableAt ℝ (exponentialGraphLiftSystem Ftilde g) p) :
    exponentialGraphJacobian Ftilde g basis p ≠ 0 ↔
      Function.Surjective
        (fderiv ℝ (exponentialGraphLiftSystem Ftilde g) p) := by
  constructor
  · intro hJ
    apply surjective_exponentialGraphLiftSystem_of_constraintFDeriv
      Ftilde g p hG
    apply LinearMap.range_eq_top.mp
    apply (constraintJacobianInBasis_det_ne_zero_iff_surjective
      (exponentialGraphLiftTuple Ftilde g) (graphProductBasis basis) p).mp
    rw [← exponentialGraphJacobian_eq_det_constraintJacobian]
    exact hJ
  · exact exponentialGraphJacobian_ne_zero_of_surjective
      Ftilde g basis p hG

/-- Every original regular zero gives a point on the lifted graph where the
paper's Jacobian is nonzero. -/
theorem exponentialGraphJacobian_ne_zero_of_mem_regularZeroSet {n : ℕ}
    {Omega : Set E} (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, Real.exp (g x)))
    (hg : DifferentiableAt ℝ g x)
    (hx : x ∈ regularZeroSet Omega
      (exponentialGraphSubstitution Ftilde g)) :
    exponentialGraphJacobian Ftilde g basis (x, Real.exp (g x)) ≠ 0 := by
  have hlift :=
    (mem_regularZeroSet_exponentialGraphLift_iff hF hg).mp hx
  have hG : DifferentiableAt ℝ (exponentialGraphLiftSystem Ftilde g)
      (x, Real.exp (g x)) := by
    unfold exponentialGraphLiftSystem graphLiftSystem
    fun_prop
  exact exponentialGraphJacobian_ne_zero_of_surjective
    Ftilde g basis (x, Real.exp (g x)) hG hlift.2.2

end AbelFormalization
