import AbelFormalization.ExponentialGraphJacobian

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_exponentialGraphEquation_at_graph
    (g : E → ℝ) {x : E} (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (fun p : E × ℝ ↦ p.2 - Real.exp (g p.1))
        (x, Real.exp (g x)) =
      ContinuousLinearMap.snd ℝ E ℝ -
        Real.exp (g x) • (fderiv ℝ g x).comp
          (ContinuousLinearMap.fst ℝ E ℝ) := by
  have hgcomp : HasFDerivAt (fun p : E × ℝ ↦ g p.1)
      ((fderiv ℝ g x).comp (ContinuousLinearMap.fst ℝ E ℝ))
      (x, Real.exp (g x)) :=
    hg.hasFDerivAt.comp (x, Real.exp (g x))
      (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt
  exact ((ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.sub hgcomp.exp).fderiv



theorem exponentialGraphJacobian_top_castSucc {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (p : E × ℝ)
    (i j : Fin n) :
    constraintJacobianInBasis (exponentialGraphLiftTuple Ftilde g)
        (graphProductBasis basis) p i.castSucc j.castSucc =
      fderiv ℝ (fun q ↦ Ftilde q i) p (basis j, 0) := by
  simp [constraintJacobianInBasis, exponentialGraphLiftTuple]

theorem exponentialGraphJacobian_top_last {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (p : E × ℝ)
    (i : Fin n) :
    constraintJacobianInBasis (exponentialGraphLiftTuple Ftilde g)
        (graphProductBasis basis) p i.castSucc (Fin.last n) =
      fderiv ℝ (fun q ↦ Ftilde q i) p (0, 1) := by
  simp [constraintJacobianInBasis, exponentialGraphLiftTuple]

theorem exponentialGraphJacobian_bottom_castSucc {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hg : DifferentiableAt ℝ g x) (j : Fin n) :
    constraintJacobianInBasis (exponentialGraphLiftTuple Ftilde g)
        (graphProductBasis basis) (x, Real.exp (g x))
        (Fin.last n) j.castSucc =
      -Real.exp (g x) * fderiv ℝ g x (basis j) := by
  rw [constraintJacobianInBasis, exponentialGraphLiftTuple,
    functionTupleSnoc_last, graphProductBasis_castSucc,
    fderiv_exponentialGraphEquation_at_graph g hg]
  simp

theorem exponentialGraphJacobian_bottom_last {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hg : DifferentiableAt ℝ g x) :
    constraintJacobianInBasis (exponentialGraphLiftTuple Ftilde g)
        (graphProductBasis basis) (x, Real.exp (g x))
        (Fin.last n) (Fin.last n) = 1 := by
  rw [constraintJacobianInBasis, exponentialGraphLiftTuple,
    functionTupleSnoc_last, graphProductBasis_last,
    fderiv_exponentialGraphEquation_at_graph g hg]
  simp


/-- The displayed block matrix
`[D_x F̃  D_Y F̃; -exp(g(x)) Dg  1]` from the manuscript. -/
def paperExponentialGraphJacobianMatrix {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) (x : E) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j ↦ Fin.lastCases
    (Fin.lastCases 1
      (fun k ↦ -Real.exp (g x) * fderiv ℝ g x (basis k)) j)
    (fun h ↦ Fin.lastCases
      (fderiv ℝ (fun q ↦ Ftilde q h) (x, Real.exp (g x)) (0, 1))
      (fun k ↦ fderiv ℝ (fun q ↦ Ftilde q h)
        (x, Real.exp (g x)) (basis k, 0)) j) i

theorem constraintJacobianInBasis_exponentialGraph_eq_paperMatrix {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hg : DifferentiableAt ℝ g x) :
    constraintJacobianInBasis (exponentialGraphLiftTuple Ftilde g)
        (graphProductBasis basis) (x, Real.exp (g x)) =
      paperExponentialGraphJacobianMatrix Ftilde g basis x := by
  ext i j
  refine Fin.lastCases ?_ (fun h ↦ ?_) i
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simpa [paperExponentialGraphJacobianMatrix] using
        exponentialGraphJacobian_bottom_last Ftilde g basis hg
    · simpa [paperExponentialGraphJacobianMatrix] using
        exponentialGraphJacobian_bottom_castSucc Ftilde g basis hg k
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simpa [paperExponentialGraphJacobianMatrix] using
        exponentialGraphJacobian_top_last Ftilde g basis
          (x, Real.exp (g x)) h
    · simpa [paperExponentialGraphJacobianMatrix] using
        exponentialGraphJacobian_top_castSucc Ftilde g basis
          (x, Real.exp (g x)) h k

theorem exponentialGraphJacobian_eq_det_paperMatrix {n : ℕ}
    (Ftilde : E × ℝ → Fin n → ℝ) (g : E → ℝ)
    (basis : Module.Basis (Fin n) ℝ E) {x : E}
    (hg : DifferentiableAt ℝ g x) :
    exponentialGraphJacobian Ftilde g basis (x, Real.exp (g x)) =
      (paperExponentialGraphJacobianMatrix Ftilde g basis x).det := by
  rw [exponentialGraphJacobian_eq_det_constraintJacobian,
    constraintJacobianInBasis_exponentialGraph_eq_paperMatrix Ftilde g basis hg]

end AbelFormalization
