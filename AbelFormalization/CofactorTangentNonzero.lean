import AbelFormalization.CofactorTangent
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Nonvanishing of the cofactor tangent

For a codimension-one regular constraint system, the maximal-minor cofactor
vector cannot vanish.  The proof extends the independent constraint
covectors by one covector, evaluates the resulting basis of the dual on an
ambient basis, and uses nonsingularity of the resulting square matrix.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem constraintCovectors_linearIndependent_of_surjective
    {r : ℕ} (H : Fin r → E → ℝ) (x : E)
    (hsurj : (constraintFDeriv H x).range = ⊤) :
    LinearIndependent ℝ (fun i ↦ fderiv ℝ (H i) x) := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp hsurj
    (Pi.single i (1 : ℝ) : Fin r → ℝ)
  have hycoord : ∀ j, fderiv ℝ (H j) x y =
      (Pi.single i (1 : ℝ) : Fin r → ℝ) j := by
    intro j
    have := congrFun hy j
    simpa [constraintFDeriv] using this
  have hsumy := congrArg (fun L : E →L[ℝ] ℝ ↦ L y) hsum
  simp only [sum_apply, smul_apply, smul_eq_mul, zero_apply, hycoord] at hsumy
  simpa [Pi.single_apply, hi] using hsumy

theorem dualEvaluationMap_injective {n : ℕ}
    (basis : Module.Basis (Fin n) ℝ E) :
    Function.Injective (dualEvaluationMap basis) := by
  intro phi psi h
  apply ContinuousLinearMap.coe_injective
  apply basis.ext
  intro i
  exact congrFun h i

variable [FiniteDimensional ℝ E]

theorem exists_objective_criticalDeterminant_ne_zero
    {r : ℕ} (H : Fin r → E → ℝ) (x : E)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (hsurj : (constraintFDeriv H x).range = ⊤) :
    ∃ f : E → ℝ, criticalDeterminant H f basis x ≠ 0 := by
  have hrows : LinearIndependent ℝ (fun i ↦ fderiv ℝ (H i) x) :=
    constraintCovectors_linearIndependent_of_surjective H x hsurj
  have hdualfin : Module.finrank ℝ (StrongDual ℝ E) =
      Module.finrank ℝ E := by
    calc
      Module.finrank ℝ (StrongDual ℝ E) =
          Module.finrank ℝ (Module.Dual ℝ E) :=
        (LinearMap.toContinuousLinearMap :
          (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq.symm
      _ = Module.finrank ℝ E := Subspace.dual_finrank_eq
  have hEfin : Module.finrank ℝ E = r + 1 := by
    simpa using Module.finrank_eq_card_basis basis
  have hlt : r < Module.finrank ℝ (StrongDual ℝ E) := by
    rw [hdualfin, hEfin]
    exact Nat.lt_succ_self r
  obtain ⟨phi, hsnoc⟩ :=
    exists_linearIndependent_snoc_of_lt_finrank hrows hlt
  let f : E → ℝ := fun y ↦ phi y
  refine ⟨f, ?_⟩
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    criticalJacobianMatrix H f basis x
  have hroweq : M.row =
      (dualEvaluationMap basis) ∘
        Fin.snoc (fun i ↦ fderiv ℝ (H i) x) phi := by
    funext i j
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · simp only [M, Matrix.row_apply, criticalJacobianMatrix,
        functionTupleSnoc_last, Function.comp_apply, Fin.snoc_last,
        dualEvaluationMap_apply]
      exact congrArg (fun L : E →L[ℝ] ℝ ↦ L (basis j))
        phi.hasFDerivAt.fderiv
    · simp [M, criticalJacobianMatrix, Fin.snoc_castSucc]
  have hevalker : (dualEvaluationMap basis).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (dualEvaluationMap_injective basis)
  have hmatrixrows : LinearIndependent ℝ M.row := by
    rw [hroweq]
    exact hsnoc.map' (dualEvaluationMap basis) hevalker
  change M.det ≠ 0
  exact Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_row hmatrixrows)

theorem criticalCofactorTangent_ne_zero_of_surjective
    {r : ℕ} (H : Fin r → E → ℝ) (rho : E → ℝ) (x : E)
    (basis : Module.Basis (Fin (r + 1)) ℝ E)
    (hsurj : (constraintFDeriv H x).range = ⊤) :
    criticalCofactorTangent H rho basis x ≠ 0 := by
  obtain ⟨f, hf⟩ :=
    exists_objective_criticalDeterminant_ne_zero H x basis hsurj
  exact criticalCofactorTangent_ne_zero_of_criticalDeterminant_ne_zero
    H rho f basis x hf

end AbelFormalization
