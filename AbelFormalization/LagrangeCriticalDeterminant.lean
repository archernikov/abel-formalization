import AbelFormalization.ClosedDenominatorGraph
import Mathlib.Analysis.Calculus.LagrangeMultipliers

/-!
# Lagrange multipliers and the critical determinant

The critical determinant in the manuscript is the determinant obtained by
appending the derivative of squared distance to the constraint derivative
matrix.  This file proves directly from mathlib's Lagrange multiplier theorem
that this determinant vanishes at every constrained local extremum.
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- A linearly dependent finite family remains dependent after applying a
linear map. -/
theorem not_linearIndependent_comp_linearMap
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (v : ι → M) (hdep : ¬ LinearIndependent ℝ v) (L : M →ₗ[ℝ] N) :
    ¬ LinearIndependent ℝ (L ∘ v) := by
  rw [Fintype.not_linearIndependent_iff] at hdep ⊢
  obtain ⟨g, hg, i, hi⟩ := hdep
  refine ⟨g, ?_, i, hi⟩
  calc
    ∑ j, g j • (L ∘ v) j = L (∑ j, g j • v j) := by simp
    _ = 0 := by rw [hg, map_zero]

/-- Evaluate a continuous linear functional on a finite tuple of directions. -/
def dualEvaluationMap {κ : Type*} (basis : κ → E) :
    StrongDual ℝ E →ₗ[ℝ] (κ → ℝ) where
  toFun φ j := φ (basis j)
  map_add' φ ψ := by
    funext j
    rfl
  map_smul' a φ := by
    funext j
    rfl

@[simp]
theorem dualEvaluationMap_apply {κ : Type*} (basis : κ → E)
    (φ : StrongDual ℝ E) (j : κ) :
    dualEvaluationMap basis φ j = φ (basis j) := rfl

/-- A dependent family of covectors gives a zero determinant after evaluation
on any equally indexed tuple of directions. -/
theorem det_evaluation_eq_zero_of_not_linearIndependent
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (v : ι → StrongDual ℝ E) (basis : κ → E)
    (hdep : ¬ LinearIndependent ℝ v) :
    Matrix.det (fun i j ↦ v (e i) (basis j)) = 0 := by
  apply Matrix.det_eq_zero_of_not_linearIndependent_rows
  intro hrows
  apply not_linearIndependent_comp_linearMap v hdep (dualEvaluationMap basis)
  apply (linearIndependent_equiv e).mp
  change LinearIndependent ℝ (fun i j ↦ v (e i) (basis j))
  exact hrows

/-- At a constrained local extremum, appending the objective differential to
the constraint differentials produces a singular square matrix. -/
theorem criticalDeterminant_eq_zero_of_isLocalExtrOn
    {r : ℕ} (H : Fin r → E → ℝ) (ρ : E → ℝ) (x : E)
    (basis : Fin (r + 1) → E)
    (hlocal : IsLocalExtrOn ρ {y | ∀ i, H i y = H i x} x)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hρ : HasStrictFDerivAt ρ (fderiv ℝ ρ x) x) :
    Matrix.det (fun i j ↦
      (Option.elim' (fderiv ℝ ρ x) (fun k ↦ fderiv ℝ (H k) x)
        (finSuccEquivLast i)) (basis j)) = 0 := by
  apply det_evaluation_eq_zero_of_not_linearIndependent finSuccEquivLast
  exact hlocal.linear_dependent_of_hasStrictFDerivAt hH hρ

/-- The same conclusion in the `functionTupleSnoc` row ordering used by the
expression-level critical-system construction. -/
theorem criticalSystemDeterminant_eq_zero_of_isLocalExtrOn
    {r : ℕ} (H : Fin r → E → ℝ) (ρ : E → ℝ) (x : E)
    (basis : Fin (r + 1) → E)
    (hlocal : IsLocalExtrOn ρ {y | ∀ i, H i y = H i x} x)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hρ : HasStrictFDerivAt ρ (fderiv ℝ ρ x) x) :
    Matrix.det (fun i j ↦
      fderiv ℝ (functionTupleSnoc H ρ i) x (basis j)) = 0 := by
  have hzero :=
    criticalDeterminant_eq_zero_of_isLocalExtrOn H ρ x basis hlocal hH hρ
  rw [show (fun i j ↦ fderiv ℝ (functionTupleSnoc H ρ i) x (basis j)) =
      (fun i j ↦
        (Option.elim' (fderiv ℝ ρ x) (fun k ↦ fderiv ℝ (H k) x)
          (finSuccEquivLast i)) (basis j)) by
    funext i j
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · simp
    · simp]
  exact hzero

/-- A global minimum on `t` is a local minimum on `s` if, near the point,
`s` lies in `t`. -/
theorem IsMinOn.isLocalMinOn_of_mem_nhds_inter_subset
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} {s t U : Set X} {x : X}
    (hmin : IsMinOn f t x) (hU : U ∈ nhds x) (hsub : U ∩ s ⊆ t) :
    IsLocalMinOn f s x := by
  rw [IsLocalMinOn]
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin]
    with y hyU hys
  exact hmin (hsub ⟨hyU, hys⟩)

/-- A componentwise minimum is a zero of the critical determinant whenever
the local constraint fiber lies in that connected component. -/
theorem criticalSystemDeterminant_eq_zero_of_componentMinimizer
    {r : ℕ} (H : Fin r → E → ℝ) (ρ : E → ℝ) (x : E)
    (basis : Fin (r + 1) → E) {U : Set E}
    (hmin : x ∈ componentMinimizers ρ) (hU : U ∈ nhds x)
    (hlocalFiber : U ∩ {y | ∀ i, H i y = H i x} ⊆ connectedComponent x)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hρ : HasStrictFDerivAt ρ (fderiv ℝ ρ x) x) :
    Matrix.det (fun i j ↦
      fderiv ℝ (functionTupleSnoc H ρ i) x (basis j)) = 0 := by
  change IsMinOn ρ (connectedComponent x) x at hmin
  apply criticalSystemDeterminant_eq_zero_of_isLocalExtrOn H ρ x basis
    (Or.inl (IsMinOn.isLocalMinOn_of_mem_nhds_inter_subset
      hmin hU hlocalFiber)) hH hρ

end AbelFormalization
