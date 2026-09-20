import AbelFormalization.MaxwellPseudofunction
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Topology of Maxwell difference-quotient traces

This file supplies the elementary topological and analytic facts behind the
zero-step trace of a Maxwell directional difference quotient.  In particular,
the zero-step insertion is linear and continuous, its pullback of the closed
quotient relation is closed, and an ordinary differentiable scalar graph
contains its directional derivative in the zero-step trace.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- The zero-step insertion, bundled as a linear map. -/
def maxwellInsertZeroStepLinearMap (p : ℕ) :
    RealEuclidean (p + 1) →ₗ[ℝ] RealEuclidean ((p + 1) + 1) where
  toFun := maxwellInsertZeroStep
  map_add' := by
    intro v w
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
    · refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) k <;>
        simp [maxwellInsertZeroStep, realEuclideanAppend,
          realEuclideanTakeLeft, realEuclideanTakeRight]
    · simp [maxwellInsertZeroStep, realEuclideanAppend,
        realEuclideanTakeLeft, realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
    · refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) k <;>
        simp [maxwellInsertZeroStep, realEuclideanAppend,
          realEuclideanTakeLeft, realEuclideanTakeRight]
    · simp [maxwellInsertZeroStep, realEuclideanAppend,
        realEuclideanTakeLeft, realEuclideanTakeRight]

@[simp]
theorem maxwellInsertZeroStepLinearMap_apply {p : ℕ}
    (v : RealEuclidean (p + 1)) :
    maxwellInsertZeroStepLinearMap p v = maxwellInsertZeroStep v :=
  rfl

/-- Inserting a zero step is continuous. -/
theorem continuous_maxwellInsertZeroStep {p : ℕ} :
    Continuous (@maxwellInsertZeroStep p) :=
  (maxwellInsertZeroStepLinearMap p).continuous_of_finiteDimensional

theorem maxwellInsertZeroStep_continuous {p : ℕ} :
    Continuous (@maxwellInsertZeroStep p) :=
  continuous_maxwellInsertZeroStep

/-- The zero-step trace is closed, independently of any geometric-family
membership assertion for the quotient relation. -/
theorem isClosed_maxwellDifferenceQuotientZeroTrace
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    IsClosed (maxwellDifferenceQuotientZeroTrace U R i) := by
  exact isClosed_closure.preimage continuous_maxwellInsertZeroStep

theorem maxwellDifferenceQuotientZeroTrace_isClosed
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    IsClosed (maxwellDifferenceQuotientZeroTrace U R i) :=
  isClosed_maxwellDifferenceQuotientZeroTrace U R i

/-- At a differentiability point of an ordinary scalar graph, the value of
the Fréchet derivative in a coordinate direction belongs to the zero-step
difference-quotient trace.  This is the analytic assertion in Lemma 2.3.8(4)
of the source. -/
theorem maxwellDifferenceQuotientZeroTrace_functionGraph_fderiv_mem
    {p : ℕ} {U : Set (RealEuclidean p)} (hU : IsOpen U)
    {x : RealEuclidean p} (hx : x ∈ U)
    (f : RealEuclidean p → ℝ) (i : Fin p)
    (hf : DifferentiableAt ℝ f x) :
    realEuclideanAppend x
        (fun _ : Fin 1 ↦
          fderiv ℝ f x (Pi.single i 1 : RealEuclidean p)) ∈
      maxwellDifferenceQuotientZeroTrace U
        (maxwellFunctionGraph U (fun u _ ↦ f u)) i := by
  let v : RealEuclidean p := Pi.single i 1
  let d : ℝ := fderiv ℝ f x v
  let quotientPoint : ℝ → RealEuclidean ((p + 1) + 1) := fun epsilon ↦
    realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
      (fun _ : Fin 1 ↦
        epsilon⁻¹ • (f (x + epsilon • v) - f x))

  change realEuclideanAppend x (fun _ : Fin 1 ↦ d) ∈
    maxwellDifferenceQuotientZeroTrace U
      (maxwellFunctionGraph U (fun u _ ↦ f u)) i

  have hepsilonZero :
      Tendsto (fun epsilon : ℝ ↦ epsilon) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id

  have hquotient :
      Tendsto
        (fun epsilon : ℝ ↦ epsilon⁻¹ • (f (x + epsilon • v) - f x))
        (𝓝[≠] 0) (𝓝 d) := by
    exact (hf.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero

  have hpath :
      Tendsto quotientPoint (𝓝[≠] 0)
        (𝓝 (realEuclideanAppend
          (realEuclideanAppend x (0 : RealEuclidean 1))
          (fun _ : Fin 1 ↦ d))) := by
    apply tendsto_pi_nhds.2
    intro j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
    · refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) k
      · simpa [quotientPoint, realEuclideanAppend] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x l) (𝓝[≠] 0) (𝓝 (x l)))
      · simpa [quotientPoint, realEuclideanAppend] using
          hepsilonZero
    · simpa [quotientPoint, realEuclideanAppend] using hquotient

  have hshift :
      Tendsto (fun epsilon : ℝ ↦ x + epsilon • v)
        (𝓝[≠] 0) (𝓝 x) := by
    simpa using
      (tendsto_const_nhds.add
        (hepsilonZero.smul
          (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ v) (𝓝[≠] 0) (𝓝 v))))
  have hshiftU : ∀ᶠ epsilon : ℝ in 𝓝[≠] 0, x + epsilon • v ∈ U :=
    hshift.eventually (hU.mem_nhds hx)
  have hne : ∀ᶠ epsilon : ℝ in 𝓝[≠] 0, epsilon ≠ 0 := by
    filter_upwards [eventually_mem_nhdsWithin] with epsilon hepsilon
    simpa using hepsilon
  have hmem :
      ∀ᶠ epsilon : ℝ in 𝓝[≠] 0,
        quotientPoint epsilon ∈
          maxwellDifferenceQuotientRelation U
            (maxwellFunctionGraph U (fun u _ ↦ f u)) i := by
    filter_upwards [hshiftU, hne] with epsilon hepsilonU hepsilon
    rw [show quotientPoint epsilon =
        realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
          (fun _ : Fin 1 ↦
            epsilon⁻¹ • (f (x + epsilon • v) - f x)) by rfl]
    rw [realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_functionGraph_iff]
    refine ⟨hx, ?_, hepsilon, ?_⟩
    · simpa [v] using hepsilonU
    · simp only [v]
      rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hepsilon, one_mul]

  apply
    (realEuclideanAppend_scalar_mem_maxwellDifferenceQuotientZeroTrace_iff
      U (maxwellFunctionGraph U (fun u _ ↦ f u)) i x d).mpr
  exact mem_closure_of_tendsto hpath hmem

/-- Predicate-form packaging of the preceding analytic containment theorem. -/
theorem maxwellDifferenceQuotientTraceContainsDirectionalDerivative_functionGraph
    {p : ℕ} {U : Set (RealEuclidean p)} (hU : IsOpen U)
    (f : RealEuclidean p → ℝ) (i : Fin p) :
    MaxwellDifferenceQuotientTraceContainsDirectionalDerivative U
      (maxwellFunctionGraph U (fun u _ ↦ f u)) i f := by
  intro x hx hfx
  exact maxwellDifferenceQuotientZeroTrace_functionGraph_fderiv_mem
    hU hx f i hfx

end AbelFormalization
