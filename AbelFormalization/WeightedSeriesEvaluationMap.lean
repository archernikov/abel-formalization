import AbelFormalization.WeightedSeriesBanach
import AbelFormalization.WeightedSeriesEvaluation
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.Normed.Operator.Basic

/-! # Bounded evaluation maps on the weighted Banach algebra

Evaluation inside the closed polydisk is both a real-algebra homomorphism and
a continuous linear functional with norm at most one. Consequently it commutes
with every convergent sum in the weighted Banach space.
-/

noncomputable section

namespace AbelFormalization

variable {σ : Type*}

/-- Evaluation inside the polyradii, bundled as a real-algebra homomorphism. -/
def weightedSeriesEvalAlgHom (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ ρ i) : WeightedSeries ρ hρ →ₐ[ℝ] ℝ where
  toFun f := weightedSeriesEval f.val x
  map_zero' := weightedSeriesEval_zero x
  map_one' := weightedSeriesEval_one x
  map_add' f g := weightedSeriesEval_add hx f.property g.property
  map_mul' f g := weightedSeriesEval_mul hx f.property g.property
  commutes' c := weightedSeriesEval_C c x

@[simp]
theorem weightedSeriesEvalAlgHom_apply (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ ρ i) (f : WeightedSeries ρ hρ) :
    weightedSeriesEvalAlgHom ρ hρ x hx f = weightedSeriesEval f.val x := rfl

/-- Evaluation as a bounded real-linear functional. -/
def weightedSeriesEvalCLM (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ ρ i) : WeightedSeries ρ hρ →L[ℝ] ℝ :=
  (weightedSeriesEvalAlgHom ρ hρ x hx).toLinearMap.mkContinuous 1 fun f => by
    simpa only [one_mul, weightedSeries_norm_eq, weightedSeriesEvalAlgHom_apply,
      AlgHom.toLinearMap_apply] using norm_weightedSeriesEval_le hx f.property

@[simp]
theorem weightedSeriesEvalCLM_apply (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ ρ i) (f : WeightedSeries ρ hρ) :
    weightedSeriesEvalCLM ρ hρ x hx f = weightedSeriesEval f.val x := rfl

theorem weightedSeriesEvalCLM_norm_le (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ ρ i) :
    ‖weightedSeriesEvalCLM ρ hρ x hx‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [weightedSeriesEvalCLM_apply, one_mul, weightedSeries_norm_eq] using
    norm_weightedSeriesEval_le hx f.property

/-- The continuous and algebraic structures refer to the same evaluation map. -/
def weightedSeriesEvalContinuousAlgHom (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ ρ i) : WeightedSeries ρ hρ →A[ℝ] ℝ where
  toAlgHom := weightedSeriesEvalAlgHom ρ hρ x hx
  cont := (weightedSeriesEvalCLM ρ hρ x hx).continuous

theorem weightedSeriesEval_hasSum (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ ρ i) {ι : Type*}
    {f : ι → WeightedSeries ρ hρ} {s : WeightedSeries ρ hρ} (hf : HasSum f s) :
    HasSum (fun i => weightedSeriesEval (f i).val x) (weightedSeriesEval s.val x) :=
  (weightedSeriesEvalCLM ρ hρ x hx).hasSum hf

theorem weightedSeriesEval_tsum (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (x : σ → ℝ) (hx : ∀ i, |x i| ≤ ρ i) {ι : Type*}
    {f : ι → WeightedSeries ρ hρ} (hf : Summable f) :
    weightedSeriesEval (∑' i, f i).val x = ∑' i, weightedSeriesEval (f i).val x :=
  (weightedSeriesEvalCLM ρ hρ x hx).map_tsum hf

end AbelFormalization
