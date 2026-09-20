import AbelFormalization.AnalyticGerm
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Differentiation of analytic germs

Directional differentiation is independent of the analytic representative.
It preserves the analytic-germ ring and satisfies the sum and product rules.
-/

noncomputable section

namespace AbelFormalization

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem analyticAt_directionalDerivative {f : E → ℝ} {x : E}
    (hf : AnalyticAt ℝ f x) (v : E) :
    AnalyticAt ℝ (fun y => fderiv ℝ f y v) x := by
  exact ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt (fderiv ℝ f x)).fun_comp hf.fderiv

/-- Directional differentiation on neighborhood germs is well-defined even
before restricting to germs with analytic representatives. -/
def germDirectionalDerivative (x v : E) : Germ (𝓝 x) ℝ → Germ (𝓝 x) ℝ :=
  Germ.map' (fun f : E → ℝ => fun y => fderiv ℝ f y v) (by
    intro f g h
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun D : E →L[ℝ] ℝ => D v) hy)

/-- Directional differentiation preserves analytic germs. -/
def analyticGermDirectionalDerivative (x v : E) (g : AnalyticGermAt x) : AnalyticGermAt x :=
  ⟨germDirectionalDerivative x v g, by
    obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
    exact ⟨fun y => fderiv ℝ f y v, analyticAt_directionalDerivative hf v, rfl⟩⟩

@[simp]
theorem analyticGermDirectionalDerivative_of {x : E} (v : E) (f : E → ℝ)
    (hf : AnalyticAt ℝ f x) :
    analyticGermDirectionalDerivative x v (analyticGermOf f hf) =
      analyticGermOf (fun y => fderiv ℝ f y v) (analyticAt_directionalDerivative hf v) := rfl

theorem analyticGermDirectionalDerivative_add (x v : E) (f g : AnalyticGermAt x) :
    analyticGermDirectionalDerivative x v (f + g) =
      analyticGermDirectionalDerivative x v f + analyticGermDirectionalDerivative x v g := by
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative f
  obtain ⟨g, hg, rfl⟩ := exists_analyticGerm_representative g
  rw [← analyticGermOf_add, analyticGermDirectionalDerivative_of,
    analyticGermDirectionalDerivative_of, analyticGermDirectionalDerivative_of,
    ← analyticGermOf_add, analyticGermOf_eq_iff]
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with y hyf hyg
  change fderiv ℝ (f + g) y v = fderiv ℝ f y v + fderiv ℝ g y v
  rw [fderiv_add hyf.differentiableAt hyg.differentiableAt]
  rfl

theorem analyticGermDirectionalDerivative_mul (x v : E) (f g : AnalyticGermAt x) :
    analyticGermDirectionalDerivative x v (f * g) =
      analyticGermDirectionalDerivative x v f * g + f * analyticGermDirectionalDerivative x v g := by
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative f
  obtain ⟨g, hg, rfl⟩ := exists_analyticGerm_representative g
  rw [← analyticGermOf_mul, analyticGermDirectionalDerivative_of,
    analyticGermDirectionalDerivative_of, analyticGermDirectionalDerivative_of,
    ← analyticGermOf_mul, ← analyticGermOf_mul, ← analyticGermOf_add,
    analyticGermOf_eq_iff]
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with y hyf hyg
  change fderiv ℝ (f * g) y v = fderiv ℝ f y v * g y + f y * fderiv ℝ g y v
  rw [fderiv_mul hyf.differentiableAt hyg.differentiableAt]
  change f y * fderiv ℝ g y v + g y * fderiv ℝ f y v = _
  ring

@[simp]
theorem analyticGermDirectionalDerivative_const (x v : E) (c : ℝ) :
    analyticGermDirectionalDerivative x v
      (analyticGermOf (fun _ : E => c) analyticAt_const) = 0 := by
  apply Subtype.ext
  change (fun y => fderiv ℝ (fun _ : E => c) y v : Germ (𝓝 x) ℝ) = 0
  simp
  rfl

end AbelFormalization
