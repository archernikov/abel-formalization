import AbelFormalization.AnalyticGermDerivatives
import AbelFormalization.AnalyticGermLocal
import Mathlib.RingTheory.Derivation.Basic

/-! # Derivations of the actual analytic-germ algebra

Directional differentiation is a real-linear derivation of the real-analytic
germ ring. Coordinate partial derivatives are obtained by choosing the
standard coordinate directions.
-/

noncomputable section

open Filter
open scoped Topology

namespace AbelFormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Directional differentiation is linear over the constant real germs. -/
theorem analyticGermDirectionalDerivative_smul (x v : E) (c : ℝ) (g : AnalyticGermAt x) :
    analyticGermDirectionalDerivative x v (c • g) =
      c • analyticGermDirectionalDerivative x v g := by
  simp only [Algebra.smul_def, analyticGerm_algebraMap, analyticGermDirectionalDerivative_mul,
    analyticGermDirectionalDerivative_const, zero_mul, zero_add]

/-- Directional differentiation as a derivation of the real-analytic germ
algebra, with its actual constant coefficient map. -/
def analyticGermDerivation (x v : E) :
    Derivation ℝ (AnalyticGermAt x) (AnalyticGermAt x) where
  toFun := analyticGermDirectionalDerivative x v
  map_add' := analyticGermDirectionalDerivative_add x v
  map_smul' := analyticGermDirectionalDerivative_smul x v
  map_one_eq_zero' := by
    change analyticGermDirectionalDerivative x v
      (analyticGermOf (fun _ : E => 1) analyticAt_const) = 0
    exact analyticGermDirectionalDerivative_const x v 1
  leibniz' f g := by
    change analyticGermDirectionalDerivative x v (f * g) =
      f * analyticGermDirectionalDerivative x v g + g * analyticGermDirectionalDerivative x v f
    simpa only [mul_comm, add_comm] using
      analyticGermDirectionalDerivative_mul x v f g

@[simp]
theorem analyticGermDerivation_apply (x v : E) (g : AnalyticGermAt x) :
    analyticGermDerivation x v g = analyticGermDirectionalDerivative x v g := rfl

/-- The bundled derivation has the expected representative. -/
theorem analyticGermDerivation_of {x : E} (v : E) (f : E → ℝ)
    (hf : AnalyticAt ℝ f x) :
    analyticGermDerivation x v (analyticGermOf f hf) =
      analyticGermOf (fun y => fderiv ℝ f y v) (analyticAt_directionalDerivative hf v) := rfl

@[simp]
theorem analyticGermDerivation_value_of {x : E} (v : E) (f : E → ℝ)
    (hf : AnalyticAt ℝ f x) :
    analyticGermValue x (analyticGermDerivation x v (analyticGermOf f hf)) =
      fderiv ℝ f x v := rfl

/-- The germ of a coordinate function at the origin. -/
def analyticGermCoordinate (p : ℕ) (j : Fin p) : RealAnalyticGerm p :=
  let L : (Fin p → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  analyticGermOf L (L.analyticAt (0 : Fin p → ℝ))

/-- The coordinate partial derivation on germs in finitely many variables. -/
def analyticGermPartial (p : ℕ) (i : Fin p) :
    Derivation ℝ (RealAnalyticGerm p) (RealAnalyticGerm p) :=
  analyticGermDerivation 0 (Pi.single i (1 : ℝ))

/-- A coordinate partial derivative of a coordinate germ is the corresponding
Kronecker delta, viewed as a constant germ. -/
theorem analyticGermPartial_coordinate (p : ℕ) (i j : Fin p) :
    analyticGermPartial p i (analyticGermCoordinate p j) =
      algebraMap ℝ (RealAnalyticGerm p) (if i = j then 1 else 0) := by
  unfold analyticGermPartial analyticGermCoordinate
  rw [analyticGermDerivation_of, analyticGerm_algebraMap, analyticGermOf_eq_iff]
  filter_upwards with y
  rw [ContinuousLinearMap.fderiv]
  simp [ContinuousLinearMap.proj_apply, Pi.single_apply, eq_comm]

end AbelFormalization
