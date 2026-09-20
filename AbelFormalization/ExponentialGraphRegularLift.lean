import AbelFormalization.RegularZeroGraphLift
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Substitute the exponential of the final exponent into a lifted system. -/
def exponentialGraphSubstitution (Ftilde : E × ℝ → F) (g : E → ℝ) : E → F :=
  graphSubstitution Ftilde (fun x ↦ Real.exp (g x))

/-- The square graph system used to compare regularity before and after
introducing the last exponential as a variable. -/
def exponentialGraphLiftSystem (Ftilde : E × ℝ → F) (g : E → ℝ) :
    E × ℝ → F × ℝ :=
  graphLiftSystem Ftilde (fun x ↦ Real.exp (g x))

@[simp]
theorem exponentialGraphSubstitution_apply
    (Ftilde : E × ℝ → F) (g : E → ℝ) (x : E) :
    exponentialGraphSubstitution Ftilde g x = Ftilde (x, Real.exp (g x)) :=
  rfl

@[simp]
theorem exponentialGraphLiftSystem_apply
    (Ftilde : E × ℝ → F) (g : E → ℝ) (p : E × ℝ) :
    exponentialGraphLiftSystem Ftilde g p =
      (Ftilde p, p.2 - Real.exp (g p.1)) :=
  rfl

/-- Regular-zero membership is preserved by adjoining the exponential graph
equation. -/
theorem mem_regularZeroSet_exponentialGraphLift_iff
    {Omega : Set E} {Ftilde : E × ℝ → F} {g : E → ℝ} {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, Real.exp (g x)))
    (hg : DifferentiableAt ℝ g x) :
    x ∈ regularZeroSet Omega (exponentialGraphSubstitution Ftilde g) ↔
      (x, Real.exp (g x)) ∈ regularZeroSet
        ((fun p : E × ℝ ↦ p.1) ⁻¹' Omega)
        (exponentialGraphLiftSystem Ftilde g) := by
  apply mem_regularZeroSet_graphLift_iff hF
  fun_prop

/-- The logarithmic comparison function; it is used only on the positive
half-space, never as an equation in the lower exponential level. -/
def exponentialGraphComparison (g : E → ℝ) : E × ℝ → ℝ :=
  fun p ↦ Real.log p.2 - g p.1

@[simp]
theorem exponentialGraphComparison_on_graph (g : E → ℝ) (x : E) :
    exponentialGraphComparison g (x, Real.exp (g x)) = 0 := by
  simp [exponentialGraphComparison]

theorem exponentialGraphComparison_eq_zero_iff
    (g : E → ℝ) {p : E × ℝ} (hp : 0 < p.2) :
    exponentialGraphComparison g p = 0 ↔ p.2 = Real.exp (g p.1) := by
  constructor
  · intro h
    have hlog : Real.log p.2 = g p.1 := sub_eq_zero.mp h
    calc
      p.2 = Real.exp (Real.log p.2) := (Real.exp_log hp).symm
      _ = Real.exp (g p.1) := congrArg Real.exp hlog
  · intro h
    rw [exponentialGraphComparison, h, Real.log_exp, sub_self]

theorem exponentialGraphLift_injective (g : E → ℝ) :
    Function.Injective (fun x ↦ (x, Real.exp (g x))) := by
  intro x y h
  exact congrArg Prod.fst h

/-- Finiteness descends along the injective exponential graph lift. -/
theorem finite_regularZeroSet_of_finite_exponentialGraphLift
    {Omega : Set E} {Ftilde : E × ℝ → F} {g : E → ℝ}
    (hF : ∀ x, DifferentiableAt ℝ Ftilde (x, Real.exp (g x)))
    (hg : Differentiable ℝ g)
    (hfinite : (regularZeroSet
      ((fun p : E × ℝ ↦ p.1) ⁻¹' Omega)
      (exponentialGraphLiftSystem Ftilde g)).Finite) :
    (regularZeroSet Omega (exponentialGraphSubstitution Ftilde g)).Finite := by
  apply Set.Finite.of_finite_image (f := fun x ↦ (x, Real.exp (g x)))
  · exact hfinite.subset fun y hy ↦ by
      obtain ⟨x, hx, rfl⟩ := hy
      exact (mem_regularZeroSet_exponentialGraphLift_iff
        (hF x) (hg x)).mp hx
  · exact (exponentialGraphLift_injective g).injOn

end AbelFormalization
