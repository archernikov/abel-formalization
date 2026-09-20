import AbelFormalization.TransferFiniteBounds
import Mathlib.Analysis.Polynomial.Basic

/-!
# Eventual lower bounds for nonzero real polynomials

The terminal height argument produces a nonzero univariate real polynomial.
This file turns that algebraic certificate into the quantitative seed needed
by the backwards transfer argument.  The exponent is zero: along any input
tending to `+∞`, the absolute value of a nonzero polynomial is eventually
bounded below by one positive constant.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped Polynomial Topology

variable {X : Type*}

/-- A nonzero real polynomial evaluated along a function tending to `+∞` is
eventually bounded away from zero.  The constant-polynomial case is handled
separately from `Polynomial.abs_tendsto_atTop`. -/
theorem nonzeroPolynomial_exists_pos_eventually_le_abs_eval_comp
    (P : ℝ[X]) (hP : P ≠ 0) {l : Filter X} {u : X → ℝ}
    (hu : Tendsto u l atTop) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in l, c ≤ |P.eval (u x)| := by
  by_cases hdegree : P.natDegree = 0
  · have hcoeff : P.coeff 0 ≠ 0 := by
      intro hcoeff
      apply hP
      rw [P.eq_C_of_natDegree_eq_zero hdegree, hcoeff, Polynomial.C_0]
    refine ⟨|P.coeff 0|, abs_pos.mpr hcoeff, ?_⟩
    filter_upwards [] with x
    rw [P.eq_C_of_natDegree_eq_zero hdegree, Polynomial.eval_C]
    simp
  · have hdegreePos : 0 < P.degree :=
      Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdegree)
    refine ⟨1, zero_lt_one, ?_⟩
    exact (tendsto_atTop.1 ((P.abs_tendsto_atTop hdegreePos).comp hu)) 1

/-- Singleton-family form of the polynomial lower bound.  The scale is
arbitrary because the inverse-power exponent can be chosen to be zero. -/
theorem nonzeroPolynomial_hasInversePowerLowerBound
    (P : ℝ[X]) (hP : P ≠ 0) {l : Filter X} {u : X → ℝ}
    (hu : Tendsto u l atTop) (S : X → ℝ) :
    HasInversePowerLowerBound l S
      (fun _ : Fin 1 => fun x => P.eval (u x)) := by
  obtain ⟨c, hc, hbound⟩ :=
    nonzeroPolynomial_exists_pos_eventually_le_abs_eval_comp P hP hu
  refine ⟨c, hc, 0, ?_⟩
  filter_upwards [hbound] with x hx
  simpa only [pow_zero, div_one] using
    hx.trans (abs_le_finiteFamilyMaxAbs
      (fun _ : Fin 1 => fun x => P.eval (u x)) x 0)

end AbelFormalization
