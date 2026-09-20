import AbelFormalization.Inverse
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Quantitative calculus for a fixed iterate of `exp x - 1`

Scratch lemmas for the bounded-shift argument.  The derivative of an
iterate is written as the product along its orbit, which gives the lower
derivative and secant estimates used to locate and bound the shift.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

private theorem differentiable_E : Differentiable ℝ E := by
  intro x
  exact ((Real.hasDerivAt_exp x).sub_const 1).differentiableAt

/-- The derivative of `E^[d]` is the product of the derivatives of `E`
along the first `d` points of the orbit. -/
theorem hasDerivAt_E_iterate (d : ℕ) (x : ℝ) :
    HasDerivAt (E^[d])
      (Finset.prod (Finset.range d) fun k => Real.exp (E^[k] x)) x := by
  induction d with
  | zero =>
      simpa using hasDerivAt_id x
  | succ d ih =>
      have hE : HasDerivAt E (Real.exp (E^[d] x)) (E^[d] x) := by
        change HasDerivAt (fun y : ℝ => Real.exp y - 1)
          (Real.exp (E^[d] x)) (E^[d] x)
        exact (Real.hasDerivAt_exp (E^[d] x)).sub_const 1
      simpa only [Function.iterate_succ', Finset.prod_range_succ, mul_comm] using
        hE.comp x ih

/-- Formula for the derivative of a fixed iterate of `E`. -/
theorem deriv_E_iterate (d : ℕ) (x : ℝ) :
    deriv (E^[d]) x =
      Finset.prod (Finset.range d) fun k => Real.exp (E^[k] x) :=
  (hasDerivAt_E_iterate d x).deriv

/-- On the positive half-line, the derivative of every positive iterate of
`E` is at least the derivative of its first factor. -/
theorem exp_le_deriv_E_iterate {d : ℕ} (hd : 1 ≤ d)
    {x : ℝ} (hx : 0 < x) :
    Real.exp x ≤ deriv (E^[d]) x := by
  rw [deriv_E_iterate]
  have hfactor : ∀ k ∈ Finset.range d,
      1 ≤ Real.exp (E^[k] x) := by
    intro k _
    simpa only [Real.exp_zero] using
      Real.exp_strictMono.monotone (E_iterate_pos hx k).le
  have hzero : 0 ∈ Finset.range d :=
    Finset.mem_range.mpr (by omega)
  have hrest : 1 ≤ Finset.prod ((Finset.range d).erase 0)
      (fun k => Real.exp (E^[k] x)) :=
    Finset.one_le_prod₀ fun k hk =>
      hfactor k (Finset.mem_of_mem_erase hk)
  calc
    Real.exp x = Real.exp (E^[0] x) * 1 := by simp
    _ ≤ Real.exp (E^[0] x) *
        Finset.prod ((Finset.range d).erase 0)
          (fun k => Real.exp (E^[k] x)) :=
      mul_le_mul_of_nonneg_left hrest (Real.exp_pos _).le
    _ = Finset.prod (Finset.range d)
        (fun k => Real.exp (E^[k] x)) :=
      Finset.mul_prod_erase (Finset.range d)
        (fun k : ℕ => Real.exp (E^[k] x)) hzero

/-- A quantitative secant estimate for a positive iterate of `E`.
If the whole interval starts to the right of a positive point `a`, then
`E^[d]` expands its length by at least `exp a`. -/
theorem E_iterate_secant_lower {d : ℕ} (hd : 1 ≤ d)
    {a x y : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxy : x ≤ y) :
    Real.exp a * (y - x) ≤ E^[d] y - E^[d] x := by
  have hG : Differentiable ℝ (E^[d]) := differentiable_E.iterate d
  exact (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv
    hG.continuous.continuousOn hG.differentiableOn
    (fun z hz => by
      rw [interior_Icc] at hz
      have haz : a ≤ z := hax.trans hz.1.le
      exact (Real.exp_strictMono.monotone haz).trans
        (exp_le_deriv_E_iterate hd (ha.trans_le haz)))
    x (left_mem_Icc.mpr hxy) y (right_mem_Icc.mpr hxy) hxy

/-! ## The bounded shift -/

/-- Iterating the one-sided inverse identity `E (L x) = x` is valid as
long as the initial argument is positive. -/
theorem E_iterate_L_iterate {x : ℝ} (hx : 0 < x) (d : ℕ) :
    E^[d] (L^[d] x) = x := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [Function.iterate_succ_apply (f := E),
        Function.iterate_succ_apply' (f := L),
        E_L (L_iterate_pos hx d), ih]

/-- The explicit shift obtained by applying the inverse iterate. -/
def fixedIterateShift (d : ℕ) (v c : ℝ) : ℝ :=
  L^[d] (E^[d] v + c) - v

/-- The intermediate-value and mean-value part of the bounded-shift
argument, before identifying the witness with `fixedIterateShift`. -/
theorem exists_bounded_E_iterate_shift {d : ℕ} (hd : 1 ≤ d)
    {B v c : ℝ} (hB : 0 ≤ B) (hc : |c| ≤ B) (hv : B + 2 < v) :
    ∃ ξ : ℝ, ξ ∈ Ioo (-1) 1 ∧
      E^[d] (v + ξ) - E^[d] v = c ∧
      |ξ| ≤ B * Real.exp (1 - v) := by
  have hv1 : 0 < v - 1 := by linarith
  have hCB : B < Real.exp (v - 1) := by
    calc
      B < v := by linarith
      _ = (v - 1) + 1 := by ring
      _ < Real.exp (v - 1) := Real.add_one_lt_exp (ne_of_gt hv1)
  have hcLower : -B ≤ c := neg_le_of_abs_le hc
  have hcUpper : c ≤ B := le_of_abs_le hc
  have hleftSecant := E_iterate_secant_lower hd hv1
    (show v - 1 ≤ v - 1 from le_rfl)
    (show v - 1 ≤ v by linarith)
  have hrightSecant := E_iterate_secant_lower hd hv1
    (show v - 1 ≤ v by linarith)
    (show v ≤ v + 1 by linarith)
  have hleft : B < E^[d] v - E^[d] (v - 1) := by
    nlinarith
  have hright : B < E^[d] (v + 1) - E^[d] v := by
    nlinarith
  let F : ℝ → ℝ := fun ξ ↦ E^[d] (v + ξ) - E^[d] v - c
  have hFcont : Continuous F := by
    have hfirst : Continuous (fun ξ : ℝ ↦ E^[d] (v + ξ)) :=
      (E_continuous.iterate d).comp (continuous_const.add continuous_id)
    have hsecond : Continuous (fun _ : ℝ ↦ E^[d] v) := continuous_const
    exact (hfirst.sub hsecond).sub continuous_const
  have hFneg : F (-1) < 0 := by
    dsimp [F]
    rw [show v + (-1 : ℝ) = v - 1 by ring]
    linarith
  have hFpos : 0 < F 1 := by
    dsimp [F]
    linarith
  obtain ⟨ξ, hξ, hFξ⟩ :=
    intermediate_value_Ioo (f := F) (by norm_num : (-1 : ℝ) ≤ 1)
      hFcont.continuousOn ⟨hFneg, hFpos⟩
  have hEq : E^[d] (v + ξ) - E^[d] v = c := by
    dsimp [F] at hFξ
    linarith
  have hmul : Real.exp (v - 1) * |ξ| ≤ B := by
    by_cases hξnonneg : 0 ≤ ξ
    · rw [abs_of_nonneg hξnonneg]
      have hsecant := E_iterate_secant_lower hd hv1
        (show v - 1 ≤ v by linarith)
        (show v ≤ v + ξ by linarith)
      nlinarith
    · have hξnonpos : ξ ≤ 0 := le_of_not_ge hξnonneg
      rw [abs_of_nonpos hξnonpos]
      have hsecant := E_iterate_secant_lower hd hv1
        (show v - 1 ≤ v + ξ by linarith [hξ.1])
        (show v + ξ ≤ v by linarith)
      nlinarith
  have hdiv : |ξ| ≤ B / Real.exp (v - 1) :=
    (le_div_iff₀ (Real.exp_pos (v - 1))).2 (by
      simpa only [mul_comm] using hmul)
  have hbound : |ξ| ≤ B * Real.exp (1 - v) := by
    calc
      |ξ| ≤ B / Real.exp (v - 1) := hdiv
      _ = B * (Real.exp (v - 1))⁻¹ := div_eq_mul_inv _ _
      _ = B * Real.exp (-(v - 1)) := by rw [Real.exp_neg]
      _ = B * Real.exp (1 - v) := by
        congr 2
        ring
  exact ⟨ξ, hξ, hEq, hbound⟩

/-- Quantitative specification of the explicit fixed-iterate shift.  The
last clause states uniqueness among all real shifts, stronger than uniqueness
in `(-1, 1)`. -/
theorem fixedIterateShift_spec {d : ℕ} (hd : 1 ≤ d)
    {B v c : ℝ} (hB : 0 ≤ B) (hc : |c| ≤ B) (hv : B + 2 < v) :
    fixedIterateShift d v c ∈ Ioo (-1) 1 ∧
      E^[d] (v + fixedIterateShift d v c) - E^[d] v = c ∧
      |fixedIterateShift d v c| ≤ B * Real.exp (1 - v) ∧
      0 < deriv (E^[d]) (v + fixedIterateShift d v c) ∧
      ∀ ξ : ℝ, E^[d] (v + ξ) - E^[d] v = c →
        ξ = fixedIterateShift d v c := by
  obtain ⟨ξ, hξ, hEq, hbound⟩ :=
    exists_bounded_E_iterate_shift hd hB hc hv
  have hvξ : 0 < v + ξ := by linarith [hξ.1]
  have hyEq : E^[d] v + c = E^[d] (v + ξ) := by linarith
  have hyPos : 0 < E^[d] v + c := by
    rw [hyEq]
    exact E_iterate_pos hvξ d
  have hshiftEq :
      E^[d] (v + fixedIterateShift d v c) - E^[d] v = c := by
    unfold fixedIterateShift
    rw [show v + (L^[d] (E^[d] v + c) - v) =
      L^[d] (E^[d] v + c) by ring]
    rw [E_iterate_L_iterate hyPos d]
    ring
  have hshift : fixedIterateShift d v c = ξ := by
    have himage :
        E^[d] (v + fixedIterateShift d v c) = E^[d] (v + ξ) := by
      linarith
    have harg := (E_strictMono.iterate d).injective himage
    linarith
  have hvshift : 0 < v + fixedIterateShift d v c := by
    rw [hshift]
    exact hvξ
  refine ⟨?_, hshiftEq, ?_, ?_, ?_⟩
  · simpa only [hshift] using hξ
  · simpa only [hshift] using hbound
  · exact (Real.exp_pos (v + fixedIterateShift d v c)).trans_le
      (exp_le_deriv_E_iterate hd hvshift)
  · intro ζ hζ
    have himage :
        E^[d] (v + ζ) = E^[d] (v + fixedIterateShift d v c) := by
      linarith
    have harg := (E_strictMono.iterate d).injective himage
    linarith

end AbelFormalization
