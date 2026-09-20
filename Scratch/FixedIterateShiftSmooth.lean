import AbelFormalization.FixedIterateShift
import AbelFormalization.RestrictedExpressionTower
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Smoothness of the fixed-iterate shift

The explicit logarithmic formula makes the global shift smooth wherever
its argument before the logarithmic iterates is positive.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

private theorem contDiff_E : ContDiff ℝ ∞ E := by
  change ContDiff ℝ ∞ (fun x : ℝ => Real.exp x - 1)
  exact Real.contDiff_exp.sub contDiff_const

/-- Every fixed iterate of `E` is smooth on the real line. -/
theorem contDiff_E_iterate (d : ℕ) : ContDiff ℝ ∞ (E^[d]) := by
  induction d with
  | zero =>
      simpa only [Function.iterate_zero] using
        (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ))
  | succ d ih =>
      rw [Function.iterate_succ']
      exact contDiff_E.comp ih

private theorem contDiffAt_L {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ ∞ L x := by
  change ContDiffAt ℝ ∞ (fun y : ℝ => Real.log (1 + y)) x
  have hadd : ContDiffAt ℝ ∞ (fun y : ℝ => 1 + y) x :=
    contDiffAt_const.add contDiffAt_id
  change ContDiffAt ℝ ∞ (Real.log ∘ fun y : ℝ => 1 + y) x
  exact (Real.contDiffAt_log.2 (by linarith : 1 + x ≠ 0)).comp x hadd

/-- A fixed logarithmic iterate is smooth at every positive argument. -/
theorem contDiffAt_L_iterate {x : ℝ} (hx : 0 < x) (d : ℕ) :
    ContDiffAt ℝ ∞ (L^[d]) x := by
  induction d with
  | zero =>
      simpa only [Function.iterate_zero] using
        (contDiffAt_id : ContDiffAt ℝ ∞ (id : ℝ → ℝ) x)
  | succ d ih =>
      rw [Function.iterate_succ']
      exact (contDiffAt_L (L_iterate_pos hx d)).comp x ih

/-- The fixed-iterate shift is smooth in its unbounded coordinate and its
scalar displacement whenever the input to the inverse iterate is positive. -/
theorem contDiffAt_fixedIterateShift (d : ℕ) {v c : ℝ}
    (harg : 0 < E^[d] v + c) :
    ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => fixedIterateShift d q.1 q.2) (v, c) := by
  have hfirst : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => E^[d] q.1) (v, c) := by
    change ContDiffAt ℝ ∞ ((E^[d]) ∘ Prod.fst) (v, c)
    exact (contDiff_E_iterate d).contDiffAt.comp (v, c) contDiffAt_fst
  have hinner : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => E^[d] q.1 + q.2) (v, c) :=
    hfirst.add contDiffAt_snd
  have hreturned : ContDiffAt ℝ ∞
      (fun q : ℝ × ℝ => L^[d] (E^[d] q.1 + q.2)) (v, c) := by
    change ContDiffAt ℝ ∞
      ((L^[d]) ∘ fun q : ℝ × ℝ => E^[d] q.1 + q.2) (v, c)
    exact (contDiffAt_L_iterate harg d).comp (v, c) hinner
  change ContDiffAt ℝ ∞
    (fun q : ℝ × ℝ => L^[d] (E^[d] q.1 + q.2) - q.1) (v, c)
  exact hreturned.sub contDiffAt_fst

/-! ## A restricted-box family -/

/-- Apply the scalar fixed-iterate shift to an analytic bounded-coordinate
coefficient. -/
def restrictedFixedIterateShift {p : ℕ} (d : ℕ) (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    ℝ × RestrictedBoxSpace p → ℝ :=
  fun q => fixedIterateShift d q.1 (b q.2)

/-- Pointwise quantitative properties of the restricted-box shift, assuming
an explicit uniform bound for the coefficient on the closed box. -/
theorem restrictedFixedIterateShift_spec {p d : ℕ} (hd : 1 ≤ d)
    (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {B v : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ D.closedBox, |b w| ≤ B)
    (hv : B + 2 < v) {w : RestrictedBoxSpace p} (hw : w ∈ D.openBox) :
    restrictedFixedIterateShift d D b (v, w) ∈ Ioo (-1) 1 ∧
      E^[d] (v + restrictedFixedIterateShift d D b (v, w)) - E^[d] v = b w ∧
      |restrictedFixedIterateShift d D b (v, w)| ≤ B * Real.exp (1 - v) ∧
      0 < deriv (E^[d]) (v + restrictedFixedIterateShift d D b (v, w)) ∧
      ∀ ξ : ℝ, E^[d] (v + ξ) - E^[d] v = b w →
        ξ = restrictedFixedIterateShift d D b (v, w) := by
  simpa only [restrictedFixedIterateShift] using
    fixedIterateShift_spec hd hB
      (hbB w (D.openBox_subset_closedBox hw)) hv

/-- Smoothness of the restricted-box family on the same quantitative tail
where the scalar specification holds. -/
theorem contDiffOn_restrictedFixedIterateShift {p d : ℕ} (hd : 1 ≤ d)
    (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ D.closedBox, |b w| ≤ B) :
    ContDiffOn ℝ ∞ (restrictedFixedIterateShift d D b)
      (Ioi (B + 2) ×ˢ D.openBox) := by
  intro q hq
  have hspec := restrictedFixedIterateShift_spec hd D b hB hbB hq.1 hq.2
  have hvshift : 0 < q.1 + restrictedFixedIterateShift d D b q := by
    have heta := hspec.1.1
    linarith
  have hargEq : E^[d] q.1 + b q.2 =
      E^[d] (q.1 + restrictedFixedIterateShift d D b q) := by
    linarith [hspec.2.1]
  have harg : 0 < E^[d] q.1 + b q.2 := by
    rw [hargEq]
    exact E_iterate_pos hvshift d
  have hbNhd : AnalyticOnNhd ℝ
      (b : RestrictedBoxSpace p → ℝ) D.closedBox :=
    D.analyticNearClosedBox_iff.mp b.property
  have hbAt : AnalyticAt ℝ (b : RestrictedBoxSpace p → ℝ) q.2 :=
    hbNhd q.2 (D.openBox_subset_closedBox hq.2)
  have hcoeff : ContDiffAt ℝ ∞
      (fun z : ℝ × RestrictedBoxSpace p => b z.2) q := by
    change ContDiffAt ℝ ∞
      ((b : RestrictedBoxSpace p → ℝ) ∘ Prod.snd) q
    exact hbAt.contDiffAt.comp q contDiffAt_snd
  have hparameters : ContDiffAt ℝ ∞
      (fun z : ℝ × RestrictedBoxSpace p => (z.1, b z.2)) q :=
    contDiffAt_fst.prodMk hcoeff
  have hsmooth := (contDiffAt_fixedIterateShift d harg).comp q hparameters
  change ContDiffAt ℝ ∞
    (fun z : ℝ × RestrictedBoxSpace p => fixedIterateShift d z.1 (b z.2)) q at hsmooth
  simpa only [restrictedFixedIterateShift] using hsmooth.contDiffWithinAt

/-- Manuscript-style bounded-shift data for an analytic coefficient on a
bounded box.  The witnesses are chosen from an attained maximum of `|b|`,
and `V0` is the concrete value `B + 2`. -/
theorem exists_restrictedFixedIterateShift_data {p d : ℕ} (hd : 1 ≤ d)
    (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    ∃ B V0 : ℝ,
      0 ≤ B ∧ 1 < V0 ∧ V0 = B + 2 ∧
      (∀ w ∈ D.closedBox, |b w| ≤ B) ∧
      ContDiffOn ℝ ∞ (restrictedFixedIterateShift d D b)
        (Ioi V0 ×ˢ D.openBox) ∧
      ∀ v > V0, ∀ w ∈ D.openBox,
        restrictedFixedIterateShift d D b (v, w) ∈ Ioo (-1) 1 ∧
        E^[d] (v + restrictedFixedIterateShift d D b (v, w)) - E^[d] v = b w ∧
        |restrictedFixedIterateShift d D b (v, w)| ≤ B * Real.exp (1 - v) ∧
        0 < deriv (E^[d]) (v + restrictedFixedIterateShift d D b (v, w)) ∧
        ∀ ξ : ℝ, E^[d] (v + ξ) - E^[d] v = b w →
          ξ = restrictedFixedIterateShift d D b (v, w) := by
  have hbNhd : AnalyticOnNhd ℝ
      (b : RestrictedBoxSpace p → ℝ) D.closedBox :=
    D.analyticNearClosedBox_iff.mp b.property
  have hbAbsContinuous : ContinuousOn
      (fun w : RestrictedBoxSpace p => |b w|) D.closedBox :=
    hbNhd.continuousOn.abs
  obtain ⟨w0, hw0, hmax⟩ :=
    D.isCompact_closedBox.exists_isMaxOn D.closedBox_nonempty hbAbsContinuous
  let B : ℝ := |b w0|
  have hB : 0 ≤ B := abs_nonneg _
  have hbB : ∀ w ∈ D.closedBox, |b w| ≤ B := by
    intro w hw
    exact isMaxOn_iff.mp hmax w hw
  refine ⟨B, B + 2, hB, by linarith, rfl, hbB, ?_, ?_⟩
  · exact contDiffOn_restrictedFixedIterateShift hd D b hB hbB
  · intro v hv w hw
    exact restrictedFixedIterateShift_spec hd D b hB hbB hv hw

end AbelFormalization
