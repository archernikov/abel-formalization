import AbelFormalization.FixedIterateShift
import AbelFormalization.RestrictedExpressionTower

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- Apply the scalar fixed-iterate shift to an analytic bounded-coordinate
coefficient. -/
def restrictedFixedIterateShift {p : ℕ} (d : ℕ) (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    ℝ × RestrictedBoxSpace p → ℝ :=
  fun q => fixedIterateShift d q.1
    ((b : RestrictedBoxSpace p → ℝ) q.2)

/-- Pointwise quantitative properties of the restricted-box shift, assuming
an explicit uniform bound for the coefficient on the closed box. -/
theorem restrictedFixedIterateShift_spec {p d : ℕ} (hd : 1 ≤ d)
    (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {B v : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ D.closedBox,
      |(b : RestrictedBoxSpace p → ℝ) w| ≤ B)
    (hv : B + 2 < v) {w : RestrictedBoxSpace p} (hw : w ∈ D.openBox) :
    restrictedFixedIterateShift d D b (v, w) ∈ Ioo (-1) 1 ∧
      E^[d] (v + restrictedFixedIterateShift d D b (v, w)) - E^[d] v =
        (b : RestrictedBoxSpace p → ℝ) w ∧
      |restrictedFixedIterateShift d D b (v, w)| ≤
        B * Real.exp (1 - v) ∧
      0 < deriv (E^[d])
        (v + restrictedFixedIterateShift d D b (v, w)) ∧
      ∀ ξ : ℝ, E^[d] (v + ξ) - E^[d] v =
          (b : RestrictedBoxSpace p → ℝ) w →
        ξ = restrictedFixedIterateShift d D b (v, w) := by
  exact fixedIterateShift_spec hd hB
    (hbB w (D.openBox_subset_closedBox hw)) hv

/-- Smoothness of the restricted-box family on the same quantitative tail
where the scalar specification holds. -/
theorem contDiffOn_restrictedFixedIterateShift {p d : ℕ} (hd : 1 ≤ d)
    (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ D.closedBox,
      |(b : RestrictedBoxSpace p → ℝ) w| ≤ B) :
    ContDiffOn ℝ ∞ (restrictedFixedIterateShift d D b)
      (Ioi (B + 2) ×ˢ D.openBox) := by
  intro q hq
  have hspec := restrictedFixedIterateShift_spec hd D b hB hbB hq.1 hq.2
  have hvshift : 0 < q.1 + restrictedFixedIterateShift d D b q := by
    have heta : -1 < restrictedFixedIterateShift d D b q := by
      simpa using hspec.1.1
    have hv : B + 2 < q.1 := hq.1
    linarith
  have hargEq : E^[d] q.1 + (b : RestrictedBoxSpace p → ℝ) q.2 =
      E^[d] (q.1 + restrictedFixedIterateShift d D b q) := by
    linarith [hspec.2.1]
  have harg : 0 < E^[d] q.1 + (b : RestrictedBoxSpace p → ℝ) q.2 := by
    rw [hargEq]
    exact E_iterate_pos hvshift d
  have hbNhd : AnalyticOnNhd ℝ
      (b : RestrictedBoxSpace p → ℝ) D.closedBox :=
    D.analyticNearClosedBox_iff.mp b.property
  have hbAt : AnalyticAt ℝ (b : RestrictedBoxSpace p → ℝ) q.2 :=
    hbNhd q.2 (D.openBox_subset_closedBox hq.2)
  have hcoeff : ContDiffAt ℝ ∞
      (fun z : ℝ × RestrictedBoxSpace p =>
        (b : RestrictedBoxSpace p → ℝ) z.2) q := by
    change ContDiffAt ℝ ∞
      ((b : RestrictedBoxSpace p → ℝ) ∘ Prod.snd) q
    exact hbAt.contDiffAt.comp q contDiffAt_snd
  have hparameters : ContDiffAt ℝ ∞
      (fun z : ℝ × RestrictedBoxSpace p =>
        (z.1, (b : RestrictedBoxSpace p → ℝ) z.2)) q :=
    contDiffAt_fst.prodMk hcoeff
  have hsmooth := (contDiffAt_fixedIterateShift d harg).comp q hparameters
  change ContDiffWithinAt ℝ ∞
    (fun z : ℝ × RestrictedBoxSpace p =>
      fixedIterateShift d z.1 ((b : RestrictedBoxSpace p → ℝ) z.2))
    (Ioi (B + 2) ×ˢ D.openBox) q
  exact hsmooth.contDiffWithinAt

/-- Manuscript-style bounded-shift data for an analytic coefficient on a
bounded box.  The witnesses are chosen from an attained maximum of `|b|`,
and `V0` is the concrete value `B + 2`. -/
theorem exists_restrictedFixedIterateShift_data {p d : ℕ} (hd : 1 ≤ d)
    (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    ∃ B V0 : ℝ,
      0 ≤ B ∧ 1 < V0 ∧ V0 = B + 2 ∧
      (∀ w ∈ D.closedBox,
        |(b : RestrictedBoxSpace p → ℝ) w| ≤ B) ∧
      ContDiffOn ℝ ∞ (restrictedFixedIterateShift d D b)
        (Ioi V0 ×ˢ D.openBox) ∧
      ∀ v > V0, ∀ w ∈ D.openBox,
        restrictedFixedIterateShift d D b (v, w) ∈ Ioo (-1) 1 ∧
        E^[d] (v + restrictedFixedIterateShift d D b (v, w)) - E^[d] v =
          (b : RestrictedBoxSpace p → ℝ) w ∧
        |restrictedFixedIterateShift d D b (v, w)| ≤
          B * Real.exp (1 - v) ∧
        0 < deriv (E^[d])
          (v + restrictedFixedIterateShift d D b (v, w)) ∧
        ∀ ξ : ℝ, E^[d] (v + ξ) - E^[d] v =
            (b : RestrictedBoxSpace p → ℝ) w →
          ξ = restrictedFixedIterateShift d D b (v, w) := by
  have hbNhd : AnalyticOnNhd ℝ
      (b : RestrictedBoxSpace p → ℝ) D.closedBox :=
    D.analyticNearClosedBox_iff.mp b.property
  have hbAbsContinuous : ContinuousOn
      (fun w : RestrictedBoxSpace p => |(b : RestrictedBoxSpace p → ℝ) w|)
      D.closedBox := hbNhd.continuousOn.abs
  obtain ⟨w0, hw0, hmax⟩ :=
    D.isCompact_closedBox.exists_isMaxOn D.closedBox_nonempty hbAbsContinuous
  let B : ℝ := |(b : RestrictedBoxSpace p → ℝ) w0|
  have hB : 0 ≤ B := abs_nonneg _
  have hbB : ∀ w ∈ D.closedBox,
      |(b : RestrictedBoxSpace p → ℝ) w| ≤ B := by
    intro w hw
    exact isMaxOn_iff.mp hmax w hw
  refine ⟨B, B + 2, hB, by linarith, rfl, hbB, ?_, ?_⟩
  · exact contDiffOn_restrictedFixedIterateShift hd D b hB hbB
  · intro v hv w hw
    exact restrictedFixedIterateShift_spec hd D b hB hbB hv hw

end AbelFormalization
