import AbelFormalization.ImplicitRegularZeroGraphLift
import AbelFormalization.RestrictedFixedIterateShift

/-!
# Graph equation for a fixed-iterate bounded shift

The shift supplied by `restrictedFixedIterateShift` is represented by the
allowed equation
`E^[d] (v + eta) - E^[d] v - b(w) = 0`.
Its vertical derivative is positive, so adjoining this equation preserves
regular-zero membership.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The implicit graph equation defining one fixed-iterate shift variable. -/
def restrictedFixedIterateShiftGraphEquation {p : ℕ} (d : ℕ)
    (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    ((ℝ × RestrictedBoxSpace p) × ℝ) → ℝ :=
  fun q ↦ E^[d] (q.1.1 + q.2) - E^[d] q.1.1 -
    (b : RestrictedBoxSpace p → ℝ) q.1.2

@[simp]
theorem restrictedFixedIterateShiftGraphEquation_on_shift
    {p d : ℕ} (hd : 1 ≤ d) (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {B v : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ D.closedBox,
      |(b : RestrictedBoxSpace p → ℝ) w| ≤ B)
    (hv : B + 2 < v) {w : RestrictedBoxSpace p} (hw : w ∈ D.openBox) :
    restrictedFixedIterateShiftGraphEquation d D b
      ((v, w), restrictedFixedIterateShift d D b (v, w)) = 0 := by
  have hspec := restrictedFixedIterateShift_spec hd D b hB hbB hv hw
  simp only [restrictedFixedIterateShiftGraphEquation]
  linarith [hspec.2.1]

/-- The fixed-iterate graph identity holds on a whole neighborhood of each
point in its tail domain. -/
theorem eventuallyEq_restrictedFixedIterateShiftGraphEquation
    {p d : ℕ} (hd : 1 ≤ d) (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {B v : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ D.closedBox,
      |(b : RestrictedBoxSpace p → ℝ) w| ≤ B)
    (hv : B + 2 < v) {w : RestrictedBoxSpace p} (hw : w ∈ D.openBox) :
    (fun q : ℝ × RestrictedBoxSpace p ↦
      restrictedFixedIterateShiftGraphEquation d D b
        (q, restrictedFixedIterateShift d D b q)) =ᶠ[nhds (v, w)]
      (fun _ ↦ (0 : ℝ)) := by
  have hopen : IsOpen (Ioi (B + 2) ×ˢ D.openBox) :=
    isOpen_Ioi.prod D.isOpen_openBox
  filter_upwards [hopen.mem_nhds ⟨hv, hw⟩] with q hq
  exact restrictedFixedIterateShiftGraphEquation_on_shift
    hd D b hB hbB hq.1 hq.2

/-- The fixed-iterate shift is differentiable on its quantitative tail. -/
theorem differentiableAt_restrictedFixedIterateShift
    {p d : ℕ} (hd : 1 ≤ d) (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {B v : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ D.closedBox,
      |(b : RestrictedBoxSpace p → ℝ) w| ≤ B)
    (hv : B + 2 < v) {w : RestrictedBoxSpace p} (hw : w ∈ D.openBox) :
    DifferentiableAt ℝ (restrictedFixedIterateShift d D b) (v, w) := by
  have hopen : IsOpen (Ioi (B + 2) ×ˢ D.openBox) :=
    isOpen_Ioi.prod D.isOpen_openBox
  exact ((contDiffOn_restrictedFixedIterateShift hd D b hB hbB).contDiffAt
    (hopen.mem_nhds
      (show (v, w) ∈ Ioi (B + 2) ×ˢ D.openBox from ⟨hv, hw⟩))).differentiableAt
        (by simp)

/-- The allowed graph equation is differentiable wherever the bounded
coefficient is analytic. -/
theorem differentiableAt_restrictedFixedIterateShiftGraphEquation
    {p d : ℕ} (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {v eta : ℝ} {w : RestrictedBoxSpace p} (hw : w ∈ D.openBox) :
    DifferentiableAt ℝ (restrictedFixedIterateShiftGraphEquation d D b)
      ((v, w), eta) := by
  have hbNhd : AnalyticOnNhd ℝ
      (b : RestrictedBoxSpace p → ℝ) D.closedBox :=
    D.analyticNearClosedBox_iff.mp b.property
  have hb : DifferentiableAt ℝ
      (b : RestrictedBoxSpace p → ℝ) w :=
    (hbNhd w (D.openBox_subset_closedBox hw)).differentiableAt
  have hE : Differentiable ℝ (E^[d]) := fun x ↦
    (hasDerivAt_E_iterate d x).differentiableAt
  unfold restrictedFixedIterateShiftGraphEquation
  fun_prop

/-- The vertical derivative of the graph equation, evaluated at `1`, is the
positive derivative of the fixed iterate. -/
theorem restrictedFixedIterateShiftGraphEquation_vertical_one
    {p d : ℕ} (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {v eta : ℝ} {w : RestrictedBoxSpace p} (hw : w ∈ D.openBox) :
    graphLiftZBlock
        (fderiv ℝ (restrictedFixedIterateShiftGraphEquation d D b)
          ((v, w), eta)) 1 =
      deriv (E^[d]) (v + eta) := by
  have hh := differentiableAt_restrictedFixedIterateShiftGraphEquation
    (d := d) D b (v := v) (eta := eta) hw
  have hins : HasDerivAt (fun z : ℝ ↦ ((v, w), z)) ((0, 0), 1) eta :=
    (hasDerivAt_const eta (v, w)).prodMk (hasDerivAt_id eta)
  have hfrom := hh.hasFDerivAt.comp_hasDerivAt eta hins
  change HasDerivAt
    (fun z : ℝ ↦ restrictedFixedIterateShiftGraphEquation d D b
      ((v, w), z))
    (graphLiftZBlock
      (fderiv ℝ (restrictedFixedIterateShiftGraphEquation d D b)
        ((v, w), eta)) 1) eta at hfrom
  have hsum : HasDerivAt (fun z : ℝ ↦ v + z) 1 eta :=
    (hasDerivAt_id eta).const_add v
  have hcurve : HasDerivAt
      (fun z : ℝ ↦ restrictedFixedIterateShiftGraphEquation d D b
        ((v, w), z))
      (deriv (E^[d]) (v + eta)) eta := by
    have hmain :=
      ((hasDerivAt_E_iterate d (v + eta)).differentiableAt.hasDerivAt).comp
        eta hsum
    simpa only [restrictedFixedIterateShiftGraphEquation,
      Function.comp_apply,
      zero_add, mul_one] using
      (hmain.sub_const (E^[d] v)).sub_const
        ((b : RestrictedBoxSpace p → ℝ) w)
  exact hfrom.unique hcurve

/-- The vertical derivative block of the fixed-iterate graph equation is
surjective. -/
theorem surjective_graphLiftZBlock_restrictedFixedIterateShiftGraphEquation
    {p d : ℕ} (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {v eta : ℝ} {w : RestrictedBoxSpace p} (hw : w ∈ D.openBox) :
    Function.Surjective
      (graphLiftZBlock
        (fderiv ℝ (restrictedFixedIterateShiftGraphEquation d D b)
          ((v, w), eta))) := by
  let V : ℝ →L[ℝ] ℝ := graphLiftZBlock
    (fderiv ℝ (restrictedFixedIterateShiftGraphEquation d D b)
      ((v, w), eta))
  let c : ℝ := deriv (E^[d]) (v + eta)
  have hc : 0 < c := by
    dsimp only [c]
    rw [deriv_E_iterate]
    exact Finset.prod_pos fun k _ ↦ Real.exp_pos (E^[k] (v + eta))
  have hVone : V 1 = c := by
    exact restrictedFixedIterateShiftGraphEquation_vertical_one D b hw
  intro y
  refine ⟨y / c, ?_⟩
  calc
    V (y / c) = V ((y / c) • (1 : ℝ)) := by simp
    _ = (y / c) • V 1 := map_smul V _ _
    _ = y := by
      rw [hVone]
      simpa [smul_eq_mul] using div_mul_cancel₀ y hc.ne'

/-- Adjoining the allowed fixed-iterate graph equation preserves a regular
zero at every point of the quantitative tail. -/
theorem mem_regularZeroSet_restrictedFixedIterateShiftGraphLift_iff
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {p d : ℕ} (hd : 1 ≤ d) (D : RestrictedBox p)
    (b : RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {B v : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ D.closedBox,
      |(b : RestrictedBoxSpace p → ℝ) w| ≤ B)
    (hv : B + 2 < v) {w : RestrictedBoxSpace p} (hw : w ∈ D.openBox)
    {Omega : Set (ℝ × RestrictedBoxSpace p)}
    {Ftilde : ((ℝ × RestrictedBoxSpace p) × ℝ) → Y}
    (hF : DifferentiableAt ℝ Ftilde
      ((v, w), restrictedFixedIterateShift d D b (v, w))) :
    (v, w) ∈ regularZeroSet Omega
        (graphSubstitution Ftilde (restrictedFixedIterateShift d D b)) ↔
      ((v, w), restrictedFixedIterateShift d D b (v, w)) ∈
        regularZeroSet
          ((fun q : (ℝ × RestrictedBoxSpace p) × ℝ ↦ q.1) ⁻¹' Omega)
          (implicitGraphLiftSystem Ftilde
            (restrictedFixedIterateShiftGraphEquation d D b)) := by
  apply mem_regularZeroSet_implicitGraphLift_iff hF
    (differentiableAt_restrictedFixedIterateShiftGraphEquation D b hw)
    (differentiableAt_restrictedFixedIterateShift hd D b hB hbB hv hw)
    (eventuallyEq_restrictedFixedIterateShiftGraphEquation
      hd D b hB hbB hv hw)
  exact surjective_graphLiftZBlock_restrictedFixedIterateShiftGraphEquation
    D b hw

end AbelFormalization
