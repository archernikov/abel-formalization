import AbelFormalization.WeightedSeriesAnalytic
import AbelFormalization.WeightedSeriesRestriction
import AbelFormalization.AnalyticWeightedRepresentation
import AbelFormalization.AnalyticGermDerivation

/-! # Convergent coefficient series as actual analytic germs

Evaluation sends each weighted coefficient algebra to the actual neighborhood
germ algebra. Every analytic germ is represented at some positive radius.
-/

noncomputable section

open Filter
open scoped Topology

namespace AbelFormalization

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Finitely many positive radii have a common positive lower bound. -/
theorem exists_pos_le_polyradius (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, r ≤ ρ i := by
  suffices ∀ s : Finset σ, ∃ r : ℝ, 0 < r ∧ ∀ i ∈ s, r ≤ ρ i by
    simpa using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨r, hr, hs⟩ := ih
    refine ⟨min r (ρ a), lt_min hr (hρ a), ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hs i hi)

/-- A positive polydisc contains a neighborhood of the origin. -/
theorem eventually_abs_le_polyradius (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) :
    ∀ᶠ x : σ → ℝ in 𝓝 0, ∀ i, |x i| ≤ ρ i := by
  obtain ⟨r, hr, hbound⟩ := exists_pos_le_polyradius ρ hρ
  filter_upwards [Metric.ball_mem_nhds (0 : σ → ℝ) hr] with x hx
  intro i
  exact (norm_le_pi_norm x i).trans
    ((show ‖x‖ < r from by simpa only [Metric.mem_ball, dist_zero_right] using hx).le.trans
      (hbound i))

/-- Evaluation is analytic for arbitrary finite positive polyradii. -/
theorem analyticAt_weightedSeriesEval_polyradius (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    {f : MvPowerSeries σ ℝ} (hf : WeightedCoeffSummable ρ f) :
    AnalyticAt ℝ (weightedSeriesEval f) 0 := by
  obtain ⟨r, hr, hbound⟩ := exists_pos_le_polyradius ρ hρ
  exact analyticAt_weightedSeriesEval hr
    (weightedCoeffSummable_of_radius_le (fun _ => hr.le) hbound hf)

/-- The actual analytic germ defined by a convergent coefficient series. -/
def weightedSeriesGerm (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (f : WeightedSeries ρ hρ) : AnalyticGermAt (0 : σ → ℝ) :=
  analyticGermOf (weightedSeriesEval f.val)
    (analyticAt_weightedSeriesEval_polyradius ρ hρ f.property)

/-- Evaluation into neighborhood germs preserves the real algebra operations. -/
def weightedSeriesGermAlgHom (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i) :
    WeightedSeries ρ hρ →ₐ[ℝ] AnalyticGermAt (0 : σ → ℝ) where
  toFun := weightedSeriesGerm ρ hρ
  map_zero' := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (weightedSeriesEval_zero (σ := σ))
  map_one' := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (weightedSeriesEval_one (σ := σ))
  map_add' f g := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [eventually_abs_le_polyradius ρ hρ] with x hx
    exact weightedSeriesEval_add hx f.property g.property
  map_mul' f g := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    filter_upwards [eventually_abs_le_polyradius ρ hρ] with x hx
    exact weightedSeriesEval_mul hx f.property g.property
  commutes' c := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (weightedSeriesEval_C c)

@[simp]
theorem weightedSeriesGermAlgHom_apply (ρ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (f : WeightedSeries ρ hρ) :
    weightedSeriesGermAlgHom ρ hρ f = weightedSeriesGerm ρ hρ f := rfl

/-- Shrinking radii does not change the resulting actual analytic germ. -/
theorem weightedSeriesGerm_restrict (ρ τ : σ → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hτ : ∀ i, 0 < τ i) (hτρ : ∀ i, τ i ≤ ρ i) (f : WeightedSeries ρ hρ) :
    weightedSeriesGerm τ hτ (weightedSeriesRestrictAlgHom ρ τ hρ hτ hτρ f) =
      weightedSeriesGerm ρ hρ f := by
  apply (analyticGermOf_eq_iff _ _).mpr
  exact Eventually.of_forall (fun x => by rw [weightedSeriesRestrictAlgHom_val])

/-- Every actual analytic germ comes from a weighted coefficient algebra at
some positive radius; no convergence hypothesis is added to the germ. -/
theorem exists_weightedSeriesGerm_representation (g : AnalyticGermAt (0 : σ → ℝ)) :
    ∃ (r : ℝ) (hr : 0 < r), ∃ S : WeightedSeries (fun _ : σ => r) (fun _ => hr),
      weightedSeriesGerm (fun _ => r) (fun _ => hr) S = g := by
  obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative g
  obtain ⟨r, hr, S, hS⟩ := analyticAt_exists_weightedSeries_representation hf
  refine ⟨r, hr, S, ?_⟩
  exact (analyticGermOf_eq_iff _ _).mpr hS

end AbelFormalization
