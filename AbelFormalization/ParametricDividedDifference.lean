import AbelFormalization.ParametricCauchyRemainder
import AbelFormalization.AnalyticRemainder

/-!
# Joint holomorphy of the divided-difference remainder

The Cauchy-contour remainder equals the divided difference `dslope f 0` on
the full disk. Away from zero, the two exact remainder identities determine
the value. At zero, continuity extends the equality from a punctured
neighborhood. This transfers joint complex Fréchet differentiability to the
actual divided-difference function, including zero scale.
-/

noncomputable section

namespace AbelFormalization

open Set Metric Polynomial Filter
open scoped Topology

variable {E : Type*}

/-- The Cauchy representation and the divided difference agree throughout
the disk, including at the removable singularity. -/
theorem parameterCauchyRemainder_eq_analyticRemainder {f : E × ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) {p : E}
    (hf : AnalyticOnNhd ℂ (fun ζ => f (p, ζ)) (closedBall (0 : ℂ) ρ))
    {q : ℂ} (hq : q ∈ ball (0 : ℂ) ρ) :
    parameterCauchyRemainder f ρ p q = analyticRemainder (fun ζ => f (p, ζ)) q := by
  have hne : ∀ {z : ℂ}, z ∈ ball (0 : ℂ) ρ → z ≠ 0 →
      parameterCauchyRemainder f ρ p z = analyticRemainder (fun ζ => f (p, ζ)) z := by
    intro z hz hz0
    apply mul_left_cancel₀ hz0
    exact add_left_cancel ((parameterCauchyRemainder_identity hρ hf hz).symm.trans
      (analyticRemainder_identity (fun ζ => f (p, ζ)) z))
  by_cases hq0 : q = 0
  · subst q
    have hX : ∀ ζ ∈ sphere (0 : ℂ) ρ, (X : ℂ[X]).eval ζ ≠ 0 := by
      intro ζ hζ
      simp only [eval_X]
      intro he
      have hn : ‖ζ‖ = ρ := by simpa only [mem_sphere, dist_zero_right] using hζ
      rw [he, norm_zero] at hn
      exact hρ.ne' hn.symm
    have hc : AnalyticOnNhd ℂ (fun z => parameterCauchyRemainder f ρ p z)
        (ball (0 : ℂ) ρ) :=
      hermiteContourQuotient_analyticOnNhd hρ
        (hf.continuousOn.mono sphere_subset_closedBall) hX
    have ha := analyticOnNhd_analyticRemainder hρ (hf.mono ball_subset_closedBall)
    have he : (fun z => parameterCauchyRemainder f ρ p z) =ᶠ[𝓝[≠] (0 : ℂ)]
        analyticRemainder (fun ζ => f (p, ζ)) := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds 0 hρ),
        self_mem_nhdsWithin] with z hz hz0
      exact hne hz (by simpa only [mem_compl_iff, mem_singleton_iff] using hz0)
    exact (((hc 0 (mem_ball_self hρ)).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (ha 0 (mem_ball_self hρ)).continuousAt).mp he).eq_of_nhds
  · exact hne hq hq0

/-- In particular, the contour value at zero is the derivative of the slice. -/
theorem parameterCauchyRemainder_zero {f : E × ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) {p : E}
    (hf : AnalyticOnNhd ℂ (fun ζ => f (p, ζ)) (closedBall (0 : ℂ) ρ)) :
    parameterCauchyRemainder f ρ p 0 = deriv (fun ζ => f (p, ζ)) 0 := by
  rw [parameterCauchyRemainder_eq_analyticRemainder hρ hf (mem_ball_self hρ),
    analyticRemainder_zero]

/-- Boundary bounds on the fixed contour also bound the actual divided
difference uniformly on its inner half disk. -/
theorem norm_analyticRemainder_le_of_boundary_bound {f : E × ℂ → ℂ} {ρ S : ℝ}
    (hρ : 0 < ρ) (hS : 0 ≤ S) {p : E}
    (hf : AnalyticOnNhd ℂ (fun ζ => f (p, ζ)) (closedBall (0 : ℂ) ρ))
    (hbound : ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖f (p, ζ)‖ ≤ S)
    {q : ℂ} (hq : ‖q‖ ≤ ρ / 2) :
    ‖analyticRemainder (fun ζ => f (p, ζ)) q‖ ≤ 2 * S / ρ := by
  have hq' : q ∈ ball (0 : ℂ) ρ := by
    simpa only [mem_ball, dist_zero_right] using hq.trans_lt (half_lt_self hρ)
  rw [← parameterCauchyRemainder_eq_analyticRemainder hρ hf hq']
  exact norm_parameterCauchyRemainder_le hρ hS hbound hq

variable [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]

/-- The divided difference is jointly holomorphic in all independent complex
parameters and in the scale variable, across scale zero. -/
theorem differentiableOn_analyticRemainder_parameters {f : E × ℂ → ℂ} {U : Set E}
    {ρ : ℝ} (hU : IsOpen U) (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (U ×ˢ closedBall (0 : ℂ) ρ)) :
    DifferentiableOn ℂ
      (fun p : E × ℂ => analyticRemainder (fun ζ => f (p.1, ζ)) p.2)
      (U ×ˢ ball (0 : ℂ) ρ) := by
  apply (differentiableOn_parameterCauchyRemainder hU hρ hf).congr
  intro p hp
  have hs : AnalyticOnNhd ℂ (fun ζ => f (p.1, ζ)) (closedBall (0 : ℂ) ρ) := by
    intro ζ hζ
    exact (hf (p.1, ζ) ⟨hp.1, hζ⟩).fun_comp
      (f := fun w : ℂ => (p.1, w)) (analyticAt_const.prod analyticAt_id)
  exact (parameterCauchyRemainder_eq_analyticRemainder hρ hs hp.2).symm

end AbelFormalization
