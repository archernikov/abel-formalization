import AbelFormalization.AnalyticGermLocal
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Convex

/-! # Analytic germs form an integral domain

The identity principle on a sufficiently small ball rules out zero divisors
in the actual analytic-germ ring. This holds in every real normed parameter
space and does not assume Noetherianity or a dimension theorem.
-/

noncomputable section

open Filter Set Metric
open scoped Topology

namespace AbelFormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A product of two analytic functions vanishing near the base point forces
one of its factors to vanish near that point. -/
theorem analyticAt_eventuallyEq_zero_or_of_mul {x : E} {f g : E → ℝ}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x)
    (hfg : (f * g) =ᶠ[𝓝 x] 0) :
    f =ᶠ[𝓝 x] 0 ∨ g =ᶠ[𝓝 x] 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    ((hf.eventually_analyticAt.and hg.eventually_analyticAt).and hfg)
  by_cases hfzero : ∀ y ∈ ball x r, f y = 0
  · left
    filter_upwards [ball_mem_nhds x hr] with y hy
    exact hfzero y hy
  · push Not at hfzero
    obtain ⟨y, hy, hfy⟩ := hfzero
    have hfycont : ContinuousAt f y := (hball hy).1.1.continuousAt
    have hgneary : g =ᶠ[𝓝 y] 0 := by
      filter_upwards [isOpen_ball.mem_nhds hy, hfycont.eventually_ne hfy] with z hz hfz
      exact (mul_eq_zero.mp (hball hz).2).resolve_left hfz
    have hgball : AnalyticOnNhd ℝ g (ball x r) := fun z hz => (hball hz).1.2
    have hgzero : EqOn g 0 (ball x r) :=
      hgball.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball x r).isPreconnected hy hgneary
    right
    filter_upwards [ball_mem_nhds x hr] with z hz
    exact hgzero hz

/-- Equality with the zero germ is exactly neighborhood vanishing. -/
@[simp]
theorem analyticGermOf_eq_zero_iff {x : E} {f : E → ℝ} (hf : AnalyticAt ℝ f x) :
    analyticGermOf f hf = 0 ↔ f =ᶠ[𝓝 x] 0 :=
  analyticGermOf_eq_iff hf analyticAt_const

instance analyticGermNoZeroDivisors (x : E) : NoZeroDivisors (AnalyticGermAt x) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    obtain ⟨f, hf, rfl⟩ := exists_analyticGerm_representative a
    obtain ⟨g, hg, rfl⟩ := exists_analyticGerm_representative b
    rw [← analyticGermOf_mul, analyticGermOf_eq_zero_iff] at hab
    rcases analyticAt_eventuallyEq_zero_or_of_mul hf hg hab with hfzero | hgzero
    · exact Or.inl ((analyticGermOf_eq_zero_iff hf).mpr hfzero)
    · exact Or.inr ((analyticGermOf_eq_zero_iff hg).mpr hgzero)

/-- The analytic identity principle proves the domain property without
replacing the germ ring by a formal power-series ring. -/
instance analyticGermIsDomain (x : E) : IsDomain (AnalyticGermAt x) :=
  NoZeroDivisors.to_isDomain _

end AbelFormalization
