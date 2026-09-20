import AbelFormalization.ComplexExtension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Uniform bounded complex extensions on a compact set

Compactness supplies a common positive disk radius and norm bound. The
extension itself may depend on the center; no gluing of branches is assumed.
-/

noncomputable section

namespace AbelFormalization

open Set Filter Metric
open scoped Topology

/-- A bounded analytic extension on one disk, agreeing with `f` on its real diameter. -/
def BoundedComplexExtension (f : ℝ → ℝ) (x ρ M : ℝ) : Prop :=
  ∃ F : ℂ → ℂ,
    AnalyticOnNhd ℂ F (ball (x : ℂ) ρ) ∧
      (∀ y : ℝ, y ∈ ball x ρ → F (y : ℂ) = (f y : ℂ)) ∧
        ∀ z ∈ ball (x : ℂ) ρ, ‖F z‖ ≤ M

theorem BoundedComplexExtension.mono {f : ℝ → ℝ} {x ρ ρ' M M' : ℝ}
    (h : BoundedComplexExtension f x ρ M) (hρ : ρ' ≤ ρ) (hM : M ≤ M') :
    BoundedComplexExtension f x ρ' M' := by
  obtain ⟨F, hF, he, hb⟩ := h
  refine ⟨F, hF.mono (ball_subset_ball hρ), ?_, ?_⟩
  · intro y hy
    exact he y (ball_subset_ball hρ hy)
  · intro z hz
    exact (hb z (ball_subset_ball hρ hz)).trans hM

/-- Around one analytic point, neighboring real centers share a bounded branch. -/
theorem exists_local_bounded_complex_extensions {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) :
    ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 < M ∧
      ∀ y ∈ ball x r, BoundedComplexExtension f y r M := by
  obtain ⟨r, hr, F, hF, he⟩ := exists_complex_extension_on_ball_of_analyticAt hf
  have hsub : closedBall (x : ℂ) (r / 2) ⊆ ball (x : ℂ) r :=
    closedBall_subset_ball (by linarith)
  have hc : ContinuousOn (fun z : ℂ => ‖F z‖) (closedBall (x : ℂ) (r / 2)) :=
    (hF.continuousOn.mono hsub).norm
  obtain ⟨M, hM⟩ := (isCompact_closedBall (x : ℂ) (r / 2)).bddAbove_image hc
  refine ⟨r / 4, by positivity, max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro y hy
  have hshift : ball (y : ℂ) (r / 4) ⊆ closedBall (x : ℂ) (r / 2) := by
    intro z hz
    have hyc : dist (y : ℂ) (x : ℂ) < r / 4 := by
      rw [Complex.isometry_ofReal.dist_eq]
      exact hy
    have hz' : dist z (y : ℂ) < r / 4 := hz
    have ht := dist_triangle z (y : ℂ) (x : ℂ)
    show dist z (x : ℂ) ≤ r / 2
    linarith
  refine ⟨F, hF.mono (hshift.trans hsub), ?_, ?_⟩
  · intro t ht
    apply he t
    have ht' : dist t y < r / 4 := ht
    have hy' : dist y x < r / 4 := hy
    have htriangle := dist_triangle t y x
    show dist t x < r
    linarith
  · intro z hz
    exact (hM ⟨z, hshift hz, rfl⟩).trans (le_max_left _ _)

/-- Common radius and bound for local extensions at all points of a compact real set. -/
theorem exists_uniform_bounded_complex_extensions {f : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hf : ∀ x ∈ K, AnalyticAt ℝ f x) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, 0 < M ∧
      ∀ x ∈ K, BoundedComplexExtension f x ρ M := by
  let P : Set ℝ → Prop := fun S =>
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, 0 < M ∧
      ∀ x ∈ S, BoundedComplexExtension f x ρ M
  change P K
  apply hK.induction_on (p := P)
  · refine ⟨1, zero_lt_one, 1, zero_lt_one, ?_⟩
    intro x hx
    exact False.elim hx
  · intro S T hST hT
    obtain ⟨ρ, hρ, M, hM, h⟩ := hT
    exact ⟨ρ, hρ, M, hM, fun x hx => h x (hST hx)⟩
  · intro S T hS hT
    obtain ⟨ρS, hρS, MS, hMS, hs⟩ := hS
    obtain ⟨ρT, hρT, MT, hMT, ht⟩ := hT
    refine ⟨min ρS ρT, lt_min hρS hρT, max MS MT,
      lt_of_lt_of_le hMS (le_max_left _ _), ?_⟩
    intro x hx
    rcases hx with hx | hx
    · exact (hs x hx).mono (min_le_left _ _) (le_max_left _ _)
    · exact (ht x hx).mono (min_le_right _ _) (le_max_right _ _)
  · intro x hx
    obtain ⟨r, hr, M, hM, h⟩ := exists_local_bounded_complex_extensions (hf x hx)
    refine ⟨ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr), r, hr, M, hM, h⟩

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- Uniform bounded local branches on a compact fundamental interval. -/
theorem uniform_complex_extensions_fundamental {U : ℝ} (hU : 0 < U) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, 0 < M ∧
      ∀ x ∈ Icc U (E U), BoundedComplexExtension A x ρ M := by
  apply exists_uniform_bounded_complex_extensions isCompact_Icc
  intro x hx
  exact hA.analytic x (hU.trans_le hx.1)

end IsAbel

end AbelFormalization
