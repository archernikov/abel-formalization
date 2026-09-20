import AbelFormalization.CharbonnelSardianIntegerAffineSliceGeometry
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Sequences

/-!
# Compact intersection thickening for Wilkie's affine-slice argument

The effective exposition's Lemma 10.7 says that inside a fixed compact
region, sufficiently thin neighborhoods of two closed sets lie inside
any prescribed neighborhood of their intersection. This is the compact
topological step needed for the from-below direction of Wilkie 3.12.

The conclusion concerns `A ∩ B` itself. It does not identify
`closure (A ∩ B)` with `closure A ∩ B`.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- A one-radius strengthening of the compact intersection lemma. The
explicit `Metric.thickening` witness semantics also handles an empty
intersection correctly. -/
theorem compact_closed_intersection_thickening
    {X : Type*} [MetricSpace X]
    {K A B : Set X} (hK : IsCompact K)
    (hA : IsClosed A) (hB : IsClosed B)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ x ∈ K,
        x ∈ Metric.thickening eta A →
        x ∈ Metric.thickening eta B →
        x ∈ Metric.thickening delta (A ∩ B) := by
  classical
  by_contra hnone
  let radius : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hradius_pos : ∀ n, 0 < radius n := by
    intro n
    dsimp only [radius]
    positivity
  have hbad : ∀ n : ℕ,
      ∃ x : X, x ∈ K ∧
        x ∈ Metric.thickening (radius n) A ∧
        x ∈ Metric.thickening (radius n) B ∧
        x ∉ Metric.thickening delta (A ∩ B) := by
    intro n
    have hfail : ¬ ∀ x ∈ K,
        x ∈ Metric.thickening (radius n) A →
        x ∈ Metric.thickening (radius n) B →
        x ∈ Metric.thickening delta (A ∩ B) := by
      intro hall
      exact hnone ⟨radius n, hradius_pos n, hall⟩
    push Not at hfail
    exact hfail
  choose x hxK hxA hxB hxBad using hbad
  obtain ⟨limit, hlimitK, phi, hphiMono, hphiLimit⟩ :=
    hK.tendsto_subseq hxK
  have hradiusLimit :
      Tendsto (fun n : ℕ ↦ radius (phi n)) atTop (𝓝 0) := by
    simpa [radius, Function.comp_def] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        hphiMono.tendsto_atTop
  have limit_mem_of_near (S : Set X) (hS : IsClosed S)
      (hnear : ∀ n : ℕ,
        x (phi n) ∈ Metric.thickening (radius (phi n)) S) :
      limit ∈ S := by
    apply (Metric.mem_of_closed' hS).2
    intro epsilon hepsilon
    have hhalf : 0 < epsilon / 2 := by linarith
    have hball : ∀ᶠ n in atTop,
        x (phi n) ∈ Metric.ball limit (epsilon / 2) :=
      hphiLimit.eventually (Metric.ball_mem_nhds limit hhalf)
    have hsmall : ∀ᶠ n in atTop,
        radius (phi n) < epsilon / 2 :=
      hradiusLimit.eventually (Iio_mem_nhds hhalf)
    obtain ⟨n, hnBall, hnSmall⟩ := (hball.and hsmall).exists
    obtain ⟨y, hyS, hnNear⟩ :=
      Metric.mem_thickening_iff.mp (hnear n)
    have hnDist : dist limit (x (phi n)) < epsilon / 2 := by
      simpa only [Metric.mem_ball, dist_comm] using hnBall
    refine ⟨y, hyS, ?_⟩
    have htriangle := dist_triangle limit (x (phi n)) y
    linarith
  have hlimitA : limit ∈ A :=
    limit_mem_of_near A hA (fun n ↦ hxA (phi n))
  have hlimitB : limit ∈ B :=
    limit_mem_of_near B hB (fun n ↦ hxB (phi n))
  have hlimitInter : limit ∈ Metric.thickening delta (A ∩ B) := by
    apply Metric.mem_thickening_iff.mpr
    refine ⟨limit, ⟨hlimitA, hlimitB⟩, ?_⟩
    simpa only [dist_self] using hdelta
  have hfinally : ∀ᶠ n in atTop,
      x (phi n) ∈ Metric.thickening delta (A ∩ B) :=
    hphiLimit.eventually
      (Metric.isOpen_thickening.mem_nhds hlimitInter)
  obtain ⟨n, hn⟩ := hfinally.exists
  exact hxBad (phi n) hn

/-- The two independent radii phrasing of Lemma 10.7 follows by using
the same sufficiently small radius for both closed sets. -/
theorem compact_closed_intersection_thickening_two_radii
    {X : Type*} [MetricSpace X]
    {K A B : Set X} (hK : IsCompact K)
    (hA : IsClosed A) (hB : IsClosed B)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ etaA : ℝ, 0 < etaA ∧
      ∃ etaB : ℝ, 0 < etaB ∧
        K ∩ Metric.thickening etaA A ∩
            Metric.thickening etaB B ⊆
          Metric.thickening delta (A ∩ B) := by
  obtain ⟨eta, heta, hnear⟩ :=
    compact_closed_intersection_thickening hK hA hB hdelta
  refine ⟨eta, heta, eta, heta, ?_⟩
  intro x hx
  exact hnear x hx.1.1 hx.1.2 hx.2

/-- Specialization to points already in a compact closed target: points
of that target lying sufficiently near a closed hyperplane lie near the
actual slice. -/
theorem compact_slice_thickening
    {X : Type*} [MetricSpace X]
    {C H : Set X} (hC : IsCompact C) (hH : IsClosed H)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ x ∈ C,
        x ∈ Metric.thickening eta H →
          x ∈ Metric.thickening delta (C ∩ H) := by
  obtain ⟨eta, heta, hnear⟩ :=
    compact_closed_intersection_thickening hC hC.isClosed hH hdelta
  refine ⟨eta, heta, ?_⟩
  intro x hxC hxH
  have hxNearC : x ∈ Metric.thickening eta C := by
    apply Metric.mem_thickening_iff.mpr
    refine ⟨x, hxC, ?_⟩
    simpa only [dist_self] using heta
  exact hnear x hxC hxNearC hxH

end AbelFormalization
