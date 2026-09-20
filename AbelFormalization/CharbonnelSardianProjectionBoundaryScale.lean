import AbelFormalization.CharbonnelSardianProjectionBoundaryLift
import AbelFormalization.CharbonnelSardianProjectionCompactUniformization

/-!
# A uniform geometric scale for Wilkie's projection construction

For a fixed positive visible error, the bounded part of the projected
boundary is compact. Around each of its points, the boundary-lift theorem
produces a point of the old boundary with a fixed hidden coordinate. A
finite subcover then gives one positive scale which is small compared with
the visible error, an external modulus bound, and the reciprocal norm of
all selected old-boundary lifts.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- On one bounded projected-boundary truncation, finitely many local
boundary lifts have one common positive geometric scale. -/
theorem exists_sardianProjectionBoundaryCoverScale
    {n : ℕ} (A : Set (RealEuclidean (n + 1)))
    (extra : RealEuclidean n → ℝ)
    {r B : ℝ} (hr : 0 < r) (hB : 0 < B)
    (hextra : ∀ c ∈ sardianProjectionBoundaryTruncation A r⁻¹,
      0 < extra c) :
    ∃ eta : ℝ, 0 < eta ∧ eta < r / 8 ∧ eta < B ∧
      ∀ z ∈ sardianProjectionBoundaryTruncation A r⁻¹,
        ∃ c ∈ sardianProjectionBoundaryTruncation A r⁻¹,
          z ∈ Metric.ball c (r / 8) ∧
          ∃ a : RealEuclidean n, ∃ hidden : RealEuclidean 1,
            a ∈ Metric.ball c (r / 8) ∧
            realEuclideanAppend a hidden ∈ frontier (closure A) ∧
            ‖realEuclideanAppend a hidden‖ < eta⁻¹ ∧
            eta < extra c := by
  classical
  let K := sardianProjectionBoundaryTruncation A r⁻¹
  have hlift : ∀ c : K,
      ∃ a : RealEuclidean n, ∃ hidden : RealEuclidean 1,
        a ∈ Metric.ball (c : RealEuclidean n) (r / 8) ∧
        realEuclideanAppend a hidden ∈ frontier (closure A) := by
    intro c
    have hcBoundary : (c : RealEuclidean n) ∈
        frontier (closure (realEuclideanExistentialProjection A)) :=
      c.property.1
    obtain ⟨a, ha, hidden, hfrontier⟩ :=
      exists_fixedVertical_frontier_lift_of_projected_boundary
        A (Metric.ball (c : RealEuclidean n) (r / 8))
        Metric.isOpen_ball
        (convex_ball (c : RealEuclidean n) (r / 8))
        (Metric.mem_ball_self (by positivity)) hcBoundary
    exact ⟨a, hidden, ha, hfrontier⟩
  choose a hidden haBall hfrontier using hlift
  let oldPoint : K → RealEuclidean (n + 1) :=
    fun c ↦ realEuclideanAppend (a c) (hidden c)
  let localBound : K → ℝ := fun c ↦
    min (r / 16)
      (min (B / 2)
        (min (extra c / 2) ((‖oldPoint c‖ + 1)⁻¹)))
  have hlocalBound : ∀ c : K, 0 < localBound c := by
    intro c
    apply lt_min (by positivity)
    apply lt_min (by positivity)
    apply lt_min (by exact half_pos (hextra c c.property))
    exact inv_pos.mpr (by positivity)
  have hcover : K ⊆
      ⋃ c : K, Metric.ball (c : RealEuclidean n) (r / 8) := by
    intro z hz
    exact Set.mem_iUnion.mpr
      ⟨⟨z, hz⟩, Metric.mem_ball_self (by positivity)⟩
  obtain ⟨F, hFcover⟩ :=
    (isCompact_sardianProjectionBoundaryTruncation A r⁻¹)
      |>.elim_finite_subcover
        (fun c : K ↦ Metric.ball (c : RealEuclidean n) (r / 8))
        (fun _ ↦ Metric.isOpen_ball) hcover
  by_cases hK : K.Nonempty
  · have hF : F.Nonempty := by
      obtain ⟨z, hzK⟩ := hK
      obtain ⟨c, hcF, _hzc⟩ := Set.mem_iUnion₂.mp (hFcover hzK)
      exact ⟨c, hcF⟩
    let eta : ℝ := F.inf' hF localBound
    have heta : 0 < eta := by
      exact (Finset.lt_inf'_iff hF).2
        (fun c hcF ↦ hlocalBound c)
    obtain ⟨c0, hc0F⟩ := hF
    have hetaLocal0 : eta ≤ localBound c0 :=
      Finset.inf'_le localBound hc0F
    have hetaR16 : eta ≤ r / 16 :=
      hetaLocal0.trans (min_le_left _ _)
    have hetaB2 : eta ≤ B / 2 :=
      hetaLocal0.trans
        ((min_le_right (r / 16)
          (min (B / 2)
            (min (extra c0 / 2) ((‖oldPoint c0‖ + 1)⁻¹)))).trans
          (min_le_left _ _))
    refine ⟨eta, heta, by linarith, by linarith, ?_⟩
    intro z hzK
    obtain ⟨c, hcF, hzc⟩ := Set.mem_iUnion₂.mp (hFcover hzK)
    have hetaLocal : eta ≤ localBound c :=
      Finset.inf'_le localBound hcF
    have hetaInv : eta ≤ (‖oldPoint c‖ + 1)⁻¹ :=
      hetaLocal.trans
        ((min_le_right (r / 16)
          (min (B / 2)
            (min (extra c / 2) ((‖oldPoint c‖ + 1)⁻¹)))).trans
          ((min_le_right (B / 2)
            (min (extra c / 2) ((‖oldPoint c‖ + 1)⁻¹))).trans
            (min_le_right _ _)))
    have hetaExtraHalf : eta ≤ extra c / 2 :=
      hetaLocal.trans
        ((min_le_right (r / 16)
          (min (B / 2)
            (min (extra c / 2) ((‖oldPoint c‖ + 1)⁻¹)))).trans
          ((min_le_right (B / 2)
            (min (extra c / 2) ((‖oldPoint c‖ + 1)⁻¹))).trans
            (min_le_left _ _)))
    have hden : 0 < ‖oldPoint c‖ + 1 := by positivity
    have hdenInv : ‖oldPoint c‖ + 1 ≤ eta⁻¹ := by
      have hinv :=
        (inv_le_inv₀ (inv_pos.mpr hden) heta).2 hetaInv
      simpa only [inv_inv] using hinv
    refine ⟨c, c.property, hzc, a c, hidden c,
      haBall c, hfrontier c, ?_, by
        have := hextra c c.property
        linarith⟩
    change ‖oldPoint c‖ < eta⁻¹
    exact (by linarith : ‖oldPoint c‖ < ‖oldPoint c‖ + 1).trans_le hdenInv
  · let eta : ℝ := min (r / 16) (B / 2)
    have heta : 0 < eta := lt_min (by positivity) (by positivity)
    refine ⟨eta, heta, ?_, ?_, ?_⟩
    · exact (min_le_left _ _).trans_lt (by linarith)
    · exact (min_le_right _ _).trans_lt (by linarith)
    · intro z hz
      exact (hK ⟨z, hz⟩).elim

/-- A globally defined positive boundary scale. On positive inputs it is
chosen by the compact theorem above; on nonpositive inputs it takes the
harmless value B / 2. -/
noncomputable def sardianProjectionBoundaryScale
    {n : ℕ} (A : Set (RealEuclidean (n + 1)))
    (B : ℝ) (hB : 0 < B) (r : ℝ) : ℝ :=
  if hr : 0 < r then
    Classical.choose
      (exists_sardianProjectionBoundaryCoverScale A (fun _ ↦ B)
        hr hB (fun _ _ ↦ hB))
  else B / 2

theorem sardianProjectionBoundaryScale_pos
    {n : ℕ} (A : Set (RealEuclidean (n + 1)))
    {B : ℝ} (hB : 0 < B) {r : ℝ} (hr : 0 < r) :
    0 < sardianProjectionBoundaryScale A B hB r := by
  rw [sardianProjectionBoundaryScale, dif_pos hr]
  exact (Classical.choose_spec
    (exists_sardianProjectionBoundaryCoverScale A (fun _ ↦ B)
      hr hB (fun _ _ ↦ hB))).1

theorem sardianProjectionBoundaryScale_lt_visible
    {n : ℕ} (A : Set (RealEuclidean (n + 1)))
    {B : ℝ} (hB : 0 < B) {r : ℝ} (hr : 0 < r) :
    sardianProjectionBoundaryScale A B hB r < r / 8 := by
  rw [sardianProjectionBoundaryScale, dif_pos hr]
  exact (Classical.choose_spec
    (exists_sardianProjectionBoundaryCoverScale A (fun _ ↦ B)
      hr hB (fun _ _ ↦ hB))).2.1

theorem sardianProjectionBoundaryScale_lt_bound
    {n : ℕ} (A : Set (RealEuclidean (n + 1)))
    {B : ℝ} (hB : 0 < B) {r : ℝ} (hr : 0 < r) :
    sardianProjectionBoundaryScale A B hB r < B := by
  rw [sardianProjectionBoundaryScale, dif_pos hr]
  exact (Classical.choose_spec
    (exists_sardianProjectionBoundaryCoverScale A (fun _ ↦ B)
      hr hB (fun _ _ ↦ hB))).2.2.1

theorem sardianProjectionBoundaryScale_spec
    {n : ℕ} (A : Set (RealEuclidean (n + 1)))
    {B : ℝ} (hB : 0 < B) {r : ℝ} (hr : 0 < r)
    {z : RealEuclidean n}
    (hz : z ∈ sardianProjectionBoundaryTruncation A r⁻¹) :
    ∃ c ∈ sardianProjectionBoundaryTruncation A r⁻¹,
      z ∈ Metric.ball c (r / 8) ∧
      ∃ a : RealEuclidean n, ∃ hidden : RealEuclidean 1,
        a ∈ Metric.ball c (r / 8) ∧
        realEuclideanAppend a hidden ∈ frontier (closure A) ∧
        ‖realEuclideanAppend a hidden‖ <
          (sardianProjectionBoundaryScale A B hB r)⁻¹ := by
  rw [sardianProjectionBoundaryScale, dif_pos hr]
  obtain ⟨c, hc, hzc, a, hidden, ha, hfrontier, hnorm, _hextra⟩ :=
    (Classical.choose_spec
      (exists_sardianProjectionBoundaryCoverScale A (fun _ ↦ B)
        hr hB (fun _ _ ↦ hB))).2.2.2 z hz
  exact ⟨c, hc, hzc, a, hidden, ha, hfrontier, hnorm⟩

end AbelFormalization
