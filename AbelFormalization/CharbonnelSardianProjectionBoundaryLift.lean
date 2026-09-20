import AbelFormalization.CharbonnelSardianProjectionTopology
import Mathlib.Analysis.Convex.Topology

/-!
# Lifting a projected boundary crossing to the old boundary

Wilkie 3.10 joins a point of the old set to a point on the same vertical
slice lying outside its closure.  The joining segment must meet the old
boundary, and convexity keeps its visible coordinate in the chosen local
ball.  This file proves that topological step independently of the later
regular-value and Case-2 arguments.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A preconnected set which meets a set and its complement meets the
frontier of that set. -/
theorem IsPreconnected.inter_frontier_nonempty_of_inter_compl_nonempty
    {X : Type*} [TopologicalSpace X]
    {C S : Set X} (hC : IsPreconnected C)
    (hCS : (C ∩ S).Nonempty) (hCSc : (C ∩ Sᶜ).Nonempty) :
    (C ∩ frontier S).Nonempty := by
  letI : PreconnectedSpace C := Subtype.preconnectedSpace hC
  let D : Set C := {x | (x : X) ∈ S}
  have hDnonempty : D.Nonempty := by
    obtain ⟨x, hxC, hxS⟩ := hCS
    exact ⟨⟨x, hxC⟩, hxS⟩
  have hDne : D ≠ Set.univ := by
    obtain ⟨x, hxC, hxSc⟩ := hCSc
    intro hD
    have hxD : (⟨x, hxC⟩ : C) ∈ D := by
      rw [hD]
      exact Set.mem_univ _
    exact hxSc hxD
  obtain ⟨x, hxFrontier⟩ :=
    (nonempty_frontier_iff.mpr ⟨hDnonempty, hDne⟩)
  have hxMapped : (x : X) ∈ frontier S := by
    exact continuous_subtype_val.frontier_preimage_subset S hxFrontier
  exact ⟨x, x.property, hxMapped⟩

/-- A segment whose endpoints lie on opposite sides of a set meets its
frontier. -/
theorem exists_mem_segment_inter_frontier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {a b : E} (ha : a ∈ S) (hb : b ∉ S) :
    ∃ w ∈ segment ℝ a b, w ∈ frontier S := by
  have hsegment : IsPreconnected (segment ℝ a b) :=
    (convex_segment a b).isPreconnected
  obtain ⟨w, hwSegment, hwFrontier⟩ :=
    IsPreconnected.inter_frontier_nonempty_of_inter_compl_nonempty hsegment
      ⟨a, left_mem_segment ℝ a b, ha⟩
      ⟨b, right_mem_segment ℝ a b, hb⟩
  exact ⟨w, hwSegment, hwFrontier⟩

/-- Appending one fixed hidden coordinate is continuous. -/
theorem continuous_realEuclideanAppend_fixedRight
    {n q : ℕ} (hidden : RealEuclidean q) :
    Continuous (fun x : RealEuclidean n ↦
      realEuclideanAppend x hidden) := by
  apply continuous_pi
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa [realEuclideanAppend] using
      (continuous_apply j :
        Continuous (fun x : RealEuclidean n ↦ x j))
  · simpa [realEuclideanAppend] using
      (continuous_const :
        Continuous (fun _ : RealEuclidean n ↦ hidden j))

/-- If one point of a convex visible neighborhood has a lift in `closure A`
and another point lies outside the closed projected target, then the segment
between them contains a visible point whose fixed lift lies on
`frontier (closure A)`. -/
theorem exists_fixedVertical_frontier_lift_on_convex_segment
    {n q : ℕ} (A : Set (RealEuclidean (n + q)))
    (U : Set (RealEuclidean n)) (hUconvex : Convex ℝ U)
    {a b : RealEuclidean n} (haU : a ∈ U) (hbU : b ∈ U)
    (hidden : RealEuclidean q)
    (haLift : realEuclideanAppend a hidden ∈ closure A)
    (hbOutside : b ∉ closure (realEuclideanExistentialProjection A)) :
    ∃ w ∈ U,
      realEuclideanAppend w hidden ∈ frontier (closure A) := by
  let lift : RealEuclidean n → RealEuclidean (n + q) :=
    fun x ↦ realEuclideanAppend x hidden
  have hliftContinuous : Continuous lift :=
    continuous_realEuclideanAppend_fixedRight hidden
  have hbLift : lift b ∉ closure A := by
    intro hbClosure
    apply hbOutside
    apply realEuclideanExistentialProjection_closure_subset_closure A
    refine ⟨hidden, ?_⟩
    exact hbClosure
  have haPreimage : a ∈ lift ⁻¹' closure A := haLift
  have hbPreimage : b ∉ lift ⁻¹' closure A := hbLift
  obtain ⟨w, hwSegment, hwPreFrontier⟩ :=
    exists_mem_segment_inter_frontier haPreimage hbPreimage
  have hwLiftFrontier : lift w ∈ frontier (closure A) :=
    hliftContinuous.frontier_preimage_subset (closure A) hwPreFrontier
  exact ⟨w, hUconvex.segment_subset haU hbU hwSegment,
    hwLiftFrontier⟩

/-- A projected-boundary point in an open convex neighborhood supplies the
two visible endpoints and a fixed hidden coordinate needed by the preceding
boundary-lift theorem. -/
theorem exists_fixedVertical_frontier_lift_of_projected_boundary
    {n q : ℕ} (A : Set (RealEuclidean (n + q)))
    (U : Set (RealEuclidean n)) (hUopen : IsOpen U)
    (hUconvex : Convex ℝ U)
    {x : RealEuclidean n}
    (hxU : x ∈ U)
    (hxBoundary :
      x ∈ frontier (closure (realEuclideanExistentialProjection A))) :
    ∃ w ∈ U, ∃ hidden : RealEuclidean q,
      realEuclideanAppend w hidden ∈ frontier (closure A) := by
  let P : Set (RealEuclidean n) :=
    closure (realEuclideanExistentialProjection A)
  have hxProjectionClosure :
      x ∈ closure (realEuclideanExistentialProjection A) :=
    isClosed_closure.frontier_subset hxBoundary
  obtain ⟨a, haU, haProjection⟩ :=
    (mem_closure_iff.mp hxProjectionClosure) U hUopen hxU
  obtain ⟨hidden, haLift⟩ := haProjection
  have hxComplClosure : x ∈ closure Pᶜ := by
    rw [frontier_eq_closure_inter_closure] at hxBoundary
    exact hxBoundary.2
  obtain ⟨b, hbU, hbOutside⟩ :=
    (mem_closure_iff.mp hxComplClosure) U hUopen hxU
  obtain ⟨w, hwU, hwFrontier⟩ :=
    exists_fixedVertical_frontier_lift_on_convex_segment
      A U hUconvex haU hbU hidden (subset_closure haLift) hbOutside
  exact ⟨w, hwU, hidden, hwFrontier⟩

end AbelFormalization
