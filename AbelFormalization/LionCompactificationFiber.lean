import AbelFormalization.LionStandardCarpet
import AbelFormalization.SmoothFamilyOMinimalityCriterion

/-!
# Fibers of Lion's compactification map

Lion's Lemma 6 realizes every compact approximation as the projection of one
fiber of an enlarged map.  This is the bridge that lets the generic component
bound from Theorem 7 control the compact sets used to recover an arbitrary
fiber.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Product source for Lion's compactification: `(x,u,v,t)`. -/
abbrev LionCompactificationSource (X Y : Type*) :=
  X × (ℝ × (ℝ × Y))

/-- Product target for Lion's compactification: `(eta,epsilon,t)`. -/
abbrev LionCompactificationTarget (Y : Type*) :=
  ℝ × (ℝ × Y)

/-- Lion's compactification map
`(x,u,v,t) ↦ (delta(x)-u², dist(g(x),t)²+v², t)`. -/
def lionCompactificationMap
    {X Y : Type*} [PseudoMetricSpace Y]
    (delta : X → ℝ) (g : X → Y) :
    LionCompactificationSource X Y → LionCompactificationTarget Y :=
  fun z ↦
    (delta z.1 - z.2.1 ^ 2,
      (dist (g z.1) z.2.2.2 ^ 2 + z.2.2.1 ^ 2, z.2.2.2))

/-- The target whose fiber projects to the compact approximation with radius
`r`. -/
def lionCompactificationTargetPoint
    {Y : Type*} (eta r : ℝ) (T : Y) :
    LionCompactificationTarget Y :=
  (eta, (r ^ 2, T))

/-- The projection of a compactification fiber is exactly Lion's compact
approximation. -/
theorem image_fiber_lionCompactificationMap_eq_approximation
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    (delta : X → ℝ) (g : X → Y)
    (eta r : ℝ) (T : Y) (hr : 0 ≤ r) :
    (fun z : LionCompactificationSource X Y ↦ z.1) ''
        ((lionCompactificationMap delta g) ⁻¹'
          {lionCompactificationTargetPoint eta r T}) =
      lionCompactApproximation Set.univ delta g eta r T := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change lionCompactificationMap delta g z =
      lionCompactificationTargetPoint eta r T at hz
    have ht : z.2.2.2 = T := congrArg (fun w ↦ w.2.2) hz
    have hetaEq : delta z.1 - z.2.1 ^ 2 = eta :=
      congrArg Prod.fst hz
    have hrEq : dist (g z.1) z.2.2.2 ^ 2 + z.2.2.1 ^ 2 = r ^ 2 :=
      congrArg (fun w ↦ w.2.1) hz
    rw [ht] at hrEq
    have hetaLe : eta ≤ delta z.1 := by
      nlinarith [sq_nonneg z.2.1]
    have hdist : dist (g z.1) T ≤ r := by
      have hd : 0 ≤ dist (g z.1) T := dist_nonneg
      nlinarith [sq_nonneg z.2.2.1]
    exact ⟨⟨Set.mem_univ z.1, hetaLe⟩, hdist⟩
  · intro hx
    obtain ⟨⟨_hxU, hetaLe⟩, hdist⟩ := hx
    let u : ℝ := Real.sqrt (delta x - eta)
    let v : ℝ := Real.sqrt (r ^ 2 - dist (g x) T ^ 2)
    have huNonneg : 0 ≤ delta x - eta := sub_nonneg.mpr hetaLe
    have hvNonneg : 0 ≤ r ^ 2 - dist (g x) T ^ 2 := by
      have hd : 0 ≤ dist (g x) T := dist_nonneg
      nlinarith
    let z : LionCompactificationSource X Y := (x, (u, (v, T)))
    refine ⟨z, ?_, rfl⟩
    change lionCompactificationMap delta g z =
      lionCompactificationTargetPoint eta r T
    simp only [lionCompactificationMap, lionCompactificationTargetPoint,
      z, u, v, Real.sq_sqrt huNonneg, Real.sq_sqrt hvNonneg]
    apply Prod.ext
    · ring
    · apply Prod.ext
      · ring
      · rfl

/-- Projection cannot increase the number of connected components, so a
compact approximation has no more components than the corresponding
compactification fiber. -/
theorem enatCard_lionCompactApproximation_le_compactificationFiber
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    (delta : X → ℝ) (g : X → Y)
    (eta r : ℝ) (T : Y) (hr : 0 ≤ r) :
    ENat.card
        (ConnectedComponents
          (lionCompactApproximation Set.univ delta g eta r T)) ≤
      ENat.card
        (ConnectedComponents
          ((lionCompactificationMap delta g) ⁻¹'
            {lionCompactificationTargetPoint eta r T})) := by
  let fiber : Set (LionCompactificationSource X Y) :=
    (lionCompactificationMap delta g) ⁻¹'
      {lionCompactificationTargetPoint eta r T}
  let approximation : Set X :=
    lionCompactApproximation Set.univ delta g eta r T
  have himage : (fun z : LionCompactificationSource X Y ↦ z.1) '' fiber =
      approximation := by
    exact image_fiber_lionCompactificationMap_eq_approximation
      delta g eta r T hr
  let projection : fiber → approximation := fun z ↦
    ⟨z.1.1, by
      rw [← himage]
      exact ⟨z.1, z.2, rfl⟩⟩
  have hprojection : Continuous projection := by
    apply Continuous.subtype_mk
    exact continuous_fst.comp continuous_subtype_val
  have hsurj : Function.Surjective projection := by
    intro x
    have hxImage : (x : X) ∈
        (fun z : LionCompactificationSource X Y ↦ z.1) '' fiber := by
      rw [himage]
      exact x.property
    obtain ⟨z, hz, hzx⟩ := hxImage
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hzx
  exact enatCard_connectedComponents_le_of_continuous_surjective
    hprojection hsurj

/-- A numerical component bound on the compactification fiber transfers to
the compact approximation. -/
theorem enatCard_lionCompactApproximation_le_of_fiber_le
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    (delta : X → ℝ) (g : X → Y)
    (eta r : ℝ) (T : Y) (hr : 0 ≤ r) (N : ℕ)
    (hbound : ENat.card
        (ConnectedComponents
          ((lionCompactificationMap delta g) ⁻¹'
            {lionCompactificationTargetPoint eta r T})) ≤ (N : ℕ∞)) :
    ENat.card
        (ConnectedComponents
          (lionCompactApproximation Set.univ delta g eta r T)) ≤
      (N : ℕ∞) :=
  (enatCard_lionCompactApproximation_le_compactificationFiber
    delta g eta r T hr).trans hbound

end AbelFormalization
