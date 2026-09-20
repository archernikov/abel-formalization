import AbelFormalization.SmoothFamilyOMinimalityCriterion
import AbelFormalization.ProjectedZeroFamily

/-!
# Connected components under fiber projection

This file packages the exact topological inequality used in the affine-section
part of the smooth-family criterion.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Projection to the visible coordinates of one fiber of a product-domain
map. -/
def projectedFiberSet {X Z Y : Type*} (f : X × Z → Y) (t : Y) : Set X :=
  {x | ∃ z, f (x, z) = t}

/-- The canonical map from a fiber to its visible-coordinate projection. -/
def fiberToProjectedFiber {X Z Y : Type*} (f : X × Z → Y) (t : Y) :
    f ⁻¹' {t} → projectedFiberSet f t :=
  fun p ↦ ⟨p.1.1, p.1.2, p.2⟩

theorem continuous_fiberToProjectedFiber
    {X Z Y : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (f : X × Z → Y) (t : Y) :
    Continuous (fiberToProjectedFiber f t) := by
  apply Continuous.subtype_mk
  exact continuous_fst.comp continuous_subtype_val

theorem surjective_fiberToProjectedFiber
    {X Z Y : Type*} (f : X × Z → Y) (t : Y) :
    Function.Surjective (fiberToProjectedFiber f t) := by
  rintro ⟨x, z, hz⟩
  exact ⟨⟨(x, z), hz⟩, rfl⟩

/-- The number of connected components of a projected fiber is at most that
of the original fiber. No finiteness or continuity of the defining map is
needed; only the coordinate projection is used. -/
theorem enatCard_connectedComponents_projectedFiberSet_le
    {X Z Y : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (f : X × Z → Y) (t : Y) :
    ENat.card (ConnectedComponents (projectedFiberSet f t)) ≤
      ENat.card (ConnectedComponents (f ⁻¹' {t})) := by
  exact enatCard_connectedComponents_le_of_continuous_surjective
    (continuous_fiberToProjectedFiber f t)
    (surjective_fiberToProjectedFiber f t)

theorem enatCard_connectedComponents_projectedFiberSet_le_nat
    {X Z Y : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (f : X × Z → Y) (t : Y) (N : ℕ)
    (hfiber : ENat.card (ConnectedComponents (f ⁻¹' {t})) ≤ N) :
    ENat.card (ConnectedComponents (projectedFiberSet f t)) ≤ N :=
  (enatCard_connectedComponents_projectedFiberSet_le f t).trans hfiber

/-! ## Flat finite-coordinate fibers -/

/-- Splitting and re-appending a flat finite coordinate vector is the
identity. -/
@[simp]
theorem realEuclideanAppend_take {n q : ℕ}
    (v : RealEuclidean (n + q)) :
    realEuclideanAppend (realEuclideanTakeLeft v)
      (realEuclideanTakeRight v) = v := by
  funext k
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
    simp [realEuclideanTakeLeft, realEuclideanTakeRight]

/-- Continuous-linear projection to the first block of flat coordinates. -/
def realEuclideanTakeLeftContinuousLinearMap (n q : ℕ) :
    RealEuclidean (n + q) →L[ℝ] RealEuclidean n :=
  ({
    toFun := realEuclideanTakeLeft
    map_add' := by
      intro v w
      funext i
      rfl
    map_smul' := by
      intro c v
      funext i
      rfl
  } : RealEuclidean (n + q) →ₗ[ℝ] RealEuclidean n).toContinuousLinearMap

@[simp]
theorem realEuclideanTakeLeftContinuousLinearMap_apply
    {n q : ℕ} (v : RealEuclidean (n + q)) :
    realEuclideanTakeLeftContinuousLinearMap n q v =
      realEuclideanTakeLeft v :=
  rfl

/-- Visible-coordinate projection of a fiber of a map on flat coordinates. -/
def flatProjectedFiberSet {n q b : ℕ}
    (h : RealEuclidean (n + q) → RealEuclidean b)
    (t : RealEuclidean b) : Set (RealEuclidean n) :=
  {x | ∃ z : RealEuclidean q, h (realEuclideanAppend x z) = t}

/-- Canonical projection from a flat fiber to its visible-coordinate image. -/
def flatFiberToProjectedFiber {n q b : ℕ}
    (h : RealEuclidean (n + q) → RealEuclidean b)
    (t : RealEuclidean b) :
    h ⁻¹' {t} → flatProjectedFiberSet h t :=
  fun p ↦ ⟨realEuclideanTakeLeft p.1,
    realEuclideanTakeRight p.1, by
      rw [realEuclideanAppend_take]
      exact Set.mem_singleton_iff.mp p.2⟩

theorem continuous_flatFiberToProjectedFiber {n q b : ℕ}
    (h : RealEuclidean (n + q) → RealEuclidean b)
    (t : RealEuclidean b) :
    Continuous (flatFiberToProjectedFiber h t) := by
  apply Continuous.subtype_mk
  exact (realEuclideanTakeLeftContinuousLinearMap n q).continuous.comp
    continuous_subtype_val

theorem surjective_flatFiberToProjectedFiber {n q b : ℕ}
    (h : RealEuclidean (n + q) → RealEuclidean b)
    (t : RealEuclidean b) :
    Function.Surjective (flatFiberToProjectedFiber h t) := by
  rintro ⟨x, z, hz⟩
  refine ⟨⟨realEuclideanAppend x z, Set.mem_singleton_iff.mpr hz⟩, ?_⟩
  apply Subtype.ext
  simp [flatFiberToProjectedFiber]

theorem enatCard_connectedComponents_flatProjectedFiberSet_le
    {n q b : ℕ}
    (h : RealEuclidean (n + q) → RealEuclidean b)
    (t : RealEuclidean b) :
    ENat.card (ConnectedComponents (flatProjectedFiberSet h t)) ≤
      ENat.card (ConnectedComponents (h ⁻¹' {t})) := by
  exact enatCard_connectedComponents_le_of_continuous_surjective
    (continuous_flatFiberToProjectedFiber h t)
    (surjective_flatFiberToProjectedFiber h t)

/-- Uniform fiber finiteness for a family tuple immediately bounds every
visible-coordinate projection of its fibers. -/
theorem HasUniformFiberFiniteness.exists_flatProjectedFiber_component_bound
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hUFF : HasUniformFiberFiniteness G)
    {n q b : ℕ}
    (h : RealEuclidean (n + q) → RealEuclidean b)
    (hh : FunctionTupleInFamily G h) :
    ∃ N : ℕ, ∀ t,
      ENat.card (ConnectedComponents (flatProjectedFiberSet h t)) ≤ N := by
  obtain ⟨N, hN⟩ := hUFF (n + q) b h hh
  exact ⟨N, fun t ↦
    (enatCard_connectedComponents_flatProjectedFiberSet_le h t).trans (hN t)⟩

end AbelFormalization
