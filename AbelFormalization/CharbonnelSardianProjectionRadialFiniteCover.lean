import AbelFormalization.CharbonnelSardianProjectionRadialWS5Levels
import Mathlib.Topology.Closure

/-!
# Wilkie 3.10: finite visible-cover localization of radial accumulation

This module isolates one handoff in the positive-projection
Sardian constructor. If a fixed old tuple fiber has radial reciprocal values
accumulating at zero and its visible base is covered by finitely many members
of the literal-zero Charbonnel closure, one cover member inherits accumulation.
The maintained WS5 radial-level theorem then supplies every small positive
last parameter on that member.

The finite weak-family cover and global accumulation are explicit hypotheses.
They must be supplied by the boundary-point localization in Wilkie 3.10. This
file does not prove the projection constructor, uniform fiber finiteness, or
the manuscript's main theorem.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A finite cover localizes accumulation of an image at a point to one
member of the cover. This uses mathlib's finite-union closure identity. -/
theorem exists_image_cover_member_closure
    {X Y : Type*} [TopologicalSpace Y]
    {ι : Type*} (I : Finset ι) (S : Set X)
    (U : ι → Set X) (f : X → Y) (y : Y)
    (hcover : S ⊆ ⋃ i ∈ I, U i)
    (hclosure : y ∈ closure (f '' S)) :
    ∃ i ∈ I, y ∈ closure (f '' (S ∩ U i)) := by
  have himage : f '' S ⊆ ⋃ i ∈ I, f '' (S ∩ U i) := by
    rintro z ⟨x, hxS, rfl⟩
    obtain ⟨i, hiI, hxi⟩ := Set.mem_iUnion₂.mp (hcover hxS)
    exact Set.mem_iUnion₂.mpr ⟨i, hiI, x, ⟨hxS, hxi⟩, rfl⟩
  have hfinite : y ∈ ⋃ i ∈ I, closure (f '' (S ∩ U i)) := by
    rw [← I.closure_biUnion]
    exact closure_mono himage hclosure
  obtain ⟨i, hiI, hiClosure⟩ := Set.mem_iUnion₂.mp hfinite
  exact ⟨i, hiI, hiClosure⟩

/-- The scalar image definition is exactly the image of the old fixed fiber
under its reciprocal-radial function. -/
theorem sardianProjectionRadialValueImage_coordinate_eq_image
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1)) :
    realEuclideanOneCoordinateImage
        (sardianProjectionRadialValueImage old U e) =
      sardianProjectionRadialReciprocal n q ''
        sardianProjectionOldTupleFiber old U e := by
  ext t
  constructor
  · rintro ⟨w, ⟨v, hv, hwv⟩, hwt⟩
    exact ⟨v, hv, hwv.symm.trans hwt⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨(fun _ : Fin 1 ↦ sardianProjectionRadialReciprocal n q v), ?_, rfl⟩
    exact ⟨v, hv, rfl⟩

/-- Wilkie 3.10's finite-ball pigeonhole step, with the two source inputs
visible. The chosen ball is in the actual weak-family closure, so the
maintained WS5 radial-level theorem applies without a definability assumption. -/
theorem exists_finiteCover_radial_projected_small_levels
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (e : RealEuclidean (q + 1)) (hepos : ∀ i, 0 < e i)
    {ι : Type*} (I : Finset ι) (balls : ι → Set (RealEuclidean n))
    (hcover : U ⊆ ⋃ i ∈ I, balls i)
    (hballs : ∀ i ∈ I,
      balls i ∈ charbonnelClosure (literalZeroSetFamily G) n)
    (hzero : (0 : ℝ) ∈ closure
      (realEuclideanOneCoordinateImage
        (sardianProjectionRadialValueImage old U e))) :
    ∃ i ∈ I, ∃ η : ℝ, 0 < η ∧
      ∀ t : ℝ, 0 < t → t < η →
        ∃ x ∈ balls i,
          realEuclideanAppend x (charbonnelAppendLastParameter e t) ∈
            (sardianProjectionAlgebraicFamily
              hG hsmooth hderiv hn old).carrier := by
  let S := sardianProjectionOldTupleFiber old U e
  let f := sardianProjectionRadialReciprocal n q
  let V : ι → Set (RealEuclidean (n + (q + 1))) :=
    fun i ↦ {v | realEuclideanTakeLeft v ∈ balls i}
  have hcoverS : S ⊆ ⋃ i ∈ I, V i := by
    intro v hv
    obtain ⟨i, hiI, hvi⟩ := Set.mem_iUnion₂.mp (hcover hv.1)
    exact Set.mem_iUnion₂.mpr ⟨i, hiI, hvi⟩
  have hzeroS : (0 : ℝ) ∈ closure (f '' S) := by
    simpa only [S, f,
      sardianProjectionRadialValueImage_coordinate_eq_image] using hzero
  obtain ⟨i, hiI, hzeroLocal⟩ :=
    exists_image_cover_member_closure I S V f 0 hcoverS hzeroS
  have hsubsetLocal :
      f '' (S ∩ V i) ⊆
        realEuclideanOneCoordinateImage
          (sardianProjectionRadialValueImage old (balls i) e) := by
    rw [sardianProjectionRadialValueImage_coordinate_eq_image]
    rintro t ⟨v, ⟨hvS, hvV⟩, rfl⟩
    refine ⟨v, ?_, rfl⟩
    exact ⟨hvV, hvS.2⟩
  have hzeroBall : (0 : ℝ) ∈ closure
      (realEuclideanOneCoordinateImage
        (sardianProjectionRadialValueImage old (balls i) e)) :=
    closure_mono hsubsetLocal hzeroLocal
  obtain ⟨η, hη, hlevels⟩ :=
    sardianProjectionRadialValueImage_projectedFamily_all_small_levels
      hG hsmooth hderiv hUFF hn old (balls i) (hballs i hiI)
        e hepos hzeroBall
  exact ⟨i, hiI, η, hη, hlevels⟩

end AbelFormalization
