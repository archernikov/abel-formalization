import AbelFormalization.WilkieFixedMinorConnectedInterval
import AbelFormalization.ProjectedFiberComponents
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The bounded vertical-minor projection fork

The closed-image argument is proved from boundedness and relative closedness.
The final fork is conditional on *local projected neighborhoods* at points of
a fiber component where the fixed hidden-column minor is nonzero.  An IFT
chart for the square map `(visible projection, F)`, together with openness of
the component in the regular fiber, should discharge that local premise.
No openness of the projection of an arbitrary compact subset is assumed.

The result below records the closed-and-open projection fork, with local
openness stated as the precise additional IFT/component premise.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A component of `C ∩ W`, with `C` closed in the ambient space, is closed
relative to `W`.  The ambient closure of that component may include points
outside `W`; these are deliberately excluded by the intersection. -/
theorem closure_connectedComponentIn_inter_of_closed
    {E : Type*} [TopologicalSpace E] {C W : Set E}
    (hC : IsClosed C) {x : E} (hx : x ∈ C ∩ W) :
    closure (connectedComponentIn (C ∩ W) x) ∩ W ⊆
      connectedComponentIn (C ∩ W) x := by
  let X : Set E := C ∩ W
  let Y : Set E := connectedComponentIn X x
  have hYsubsetX : Y ⊆ X := connectedComponentIn_subset X x
  have hYclosedX : IsClosed (Subtype.val ⁻¹' Y : Set X) := by
    change IsClosed
      (Subtype.val ⁻¹' (connectedComponentIn X x) : Set X)
    rw [connectedComponentIn_eq_image hx]
    rw [Set.preimage_image_eq _ Subtype.coe_injective]
    exact isClosed_connectedComponent
  obtain ⟨D, hDclosed, hDimage⟩ := hYclosedX.image_val
  have hYsubsetD : Y ⊆ D := by
    intro y hyY
    have hyX : y ∈ X := hYsubsetX hyY
    have hyImage :
        y ∈ Subtype.val '' (Subtype.val ⁻¹' Y : Set X) :=
      ⟨⟨y, hyX⟩, hyY, rfl⟩
    rw [hDimage] at hyImage
    exact hyImage.1
  have hclosureD : closure Y ⊆ D := closure_minimal hYsubsetD hDclosed
  have hclosureC : closure Y ⊆ C :=
    closure_minimal (hYsubsetX.trans inter_subset_left) hC
  intro y hy
  have hyX : y ∈ X := ⟨hclosureC hy.1, hy.2⟩
  have hyImage : y ∈ Subtype.val '' (Subtype.val ⁻¹' Y : Set X) := by
    rw [hDimage]
    exact ⟨hclosureD hy.1, hyX⟩
  obtain ⟨z, hzY, rfl⟩ := hyImage
  exact hzY

/-- The image of a bounded set is closed relative to `U` when the set is
closed relative to the preimage of `U`.  The image of the compact ambient
closure is globally closed; relative closedness identifies its part in `U`
with the original image. -/
theorem relatively_closed_image_of_bounded_relatively_closed
    {E T : Type*} [MetricSpace E] [ProperSpace E]
    [TopologicalSpace T] [T2Space T]
    {p : E → T} (hp : Continuous p) {U : Set T} {Y : Set E}
    (hYbounded : Bornology.IsBounded Y)
    (hYrelative : closure Y ∩ p ⁻¹' U ⊆ Y) :
    IsClosed (Subtype.val ⁻¹' (p '' Y) : Set U) := by
  have hcompact : IsCompact (p '' closure Y) :=
    hYbounded.isCompact_closure.image hp
  have hpreimageEq :
      (Subtype.val ⁻¹' (p '' Y) : Set U) =
        (Subtype.val ⁻¹' (p '' closure Y) : Set U) := by
    ext v
    constructor
    · rintro ⟨y, hyY, hpy⟩
      exact ⟨y, subset_closure hyY, hpy⟩
    · rintro ⟨y, hyClosure, hpy⟩
      have hyU : y ∈ p ⁻¹' U := by
        change p y ∈ U
        rw [hpy]
        exact v.property
      exact ⟨y, hYrelative ⟨hyClosure, hyU⟩, hpy⟩
  rw [hpreimageEq]
  exact hcompact.isClosed.preimage continuous_subtype_val

/-- Local projected neighborhoods contained in a set's image make that
image relatively open.  This is the exact output needed from an IFT chart
after a fiber component is known to contain a fiber-open neighborhood. -/
theorem relatively_open_image_of_local_projected_neighborhoods
    {E T : Type*} [TopologicalSpace E] [TopologicalSpace T]
    {p : E → T} {U : Set T} {Y : Set E}
    (hlocal : ∀ y ∈ Y, ∃ V : Set T,
      IsOpen (Subtype.val ⁻¹' V : Set U) ∧
        p y ∈ V ∧ V ∩ U ⊆ p '' Y) :
    IsOpen (Subtype.val ⁻¹' (p '' Y) : Set U) := by
  apply isOpen_iff_mem_nhds.mpr
  intro v hv
  obtain ⟨y, hyY, hpy⟩ := hv
  obtain ⟨V, hVopen, hyV, hVsubset⟩ := hlocal y hyY
  have hvV : v ∈ (Subtype.val ⁻¹' V : Set U) := by
    change (v : T) ∈ V
    rw [← hpy]
    exact hyV
  have hVsubsetImage :
      (Subtype.val ⁻¹' V : Set U) ⊆
        (Subtype.val ⁻¹' (p '' Y) : Set U) := by
    intro w hw
    exact hVsubset ⟨hw, w.property⟩
  exact Filter.mem_of_superset (hVopen.mem_nhds hvV) hVsubsetImage

/-- The bounded part of a flat level fiber lying over a visible target set. -/
def wilkieFiberOver {n k : ℕ}
    (F : RealEuclidean (n + k) → RealEuclidean k)
    (a : RealEuclidean k) (U : Set (RealEuclidean n)) :
    Set (RealEuclidean (n + k)) :=
  F ⁻¹' {a} ∩ realEuclideanTakeLeft ⁻¹' U

/-- A component of the restricted fiber, not of the full level fiber. -/
def wilkieFiberComponent {n k : ℕ}
    (F : RealEuclidean (n + k) → RealEuclidean k)
    (a : RealEuclidean k) (U : Set (RealEuclidean n))
    (x : RealEuclidean (n + k)) : Set (RealEuclidean (n + k)) :=
  connectedComponentIn (wilkieFiberOver F a U) x

/-- Safe conditional vertical-minor fork.  A local IFT chart plus openness of
the connected component should produce `hlocal`, a neighborhood in `U`
contained in the projection of that component.  The closed-image half and
the connected-target conclusion are proved here from the stated `C¹`,
boundedness, and component premises. -/
theorem wilkieVerticalMinor_component_projection_eq_of_localOpen
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    {U : Set (RealEuclidean n)} (hU : IsPreconnected U)
    (hregular : ∀ y, F y = a →
      Function.Surjective (fderiv ℝ F y))
    (hbounded : Bornology.IsBounded (wilkieFiberOver F a U))
    {x : RealEuclidean (n + k)}
    (hx : x ∈ wilkieFiberOver F a U)
    (hminor : ∀ y ∈ wilkieFiberComponent F a U x,
      standardJacobianColumnMinor F (Fin.natAddEmb n) y ≠ 0)
    (hlocal : ∀ y ∈ wilkieFiberComponent F a U x,
      Function.Surjective (fderiv ℝ F y) →
      standardJacobianColumnMinor F (Fin.natAddEmb n) y ≠ 0 →
      ∃ V : Set (RealEuclidean n),
        IsOpen (Subtype.val ⁻¹' V : Set U) ∧
          realEuclideanTakeLeft y ∈ V ∧
          V ∩ U ⊆ realEuclideanTakeLeft ''
            wilkieFiberComponent F a U x) :
    realEuclideanTakeLeft '' wilkieFiberComponent F a U x = U := by
  let p : RealEuclidean (n + k) → RealEuclidean n :=
    fun y ↦ realEuclideanTakeLeft y
  let C : Set (RealEuclidean (n + k)) := F ⁻¹' {a}
  let W : Set (RealEuclidean (n + k)) := p ⁻¹' U
  let X : Set (RealEuclidean (n + k)) := C ∩ W
  let Y : Set (RealEuclidean (n + k)) := connectedComponentIn X x
  have hp : Continuous p := by
    change Continuous (realEuclideanTakeLeftContinuousLinearMap n k)
    exact (realEuclideanTakeLeftContinuousLinearMap n k).continuous
  have hCclosed : IsClosed C :=
    isClosed_singleton.preimage hF.continuous
  have hxX : x ∈ X := by
    simpa only [X, C, W, p, wilkieFiberOver] using hx
  have hYsubsetX : Y ⊆ X := connectedComponentIn_subset X x
  have hYbounded : Bornology.IsBounded Y := by
    apply hbounded.subset
    simpa only [Y, X, C, W, p, wilkieFiberOver] using hYsubsetX
  have hYrelative : closure Y ∩ p ⁻¹' U ⊆ Y := by
    simpa only [Y, X, C, W] using
      (closure_connectedComponentIn_inter_of_closed hCclosed hxX)
  have hclosed : IsClosed (Subtype.val ⁻¹' (p '' Y) : Set U) :=
    relatively_closed_image_of_bounded_relatively_closed hp
      hYbounded hYrelative
  have hYimageSubset : p '' Y ⊆ U := by
    rintro v ⟨y, hyY, rfl⟩
    exact (hYsubsetX hyY).2
  have hopen : IsOpen (Subtype.val ⁻¹' (p '' Y) : Set U) := by
    apply relatively_open_image_of_local_projected_neighborhoods
    intro y hyY
    have hyFiber : F y = a := by
      have hyC : y ∈ C := (hYsubsetX hyY).1
      exact hyC
    have hyRegular : Function.Surjective (fderiv ℝ F y) :=
      hregular y hyFiber
    have hyMinor :
        standardJacobianColumnMinor F (Fin.natAddEmb n) y ≠ 0 :=
      hminor y (by simpa only [Y, X, C, W, p,
        wilkieFiberComponent, wilkieFiberOver] using hyY)
    simpa only [p, Y, X, C, W,
      wilkieFiberComponent, wilkieFiberOver] using
      (hlocal y (by simpa only [Y, X, C, W, p,
        wilkieFiberComponent, wilkieFiberOver] using hyY)
        hyRegular hyMinor)
  have hYimageNonempty : (p '' Y).Nonempty :=
    ⟨p x, ⟨x, mem_connectedComponentIn hxX, rfl⟩⟩
  have hresult : p '' Y = U :=
    eq_of_nonempty_relatively_clopen_of_preconnected hU
      hYimageSubset hYimageNonempty hclosed hopen
  simpa only [p, Y, X, C, W,
    wilkieFiberComponent, wilkieFiberOver] using hresult

end AbelFormalization
