import AbelFormalization.SmoothFamilyConstantRankLocalFiber
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Connected interval produced by a fixed Jacobian minor

This is the purely topological final step in Wilkie's Corollary 2.9.  It
requires a zero and a nonzero point for the *same* minor in one preconnected
set.  `WilkieVerticalMinorMissingProjectionInterval` obtains that zero for
the final vertical-minor branch of 2.9 under an open target and a regular
value.  The finite-projection lemma is also purely topological.  Neither
result constructs the earlier arbitrary-minor and regular-slice steps.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A continuous real function on a preconnected set realizes the interval
between any zero and any positive value attained there. -/
theorem interval_image_of_preconnected_zero_positive
    {X : Type*} [TopologicalSpace X] {Y : Set X}
    (hY : IsPreconnected Y) {f : X → ℝ} (hf : ContinuousOn f Y)
    {z x : X} (hz : z ∈ Y) (hx : x ∈ Y)
    (hzero : f z = 0) (hpositive : 0 < f x) :
    ∃ η : ℝ, 0 < η ∧ Icc (0 : ℝ) η ⊆ f '' Y := by
  refine ⟨f x, hpositive, ?_⟩
  simpa only [hzero] using hY.intermediate_value hz hx hf

/-- A nonempty subset that is both relatively open and relatively closed
inside a preconnected target is the whole target.  In the fiber application,
the relative openness comes from the implicit-function chart and the relative
closedness from boundedness plus closedness of the fiber component. -/
theorem eq_of_nonempty_relatively_clopen_of_preconnected
    {X : Type*} [TopologicalSpace X] {U P : Set X}
    (hU : IsPreconnected U) (hsubset : P ⊆ U)
    (hnonempty : P.Nonempty)
    (hclosed : IsClosed (Subtype.val ⁻¹' P : Set U))
    (hopen : IsOpen (Subtype.val ⁻¹' P : Set U)) :
    P = U := by
  letI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  have hsubNonempty : (Subtype.val ⁻¹' P : Set U).Nonempty := by
    obtain ⟨x, hx⟩ := hnonempty
    exact ⟨⟨x, hsubset hx⟩, hx⟩
  have hsubEq : (Subtype.val ⁻¹' P : Set U) = Set.univ :=
    (isClopen_iff.mp ⟨hclosed, hopen⟩).resolve_left hsubNonempty.ne_empty
  apply Set.Subset.antisymm hsubset
  intro x hx
  have hxSub : (⟨x, hx⟩ : U) ∈ (Subtype.val ⁻¹' P : Set U) := by
    rw [hsubEq]
    trivial
  exact hxSub

/-- If a preconnected set meets an open set in a nonempty finite set, then
the whole preconnected set is that one point.  This is the purely topological
part of Wilkie's finite-visible-projection case: the component is allowed to
extend outside the open ball a priori. -/
theorem eq_singleton_of_preconnected_finite_inter_open
    {X : Type*} [TopologicalSpace X] [T1Space X]
    {K U : Set X} (hK : IsPreconnected K) (hUopen : IsOpen U)
    (hfinite : (K ∩ U).Finite) (hinter : (K ∩ U).Nonempty) :
    ∃ x : X, K = {x} := by
  have hpreimageEq :
      (Subtype.val ⁻¹' (K ∩ U) : Set K) =
        (Subtype.val ⁻¹' U : Set K) := by
    ext x
    simp [x.property]
  have hrelClosed : IsClosed (Subtype.val ⁻¹' (K ∩ U) : Set K) :=
    hfinite.isClosed.preimage continuous_subtype_val
  have hrelOpen : IsOpen (Subtype.val ⁻¹' (K ∩ U) : Set K) := by
    rw [hpreimageEq]
    exact hUopen.preimage continuous_subtype_val
  have hinterEq : K ∩ U = K :=
    eq_of_nonempty_relatively_clopen_of_preconnected hK
      inter_subset_left hinter hrelClosed hrelOpen
  have hKfinite : K.Finite := by
    simpa only [hinterEq] using hfinite
  have hKsubsingleton : K.Subsingleton :=
    (hK.isDiscrete_iff_subsingleton).mp hKfinite.isDiscrete
  obtain ⟨x, hxK, _⟩ := hinter
  exact ⟨x, hKsubsingleton.eq_singleton_of_mem hxK⟩

/-- If a fixed continuous determinant vanishes and is nonzero at points of
one preconnected set, its square takes all values in a positive initial
interval. -/
theorem squared_interval_image_of_preconnected_minor
    {X : Type*} [TopologicalSpace X] {Y : Set X}
    (hY : IsPreconnected Y) {d : X → ℝ} (hd : ContinuousOn d Y)
    {z x : X} (hz : z ∈ Y) (hx : x ∈ Y)
    (hzero : d z = 0) (hnonzero : d x ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ Icc (0 : ℝ) η ⊆ (fun y ↦ (d y) ^ 2) '' Y := by
  apply interval_image_of_preconnected_zero_positive hY (hd.pow 2) hz hx
  · simp [hzero]
  · exact sq_pos_of_ne_zero hnonzero

/-- The final interval step for one specified maximal column minor of a
globally `C¹` Euclidean map. -/
theorem squared_standardJacobianColumnMinor_interval
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) (cols : Fin b ↪ Fin a)
    {Y : Set (RealEuclidean a)} (hY : IsPreconnected Y)
    {z x : RealEuclidean a} (hz : z ∈ Y) (hx : x ∈ Y)
    (hzero : standardJacobianColumnMinor g cols z = 0)
    (hnonzero : standardJacobianColumnMinor g cols x ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ Icc (0 : ℝ) η ⊆
      (fun y ↦ (standardJacobianColumnMinor g cols y) ^ 2) '' Y := by
  have hcontinuous : Continuous (standardJacobianColumnMinor g cols) := by
    change Continuous
      (standardJacobianMinor g (Function.Embedding.refl (Fin b)) cols)
    exact continuous_standardJacobianMinor_of_contDiff_one hg
      (Function.Embedding.refl (Fin b)) cols
  exact squared_interval_image_of_preconnected_minor hY
    hcontinuous.continuousOn hz hx hzero hnonzero

/-- Wilkie's fixed-minor interval conclusion on a preconnected part of one
`C¹` level fiber.  The two point witnesses are explicit: this theorem does
not derive the vanishing point from boundedness or a missing projection. -/
theorem squared_standardJacobianColumnMinor_interval_on_levelFiber
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    (cols : Fin k ↪ Fin (n + k))
    {Y : Set (RealEuclidean (n + k))} (hY : IsPreconnected Y)
    (_hfiber : Y ⊆ F ⁻¹' {a})
    {z x : RealEuclidean (n + k)} (hz : z ∈ Y) (hx : x ∈ Y)
    (hzero : standardJacobianColumnMinor F cols z = 0)
    (hnonzero : standardJacobianColumnMinor F cols x ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ Icc (0 : ℝ) η ⊆
      (fun y ↦ (standardJacobianColumnMinor F cols y) ^ 2) '' Y := by
  exact squared_standardJacobianColumnMinor_interval hF cols hY
    hz hx hzero hnonzero

end AbelFormalization
