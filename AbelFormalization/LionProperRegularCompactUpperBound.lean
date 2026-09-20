import AbelFormalization.LionUpperNumbersCenterControl
import AbelFormalization.LionProperRegularFiberFinite
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper regular fibers have locally bounded full cardinality

The compact-target conclusion applies only to compact sets consisting of
regular values. It does not assert the Gabrielov upper-number property at
singular centers or a bound across the unbounded full target space.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- An invertible derivative gives an open source patch on which the fixed
square map is injective. -/
private theorem exists_open_injective_chart_at_regular_preimage
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) {x : RealEuclidean n}
    (hsurj : Function.Surjective (fderiv ℝ F x)) :
    ∃ U : Set (RealEuclidean n), IsOpen U ∧ x ∈ U ∧ InjOn F U := by
  let D : RealEuclidean n →L[ℝ] RealEuclidean n := fderiv ℝ F x
  have hinj : Function.Injective D :=
    continuousLinearMap_injective_of_surjective_of_finrank_eq D rfl hsurj
  have hker : D.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrange : D.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  let e : RealEuclidean n ≃L[ℝ] RealEuclidean n :=
    ContinuousLinearEquiv.ofBijective D hker hrange
  have heD : (e : RealEuclidean n →L[ℝ] RealEuclidean n) = D :=
    ContinuousLinearEquiv.coe_ofBijective D hker hrange
  have hderiv : HasFDerivAt F
      (e : RealEuclidean n →L[ℝ] RealEuclidean n) x := by
    rw [heD]
    exact hF.contDiffAt.differentiableAt_one.hasFDerivAt
  let chart : OpenPartialHomeomorph (RealEuclidean n) (RealEuclidean n) :=
    hF.contDiffAt.toOpenPartialHomeomorph F hderiv (by norm_num)
  refine ⟨chart.source, chart.open_source, ?_, ?_⟩
  · exact hF.contDiffAt.mem_toOpenPartialHomeomorph_source hderiv (by norm_num)
  · exact chart.injOn

/-- At a regular finite fiber of a proper smooth square map, a whole open
target neighborhood has full fibers bounded by the center fiber's size.
The nearby target values need not themselves be regular. -/
theorem exists_open_fullFiber_bound_of_proper_regular_center
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) (hproper : IsProperMap F)
    {u : RealEuclidean n} (hregular : IsRegularTargetValue F u)
    (hfinite : (F ⁻¹' {u}).Finite) :
    ∃ N : ℕ, ∃ W : Set (RealEuclidean n),
      IsOpen W ∧ u ∈ W ∧
        ∀ v ∈ W, ENat.card (F ⁻¹' {v}) ≤ N := by
  classical
  letI : Finite (F ⁻¹' {u}) := Set.finite_coe_iff.mpr hfinite
  have hcharts : ∀ x : F ⁻¹' {u},
      ∃ U : Set (RealEuclidean n), IsOpen U ∧ (x : RealEuclidean n) ∈ U ∧
        InjOn F U := by
    intro x
    have hxvalue : F (x : RealEuclidean n) = u := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using x.property
    exact exists_open_injective_chart_at_regular_preimage hF
      (hregular x hxvalue)
  choose U hUopen hxU hUinj using hcharts
  let Uall : Set (RealEuclidean n) := ⋃ x : F ⁻¹' {u}, U x
  have hUallOpen : IsOpen Uall := isOpen_iUnion fun x ↦ hUopen x
  have hcoverCenter : ∀ y : RealEuclidean n, F y = u → y ∈ Uall := by
    intro y hy
    let yy : F ⁻¹' {u} := ⟨y, by simpa only [Set.mem_preimage,
      Set.mem_singleton_iff] using hy⟩
    exact Set.mem_iUnion.mpr ⟨yy, hxU yy⟩
  let W : Set (RealEuclidean n) := (F '' Uallᶜ)ᶜ
  have hWopen : IsOpen W :=
    (hproper.isClosedMap Uallᶜ hUallOpen.isClosed_compl).isOpen_compl
  have huW : u ∈ W := by
    change u ∉ F '' Uallᶜ
    intro hu
    obtain ⟨y, hyoutside, hyvalue⟩ := hu
    exact hyoutside (hcoverCenter y hyvalue)
  let N : ℕ := Nat.card (F ⁻¹' {u})
  refine ⟨N, W, hWopen, huW, ?_⟩
  intro v hvW
  have hvOutside : v ∉ F '' Uallᶜ := hvW
  have hSome : ∀ y : F ⁻¹' {v},
      ∃ x : F ⁻¹' {u}, (y : RealEuclidean n) ∈ U x := by
    intro y
    have hyvalue : F (y : RealEuclidean n) = v := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using y.property
    have hyUall : (y : RealEuclidean n) ∈ Uall := by
      by_contra hyoutside
      exact hvOutside ⟨y, by simpa only [Set.mem_compl_iff] using hyoutside,
        hyvalue⟩
    exact Set.mem_iUnion.mp hyUall
  choose assign hassign using hSome
  have hassignInj : Function.Injective assign := by
    intro y z hyz
    apply Subtype.ext
    have hzU : (z : RealEuclidean n) ∈ U (assign y) := by
      simpa only [hyz] using hassign z
    have hyvalue : F (y : RealEuclidean n) = v := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using y.property
    have hzvalue : F (z : RealEuclidean n) = v := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using z.property
    exact hUinj (assign y) (hassign y) hzU (hyvalue.trans hzvalue.symm)
  have hcard : ENat.card (F ⁻¹' {v}) ≤ ENat.card (F ⁻¹' {u}) :=
    ENat.card_le_card_of_injective hassignInj
  simpa only [N, ENat.card_eq_coe_natCard] using hcard

/-- Properness and a finite regular center supply Khovanskii's local upper
number, by a stronger bound that also counts singular nearby fibers. -/
theorem hasUpperNumberOfPreimagesAt_of_proper_regular_center
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) (hproper : IsProperMap F)
    {u : RealEuclidean n} (hregular : IsRegularTargetValue F u)
    (hfinite : (F ⁻¹' {u}).Finite) :
    ∃ N : ℕ, HasUpperNumberOfPreimagesAt F u N := by
  obtain ⟨N, W, hWopen, huW, hWbound⟩ :=
    exists_open_fullFiber_bound_of_proper_regular_center
      hF hproper hregular hfinite
  refine ⟨N, W, hWopen, huW, ?_⟩
  intro v hvW _
  exact hWbound v hvW

/-- A compact collection of regular target values has one full-fiber bound.
The explicit pointwise finiteness premise can later be discharged from
properness, compact fibers, inverse-function charts, and discreteness. -/
theorem exists_uniform_preimage_bound_on_compact_regular_targets
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) (hproper : IsProperMap F)
    {K : Set (RealEuclidean n)} (hK : IsCompact K)
    (hregular : ∀ u ∈ K, IsRegularTargetValue F u)
    (hfinite : ∀ u ∈ K, (F ⁻¹' {u}).Finite) :
    ∃ N : ℕ, ∀ u ∈ K, ENat.card (F ⁻¹' {u}) ≤ N := by
  classical
  have hlocal : ∀ u : K,
      ∃ N : ℕ, ∃ W : Set (RealEuclidean n),
        IsOpen W ∧ (u : RealEuclidean n) ∈ W ∧
          ∀ v ∈ W, ENat.card (F ⁻¹' {v}) ≤ N := by
    intro u
    exact exists_open_fullFiber_bound_of_proper_regular_center
      hF hproper (hregular u u.property) (hfinite u u.property)
  choose bound neighborhood hopen hcenter hnear using hlocal
  have hcover : K ⊆ ⋃ u : K, neighborhood u := by
    intro v hv
    exact Set.mem_iUnion.mpr ⟨⟨v, hv⟩, hcenter ⟨v, hv⟩⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover neighborhood hopen hcover
  let N : ℕ := T.sup bound
  refine ⟨N, ?_⟩
  intro v hv
  obtain ⟨u, huT, hvU⟩ := Set.mem_iUnion₂.mp (hT hv)
  exact (hnear u v hvU).trans
    (ENat.natCast_le_natCast.mpr (Finset.le_sup (f := bound) huT))

/-- Properness and a regular target supply the local upper number without
assuming pointwise fiber finiteness separately. -/
theorem hasUpperNumberOfPreimagesAt_of_proper_regular_target
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) (hproper : IsProperMap F)
    {u : RealEuclidean n} (hregular : IsRegularTargetValue F u) :
    ∃ N : ℕ, HasUpperNumberOfPreimagesAt F u N :=
  hasUpperNumberOfPreimagesAt_of_proper_regular_center
    hF hproper hregular
    (finite_fullFiber_of_proper_regular_target hF hproper hregular)

/-- Properness alone discharges the pointwise finite-fiber premise when
all targets in the compact set are regular. -/
theorem exists_uniform_preimage_bound_on_compact_regular_targets_of_proper
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) (hproper : IsProperMap F)
    {K : Set (RealEuclidean n)} (hK : IsCompact K)
    (hregular : ∀ u ∈ K, IsRegularTargetValue F u) :
    ∃ N : ℕ, ∀ u ∈ K, ENat.card (F ⁻¹' {u}) ≤ N :=
  exists_uniform_preimage_bound_on_compact_regular_targets
    hF hproper hK hregular
    (fun u hu ↦ finite_fullFiber_of_proper_regular_target
      hF hproper (hregular u hu))

end AbelFormalization
