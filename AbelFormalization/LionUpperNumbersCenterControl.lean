import AbelFormalization.CountableSardAvoidance
import AbelFormalization.LionUniformPreimageReduction
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Topology.Separation.Hausdorff

/-!
# Khovanskii's center-control lemma

This file proves the local part of the upper-number argument left explicit in
`LionUniformPreimageReduction`.  For a globally `C¹` square map, an upper
number of nearby regular preimages also bounds the nondegenerate preimages at
the center.

Given `N + 1` nondegenerate preimages of the center, separate them by pairwise
disjoint open source neighborhoods.  The inverse function theorem maps each
neighborhood onto an open neighborhood of the center.  Their finite
intersection contains a regular value, because the critical-value set has
Lebesgue measure zero.  That regular value then has `N + 1` distinct
preimages, contradicting the upper number.
-/

noncomputable section

open Set Function MeasureTheory
open scoped MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Finite selections from an extended-cardinal inequality -/

/-- If the extended cardinal of a type is not at most `N`, the type contains
`N + 1` distinct elements. -/
theorem exists_fin_succ_injection_of_enatCard_not_le_lion
    {α : Type*} {N : ℕ} (h : ¬ ENat.card α ≤ (N : ℕ∞)) :
    ∃ f : Fin (N + 1) → α, Function.Injective f := by
  have hlt : (N : ℕ∞) < ENat.card α := lt_of_not_ge h
  have hsucc : (N + 1 : ℕ∞) ≤ ENat.card α := by
    rw [ENat.natCast_add_one_le_iff]
    exact hlt
  have hcard : ((N + 1 : ℕ) : Cardinal) ≤ Cardinal.mk α := by
    exact Cardinal.natCast_le_toENat.mp hsucc
  obtain ⟨f⟩ : Nonempty (Fin (N + 1) ↪ α) := by
    rw [← Cardinal.lift_mk_le']
    simpa using hcard
  exact ⟨f, f.injective⟩

/-! ## One local inverse branch -/

/-- A nondegenerate preimage of `u` supplies, inside every open neighborhood
of that preimage, a preimage branch over an open neighborhood of `u`. -/
theorem exists_open_target_preimages_in_of_contDiff_of_surjective_fderiv
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) {x u : RealEuclidean n}
    (hxu : F x = u) (hsurj : Function.Surjective (fderiv ℝ F x))
    {U : Set (RealEuclidean n)} (hUopen : IsOpen U) (hxU : x ∈ U) :
    ∃ W : Set (RealEuclidean n), IsOpen W ∧ u ∈ W ∧
      ∀ v ∈ W, ∃ y ∈ U, F y = v := by
  let D : RealEuclidean n →L[ℝ] RealEuclidean n := fderiv ℝ F x
  have hinj : Function.Injective D :=
    continuousLinearMap_injective_of_surjective_of_finrank_eq
      D rfl hsurj
  have hker : D.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrange : D.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  let e : RealEuclidean n ≃L[ℝ] RealEuclidean n :=
    ContinuousLinearEquiv.ofBijective D hker hrange
  have heD : (e : RealEuclidean n →L[ℝ] RealEuclidean n) = D :=
    ContinuousLinearEquiv.coe_ofBijective D hker hrange
  have hderiv : HasFDerivAt F (e : RealEuclidean n →L[ℝ] RealEuclidean n) x := by
    rw [heD]
    exact hF.contDiffAt.differentiableAt_one.hasFDerivAt
  let chart : OpenPartialHomeomorph (RealEuclidean n) (RealEuclidean n) :=
    hF.contDiffAt.toOpenPartialHomeomorph F hderiv (by norm_num)
  have hxsource : x ∈ chart.source :=
    hF.contDiffAt.mem_toOpenPartialHomeomorph_source hderiv (by norm_num)
  let W : Set (RealEuclidean n) := F '' (chart.source ∩ U)
  refine ⟨W, ?_, ?_, ?_⟩
  · exact chart.isOpen_image_source_inter hUopen
  · exact ⟨x, ⟨hxsource, hxU⟩, hxu⟩
  · intro v hv
    obtain ⟨y, hy, hyv⟩ := hv
    exact ⟨y, hy.2, hyv⟩

/-! ## Critical values -/

/-- The critical values of a globally `C¹` square Euclidean map have zero
Lebesgue measure. -/
theorem volume_criticalValues_eq_zero_of_contDiff
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) :
    (volume : Measure (RealEuclidean n))
        (F '' {x | ¬ Function.Surjective (fderiv ℝ F x)}) = 0 := by
  apply addHaar_image_criticalSet_eq_zero
    (volume : Measure (RealEuclidean n))
  · intro x _
    exact hF.differentiable_one.differentiableAt
  · intro x hx
    have hker : (fderiv ℝ F x).ker ≠ ⊥ := by
      intro hker
      have hinj : Function.Injective (fderiv ℝ F x) :=
        LinearMap.ker_eq_bot.mp hker
      have hsurj : Function.Surjective (fderiv ℝ F x) :=
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
      exact hx hsurj
    exact LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker

/-! ## Khovanskii's local center control -/

/-- For a globally `C¹` square map, every local upper number controls the
nondegenerate preimages at its center. -/
theorem upperNumbersControlNondegeneratePreimages_of_contDiff
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F) :
    UpperNumbersControlNondegeneratePreimages F := by
  intro u N hupper
  by_contra hnot
  obtain ⟨selected, hselected⟩ :=
    exists_fin_succ_injection_of_enatCard_not_le_lion hnot

  let point : Fin (N + 1) → RealEuclidean n := fun i ↦ selected i
  have hpoint : Function.Injective point := by
    intro i j hij
    exact hselected (Subtype.ext hij)
  have hpointFinite : (Set.range point).Finite := Set.finite_range point
  obtain ⟨U, hUopen, hUdisj⟩ := hpointFinite.t2_separation

  have hbranch (i : Fin (N + 1)) :
      ∃ W : Set (RealEuclidean n), IsOpen W ∧ u ∈ W ∧
        ∀ v ∈ W, ∃ y ∈ U (point i), F y = v := by
    exact exists_open_target_preimages_in_of_contDiff_of_surjective_fderiv
      hF (selected i).property.1 (selected i).property.2
      (hUopen (point i)).2 (hUopen (point i)).1
  choose W hWopen huW hWpreimage using hbranch

  obtain ⟨V, hVopen, huV, hVbound⟩ := hupper
  let O : Set (RealEuclidean n) := V ∩ ⋂ i, W i
  have hOopen : IsOpen O :=
    hVopen.inter (isOpen_iInter_of_finite hWopen)
  have huO : u ∈ O := by
    refine ⟨huV, Set.mem_iInter.mpr ?_⟩
    exact huW
  have hcriticalNull :
      (volume : Measure (RealEuclidean n))
          (F '' {x | ¬ Function.Surjective (fderiv ℝ F x)}) = 0 :=
    volume_criticalValues_eq_zero_of_contDiff hF
  have hO_not_subset :
      ¬ O ⊆ F '' {x | ¬ Function.Surjective (fderiv ℝ F x)} := by
    intro hsubset
    have hOnull : (volume : Measure (RealEuclidean n)) O = 0 :=
      measure_mono_null hsubset hcriticalNull
    exact hOopen.measure_ne_zero volume ⟨u, huO⟩ hOnull
  obtain ⟨v, hvO, hvregularImage⟩ := Set.not_subset.mp hO_not_subset
  have hvregular : IsRegularTargetValue F v := by
    intro x hx
    by_contra hxnonsurj
    exact hvregularImage ⟨x, hxnonsurj, hx⟩

  have hvW (i : Fin (N + 1)) : v ∈ W i :=
    Set.mem_iInter.mp hvO.2 i
  choose preimage hpreimageU hpreimageEq using
    fun i ↦ hWpreimage i v (hvW i)
  let lifted : Fin (N + 1) → F ⁻¹' {v} := fun i ↦
    ⟨preimage i, by simpa using hpreimageEq i⟩
  have hlifted : Function.Injective lifted := by
    intro i j hij
    by_contra hijIndex
    have hpointNe : point i ≠ point j := fun h ↦ hijIndex (hpoint h)
    have hdisjoint : Disjoint (U (point i)) (U (point j)) :=
      hUdisj (Set.mem_range_self i) (Set.mem_range_self j) hpointNe
    have hpreimagePoint : preimage i = preimage j :=
      congrArg Subtype.val hij
    have hpreimageUj' : preimage i ∈ U (point j) := by
      rw [hpreimagePoint]
      exact hpreimageU j
    exact (Set.disjoint_left.mp hdisjoint)
      (hpreimageU i) hpreimageUj'

  have hlower : (N + 1 : ℕ∞) ≤ ENat.card (F ⁻¹' {v}) := by
    simpa using ENat.card_le_card_of_injective hlifted
  have hupperAtV : ENat.card (F ⁻¹' {v}) ≤ (N : ℕ∞) :=
    hVbound v hvO.1 hvregular
  have hcontra : (N + 1 : ℕ∞) ≤ (N : ℕ∞) :=
    hlower.trans hupperAtV
  have : N + 1 ≤ N := ENat.natCast_le_natCast.mp hcontra
  omega

/-- Consequently the center-control premise in the fixed-map Gabrielov
reduction is automatic for every globally `C¹` square map. -/
theorem hasUniformRegularFiberBound_of_gabrielovUpperNumbers_of_contDiff
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F)
    (hupper : HasGabrielovUniformUpperNumberProperty F) :
    HasUniformRegularFiberBound F :=
  hasUniformRegularFiberBound_of_gabrielovUpperNumbers hF
    (upperNumbersControlNondegeneratePreimages_of_contDiff hF) hupper

/-- Family-level form: smoothness discharges Khovanskii's center-control
step, so Gabrielov's uniform upper-number property for every square family
tuple is the sole remaining premise for uniform regular-fiber bounds. -/
theorem hasUniformSquareRegularFiberBound_of_gabrielovUpperNumbers
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hupper : ∀ n (F : RealEuclidean n → RealEuclidean n),
      FunctionTupleInFamily G F →
        HasGabrielovUniformUpperNumberProperty F) :
    HasUniformSquareRegularFiberBound G := by
  intro n F hFmem
  have hF : ContDiff ℝ 1 F := by
    rw [contDiff_pi]
    intro i
    exact (hsmooth n (fun x ↦ F x i) (hFmem i)).of_le (by simp)
  exact hasUniformRegularFiberBound_of_gabrielovUpperNumbers_of_contDiff
    hF (hupper n F hFmem)

end AbelFormalization
