import AbelFormalization.ParametricImplicitChart
import AbelFormalization.RectangularMorseSard

/-!
# Rectangular parametric regular slices

A joint submersion `Phi : X × Y → Z` has, near each point of a fixed level,
a smooth implicit chart whose source is the kernel of `d Phi`.  When
`dim Z ≤ dim X`, that kernel has dimension at least `dim Y`.  Rectangular
Morse--Sard applied to the chart projection therefore selects a parameter
whose fixed-parameter slice is regular at every point of the level.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped Topology ContDiff MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-- Rectangular Morse--Sard is local on an open source set for smooth maps. -/
theorem volume_image_rectangularCriticalSource_inter_open_eq_zero_of_contDiffOn_top
    {a b : ℕ} (hba : b ≤ a)
    {f : RealEuclidean a → RealEuclidean b}
    {W : Set (RealEuclidean a)} (hWopen : IsOpen W)
    (hf : ContDiffOn ℝ ∞ f W) :
    volume (f '' (rectangularCriticalSource f ∩ W)) = 0 := by
  let S : Set (RealEuclidean a) := rectangularCriticalSource f ∩ W
  let r : ℕ := morseSardElementaryOrder a
  have hlocal : ∀ u ∈ W, ∃ N : Set (RealEuclidean a),
      IsOpen N ∧ u ∈ N ∧
        volume (f '' (rectangularCriticalSource f ∩ N)) = 0 := by
    intro u huW
    have hfuTop : ContDiffAt ℝ ∞ f u :=
      (hf u huW).contDiffAt (hWopen.mem_nhds huW)
    have hfu : ContDiffAt ℝ r f u := hfuTop.of_le (by simp)
    obtain ⟨f', hf', heq⟩ :=
      exists_contDiff_eventuallyEq_of_contDiffAt hfu
    have hgood : {y | y ∈ W ∧ f' y = f y} ∈ 𝓝 u := by
      filter_upwards [hWopen.mem_nhds huW, heq]
        with y hyW hyEq
      exact ⟨hyW, hyEq⟩
    let N : Set (RealEuclidean a) :=
      interior {y | y ∈ W ∧ f' y = f y}
    have hNopen : IsOpen N := isOpen_interior
    have huN : u ∈ N := mem_interior_iff_mem_nhds.mpr hgood
    have himage : f '' (rectangularCriticalSource f ∩ N) ⊆
        standardJacobianCriticalValueSet f' := by
      rintro z ⟨y, hy, rfl⟩
      have hyGood := interior_subset hy.2
      have hlocalEq : f' =ᶠ[𝓝 y] f := by
        filter_upwards [hNopen.mem_nhds hy.2] with w hw
        exact (interior_subset hw).2
      have hderivEq : fderiv ℝ f' y = fderiv ℝ f y :=
        hlocalEq.fderiv_eq
      have hf'Diff : Differentiable ℝ f' :=
        hf'.differentiable (by
          dsimp only [r]
          exact_mod_cast (morseSardElementaryOrder_pos a).ne')
      rw [← rectangularCriticalValues_eq_standardJacobianCriticalValueSet
        hf'Diff]
      refine ⟨y, ?_, hyGood.2⟩
      change ¬Function.Surjective (fderiv ℝ f' y)
      rw [hderivEq]
      exact hy.1
    refine ⟨N, hNopen, huN, measure_mono_null himage ?_⟩
    exact volume_standardJacobianCriticalValueSet_eq_zero_of_elementaryOrder
      hba hf'
  choose N hNopen huN hNzero using
    fun p : S => hlocal p p.property.2
  let O : S → Set S := fun p => Subtype.val ⁻¹' N p
  have hO : ∀ p : S, O p ∈ 𝓝 p := by
    intro p
    exact continuousAt_subtype_val.preimage_mem_nhds
      ((hNopen p).mem_nhds (huN p))
  obtain ⟨T, hTcount, hTcover⟩ :=
    TopologicalSpace.countable_cover_nhds hO
  have hcover : S ⊆ ⋃ p ∈ T,
      rectangularCriticalSource f ∩ N p := by
    intro x hx
    let q : S := ⟨x, hx⟩
    have hq : q ∈ ⋃ p ∈ T, O p := by
      rw [hTcover]
      exact Set.mem_univ q
    simp only [Set.mem_iUnion] at hq
    obtain ⟨p, hpT, hxp⟩ := hq
    exact Set.mem_iUnion.mpr ⟨p,
      Set.mem_iUnion.mpr ⟨hpT, hx.1, hxp⟩⟩
  have himage : f '' S ⊆ ⋃ p ∈ T,
      f '' (rectangularCriticalSource f ∩ N p) := by
    rintro z ⟨x, hx, rfl⟩
    have hxc := hcover hx
    simp only [Set.mem_iUnion] at hxc ⊢
    obtain ⟨p, hpT, hxp⟩ := hxc
    exact ⟨p, hpT, x, hxp, rfl⟩
  apply measure_mono_null himage
  exact (measure_biUnion_null_iff hTcount).mpr
    (fun p _hpT => hNzero p)


variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
  [FiniteDimensional ℝ Z]

/-- Dimension of the kernel of a surjective derivative on `X × Y`. -/
def rectangularParametricKernelDimension (X Y Z : Type*)
    [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    [AddCommGroup Z] [Module ℝ Z]
    [Module.Free ℝ X] [Module.Finite ℝ X]
    [Module.Free ℝ Y] [Module.Finite ℝ Y]
    [Module.Free ℝ Z] [Module.Finite ℝ Z] : ℕ :=
  Module.finrank ℝ X + Module.finrank ℝ Y - Module.finrank ℝ Z

theorem finrank_ker_eq_rectangularParametricKernelDimension
    (L : (X × Y) →L[ℝ] Z) (hL : L.range = ⊤) :
    Module.finrank ℝ L.ker =
      rectangularParametricKernelDimension X Y Z := by
  have hrankNullity := L.toLinearMap.finrank_range_add_finrank_ker
  rw [hL, finrank_top, Module.finrank_prod] at hrankNullity
  dsimp only [rectangularParametricKernelDimension]
  omega

/-- Euclidean coordinates on the kernel of a surjective joint derivative. -/
def rectangularParameterKernelEquiv
    (L : (X × Y) →L[ℝ] Z) (hL : L.range = ⊤) :
    RealEuclidean (rectangularParametricKernelDimension X Y Z) ≃L[ℝ] L.ker :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [finrank_ker_eq_rectangularParametricKernelDimension L hL,
      Module.finrank_pi, Fintype.card_fin])

/-- Constant-level coordinates in an implicit chart, with the whole kernel
rather than only the parameter-dimensional square case. -/
def rectangularParametricLevelCoordinates
    (Phi : X × Y → Z) (p : X × Y)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) :
    RealEuclidean (rectangularParametricKernelDimension X Y Z) →
      Z × (fderiv ℝ Phi p).ker := fun w =>
  (Phi p, rectangularParameterKernelEquiv (fderiv ℝ Phi p) hSurj w)

/-- The corresponding parametrization of the fixed level of `Phi`. -/
def rectangularParametricLevelChart
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) :
    RealEuclidean (rectangularParametricKernelDimension X Y Z) → X × Y :=
  fun w => (parametricImplicitChart Phi p hPhi hSurj).symm
    (rectangularParametricLevelCoordinates Phi p hSurj w)



/-- A chart derivative whose chart coordinates cover the full kernel has
range equal to that kernel. -/
theorem range_eq_ker_of_rectangular_chart_derivative
    {W V : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ W]
    (L : (X × Y) →L[ℝ] Z)
    (A : (X × Y) →L[ℝ] (Z × V))
    (d : W →L[ℝ] (X × Y))
    (e : W ≃L[ℝ] V)
    (hL : L.range = ⊤)
    (hkerDim : Module.finrank ℝ W = Module.finrank ℝ L.ker)
    (hfst : (ContinuousLinearMap.fst ℝ Z V).comp A = L)
    (hcomp : A.comp d =
      (0 : W →L[ℝ] Z).prod (e : W →L[ℝ] V)) :
    d.range = L.ker := by
  have hcomp_apply : ∀ u : W, A (d u) = (0, e u) := by
    intro u
    have hu := congrArg
      (fun T : W →L[ℝ] (Z × V) => T u) hcomp
    simpa using hu
  have hd_injective : Function.Injective d := by
    intro u v huv
    apply e.injective
    have hAuv : A (d u) = A (d v) := congrArg A huv
    simpa [hcomp_apply] using congrArg Prod.snd hAuv
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro w ⟨u, rfl⟩
    change L (d u) = 0
    have hfst_apply := congrArg
      (fun T : (X × Y) →L[ℝ] Z => T (d u)) hfst
    simpa [hcomp_apply] using hfst_apply.symm
  · rw [LinearMap.finrank_range_of_inj hd_injective]
    exact hkerDim

/-- The rectangular level chart stays on the level used to define it. -/
theorem rectangularParametricLevelChart_value_of_mem
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hSurj : (fderiv ℝ Phi p).range = ⊤)
    {w : RealEuclidean (rectangularParametricKernelDimension X Y Z)}
    (hw : rectangularParametricLevelCoordinates Phi p hSurj w ∈
      (parametricImplicitChart Phi p hPhi hSurj).target) :
    Phi (rectangularParametricLevelChart Phi p hPhi hSurj w) = Phi p := by
  have hr := (parametricImplicitChart Phi p hPhi hSurj).right_inv hw
  have hrfst := congrArg Prod.fst hr
  simpa [rectangularParametricLevelChart,
    rectangularParametricLevelCoordinates] using hrfst

/-- Smoothness of the rectangular level chart at points where the implicit
chart derivative remains invertible. -/
theorem contDiffAt_rectangularParametricLevelChart
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hSurj : (fderiv ℝ Phi p).range = ⊤)
    (w : RealEuclidean (rectangularParametricKernelDimension X Y Z))
    (htarget : rectangularParametricLevelCoordinates Phi p hSurj w ∈
      (parametricImplicitChart Phi p hPhi hSurj).target)
    (hPhiPoint : ContDiffAt ℝ ∞ Phi
      (rectangularParametricLevelChart Phi p hPhi hSurj w))
    (hinv : (fderiv ℝ (parametricImplicitChart Phi p hPhi hSurj)
      (rectangularParametricLevelChart Phi p hPhi hSurj w)).IsInvertible) :
    ContDiffAt ℝ ∞
      (rectangularParametricLevelChart Phi p hPhi hSurj) w := by
  let e := parametricImplicitChart Phi p hPhi hSurj
  let c := rectangularParametricLevelCoordinates Phi p hSurj
  let gamma := rectangularParametricLevelChart Phi p hPhi hSurj
  rcases hinv with ⟨A, hA⟩
  have heCD : ContDiffAt ℝ ∞ e (gamma w) := by
    change ContDiffAt ℝ ∞
      (parametricImplicitData Phi p hPhi hSurj).prodFun (gamma w)
    unfold ImplicitFunctionData.prodFun
    dsimp [parametricImplicitData,
      HasStrictFDerivAt.implicitFunctionDataOfComplemented]
    fun_prop
  have hsymm : ContDiffAt ℝ ∞ e.symm (c w) := by
    apply e.contDiffAt_symm htarget (f₀' := A)
    · simpa [gamma, c, e, rectangularParametricLevelChart, hA] using
        (heCD.differentiableAt (by simp)).hasFDerivAt
    · simpa [gamma, c, e, rectangularParametricLevelChart] using heCD
  have hc : ContDiff ℝ ∞ c := by
    change ContDiff ℝ ∞ (fun u ↦
      (Phi p, rectangularParameterKernelEquiv
        (fderiv ℝ Phi p) hSurj u))
    exact contDiff_const.prodMk
      (rectangularParameterKernelEquiv
        (fderiv ℝ Phi p) hSurj).contDiff
  exact hsymm.comp w hc.contDiffAt

/-- The derivative range of the rectangular level chart is the full kernel
of the joint derivative. -/
theorem fderiv_rectangularParametricLevelChart_range_eq_ker
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hSurj : (fderiv ℝ Phi p).range = ⊤)
    (w : RealEuclidean (rectangularParametricKernelDimension X Y Z))
    (htarget : rectangularParametricLevelCoordinates Phi p hSurj w ∈
      (parametricImplicitChart Phi p hPhi hSurj).target)
    (hPhiPoint : ContDiffAt ℝ ∞ Phi
      (rectangularParametricLevelChart Phi p hPhi hSurj w))
    (hinv : (fderiv ℝ (parametricImplicitChart Phi p hPhi hSurj)
      (rectangularParametricLevelChart Phi p hPhi hSurj w)).IsInvertible)
    (hPointSurj : (fderiv ℝ Phi
      (rectangularParametricLevelChart Phi p hPhi hSurj w)).range = ⊤) :
    (fderiv ℝ (rectangularParametricLevelChart Phi p hPhi hSurj) w).range =
      (fderiv ℝ Phi
        (rectangularParametricLevelChart Phi p hPhi hSurj w)).ker := by
  let e := parametricImplicitChart Phi p hPhi hSurj
  let c := rectangularParametricLevelCoordinates Phi p hSurj
  let gamma := rectangularParametricLevelChart Phi p hPhi hSurj
  let q := rectangularParameterKernelEquiv (fderiv ℝ Phi p) hSurj
  let A := fderiv ℝ e (gamma w)
  let d := fderiv ℝ gamma w
  let L := fderiv ℝ Phi (gamma w)
  have hgammaCD : ContDiffAt ℝ ∞ gamma w :=
    contDiffAt_rectangularParametricLevelChart
      Phi p hPhi hSurj w htarget hPhiPoint hinv
  have hgamma : DifferentiableAt ℝ gamma w :=
    hgammaCD.differentiableAt (by simp)
  have heDiff : DifferentiableAt ℝ e (gamma w) := by
    have heCD : ContDiffAt ℝ ∞ e (gamma w) := by
      change ContDiffAt ℝ ∞
        (parametricImplicitData Phi p hPhi hSurj).prodFun (gamma w)
      unfold ImplicitFunctionData.prodFun
      dsimp [parametricImplicitData,
        HasStrictFDerivAt.implicitFunctionDataOfComplemented]
      fun_prop
    exact heCD.differentiableAt (by simp)
  have hcDeriv : HasFDerivAt c
      ((0 : RealEuclidean
          (rectangularParametricKernelDimension X Y Z) →L[ℝ] Z).prod
        (q : RealEuclidean
          (rectangularParametricKernelDimension X Y Z) →L[ℝ]
            (fderiv ℝ Phi p).ker)) w := by
    exact (hasFDerivAt_const (𝕜 := ℝ) (Phi p) w).prodMk q.hasFDerivAt
  have hevent : (fun t => e (gamma t)) =ᶠ[𝓝 w] c := by
    have hright := e.eventually_right_inverse htarget
    have hcCont : Continuous c := by
      change Continuous (fun u ↦
        (Phi p, rectangularParameterKernelEquiv
          (fderiv ℝ Phi p) hSurj u))
      exact continuous_const.prodMk
        (rectangularParameterKernelEquiv
          (fderiv ℝ Phi p) hSurj).continuous
    have hpre := hcCont.continuousAt hright
    filter_upwards [hpre] with t ht
    exact ht
  have hcompDeriv : HasFDerivAt (fun t => e (gamma t)) (A.comp d) w := by
    exact heDiff.hasFDerivAt.comp w hgamma.hasFDerivAt
  have hcomp : A.comp d =
      (0 : RealEuclidean
          (rectangularParametricKernelDimension X Y Z) →L[ℝ] Z).prod
        (q : RealEuclidean
          (rectangularParametricKernelDimension X Y Z) →L[ℝ]
            (fderiv ℝ Phi p).ker) := by
    exact (hcompDeriv.congr_of_eventuallyEq hevent.symm).unique hcDeriv
  have hfirstFun : (fun u => (e u).1) = Phi := by
    funext u
    exact parametricImplicitChart_fst Phi p u hPhi hSurj
  have hfirstDeriv :
      fderiv ℝ (fun u => (e u).1) (gamma w) = L := by
    exact congrArg (fun f : (X × Y) → Z => fderiv ℝ f (gamma w)) hfirstFun
  have hfst :
      (ContinuousLinearMap.fst ℝ Z (fderiv ℝ Phi p).ker).comp A = L := by
    exact (fderiv.fst heDiff).symm.trans hfirstDeriv
  have hkerDim : Module.finrank ℝ
      (RealEuclidean (rectangularParametricKernelDimension X Y Z)) =
      Module.finrank ℝ L.ker := by
    rw [Module.finrank_pi, Fintype.card_fin,
      finrank_ker_eq_rectangularParametricKernelDimension L hPointSurj]
  exact range_eq_ker_of_rectangular_chart_derivative
    L A d q hPointSurj hkerDim hfst hcomp



/-- Every point of the base level inside the implicit-chart source has
rectangular kernel coordinates. -/
theorem exists_rectangularParametricLevelChart_coordinate
    (Phi : X × Y → Z) (p q : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hSurj : (fderiv ℝ Phi p).range = ⊤)
    (hlevel : Phi q = Phi p)
    (hqsource : q ∈ (parametricImplicitChart Phi p hPhi hSurj).source) :
    ∃ w : RealEuclidean (rectangularParametricKernelDimension X Y Z),
      rectangularParametricLevelCoordinates Phi p hSurj w ∈
        (parametricImplicitChart Phi p hPhi hSurj).target ∧
      rectangularParametricLevelChart Phi p hPhi hSurj w = q := by
  let e := parametricImplicitChart Phi p hPhi hSurj
  let k : (fderiv ℝ Phi p).ker := (e q).2
  let w := (rectangularParameterKernelEquiv
    (fderiv ℝ Phi p) hSurj).symm k
  have hcoord : rectangularParametricLevelCoordinates Phi p hSurj w =
      e q := by
    apply Prod.ext
    · change Phi p = (e q).1
      rw [show (e q).1 = Phi q by
        exact parametricImplicitChart_fst Phi p q hPhi hSurj]
      exact hlevel.symm
    · change rectangularParameterKernelEquiv
        (fderiv ℝ Phi p) hSurj w = (e q).2
      simp [w, k]
  refine ⟨w, ?_, ?_⟩
  · rw [hcoord]
    exact e.map_source hqsource
  · change e.symm
      (rectangularParametricLevelCoordinates Phi p hSurj w) = q
    rw [hcoord]
    exact e.left_inv hqsource

/-- If a level-chart derivative covers the joint kernel, failure of the
fixed-variable derivative forces criticality of the parameter projection. -/
theorem not_surjective_fderiv_rectangularChartProjection
    {W B : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Phi : X × Y → Z) (gamma : W → X × Y) (w : W)
    (E : Y ≃L[ℝ] B)
    (hgamma : DifferentiableAt ℝ gamma w)
    (hrange : (fderiv ℝ gamma w).range =
      (fderiv ℝ Phi (gamma w)).ker)
    (hjoint : (fderiv ℝ Phi (gamma w)).range = ⊤)
    (hfixed : (fstPartial (fderiv ℝ Phi (gamma w))).range ≠ ⊤) :
    ¬Function.Surjective
      (fderiv ℝ (fun t => E (gamma t).2) w) := by
  let D := fderiv ℝ Phi (gamma w)
  let d := fderiv ℝ gamma w
  have hsndDeriv :
      fderiv ℝ (fun t => (gamma t).2) w =
        (ContinuousLinearMap.snd ℝ X Y).comp d :=
    fderiv.snd hgamma
  have hsndKernel :
      ((ContinuousLinearMap.snd ℝ X Y).comp d).range =
        (sndOnKernel D).range :=
    range_eq_top_comp_of_range_eq_ker D d (by simpa [D, d] using hrange)
  have hsndBad : (sndOnKernel D).range ≠ ⊤ := by
    intro hsnd
    apply hfixed
    exact (fstPartial_range_eq_top_iff_sndOnKernel_range_eq_top
      D (by simpa [D] using hjoint)).mpr hsnd
  have hsndNotSurj : ¬Function.Surjective
      (fderiv ℝ (fun t => (gamma t).2) w) := by
    intro hsnd
    apply hsndBad
    rw [← hsndKernel, ← hsndDeriv]
    exact LinearMap.range_eq_top.mpr hsnd
  have hprojectionDeriv :
      fderiv ℝ (fun t => E (gamma t).2) w =
        (E : Y →L[ℝ] B).comp
          (fderiv ℝ (fun t => (gamma t).2) w) := by
    exact (E.hasFDerivAt.comp w hgamma.snd.hasFDerivAt).fderiv
  intro hprojection
  apply hsndNotSurj
  intro y
  obtain ⟨u, hu⟩ := hprojection (E y)
  refine ⟨u, E.injective ?_⟩
  rw [← hu, hprojectionDeriv]
  rfl



/-- A finite-dimensional real space in standard Euclidean coordinates. -/
def finiteDimensionalEuclideanEquiv (Y : Type*)
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] :
    Y ≃L[ℝ] RealEuclidean (Module.finrank ℝ Y) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp only [Module.finrank_pi, Fintype.card_fin])

/-- Parametric transversality for a rectangular smooth joint submersion,
with the parameter selected in a prescribed nonempty open set.  If
`dim Z ≤ dim X`, one parameter makes the fixed-parameter derivative
surjective at every point of the chosen level inside the open set `U`. -/
theorem exists_parameter_mem_with_regular_fixed_slice_rectangular
    (Phi : X × Y → Z) (U : Set (X × Y)) (z : Z)
    (hUopen : IsOpen U)
    (hPhi : ContDiffOn ℝ ∞ Phi U)
    (hdim : Module.finrank ℝ Z ≤ Module.finrank ℝ X)
    (hSurj : ∀ p ∈ U, (fderiv ℝ Phi p).range = ⊤)
    (V : Set Y) (hVopen : IsOpen V) (hVnonempty : V.Nonempty) :
    ∃ c ∈ V, ∀ q ∈ U, Phi q = z → q.2 = c →
      (fstPartial (fderiv ℝ Phi q)).range = ⊤ := by
  let S : Set (X × Y) := {p | p ∈ U ∧ Phi p = z}
  have hPhiAt (p : S) : ContDiffAt ℝ 1 Phi p.1 := by
    exact ((hPhi p.1 p.2.1).contDiffAt
      (hUopen.mem_nhds p.2.1)).of_le (by norm_num)
  have hSurjAt (p : S) : (fderiv ℝ Phi p.1).range = ⊤ :=
    hSurj p.1 p.2.1
  let R : S → Set (X × Y) := fun p =>
    interior (parametricImplicitRegularSource
      Phi p.1 (hPhiAt p) (hSurjAt p) ∩ U)
  have hRopen : ∀ p : S, IsOpen (R p) := fun _ => isOpen_interior
  have hpR : ∀ p : S, p.1 ∈ R p := by
    intro p
    apply mem_interior_iff_mem_nhds.mpr
    exact inter_mem
      (parametricImplicitRegularSource_mem_nhds
        Phi p.1 (hPhiAt p) (hSurjAt p))
      (hUopen.mem_nhds p.2.1)
  have hRsource : ∀ p : S, R p ⊆
      (parametricImplicitChart Phi p.1 (hPhiAt p) (hSurjAt p)).source := by
    intro p q hq
    exact (interior_subset hq).1.1
  have hRU : ∀ p : S, R p ⊆ U := by
    intro p q hq
    exact (interior_subset hq).2
  have hRinv : ∀ p : S, ∀ q ∈ R p,
      (fderiv ℝ
        (parametricImplicitChart Phi p.1 (hPhiAt p) (hSurjAt p)) q).IsInvertible := by
    intro p q hq
    exact (interior_subset hq).1.2.2
  let O : S → Set S := fun p => Subtype.val ⁻¹' R p
  have hO : ∀ p : S, O p ∈ 𝓝 p := by
    intro p
    exact continuousAt_subtype_val.preimage_mem_nhds
      ((hRopen p).mem_nhds (hpR p))
  obtain ⟨T, hTcount, hTcover⟩ :=
    TopologicalSpace.countable_cover_nhds hO
  let E : Y ≃L[ℝ] RealEuclidean (Module.finrank ℝ Y) :=
    finiteDimensionalEuclideanEquiv Y
  let chart : S →
      RealEuclidean (rectangularParametricKernelDimension X Y Z) →
        X × Y := fun p =>
    rectangularParametricLevelChart Phi p.1 (hPhiAt p) (hSurjAt p)
  let coordinates : (p : S) →
      RealEuclidean (rectangularParametricKernelDimension X Y Z) →
        Z × (fderiv ℝ Phi p.1).ker := fun p =>
    rectangularParametricLevelCoordinates Phi p.1 (hSurjAt p)
  let chartDomain : S →
      Set (RealEuclidean (rectangularParametricKernelDimension X Y Z)) :=
    fun p => (coordinates p) ⁻¹'
      ((parametricImplicitChart Phi p.1 (hPhiAt p) (hSurjAt p)) '' R p)
  let projection : S →
      RealEuclidean (rectangularParametricKernelDimension X Y Z) →
        RealEuclidean (Module.finrank ℝ Y) := fun p w => E (chart p w).2
  let badDomain : S →
      Set (RealEuclidean (rectangularParametricKernelDimension X Y Z)) :=
    fun p => {w | w ∈ chartDomain p ∧
      (fstPartial (fderiv ℝ Phi (chart p w))).range ≠ ⊤}
  have hcoordinatesContinuous : ∀ p : S, Continuous (coordinates p) := by
    intro p
    change Continuous (fun w =>
      (Phi p.1, rectangularParameterKernelEquiv
        (fderiv ℝ Phi p.1) (hSurjAt p) w))
    exact continuous_const.prodMk
      (rectangularParameterKernelEquiv
        (fderiv ℝ Phi p.1) (hSurjAt p)).continuous
  have hchartDomainOpen : ∀ p : S, IsOpen (chartDomain p) := by
    intro p
    have himageOpen : IsOpen
        ((parametricImplicitChart Phi p.1 (hPhiAt p) (hSurjAt p)) '' R p) :=
      (parametricImplicitChart Phi p.1 (hPhiAt p) (hSurjAt p)).isOpen_image_of_subset_source
        (hRopen p) (hRsource p)
    exact himageOpen.preimage (hcoordinatesContinuous p)
  have hchartPoint : ∀ p : S,
      ∀ w ∈ chartDomain p,
        coordinates p w ∈
          (parametricImplicitChart Phi p.1 (hPhiAt p) (hSurjAt p)).target ∧
        chart p w ∈ R p := by
    intro p w hw
    obtain ⟨q, hqR, hcoord⟩ := hw
    have hqsource := hRsource p hqR
    have htarget : coordinates p w ∈
        (parametricImplicitChart Phi p.1 (hPhiAt p) (hSurjAt p)).target := by
      rw [← hcoord]
      exact (parametricImplicitChart Phi p.1 (hPhiAt p)
        (hSurjAt p)).map_source hqsource
    have hchartEq : chart p w = q := by
      change (parametricImplicitChart Phi p.1 (hPhiAt p)
        (hSurjAt p)).symm (coordinates p w) = q
      rw [← hcoord]
      exact (parametricImplicitChart Phi p.1 (hPhiAt p)
        (hSurjAt p)).left_inv hqsource
    exact ⟨htarget, by rw [hchartEq]; exact hqR⟩
  have hchartSmooth : ∀ p : S, ContDiffOn ℝ ∞ (chart p) (chartDomain p) := by
    intro p w hw
    have hpoint := hchartPoint p w hw
    have hpointU : chart p w ∈ U := hRU p hpoint.2
    have hPhiPoint : ContDiffAt ℝ ∞ Phi (chart p w) :=
      (hPhi (chart p w) hpointU).contDiffAt
        (hUopen.mem_nhds hpointU)
    have hinv := hRinv p (chart p w) hpoint.2
    exact (contDiffAt_rectangularParametricLevelChart
      Phi p.1 (hPhiAt p) (hSurjAt p) w hpoint.1 hPhiPoint hinv).contDiffWithinAt
  have hprojectionSmooth : ∀ p : S,
      ContDiffOn ℝ ∞ (projection p) (chartDomain p) := by
    intro p w hw
    have hgamma := (hchartSmooth p w hw).contDiffAt
      ((hchartDomainOpen p).mem_nhds hw)
    exact (E.contDiff.contDiffAt.comp w hgamma.snd).contDiffWithinAt
  have hbadCritical : ∀ p : S, badDomain p ⊆
      rectangularCriticalSource (projection p) ∩ chartDomain p := by
    intro p w hw
    have hpoint := hchartPoint p w hw.1
    have hpointU : chart p w ∈ U := hRU p hpoint.2
    have hPhiPoint : ContDiffAt ℝ ∞ Phi (chart p w) :=
      (hPhi (chart p w) hpointU).contDiffAt
        (hUopen.mem_nhds hpointU)
    have hinv := hRinv p (chart p w) hpoint.2
    have hgammaCD := contDiffAt_rectangularParametricLevelChart
      Phi p.1 (hPhiAt p) (hSurjAt p) w hpoint.1 hPhiPoint hinv
    have hrange := fderiv_rectangularParametricLevelChart_range_eq_ker
      Phi p.1 (hPhiAt p) (hSurjAt p) w hpoint.1 hPhiPoint hinv
        (hSurj (chart p w) hpointU)
    refine ⟨?_, hw.1⟩
    exact not_surjective_fderiv_rectangularChartProjection
      Phi (chart p) w E
      (hgammaCD.differentiableAt (by simp)) hrange
      (hSurj (chart p w) hpointU) hw.2
  have hdimChart : Module.finrank ℝ Y ≤
      rectangularParametricKernelDimension X Y Z := by
    dsimp only [rectangularParametricKernelDimension]
    omega
  have hbadNull : ∀ p : S,
      volume (projection p '' badDomain p) = 0 := by
    intro p
    apply measure_mono_null (image_mono (hbadCritical p))
    exact volume_image_rectangularCriticalSource_inter_open_eq_zero_of_contDiffOn_top
      hdimChart (hchartDomainOpen p) (hprojectionSmooth p)
  let badValues : Set (RealEuclidean (Module.finrank ℝ Y)) :=
    ⋃ p ∈ T, projection p '' badDomain p
  have hbadValuesNull : volume badValues = 0 := by
    dsimp only [badValues]
    exact (measure_biUnion_null_iff hTcount).mpr
      (fun p _hp => hbadNull p)
  have hEVopen : IsOpen (E '' V) := E.isOpenMap V hVopen
  have hEVnonempty : (E '' V).Nonempty := hVnonempty.image E
  have hEVnotSubset : ¬ E '' V ⊆ badValues := by
    intro hsub
    have hEVzero : volume (E '' V) = 0 :=
      measure_mono_null hsub hbadValuesNull
    exact (hEVopen.measure_ne_zero
      (volume : Measure (RealEuclidean (Module.finrank ℝ Y)))
      hEVnonempty) hEVzero
  obtain ⟨c₀, hc₀V, hc₀⟩ := Set.not_subset.mp hEVnotSubset
  let c : Y := E.symm c₀
  have hcV : c ∈ V := by
    obtain ⟨y, hyV, hy⟩ := hc₀V
    have hyc : y = c := by
      apply E.injective
      simpa only [c, E.apply_symm_apply] using hy
    simpa only [← hyc] using hyV
  refine ⟨c, hcV, ?_⟩
  intro q hqU hqLevel hqParameter
  by_contra hqBad
  let qs : S := ⟨q, hqU, hqLevel⟩
  have hqCover : qs ∈ ⋃ p ∈ T, O p := by
    rw [hTcover]
    exact Set.mem_univ qs
  simp only [Set.mem_iUnion] at hqCover
  obtain ⟨p, hpT, hqR⟩ := hqCover
  change q ∈ R p at hqR
  obtain ⟨w, hwTarget, hchartEq⟩ :=
    exists_rectangularParametricLevelChart_coordinate
      Phi p.1 q (hPhiAt p) (hSurjAt p)
      (hqLevel.trans p.2.2.symm) (hRsource p hqR)
  have hchartEq' : chart p w = q := by
    simpa only [chart] using hchartEq
  have hcoordEq :
      parametricImplicitChart Phi p.1 (hPhiAt p) (hSurjAt p) q =
        coordinates p w := by
    have hright := (parametricImplicitChart Phi p.1 (hPhiAt p)
      (hSurjAt p)).right_inv hwTarget
    change _ = coordinates p w
    have hright' :
        parametricImplicitChart Phi p.1 (hPhiAt p) (hSurjAt p)
          (chart p w) = coordinates p w := by
      simpa only [chart, coordinates, rectangularParametricLevelChart] using hright
    rw [hchartEq'] at hright'
    exact hright'
  have hwDomain : w ∈ chartDomain p := by
    exact ⟨q, hqR, hcoordEq⟩
  have hwBad : w ∈ badDomain p := by
    refine ⟨hwDomain, ?_⟩
    rw [hchartEq']
    exact hqBad
  apply hc₀
  change c₀ ∈ badValues
  refine Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hpT, ?_⟩⟩
  refine ⟨w, hwBad, ?_⟩
  change E (chart p w).2 = c₀
  rw [hchartEq', hqParameter]
  exact E.apply_symm_apply c₀

/-- Parametric transversality for a rectangular smooth joint submersion.
This unrestricted form follows by selecting inside the whole parameter
space. -/
theorem exists_parameter_with_regular_fixed_slice_rectangular
    (Phi : X × Y → Z) (U : Set (X × Y)) (z : Z)
    (hUopen : IsOpen U)
    (hPhi : ContDiffOn ℝ ∞ Phi U)
    (hdim : Module.finrank ℝ Z ≤ Module.finrank ℝ X)
    (hSurj : ∀ p ∈ U, (fderiv ℝ Phi p).range = ⊤) :
    ∃ c : Y, ∀ q ∈ U, Phi q = z → q.2 = c →
      (fstPartial (fderiv ℝ Phi q)).range = ⊤ := by
  obtain ⟨c, _hc, hregular⟩ :=
    exists_parameter_mem_with_regular_fixed_slice_rectangular
      Phi U z hUopen hPhi hdim hSurj Set.univ isOpen_univ univ_nonempty
  exact ⟨c, hregular⟩


end AbelFormalization
