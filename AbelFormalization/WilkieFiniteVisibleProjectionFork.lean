import AbelFormalization.WilkieFixedMinorConnectedInterval
import AbelFormalization.WilkieCompactOpenImageObstruction
import AbelFormalization.WilkieVerticalMinorProjectionFork
import AbelFormalization.LocalConstraintFiber
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The finite-visible-image fork in Wilkie 2.9

The component used here is a component of the *full* closed level fiber.
Finite visible image makes that component stay over the base visible point,
so boundedness of the restricted fiber makes it compact. A square-map inverse
function chart for complementary coordinates then makes the component's
complementary-coordinate image open whenever the selected maximal minor is
nonzero throughout it. A nonempty compact open subset of a connected
noncompact coordinate space cannot exist.

The square-chart premise below is deliberately explicit. The existing
vertical-column derivative bridge proves it for the last `k` columns; the
arbitrary embedding `cols` needs a permutation/complementary-coordinate
derivative bridge before this file gives the unconditional paper case.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- The connected component of the complete level fiber, rather than of its
part over an open visible set. -/
def wilkieFullFiberComponent {n k : ℕ}
    (F : RealEuclidean (n + k) → RealEuclidean k)
    (a : RealEuclidean k) (x : RealEuclidean (n + k)) :
    Set (RealEuclidean (n + k)) :=
  connectedComponentIn (F ⁻¹' {a}) x

/-- Finite visible image of the bounded restricted fiber forces its full
fiber component through a restricted point to stay over that point. This
also makes the full component globally compact. -/
theorem wilkieFullFiberComponent_compact_of_finite_visible_image
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    {U : Set (RealEuclidean n)} (hUopen : IsOpen U)
    (hbounded : Bornology.IsBounded (wilkieFiberOver F a U))
    (hfinite : (realEuclideanTakeLeft '' wilkieFiberOver F a U).Finite)
    {x : RealEuclidean (n + k)} (hx : x ∈ wilkieFiberOver F a U) :
    IsCompact (wilkieFullFiberComponent F a x) ∧
      wilkieFullFiberComponent F a x ⊆ wilkieFiberOver F a U := by
  let C : Set (RealEuclidean (n + k)) := F ⁻¹' {a}
  let Y : Set (RealEuclidean (n + k)) := connectedComponentIn C x
  let p : RealEuclidean (n + k) → RealEuclidean n :=
    fun y ↦ realEuclideanTakeLeft y
  have hp : Continuous p := by
    change Continuous (realEuclideanTakeLeftContinuousLinearMap n k)
    exact (realEuclideanTakeLeftContinuousLinearMap n k).continuous
  have hxC : x ∈ C := hx.1
  have hxY : x ∈ Y := mem_connectedComponentIn hxC
  have hYsubsetC : Y ⊆ C := connectedComponentIn_subset C x
  have hKpre : IsPreconnected (p '' Y) :=
    isPreconnected_connectedComponentIn.image p hp.continuousOn
  have hKfinite : (p '' Y ∩ U).Finite := by
    apply hfinite.subset
    rintro v ⟨⟨y, hyY, rfl⟩, hyU⟩
    exact ⟨y, ⟨hYsubsetC hyY, hyU⟩, rfl⟩
  have hKinter : (p '' Y ∩ U).Nonempty :=
    ⟨p x, ⟨x, hxY, rfl⟩, hx.2⟩
  obtain ⟨u, hKsingleton⟩ :=
    eq_singleton_of_preconnected_finite_inter_open
      hKpre hUopen hKfinite hKinter
  have hpxEq : p x = u := by
    have hpxImage : p x ∈ p '' Y := ⟨x, hxY, rfl⟩
    rw [hKsingleton] at hpxImage
    simpa only [mem_singleton_iff] using hpxImage
  have huU : u ∈ U := by rw [← hpxEq]; exact hx.2
  have hYsubsetX : Y ⊆ wilkieFiberOver F a U := by
    intro y hyY
    have hpyImage : p y ∈ p '' Y := ⟨y, hyY, rfl⟩
    rw [hKsingleton] at hpyImage
    have hpyEq : p y = u := by
      simpa only [mem_singleton_iff] using hpyImage
    have hpyU : p y ∈ U := by rw [hpyEq]; exact huU
    exact ⟨hYsubsetC hyY, hpyU⟩
  have hYbounded : Bornology.IsBounded Y :=
    hbounded.subset hYsubsetX
  have hCclosed : IsClosed C :=
    isClosed_singleton.preimage hF.continuous
  have hYclosedInC :
      IsClosed (Subtype.val ⁻¹' Y : Set C) := by
    change IsClosed
      (Subtype.val ⁻¹' (connectedComponentIn C x) : Set C)
    rw [connectedComponentIn_eq_image hxC]
    rw [Set.preimage_image_eq _ Subtype.coe_injective]
    exact isClosed_connectedComponent
  obtain ⟨D, hDclosed, hDimage⟩ := hYclosedInC.image_val
  have hYeq : Y = D ∩ C := by
    have hinter : Y ∩ C = D ∩ C := by
      calc
        Y ∩ C = C ∩ Y := inter_comm _ _
        _ = D ∩ C := by
          simpa only [Subtype.image_preimage_coe] using hDimage
    simpa only [inter_eq_left.mpr hYsubsetC] using hinter
  have hYclosed : IsClosed Y := by
    rw [hYeq]
    exact hDclosed.inter hCclosed
  have hYcompact : IsCompact Y := by
    simpa only [hYclosed.closure_eq] using hYbounded.isCompact_closure
  exact ⟨hYcompact, hYsubsetX⟩

/-- An inverse-function chart for `(q,F)` near a regular fiber point gives a
neighborhood in complementary coordinates covered by the full component.
This is the IFT step shared by every choice of `q`. -/
theorem wilkieFullFiberComponent_localComplementaryNeighborhood_of_squareChart
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    (hregular : ∀ y, F y = a →
      Function.Surjective (fderiv ℝ F y))
    (q : RealEuclidean (n + k) →L[ℝ] RealEuclidean n)
    {x y : RealEuclidean (n + k)}
    (_hx : x ∈ F ⁻¹' {a})
    (hy : y ∈ wilkieFullFiberComponent F a x)
    (hSquare : ∃ L : RealEuclidean (n + k) ≃L[ℝ]
        (RealEuclidean n × RealEuclidean k),
      HasStrictFDerivAt (fun z ↦ (q z, F z))
        (L : RealEuclidean (n + k) →L[ℝ]
          (RealEuclidean n × RealEuclidean k)) y) :
    ∃ V : Set (RealEuclidean n),
      IsOpen V ∧ q y ∈ V ∧
        V ⊆ q '' wilkieFullFiberComponent F a x := by
  let C : Set (RealEuclidean (n + k)) := F ⁻¹' {a}
  let M : RealEuclidean (n + k) →
      RealEuclidean n × RealEuclidean k := fun z ↦ (q z, F z)
  have hyC : y ∈ C :=
    connectedComponentIn_subset C x hy
  have hyFy : F y = a := hyC
  have hFstrict : HasStrictFDerivAt F (fderiv ℝ F y) y :=
    hF.contDiffAt.hasStrictFDerivAt one_ne_zero
  have hlocalLevel : ∃ W ∈ 𝓝 y,
      W ∩ {z | F z = F y} ⊆ C := by
    refine ⟨Set.univ, univ_mem, ?_⟩
    intro z hz
    exact hz.2.trans hyFy
  obtain ⟨K₀, hK₀, hK₀component⟩ :=
    HasStrictFDerivAt.exists_local_level_connectedComponent
      hFstrict (LinearMap.range_eq_top.mpr (hregular y hyFy))
      hyC hlocalLevel
  obtain ⟨K, hKsubset, hKopen, hyK⟩ := mem_nhds_iff.mp hK₀
  obtain ⟨L, hSquareAt⟩ := hSquare
  let e : OpenPartialHomeomorph
      (RealEuclidean (n + k))
      (RealEuclidean n × RealEuclidean k) :=
    hSquareAt.toOpenPartialHomeomorph M
  have hySource : y ∈ e.source :=
    hSquareAt.mem_toOpenPartialHomeomorph_source
  have hMy : M y = (q y, a) := by simp only [M, hyFy]
  have hyTarget : (q y, a) ∈ e.target := by
    rw [← hMy]
    exact e.map_source hySource
  have hSymmY : e.symm (q y, a) = y := by
    rw [← hMy]
    exact e.left_inv hySource
  let T : Set (RealEuclidean n × RealEuclidean k) :=
    e.target ∩ e.symm ⁻¹' K
  let V : Set (RealEuclidean n) :=
    (fun v ↦ (v, a)) ⁻¹' T
  have hTopen : IsOpen T := e.isOpen_inter_preimage_symm hKopen
  have hVopen : IsOpen V :=
    hTopen.preimage (continuous_id.prodMk continuous_const)
  refine ⟨V, hVopen, ?_, ?_⟩
  · refine ⟨hyTarget, ?_⟩
    change e.symm (q y, a) ∈ K
    rw [hSymmY]
    exact hyK
  · intro v hv
    let z : RealEuclidean (n + k) := e.symm (v, a)
    have hvTarget : (v, a) ∈ e.target := hv.1
    have hzK : z ∈ K := hv.2
    have hRight : M z = (v, a) := by
      change e z = (v, a)
      exact e.right_inv hvTarget
    have hqz : q z = v := congrArg Prod.fst hRight
    have hFz : F z = a := congrArg Prod.snd hRight
    obtain ⟨hzC, hzComponent⟩ :=
      hK₀component z (hKsubset hzK) (hFz.trans hyFy.symm)
    have hzLocal : z ∈ connectedComponentIn C y := by
      rw [connectedComponentIn_eq_image hyC]
      exact ⟨⟨z, hzC⟩, hzComponent, rfl⟩
    have hComponentEq :
        wilkieFullFiberComponent F a x = connectedComponentIn C y := by
      simpa only [wilkieFullFiberComponent, C] using
        (connectedComponentIn_eq hy)
    have hzY : z ∈ wilkieFullFiberComponent F a x := by
      rw [hComponentEq]
      exact hzLocal
    exact ⟨z, hzY, hqz⟩

/-- Compactness and an IFT square-chart interface force the *chosen* minor
to vanish somewhere on the full fiber component. -/
theorem wilkieFiniteVisibleImage_sameMinor_zero_of_squareChart
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    {U : Set (RealEuclidean n)} (hUopen : IsOpen U)
    (hregular : ∀ y, F y = a →
      Function.Surjective (fderiv ℝ F y))
    (hbounded : Bornology.IsBounded (wilkieFiberOver F a U))
    (hfinite : (realEuclideanTakeLeft '' wilkieFiberOver F a U).Finite)
    {x : RealEuclidean (n + k)} (hx : x ∈ wilkieFiberOver F a U)
    (cols : Fin k ↪ Fin (n + k))
    (q : RealEuclidean (n + k) →L[ℝ] RealEuclidean n)
    [ConnectedSpace (RealEuclidean n)]
    [NoncompactSpace (RealEuclidean n)]
    (hSquare : ∀ y ∈ wilkieFullFiberComponent F a x,
      standardJacobianColumnMinor F cols y ≠ 0 →
      ∃ L : RealEuclidean (n + k) ≃L[ℝ]
        (RealEuclidean n × RealEuclidean k),
        HasStrictFDerivAt (fun z ↦ (q z, F z))
          (L : RealEuclidean (n + k) →L[ℝ]
            (RealEuclidean n × RealEuclidean k)) y) :
    ∃ z ∈ wilkieFullFiberComponent F a x,
      standardJacobianColumnMinor F cols z = 0 := by
  let Y : Set (RealEuclidean (n + k)) :=
    wilkieFullFiberComponent F a x
  have hxY : x ∈ Y := mem_connectedComponentIn hx.1
  have hcompact : IsCompact Y :=
    (wilkieFullFiberComponent_compact_of_finite_visible_image
      hF a hUopen hbounded hfinite hx).1
  by_contra hzeroMissing
  have hminor : ∀ y ∈ Y,
      standardJacobianColumnMinor F cols y ≠ 0 := by
    intro y hyY hzero
    exact hzeroMissing ⟨y, hyY, hzero⟩
  have hopen : IsOpen (q '' Y) := by
    apply isOpen_iff_mem_nhds.mpr
    intro v hv
    obtain ⟨y, hyY, hqyv⟩ := hv
    obtain ⟨V, hVopen, hqyV, hVsubset⟩ :=
      wilkieFullFiberComponent_localComplementaryNeighborhood_of_squareChart
        hF a hregular q hx.1 hyY (hSquare y hyY (hminor y hyY))
    have hvV : v ∈ V := by rw [← hqyv]; exact hqyV
    exact Filter.mem_of_superset (hVopen.mem_nhds hvV) hVsubset
  exact (compact_nonempty_image_not_open q.continuous hcompact
    ⟨x, hxY⟩) hopen

/-- The fixed-minor interval follows on the restricted fiber because the
full component lies inside it in the finite-image case. -/
theorem wilkieFiniteVisibleImage_sameMinor_squared_interval_of_squareChart
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    {U : Set (RealEuclidean n)} (hUopen : IsOpen U)
    (hregular : ∀ y, F y = a →
      Function.Surjective (fderiv ℝ F y))
    (hbounded : Bornology.IsBounded (wilkieFiberOver F a U))
    (hfinite : (realEuclideanTakeLeft '' wilkieFiberOver F a U).Finite)
    {x : RealEuclidean (n + k)} (hx : x ∈ wilkieFiberOver F a U)
    (cols : Fin k ↪ Fin (n + k))
    (hminorAtX : standardJacobianColumnMinor F cols x ≠ 0)
    (q : RealEuclidean (n + k) →L[ℝ] RealEuclidean n)
    [ConnectedSpace (RealEuclidean n)]
    [NoncompactSpace (RealEuclidean n)]
    (hSquare : ∀ y ∈ wilkieFullFiberComponent F a x,
      standardJacobianColumnMinor F cols y ≠ 0 →
      ∃ L : RealEuclidean (n + k) ≃L[ℝ]
        (RealEuclidean n × RealEuclidean k),
        HasStrictFDerivAt (fun z ↦ (q z, F z))
          (L : RealEuclidean (n + k) →L[ℝ]
            (RealEuclidean n × RealEuclidean k)) y) :
    ∃ η : ℝ, 0 < η ∧ Set.Icc (0 : ℝ) η ⊆
      (fun y ↦ (standardJacobianColumnMinor F cols y) ^ 2) ''
        wilkieFiberOver F a U := by
  let Y : Set (RealEuclidean (n + k)) :=
    wilkieFullFiberComponent F a x
  obtain ⟨z, hzY, hzZero⟩ :=
    wilkieFiniteVisibleImage_sameMinor_zero_of_squareChart
      hF a hUopen hregular hbounded hfinite hx cols q hSquare
  have hxY : x ∈ Y := mem_connectedComponentIn hx.1
  have hYpre : IsPreconnected Y := isPreconnected_connectedComponentIn
  obtain ⟨η, hη, hinterval⟩ :=
    squared_standardJacobianColumnMinor_interval
      hF cols hYpre hzY hxY hzZero hminorAtX
  have hYsubsetX : Y ⊆ wilkieFiberOver F a U :=
    (wilkieFullFiberComponent_compact_of_finite_visible_image
      hF a hUopen hbounded hfinite hx).2
  exact ⟨η, hη, hinterval.trans (Set.image_mono hYsubsetX)⟩

end AbelFormalization
