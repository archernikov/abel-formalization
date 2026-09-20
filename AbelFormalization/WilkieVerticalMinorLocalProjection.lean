import AbelFormalization.WilkieVerticalMinorProjectionFork
import AbelFormalization.LocalConstraintFiber
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Local projection from an inverse-function chart

This file isolates the topology needed for the local-open
premise in `wilkieVerticalMinor_component_projection_eq_of_localOpen`.
The visible target is explicitly open.  The remaining differential bridge is
the construction of an invertible derivative for the square map from the
nonzero hidden-column minor; it is stated as a hypothesis below.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-- The square map that records visible coordinates and the fiber value. -/
def wilkieVisibleFiberSquareMap {n k : ℕ}
    (F : RealEuclidean (n + k) → RealEuclidean k) :
    RealEuclidean (n + k) → RealEuclidean n × RealEuclidean k :=
  fun z ↦ (realEuclideanTakeLeft z, F z)

/-- An invertible strict derivative of `(visible projection, F)` gives the
local projected neighborhood required by the vertical-minor fork.  Openness
of `U` makes the restricted level fiber contain a level-open neighborhood,
so its local level patch stays in the chosen connected component. -/
theorem wilkieVerticalMinor_localProjectedNeighborhood_of_squareChart
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    {U : Set (RealEuclidean n)} (hUopen : IsOpen U)
    {x : RealEuclidean (n + k)}
    (hSquare : ∀ y ∈ wilkieFiberComponent F a U x,
      standardJacobianColumnMinor F (Fin.natAddEmb n) y ≠ 0 →
        ∃ L : RealEuclidean (n + k) ≃L[ℝ]
          (RealEuclidean n × RealEuclidean k),
          HasStrictFDerivAt (wilkieVisibleFiberSquareMap F)
            (L : RealEuclidean (n + k) →L[ℝ]
              (RealEuclidean n × RealEuclidean k)) y) :
    ∀ y ∈ wilkieFiberComponent F a U x,
      Function.Surjective (fderiv ℝ F y) →
      standardJacobianColumnMinor F (Fin.natAddEmb n) y ≠ 0 →
      ∃ V : Set (RealEuclidean n),
        IsOpen (Subtype.val ⁻¹' V : Set U) ∧
          realEuclideanTakeLeft y ∈ V ∧
          V ∩ U ⊆ realEuclideanTakeLeft ''
            wilkieFiberComponent F a U x := by
  intro y hyY hyRegular hyMinor
  let p : RealEuclidean (n + k) → RealEuclidean n :=
    fun z ↦ realEuclideanTakeLeft z
  let M : Set (RealEuclidean (n + k)) := wilkieFiberOver F a U
  have hyM : y ∈ M := by
    exact connectedComponentIn_subset M x hyY
  have hyFiber : F y = a := hyM.1
  have hyU : p y ∈ U := hyM.2
  have hp : Continuous p := by
    change Continuous (realEuclideanTakeLeftContinuousLinearMap n k)
    exact (realEuclideanTakeLeftContinuousLinearMap n k).continuous
  have hFstrict : HasStrictFDerivAt F (fderiv ℝ F y) y :=
    hF.contDiffAt.hasStrictFDerivAt one_ne_zero
  have hlocalLevel : ∃ W ∈ 𝓝 y,
      W ∩ {z | F z = F y} ⊆ M := by
    refine ⟨p ⁻¹' U, (hUopen.preimage hp).mem_nhds hyU, ?_⟩
    intro z hz
    exact ⟨hz.2.trans hyFiber, hz.1⟩
  obtain ⟨K₀, hK₀, hK₀component⟩ :=
    HasStrictFDerivAt.exists_local_level_connectedComponent
      hFstrict (LinearMap.range_eq_top.mpr hyRegular) hyM hlocalLevel
  obtain ⟨K, hKsubset, hKopen, hyK⟩ := mem_nhds_iff.mp hK₀
  obtain ⟨L, hSquareAt⟩ := hSquare y hyY hyMinor
  let e : OpenPartialHomeomorph
      (RealEuclidean (n + k))
      (RealEuclidean n × RealEuclidean k) :=
    hSquareAt.toOpenPartialHomeomorph (wilkieVisibleFiberSquareMap F)
  have hySource : y ∈ e.source :=
    hSquareAt.mem_toOpenPartialHomeomorph_source
  have hSquareY : wilkieVisibleFiberSquareMap F y = (p y, a) := by
    simp only [wilkieVisibleFiberSquareMap, p, hyFiber]
  have hyTarget : (p y, a) ∈ e.target := by
    rw [← hSquareY]
    exact e.map_source hySource
  have hSymmY : e.symm (p y, a) = y := by
    rw [← hSquareY]
    exact e.left_inv hySource
  let T : Set (RealEuclidean n × RealEuclidean k) :=
    e.target ∩ e.symm ⁻¹' K
  let V : Set (RealEuclidean n) :=
    (fun v ↦ (v, a)) ⁻¹' T
  have hTopen : IsOpen T := e.isOpen_inter_preimage_symm hKopen
  have hVopen : IsOpen V :=
    hTopen.preimage (continuous_id.prodMk continuous_const)
  refine ⟨V, hVopen.preimage continuous_subtype_val, ?_, ?_⟩
  · refine ⟨hyTarget, ?_⟩
    change e.symm (p y, a) ∈ K
    rw [hSymmY]
    exact hyK
  · intro v hv
    let z : RealEuclidean (n + k) := e.symm (v, a)
    have hvTarget : (v, a) ∈ e.target := hv.1.1
    have hzK : z ∈ K := hv.1.2
    have hRight : wilkieVisibleFiberSquareMap F z = (v, a) := by
      change e z = (v, a)
      exact e.right_inv hvTarget
    have hpz : realEuclideanTakeLeft z = v :=
      congrArg Prod.fst hRight
    have hFz : F z = a := congrArg Prod.snd hRight
    obtain ⟨hzM, hzComponent⟩ :=
      hK₀component z (hKsubset hzK) (hFz.trans hyFiber.symm)
    have hzLocal : z ∈ connectedComponentIn M y := by
      rw [connectedComponentIn_eq_image hyM]
      exact ⟨⟨z, hzM⟩, hzComponent, rfl⟩
    have hComponentEq :
        wilkieFiberComponent F a U x = connectedComponentIn M y := by
      simpa only [wilkieFiberComponent, M] using
        (connectedComponentIn_eq hyY)
    have hzY : z ∈ wilkieFiberComponent F a U x := by
      rw [hComponentEq]
      exact hzLocal
    exact ⟨z, hzY, hpz⟩

/-- The conditional fork has no separate local-open premise once the
square-map chart is available on its fixed-minor component. -/
theorem wilkieVerticalMinor_component_projection_eq_of_squareChart
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    {U : Set (RealEuclidean n)} (hU : IsPreconnected U)
    (hUopen : IsOpen U)
    (hregular : ∀ y, F y = a →
      Function.Surjective (fderiv ℝ F y))
    (hbounded : Bornology.IsBounded (wilkieFiberOver F a U))
    {x : RealEuclidean (n + k)}
    (hx : x ∈ wilkieFiberOver F a U)
    (hminor : ∀ y ∈ wilkieFiberComponent F a U x,
      standardJacobianColumnMinor F (Fin.natAddEmb n) y ≠ 0)
    (hSquare : ∀ y ∈ wilkieFiberComponent F a U x,
      standardJacobianColumnMinor F (Fin.natAddEmb n) y ≠ 0 →
        ∃ L : RealEuclidean (n + k) ≃L[ℝ]
          (RealEuclidean n × RealEuclidean k),
          HasStrictFDerivAt (wilkieVisibleFiberSquareMap F)
            (L : RealEuclidean (n + k) →L[ℝ]
              (RealEuclidean n × RealEuclidean k)) y) :
    realEuclideanTakeLeft '' wilkieFiberComponent F a U x = U := by
  exact wilkieVerticalMinor_component_projection_eq_of_localOpen
    hF a hU hregular hbounded hx hminor
    (wilkieVerticalMinor_localProjectedNeighborhood_of_squareChart
      hF a hUopen hSquare)

end AbelFormalization
