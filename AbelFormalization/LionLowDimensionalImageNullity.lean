import AbelFormalization.LionTheorem7GenericBound
import AbelFormalization.LowerDimensionalImageAvoidance

/-!
# Null images of low-dimensional carpeted leaves

The first branch of Lion's Theorem 7' says that a generic fiber is empty
when the target dimension is larger than the leaf dimension.  This file
proves the required null-image statement from the implicit-function chart
of the leaf and mathlib's Hausdorff-dimension estimate for differentiable
images.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

namespace LionCarpetedLeaf

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)} {n q p : ℕ}

/-- Around each point of a carpeted leaf, the image of the leaf under a
smooth map to a strictly larger-dimensional target is null. -/
theorem exists_local_carrier_image_null_of_dimension_lt
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (hqn : q ≤ n) (hdim : n - q < p)
    {x : RealEuclidean n} (hx : x ∈ L.carrier) :
    ∃ N : Set (RealEuclidean n), IsOpen N ∧ x ∈ N ∧
      volume (g '' (L.carrier ∩ N)) = 0 := by
  let r : ℕ := 1
  have hr : 0 < r := by simp [r]
  have hfSmooth : ContDiff ℝ r L.equations :=
    (L.equations_contDiff hsmooth).of_le (by simp)
  have hgSmooth : ContDiff ℝ r g := by
    rw [contDiff_pi]
    intro i
    exact (hsmooth n (fun y ↦ g y i) (hg i)).of_le (by simp)
  let A : RealEuclidean n →L[ℝ] RealEuclidean q :=
    fderiv ℝ L.equations x
  have hA : Function.Surjective A :=
    L.fderiv_surjective x hx.1
  have hArange : A.range = ⊤ := LinearMap.range_eq_top.mpr hA
  have hstrict : HasStrictFDerivAt L.equations A x :=
    hfSmooth.contDiffAt.hasStrictFDerivAt (by simp [r])
  let hkernel : A.ker.ClosedComplemented :=
    A.ker_closedComplemented_of_finiteDimensional_range
  let chartData :=
    hstrict.implicitFunctionDataOfComplemented
      L.equations A hArange hkernel
  let e : OpenPartialHomeomorph (RealEuclidean n)
      (RealEuclidean q × A.ker) :=
    chartData.toOpenPartialHomeomorph
  have hxSource : x ∈ e.source :=
    chartData.pt_mem_toOpenPartialHomeomorph_source
  have hfst : ∀ y, (e y).1 = L.equations y := by
    intro y
    rfl
  have hrightSmooth : ContDiff ℝ r
      (fun y : RealEuclidean n ↦
        Classical.choose hkernel (y - x)) :=
    (Classical.choose hkernel).contDiff.comp
      (contDiff_id.sub contDiff_const)
  have heSmooth : ContDiff ℝ r e := by
    change ContDiff ℝ r chartData.prodFun
    exact hfSmooth.prodMk hrightSmooth
  have hex : e x = (0, 0) := by
    apply Prod.ext
    · rw [hfst]
      exact hx.2
    · change Classical.choose hkernel (x - x) = 0
      simp
  have hinverseAt : ContDiffAt ℝ r e.symm (e x) := by
    apply e.contDiffAt_symm (e.map_source hxSource)
    · rw [e.left_inv hxSource]
      exact chartData.hasStrictFDerivAt.hasFDerivAt
    · rw [e.left_inv hxSource]
      exact heSmooth.contDiffAt
  let kappa : RealEuclidean (n - q) ≃L[ℝ] A.ker :=
    euclideanKernelEquivOfSurjective A hA
  let slice : RealEuclidean (n - q) → RealEuclidean p :=
    fun z ↦ g (e.symm ((0 : RealEuclidean q), kappa z))
  have hpairSmooth : ContDiff ℝ r
      (fun z : RealEuclidean (n - q) ↦
        ((0 : RealEuclidean q), kappa z)) :=
    contDiff_const.prodMk kappa.contDiff
  have hsliceAt : ContDiffAt ℝ r slice 0 := by
    have hinvPair : ContDiffAt ℝ r
        (fun z : RealEuclidean (n - q) ↦
          e.symm ((0 : RealEuclidean q), kappa z)) 0 := by
      have hinverseAt' : ContDiffAt ℝ r e.symm
          ((0 : RealEuclidean q), kappa (0 : RealEuclidean (n - q))) := by
        simpa only [hex, map_zero] using hinverseAt
      exact hinverseAt'.comp 0 hpairSmooth.contDiffAt
    exact hgSmooth.contDiffAt.comp 0 hinvPair
  obtain ⟨H, hHSmooth, hHeq⟩ :=
    exists_contDiff_eventuallyEq_of_contDiffAt hsliceAt
  have hHnull : volume (Set.range H) = 0 := by
    have hnull := hausdorffMeasure_image_eq_zero_of_finrank_lt
      (f := H) (s := Set.univ)
      (hHSmooth.differentiable (by simp [r])).differentiableOn
      (by
        simpa only [Module.finrank_fin_fun] using hdim)
    have hmeasure :
        (μH[Module.finrank ℝ (RealEuclidean p)] :
          Measure (RealEuclidean p)) = volume := by
      simpa using
        (hausdorffMeasure_pi_real (ι := Fin p))
    rw [← hmeasure]
    simpa only [image_univ] using hnull
  let coord : RealEuclidean n → RealEuclidean (n - q) :=
    fun y ↦ kappa.symm (e y).2
  have hcoordx : coord x = 0 := by
    simp only [coord, hex, map_zero]
  have hcoordTendsto : Tendsto coord (nhds x) (nhds 0) := by
    have heCont : ContinuousAt e x := e.continuousAt hxSource
    have hsnd : Tendsto (fun y ↦ (e y).2) (nhds x) (nhds (e x).2) :=
      continuous_snd.continuousAt.comp heCont
    have hk := kappa.symm.continuous.continuousAt.tendsto.comp hsnd
    change Tendsto (kappa.symm ∘ fun y ↦ (e y).2)
      (nhds x) (nhds 0)
    simpa only [hex, map_zero] using hk
  have hgood :
      {y | y ∈ e.source ∧ H (coord y) = slice (coord y)} ∈ nhds x := by
    filter_upwards
      [e.open_source.mem_nhds hxSource,
        hcoordTendsto.eventually hHeq]
      with y hySource hyEq
    exact ⟨hySource, hyEq⟩
  let N : Set (RealEuclidean n) :=
    interior {y | y ∈ e.source ∧ H (coord y) = slice (coord y)}
  have hNopen : IsOpen N := isOpen_interior
  have hxN : x ∈ N := mem_interior_iff_mem_nhds.mpr hgood
  refine ⟨N, hNopen, hxN, ?_⟩
  apply measure_mono_null _ hHnull
  rintro z ⟨y, ⟨hyLeaf, hyN⟩, rfl⟩
  have hyGood := interior_subset hyN
  let w : RealEuclidean (n - q) := coord y
  have hey : e y = (0, kappa w) := by
    apply Prod.ext
    · exact (hfst y).trans hyLeaf.2
    · simp only [w, coord, kappa.apply_symm_apply]
  refine ⟨w, ?_⟩
  calc
    H w = slice w := hyGood.2
    _ = g (e.symm (e y)) := by
      change g (e.symm ((0 : RealEuclidean q), kappa w)) = _
      rw [← hey]
    _ = g y := by rw [e.left_inv hyGood.1]

/-- Countably many local null-image neighborhoods cover the leaf, so the
entire leaf image is null. -/
theorem volume_image_carrier_eq_zero_of_dimension_lt
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (hqn : q ≤ n) (hdim : n - q < p) :
    volume (g '' L.carrier) = 0 := by
  choose U hUopen hxU hUzero using fun x : L.carrier ↦
    L.exists_local_carrier_image_null_of_dimension_lt
      hsmooth g hg hqn hdim x.property
  let W : L.carrier → Set L.carrier := fun x ↦ Subtype.val ⁻¹' U x
  have hW : ∀ x : L.carrier, W x ∈ nhds x := by
    intro x
    exact continuousAt_subtype_val.preimage_mem_nhds
      ((hUopen x).mem_nhds (hxU x))
  obtain ⟨T, hTcount, hTcover⟩ :=
    TopologicalSpace.countable_cover_nhds hW
  have hcover : L.carrier ⊆ ⋃ x ∈ T, L.carrier ∩ U x := by
    intro y hy
    let z : L.carrier := ⟨y, hy⟩
    have hz : z ∈ ⋃ x ∈ T, W x := by
      rw [hTcover]
      exact Set.mem_univ z
    simp only [Set.mem_iUnion] at hz ⊢
    obtain ⟨x, hxT, hzx⟩ := hz
    exact ⟨x, hxT, hy, hzx⟩
  apply measure_mono_null (image_mono hcover)
  have hnull : volume
      (⋃ x ∈ T, g '' (L.carrier ∩ U x)) = 0 :=
    (measure_biUnion_null_iff hTcount).mpr
      (fun x _hxT ↦ hUzero x)
  simpa only [image_iUnion] using hnull

end LionCarpetedLeaf

/-- Everywhere smooth geometric families satisfy the low-dimensional image
nullity input used by the numerical Theorem 7' induction. -/
theorem hasLionLowDimensionalImageNullity
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    HasLionLowDimensionalImageNullity G := by
  intro n q p L g hg hqn hdim
  exact L.volume_image_carrier_eq_zero_of_dimension_lt
    hsmooth g hg hqn hdim

end AbelFormalization
