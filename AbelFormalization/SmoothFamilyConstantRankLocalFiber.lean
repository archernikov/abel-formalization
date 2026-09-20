import AbelFormalization.SmoothFamilyRankStratumLocalFiber
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.PathConnected

/-!
# Local fibers under a finite-dimensional constant-rank bound

A nonzero selected `k × k` Jacobian minor makes the selected output map a
submersion.  If the full derivative has rank at most `k` throughout a
neighborhood, rank-nullity identifies the kernel of the full derivative with
the kernel of the selected derivative.  In an implicit-function chart, the
full map therefore has zero derivative in every vertical direction.  On a
small convex chart ball it is constant on each selected-output fiber.

This is a local statement under a neighborhood rank bound.  It does not claim
that an unqualified rank locus is a manifold.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-- The continuous linear map selecting the output coordinates indexed by
`rows`. -/
def selectedOutputLinearMap {b k : ℕ} (rows : Fin k ↪ Fin b) :
    RealEuclidean b →L[ℝ] RealEuclidean k :=
  ContinuousLinearMap.pi fun i ↦
    ContinuousLinearMap.proj (R := ℝ) (rows i)

@[simp]
theorem selectedOutputLinearMap_apply {b k : ℕ}
    (rows : Fin k ↪ Fin b) (v : RealEuclidean b) (i : Fin k) :
    selectedOutputLinearMap rows v i = v (rows i) := by
  rfl

/-- Selecting output coordinates commutes with taking the Fréchet derivative. -/
theorem fderiv_selectedOutputMap_eq_comp {a b k : ℕ}
    {g : RealEuclidean a → RealEuclidean b} {y : RealEuclidean a}
    (hg : DifferentiableAt ℝ g y) (rows : Fin k ↪ Fin b) :
    fderiv ℝ (selectedOutputMap g rows) y =
      (selectedOutputLinearMap rows).comp (fderiv ℝ g y) := by
  have h := (selectedOutputLinearMap rows).hasFDerivAt.comp y hg.hasFDerivAt
  exact h.fderiv

/-- Under surjectivity of the selected derivative and the matching upper-rank
bound for the full derivative, the two kernels agree.  The proof is pure
finite-dimensional rank-nullity and includes `k = 0`. -/
theorem ker_fderiv_eq_ker_fderiv_selectedOutputMap_of_rank_le
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {y : RealEuclidean a} (hg : DifferentiableAt ℝ g y)
    (rows : Fin k ↪ Fin b)
    (hsurj : Function.Surjective
      (fderiv ℝ (selectedOutputMap g rows) y))
    (hrank : Module.finrank ℝ
      (LinearMap.range (fderiv ℝ g y).toLinearMap) ≤ k) :
    LinearMap.ker (fderiv ℝ g y).toLinearMap =
      LinearMap.ker
        (fderiv ℝ (selectedOutputMap g rows) y).toLinearMap := by
  let full := (fderiv ℝ g y).toLinearMap
  let selected :=
    (fderiv ℝ (selectedOutputMap g rows) y).toLinearMap
  have hcomp : fderiv ℝ (selectedOutputMap g rows) y =
      (selectedOutputLinearMap rows).comp (fderiv ℝ g y) :=
    fderiv_selectedOutputMap_eq_comp hg rows
  have hle : LinearMap.ker full ≤ LinearMap.ker selected := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    change fderiv ℝ (selectedOutputMap g rows) y v = 0
    rw [hcomp, ContinuousLinearMap.comp_apply]
    change selectedOutputLinearMap rows (full v) = 0
    rw [hv, map_zero]
  have hrangeSelected : Module.finrank ℝ (LinearMap.range selected) = k := by
    have htop : LinearMap.range selected = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    rw [htop, finrank_top, Module.finrank_fin_fun]
  have hrankFull : Module.finrank ℝ (LinearMap.range full) ≤ k := by
    exact hrank
  have hfullNullity := full.finrank_range_add_finrank_ker
  have hselectedNullity := selected.finrank_range_add_finrank_ker
  have hkerFinrank :
      Module.finrank ℝ (LinearMap.ker selected) ≤
        Module.finrank ℝ (LinearMap.ker full) := by
    omega
  exact Submodule.eq_of_le_of_finrank_le hle hkerFinrank

/-- A `C¹` map has continuous square Jacobian minors. -/
theorem continuous_standardJacobianMinor_of_contDiff_one
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) (rows : Fin k ↪ Fin b)
    (cols : Fin k ↪ Fin a) :
    Continuous (standardJacobianMinor g rows cols) := by
  change Continuous fun y ↦
    ((standardRectangularJacobian g y).submatrix rows cols).det
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous fun y ↦
    fderiv ℝ (fun z ↦ g z (rows i)) y
      ((Pi.basisFun ℝ (Fin a)) (cols j))
  exact ((contDiff_pi.mp hg (rows i)).continuous_fderiv one_ne_zero).clm_apply
    continuous_const

/-- In a local chart whose first coordinate is `f`, equality of the derivative
kernels forces the derivative of `g` in every vertical chart direction to
vanish. -/
theorem fderiv_const_fst_openPartialHomeomorph_eq_zero
    {E F G K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (f : E → F) (g : E → G) (e : OpenPartialHomeomorph E (F × K))
    (hfst : ∀ y, (e y).1 = f y) {q : F × K}
    (hq : q ∈ e.target) (hinv : DifferentiableAt ℝ e.symm q)
    (hf : DifferentiableAt ℝ f (e.symm q))
    (hg : DifferentiableAt ℝ g (e.symm q))
    (hker : LinearMap.ker (fderiv ℝ g (e.symm q)).toLinearMap =
      LinearMap.ker (fderiv ℝ f (e.symm q)).toLinearMap) :
    fderiv ℝ (fun z : K ↦ g (e.symm (q.1, z))) q.2 = 0 := by
  have hpair : HasFDerivAt (fun z : K ↦ (q.1, z))
      (ContinuousLinearMap.inr ℝ F K) q.2 :=
    hasFDerivAt_prodMk_right q.1 q.2
  have hinvPair : HasFDerivAt (fun z : K ↦ e.symm (q.1, z))
      ((fderiv ℝ e.symm q).comp (ContinuousLinearMap.inr ℝ F K)) q.2 :=
    hinv.hasFDerivAt.comp q.2 hpair
  have htotal : HasFDerivAt (fun z : K ↦ g (e.symm (q.1, z)))
      ((fderiv ℝ g (e.symm q)).comp
        ((fderiv ℝ e.symm q).comp (ContinuousLinearMap.inr ℝ F K))) q.2 :=
    hg.hasFDerivAt.comp q.2 hinvPair
  rw [htotal.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    zero_apply]
  let tangent := fderiv ℝ e.symm q (0, v)
  have hright :
      (fun p : F × K ↦ f (e.symm p)) =ᶠ[𝓝 q] fun p ↦ p.1 :=
    (e.eventually_right_inverse hq).mono fun p hp ↦
      (hfst (e.symm p)).symm.trans (congrArg Prod.fst hp)
  have hcomp : HasFDerivAt (fun p : F × K ↦ f (e.symm p))
      ((fderiv ℝ f (e.symm q)).comp (fderiv ℝ e.symm q)) q :=
    hf.hasFDerivAt.comp q hinv.hasFDerivAt
  have htangentSelected : fderiv ℝ f (e.symm q) tangent = 0 := by
    have hderiv := congrArg
      (fun L : (F × K) →L[ℝ] F ↦ L (0, v))
      hright.fderiv_eq
    rw [hcomp.fderiv] at hderiv
    rw [fderiv_fst] at hderiv
    change fderiv ℝ f (e.symm q) tangent = (0 : F) at hderiv
    exact hderiv
  have htangentMemSelected :
      tangent ∈ LinearMap.ker (fderiv ℝ f (e.symm q)).toLinearMap := by
    apply LinearMap.mem_ker.mpr
    change fderiv ℝ f (e.symm q) tangent = 0
    exact htangentSelected
  have htangentMemFull :
      tangent ∈ LinearMap.ker (fderiv ℝ g (e.symm q)).toLinearMap := by
    rw [hker]
    exact htangentMemSelected
  have htangentFull := LinearMap.mem_ker.mp htangentMemFull
  change fderiv ℝ g (e.symm q) tangent = 0 at htangentFull
  simpa only [tangent] using htangentFull

/-- If a selected `k × k` minor is nonzero at `x` and the full derivative has
rank at most `k` throughout a neighborhood of `x`, then on some open
neighborhood the full map has exactly the same fibers as its selected output
map. -/
theorem exists_open_nhds_eq_of_selectedOutputMap_eq_of_rank_le
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) (x : RealEuclidean a)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a)
    (hminor : standardJacobianMinor g rows cols x ≠ 0)
    (hrank : ∀ᶠ y in 𝓝 x,
      Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) ≤ k) :
    ∃ U : Set (RealEuclidean a),
      IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U,
          selectedOutputMap g rows y = selectedOutputMap g rows z →
            g y = g z := by
  let f := selectedOutputMap g rows
  have hf : ContDiff ℝ 1 f := by
    change ContDiff ℝ 1 (fun y i ↦ g y (rows i))
    rw [contDiff_pi]
    intro i
    exact contDiff_pi.mp hg (rows i)
  have hsurj : Function.Surjective (fderiv ℝ f x) :=
    fderiv_selectedOutputMap_surjective_of_standardJacobianMinor_ne_zero
      (hg.differentiable one_ne_zero x) rows cols hminor
  have hsurjRange : (fderiv ℝ f x).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hstrict : HasStrictFDerivAt f (fderiv ℝ f x) x :=
    hf.contDiffAt.hasStrictFDerivAt one_ne_zero
  let hkernel : (fderiv ℝ f x).ker.ClosedComplemented :=
    (fderiv ℝ f x).ker_closedComplemented_of_finiteDimensional_range
  let chartData :=
    hstrict.implicitFunctionDataOfComplemented f (fderiv ℝ f x)
      hsurjRange hkernel
  let e := chartData.toOpenPartialHomeomorph
  have hxsource : x ∈ e.source := by
    exact chartData.pt_mem_toOpenPartialHomeomorph_source
  have hfst : ∀ y, (e y).1 = f y := by
    intro y
    rfl
  have hrightCont : ContDiff ℝ 1
      (fun y : RealEuclidean a ↦ Classical.choose hkernel (y - x)) :=
    (Classical.choose hkernel).contDiff.comp
      (contDiff_id.sub contDiff_const)
  have hchartCont : ContDiff ℝ 1 chartData.prodFun := by
    change ContDiff ℝ 1
      (fun y : RealEuclidean a ↦
        (f y, Classical.choose hkernel (y - x)))
    exact hf.prodMk hrightCont
  have hinverseAt : ContDiffAt ℝ 1 e.symm (e x) := by
    apply e.contDiffAt_symm (e.map_source hxsource)
    · rw [e.left_inv hxsource]
      exact chartData.hasStrictFDerivAt.hasFDerivAt
    · rw [e.left_inv hxsource]
      exact hchartCont.contDiffAt
  have hminorContinuous : Continuous (standardJacobianMinor g rows cols) :=
    continuous_standardJacobianMinor_of_contDiff_one hg rows cols
  have hminorEventually :
      ∀ᶠ y in 𝓝 x, standardJacobianMinor g rows cols y ≠ 0 :=
    (isOpen_ne_fun hminorContinuous continuous_const).eventually_mem hminor
  have htendsto : Tendsto e.symm (𝓝 (e x)) (𝓝 x) :=
    e.tendsto_symm hxsource
  have hgood : ∀ᶠ q in 𝓝 (e x),
      q ∈ e.target ∧
        ContDiffAt ℝ 1 e.symm q ∧
        standardJacobianMinor g rows cols (e.symm q) ≠ 0 ∧
        Module.finrank ℝ
          (LinearMap.range (fderiv ℝ g (e.symm q)).toLinearMap) ≤ k := by
    filter_upwards [e.open_target.eventually_mem (e.map_source hxsource),
      hinverseAt.eventually (by simp), htendsto.eventually hminorEventually,
      htendsto.eventually hrank] with q hq hinv hqminor hqrank
    exact ⟨hq, hinv, hqminor, hqrank⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let U : Set (RealEuclidean a) :=
    e.source ∩ e ⁻¹' Metric.ball (e x) ε
  have hUopen : IsOpen U :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  have hxU : x ∈ U := by
    exact ⟨hxsource, Metric.mem_ball_self hε⟩
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hy z hz hselected
  have hyball : e y ∈ Metric.ball (e x) ε := hy.2
  have hzball : e z ∈ Metric.ball (e x) ε := hz.2
  have hfirst : (e y).1 = (e z).1 := by
    rw [hfst y, hfst z]
    exact hselected
  let s : RealEuclidean k := (e y).1
  let slice : Set (fderiv ℝ f x).ker :=
    {v | (s, v) ∈ Metric.ball (e x) ε}
  let H : (fderiv ℝ f x).ker → RealEuclidean b :=
    fun v ↦ g (e.symm (s, v))
  have hsliceOpen : IsOpen slice := by
    exact Metric.isOpen_ball.preimage (continuous_const.prodMk continuous_id)
  have hsliceConvex : Convex ℝ slice := by
    rw [convex_iff_add_mem]
    intro v₁ hv₁ v₂ hv₂ α β hα hβ hab
    have hcomb := (convex_ball (e x) ε)
      hv₁ hv₂ hα hβ hab
    simpa only [slice, Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk,
      ← add_smul, hab, one_smul] using hcomb
  have hHdiff : DifferentiableOn ℝ H slice := by
    intro v hv
    have hq := (hball hv).2.1
    have hpair : DifferentiableAt ℝ
        (fun w : (fderiv ℝ f x).ker ↦ (s, w)) v :=
      (hasFDerivAt_prodMk_right s v).differentiableAt
    have hinvComp : DifferentiableAt ℝ
        (fun w : (fderiv ℝ f x).ker ↦ e.symm (s, w)) v :=
      (hq.differentiableAt one_ne_zero).comp v hpair
    exact ((hg.differentiable one_ne_zero (e.symm (s, v))).comp v
      hinvComp).differentiableWithinAt
  have hHzero : slice.EqOn (fderiv ℝ H) 0 := by
    intro v hv
    obtain ⟨hqtarget, hqinverse, hqminor, hqrank⟩ := hball hv
    have hqsurj : Function.Surjective (fderiv ℝ f (e.symm (s, v))) :=
      fderiv_selectedOutputMap_surjective_of_standardJacobianMinor_ne_zero
        (hg.differentiable one_ne_zero (e.symm (s, v))) rows cols hqminor
    have hqker :
        LinearMap.ker (fderiv ℝ g (e.symm (s, v))).toLinearMap =
          LinearMap.ker (fderiv ℝ f (e.symm (s, v))).toLinearMap :=
      ker_fderiv_eq_ker_fderiv_selectedOutputMap_of_rank_le
        (hg.differentiable one_ne_zero (e.symm (s, v))) rows hqsurj hqrank
    exact fderiv_const_fst_openPartialHomeomorph_eq_zero
      f g e hfst hqtarget (hqinverse.differentiableAt one_ne_zero)
      (hf.differentiable one_ne_zero (e.symm (s, v)))
      (hg.differentiable one_ne_zero (e.symm (s, v))) hqker
  have hySlice : (e y).2 ∈ slice := by
    simpa only [slice, Set.mem_ofPred_eq, s, Prod.eta] using hyball
  have hzSlice : (e z).2 ∈ slice := by
    change (s, (e z).2) ∈ Metric.ball (e x) ε
    rw [show (s, (e z).2) = e z by
      apply Prod.ext
      · exact hfirst
      · rfl]
    exact hzball
  have hH : H (e y).2 = H (e z).2 :=
    hsliceOpen.is_const_of_fderiv_eq_zero hsliceConvex.isPreconnected
      hHdiff hHzero hySlice hzSlice
  calc
    g y = H (e y).2 := by
      rw [show H (e y).2 = g (e.symm (e y)) by
        rfl, e.left_inv hy.1]
    _ = H (e z).2 := hH
    _ = g z := by
      rw [show H (e z).2 = g (e.symm (e z)) by
        change g (e.symm (s, (e z).2)) = _
        rw [show (s, (e z).2) = e z by
          apply Prod.ext
          · exact hfirst
          · rfl], e.left_inv hz.1]

/-- The zero-rank case of the local fiber theorem.  Here the selected map has
codomain `Fin 0 → ℝ`, so the conclusion is local constancy of `g`. -/
theorem exists_open_nhds_eq_of_fderiv_rank_zero
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) (x : RealEuclidean a)
    (hrank : ∀ᶠ y in 𝓝 x,
      Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) ≤ 0) :
    ∃ U : Set (RealEuclidean a),
      IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U, g y = g z := by
  let emptyEmbedding (n : ℕ) : Fin 0 ↪ Fin n :=
    ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
  let rows : Fin 0 ↪ Fin b := emptyEmbedding b
  let cols : Fin 0 ↪ Fin a := emptyEmbedding a
  have hminor : standardJacobianMinor g rows cols x ≠ 0 := by
    rw [standardJacobianMinor, Matrix.det_fin_zero]
    exact one_ne_zero
  obtain ⟨U, hUopen, hxU, hU⟩ :=
    exists_open_nhds_eq_of_selectedOutputMap_eq_of_rank_le
      hg x rows cols hminor hrank
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hy z hz
  exact hU y hy z hz (Subsingleton.elim _ _)

end AbelFormalization
