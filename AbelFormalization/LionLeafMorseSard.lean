import AbelFormalization.LionLemma4SectionAssembly
import AbelFormalization.CharbonnelSardianProjectionCriticalValues
import AbelFormalization.MorseSardNonflatHypersurface
import AbelFormalization.RectangularMorseSard

/-!
# Rectangular Morse--Sard on a carpeted leaf

Lion's Lemma 4 applies Sard's theorem to the restriction of a smooth map to
a carpeted leaf.  This file transfers the Euclidean rectangular statement to
that constrained setting.  The proof uses the implicit-function chart of the
leaf equations and a countable local-to-global assembly.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Linear algebra for a constrained critical point -/

/-- Append two continuous linear maps in `Fin` coordinates. -/
def finAppendContinuousLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q p : ℕ}
    (A : E →L[ℝ] RealEuclidean q)
    (B : E →L[ℝ] RealEuclidean p) :
    E →L[ℝ] RealEuclidean (q + p) :=
  ContinuousLinearMap.pi fun i ↦
    Fin.addCases
      (fun j ↦ (ContinuousLinearMap.proj j).comp A)
      (fun j ↦ (ContinuousLinearMap.proj j).comp B) i

@[simp]
theorem finAppendContinuousLinearMap_apply_castAdd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q p : ℕ}
    (A : E →L[ℝ] RealEuclidean q)
    (B : E →L[ℝ] RealEuclidean p) (v : E) (i : Fin q) :
    finAppendContinuousLinearMap A B v (Fin.castAdd p i) = A v i := by
  simp [finAppendContinuousLinearMap]

@[simp]
theorem finAppendContinuousLinearMap_apply_natAdd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q p : ℕ}
    (A : E →L[ℝ] RealEuclidean q)
    (B : E →L[ℝ] RealEuclidean p) (v : E) (i : Fin p) :
    finAppendContinuousLinearMap A B v (Fin.natAdd q i) = B v i := by
  simp [finAppendContinuousLinearMap]

/-- If the first block is surjective, the appended map is surjective exactly
when the second block is surjective on the kernel of the first. -/
theorem finAppendContinuousLinearMap_surjective_iff_restrictKer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q p : ℕ}
    (A : E →L[ℝ] RealEuclidean q)
    (B : E →L[ℝ] RealEuclidean p)
    (hA : Function.Surjective A) :
    Function.Surjective (finAppendContinuousLinearMap A B) ↔
      Function.Surjective (B.comp A.ker.subtypeL) := by
  constructor
  · intro hAB z
    let target : RealEuclidean (q + p) :=
      Fin.addCases (fun _ ↦ 0) z
    obtain ⟨v, hv⟩ := hAB target
    have hAv : A v = 0 := by
      funext i
      have hi := congrFun hv (Fin.castAdd p i)
      simpa [target] using hi
    let w : A.ker := ⟨v, hAv⟩
    refine ⟨w, ?_⟩
    funext i
    have hi := congrFun hv (Fin.natAdd q i)
    simpa [w, target, ContinuousLinearMap.comp_apply] using hi
  · intro hB target
    let left : RealEuclidean q := fun i ↦ target (Fin.castAdd p i)
    let right : RealEuclidean p := fun i ↦ target (Fin.natAdd q i)
    obtain ⟨v, hv⟩ := hA left
    obtain ⟨w, hw⟩ := hB (right - B v)
    refine ⟨v + (w : E), ?_⟩
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · rw [finAppendContinuousLinearMap_apply_castAdd, map_add]
      have hwA : A (w : E) = 0 := w.property
      rw [hv, hwA, add_zero]
    · rw [finAppendContinuousLinearMap_apply_natAdd, map_add]
      have hwB : B (w : E) = right - B v := by
        simpa [ContinuousLinearMap.comp_apply] using hw
      rw [hwB]
      simp [right]

/-- Composing with a map whose range is a prescribed subspace has the same
surjectivity as restricting the outer map to that subspace. -/
theorem surjective_comp_iff_restrict_of_range_eq
    {E V P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (B : E →L[ℝ] P) (d : V →L[ℝ] E) (K : Submodule ℝ E)
    (hd : d.range = K) :
    Function.Surjective (B.comp d) ↔
      Function.Surjective (B.comp K.subtypeL) := by
  constructor
  · intro h z
    obtain ⟨v, hv⟩ := h z
    have hdv : d v ∈ K := by
      rw [← hd]
      exact ⟨v, rfl⟩
    exact ⟨⟨d v, hdv⟩, by
      simpa [ContinuousLinearMap.comp_apply] using hv⟩
  · intro h z
    obtain ⟨k, hkz⟩ := h z
    have hk : (k : E) ∈ d.range := by
      rw [hd]
      exact k.property
    obtain ⟨v, hv⟩ := hk
    refine ⟨v, ?_⟩
    have hkz' : B (k : E) = z := by
      simpa [ContinuousLinearMap.comp_apply] using hkz
    exact (congrArg B hv).trans hkz'

/-- In an implicit chart whose first coordinate is the constraint map, the
derivative of a zero-level slice has range exactly the tangent kernel. -/
theorem range_fderiv_implicitZeroSlice_eq_ker
    {E F K V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : E → F) (e : OpenPartialHomeomorph E (F × K))
    (hfst : ∀ y, (e y).1 = f y) (kappa : V ≃L[ℝ] K)
    {y : E} {z : V}
    (hy : y ∈ e.source) (hey : e y = (0, kappa z))
    (he : DifferentiableAt ℝ e y)
    (hinv : DifferentiableAt ℝ e.symm (e y))
    (hf : DifferentiableAt ℝ f y)
    (hdim : Module.finrank ℝ V =
      Module.finrank ℝ (fderiv ℝ f y).ker) :
    (fderiv ℝ (fun w : V ↦ e.symm (0, kappa w)) z).range =
      (fderiv ℝ f y).ker := by
  let pair : V → F × K := fun w ↦ (0, kappa w)
  let gamma : V → E := fun w ↦ e.symm (pair w)
  have hpair : HasFDerivAt pair
      ((ContinuousLinearMap.inr ℝ F K).comp
        (kappa : V →L[ℝ] K)) z := by
    exact (hasFDerivAt_const (0 : F) z).prodMk
      kappa.hasFDerivAt
  have heyz : e y = pair z := by
    exact hey
  have hpairTarget : pair z ∈ e.target := by
    rw [← heyz]
    exact e.map_source hy
  have hgamma : HasFDerivAt gamma
      ((fderiv ℝ e.symm (pair z)).comp
        ((ContinuousLinearMap.inr ℝ F K).comp
          (kappa : V →L[ℝ] K))) z := by
    have hinv' : HasFDerivAt e.symm
        (fderiv ℝ e.symm (pair z)) (pair z) := by
      simpa only [← heyz] using hinv.hasFDerivAt
    exact hinv'.comp z hpair
  have hgammaValue : gamma z = y := by
    simpa only [gamma, ← heyz] using e.left_inv hy
  have hright : (fun w ↦ e (gamma w)) =ᶠ[nhds z] pair := by
    have htendsto : Tendsto pair (nhds z) (nhds (pair z)) :=
      hpair.continuousAt
    filter_upwards
      [htendsto.eventually (e.open_target.mem_nhds hpairTarget)] with w hw
    exact e.right_inv hw
  have hcomp : HasFDerivAt (fun w ↦ e (gamma w))
      ((fderiv ℝ e y).comp
        ((fderiv ℝ e.symm (pair z)).comp
          ((ContinuousLinearMap.inr ℝ F K).comp
            (kappa : V →L[ℝ] K)))) z := by
    have he' : HasFDerivAt e (fderiv ℝ e y) (gamma z) := by
      simpa only [hgammaValue] using he.hasFDerivAt
    exact he'.comp z hgamma
  have hderivRight :
      (fderiv ℝ e y).comp
          ((fderiv ℝ e.symm (pair z)).comp
            ((ContinuousLinearMap.inr ℝ F K).comp
              (kappa : V →L[ℝ] K))) =
        (ContinuousLinearMap.inr ℝ F K).comp
          (kappa : V →L[ℝ] K) := by
    have h := hright.fderiv_eq (𝕜 := ℝ)
    rw [hcomp.fderiv, hpair.fderiv] at h
    exact h
  have hdInjective : Function.Injective
      (fderiv ℝ gamma z) := by
    intro u v huv
    apply kappa.injective
    have huv' := congrArg (fderiv ℝ e y) huv
    have hgammaDeriv : fderiv ℝ gamma z =
        (fderiv ℝ e.symm (pair z)).comp
          ((ContinuousLinearMap.inr ℝ F K).comp
            (kappa : V →L[ℝ] K)) := hgamma.fderiv
    rw [hgammaDeriv] at huv'
    have hu := congrArg
      (fun T : V →L[ℝ] (F × K) ↦ T u) hderivRight
    have hv := congrArg
      (fun T : V →L[ℝ] (F × K) ↦ T v) hderivRight
    simpa [ContinuousLinearMap.comp_apply] using hu.symm.trans (huv'.trans hv)
  have hfgamma : (fun w ↦ f (gamma w)) =ᶠ[nhds z]
      (fun _ ↦ (0 : F)) := by
    filter_upwards [hright] with w hw
    have hfirst := congrArg Prod.fst hw
    simpa only [hfst, pair] using hfirst
  have hfgammaDeriv :
      (fderiv ℝ f y).comp (fderiv ℝ gamma z) = 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f y) (gamma z) := by
      simpa only [hgammaValue] using hf.hasFDerivAt
    have hchain : fderiv ℝ (fun w ↦ f (gamma w)) z =
        (fderiv ℝ f y).comp (fderiv ℝ gamma z) := by
      have hc := (hf'.comp z hgamma).fderiv
      simpa only [Function.comp_def, hgamma.fderiv] using hc
    have h := hfgamma.fderiv_eq (𝕜 := ℝ)
    rw [hchain] at h
    simpa using h
  have hrangeLe : (fderiv ℝ gamma z).range ≤
      (fderiv ℝ f y).ker := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    have hv := congrArg
      (fun T : V →L[ℝ] F ↦ T v) hfgammaDeriv
    simpa [ContinuousLinearMap.comp_apply] using hv
  apply Submodule.eq_of_le_of_finrank_eq hrangeLe
  rw [LinearMap.finrank_range_of_inj hdInjective]
  exact hdim

/-- Rank-nullity for a surjection between standard Euclidean spaces. -/
theorem finrank_ker_eq_sub_of_surjective
    {n q : ℕ} (A : RealEuclidean n →L[ℝ] RealEuclidean q)
    (hA : Function.Surjective A) :
    Module.finrank ℝ A.ker = n - q := by
  have hrange : A.range = ⊤ := LinearMap.range_eq_top.mpr hA
  have hrankNullity := A.toLinearMap.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at hrankNullity
  simp only [Module.finrank_fin_fun] at hrankNullity
  omega

/-- Standard Euclidean coordinates on the tangent kernel of a Euclidean
submersion. -/
def euclideanKernelEquivOfSurjective
    {n q : ℕ} (A : RealEuclidean n →L[ℝ] RealEuclidean q)
    (hA : Function.Surjective A) :
    RealEuclidean (n - q) ≃L[ℝ] A.ker :=
  ContinuousLinearEquiv.ofFinrankEq <| by
    rw [Module.finrank_fin_fun,
      finrank_ker_eq_sub_of_surjective A hA]

/-- In a smooth implicit chart, surjectivity of the constrained derivative
is equivalent to surjectivity of the Euclidean slice derivative. -/
theorem surjective_fderiv_implicitZeroSlice_iff_restrictKer
    {E F K V P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (f : E → F) (g : E → P)
    (e : OpenPartialHomeomorph E (F × K))
    (hfst : ∀ y, (e y).1 = f y) (kappa : V ≃L[ℝ] K)
    {y : E} {z : V}
    (hy : y ∈ e.source) (hey : e y = (0, kappa z))
    (he : DifferentiableAt ℝ e y)
    (hinv : DifferentiableAt ℝ e.symm (e y))
    (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y)
    (hdim : Module.finrank ℝ V =
      Module.finrank ℝ (fderiv ℝ f y).ker) :
    Function.Surjective
        (fderiv ℝ (fun w : V ↦ g (e.symm (0, kappa w))) z) ↔
      Function.Surjective
        ((fderiv ℝ g y).comp
          (fderiv ℝ f y).ker.subtypeL) := by
  let gamma : V → E := fun w ↦ e.symm (0, kappa w)
  have hpair : HasFDerivAt (fun w : V ↦ (0, kappa w))
      ((ContinuousLinearMap.inr ℝ F K).comp
        (kappa : V →L[ℝ] K)) z :=
    (hasFDerivAt_const (0 : F) z).prodMk kappa.hasFDerivAt
  have htarget : e y ∈ e.target := e.map_source hy
  have hgammaValue : gamma z = y := by
    simpa only [gamma, ← hey] using e.left_inv hy
  have hgamma : DifferentiableAt ℝ gamma z := by
    have hinv' : DifferentiableAt ℝ e.symm (0, kappa z) := by
      simpa only [← hey] using hinv
    exact hinv'.comp z hpair.differentiableAt
  have hcomp : fderiv ℝ (fun w : V ↦ g (gamma w)) z =
      (fderiv ℝ g y).comp (fderiv ℝ gamma z) := by
    have hg' : DifferentiableAt ℝ g (gamma z) := by
      simpa only [hgammaValue] using hg
    have hc := (hg'.hasFDerivAt.comp z hgamma.hasFDerivAt).fderiv
    rw [hgammaValue] at hc
    simpa only [Function.comp_def] using hc
  have hrange : (fderiv ℝ gamma z).range =
      (fderiv ℝ f y).ker := by
    exact range_fderiv_implicitZeroSlice_eq_ker
      f e hfst kappa hy hey he hinv hf hdim
  change Function.Surjective (fderiv ℝ (fun w : V ↦ g (gamma w)) z) ↔ _
  rw [hcomp]
  exact surjective_comp_iff_restrict_of_range_eq
    (fderiv ℝ g y) (fderiv ℝ gamma z)
      (fderiv ℝ f y).ker hrange

namespace LionCarpetedLeaf

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)} {n q p : ℕ}

/-- The critical source of `g` on a carpeted leaf. -/
def leafCriticalSource
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p) : Set (RealEuclidean n) :=
  {x | x ∈ L.carrier ∧
    ¬ Function.Surjective (fderiv ℝ (L.definingTupleAppend g) x)}

theorem criticalTargetSet_eq_image_leafCriticalSource
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p) :
    L.criticalTargetSet g = g '' L.leafCriticalSource g := by
  ext t
  simp only [criticalTargetSet, leafCriticalSource, Set.mem_ofPred_eq,
    Set.mem_image]
  aesop

/-- The derivative of the appended defining tuple is the coordinate append
of the two derivatives. -/
theorem fderiv_definingTupleAppend
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    {x : RealEuclidean n}
    (hf : DifferentiableAt ℝ L.equations x)
    (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ (L.definingTupleAppend g) x =
      finAppendContinuousLinearMap
        (fderiv ℝ L.equations x) (fderiv ℝ g x) := by
  rw [fderiv_pi]
  · apply ContinuousLinearMap.ext
    intro v
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [ContinuousLinearMap.pi_apply,
        finAppendContinuousLinearMap_apply_castAdd]
      rw [show (fun y ↦ L.definingTupleAppend g y (Fin.castAdd p j)) =
          (fun y ↦ L.equations y j) by
        funext y
        exact L.definingTupleAppend_castAdd g y j]
      rw [fderiv_apply hf]
      rfl
    · simp only [ContinuousLinearMap.pi_apply,
        finAppendContinuousLinearMap_apply_natAdd]
      rw [show (fun y ↦ L.definingTupleAppend g y (Fin.natAdd q j)) =
          (fun y ↦ g y j) by
        funext y
        exact L.definingTupleAppend_natAdd g y j]
      rw [fderiv_apply hg]
      rfl
  · intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa only [L.definingTupleAppend_castAdd] using
        (differentiableAt_pi.mp hf j)
    · simpa only [L.definingTupleAppend_natAdd] using
        (differentiableAt_pi.mp hg j)

/-- Criticality of `g` on the leaf is criticality of its derivative
restricted to the tangent kernel of the defining equations. -/
theorem fderiv_definingTupleAppend_surjective_iff_restrictKer
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    {x : RealEuclidean n}
    (hf : DifferentiableAt ℝ L.equations x)
    (hg : DifferentiableAt ℝ g x)
    (hsub : Function.Surjective (fderiv ℝ L.equations x)) :
    Function.Surjective (fderiv ℝ (L.definingTupleAppend g) x) ↔
      Function.Surjective
        ((fderiv ℝ g x).comp
          (fderiv ℝ L.equations x).ker.subtypeL) := by
  rw [L.fderiv_definingTupleAppend g hf hg]
  exact finAppendContinuousLinearMap_surjective_iff_restrictKer
    (fderiv ℝ L.equations x) (fderiv ℝ g x) hsub

/-! ## Local implicit-chart Sard estimate -/

/-- Around each constrained critical point, the constrained critical values
are contained in the critical values of one Euclidean map at any prescribed
positive finite differentiability order. -/
theorem exists_local_leafCriticalSource_image_null_of_order
    (r : ℕ) (hr : 0 < r)
    (hMS : ∀ H : RealEuclidean (n - q) → RealEuclidean p,
      ContDiff ℝ r H →
        volume (standardJacobianCriticalValueSet H) = 0)
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (hdim : p + q ≤ n)
    {x : RealEuclidean n} (hx : x ∈ L.leafCriticalSource g) :
    ∃ N : Set (RealEuclidean n),
      IsOpen N ∧ x ∈ N ∧
        volume (g '' (L.leafCriticalSource g ∩ N)) = 0 := by
  have hpdim : p ≤ n - q := by omega
  have hfSmooth : ContDiff ℝ r L.equations :=
    (L.equations_contDiff hsmooth).of_le (by simp)
  have hgSmooth : ContDiff ℝ r g := by
    rw [contDiff_pi]
    intro i
    exact (hsmooth n (fun y ↦ g y i) (hg i)).of_le (by simp)
  let A : RealEuclidean n →L[ℝ] RealEuclidean q :=
    fderiv ℝ L.equations x
  have hA : Function.Surjective A :=
    L.fderiv_surjective x hx.1.1
  have hArange : A.range = ⊤ := LinearMap.range_eq_top.mpr hA
  have hstrict : HasStrictFDerivAt L.equations A x := by
    exact hfSmooth.contDiffAt.hasStrictFDerivAt
      (by exact_mod_cast hr.ne')
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
      exact hx.1.2
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
  have hHnull : volume (standardJacobianCriticalValueSet H) = 0 := by
    exact hMS H hHSmooth
  let coord : RealEuclidean n → RealEuclidean (n - q) :=
    fun y ↦ kappa.symm (e y).2
  have hcoordx : coord x = 0 := by
    simp only [coord, hex, map_zero]
  have hcoordTendsto : Tendsto coord (nhds x) (nhds 0) := by
    have heCont : ContinuousAt e x := e.continuousAt hxSource
    have hsnd : Tendsto (fun y ↦ (e y).2) (nhds x) (nhds (e x).2) :=
      continuous_snd.continuousAt.comp heCont
    have hk := kappa.symm.continuous.continuousAt.tendsto.comp hsnd
    simpa only [coord, Function.comp_def, hex, map_zero] using hk
  have hinverseEventually :
      ∀ᶠ y in nhds (e x), ContDiffAt ℝ r e.symm y :=
    hinverseAt.eventually (by simp)
  have hgood :
      {y | y ∈ e.source ∧
        ContDiffAt ℝ r e.symm (e y) ∧
        H (coord y) = slice (coord y) ∧
        fderiv ℝ H (coord y) = fderiv ℝ slice (coord y)} ∈ nhds x := by
    filter_upwards
      [e.open_source.mem_nhds hxSource,
        (e.continuousAt hxSource).eventually hinverseEventually,
        hcoordTendsto.eventually hHeq,
        hcoordTendsto.eventually (hHeq.fderiv (𝕜 := ℝ))]
      with y hySource hyInv hyEq hyDeriv
    exact ⟨hySource, hyInv, hyEq, hyDeriv⟩
  let N : Set (RealEuclidean n) := interior
    {y | y ∈ e.source ∧
      ContDiffAt ℝ r e.symm (e y) ∧
      H (coord y) = slice (coord y) ∧
      fderiv ℝ H (coord y) = fderiv ℝ slice (coord y)}
  have hNopen : IsOpen N := isOpen_interior
  have hxN : x ∈ N := mem_interior_iff_mem_nhds.mpr hgood
  refine ⟨N, hNopen, hxN, ?_⟩
  apply measure_mono_null _ hHnull
  rintro t ⟨y, hy, rfl⟩
  have hyCritical := hy.1
  have hyLeaf := hyCritical.1
  have hyGood := interior_subset hy.2
  let z : RealEuclidean (n - q) := coord y
  have hey : e y = (0, kappa z) := by
    apply Prod.ext
    · exact (hfst y).trans hyLeaf.2
    · simp only [z, coord, kappa.apply_symm_apply]
  have hyInv : DifferentiableAt ℝ e.symm (e y) :=
    hyGood.2.1.differentiableAt (by exact_mod_cast hr.ne')
  have hyEDiff : DifferentiableAt ℝ e y :=
    heSmooth.differentiable (by exact_mod_cast hr.ne') y
  have hyFDiff : DifferentiableAt ℝ L.equations y :=
    hfSmooth.differentiable (by exact_mod_cast hr.ne') y
  have hyGDiff : DifferentiableAt ℝ g y :=
    hgSmooth.differentiable (by exact_mod_cast hr.ne') y
  have hySub : Function.Surjective
      (fderiv ℝ L.equations y) :=
    L.fderiv_surjective y hyLeaf.1
  have hyKernelDim : Module.finrank ℝ (RealEuclidean (n - q)) =
      Module.finrank ℝ (fderiv ℝ L.equations y).ker := by
    rw [Module.finrank_fin_fun,
      finrank_ker_eq_sub_of_surjective _ hySub]
  have hyRestrictCritical : ¬ Function.Surjective
      ((fderiv ℝ g y).comp
        (fderiv ℝ L.equations y).ker.subtypeL) := by
    intro hsurj
    exact hyCritical.2
      ((L.fderiv_definingTupleAppend_surjective_iff_restrictKer
        g hyFDiff hyGDiff hySub).mpr hsurj)
  have hySliceCritical : ¬ Function.Surjective
      (fderiv ℝ slice z) := by
    intro hsurj
    apply hyRestrictCritical
    exact (surjective_fderiv_implicitZeroSlice_iff_restrictKer
      L.equations g e hfst kappa hyGood.1 hey hyEDiff hyInv
        hyFDiff hyGDiff hyKernelDim).mp hsurj
  have hyHCritical : ¬ Function.Surjective
      (fderiv ℝ H z) := by
    intro hsurj
    apply hySliceCritical
    rw [← hyGood.2.2.2]
    exact hsurj
  rw [mem_standardJacobianCriticalValueSet_iff_nonsurjective
    H (hHSmooth.differentiable (by exact_mod_cast hr.ne'))]
  refine ⟨z, ?_, hyHCritical⟩
  calc
    H z = slice z := hyGood.2.2.1
    _ = g (e.symm (e y)) := by
      change g (e.symm ((0 : RealEuclidean q), kappa z)) = _
      rw [← hey]
    _ = g y := by rw [e.left_inv hyGood.1]

/-- The sharp finite-order rectangular Morse--Sard hypothesis supplies the
order used in the local leaf chart. -/
theorem exists_local_leafCriticalSource_image_null
    (hMS : ∀ {a b : ℕ}, b ≤ a →
      ∀ H : RealEuclidean a → RealEuclidean b,
        ContDiff ℝ (a - b + 1 : ℕ) H →
          volume (standardJacobianCriticalValueSet H) = 0)
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (hdim : p + q ≤ n)
    {x : RealEuclidean n} (hx : x ∈ L.leafCriticalSource g) :
    ∃ N : Set (RealEuclidean n),
      IsOpen N ∧ x ∈ N ∧
        volume (g '' (L.leafCriticalSource g ∩ N)) = 0 := by
  let r : ℕ := (n - q) - p + 1
  have hr : 0 < r := by
    dsimp only [r]
    omega
  have hpdim : p ≤ n - q := by omega
  apply exists_local_leafCriticalSource_image_null_of_order
    r hr (fun H hH ↦ hMS hpdim H (by simpa only [r] using hH))
      (L := L) (hsmooth := hsmooth) (g := g) (hg := hg) hdim hx

/-- The all-dimensional smooth rectangular Morse--Sard theorem supplies a
finite elementary order in every local leaf chart. -/
theorem exists_local_leafCriticalSource_image_null_of_contDiff_top
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (hdim : p + q ≤ n)
    {x : RealEuclidean n} (hx : x ∈ L.leafCriticalSource g) :
    ∃ N : Set (RealEuclidean n),
      IsOpen N ∧ x ∈ N ∧
        volume (g '' (L.leafCriticalSource g ∩ N)) = 0 := by
  let r : ℕ := morseSardElementaryOrder (n - q)
  have hr : 0 < r := by
    exact morseSardElementaryOrder_pos (n - q)
  have hpdim : p ≤ n - q := by omega
  apply exists_local_leafCriticalSource_image_null_of_order
    r hr (fun H hH ↦
      volume_standardJacobianCriticalValueSet_eq_zero_of_elementaryOrder
        hpdim (by simpa only [r] using hH))
      (L := L) (hsmooth := hsmooth) (g := g) (hg := hg) hdim hx

/-- Null local images around all constrained critical points assemble to
nullity of the complete constrained critical-value set. -/
theorem volume_criticalTargetSet_eq_zero_of_local
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (hlocal : ∀ x ∈ L.leafCriticalSource g,
      ∃ U : Set (RealEuclidean n),
        IsOpen U ∧ x ∈ U ∧
          volume (g '' (L.leafCriticalSource g ∩ U)) = 0) :
    volume (L.criticalTargetSet g) = 0 := by
  let S := L.leafCriticalSource g
  choose U hUopen hxU hUzero using
    fun x : S ↦ hlocal x x.property
  let W : S → Set S := fun x ↦ Subtype.val ⁻¹' U x
  have hW : ∀ x : S, W x ∈ nhds x := by
    intro x
    exact continuousAt_subtype_val.preimage_mem_nhds
      ((hUopen x).mem_nhds (hxU x))
  obtain ⟨T, hTcount, hTcover⟩ :=
    TopologicalSpace.countable_cover_nhds hW
  have hcover : S ⊆ ⋃ x ∈ T, S ∩ U x := by
    intro y hy
    let z : S := ⟨y, hy⟩
    have hz : z ∈ ⋃ x ∈ T, W x := by
      rw [hTcover]
      exact Set.mem_univ z
    simp only [Set.mem_iUnion] at hz ⊢
    obtain ⟨x, hxT, hzx⟩ := hz
    exact ⟨x, hxT, hy, hzx⟩
  have himage : g '' S ⊆
      ⋃ x ∈ T, g '' (S ∩ U x) := by
    rintro z ⟨y, hy, rfl⟩
    have hycover := hcover hy
    simp only [Set.mem_iUnion] at hycover ⊢
    obtain ⟨x, hxT, hyx⟩ := hycover
    exact ⟨x, hxT, y, hyx, rfl⟩
  rw [criticalTargetSet_eq_image_leafCriticalSource]
  apply measure_mono_null himage
  exact (measure_biUnion_null_iff hTcount).mpr
    (fun x _hxT ↦ hUzero x)

/-- Euclidean rectangular Morse--Sard implies the corresponding theorem for
a smooth map restricted to a carpeted leaf. -/
theorem volume_criticalTargetSet_eq_zero_of_rectangularMorseSard
    (hMS : ∀ {a b : ℕ}, b ≤ a →
      ∀ H : RealEuclidean a → RealEuclidean b,
        ContDiff ℝ (a - b + 1 : ℕ) H →
          volume (standardJacobianCriticalValueSet H) = 0)
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (hdim : p + q ≤ n) :
    volume (L.criticalTargetSet g) = 0 := by
  apply L.volume_criticalTargetSet_eq_zero_of_local g
  intro x hx
  exact L.exists_local_leafCriticalSource_image_null
    hMS hsmooth g hg hdim hx

/-- The proved smooth rectangular Morse--Sard theorem gives null constrained
critical values for every smooth map in the family, with no external Sard
hypothesis. -/
theorem volume_criticalTargetSet_eq_zero_of_contDiff_top
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (hdim : p + q ≤ n) :
    volume (L.criticalTargetSet g) = 0 := by
  apply L.volume_criticalTargetSet_eq_zero_of_local g
  intro x hx
  exact L.exists_local_leafCriticalSource_image_null_of_contDiff_top
    hsmooth g hg hdim hx

/-- Rectangular Morse--Sard makes Lion's simultaneous good-target set full:
it applies both to the original leaf and to every selected coefficient leaf,
whose dimension equals the target dimension. -/
theorem volume_compl_lemma4GoodTargetSet_eq_zero_of_rectangularMorseSard
    (hMS : ∀ {a b : ℕ}, b ≤ a →
      ∀ H : RealEuclidean a → RealEuclidean b,
        ContDiff ℝ (a - b + 1 : ℕ) H →
          volume (standardJacobianCriticalValueSet H) = 0)
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n) :
    volume (L.lemma4GoodTargetSet
      hG hsmooth hderiv g hg center hheight hdim)ᶜ = 0 := by
  apply L.volume_compl_lemma4GoodTargetSet_eq_zero
    hG hsmooth hderiv g hg center hheight hdim
  · exact L.volume_criticalTargetSet_eq_zero_of_rectangularMorseSard
      hMS hsmooth g hg (by omega)
  · intro selection
    let K := L.selectedCriticalCoefficientLeaf
      hG hsmooth hderiv g hg center hheight hdim selection
    exact K.volume_criticalTargetSet_eq_zero_of_rectangularMorseSard
      hMS hsmooth g hg (by omega)

/-- Smooth rectangular Morse--Sard makes Lion's simultaneous good-target
set conull without an external finite-order Morse--Sard assumption. -/
theorem volume_compl_lemma4GoodTargetSet_eq_zero_of_contDiff_top
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (hdim : p + q < n) :
    volume (L.lemma4GoodTargetSet
      hG hsmooth hderiv g hg center hheight hdim)ᶜ = 0 := by
  apply L.volume_compl_lemma4GoodTargetSet_eq_zero
    hG hsmooth hderiv g hg center hheight hdim
  · exact L.volume_criticalTargetSet_eq_zero_of_contDiff_top
      hsmooth g hg (by omega)
  · intro selection
    let K := L.selectedCriticalCoefficientLeaf
      hG hsmooth hderiv g hg center hheight hdim selection
    exact K.volume_criticalTargetSet_eq_zero_of_contDiff_top
      hsmooth g hg (by omega)

end LionCarpetedLeaf

end AbelFormalization
