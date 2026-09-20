import AbelFormalization.MorseSardFlatJet
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Nonflat Morse--Sard strata lie on regular hypersurfaces

This file supplies the local geometric step in the classical induction proof
of rectangular Morse--Sard.  Between two consecutive flat-jet loci, a suitable
scalar coordinate of the preceding derivative vanishes and has nonzero
derivative.  Thus every point of that stratum lies on a regular hypersurface,
where the source dimension drops by one.

This is the missing nonflat counterpart to `MorseSardFlatJet`: that file
handles the deepest flat stratum by a Taylor/Hausdorff-dimension estimate,
while the lemmas below expose all remaining strata to hypersurface induction.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The points whose positive derivatives below `r` vanish, but whose
`r`-th derivative does not. -/
def iteratedFDerivFirstNonflatStratum (r : ℕ) (g : E → F) : Set E :=
  iteratedFDerivFlatSet r g \ iteratedFDerivFlatSet (r + 1) g

theorem mem_iteratedFDerivFirstNonflatStratum_iff
    {r : ℕ} {g : E → F} {x : E} (hr : 0 < r) :
    x ∈ iteratedFDerivFirstNonflatStratum r g ↔
      x ∈ iteratedFDerivFlatSet r g ∧ iteratedFDeriv ℝ r g x ≠ 0 := by
  rw [iteratedFDerivFirstNonflatStratum, Set.mem_sdiff]
  constructor
  · rintro ⟨hxflat, hxnot⟩
    refine ⟨hxflat, ?_⟩
    intro hrzero
    apply hxnot
    intro i hi hir
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hir) with hil | rfl
    · exact hxflat i hi hil
    · exact hrzero
  · rintro ⟨hxflat, hrne⟩
    refine ⟨hxflat, ?_⟩
    intro hxnext
    exact hrne (hxnext r hr (by omega))

/-! ## Flat jets under a smooth parameterization -/

/-- If all positive derivatives of the outer map through order `i` vanish,
then the `i`-th derivative of a composition vanishes.  In the
Faà di Bruno formula every ordered partition has a positive number of
parts, so every summand contains one of the vanishing outer derivatives. -/
theorem iteratedFDeriv_comp_eq_zero_of_outer_flat
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : F → G} {f : E → F} {x : E} {i : ℕ}
    (hi : 0 < i)
    (hg : ContDiffAt ℝ i g (f x))
    (hf : ContDiffAt ℝ i f x)
    (hflat : ∀ j : ℕ, 0 < j → j ≤ i →
      iteratedFDeriv ℝ j g (f x) = 0) :
    iteratedFDeriv ℝ i (g ∘ f) x = 0 := by
  rw [iteratedFDeriv_comp hg hf le_rfl]
  rw [FormalMultilinearSeries.taylorComp]
  apply Finset.sum_eq_zero
  intro c _hc
  ext v
  rw [FormalMultilinearSeries.compAlongOrderedFinpartition_apply]
  rw [show ftaylorSeries ℝ g (f x) c.length = 0 by
    exact hflat c.length (c.length_pos hi) c.length_le]
  simp

/-- Flatness of an outer jet survives composition as far as the inner map is
differentiable.  A `C^q` parameterization transports every vanishing
derivative below any order `r ≤ q + 1`; this `+1` is exact because membership
in `iteratedFDerivFlatSet r` only asks for derivatives of order `< r`. -/
theorem mem_iteratedFDerivFlatSet_comp_of_contDiffAt
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : F → G} {f : E → F} {x : E} {r q : ℕ}
    (hrq : r ≤ q + 1)
    (hg : ContDiffAt ℝ q g (f x))
    (hf : ContDiffAt ℝ q f x)
    (hx : f x ∈ iteratedFDerivFlatSet r g) :
    x ∈ iteratedFDerivFlatSet r (g ∘ f) := by
  intro i hi hir
  have hiq : i ≤ q := by omega
  apply iteratedFDeriv_comp_eq_zero_of_outer_flat hi
  · exact hg.of_le (by exact_mod_cast hiq)
  · exact hf.of_le (by exact_mod_cast hiq)
  · intro j hj hji
    exact hx j hj (hji.trans_lt hir)

/-- A nonzero multilinear map to a Euclidean space is nonzero on some tuple
and in some output coordinate. -/
theorem exists_tuple_coordinate_ne_zero_of_continuousMultilinearMap_ne_zero
    {r b : ℕ} {A : E[×r]→L[ℝ] (Fin b → ℝ)} (hA : A ≠ 0) :
    ∃ v : Fin r → E, ∃ j : Fin b, A v j ≠ 0 := by
  by_contra h
  push Not at h
  apply hA
  ext v j
  exact h v j

/-- The scalar function used to cut out a nonflat jet stratum. -/
def nonflatJetCuttingFunction {a b n : ℕ}
    (g : (Fin a → ℝ) → (Fin b → ℝ))
    (v : Fin (n + 1) → (Fin a → ℝ)) (j : Fin b) :
    (Fin a → ℝ) → ℝ :=
  fun y ↦ iteratedFDeriv ℝ n g y (Fin.tail v) j

/-- The cutting function has the expected derivative in the distinguished
first direction. -/
theorem fderiv_nonflatJetCuttingFunction_apply_first
    {a b n : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (n + 1 : ℕ) g)
    (x : Fin a → ℝ) (v : Fin (n + 1) → (Fin a → ℝ))
    (j : Fin b) :
    fderiv ℝ (nonflatJetCuttingFunction g v j) x (v 0) =
      iteratedFDeriv ℝ (n + 1) g x v j := by
  let D : (Fin a → ℝ) →
      (Fin a → ℝ)[×n]→L[ℝ] (Fin b → ℝ) :=
    iteratedFDeriv ℝ n g
  let A : (Fin a → ℝ) → (Fin b → ℝ) :=
    fun y ↦ D y (Fin.tail v)
  have hD : DifferentiableAt ℝ D x :=
    (hg.differentiable_iteratedFDeriv (by norm_cast; omega) x)
  have hA : DifferentiableAt ℝ A x :=
    hD.continuousMultilinear_apply_const (Fin.tail v)
  rw [show nonflatJetCuttingFunction g v j = fun y ↦ A y j by rfl]
  rw [fderiv_apply hA j, ContinuousLinearMap.comp_apply]
  change fderiv ℝ A x (v 0) j = _
  rw [show fderiv ℝ A x (v 0) =
      fderiv ℝ D x (v 0) (Fin.tail v) by
    exact fderiv_continuousMultilinear_apply_const_apply hD (Fin.tail v) (v 0)]
  exact congrArg (fun w : Fin b → ℝ ↦ w j)
    (iteratedFDeriv_succ_apply_left (f := g) (x := x) v).symm

/-- A nonzero value of the next derivative makes the scalar cutting function
a submersion to `ℝ`. -/
theorem surjective_fderiv_nonflatJetCuttingFunction
    {a b n : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (n + 1 : ℕ) g)
    {x : Fin a → ℝ} {v : Fin (n + 1) → (Fin a → ℝ)}
    {j : Fin b} (hv : iteratedFDeriv ℝ (n + 1) g x v j ≠ 0) :
    Function.Surjective
      (fderiv ℝ (nonflatJetCuttingFunction g v j) x) := by
  let c := iteratedFDeriv ℝ (n + 1) g x v j
  have hc : c ≠ 0 := hv
  intro z
  refine ⟨(z / c) • v 0, ?_⟩
  rw [map_smul, fderiv_nonflatJetCuttingFunction_apply_first hg]
  change (z / c) * c = z
  exact div_mul_cancel₀ z hc

/-- Every nonflat layer above the first derivative is locally contained in a
regular scalar zero set.  This is the precise hypersurface step used by the
source-dimension induction in Morse--Sard. -/
theorem exists_regular_hypersurface_of_mem_firstNonflatStratum
    {a b n : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (n + 1 : ℕ) g) (hn : 0 < n)
    {x : Fin a → ℝ}
    (hx : x ∈ iteratedFDerivFirstNonflatStratum (n + 1) g) :
    ∃ phi : (Fin a → ℝ) → ℝ,
      ContDiff ℝ 1 phi ∧ phi x = 0 ∧
        Function.Surjective (fderiv ℝ phi x) ∧
        iteratedFDerivFirstNonflatStratum (n + 1) g ⊆ phi ⁻¹' {0} := by
  have hnext : iteratedFDeriv ℝ (n + 1) g x ≠ 0 :=
    (mem_iteratedFDerivFirstNonflatStratum_iff (by omega)).mp hx |>.2
  obtain ⟨v, j, hv⟩ :=
    exists_tuple_coordinate_ne_zero_of_continuousMultilinearMap_ne_zero hnext
  let phi := nonflatJetCuttingFunction g v j
  have hD : ContDiff ℝ 1 (iteratedFDeriv ℝ n g) :=
    hg.iteratedFDeriv_right (by norm_cast; omega)
  have hphi : ContDiff ℝ 1 phi := by
    change ContDiff ℝ 1
      (fun y ↦ iteratedFDeriv ℝ n g y (Fin.tail v) j)
    let eval : ((Fin a → ℝ)[×n]→L[ℝ] (Fin b → ℝ)) →L[ℝ]
        (Fin b → ℝ) :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ Fin a → ℝ)
        (Fin b → ℝ) (Fin.tail v)
    have hEval : ContDiff ℝ 1
        (fun y ↦ iteratedFDeriv ℝ n g y (Fin.tail v)) := by
      exact eval.contDiff.comp hD
    simpa [Function.comp_def] using
      (contDiff_apply ℝ ℝ j).comp hEval
  have hphix : phi x = 0 := by
    have hxflat :=
      (mem_iteratedFDerivFirstNonflatStratum_iff (by omega)).mp hx |>.1
    have hnzero : iteratedFDeriv ℝ n g x = 0 :=
      hxflat n hn (by omega)
    simp only [phi, nonflatJetCuttingFunction, hnzero, zero_apply,
      Pi.zero_apply]
  refine ⟨phi, hphi, hphix,
    surjective_fderiv_nonflatJetCuttingFunction hg hv, ?_⟩
  intro y hy
  have hyflat :=
    (mem_iteratedFDerivFirstNonflatStratum_iff (by omega)).mp hy |>.1
  have hynzero : iteratedFDeriv ℝ n g y = 0 :=
    hyflat n hn (by omega)
  simp only [phi, nonflatJetCuttingFunction, Set.mem_preimage,
    Set.mem_singleton_iff, hynzero, zero_apply, Pi.zero_apply]

/-- A version of the nonflat cutting lemma which records all differentiability
left after taking the `n`-th derivative.  This is the regularity bookkeeping
needed in the iterated hypersurface argument: a `C^(s+n)` map gives a `C^s`
chart for its first nonflat layer of order `n+1`. -/
theorem exists_contDiff_regular_hypersurface_of_mem_firstNonflatStratum
    {a b n s : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (s + n : ℕ) g) (hs : 0 < s) (hn : 0 < n)
    {x : Fin a → ℝ}
    (hx : x ∈ iteratedFDerivFirstNonflatStratum (n + 1) g) :
    ∃ phi : (Fin a → ℝ) → ℝ,
      ContDiff ℝ s phi ∧ phi x = 0 ∧
        Function.Surjective (fderiv ℝ phi x) ∧
        iteratedFDerivFirstNonflatStratum (n + 1) g ⊆ phi ⁻¹' {0} := by
  have hnext : iteratedFDeriv ℝ (n + 1) g x ≠ 0 :=
    (mem_iteratedFDerivFirstNonflatStratum_iff (by omega)).mp hx |>.2
  obtain ⟨v, j, hv⟩ :=
    exists_tuple_coordinate_ne_zero_of_continuousMultilinearMap_ne_zero hnext
  let phi := nonflatJetCuttingFunction g v j
  have horder : ContDiff ℝ (n + 1 : ℕ) g :=
    hg.of_le (by norm_cast; omega)
  have hD : ContDiff ℝ s (iteratedFDeriv ℝ n g) := by
    simpa only [Nat.cast_add, add_comm] using
      (hg.iteratedFDeriv_right' (i := n))
  have hphi : ContDiff ℝ s phi := by
    change ContDiff ℝ s
      (fun y ↦ iteratedFDeriv ℝ n g y (Fin.tail v) j)
    let eval : ((Fin a → ℝ)[×n]→L[ℝ] (Fin b → ℝ)) →L[ℝ]
        (Fin b → ℝ) :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ Fin a → ℝ)
        (Fin b → ℝ) (Fin.tail v)
    have hEval : ContDiff ℝ s
        (fun y ↦ iteratedFDeriv ℝ n g y (Fin.tail v)) :=
      eval.contDiff.comp hD
    simpa [Function.comp_def] using
      (contDiff_apply ℝ ℝ j).comp hEval
  have hphix : phi x = 0 := by
    have hxflat :=
      (mem_iteratedFDerivFirstNonflatStratum_iff (by omega)).mp hx |>.1
    have hnzero : iteratedFDeriv ℝ n g x = 0 :=
      hxflat n hn (by omega)
    simp only [phi, nonflatJetCuttingFunction, hnzero, zero_apply,
      Pi.zero_apply]
  refine ⟨phi, hphi, hphix,
    surjective_fderiv_nonflatJetCuttingFunction horder hv, ?_⟩
  intro y hy
  have hyflat :=
    (mem_iteratedFDerivFirstNonflatStratum_iff (by omega)).mp hy |>.1
  have hynzero : iteratedFDeriv ℝ n g y = 0 :=
    hyflat n hn (by omega)
  simp only [phi, nonflatJetCuttingFunction, Set.mem_preimage,
    Set.mem_singleton_iff, hynzero, zero_apply, Pi.zero_apply]

/-! ## Local parameterization of a regular scalar level -/

/-- The kernel used to parameterize a regular scalar level has exactly one
less dimension than the Euclidean source. -/
theorem finrank_ker_fderiv_eq_sub_one_of_surjective
    {a : ℕ} {phi : (Fin a → ℝ) → ℝ} {x : Fin a → ℝ}
    (hsurj : Function.Surjective (fderiv ℝ phi x)) :
    Module.finrank ℝ (fderiv ℝ phi x).ker = a - 1 := by
  have hrange : LinearMap.range (fderiv ℝ phi x).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrankNullity :=
    (fderiv ℝ phi x).toLinearMap.finrank_range_add_finrank_ker
  rw [hrange, finrank_top] at hrankNullity
  simp only [Module.finrank_self, Module.finrank_fin_fun] at hrankNullity
  omega

/-! ### Localizing the global flat-jet estimate -/

/-- In a finite-dimensional real normed space, a finite-order smooth germ is
represented by a globally smooth map.  Multiplication by a smooth bump which
is one near the base point preserves the germ and cuts it off before leaving
the neighborhood on which the original map is `C^r`.

This elementary localization lets the global flat-jet estimate from
`MorseSardFlatJet` be used on the open domains produced by implicit-function
charts. -/
theorem exists_contDiff_eventuallyEq_of_contDiffAt
    [FiniteDimensional ℝ E] {f : E → F} {x : E} {r : ℕ}
    (hf : ContDiffAt ℝ r f x) :
    ∃ f' : E → F, ContDiff ℝ r f' ∧ f' =ᶠ[𝓝 x] f := by
  have hgood : {y | ContDiffAt ℝ r f y} ∈ 𝓝 x :=
    hf.eventually (by simp)
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let bump : ContDiffBump x :=
    ⟨eps / 4, eps / 2, by positivity, by linarith⟩
  let f' : E → F := fun y => bump y • f y
  have hclosed : Metric.closedBall x bump.rOut ⊆
      {y | ContDiffAt ℝ r f y} := by
    intro y hy
    apply hball
    rw [Metric.mem_ball]
    have hy' : dist y x ≤ eps / 2 := by
      simpa only [bump] using Metric.mem_closedBall.mp hy
    linarith
  have hf' : ContDiff ℝ r f' := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Metric.closedBall x bump.rOut
    · exact bump.contDiffAt.smul (hclosed hy)
    · have houtside : (Metric.closedBall x bump.rOut)ᶜ ∈ 𝓝 y :=
        Metric.isClosed_closedBall.isOpen_compl.mem_nhds hy
      have heq : f' =ᶠ[𝓝 y] 0 := by
        filter_upwards [houtside] with z hz
        have hzero : bump z = 0 := by
          apply bump.zero_of_le_dist
          exact le_of_lt (by
            simpa [Metric.mem_closedBall, not_le] using hz)
        simp [f', hzero]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  refine ⟨f', hf', ?_⟩
  filter_upwards [bump.eventuallyEq_one] with y hy
  simp [f', hy]

/-- The flat-jet image estimate is local on the source.  On an open set it
needs only `ContDiffOn`: replace the map near each source point by the global
smooth representative above, apply the global estimate, and assemble the
local null images through second countability.

This is the measure-theoretic bridge needed for implicit-function charts,
whose parameterizations are smooth only on their open chart domains. -/
theorem volume_image_iteratedFDerivFlatSet_inter_open_eq_zero
    {a b r : ℕ} {f : (Fin a → ℝ) → (Fin b → ℝ)}
    {W : Set (Fin a → ℝ)} (hWopen : IsOpen W)
    (hf : ContDiffOn ℝ r f W) (hr : 0 < r) (hdim : a < r * b) :
    volume (f '' (iteratedFDerivFlatSet r f ∩ W)) = 0 := by
  let S := iteratedFDerivFlatSet r f ∩ W
  have hlocal : ∀ u ∈ W, ∃ N : Set (Fin a → ℝ),
      IsOpen N ∧ u ∈ N ∧
        volume (f '' (iteratedFDerivFlatSet r f ∩ N)) = 0 := by
    intro u huW
    have hfu : ContDiffAt ℝ r f u :=
      hf.contDiffAt (hWopen.mem_nhds huW)
    obtain ⟨f', hf', heq⟩ :=
      exists_contDiff_eventuallyEq_of_contDiffAt hfu
    have hjet : ∀ᶠ y in 𝓝 u, ∀ i ∈ Finset.range r,
        iteratedFDeriv ℝ i f' y = iteratedFDeriv ℝ i f y := by
      rw [Filter.eventually_all_finset]
      intro i _hi
      exact heq.iteratedFDeriv ℝ i
    have hgood : {y | y ∈ W ∧ f' y = f y ∧
        ∀ i ∈ Finset.range r,
          iteratedFDeriv ℝ i f' y = iteratedFDeriv ℝ i f y} ∈ 𝓝 u := by
      filter_upwards [hWopen.mem_nhds huW, heq, hjet]
        with y hyW hyEq hyJet
      exact ⟨hyW, hyEq, hyJet⟩
    let N : Set (Fin a → ℝ) := interior {y | y ∈ W ∧ f' y = f y ∧
      ∀ i ∈ Finset.range r,
        iteratedFDeriv ℝ i f' y = iteratedFDeriv ℝ i f y}
    have hNopen : IsOpen N := isOpen_interior
    have huN : u ∈ N := mem_interior_iff_mem_nhds.mpr hgood
    have himage : f '' (iteratedFDerivFlatSet r f ∩ N) ⊆
        f' '' iteratedFDerivFlatSet r f' := by
      rintro z ⟨y, hy, rfl⟩
      have hyGood := interior_subset hy.2
      refine ⟨y, ?_, hyGood.2.1⟩
      intro i hi hir
      rw [hyGood.2.2 i (Finset.mem_range.mpr hir)]
      exact hy.1 i hi hir
    refine ⟨N, hNopen, huN, measure_mono_null himage ?_⟩
    exact volume_image_iteratedFDerivFlatSet_eq_zero hf' hr hdim
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
      iteratedFDerivFlatSet r f ∩ N p := by
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
      f '' (iteratedFDerivFlatSet r f ∩ N p) := by
    rintro z ⟨x, hx, rfl⟩
    have hxc := hcover hx
    simp only [Set.mem_iUnion] at hxc ⊢
    obtain ⟨p, hpT, hxp⟩ := hxc
    exact ⟨p, hpT, x, hxp, rfl⟩
  apply measure_mono_null himage
  exact (measure_biUnion_null_iff hTcount).mpr
    (fun p _hpT => hNzero p)

/-- The critical-dimensional little-o estimate is local on the source as
well.  Here the map is only `C^s` on an open set, while the selected locus
asks that derivatives through order `s` vanish.  Smooth representatives of
the germs preserve all of these derivatives and reduce the statement to
`volume_image_iteratedFDerivFlatSet_succ_eq_zero`. -/
theorem volume_image_iteratedFDerivFlatSet_succ_inter_open_eq_zero
    {a b s : ℕ} {f : (Fin a → ℝ) → (Fin b → ℝ)}
    {W : Set (Fin a → ℝ)} (hWopen : IsOpen W)
    (hf : ContDiffOn ℝ s f W) (hs : 0 < s) (hb : 0 < b)
    (hdim : a ≤ s * b) :
    volume (f '' (iteratedFDerivFlatSet (s + 1) f ∩ W)) = 0 := by
  let S := iteratedFDerivFlatSet (s + 1) f ∩ W
  have hlocal : ∀ u ∈ W, ∃ N : Set (Fin a → ℝ),
      IsOpen N ∧ u ∈ N ∧
        volume (f '' (iteratedFDerivFlatSet (s + 1) f ∩ N)) = 0 := by
    intro u huW
    have hfu : ContDiffAt ℝ s f u :=
      hf.contDiffAt (hWopen.mem_nhds huW)
    obtain ⟨f', hf', heq⟩ :=
      exists_contDiff_eventuallyEq_of_contDiffAt hfu
    have hjet : ∀ᶠ y in 𝓝 u, ∀ i ∈ Finset.range (s + 1),
        iteratedFDeriv ℝ i f' y = iteratedFDeriv ℝ i f y := by
      rw [Filter.eventually_all_finset]
      intro i _hi
      exact heq.iteratedFDeriv ℝ i
    have hgood : {y | y ∈ W ∧ f' y = f y ∧
        ∀ i ∈ Finset.range (s + 1),
          iteratedFDeriv ℝ i f' y = iteratedFDeriv ℝ i f y} ∈ 𝓝 u := by
      filter_upwards [hWopen.mem_nhds huW, heq, hjet]
        with y hyW hyEq hyJet
      exact ⟨hyW, hyEq, hyJet⟩
    let N : Set (Fin a → ℝ) := interior {y | y ∈ W ∧ f' y = f y ∧
      ∀ i ∈ Finset.range (s + 1),
        iteratedFDeriv ℝ i f' y = iteratedFDeriv ℝ i f y}
    have hNopen : IsOpen N := isOpen_interior
    have huN : u ∈ N := mem_interior_iff_mem_nhds.mpr hgood
    have himage : f '' (iteratedFDerivFlatSet (s + 1) f ∩ N) ⊆
        f' '' iteratedFDerivFlatSet (s + 1) f' := by
      rintro z ⟨y, hy, rfl⟩
      have hyGood := interior_subset hy.2
      refine ⟨y, ?_, hyGood.2.1⟩
      intro i hi hir
      rw [hyGood.2.2 i (Finset.mem_range.mpr hir)]
      exact hy.1 i hi hir
    refine ⟨N, hNopen, huN, measure_mono_null himage ?_⟩
    exact volume_image_iteratedFDerivFlatSet_succ_eq_zero hf' hs hb hdim
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
      iteratedFDerivFlatSet (s + 1) f ∩ N p := by
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
      f '' (iteratedFDerivFlatSet (s + 1) f ∩ N p) := by
    rintro z ⟨x, hx, rfl⟩
    have hxc := hcover hx
    simp only [Set.mem_iUnion] at hxc ⊢
    obtain ⟨p, hpT, hxp⟩ := hxc
    exact ⟨p, hpT, x, hxp, rfl⟩
  apply measure_mono_null himage
  exact (measure_biUnion_null_iff hTcount).mpr
    (fun p _hpT => hNzero p)

/-- A regular scalar level in Euclidean space is locally the image of a
`C^s` map on the kernel of its derivative.  The domain has codimension one;
keeping it as the actual kernel avoids an arbitrary choice of Euclidean
coordinates and is the natural input to the source-dimension induction. -/
theorem exists_local_contDiffOn_level_parameterization
    {a s : ℕ} {phi : (Fin a → ℝ) → ℝ} (hs : 0 < s)
    (hphi : ContDiff ℝ s phi) {x : Fin a → ℝ}
    (hsurj : Function.Surjective (fderiv ℝ phi x)) :
    ∃ U : Set (Fin a → ℝ),
      ∃ V : Set (fderiv ℝ phi x).ker,
        ∃ psi : (fderiv ℝ phi x).ker → (Fin a → ℝ),
          IsOpen U ∧ x ∈ U ∧ IsOpen V ∧
            ContDiffOn ℝ s psi V ∧
            U ∩ phi ⁻¹' {phi x} ⊆ psi '' V := by
  have hphiOne : ContDiff ℝ 1 phi :=
    hphi.of_le (by exact_mod_cast hs)
  have hstrict : HasStrictFDerivAt phi (fderiv ℝ phi x) x :=
    hphiOne.contDiffAt.hasStrictFDerivAt one_ne_zero
  have hrange : (fderiv ℝ phi x).range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  let hkernel : (fderiv ℝ phi x).ker.ClosedComplemented :=
    (fderiv ℝ phi x).ker_closedComplemented_of_finiteDimensional_range
  let chartData :=
    hstrict.implicitFunctionDataOfComplemented phi (fderiv ℝ phi x)
      hrange hkernel
  let e := chartData.toOpenPartialHomeomorph
  have hxSource : x ∈ e.source :=
    chartData.pt_mem_toOpenPartialHomeomorph_source
  have hfst : ∀ y, (e y).1 = phi y := by
    intro y
    rfl
  have hright : ContDiff ℝ s
      (fun y : Fin a → ℝ ↦ Classical.choose hkernel (y - x)) :=
    (Classical.choose hkernel).contDiff.comp
      (contDiff_id.sub contDiff_const)
  have hchart : ContDiff ℝ s chartData.prodFun := by
    change ContDiff ℝ s
      (fun y : Fin a → ℝ ↦
        (phi y, Classical.choose hkernel (y - x)))
    exact hphi.prodMk hright
  have hinverseAt : ContDiffAt ℝ s e.symm (e x) := by
    apply e.contDiffAt_symm (e.map_source hxSource)
    · rw [e.left_inv hxSource]
      exact chartData.hasStrictFDerivAt.hasFDerivAt
    · rw [e.left_inv hxSource]
      exact hchart.contDiffAt
  let c : ℝ := (e x).1
  let v₀ : (fderiv ℝ phi x).ker := (e x).2
  let psi : (fderiv ℝ phi x).ker → (Fin a → ℝ) :=
    fun v ↦ e.symm (c, v)
  have hpsiAt : ContDiffAt ℝ s psi v₀ := by
    have hpair : ContDiffAt ℝ s
        (fun v : (fderiv ℝ phi x).ker ↦ (c, v)) v₀ :=
      (contDiff_const.prodMk contDiff_id).contDiffAt
    have hcomp := hinverseAt.comp v₀ hpair
    have hc : chartData.leftFun x = c := by rfl
    simpa only [psi, Function.comp_def, hc] using hcomp
  have htargetEventually :
      ∀ᶠ v in 𝓝 v₀, (c, v) ∈ e.target := by
    have hopen : IsOpen
        ((fun v : (fderiv ℝ phi x).ker ↦ (c, v)) ⁻¹' e.target) :=
      e.open_target.preimage (continuous_const.prodMk continuous_id)
    apply hopen.mem_nhds
    change (c, v₀) ∈ e.target
    simpa only [c, v₀, Prod.eta] using e.map_source hxSource
  have hpsiEventually : ∀ᶠ v in 𝓝 v₀, ContDiffAt ℝ s psi v :=
    hpsiAt.eventually (by simp)
  let good : Set (fderiv ℝ phi x).ker :=
    {v | (c, v) ∈ e.target ∧ ContDiffAt ℝ s psi v}
  have hgood : good ∈ 𝓝 v₀ := by
    filter_upwards [htargetEventually, hpsiEventually]
      with v hvTarget hvSmooth
    exact ⟨hvTarget, hvSmooth⟩
  let V := interior good
  have hVopen : IsOpen V := isOpen_interior
  have hv₀V : v₀ ∈ V := mem_interior_iff_mem_nhds.mpr hgood
  let U : Set (Fin a → ℝ) :=
    e.source ∩ e ⁻¹' (Set.univ ×ˢ V)
  have hUopen : IsOpen U :=
    e.isOpen_inter_preimage (isOpen_univ.prod hVopen)
  have hxU : x ∈ U := by
    refine ⟨hxSource, ?_⟩
    exact ⟨Set.mem_univ _, hv₀V⟩
  have hpsi : ContDiffOn ℝ s psi V := by
    intro v hv
    exact (interior_subset hv).2.contDiffWithinAt
  refine ⟨U, V, psi, hUopen, hxU, hVopen, hpsi, ?_⟩
  rintro y ⟨hyU, hyLevel⟩
  have hyPhi : phi y = phi x := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hyLevel
  let v : (fderiv ℝ phi x).ker := (e y).2
  have hvV : v ∈ V := hyU.2.2
  refine ⟨v, hvV, ?_⟩
  change e.symm (c, v) = y
  rw [← e.left_inv hyU.1]
  apply congrArg e.symm
  apply Prod.ext
  · change c = (e y).1
    rw [hfst y, hyPhi]
    exact (hfst x).symm
  · rfl

/-- Every point of a nonflat jet layer has a local `C^s`
codimension-one parameterization of that layer.  This packages the cutting
function and the implicit-function chart into the exact local object used by
the source-dimension step of Morse--Sard. -/
theorem exists_local_contDiffOn_parameterization_of_mem_firstNonflatStratum
    {a b n s : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (s + n : ℕ) g) (hs : 0 < s) (hn : 0 < n)
    {x : Fin a → ℝ}
    (hx : x ∈ iteratedFDerivFirstNonflatStratum (n + 1) g) :
    ∃ phi : (Fin a → ℝ) → ℝ,
      ContDiff ℝ s phi ∧ phi x = 0 ∧
        Function.Surjective (fderiv ℝ phi x) ∧
        ∃ U : Set (Fin a → ℝ),
          ∃ V : Set (fderiv ℝ phi x).ker,
            ∃ psi : (fderiv ℝ phi x).ker → (Fin a → ℝ),
              IsOpen U ∧ x ∈ U ∧ IsOpen V ∧
                ContDiffOn ℝ s psi V ∧
                (iteratedFDerivFirstNonflatStratum (n + 1) g ∩ U) ⊆
                  psi '' V := by
  obtain ⟨phi, hphi, hphix, hsurj, hlayer⟩ :=
    exists_contDiff_regular_hypersurface_of_mem_firstNonflatStratum
      hg hs hn hx
  obtain ⟨U, V, psi, hUopen, hxU, hVopen, hpsi, hlevel⟩ :=
    exists_local_contDiffOn_level_parameterization hs hphi hsurj
  refine ⟨phi, hphi, hphix, hsurj, U, V, psi,
    hUopen, hxU, hVopen, hpsi, ?_⟩
  intro y hy
  apply hlevel
  refine ⟨hy.2, ?_⟩
  have hyZero := hlayer hy.1
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, hphix] using hyZero

/-- The hypersurface parameterization can be put on the standard Euclidean
space of dimension `a - 1`.  More importantly, the old flat jet is transported
through the parameterization with its precise differentiability loss:

* the parameterized map is `C^s` on its open chart domain;
* derivatives of the composition below
  `min (n + 1) (s + 1)` vanish over the old first-nonflat layer.

The image inclusion in the conclusion is the exact input for the
lower-source-dimension induction: locally, the order-`n+1` layer in dimension
`a` is an image of that transported flat locus in dimension `a-1`. -/
theorem exists_local_contDiffOn_flat_parameterization_of_mem_firstNonflatStratum
    {a b n s : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (s + n : ℕ) g) (hs : 0 < s) (hn : 0 < n)
    {x : Fin a → ℝ}
    (hx : x ∈ iteratedFDerivFirstNonflatStratum (n + 1) g) :
    ∃ U : Set (Fin a → ℝ), ∃ W : Set (Fin (a - 1) → ℝ),
      ∃ theta : (Fin (a - 1) → ℝ) → (Fin a → ℝ),
        IsOpen U ∧ x ∈ U ∧ IsOpen W ∧
          ContDiffOn ℝ s theta W ∧
          ContDiffOn ℝ s (g ∘ theta) W ∧
          (iteratedFDerivFirstNonflatStratum (n + 1) g ∩ U) ⊆
            theta '' W ∧
          g '' (iteratedFDerivFirstNonflatStratum (n + 1) g ∩ U) ⊆
            (g ∘ theta) ''
              (iteratedFDerivFlatSet (min (n + 1) (s + 1))
                (g ∘ theta) ∩ W) := by
  obtain ⟨phi, hphi, _hphix, hsurj, U, V, psi,
      hUopen, hxU, hVopen, hpsi, hlayer⟩ :=
    exists_local_contDiffOn_parameterization_of_mem_firstNonflatStratum
      hg hs hn hx
  have hfin := finrank_ker_fderiv_eq_sub_one_of_surjective hsurj
  have hdim : Module.finrank ℝ (Fin (a - 1) → ℝ) =
      Module.finrank ℝ (fderiv ℝ phi x).ker := by
    simpa only [Module.finrank_fin_fun] using hfin.symm
  let e : (Fin (a - 1) → ℝ) ≃L[ℝ] (fderiv ℝ phi x).ker :=
    ContinuousLinearEquiv.ofFinrankEq hdim
  let W : Set (Fin (a - 1) → ℝ) := e ⁻¹' V
  let theta : (Fin (a - 1) → ℝ) → (Fin a → ℝ) := psi ∘ e
  have hWopen : IsOpen W := hVopen.preimage e.continuous
  have htheta : ContDiffOn ℝ s theta W := by
    apply hpsi.comp e.contDiff.contDiffOn
    intro u hu
    exact hu
  have hgS : ContDiff ℝ s g := hg.of_le (by norm_cast; omega)
  have hgtheta : ContDiffOn ℝ s (g ∘ theta) W :=
    hgS.comp_contDiffOn htheta
  have hcover :
      (iteratedFDerivFirstNonflatStratum (n + 1) g ∩ U) ⊆
        theta '' W := by
    intro y hy
    obtain ⟨v, hvV, hv⟩ := hlayer hy
    refine ⟨e.symm v, ?_, ?_⟩
    · change e (e.symm v) ∈ V
      simpa using hvV
    · change psi (e (e.symm v)) = y
      simpa using hv
  refine ⟨U, W, theta, hUopen, hxU, hWopen, htheta, hgtheta,
    hcover, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  obtain ⟨u, huW, hu⟩ := hcover hy
  refine ⟨u, ⟨?_, huW⟩, ?_⟩
  · have huAt : ContDiffAt ℝ s theta u :=
      htheta.contDiffAt (hWopen.mem_nhds huW)
    have hyLayer : theta u ∈
        iteratedFDerivFirstNonflatStratum (n + 1) g := by
      rw [hu]
      exact hy.1
    have hyFlat : theta u ∈
        iteratedFDerivFlatSet (min (n + 1) (s + 1)) g := by
      intro i hi hit
      have hiN : i < n + 1 :=
        hit.trans_le (min_le_left _ _)
      exact ((mem_iteratedFDerivFirstNonflatStratum_iff (by omega)).mp
        hyLayer).1 i hi hiN
    apply mem_iteratedFDerivFlatSet_comp_of_contDiffAt
      (min_le_right (n + 1) (s + 1)) hgS.contDiffAt huAt hyFlat
  · change g (theta u) = g y
    rw [hu]

/-- A concrete local null-image consequence of the transported flat jet.
After the hypersurface step the source dimension is `a-1`, the composition
is only `C^s`, and its available Taylor order is therefore
`min (n+1) s`.  Whenever that exact Taylor exponent beats the new
source/target dimension ratio, the whole local nonflat layer has null image.

The dimension hypothesis records the genuine limit of the direct flat-jet
estimate.  The remaining classical cases require the further
source-dimension/flat-order induction rather than any stronger conclusion
from a single hypersurface chart. -/
theorem exists_open_image_volume_eq_zero_of_mem_firstNonflatStratum_of_dim
    {a b n s : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (s + n : ℕ) g) (hs : 0 < s) (hn : 0 < n)
    (hdim : a - 1 < min (n + 1) s * b)
    {x : Fin a → ℝ}
    (hx : x ∈ iteratedFDerivFirstNonflatStratum (n + 1) g) :
    ∃ U : Set (Fin a → ℝ), IsOpen U ∧ x ∈ U ∧
      volume (g ''
        (iteratedFDerivFirstNonflatStratum (n + 1) g ∩ U)) = 0 := by
  obtain ⟨U, W, theta, hUopen, hxU, hWopen, _htheta,
      hgtheta, _hcover, himage⟩ :=
    exists_local_contDiffOn_flat_parameterization_of_mem_firstNonflatStratum
      hg hs hn hx
  let r := min (n + 1) s
  have hr : 0 < r := by
    dsimp [r]
    omega
  have hrs : r ≤ s := min_le_right _ _
  have hgthetaR : ContDiffOn ℝ r (g ∘ theta) W :=
    hgtheta.of_le (by exact_mod_cast hrs)
  have hflatNull : volume ((g ∘ theta) ''
      (iteratedFDerivFlatSet r (g ∘ theta) ∩ W)) = 0 :=
    volume_image_iteratedFDerivFlatSet_inter_open_eq_zero
      hWopen hgthetaR hr (by simpa only [r] using hdim)
  refine ⟨U, hUopen, hxU, measure_mono_null himage ?_⟩
  apply measure_mono_null _ hflatNull
  rintro z ⟨u, hu, rfl⟩
  refine ⟨u, ⟨?_, hu.2⟩, rfl⟩
  intro i hi hir
  exact hu.1 i hi (by
    have hirn : i < n + 1 := hir.trans_le (min_le_left _ _)
    have hirs : i < s + 1 := by omega
    exact lt_min hirn hirs)

/-- The complementary critical-dimensional chart case.  If the
hypersurface parameterization retains `s` derivatives and the old layer is
flat through at least order `s`, then the transported map is flat through
order `s` on a source of dimension `a - 1`.  The little-o endpoint therefore
allows the non-strict inequality `a - 1 ≤ s * b`.

This is the late-layer branch needed by the two-parameter Morse--Sard
induction; `s ≤ n` is exactly the statement that the old order-`n+1` flat
jet supplies the extra vanishing derivative at the new smoothness order. -/
theorem exists_open_image_volume_eq_zero_of_mem_firstNonflatStratum_of_late
    {a b n s : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (s + n : ℕ) g) (hs : 0 < s) (hn : 0 < n)
    (hb : 0 < b) (hsn : s ≤ n) (hdim : a - 1 ≤ s * b)
    {x : Fin a → ℝ}
    (hx : x ∈ iteratedFDerivFirstNonflatStratum (n + 1) g) :
    ∃ U : Set (Fin a → ℝ), IsOpen U ∧ x ∈ U ∧
      volume (g ''
        (iteratedFDerivFirstNonflatStratum (n + 1) g ∩ U)) = 0 := by
  obtain ⟨U, W, theta, hUopen, hxU, hWopen, _htheta,
      hgtheta, _hcover, himage⟩ :=
    exists_local_contDiffOn_flat_parameterization_of_mem_firstNonflatStratum
      hg hs hn hx
  have horder : min (n + 1) (s + 1) = s + 1 :=
    min_eq_right (by omega)
  rw [horder] at himage
  have hflatNull : volume ((g ∘ theta) ''
      (iteratedFDerivFlatSet (s + 1) (g ∘ theta) ∩ W)) = 0 :=
    volume_image_iteratedFDerivFlatSet_succ_inter_open_eq_zero
      hWopen hgtheta hs hb hdim
  exact ⟨U, hUopen, hxU, measure_mono_null himage hflatNull⟩

/-- The local null-image estimates for one nonflat layer assemble globally
by second countability of its source subtype. -/
theorem volume_image_iteratedFDerivFirstNonflatStratum_eq_zero_of_dim
    {a b n s : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (s + n : ℕ) g) (hs : 0 < s) (hn : 0 < n)
    (hdim : a - 1 < min (n + 1) s * b) :
    volume (g '' iteratedFDerivFirstNonflatStratum (n + 1) g) = 0 := by
  let S := iteratedFDerivFirstNonflatStratum (n + 1) g
  choose U hUopen hxU hUzero using
    fun p : S =>
      exists_open_image_volume_eq_zero_of_mem_firstNonflatStratum_of_dim
        hg hs hn hdim p.property
  let W : S → Set S := fun p => Subtype.val ⁻¹' U p
  have hW : ∀ p : S, W p ∈ 𝓝 p := by
    intro p
    exact continuousAt_subtype_val.preimage_mem_nhds
      ((hUopen p).mem_nhds (hxU p))
  obtain ⟨T, hTcount, hTcover⟩ :=
    TopologicalSpace.countable_cover_nhds hW
  have hcover : S ⊆ ⋃ p ∈ T, S ∩ U p := by
    intro x hx
    let q : S := ⟨x, hx⟩
    have hq : q ∈ ⋃ p ∈ T, W p := by
      rw [hTcover]
      exact Set.mem_univ q
    simp only [Set.mem_iUnion] at hq
    obtain ⟨p, hpT, hxp⟩ := hq
    exact Set.mem_iUnion.mpr ⟨p,
      Set.mem_iUnion.mpr ⟨hpT, hx, hxp⟩⟩
  have himage : g '' S ⊆ ⋃ p ∈ T, g '' (S ∩ U p) := by
    rintro z ⟨x, hx, rfl⟩
    have hxc := hcover hx
    simp only [Set.mem_iUnion] at hxc ⊢
    obtain ⟨p, hpT, hxp⟩ := hxc
    exact ⟨p, hpT, x, hxp, rfl⟩
  apply measure_mono_null himage
  exact (measure_biUnion_null_iff hTcount).mpr
    (fun p _hpT => hUzero p)

/-- Global form of the late-layer critical-dimensional endpoint. -/
theorem volume_image_iteratedFDerivFirstNonflatStratum_eq_zero_of_late
    {a b n s : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (s + n : ℕ) g) (hs : 0 < s) (hn : 0 < n)
    (hb : 0 < b) (hsn : s ≤ n) (hdim : a - 1 ≤ s * b) :
    volume (g '' iteratedFDerivFirstNonflatStratum (n + 1) g) = 0 := by
  let S := iteratedFDerivFirstNonflatStratum (n + 1) g
  choose U hUopen hxU hUzero using
    fun p : S =>
      exists_open_image_volume_eq_zero_of_mem_firstNonflatStratum_of_late
        hg hs hn hb hsn hdim p.property
  let W : S → Set S := fun p => Subtype.val ⁻¹' U p
  have hW : ∀ p : S, W p ∈ 𝓝 p := by
    intro p
    exact continuousAt_subtype_val.preimage_mem_nhds
      ((hUopen p).mem_nhds (hxU p))
  obtain ⟨T, hTcount, hTcover⟩ :=
    TopologicalSpace.countable_cover_nhds hW
  have hcover : S ⊆ ⋃ p ∈ T, S ∩ U p := by
    intro x hx
    let q : S := ⟨x, hx⟩
    have hq : q ∈ ⋃ p ∈ T, W p := by
      rw [hTcover]
      exact Set.mem_univ q
    simp only [Set.mem_iUnion] at hq
    obtain ⟨p, hpT, hxp⟩ := hq
    exact Set.mem_iUnion.mpr ⟨p,
      Set.mem_iUnion.mpr ⟨hpT, hx, hxp⟩⟩
  have himage : g '' S ⊆ ⋃ p ∈ T, g '' (S ∩ U p) := by
    rintro z ⟨x, hx, rfl⟩
    have hxc := hcover hx
    simp only [Set.mem_iUnion] at hxc ⊢
    obtain ⟨p, hpT, hxp⟩ := hxc
    exact ⟨p, hpT, x, hxp, rfl⟩
  apply measure_mono_null himage
  exact (measure_biUnion_null_iff hTcount).mpr
    (fun p _hpT => hUzero p)

/-! ## Finite nonflat decomposition of the rank-zero critical source -/

/-- The rank-zero part of the critical source.  After the usual constant-rank
normalization, this is the residual source to which the hypersurface induction
is applied. -/
def fderivRankZeroSource {a b : ℕ}
    (g : (Fin a → ℝ) → (Fin b → ℝ)) : Set (Fin a → ℝ) :=
  {x | fderiv ℝ g x = 0}

/-- Vanishing of the first derivative is exactly membership in the order-two
flat-jet locus. -/
theorem fderivRankZeroSource_eq_iteratedFDerivFlatSet_two
    {a b : ℕ} (g : (Fin a → ℝ) → (Fin b → ℝ)) :
    fderivRankZeroSource g = iteratedFDerivFlatSet 2 g := by
  ext x
  simp only [fderivRankZeroSource, Set.mem_ofPred_eq,
    iteratedFDerivFlatSet]
  constructor
  · intro hx i hi hiTwo
    have hiOne : i = 1 := by omega
    subst i
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_one, hx, norm_zero]
  · intro hx
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_one]
    exact norm_eq_zero.mpr (hx 1 (by omega) (by omega))

/-- Up to any fixed depth `R`, the rank-zero critical source is the union of
the deepest flat locus and finitely many consecutive nonflat layers.  The
deepest locus is handled by the Taylor estimate; every other layer is handled
by `exists_regular_hypersurface_of_mem_firstNonflatStratum`. -/
theorem fderivRankZeroSource_subset_flat_union_nonflatLayers
    {a b R : ℕ} (_hR : 2 ≤ R)
    (g : (Fin a → ℝ) → (Fin b → ℝ)) :
    fderivRankZeroSource g ⊆
      iteratedFDerivFlatSet R g ∪
        ⋃ i ∈ Finset.Ico 2 R, iteratedFDerivFirstNonflatStratum i g := by
  classical
  intro x hx
  have hxTwo : x ∈ iteratedFDerivFlatSet 2 g := by
    rw [← fderivRankZeroSource_eq_iteratedFDerivFlatSet_two]
    exact hx
  by_cases hxR : x ∈ iteratedFDerivFlatSet R g
  · exact Or.inl hxR
  · right
    have hex : ∃ i : ℕ, 0 < i ∧ i < R ∧ iteratedFDeriv ℝ i g x ≠ 0 := by
      simp only [iteratedFDerivFlatSet, Set.mem_ofPred_eq] at hxR
      push Not at hxR
      obtain ⟨i, hi, hiR, hine⟩ := hxR
      exact ⟨i, hi, hiR, hine⟩
    let i := Nat.find hex
    have hi : 0 < i ∧ i < R ∧ iteratedFDeriv ℝ i g x ≠ 0 := by
      simpa only [i] using Nat.find_spec hex
    have hiTwo : 2 ≤ i := by
      have hiNeOne : i ≠ 1 := by
        intro hiOne
        have hi' := hi
        rw [hiOne] at hi'
        exact hi'.2.2 (hxTwo 1 (by omega) (by omega))
      omega
    have hiflat : x ∈ iteratedFDerivFlatSet i g := by
      intro j hjpos hjlt
      by_contra hjne
      have hjWitness : 0 < j ∧ j < R ∧
          iteratedFDeriv ℝ j g x ≠ 0 :=
        ⟨hjpos, hjlt.trans hi.2.1, hjne⟩
      have hij : i ≤ j := by
        simpa only [i] using Nat.find_min' hex hjWitness
      omega
    have hiLayer : x ∈ iteratedFDerivFirstNonflatStratum i g := by
      apply (mem_iteratedFDerivFirstNonflatStratum_iff hi.1).mpr
      exact ⟨hiflat, hi.2.2⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, Set.mem_iUnion.mpr ⟨?_, hiLayer⟩⟩
    exact Finset.mem_Ico.mpr ⟨hiTwo, hi.2.1⟩

/-- In the first full range of the source/target dimension induction,
`a ≤ 2b`, the deepest flat locus and every nonflat layer are already covered
by the direct transported flat-jet estimate.  Thus the complete rank-zero
source has null image at the exact classical order `C^(a-b+1)`.

For larger dimension gaps the end layers only retain Taylor exponent two,
which no longer beats the source dimension.  That is precisely where the
remaining two-parameter source-dimension/flat-order induction is needed. -/
theorem volume_image_fderivRankZeroSource_eq_zero_of_morseSardOrder_of_le_two_mul
    {a b : ℕ} (hba : b < a) (hb : 1 < b) (hab : a ≤ 2 * b)
    {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (a - b + 1 : ℕ) g) :
    volume (g '' fderivRankZeroSource g) = 0 := by
  let R := a - b + 1
  have hR : 2 ≤ R := by
    dsimp [R]
    omega
  have hsource := fderivRankZeroSource_subset_flat_union_nonflatLayers
    hR g
  apply measure_mono_null (image_mono hsource)
  rw [image_union, measure_union_null_iff]
  constructor
  · simpa only [R] using
      volume_image_iteratedFDerivFlatSet_eq_zero_of_morseSardOrder
        hba hb hg
  · rw [image_iUnion, measure_iUnion_null_iff]
    intro i
    rw [image_iUnion, measure_iUnion_null_iff]
    intro hi
    have hiIco := Finset.mem_Ico.mp hi
    let n := i - 1
    let s := R - n
    have hn : 0 < n := by
      dsimp [n]
      omega
    have hs : 0 < s := by
      dsimp [s, n]
      omega
    have hni : n + 1 = i := by
      dsimp [n]
      omega
    have hsum : s + n = R := by
      dsimp [s]
      omega
    have htwoN : 2 ≤ n + 1 := by omega
    have htwoS : 2 ≤ s := by
      dsimp [s]
      omega
    have htwoMin : 2 ≤ min (n + 1) s :=
      le_min htwoN htwoS
    have hmul : 2 * b ≤ min (n + 1) s * b :=
      Nat.mul_le_mul_right b htwoMin
    have hdim : a - 1 < min (n + 1) s * b := by omega
    have hg' : ContDiff ℝ (s + n : ℕ) g := by
      simpa only [hsum, R] using hg
    simpa only [hni] using
      volume_image_iteratedFDerivFirstNonflatStratum_eq_zero_of_dim
        hg' hs hn hdim

/-- The first-range rank-zero theorem is local on the source.  If the map is
only `C^(a-b+1)` on an open chart domain, smooth cutoff representatives of
its germs reduce the claim to the global theorem, and second countability
assembles the resulting local null images. -/
theorem volume_image_fderivRankZeroSource_inter_open_eq_zero_of_morseSardOrder_of_le_two_mul
    {a b : ℕ} (hba : b < a) (hb : 1 < b) (hab : a ≤ 2 * b)
    {f : (Fin a → ℝ) → (Fin b → ℝ)}
    {W : Set (Fin a → ℝ)} (hWopen : IsOpen W)
    (hf : ContDiffOn ℝ (a - b + 1 : ℕ) f W) :
    volume (f '' (fderivRankZeroSource f ∩ W)) = 0 := by
  let S := fderivRankZeroSource f ∩ W
  have hlocal : ∀ u ∈ W, ∃ N : Set (Fin a → ℝ),
      IsOpen N ∧ u ∈ N ∧
        volume (f '' (fderivRankZeroSource f ∩ N)) = 0 := by
    intro u huW
    have hfu : ContDiffAt ℝ (a - b + 1 : ℕ) f u :=
      hf.contDiffAt (hWopen.mem_nhds huW)
    obtain ⟨f', hf', heq⟩ :=
      exists_contDiff_eventuallyEq_of_contDiffAt hfu
    have hderiv : fderiv ℝ f' =ᶠ[𝓝 u] fderiv ℝ f := heq.fderiv
    have hgood : {y | y ∈ W ∧ f' y = f y ∧
        fderiv ℝ f' y = fderiv ℝ f y} ∈ 𝓝 u := by
      filter_upwards [hWopen.mem_nhds huW, heq, hderiv]
        with y hyW hyEq hyDeriv
      exact ⟨hyW, hyEq, hyDeriv⟩
    let N : Set (Fin a → ℝ) :=
      interior {y | y ∈ W ∧ f' y = f y ∧
        fderiv ℝ f' y = fderiv ℝ f y}
    have hNopen : IsOpen N := isOpen_interior
    have huN : u ∈ N := mem_interior_iff_mem_nhds.mpr hgood
    have himage : f '' (fderivRankZeroSource f ∩ N) ⊆
        f' '' fderivRankZeroSource f' := by
      rintro z ⟨y, hy, rfl⟩
      have hyGood := interior_subset hy.2
      refine ⟨y, ?_, hyGood.2.1⟩
      change fderiv ℝ f' y = 0
      rw [hyGood.2.2]
      exact hy.1
    refine ⟨N, hNopen, huN, measure_mono_null himage ?_⟩
    exact
      volume_image_fderivRankZeroSource_eq_zero_of_morseSardOrder_of_le_two_mul
        hba hb hab hf'
  choose N hNopen huN hNzero using
    fun p : S ↦ hlocal p p.property.2
  let O : S → Set S := fun p ↦ Subtype.val ⁻¹' N p
  have hO : ∀ p : S, O p ∈ 𝓝 p := by
    intro p
    exact continuousAt_subtype_val.preimage_mem_nhds
      ((hNopen p).mem_nhds (huN p))
  obtain ⟨T, hTcount, hTcover⟩ :=
    TopologicalSpace.countable_cover_nhds hO
  have hcover : S ⊆ ⋃ p ∈ T, fderivRankZeroSource f ∩ N p := by
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
      f '' (fderivRankZeroSource f ∩ N p) := by
    rintro z ⟨x, hx, rfl⟩
    have hxc := hcover hx
    simp only [Set.mem_iUnion] at hxc ⊢
    obtain ⟨p, hpT, hxp⟩ := hxc
    exact ⟨p, hpT, x, hxp, rfl⟩
  apply measure_mono_null himage
  exact (measure_biUnion_null_iff hTcount).mpr
    (fun p _hpT ↦ hNzero p)

/-- The first nonflat layer in the next source-dimensional range is the
lower-source rank-zero problem.  Its hypersurface parameterization has source
dimension `a - 1`, retains exactly `C^(a-b)`, and transports first-derivative
vanishing.  Hence the already-established `a - 1 ≤ 2b` rank-zero theorem
supplies the local null-image estimate. -/
theorem exists_open_image_volume_eq_zero_of_mem_firstNonflatStratum_two_of_lower_rankzero
    {a b : ℕ} (hba : b < a - 1) (hb : 1 < b)
    (hab : a - 1 ≤ 2 * b)
    {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (a - b + 1 : ℕ) g)
    {x : Fin a → ℝ}
    (hx : x ∈ iteratedFDerivFirstNonflatStratum 2 g) :
    ∃ U : Set (Fin a → ℝ), IsOpen U ∧ x ∈ U ∧
      volume (g ''
        (iteratedFDerivFirstNonflatStratum 2 g ∩ U)) = 0 := by
  have hs : 0 < a - b := by omega
  obtain ⟨U, W, theta, hUopen, hxU, hWopen, _htheta,
      hgtheta, _hcover, himage⟩ :=
    exists_local_contDiffOn_flat_parameterization_of_mem_firstNonflatStratum
      (n := 1) (s := a - b) hg hs (by omega) hx
  have horder : min (1 + 1) (a - b + 1) = 2 := by omega
  rw [horder] at himage
  have hsourceOrder : (a - 1) - b + 1 = a - b := by omega
  have hgtheta' : ContDiffOn ℝ ((a - 1) - b + 1 : ℕ)
      (g ∘ theta) W := by
    simpa only [hsourceOrder] using hgtheta
  have hflatNull : volume ((g ∘ theta) ''
      (fderivRankZeroSource (g ∘ theta) ∩ W)) = 0 :=
    volume_image_fderivRankZeroSource_inter_open_eq_zero_of_morseSardOrder_of_le_two_mul
      hba hb hab hWopen hgtheta'
  rw [fderivRankZeroSource_eq_iteratedFDerivFlatSet_two] at hflatNull
  exact ⟨U, hUopen, hxU, measure_mono_null himage hflatNull⟩

/-- Global form of the lower-source induction for the first nonflat layer. -/
theorem volume_image_iteratedFDerivFirstNonflatStratum_two_eq_zero_of_lower_rankzero
    {a b : ℕ} (hba : b < a - 1) (hb : 1 < b)
    (hab : a - 1 ≤ 2 * b)
    {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (a - b + 1 : ℕ) g) :
    volume (g '' iteratedFDerivFirstNonflatStratum 2 g) = 0 := by
  let S := iteratedFDerivFirstNonflatStratum 2 g
  choose U hUopen hxU hUzero using
    fun p : S =>
      exists_open_image_volume_eq_zero_of_mem_firstNonflatStratum_two_of_lower_rankzero
        hba hb hab hg p.property
  let W : S → Set S := fun p => Subtype.val ⁻¹' U p
  have hW : ∀ p : S, W p ∈ 𝓝 p := by
    intro p
    exact continuousAt_subtype_val.preimage_mem_nhds
      ((hUopen p).mem_nhds (hxU p))
  obtain ⟨T, hTcount, hTcover⟩ :=
    TopologicalSpace.countable_cover_nhds hW
  have hcover : S ⊆ ⋃ p ∈ T, S ∩ U p := by
    intro x hx
    let q : S := ⟨x, hx⟩
    have hq : q ∈ ⋃ p ∈ T, W p := by
      rw [hTcover]
      exact Set.mem_univ q
    simp only [Set.mem_iUnion] at hq
    obtain ⟨p, hpT, hxp⟩ := hq
    exact Set.mem_iUnion.mpr ⟨p,
      Set.mem_iUnion.mpr ⟨hpT, hx, hxp⟩⟩
  have himage : g '' S ⊆ ⋃ p ∈ T, g '' (S ∩ U p) := by
    rintro z ⟨x, hx, rfl⟩
    have hxc := hcover hx
    simp only [Set.mem_iUnion] at hxc ⊢
    obtain ⟨p, hpT, hxp⟩ := hxc
    exact ⟨p, hpT, x, hxp, rfl⟩
  apply measure_mono_null himage
  exact (measure_biUnion_null_iff hTcount).mpr
    (fun p _hpT => hUzero p)

/-- One complete source-dimension step beyond the direct `a ≤ 2b` range.
At the boundary `a = 2b + 1`, the order-two layer is the already-proved
rank-zero theorem in source dimension `a - 1`; late layers use the critical
little-o endpoint, and the remaining layers satisfy the strict Taylor
dimension inequality. -/
theorem volume_image_fderivRankZeroSource_eq_zero_of_morseSardOrder_of_le_two_mul_add_one
    {a b : ℕ} (hba : b < a) (hb : 1 < b)
    (hab : a ≤ 2 * b + 1)
    {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (a - b + 1 : ℕ) g) :
    volume (g '' fderivRankZeroSource g) = 0 := by
  by_cases habBase : a ≤ 2 * b
  · exact
      volume_image_fderivRankZeroSource_eq_zero_of_morseSardOrder_of_le_two_mul
        hba hb habBase hg
  have haeq : a = 2 * b + 1 := by omega
  let R := a - b + 1
  have hR : 2 ≤ R := by
    dsimp [R]
    omega
  have hsource := fderivRankZeroSource_subset_flat_union_nonflatLayers
    hR g
  apply measure_mono_null (image_mono hsource)
  rw [image_union, measure_union_null_iff]
  constructor
  · simpa only [R] using
      volume_image_iteratedFDerivFlatSet_eq_zero_of_morseSardOrder
        hba hb hg
  · rw [image_iUnion, measure_iUnion_null_iff]
    intro i
    rw [image_iUnion, measure_iUnion_null_iff]
    intro hi
    have hiIco := Finset.mem_Ico.mp hi
    by_cases hiTwo : i = 2
    · subst i
      apply volume_image_iteratedFDerivFirstNonflatStratum_two_eq_zero_of_lower_rankzero
      · omega
      · exact hb
      · omega
      · exact hg
    let n := i - 1
    let s := R - n
    have hn : 0 < n := by
      dsimp [n]
      omega
    have hs : 0 < s := by
      dsimp [s, n, R]
      omega
    have hni : n + 1 = i := by
      dsimp [n]
      omega
    have hsum : s + n = R := by
      dsimp [s]
      omega
    have hg' : ContDiff ℝ (s + n : ℕ) g := by
      simpa only [hsum, R] using hg
    by_cases hlate : s ≤ n
    · have hdim : a - 1 ≤ s * b := by
        have hsTwo : 2 ≤ s := by
          dsimp [s, R, n]
          omega
        have hmul : 2 * b ≤ s * b :=
          Nat.mul_le_mul_right b hsTwo
        omega
      simpa only [hni] using
        volume_image_iteratedFDerivFirstNonflatStratum_eq_zero_of_late
          hg' hs hn (by omega) hlate hdim
    · have hnTwo : 2 ≤ n := by
        dsimp [n]
        omega
      have hdim : a - 1 < min (n + 1) s * b := by
        have hnlt : n < s := by omega
        rw [min_eq_left (by omega)]
        have hmul : 2 * b < (n + 1) * b :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        omega
      simpa only [hni] using
        volume_image_iteratedFDerivFirstNonflatStratum_eq_zero_of_dim
          hg' hs hn hdim


/-- The `a ≤ 2b + 1` rank-zero theorem localized to an open source chart. -/
theorem volume_image_fderivRankZeroSource_inter_open_eq_zero_of_morseSardOrder_of_le_two_mul_add_one
    {a b : ℕ} (hba : b < a) (hb : 1 < b)
    (hab : a ≤ 2 * b + 1)
    {f : (Fin a → ℝ) → (Fin b → ℝ)}
    {W : Set (Fin a → ℝ)} (hWopen : IsOpen W)
    (hf : ContDiffOn ℝ (a - b + 1 : ℕ) f W) :
    volume (f '' (fderivRankZeroSource f ∩ W)) = 0 := by
  let S := fderivRankZeroSource f ∩ W
  have hlocal : ∀ u ∈ W, ∃ N : Set (Fin a → ℝ),
      IsOpen N ∧ u ∈ N ∧
        volume (f '' (fderivRankZeroSource f ∩ N)) = 0 := by
    intro u huW
    have hfu : ContDiffAt ℝ (a - b + 1 : ℕ) f u :=
      hf.contDiffAt (hWopen.mem_nhds huW)
    obtain ⟨f', hf', heq⟩ :=
      exists_contDiff_eventuallyEq_of_contDiffAt hfu
    have hderiv : fderiv ℝ f' =ᶠ[𝓝 u] fderiv ℝ f := heq.fderiv
    have hgood : {y | y ∈ W ∧ f' y = f y ∧
        fderiv ℝ f' y = fderiv ℝ f y} ∈ 𝓝 u := by
      filter_upwards [hWopen.mem_nhds huW, heq, hderiv]
        with y hyW hyEq hyDeriv
      exact ⟨hyW, hyEq, hyDeriv⟩
    let N : Set (Fin a → ℝ) :=
      interior {y | y ∈ W ∧ f' y = f y ∧
        fderiv ℝ f' y = fderiv ℝ f y}
    have hNopen : IsOpen N := isOpen_interior
    have huN : u ∈ N := mem_interior_iff_mem_nhds.mpr hgood
    have himage : f '' (fderivRankZeroSource f ∩ N) ⊆
        f' '' fderivRankZeroSource f' := by
      rintro z ⟨y, hy, rfl⟩
      have hyGood := interior_subset hy.2
      refine ⟨y, ?_, hyGood.2.1⟩
      change fderiv ℝ f' y = 0
      rw [hyGood.2.2]
      exact hy.1
    refine ⟨N, hNopen, huN, measure_mono_null himage ?_⟩
    exact
      volume_image_fderivRankZeroSource_eq_zero_of_morseSardOrder_of_le_two_mul_add_one
        hba hb hab hf'
  choose N hNopen huN hNzero using
    fun p : S ↦ hlocal p p.property.2
  let O : S → Set S := fun p ↦ Subtype.val ⁻¹' N p
  have hO : ∀ p : S, O p ∈ 𝓝 p := by
    intro p
    exact continuousAt_subtype_val.preimage_mem_nhds
      ((hNopen p).mem_nhds (huN p))
  obtain ⟨T, hTcount, hTcover⟩ :=
    TopologicalSpace.countable_cover_nhds hO
  have hcover : S ⊆ ⋃ p ∈ T, fderivRankZeroSource f ∩ N p := by
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
      f '' (fderivRankZeroSource f ∩ N p) := by
    rintro z ⟨x, hx, rfl⟩
    have hxc := hcover hx
    simp only [Set.mem_iUnion] at hxc ⊢
    obtain ⟨p, hpT, hxp⟩ := hxc
    exact ⟨p, hpT, x, hxp, rfl⟩
  apply measure_mono_null himage
  exact (measure_biUnion_null_iff hTcount).mpr
    (fun p _hpT ↦ hNzero p)

/-- An explicit finite differentiability budget for the elementary
hypersurface proof of rank-zero Morse--Sard.  At a source-dimension step,
the added `a+1` derivatives pay for every possible nonflat cutting order
before the source dimension drops.  Kneser--Glaeser rough composition would
reduce this budget to the sharp classical order. -/
def morseSardElementaryOrder : ℕ → ℕ
  | 0 => 2
  | a + 1 => morseSardElementaryOrder a + a + 1

theorem morseSardElementaryOrder_mono : Monotone morseSardElementaryOrder :=
  monotone_nat_of_le_succ fun a => by
    simp only [morseSardElementaryOrder]
    omega

theorem morseSardElementaryOrder_pos (a : ℕ) : 0 < morseSardElementaryOrder a := by
  induction a with
  | zero => simp [morseSardElementaryOrder]
  | succ a ih => simp [morseSardElementaryOrder]

private theorem morseSardElementaryOrder_two_le (a : ℕ) : 2 ≤ morseSardElementaryOrder a := by
  induction a with
  | zero => simp [morseSardElementaryOrder]
  | succ a ih => simp [morseSardElementaryOrder]; omega

theorem morseSardElementaryOrder_source_le (a : ℕ) : a + 1 ≤ morseSardElementaryOrder a := by
  induction a with
  | zero => simp [morseSardElementaryOrder]
  | succ a ih => simp [morseSardElementaryOrder]; omega

private theorem morseSardElementaryOrder_step {a n : ℕ} (hn : n ≤ a + 1) :
    morseSardElementaryOrder a + n ≤ morseSardElementaryOrder (a + 1) := by
  simp [morseSardElementaryOrder]
  omega

private def MorseSardRankZeroGlobal (a : ℕ) : Prop :=
  ∀ {b : ℕ}, 0 < b → ∀ {g : (Fin a → ℝ) → (Fin b → ℝ)},
    ContDiff ℝ (morseSardElementaryOrder a : ℕ) g →
      volume (g '' fderivRankZeroSource g) = 0

private def MorseSardRankZeroLocal (a : ℕ) : Prop :=
  ∀ {b : ℕ}, 0 < b → ∀ {f : (Fin a → ℝ) → (Fin b → ℝ)}
    {W : Set (Fin a → ℝ)}, IsOpen W →
    ContDiffOn ℝ (morseSardElementaryOrder a : ℕ) f W →
      volume (f '' (fderivRankZeroSource f ∩ W)) = 0

private theorem morseSardRankZeroLocal_of_global {a : ℕ} (hglobal : MorseSardRankZeroGlobal a) :
    MorseSardRankZeroLocal a := by
  intro b hb f W hWopen hf
  let S := fderivRankZeroSource f ∩ W
  have hlocal : ∀ u ∈ W, ∃ N : Set (Fin a → ℝ),
      IsOpen N ∧ u ∈ N ∧
        volume (f '' (fderivRankZeroSource f ∩ N)) = 0 := by
    intro u huW
    have hfu : ContDiffAt ℝ (morseSardElementaryOrder a : ℕ) f u :=
      hf.contDiffAt (hWopen.mem_nhds huW)
    obtain ⟨f', hf', heq⟩ :=
      exists_contDiff_eventuallyEq_of_contDiffAt hfu
    have hderiv : fderiv ℝ f' =ᶠ[𝓝 u] fderiv ℝ f := heq.fderiv
    have hgood : {y | y ∈ W ∧ f' y = f y ∧
        fderiv ℝ f' y = fderiv ℝ f y} ∈ 𝓝 u := by
      filter_upwards [hWopen.mem_nhds huW, heq, hderiv]
        with y hyW hyEq hyDeriv
      exact ⟨hyW, hyEq, hyDeriv⟩
    let N : Set (Fin a → ℝ) :=
      interior {y | y ∈ W ∧ f' y = f y ∧
        fderiv ℝ f' y = fderiv ℝ f y}
    have hNopen : IsOpen N := isOpen_interior
    have huN : u ∈ N := mem_interior_iff_mem_nhds.mpr hgood
    have himage : f '' (fderivRankZeroSource f ∩ N) ⊆
        f' '' fderivRankZeroSource f' := by
      rintro z ⟨y, hy, rfl⟩
      have hyGood := interior_subset hy.2
      refine ⟨y, ?_, hyGood.2.1⟩
      change fderiv ℝ f' y = 0
      rw [hyGood.2.2]
      exact hy.1
    refine ⟨N, hNopen, huN, measure_mono_null himage ?_⟩
    exact hglobal hb hf'
  choose N hNopen huN hNzero using
    fun p : S ↦ hlocal p p.property.2
  let O : S → Set S := fun p ↦ Subtype.val ⁻¹' N p
  have hO : ∀ p : S, O p ∈ 𝓝 p := by
    intro p
    exact continuousAt_subtype_val.preimage_mem_nhds
      ((hNopen p).mem_nhds (huN p))
  obtain ⟨T, hTcount, hTcover⟩ :=
    TopologicalSpace.countable_cover_nhds hO
  have hcover : S ⊆ ⋃ p ∈ T, fderivRankZeroSource f ∩ N p := by
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
      f '' (fderivRankZeroSource f ∩ N p) := by
    rintro z ⟨x, hx, rfl⟩
    have hxc := hcover hx
    simp only [Set.mem_iUnion] at hxc ⊢
    obtain ⟨p, hpT, hxp⟩ := hxc
    exact ⟨p, hpT, x, hxp, rfl⟩
  apply measure_mono_null himage
  exact (measure_biUnion_null_iff hTcount).mpr
    (fun p _hpT ↦ hNzero p)

private theorem morseSardRankZero_base_global : MorseSardRankZeroGlobal 0 := by
  intro b hb g hg
  rw [fderivRankZeroSource_eq_iteratedFDerivFlatSet_two]
  exact volume_image_iteratedFDerivFlatSet_eq_zero
    hg (by omega) (by omega)


private theorem morseSardRankZero_step_global (a : ℕ) (ihLocal : MorseSardRankZeroLocal a) :
    MorseSardRankZeroGlobal (a + 1) := by
  intro b hb g hg
  let R := a + 2
  have hR : 2 ≤ R := by simp [R]
  have hsource := fderivRankZeroSource_subset_flat_union_nonflatLayers
    hR g
  apply measure_mono_null (image_mono hsource)
  rw [image_union, measure_union_null_iff]
  constructor
  · have hRle : R ≤ morseSardElementaryOrder (a + 1) := by
      have htwo := morseSardElementaryOrder_two_le a
      simp only [R, morseSardElementaryOrder]
      omega
    have hgR : ContDiff ℝ R g :=
      hg.of_le (by exact_mod_cast hRle)
    apply volume_image_iteratedFDerivFlatSet_eq_zero hgR (by omega)
    have hbOne : 1 ≤ b := by omega
    have hmul : R * 1 ≤ R * b := Nat.mul_le_mul_left R hbOne
    simp only [mul_one] at hmul
    dsimp [R] at hmul ⊢
    omega
  · rw [image_iUnion, measure_iUnion_null_iff]
    intro i
    rw [image_iUnion, measure_iUnion_null_iff]
    intro hi
    have hiIco := Finset.mem_Ico.mp hi
    let n := i - 1
    let s := morseSardElementaryOrder a
    have hn : 0 < n := by
      dsimp [n]
      omega
    have hs : 0 < s := by
      exact morseSardElementaryOrder_pos a
    have hni : n + 1 = i := by
      dsimp [n]
      omega
    have hnle : n ≤ a + 1 := by
      dsimp [n, R] at *
      omega
    have hsn : s + n ≤ morseSardElementaryOrder (a + 1) := by
      exact morseSardElementaryOrder_step hnle
    have hg' : ContDiff ℝ (s + n : ℕ) g :=
      hg.of_le (by exact_mod_cast hsn)
    let S := iteratedFDerivFirstNonflatStratum (n + 1) g
    have hlocal : ∀ x ∈ S, ∃ U : Set (Fin (a + 1) → ℝ),
        IsOpen U ∧ x ∈ U ∧ volume (g '' (S ∩ U)) = 0 := by
      intro x hx
      obtain ⟨U, W, theta, hUopen, hxU, hWopen, _htheta,
          hgtheta, _hcover, himage⟩ :=
        exists_local_contDiffOn_flat_parameterization_of_mem_firstNonflatStratum
          hg' hs hn hx
      have hminTwo : 2 ≤ min (n + 1) (s + 1) := by
        apply le_min
        · omega
        · have hsTwo := morseSardElementaryOrder_two_le a
          dsimp [s]
          omega
      have hcompNull : volume ((g ∘ theta) ''
          (fderivRankZeroSource (g ∘ theta) ∩ W)) = 0 := by
        exact ihLocal hb hWopen hgtheta
      rw [fderivRankZeroSource_eq_iteratedFDerivFlatSet_two] at hcompNull
      refine ⟨U, hUopen, hxU, measure_mono_null himage ?_⟩
      apply measure_mono_null _ hcompNull
      rintro z ⟨u, hu, rfl⟩
      refine ⟨u, ⟨?_, hu.2⟩, rfl⟩
      intro j hj hjTwo
      exact hu.1 j hj (hjTwo.trans_le hminTwo)
    choose U hUopen hxU hUzero using
      fun p : S => hlocal p p.property
    let O : S → Set S := fun p => Subtype.val ⁻¹' U p
    have hO : ∀ p : S, O p ∈ 𝓝 p := by
      intro p
      exact continuousAt_subtype_val.preimage_mem_nhds
        ((hUopen p).mem_nhds (hxU p))
    obtain ⟨T, hTcount, hTcover⟩ :=
      TopologicalSpace.countable_cover_nhds hO
    have hcover : S ⊆ ⋃ p ∈ T, S ∩ U p := by
      intro x hx
      let q : S := ⟨x, hx⟩
      have hq : q ∈ ⋃ p ∈ T, O p := by
        rw [hTcover]
        exact Set.mem_univ q
      simp only [Set.mem_iUnion] at hq
      obtain ⟨p, hpT, hxp⟩ := hq
      exact Set.mem_iUnion.mpr ⟨p,
        Set.mem_iUnion.mpr ⟨hpT, hx, hxp⟩⟩
    have himage : g '' S ⊆ ⋃ p ∈ T, g '' (S ∩ U p) := by
      rintro z ⟨x, hx, rfl⟩
      have hxc := hcover hx
      simp only [Set.mem_iUnion] at hxc ⊢
      obtain ⟨p, hpT, hxp⟩ := hxc
      exact ⟨p, hpT, x, hxp, rfl⟩
    have hzero : volume (g '' S) = 0 := by
      apply measure_mono_null himage
      exact (measure_biUnion_null_iff hTcount).mpr
        (fun p _hpT => hUzero p)
    simpa only [S, hni] using hzero

private theorem morseSardRankZero_global_local (a : ℕ) : MorseSardRankZeroGlobal a ∧ MorseSardRankZeroLocal a := by
  induction a with
  | zero =>
      have hglobal : MorseSardRankZeroGlobal 0 := morseSardRankZero_base_global
      exact ⟨hglobal, morseSardRankZeroLocal_of_global hglobal⟩
  | succ a ih =>
      have hglobal : MorseSardRankZeroGlobal (a + 1) := morseSardRankZero_step_global a ih.2
      exact ⟨hglobal, morseSardRankZeroLocal_of_global hglobal⟩

/-- Rank-zero Morse--Sard in all source and positive target dimensions at
an explicit finite regularity order.  The proof is a genuine induction on
source dimension: the deepest flat locus uses Taylor--Hausdorff nullity, and
each nonflat layer is parameterized by a hypersurface and passed to the
localized lower-dimensional induction hypothesis. -/
theorem volume_image_fderivRankZeroSource_eq_zero_of_elementaryOrder
    {a b : ℕ} (hb : 0 < b)
    {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ (morseSardElementaryOrder a : ℕ) g) :
    volume (g '' fderivRankZeroSource g) = 0 :=
  (morseSardRankZero_global_local a).1 hb hg


/-- Local open-chart form of the all-dimensional elementary-order theorem. -/
theorem volume_image_fderivRankZeroSource_inter_open_eq_zero_of_elementaryOrder
    {a b : ℕ} (hb : 0 < b)
    {f : (Fin a → ℝ) → (Fin b → ℝ)} {W : Set (Fin a → ℝ)}
    (hWopen : IsOpen W)
    (hf : ContDiffOn ℝ (morseSardElementaryOrder a : ℕ) f W) :
    volume (f '' (fderivRankZeroSource f ∩ W)) = 0 :=
  (morseSardRankZero_global_local a).2 hb hWopen hf

/-- Every smooth Euclidean map has a null image of its rank-zero source. -/
theorem volume_image_fderivRankZeroSource_eq_zero_of_contDiff_top
    {a b : ℕ} (hb : 0 < b)
    {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ ∞ g) :
    volume (g '' fderivRankZeroSource g) = 0 := by
  apply volume_image_fderivRankZeroSource_eq_zero_of_elementaryOrder hb
  exact hg.of_le (by simp)

/-- Local open-chart form of smooth rank-zero Morse--Sard. -/
theorem volume_image_fderivRankZeroSource_inter_open_eq_zero_of_contDiffOn_top
    {a b : ℕ} (hb : 0 < b)
    {f : (Fin a → ℝ) → (Fin b → ℝ)} {W : Set (Fin a → ℝ)}
    (hWopen : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) :
    volume (f '' (fderivRankZeroSource f ∩ W)) = 0 := by
  apply volume_image_fderivRankZeroSource_inter_open_eq_zero_of_elementaryOrder hb hWopen
  exact hf.of_le (by simp)

end AbelFormalization
