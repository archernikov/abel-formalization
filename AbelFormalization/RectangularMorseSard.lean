import AbelFormalization.SmoothFamilyConstantRankLocalFiber
import AbelFormalization.CharbonnelSardianProjectionCriticalValues
import AbelFormalization.MorseSardNonflatHypersurface
import AbelFormalization.MorseSardRankNormalization
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The constant-rank part of rectangular Morse--Sard

Mathlib's Jacobian Sard theorem treats square maps.  For a rectangular map
`g : ℝᵃ → ℝᵇ`, this file separates the part of the classical proof that only
uses the constant-rank theorem from the genuinely higher-order rank-jump
argument.

For a `C¹` map, derivative rank is lower semicontinuous.  Consequently its
critical source is the union of finitely many locally constant-rank strata
and a rank-jump set contained in a finite union of frontiers.  Every locally
constant-rank stratum of rank `< b` has null image: an implicit-function
chart gives a local `C¹` parametrization by `ℝᵏ`, and second countability
turns the local statement into a countable cover.

Thus rectangular Morse--Sard is reduced exactly to nullity of the image of
the rank-jump set.  Controlling that image is the part requiring the
`C^(a-b+1)` Taylor-cover induction; it does not follow from the square Sard
theorem or from the constant-rank APIs alone.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## Coordinate splitting for residual slices -/

/-- Reorder the target coordinates so that the coordinates selected by
`rows` come first and the complementary `b-k` coordinates come second. -/
noncomputable def selectedOutputIndexEquiv {b k : ℕ}
    (rows : Fin k ↪ Fin b) : Fin k ⊕ Fin (b - k) ≃ Fin b := by
  let p : Fin b → Prop := fun j ↦ j ∈ Set.range rows
  let erange : Fin k ≃ {j : Fin b // p j} := rows.toEquivRange
  have hrange : Fintype.card {j : Fin b // p j} = k := by
    rw [← Fintype.card_congr erange]
    simp
  have hcompl : Fintype.card {j : Fin b // ¬ p j} = b - k := by
    rw [Fintype.card_subtype_compl, hrange]
    simp
  let ecompl : Fin (b - k) ≃ {j : Fin b // ¬ p j} :=
    (Fintype.equivFinOfCardEq hcompl).symm
  exact (erange.sumCongr ecompl).trans (Equiv.sumCompl p)

/-- The first block of `selectedOutputIndexEquiv` is exactly `rows`. -/
@[simp] theorem selectedOutputIndexEquiv_apply_inl {b k : ℕ}
    (rows : Fin k ↪ Fin b) (i : Fin k) :
    selectedOutputIndexEquiv rows (Sum.inl i) = rows i := by
  simp [selectedOutputIndexEquiv]

/-- The continuous linear target-coordinate split associated to selected
output rows.  Its first component records the selected outputs. -/
noncomputable def selectedOutputSplit {b k : ℕ}
    (rows : Fin k ↪ Fin b) :
    RealEuclidean b ≃L[ℝ]
      (RealEuclidean k × RealEuclidean (b - k)) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin b ↦ ℝ)
      (selectedOutputIndexEquiv rows)).symm.trans
    (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin k) (Fin (b - k))
      (fun _ ↦ ℝ))

/-- Applying the first block of the split reads the selected coordinate. -/
@[simp] theorem selectedOutputSplit_fst_apply {b k : ℕ}
    (rows : Fin k ↪ Fin b) (z : RealEuclidean b) (i : Fin k) :
    (selectedOutputSplit rows z).1 i = z (rows i) := by
  change ((ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin b ↦ ℝ)
    (selectedOutputIndexEquiv rows)).symm z) (Sum.inl i) = z (rows i)
  change (Equiv.piCongrLeft (fun _ : Fin b ↦ ℝ)
    (selectedOutputIndexEquiv rows)).symm z (Sum.inl i) = z (rows i)
  rw [Equiv.piCongrLeft_symm_apply]
  exact congrArg z (selectedOutputIndexEquiv_apply_inl rows i)

/-- A coordinate permutation and product split preserve Euclidean volume. -/
theorem selectedOutputSplit_measurePreserving {b k : ℕ}
    (rows : Fin k ↪ Fin b) :
    MeasurePreserving (selectedOutputSplit rows)
      (volume : Measure (RealEuclidean b))
      (volume : Measure (RealEuclidean k × RealEuclidean (b - k))) := by
  have hpi :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin b ↦ ℝ)
      (selectedOutputIndexEquiv rows)).symm
  have hsum :=
    volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Fin k ⊕ Fin (b - k) ↦ ℝ)
  exact hsum.comp hpi

/-- A compact subset of a Euclidean product is null if every vertical
section is null.  Compactness supplies the measurability needed by Fubini. -/
theorem volume_eq_zero_of_isCompact_of_verticalSections_eq_zero
    {m n : ℕ} {S : Set (RealEuclidean m × RealEuclidean n)}
    (hS : IsCompact S)
    (hsections : ∀ v : RealEuclidean m,
      (volume : Measure (RealEuclidean n)) (Prod.mk v ⁻¹' S) = 0) :
    (volume : Measure (RealEuclidean m × RealEuclidean n)) S = 0 := by
  rw [Measure.volume_eq_prod]
  exact Measure.measure_prod_null_of_ae_null hS.isClosed.measurableSet
    (Eventually.of_forall hsections)

/-- Nullity after the selected-output coordinate split implies nullity in
the original target coordinates. -/
theorem volume_eq_zero_of_selectedOutputSplit_image
    {b k : ℕ} (rows : Fin k ↪ Fin b) {A : Set (RealEuclidean b)}
    (hzero : volume (selectedOutputSplit rows '' A) = 0) :
    volume A = 0 := by
  have heq := (selectedOutputSplit_measurePreserving rows).measure_preimage_emb
    (selectedOutputSplit rows).toHomeomorph.measurableEmbedding
    (selectedOutputSplit rows '' A)
  rw [Set.preimage_image_eq A (selectedOutputSplit rows).injective] at heq
  exact heq.trans hzero

/-! ## Rank decomposition -/

/-- The source points where the Fréchet derivative is not surjective. -/
def rectangularCriticalSource {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) : Set (RealEuclidean a) :=
  {x | ¬Function.Surjective (fderiv ℝ g x)}

/-- The corresponding set of critical values. -/
def rectangularCriticalValues {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) : Set (RealEuclidean b) :=
  g '' rectangularCriticalSource g

/-- Surjectivity onto `ℝᵇ` is equivalent to full range dimension. -/
theorem fderiv_surjective_iff_finrank_range_eq
    {a b : ℕ} (L : RealEuclidean a →L[ℝ] RealEuclidean b) :
    Function.Surjective L ↔
      Module.finrank ℝ (LinearMap.range L.toLinearMap) = b := by
  constructor
  · intro hL
    rw [LinearMap.range_eq_top.mpr hL, finrank_top,
      Module.finrank_fin_fun]
  · intro hL
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Module.finrank_fin_fun] using hL

/-- Failure of surjectivity is the strict rank inequality. -/
theorem not_fderiv_surjective_iff_finrank_range_lt
    {a b : ℕ} (L : RealEuclidean a →L[ℝ] RealEuclidean b) :
    ¬Function.Surjective L ↔
      Module.finrank ℝ (LinearMap.range L.toLinearMap) < b := by
  have hle : Module.finrank ℝ (LinearMap.range L.toLinearMap) ≤ b := by
    calc
      Module.finrank ℝ (LinearMap.range L.toLinearMap) ≤
          Module.finrank ℝ (RealEuclidean b) :=
        Submodule.finrank_le _
      _ = b := by simp only [Module.finrank_fin_fun]
  rw [fderiv_surjective_iff_finrank_range_eq]
  omega

/-- The critical source is the finite union of its exact-rank loci. -/
theorem rectangularCriticalSource_eq_iUnion_rankLocus
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b) :
    rectangularCriticalSource g =
      ⋃ k : Fin b, standardJacobianRankLocus g k := by
  ext x
  rw [rectangularCriticalSource, Set.mem_ofPred_eq,
    not_fderiv_surjective_iff_finrank_range_lt]
  constructor
  · intro hx
    let k : Fin b :=
      ⟨Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g x).toLinearMap), hx⟩
    exact Set.mem_iUnion.mpr ⟨k, rfl⟩
  · intro hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    change Module.finrank ℝ
      (LinearMap.range (fderiv ℝ g x).toLinearMap) = k at hk
    simpa only [hk] using k.isLt

/-- The critical values are the finite union of the images of exact-rank
loci. -/
theorem rectangularCriticalValues_eq_iUnion_image_rankLocus
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b) :
    rectangularCriticalValues g =
      ⋃ k : Fin b, g '' standardJacobianRankLocus g k := by
  rw [rectangularCriticalValues,
    rectangularCriticalSource_eq_iUnion_rankLocus, image_iUnion]

/-! ## Lower semicontinuity of derivative rank -/

/-- The locus where derivative rank is at least `k`. -/
def fderivRankAtLeast {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (k : ℕ) :
    Set (RealEuclidean a) :=
  {x | k ≤ Module.finrank ℝ
    (LinearMap.range (fderiv ℝ g x).toLinearMap)}

/-- For a `C¹` map, the locus where derivative rank is at least `k` is
open.  This is the finite-dimensional lower semicontinuity of rank. -/
theorem isOpen_fderivRankAtLeast_of_contDiff_one
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) :
    IsOpen (fderivRankAtLeast g k) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change k ≤ Module.finrank ℝ
    (LinearMap.range (fderiv ℝ g x).toLinearMap) at hx
  have hxMatrix : k ≤ (standardRectangularJacobian g x).rank := by
    rw [standardRectangularJacobian_rank_eq_finrank_range_fderiv
      (hg.differentiable one_ne_zero x)]
    exact hx
  obtain ⟨rows, cols, hminor⟩ :=
    (matrix_le_rank_iff_exists_square_minor_ne_zero
      (standardRectangularJacobian g x)).mp hxMatrix
  have hopen : IsOpen
      {y | standardJacobianMinor g rows cols y ≠ 0} :=
    isOpen_ne_fun
      (continuous_standardJacobianMinor_of_contDiff_one hg rows cols)
      continuous_const
  apply Filter.mem_of_superset (hopen.mem_nhds hminor)
  intro y hy
  change k ≤ Module.finrank ℝ
    (LinearMap.range (fderiv ℝ g y).toLinearMap)
  rw [← standardRectangularJacobian_rank_eq_finrank_range_fderiv
    (hg.differentiable one_ne_zero y)]
  exact (matrix_le_rank_iff_exists_square_minor_ne_zero
    (standardRectangularJacobian g y)).mpr ⟨rows, cols, hy⟩

/-- At an exact-rank point, rank cannot decrease in a sufficiently small
neighborhood. -/
theorem eventually_rank_ge_of_mem_standardJacobianRankLocus
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) {x : RealEuclidean a}
    (hx : x ∈ standardJacobianRankLocus g k) :
    ∀ᶠ y in 𝓝 x,
      k ≤ Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) := by
  exact (isOpen_fderivRankAtLeast_of_contDiff_one hg).mem_nhds hx.ge

/-! ## Locally constant-rank and rank-jump pieces -/

/-- Exact rank `k`, together with a neighborhood upper bound by `k`.
For a `C¹` map this is equivalent to rank being locally constant at `k`. -/
def locallyUpperRankStratum {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (k : ℕ) :
    Set (RealEuclidean a) :=
  {x | x ∈ standardJacobianRankLocus g k ∧
    ∀ᶠ y in 𝓝 x,
      Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) ≤ k}

theorem mem_locallyUpperRankStratum_iff_eventually_rank_eq
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) {x : RealEuclidean a} :
    x ∈ locallyUpperRankStratum g k ↔
      x ∈ standardJacobianRankLocus g k ∧
        ∀ᶠ y in 𝓝 x,
          Module.finrank ℝ
            (LinearMap.range (fderiv ℝ g y).toLinearMap) = k := by
  constructor
  · rintro ⟨hx, hupper⟩
    refine ⟨hx, ?_⟩
    filter_upwards
      [eventually_rank_ge_of_mem_standardJacobianRankLocus hg hx,
        hupper] with y hlower hupperY
    exact Nat.le_antisymm hupperY hlower
  · rintro ⟨hx, heq⟩
    refine ⟨hx, ?_⟩
    filter_upwards [heq] with y hy
    exact hy.le

/-- Points of exact rank `k` where no neighborhood has rank bounded by `k`. -/
def fderivRankJumpStratum {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (k : ℕ) :
    Set (RealEuclidean a) :=
  standardJacobianRankLocus g k \ locallyUpperRankStratum g k

/-- The union of all critical rank-jump strata. -/
def rectangularRankJumpSet {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) : Set (RealEuclidean a) :=
  ⋃ k : Fin b, fderivRankJumpStratum g k

/-- A rank-jump point of exact rank `k` is on the frontier of the open locus
where rank is at least `k+1`. -/
theorem fderivRankJumpStratum_subset_frontier
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) :
    fderivRankJumpStratum g k ⊆ frontier (fderivRankAtLeast g (k + 1)) := by
  intro x hx
  rcases hx with ⟨hxrank, hxnot⟩
  have hnotUpper : ¬∀ᶠ y in 𝓝 x,
      Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) ≤ k := by
    intro hupper
    exact hxnot ⟨hxrank, hupper⟩
  have hfrequent : ∃ᶠ y in 𝓝 x,
      k + 1 ≤ Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) := by
    apply (Filter.not_eventually.mp hnotUpper).mono
    intro y hy
    exact Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hy)
  have hclosure : x ∈ closure (fderivRankAtLeast g (k + 1)) := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨y, hyrank, hyt⟩ := (hfrequent.and_eventually ht).exists
    exact ⟨y, hyt, hyrank⟩
  refine ⟨hclosure, ?_⟩
  rw [(isOpen_fderivRankAtLeast_of_contDiff_one hg).interior_eq]
  change ¬k + 1 ≤ Module.finrank ℝ
    (LinearMap.range (fderiv ℝ g x).toLinearMap)
  change Module.finrank ℝ
    (LinearMap.range (fderiv ℝ g x).toLinearMap) = k at hxrank
  omega

/-- Each fixed-rank jump stratum is nowhere dense. -/
theorem isNowhereDense_fderivRankJumpStratum
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) :
    IsNowhereDense (fderivRankJumpStratum g k) := by
  apply IsNowhereDense.mono
    (fderivRankJumpStratum_subset_frontier hg)
  apply isClosed_frontier.isNowhereDense_iff.mpr
  rw [← frontier_compl]
  exact interior_frontier
    (isOpen_fderivRankAtLeast_of_contDiff_one hg).isClosed_compl

/-- The full critical rank-jump set is nowhere dense, being a finite union
of frontier pieces. -/
theorem isNowhereDense_rectangularRankJumpSet
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) :
    IsNowhereDense (rectangularRankJumpSet g) := by
  apply IsNowhereDense.iUnion
  intro k
  exact isNowhereDense_fderivRankJumpStratum hg

theorem interior_rectangularRankJumpSet_eq_empty
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) :
    interior (rectangularRankJumpSet g) = ∅ := by
  apply Set.eq_empty_of_subset_empty
  calc
    interior (rectangularRankJumpSet g) ⊆
        interior (closure (rectangularRankJumpSet g)) :=
      interior_mono subset_closure
    _ = ∅ := isNowhereDense_rectangularRankJumpSet hg

/-! ## Local parametrization of the constant-rank pieces -/

/-- At a locally upper-rank point, a nonzero minor selects output
coordinates whose fibers locally determine the full map. -/
theorem exists_selectedOutput_local_fiber_of_mem_locallyUpperRankStratum
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) {x : RealEuclidean a}
    (hx : x ∈ locallyUpperRankStratum g k) :
    ∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin a,
      standardJacobianMinor g rows cols x ≠ 0 ∧
        ∃ U : Set (RealEuclidean a),
          IsOpen U ∧ x ∈ U ∧
            ∀ y ∈ U, ∀ z ∈ U,
              selectedOutputMap g rows y = selectedOutputMap g rows z →
                g y = g z := by
  have hminors :=
    (finrank_range_fderiv_eq_iff_standardJacobianMinors
      (hg.differentiable one_ne_zero x)).mp hx.1
  obtain ⟨rows, cols, hminor⟩ := hminors.1
  obtain ⟨U, hUopen, hxU, hfiber⟩ :=
    exists_open_nhds_eq_of_selectedOutputMap_eq_of_rank_le
      hg x rows cols hminor hx.2
  exact ⟨rows, cols, hminor, U, hUopen, hxU, hfiber⟩

/-- Near a locally constant rank-`k` point, the image of `g` is contained in
the image of a `C¹` map defined on a subset of `ℝᵏ`.  This is the local
constant-rank reduction needed for the measure argument below. -/
theorem exists_local_contDiffOn_parameterization_of_mem_locallyUpperRankStratum
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) {x : RealEuclidean a}
    (hx : x ∈ locallyUpperRankStratum g k) :
    ∃ U : Set (RealEuclidean a), ∃ V : Set (RealEuclidean k),
      ∃ phi : RealEuclidean k → RealEuclidean b,
        IsOpen U ∧ x ∈ U ∧ IsOpen V ∧
          ContDiffOn ℝ 1 phi V ∧ g '' U ⊆ phi '' V := by
  obtain ⟨rows, cols, hminor, U₀, hU₀open, hxU₀, hfiber⟩ :=
    exists_selectedOutput_local_fiber_of_mem_locallyUpperRankStratum
      hg hx
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
  let s₀ : RealEuclidean k := (e x).1
  let v₀ : (fderiv ℝ f x).ker := (e x).2
  let localSec : RealEuclidean k → RealEuclidean a :=
    fun s ↦ e.symm (s, v₀)
  have hsectionBase : localSec s₀ = x := by
    change e.symm ((e x).1, (e x).2) = x
    simpa only [Prod.eta] using e.left_inv hxsource
  have hpairContDiff : ContDiff ℝ 1
      (fun s : RealEuclidean k ↦ (s, v₀)) :=
    contDiff_id.prodMk contDiff_const
  have hsectionAt : ContDiffAt ℝ 1 localSec s₀ := by
    change ContDiffAt ℝ 1
      (e.symm ∘ fun s : RealEuclidean k ↦ (s, v₀)) s₀
    have hcomp := hinverseAt.comp s₀ hpairContDiff.contDiffAt
    simpa only [s₀, v₀, Prod.eta] using hcomp
  have htargetEventually : ∀ᶠ s in 𝓝 s₀, (s, v₀) ∈ e.target := by
    have hopen : IsOpen
        ((fun s : RealEuclidean k ↦ (s, v₀)) ⁻¹' e.target) :=
      e.open_target.preimage hpairContDiff.continuous
    apply hopen.mem_nhds
    change (s₀, v₀) ∈ e.target
    simpa only [s₀, v₀, Prod.eta] using e.map_source hxsource
  have hsectionUEventually : ∀ᶠ s in 𝓝 s₀, localSec s ∈ U₀ := by
    apply hsectionAt.continuousAt
    rw [hsectionBase]
    exact hU₀open.mem_nhds hxU₀
  have hsectionContDiffEventually :
      ∀ᶠ s in 𝓝 s₀, ContDiffAt ℝ 1 localSec s :=
    hsectionAt.eventually (by simp)
  let good : Set (RealEuclidean k) :=
    {s | (s, v₀) ∈ e.target ∧ localSec s ∈ U₀ ∧
      ContDiffAt ℝ 1 localSec s}
  have hgood : good ∈ 𝓝 s₀ := by
    filter_upwards [htargetEventually, hsectionUEventually,
      hsectionContDiffEventually] with s hsTarget hsU hsContDiff
    exact ⟨hsTarget, hsU, hsContDiff⟩
  let V := interior good
  have hVopen : IsOpen V := isOpen_interior
  have hs₀V : s₀ ∈ V := mem_interior_iff_mem_nhds.mpr hgood
  let phi : RealEuclidean k → RealEuclidean b := fun s ↦ g (localSec s)
  let U : Set (RealEuclidean a) := U₀ ∩ f ⁻¹' V
  have hUopen : IsOpen U :=
    hU₀open.inter (hVopen.preimage hf.continuous)
  have hfx : f x = s₀ := by
    exact (hfst x).symm
  have hxU : x ∈ U := by
    refine ⟨hxU₀, ?_⟩
    change f x ∈ V
    rw [hfx]
    exact hs₀V
  have hphi : ContDiffOn ℝ 1 phi V := by
    intro s hs
    have hsGood : s ∈ good := interior_subset hs
    exact (hg.contDiffAt.comp s hsGood.2.2).contDiffWithinAt
  refine ⟨U, V, phi, hUopen, hxU, hVopen, hphi, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  let s : RealEuclidean k := f y
  have hsV : s ∈ V := hy.2
  have hsGood : s ∈ good := interior_subset hsV
  have hright : e (localSec s) = (s, v₀) :=
    e.right_inv hsGood.1
  have hsectionSelected : f (localSec s) = s := by
    calc
      f (localSec s) = (e (localSec s)).1 := (hfst (localSec s)).symm
      _ = ((s, v₀) : RealEuclidean k × (fderiv ℝ f x).ker).1 :=
        congrArg Prod.fst hright
      _ = s := rfl
  have hvalue : g y = g (localSec s) := by
    apply hfiber y hy.1 (localSec s) hsGood.2.1
    change f y = f (localSec s)
    rw [hsectionSelected]
  exact ⟨s, hsV, hvalue.symm⟩

/-! ## Nullity of the locally constant critical-rank part -/

/-- A locally constant rank-`k` point, with `k < b`, has an open source
neighborhood whose image has zero `b`-dimensional volume. -/
theorem exists_open_image_volume_eq_zero_of_mem_locallyUpperRankStratum
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) (hkb : k < b) {x : RealEuclidean a}
    (hx : x ∈ locallyUpperRankStratum g k) :
    ∃ U : Set (RealEuclidean a),
      IsOpen U ∧ x ∈ U ∧ volume (g '' U) = 0 := by
  obtain ⟨U, V, phi, hUopen, hxU, _hVopen, hphi, himage⟩ :=
    exists_local_contDiffOn_parameterization_of_mem_locallyUpperRankStratum
      hg hx
  have hdim :
      Module.finrank ℝ (RealEuclidean k) <
        (Module.finrank ℝ (RealEuclidean b) : ℝ) := by
    simp only [Module.finrank_fin_fun]
    exact_mod_cast hkb
  have hzeroMeasure :
      (μH[Module.finrank ℝ (RealEuclidean b)] :
        Measure (RealEuclidean k)) = 0 :=
    Real.hausdorffMeasure_of_finrank_lt hdim
  have hVzero :
      (μH[Module.finrank ℝ (RealEuclidean b)] :
        Measure (RealEuclidean k)) V = 0 := by
    rw [hzeroMeasure]
    rfl
  have hphiZero :
      (μH[Module.finrank ℝ (RealEuclidean b)] :
        Measure (RealEuclidean b)) (phi '' V) = 0 :=
    (hphi.differentiableOn (by simp)).hausdorffMeasure_image_eq_zero
      (by positivity) hVzero
  have hphiVolume : volume (phi '' V) = 0 := by
    have hmeasure :
        (μH[Module.finrank ℝ (RealEuclidean b)] :
          Measure (RealEuclidean b)) = volume := by
      simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
        (hausdorffMeasure_pi_real (ι := Fin b))
    rw [hmeasure] at hphiZero
    exact hphiZero
  exact ⟨U, hUopen, hxU, measure_mono_null himage hphiVolume⟩

/-- For each critical rank `k < b`, the image of the whole locally
constant-rank stratum has zero volume. -/
theorem volume_image_locallyUpperRankStratum_eq_zero
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) (hkb : k < b) :
    volume (g '' locallyUpperRankStratum g k) = 0 := by
  let S := locallyUpperRankStratum g k
  choose U hUopen hxU hUzero using
    fun p : S ↦
      exists_open_image_volume_eq_zero_of_mem_locallyUpperRankStratum
        hg hkb p.property
  let W : S → Set S := fun p ↦ Subtype.val ⁻¹' U p
  have hW : ∀ p : S, W p ∈ 𝓝 p := by
    intro p
    exact continuousAt_subtype_val.preimage_mem_nhds
      ((hUopen p).mem_nhds (hxU p))
  obtain ⟨T, hTcount, hTcover⟩ :=
    TopologicalSpace.countable_cover_nhds hW
  have hcover : S ⊆ ⋃ p ∈ T, U p := by
    intro x hx
    let q : S := ⟨x, hx⟩
    have hq : q ∈ ⋃ p ∈ T, W p := by
      rw [hTcover]
      exact Set.mem_univ q
    simp only [Set.mem_iUnion] at hq
    obtain ⟨p, hpT, hqp⟩ := hq
    exact Set.mem_iUnion.mpr ⟨p,
      Set.mem_iUnion.mpr ⟨hpT, hqp⟩⟩
  have himage : g '' S ⊆ ⋃ p ∈ T, g '' U p := by
    rintro z ⟨x, hx, rfl⟩
    have hxcover := hcover hx
    simp only [Set.mem_iUnion] at hxcover ⊢
    obtain ⟨p, hpT, hxUp⟩ := hxcover
    exact ⟨p, hpT, x, hxUp, rfl⟩
  apply measure_mono_null himage
  exact (measure_biUnion_null_iff hTcount).mpr
    (fun p _hpT ↦ hUzero p)

/-- The union of all locally constant critical-rank strata. -/
def rectangularLocallyConstantCriticalSet {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) : Set (RealEuclidean a) :=
  ⋃ k : Fin b, locallyUpperRankStratum g k

/-- The complete locally constant-rank part of the critical source has null
image. -/
theorem volume_image_rectangularLocallyConstantCriticalSet_eq_zero
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) :
    volume (g '' rectangularLocallyConstantCriticalSet g) = 0 := by
  rw [rectangularLocallyConstantCriticalSet, image_iUnion,
    measure_iUnion_null_iff]
  intro k
  exact volume_image_locallyUpperRankStratum_eq_zero hg k.isLt

theorem interior_image_rectangularLocallyConstantCriticalSet_eq_empty
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) :
    interior (g '' rectangularLocallyConstantCriticalSet g) = ∅ :=
  (volume : Measure (RealEuclidean b)).interior_eq_empty_of_null
    (volume_image_rectangularLocallyConstantCriticalSet_eq_zero hg)

/-- The critical source is exactly the locally constant-rank part together
with the rank-jump part. -/
theorem rectangularCriticalSource_eq_constant_union_rankJump
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b) :
    rectangularCriticalSource g =
      rectangularLocallyConstantCriticalSet g ∪
        rectangularRankJumpSet g := by
  rw [rectangularCriticalSource_eq_iUnion_rankLocus]
  ext x
  simp only [rectangularLocallyConstantCriticalSet,
    rectangularRankJumpSet, fderivRankJumpStratum,
    Set.mem_iUnion, Set.mem_union, Set.mem_sdiff]
  constructor
  · rintro ⟨k, hxk⟩
    by_cases hstable : x ∈ locallyUpperRankStratum g k
    · exact Or.inl ⟨k, hstable⟩
    · exact Or.inr ⟨k, hxk, hstable⟩
  · rintro (hstable | hjump)
    · obtain ⟨k, hxk⟩ := hstable
      exact ⟨k, hxk.1⟩
    · obtain ⟨k, hxk, _hnot⟩ := hjump
      exact ⟨k, hxk⟩

/-- The semantic critical values used here agree with the maximal-minor
critical-value set for differentiable maps. -/
theorem rectangularCriticalValues_eq_standardJacobianCriticalValueSet
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : Differentiable ℝ g) :
    rectangularCriticalValues g = standardJacobianCriticalValueSet g := by
  ext e
  rw [mem_standardJacobianCriticalValueSet_iff_nonsurjective g hg e]
  simp only [rectangularCriticalValues, rectangularCriticalSource,
    Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hcritical, rfl⟩
    exact ⟨x, rfl, hcritical⟩
  · rintro ⟨x, hx, hcritical⟩
    exact ⟨x, hcritical, hx⟩

/-- Exact reduction of rectangular Morse--Sard to the rank-jump image.  The
other critical values already form a null set by the constant-rank theorem. -/
theorem volume_standardJacobianCriticalValueSet_eq_zero_iff_rankJump
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) :
    volume (standardJacobianCriticalValueSet g) = 0 ↔
      volume (g '' rectangularRankJumpSet g) = 0 := by
  rw [← rectangularCriticalValues_eq_standardJacobianCriticalValueSet
    (hg.differentiable one_ne_zero), rectangularCriticalValues,
    rectangularCriticalSource_eq_constant_union_rankJump, image_union,
    measure_union_null_iff,
    volume_image_rectangularLocallyConstantCriticalSet_eq_zero hg]
  simp

/-- After deleting the rank-jump image, the remaining rectangular critical
values are already null. -/
theorem volume_standardJacobianCriticalValueSet_sdiff_rankJump_eq_zero
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g) :
    volume (standardJacobianCriticalValueSet g \
      (g '' rectangularRankJumpSet g)) = 0 := by
  apply measure_mono_null _
    (volume_image_rectangularLocallyConstantCriticalSet_eq_zero hg)
  intro e he
  have heCritical : e ∈ rectangularCriticalValues g := by
    rw [rectangularCriticalValues_eq_standardJacobianCriticalValueSet
      (hg.differentiable one_ne_zero)]
    exact he.1
  rw [rectangularCriticalValues,
    rectangularCriticalSource_eq_constant_union_rankJump,
    image_union] at heCritical
  exact heCritical.resolve_right he.2

/-- At the exact Morse--Sard differentiability order, the part of the
rank-jump set on which every derivative below that order vanishes already has
null image.  The remaining rank-jump points are precisely the nonflat jet
strata handled by the hypersurface induction in the classical proof. -/
theorem volume_image_rectangularRankJumpSet_inter_flatJet_eq_zero
    {a b : ℕ} (hba : b < a) (hb : 1 < b)
    {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ (a - b + 1 : ℕ) g) :
    volume (g '' (rectangularRankJumpSet g ∩
      iteratedFDerivFlatSet (a - b + 1) g)) = 0 := by
  apply measure_mono_null (image_mono inter_subset_right)
  exact volume_image_iteratedFDerivFlatSet_eq_zero_of_morseSardOrder
    hba hb hg

/-- Around every point of an exact-rank jump stratum, one fixed minor chart
turns the whole nearby exact-rank locus into rank-zero residual slices.  The
chart inverse and every residual slice retain the full `C^r` regularity of
the original map.

This is the chartwise input to the remaining measure induction: after this
lemma, the only local source pieces still to control are the deepest flat
jet locus and the codimension-one nonflat layers parameterized in
`MorseSardNonflatHypersurface`. -/
theorem exists_rankZeroResidualNeighborhood_of_mem_fderivRankJumpStratum
    {n b k r : ℕ} {g : RealEuclidean (n + k) → RealEuclidean b}
    (hr : 0 < r) (hg : ContDiff ℝ r g)
    {x : RealEuclidean (n + k)}
    (hx : x ∈ fderivRankJumpStratum g k) :
    ∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin (n + k),
      ∃ e : OpenPartialHomeomorph (RealEuclidean (n + k))
          (RealEuclidean n × RealEuclidean k),
        ∃ U : Set (RealEuclidean (n + k)),
          IsOpen U ∧ x ∈ U ∧ U ⊆ e.source ∧
          (∀ y, e y =
            (wilkieColumnComplementaryProjection cols y,
              selectedOutputMap g rows y)) ∧
          (∀ y ∈ U, ContDiffAt ℝ r e.symm (e y)) ∧
          (∀ y ∈ U,
            ContDiffAt ℝ r
              (fun u : RealEuclidean n ↦
                g (e.symm (u, selectedOutputMap g rows y)))
              (wilkieColumnComplementaryProjection cols y)) ∧
          (∀ y ∈ U ∩ standardJacobianRankLocus g k,
            fderiv ℝ
              (fun u : RealEuclidean n ↦
                g (e.symm (u, selectedOutputMap g rows y)))
              (wilkieColumnComplementaryProjection cols y) = 0) := by
  obtain ⟨rows, cols, e, U, hUopen, hxU, hUsource, he,
      hinverse, hsmooth, hzero⟩ :=
    exists_rankZeroResidualChartNeighborhood_of_mem_standardJacobianRankLocus
      hr hg hx.1
  refine ⟨rows, cols, e, U, hUopen, hxU, hUsource, he,
    hinverse, hsmooth, ?_⟩
  intro y hy
  exact hzero y hy.1 hy.2.le

/-- Compact-piece Fubini transport for one rank-normalizing chart.

The selected outputs are the base coordinates.  On each fixed selected-output
fiber, the complementary output map is a rank-zero map from `ℝⁿ` to
`ℝ^(b-k)`.  Through the first source-dimension induction step,
`n ≤ 2 * (b-k) + 1`, its local critical image is null; compactness of `K` makes
the total chart image measurable, so Fubini gives nullity of `g '' K`. -/
theorem volume_image_compact_eq_zero_of_rankZeroResidualChart_of_le_two_mul_add_one
    {n b k : ℕ}
    (hresBA : b - k < n) (hresB : 1 < b - k)
    (hresRange : n ≤ 2 * (b - k) + 1)
    {g : RealEuclidean (n + k) → RealEuclidean b}
    (hg : ContDiff ℝ ((n + k) - b + 1 : ℕ) g)
    (rows : Fin k ↪ Fin b)
    (e : OpenPartialHomeomorph (RealEuclidean (n + k))
      (RealEuclidean n × RealEuclidean k))
    (q : RealEuclidean (n + k) → RealEuclidean n)
    {U K : Set (RealEuclidean (n + k))}
    (hUopen : IsOpen U) (hUsource : U ⊆ e.source)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (he : ∀ y, e y = (q y, selectedOutputMap g rows y))
    (hsmooth : ∀ y ∈ U,
      ContDiffAt ℝ ((n + k) - b + 1 : ℕ)
        (fun u : RealEuclidean n ↦
          g (e.symm (u, selectedOutputMap g rows y))) (q y))
    (hzero : ∀ y ∈ K,
      fderiv ℝ
        (fun u : RealEuclidean n ↦
          g (e.symm (u, selectedOutputMap g rows y))) (q y) = 0) :
    volume (g '' K) = 0 := by
  have hkB : k ≤ b := by omega
  have horder : n - (b - k) + 1 = (n + k) - b + 1 := by omega
  let p : RealEuclidean b →L[ℝ] RealEuclidean (b - k) :=
    (ContinuousLinearMap.snd ℝ (RealEuclidean k)
      (RealEuclidean (b - k))).comp
      (selectedOutputSplit rows).toContinuousLinearMap
  let H : RealEuclidean (n + k) →
      RealEuclidean k × RealEuclidean (b - k) :=
    fun y ↦ selectedOutputSplit rows (g y)
  have hHcontinuous : Continuous H :=
    (selectedOutputSplit rows).continuous.comp hg.continuous
  have hHK : IsCompact (H '' K) := hK.image hHcontinuous
  have hHnull : volume (H '' K) = 0 := by
    apply volume_eq_zero_of_isCompact_of_verticalSections_eq_zero hHK
    intro v
    let R : RealEuclidean n → RealEuclidean (b - k) :=
      fun u ↦ p (g (e.symm (u, v)))
    let W : Set (RealEuclidean n) :=
      (fun u ↦ (u, v)) ⁻¹' (e '' U)
    have heUopen : IsOpen (e '' U) :=
      e.isOpen_image_of_subset_source hUopen hUsource
    have hWopen : IsOpen W := by
      exact heUopen.preimage (continuous_id.prodMk continuous_const)
    have hRsmooth : ContDiffOn ℝ (n - (b - k) + 1 : ℕ) R W := by
      intro u hu
      obtain ⟨y, hyU, hey⟩ := hu
      have hey' : e y = (q y, selectedOutputMap g rows y) := he y
      have hq : q y = u := by
        rw [hey] at hey'
        exact (congrArg Prod.fst hey').symm
      have hv : selectedOutputMap g rows y = v := by
        rw [hey] at hey'
        exact (congrArg Prod.snd hey').symm
      have hfull := hsmooth y hyU
      rw [horder]
      have hfull' : ContDiffAt ℝ ((n + k) - b + 1 : ℕ)
          (fun z : RealEuclidean n ↦ g (e.symm (z, v))) u := by
        simpa only [hq, hv] using hfull
      have hp : ContDiffAt ℝ ((n + k) - b + 1 : ℕ) p
          (g (e.symm (u, v))) := p.contDiff.contDiffAt
      have hcomp := hp.comp u hfull'
      simpa only [R, Function.comp_def] using hcomp.contDiffWithinAt
    have hRnull : volume (R '' (fderivRankZeroSource R ∩ W)) = 0 := by
      exact
        volume_image_fderivRankZeroSource_inter_open_eq_zero_of_morseSardOrder_of_le_two_mul_add_one
          hresBA hresB hresRange hWopen hRsmooth
    apply measure_mono_null _ hRnull
    intro w hw
    obtain ⟨y, hyK, hHy⟩ := hw
    have hyU : y ∈ U := hKU hyK
    have hsel : selectedOutputMap g rows y = v := by
      ext i
      calc
        selectedOutputMap g rows y i =
            (selectedOutputSplit rows (g y)).1 i := by
              exact (selectedOutputSplit_fst_apply rows (g y) i).symm
        _ = v i := congrArg (fun z ↦ z.1 i) hHy
    have heY : e y = (q y, v) := by
      rw [he y, hsel]
    have hleft : e.symm (q y, v) = y := by
      rw [← heY]
      exact e.left_inv (hUsource hyU)
    have hRvalue : R (q y) = w := by
      have hsnd : (selectedOutputSplit rows (g y)).2 = w :=
        congrArg Prod.snd hHy
      change (selectedOutputSplit rows (g (e.symm (q y, v)))).2 = w
      rw [hleft]
      exact hsnd
    refine ⟨q y, ⟨?_, ?_⟩, hRvalue⟩
    · change fderiv ℝ R (q y) = 0
      have hfullSmooth := hsmooth y hyU
      have hfullDiff : DifferentiableAt ℝ
          (fun u : RealEuclidean n ↦
            g (e.symm (u, selectedOutputMap g rows y))) (q y) :=
        hfullSmooth.differentiableAt (by
          have : 0 < (n + k) - b + 1 := by omega
          exact_mod_cast this.ne')
      have hpDeriv : HasFDerivAt p p (g (e.symm (q y,
          selectedOutputMap g rows y))) := p.hasFDerivAt
      have hcomp := hpDeriv.comp (q y) hfullDiff.hasFDerivAt
      have hcompDeriv := hcomp.fderiv
      rw [hzero y hyK] at hcompDeriv
      simpa only [R, hsel, Function.comp_def, ContinuousLinearMap.comp_zero]
        using hcompDeriv
    · change (q y, v) ∈ e '' U
      exact ⟨y, hyU, heY⟩
  apply volume_eq_zero_of_selectedOutputSplit_image rows
  simpa only [image_image, Function.comp_def, H] using hHnull

/-- The original direct residual range is an immediate subcase of the
one-step source-dimensional theorem. -/
theorem volume_image_compact_eq_zero_of_rankZeroResidualChart_of_le_two_mul
    {n b k : ℕ}
    (hresBA : b - k < n) (hresB : 1 < b - k)
    (hresRange : n ≤ 2 * (b - k))
    {g : RealEuclidean (n + k) → RealEuclidean b}
    (hg : ContDiff ℝ ((n + k) - b + 1 : ℕ) g)
    (rows : Fin k ↪ Fin b)
    (e : OpenPartialHomeomorph (RealEuclidean (n + k))
      (RealEuclidean n × RealEuclidean k))
    (q : RealEuclidean (n + k) → RealEuclidean n)
    {U K : Set (RealEuclidean (n + k))}
    (hUopen : IsOpen U) (hUsource : U ⊆ e.source)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (he : ∀ y, e y = (q y, selectedOutputMap g rows y))
    (hsmooth : ∀ y ∈ U,
      ContDiffAt ℝ ((n + k) - b + 1 : ℕ)
        (fun u : RealEuclidean n ↦
          g (e.symm (u, selectedOutputMap g rows y))) (q y))
    (hzero : ∀ y ∈ K,
      fderiv ℝ
        (fun u : RealEuclidean n ↦
          g (e.symm (u, selectedOutputMap g rows y))) (q y) = 0) :
    volume (g '' K) = 0 := by
  exact
    volume_image_compact_eq_zero_of_rankZeroResidualChart_of_le_two_mul_add_one
      hresBA hresB (by omega) hg rows e q
      hUopen hUsource hK hKU he hsmooth hzero

/-- The exact-rank-zero jump stratum is contained in the rank-zero source
used by the flat/nonflat jet decomposition. -/
theorem fderivRankJumpStratum_zero_subset_fderivRankZeroSource
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b} :
    fderivRankJumpStratum g 0 ⊆ fderivRankZeroSource g := by
  intro x hx
  change fderiv ℝ g x = 0
  have hrange : LinearMap.range (fderiv ℝ g x).toLinearMap = ⊥ :=
    Submodule.finrank_eq_zero.mp hx.1
  apply ContinuousLinearMap.ext
  intro v
  have hv : fderiv ℝ g x v ∈
      LinearMap.range (fderiv ℝ g x).toLinearMap := ⟨v, rfl⟩
  rw [hrange] at hv
  exact hv

/-- Local null-image estimates on one exact-rank jump stratum assemble to a
global estimate.  Second countability is used on the source stratum, so no
measurability of the source pieces is required. -/
theorem volume_image_fderivRankJumpStratum_eq_zero_of_local
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hlocal : ∀ x ∈ fderivRankJumpStratum g k,
      ∃ U : Set (RealEuclidean a),
        IsOpen U ∧ x ∈ U ∧
          volume (g '' (fderivRankJumpStratum g k ∩ U)) = 0) :
    volume (g '' fderivRankJumpStratum g k) = 0 := by
  let S := fderivRankJumpStratum g k
  choose U hUopen hxU hUzero using
    fun p : S ↦ hlocal p p.property
  let W : S → Set S := fun p ↦ Subtype.val ⁻¹' U p
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
    have hxcover := hcover hx
    simp only [Set.mem_iUnion] at hxcover ⊢
    obtain ⟨p, hpT, hxp⟩ := hxcover
    exact ⟨p, hpT, x, hxp, rfl⟩
  apply measure_mono_null himage
  exact (measure_biUnion_null_iff hTcount).mpr
    (fun p _hpT ↦ hUzero p)

/-- Exact-rank jump strata are null whenever their normalized residual
source and target dimensions lie in the first source-dimension extension
`n ≤ 2 * (b-k) + 1`.

For a rank-`k` stratum in source dimension `n+k`, the residual map has source
dimension `n`, target dimension `b-k`, and exactly the same classical
differentiability order.  A compact exhaustion inside the fixed-minor chart
turns the residual rank-zero estimate into the required local estimate, and
`volume_image_fderivRankJumpStratum_eq_zero_of_local` globalizes it. -/
theorem volume_image_fderivRankJumpStratum_eq_zero_of_residual_le_two_mul_add_one
    {n b k : ℕ}
    (hresBA : b - k < n) (hresB : 1 < b - k)
    (hresRange : n ≤ 2 * (b - k) + 1)
    {g : RealEuclidean (n + k) → RealEuclidean b}
    (hg : ContDiff ℝ ((n + k) - b + 1 : ℕ) g) :
    volume (g '' fderivRankJumpStratum g k) = 0 := by
  have hr : 0 < (n + k) - b + 1 := by omega
  have hgOne : ContDiff ℝ 1 g :=
    hg.of_le (by exact_mod_cast hr)
  apply volume_image_fderivRankJumpStratum_eq_zero_of_local
  intro x hx
  obtain ⟨rows, cols, e, U₀, hU₀open, hxU₀, hU₀source, he,
      _hinverse, hsmooth, hzero⟩ :=
    exists_rankZeroResidualChartNeighborhood_of_mem_standardJacobianRankLocus
      hr hg hx.1
  let U : Set (RealEuclidean (n + k)) :=
    U₀ ∩ fderivRankAtLeast g k
  have hUopen : IsOpen U :=
    hU₀open.inter (isOpen_fderivRankAtLeast_of_contDiff_one hgOne)
  have hxRankAtLeast : x ∈ fderivRankAtLeast g k := by
    change k ≤ Module.finrank ℝ
      (LinearMap.range (fderiv ℝ g x).toLinearMap)
    have hxeq := hx.1
    change Module.finrank ℝ
      (LinearMap.range (fderiv ℝ g x).toLinearMap) = k at hxeq
    omega
  have hxU : x ∈ U := ⟨hxU₀, hxRankAtLeast⟩
  obtain ⟨eps, heps, hball⟩ :=
    Metric.mem_nhds_iff.mp (hUopen.mem_nhds hxU)
  let delta : ℝ := eps / 2
  let V : Set (RealEuclidean (n + k)) := Metric.ball x delta
  let A : Set (RealEuclidean (n + k)) :=
    fderivRankAtLeast g (k + 1)
  let K : Set (RealEuclidean (n + k)) :=
    Metric.closedBall x delta ∩ frontier A
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hclosedSubset : Metric.closedBall x delta ⊆ Metric.ball x eps :=
    Metric.closedBall_subset_ball (by
      dsimp [delta]
      linarith)
  have hKcompact : IsCompact K :=
    (isCompact_closedBall x delta).inter_right isClosed_frontier
  have hKU₀ : K ⊆ U₀ := by
    intro y hy
    exact (hball (hclosedSubset hy.1)).1
  have hKzero : ∀ y ∈ K,
      fderiv ℝ
        (fun u : RealEuclidean n ↦
          g (e.symm (u, selectedOutputMap g rows y)))
        (wilkieColumnComplementaryProjection cols y) = 0 := by
    intro y hyK
    apply hzero y (hKU₀ hyK)
    have hyAtLeast : y ∈ fderivRankAtLeast g k :=
      (hball (hclosedSubset hyK.1)).2
    have hAopen : IsOpen A :=
      isOpen_fderivRankAtLeast_of_contDiff_one hgOne
    have hyNotA : y ∉ A := by
      intro hyA
      exact Set.disjoint_left.mp
        (disjoint_frontier_iff_isOpen.mpr hAopen) hyK.2 hyA
    change Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) ≤ k
    change k ≤ Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) at hyAtLeast
    change ¬k + 1 ≤ Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) at hyNotA
    omega
  have hKnull : volume (g '' K) = 0 := by
    exact
      volume_image_compact_eq_zero_of_rankZeroResidualChart_of_le_two_mul_add_one
        hresBA hresB hresRange hg rows e
        (wilkieColumnComplementaryProjection cols)
        hU₀open hU₀source hKcompact hKU₀ he hsmooth hKzero
  refine ⟨V, Metric.isOpen_ball, Metric.mem_ball_self hdelta, ?_⟩
  apply measure_mono_null (image_mono ?_) hKnull
  intro y hy
  refine ⟨Metric.ball_subset_closedBall hy.2, ?_⟩
  exact fderivRankJumpStratum_subset_frontier hgOne hy.1

/-- The original direct residual range follows from the one-step theorem. -/
theorem volume_image_fderivRankJumpStratum_eq_zero_of_residual_le_two_mul
    {n b k : ℕ}
    (hresBA : b - k < n) (hresB : 1 < b - k)
    (hresRange : n ≤ 2 * (b - k))
    {g : RealEuclidean (n + k) → RealEuclidean b}
    (hg : ContDiff ℝ ((n + k) - b + 1 : ℕ) g) :
    volume (g '' fderivRankJumpStratum g k) = 0 := by
  exact
    volume_image_fderivRankJumpStratum_eq_zero_of_residual_le_two_mul_add_one
      hresBA hresB (by omega) hg

/-- The local rank-jump assembler for the rank-zero stratum through the
first source-dimension extension `a ≤ 2b + 1`. -/
theorem volume_image_fderivRankJumpStratum_zero_eq_zero_of_morseSardOrder_of_le_two_mul_add_one
    {a b : ℕ} (hba : b < a) (hb : 1 < b) (hab : a ≤ 2 * b + 1)
    {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ (a - b + 1 : ℕ) g) :
    volume (g '' fderivRankJumpStratum g 0) = 0 := by
  apply volume_image_fderivRankJumpStratum_eq_zero_of_local
  intro x hx
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ x, ?_⟩
  apply measure_mono_null
    (image_mono (fun _y hy =>
      fderivRankJumpStratum_zero_subset_fderivRankZeroSource hy.1))
  exact
    volume_image_fderivRankZeroSource_eq_zero_of_morseSardOrder_of_le_two_mul_add_one
      hba hb hab hg

/-- The rank-zero exact stratum in the original direct range. -/
theorem volume_image_fderivRankJumpStratum_zero_eq_zero_of_morseSardOrder_of_le_two_mul
    {a b : ℕ} (hba : b < a) (hb : 1 < b) (hab : a ≤ 2 * b)
    {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ (a - b + 1 : ℕ) g) :
    volume (g '' fderivRankJumpStratum g 0) = 0 := by
  exact
    volume_image_fderivRankJumpStratum_zero_eq_zero_of_morseSardOrder_of_le_two_mul_add_one
      hba hb (by omega) hg

/-- To prove nullity of the complete rank-jump image it is enough to prove
the chart-local estimate on every critical exact-rank stratum. -/
theorem volume_image_rectangularRankJumpSet_eq_zero_of_local
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hlocal : ∀ k : Fin b, ∀ x ∈ fderivRankJumpStratum g k,
      ∃ U : Set (RealEuclidean a),
        IsOpen U ∧ x ∈ U ∧
          volume (g '' (fderivRankJumpStratum g k ∩ U)) = 0) :
    volume (g '' rectangularRankJumpSet g) = 0 := by
  rw [rectangularRankJumpSet, image_iUnion, measure_iUnion_null_iff]
  intro k
  exact volume_image_fderivRankJumpStratum_eq_zero_of_local
    (hlocal k)

/-- The exact `C^(a-b+1)` regularity appearing in classical rectangular
Morse--Sard reduces to the same rank-jump image. -/
theorem volume_standardJacobianCriticalValueSet_eq_zero_iff_rankJump_of_morseSardOrder
    {a b : ℕ} (_hba : b ≤ a)
    {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ (a - b + 1 : ℕ) g) :
    volume (standardJacobianCriticalValueSet g) = 0 ↔
      volume (g '' rectangularRankJumpSet g) = 0 := by
  apply volume_standardJacobianCriticalValueSet_eq_zero_iff_rankJump
  have horder : (1 : ℕ) ≤ a - b + 1 := by omega
  exact hg.of_le (by exact_mod_cast horder)

/-- Compact-piece Fubini transport for a normalized residual map at the
all-dimensional elementary differentiability order. -/
theorem volume_image_compact_eq_zero_of_rankZeroResidualChart_of_elementaryOrder
    {n b k : ℕ}
    (hresB : 0 < b - k)
    {g : RealEuclidean (n + k) → RealEuclidean b}
    (hg : ContDiff ℝ (morseSardElementaryOrder n : ℕ) g)
    (rows : Fin k ↪ Fin b)
    (e : OpenPartialHomeomorph (RealEuclidean (n + k))
      (RealEuclidean n × RealEuclidean k))
    (q : RealEuclidean (n + k) → RealEuclidean n)
    {U K : Set (RealEuclidean (n + k))}
    (hUopen : IsOpen U) (hUsource : U ⊆ e.source)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (he : ∀ y, e y = (q y, selectedOutputMap g rows y))
    (hsmooth : ∀ y ∈ U,
      ContDiffAt ℝ (morseSardElementaryOrder n : ℕ)
        (fun u : RealEuclidean n ↦
          g (e.symm (u, selectedOutputMap g rows y))) (q y))
    (hzero : ∀ y ∈ K,
      fderiv ℝ
        (fun u : RealEuclidean n ↦
          g (e.symm (u, selectedOutputMap g rows y))) (q y) = 0) :
    volume (g '' K) = 0 := by
  have hkB : k ≤ b := by omega
  let p : RealEuclidean b →L[ℝ] RealEuclidean (b - k) :=
    (ContinuousLinearMap.snd ℝ (RealEuclidean k)
      (RealEuclidean (b - k))).comp
      (selectedOutputSplit rows).toContinuousLinearMap
  let H : RealEuclidean (n + k) →
      RealEuclidean k × RealEuclidean (b - k) :=
    fun y ↦ selectedOutputSplit rows (g y)
  have hHcontinuous : Continuous H :=
    (selectedOutputSplit rows).continuous.comp hg.continuous
  have hHK : IsCompact (H '' K) := hK.image hHcontinuous
  have hHnull : volume (H '' K) = 0 := by
    apply volume_eq_zero_of_isCompact_of_verticalSections_eq_zero hHK
    intro v
    let R : RealEuclidean n → RealEuclidean (b - k) :=
      fun u ↦ p (g (e.symm (u, v)))
    let W : Set (RealEuclidean n) :=
      (fun u ↦ (u, v)) ⁻¹' (e '' U)
    have heUopen : IsOpen (e '' U) :=
      e.isOpen_image_of_subset_source hUopen hUsource
    have hWopen : IsOpen W := by
      exact heUopen.preimage (continuous_id.prodMk continuous_const)
    have hRsmooth : ContDiffOn ℝ (morseSardElementaryOrder n : ℕ) R W := by
      intro u hu
      obtain ⟨y, hyU, hey⟩ := hu
      have hey' : e y = (q y, selectedOutputMap g rows y) := he y
      have hq : q y = u := by
        rw [hey] at hey'
        exact (congrArg Prod.fst hey').symm
      have hv : selectedOutputMap g rows y = v := by
        rw [hey] at hey'
        exact (congrArg Prod.snd hey').symm
      have hfull := hsmooth y hyU
      have hfull' : ContDiffAt ℝ (morseSardElementaryOrder n : ℕ)
          (fun z : RealEuclidean n ↦ g (e.symm (z, v))) u := by
        simpa only [hq, hv] using hfull
      have hp : ContDiffAt ℝ (morseSardElementaryOrder n : ℕ) p
          (g (e.symm (u, v))) := p.contDiff.contDiffAt
      have hcomp := hp.comp u hfull'
      simpa only [R, Function.comp_def] using hcomp.contDiffWithinAt
    have hRnull : volume (R '' (fderivRankZeroSource R ∩ W)) = 0 := by
      exact
        volume_image_fderivRankZeroSource_inter_open_eq_zero_of_elementaryOrder
          hresB hWopen hRsmooth
    apply measure_mono_null _ hRnull
    intro w hw
    obtain ⟨y, hyK, hHy⟩ := hw
    have hyU : y ∈ U := hKU hyK
    have hsel : selectedOutputMap g rows y = v := by
      ext i
      calc
        selectedOutputMap g rows y i =
            (selectedOutputSplit rows (g y)).1 i := by
              exact (selectedOutputSplit_fst_apply rows (g y) i).symm
        _ = v i := congrArg (fun z ↦ z.1 i) hHy
    have heY : e y = (q y, v) := by
      rw [he y, hsel]
    have hleft : e.symm (q y, v) = y := by
      rw [← heY]
      exact e.left_inv (hUsource hyU)
    have hRvalue : R (q y) = w := by
      have hsnd : (selectedOutputSplit rows (g y)).2 = w :=
        congrArg Prod.snd hHy
      change (selectedOutputSplit rows (g (e.symm (q y, v)))).2 = w
      rw [hleft]
      exact hsnd
    refine ⟨q y, ⟨?_, ?_⟩, hRvalue⟩
    · change fderiv ℝ R (q y) = 0
      have hfullSmooth := hsmooth y hyU
      have hfullDiff : DifferentiableAt ℝ
          (fun u : RealEuclidean n ↦
            g (e.symm (u, selectedOutputMap g rows y))) (q y) :=
        hfullSmooth.differentiableAt (by
          exact_mod_cast (morseSardElementaryOrder_pos n).ne')
      have hpDeriv : HasFDerivAt p p (g (e.symm (q y,
          selectedOutputMap g rows y))) := p.hasFDerivAt
      have hcomp := hpDeriv.comp (q y) hfullDiff.hasFDerivAt
      have hcompDeriv := hcomp.fderiv
      rw [hzero y hyK] at hcompDeriv
      simpa only [R, hsel, Function.comp_def, ContinuousLinearMap.comp_zero]
        using hcompDeriv
    · change (q y, v) ∈ e '' U
      exact ⟨y, hyU, heY⟩
  apply volume_eq_zero_of_selectedOutputSplit_image rows
  simpa only [image_image, Function.comp_def, H] using hHnull


/-- Exact-rank transport when the source dimension is displayed as the
residual dimension plus the rank. -/
private theorem volume_image_fderivRankJumpStratum_eq_zero_of_elementaryOrder_additiveSource
    {n b k : ℕ}
    (hresB : 0 < b - k)
    {g : RealEuclidean (n + k) → RealEuclidean b}
    (hg : ContDiff ℝ (morseSardElementaryOrder n : ℕ) g) :
    volume (g '' fderivRankJumpStratum g k) = 0 := by
  have hr : 0 < morseSardElementaryOrder n :=
    morseSardElementaryOrder_pos n
  have hgOne : ContDiff ℝ 1 g :=
    hg.of_le (by exact_mod_cast hr)
  apply volume_image_fderivRankJumpStratum_eq_zero_of_local
  intro x hx
  obtain ⟨rows, cols, e, U₀, hU₀open, hxU₀, hU₀source, he,
      _hinverse, hsmooth, hzero⟩ :=
    exists_rankZeroResidualChartNeighborhood_of_mem_standardJacobianRankLocus
      hr hg hx.1
  let U : Set (RealEuclidean (n + k)) :=
    U₀ ∩ fderivRankAtLeast g k
  have hUopen : IsOpen U :=
    hU₀open.inter (isOpen_fderivRankAtLeast_of_contDiff_one hgOne)
  have hxRankAtLeast : x ∈ fderivRankAtLeast g k := by
    change k ≤ Module.finrank ℝ
      (LinearMap.range (fderiv ℝ g x).toLinearMap)
    have hxeq := hx.1
    change Module.finrank ℝ
      (LinearMap.range (fderiv ℝ g x).toLinearMap) = k at hxeq
    omega
  have hxU : x ∈ U := ⟨hxU₀, hxRankAtLeast⟩
  obtain ⟨eps, heps, hball⟩ :=
    Metric.mem_nhds_iff.mp (hUopen.mem_nhds hxU)
  let delta : ℝ := eps / 2
  let V : Set (RealEuclidean (n + k)) := Metric.ball x delta
  let A : Set (RealEuclidean (n + k)) :=
    fderivRankAtLeast g (k + 1)
  let K : Set (RealEuclidean (n + k)) :=
    Metric.closedBall x delta ∩ frontier A
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hclosedSubset : Metric.closedBall x delta ⊆ Metric.ball x eps :=
    Metric.closedBall_subset_ball (by
      dsimp [delta]
      linarith)
  have hKcompact : IsCompact K :=
    (isCompact_closedBall x delta).inter_right isClosed_frontier
  have hKU₀ : K ⊆ U₀ := by
    intro y hy
    exact (hball (hclosedSubset hy.1)).1
  have hKzero : ∀ y ∈ K,
      fderiv ℝ
        (fun u : RealEuclidean n ↦
          g (e.symm (u, selectedOutputMap g rows y)))
        (wilkieColumnComplementaryProjection cols y) = 0 := by
    intro y hyK
    apply hzero y (hKU₀ hyK)
    have hyAtLeast : y ∈ fderivRankAtLeast g k :=
      (hball (hclosedSubset hyK.1)).2
    have hAopen : IsOpen A :=
      isOpen_fderivRankAtLeast_of_contDiff_one hgOne
    have hyNotA : y ∉ A := by
      intro hyA
      exact Set.disjoint_left.mp
        (disjoint_frontier_iff_isOpen.mpr hAopen) hyK.2 hyA
    change Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) ≤ k
    change k ≤ Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) at hyAtLeast
    change ¬k + 1 ≤ Module.finrank ℝ
        (LinearMap.range (fderiv ℝ g y).toLinearMap) at hyNotA
    omega
  have hKnull : volume (g '' K) = 0 := by
    exact
      volume_image_compact_eq_zero_of_rankZeroResidualChart_of_elementaryOrder
        hresB hg rows e
        (wilkieColumnComplementaryProjection cols)
        hU₀open hU₀source hKcompact hKU₀ he hsmooth hKzero
  refine ⟨V, Metric.isOpen_ball, Metric.mem_ball_self hdelta, ?_⟩
  apply measure_mono_null (image_mono ?_) hKnull
  intro y hy
  refine ⟨Metric.ball_subset_closedBall hy.2, ?_⟩
  exact fderivRankJumpStratum_subset_frontier hgOne hy.1



/-- Every exact-rank jump stratum has null image at the elementary
regularity order of its normalized residual source dimension. -/
theorem volume_image_fderivRankJumpStratum_eq_zero_of_elementaryOrder
    {a b k : ℕ} (hka : k ≤ a) (hkb : k < b)
    {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ (morseSardElementaryOrder (a - k) : ℕ) g) :
    volume (g '' fderivRankJumpStratum g k) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, a = n + k := ⟨a - k, by omega⟩
  have hsub : n + k - k = n := by omega
  rw [hsub] at hg
  exact volume_image_fderivRankJumpStratum_eq_zero_of_elementaryOrder_additiveSource
    (n := n) (b := b) (k := k) (by omega) hg


/-- Full rectangular rank-jump nullity at the elementary finite regularity
budget.  Monotonicity of the budget supplies every residual exact-rank
stratum from the single source-order hypothesis. -/
theorem volume_image_rectangularRankJumpSet_eq_zero_of_elementaryOrder
    {a b : ℕ} (hba : b ≤ a)
    {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ (morseSardElementaryOrder a : ℕ) g) :
    volume (g '' rectangularRankJumpSet g) = 0 := by
  rw [rectangularRankJumpSet, image_iUnion, measure_iUnion_null_iff]
  intro k
  apply volume_image_fderivRankJumpStratum_eq_zero_of_elementaryOrder
  · omega
  · exact k.isLt
  · apply hg.of_le
    exact_mod_cast morseSardElementaryOrder_mono (Nat.sub_le a k)

/-- Rectangular Morse--Sard in all finite dimensions at the explicit
elementary differentiability order. -/
theorem volume_standardJacobianCriticalValueSet_eq_zero_of_elementaryOrder
    {a b : ℕ} (hba : b ≤ a)
    {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ (morseSardElementaryOrder a : ℕ) g) :
    volume (standardJacobianCriticalValueSet g) = 0 := by
  apply (volume_standardJacobianCriticalValueSet_eq_zero_iff_rankJump_of_morseSardOrder
    hba (hg.of_le ?_)).2
  · exact volume_image_rectangularRankJumpSet_eq_zero_of_elementaryOrder
      hba hg
  · have hsource := morseSardElementaryOrder_source_le a
    exact_mod_cast (show a - b + 1 ≤ morseSardElementaryOrder a by omega)

/-- The full rectangular Morse--Sard theorem for smooth Euclidean maps. -/
theorem volume_standardJacobianCriticalValueSet_eq_zero_of_contDiff_top
    {a b : ℕ} (hba : b ≤ a)
    {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ ∞ g) :
    volume (standardJacobianCriticalValueSet g) = 0 := by
  apply volume_standardJacobianCriticalValueSet_eq_zero_of_elementaryOrder hba
  exact hg.of_le (by simp)

end AbelFormalization
