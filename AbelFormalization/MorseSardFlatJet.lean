import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# The flat-jet Taylor estimate in Morse--Sard

This file proves the deepest-flat-stratum base case of the classical
higher-order Morse--Sard induction.  If the derivatives of orders
`1, ..., r - 1` of a `C^r` map vanish at two points, Taylor's theorem on the
line segment between them gives an `r`-Hölder estimate.  Exhausting the source
by closed balls then bounds the Hausdorff dimension of the whole image.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology MeasureTheory NNReal ENNReal

namespace AbelFormalization

set_option autoImplicit false

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The source points where all positive-order derivatives below `r` vanish. -/
def iteratedFDerivFlatSet (r : ℕ) (g : E → F) : Set E :=
  {x | ∀ i : ℕ, 0 < i → i < r → iteratedFDeriv ℝ i g x = 0}

private def lineCLM (v : E) : ℝ →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight v

/-- Iterated differentiation after restricting a smooth map to an affine
line amounts to evaluating its iterated Fréchet derivative repeatedly on the
line's direction vector. -/
theorem iteratedDeriv_line_eq {g : E → F} {r : ℕ}
    (hg : ContDiff ℝ r g) (x v : E) (t : ℝ) :
    iteratedDeriv r (fun u : ℝ ↦ g (x + u • v)) t =
      iteratedFDeriv ℝ r g (x + t • v) (fun _ ↦ v) := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  let L : ℝ →L[ℝ] E := lineCLM v
  have hshift : ContDiff ℝ r (fun z : E ↦ g (x + z)) := by
    exact hg.comp (contDiff_const.add contDiff_id)
  have hcomp := L.iteratedFDeriv_comp_right hshift t (i := r) le_rfl
  have happ := congrArg (fun T ↦ T (fun _ ↦ (1 : ℝ))) hcomp
  change iteratedFDeriv ℝ r ((fun z : E ↦ g (x + z)) ∘ L) t
      (fun _ ↦ 1) = _ at happ
  simpa [Function.comp_def, L, lineCLM,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_comp_add_left] using happ

/-- At a flat point, the Taylor polynomial of degree `r - 1` along any line
is just the constant term. -/
theorem taylorWithinEval_line_eq_of_mem_iteratedFDerivFlatSet
    {g : E → F} {r : ℕ} (hg : ContDiff ℝ r g)
    {x y : E} (hx : x ∈ iteratedFDerivFlatSet r g) :
    taylorWithinEval (fun t : ℝ ↦ g (x + t • (y - x))) (r - 1)
        (Icc 0 1) 0 1 = g x := by
  let phi : ℝ → F := fun t ↦ g (x + t • (y - x))
  have hphi : ContDiff ℝ r phi := by
    exact hg.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  rw [taylor_within_apply]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    have hir : i < r := by
      have := Finset.mem_range.mp hi
      omega
    have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    have hwithin :
        iteratedDerivWithin i phi (Icc 0 1) 0 = iteratedDeriv i phi 0 := by
      apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      · exact hphi.contDiffAt.of_le (by exact_mod_cast hir.le)
      · exact ⟨le_rfl, zero_le_one⟩
    have hline : iteratedDeriv i phi 0 =
        iteratedFDeriv ℝ i g x (fun _ ↦ y - x) := by
      simpa [phi] using
        iteratedDeriv_line_eq (hg.of_le (by exact_mod_cast hir.le)) x (y - x) 0
    rw [hwithin, hline, hx i hiPos hir]
    simp
  · intro h0
    simp at h0

/-- On every closed ball, the restriction of a `C^r` map to its flat
`(r - 1)`-jet set is `r`-Hölder. -/
theorem exists_holderOnWith_iteratedFDerivFlatSet_inter_closedBall
    [FiniteDimensional ℝ E] {g : E → F} {r : ℕ}
    (hg : ContDiff ℝ r g) (hr : 0 < r) (R : ℝ) :
    ∃ K : ℝ≥0, HolderOnWith K (r : ℝ≥0) g
      (iteratedFDerivFlatSet r g ∩ Metric.closedBall 0 R) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
    ((hg.continuous_iteratedFDeriv le_rfl).continuousOn)
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  let K : ℝ≥0 := Real.toNNReal (M / ((r - 1).factorial : ℝ))
  refine ⟨K, ?_⟩
  intro x hx y hy
  have hxy : ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • (y - x) ∈ Metric.closedBall (0 : E) R := by
    intro t ht
    exact (convex_closedBall (0 : E) R).add_smul_sub_mem hx.2 hy.2 ht
  let phi : ℝ → F := fun t ↦ g (x + t • (y - x))
  have hphi : ContDiff ℝ r phi := by
    exact hg.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hphiOn : ContDiffOn ℝ ((r - 1) + 1 : ℕ) phi (Icc 0 1) := by
    simpa [Nat.sub_add_cancel hr] using hphi.contDiffOn
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin ((r - 1) + 1) phi (Icc 0 1) t‖ ≤
        M * ‖y - x‖ ^ r := by
    intro t ht
    have heqWithin :
        iteratedDerivWithin ((r - 1) + 1) phi (Icc 0 1) t =
          iteratedDeriv ((r - 1) + 1) phi t := by
      apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      · exact hphi.contDiffAt.of_le (by
          norm_cast
          omega)
      · exact ht
    rw [heqWithin, Nat.sub_add_cancel hr]
    rw [iteratedDeriv_line_eq hg x (y - x) t]
    calc
      ‖iteratedFDeriv ℝ r g (x + t • (y - x)) (fun _ ↦ y - x)‖ ≤
          ‖iteratedFDeriv ℝ r g (x + t • (y - x))‖ * ‖y - x‖ ^ r := by
            simpa using (iteratedFDeriv ℝ r g (x + t • (y - x))).le_opNorm
              (fun _ ↦ y - x)
      _ ≤ M * ‖y - x‖ ^ r := by
        gcongr
        exact (hC _ (hxy t ht)).trans (le_max_left _ _)
  have htaylor := taylor_mean_remainder_bound (a := (0 : ℝ)) (b := 1)
    (x := 1) (n := r - 1) zero_le_one hphiOn (by simp) hderiv
  rw [taylorWithinEval_line_eq_of_mem_iteratedFDerivFlatSet hg hx.1] at htaylor
  have hdist : dist (g x) (g y) ≤ (K : ℝ) * dist x y ^ r := by
    rw [dist_eq_norm, dist_eq_norm]
    have hKcoe : (K : ℝ) = M / ((r - 1).factorial : ℝ) := by
      exact Real.coe_toNNReal _ (div_nonneg hM (by positivity))
    rw [hKcoe]
    calc
      ‖g x - g y‖ ≤ (M * ‖x - y‖ ^ r) / ((r - 1).factorial : ℝ) := by
        simpa [phi, norm_sub_rev] using htaylor
      _ = M / ((r - 1).factorial : ℝ) * ‖x - y‖ ^ r := by ring
  rw [edist_nndist, edist_nndist, show ((r : ℝ≥0) : ℝ) = r by simp,
    ENNReal.rpow_natCast, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  exact_mod_cast hdist

/-- Hausdorff-dimension bound for the image of the complete flat-jet set. -/
theorem dimH_image_iteratedFDerivFlatSet_le
    [FiniteDimensional ℝ E] {g : E → F} {r : ℕ}
    (hg : ContDiff ℝ r g) (hr : 0 < r) :
    dimH (g '' iteratedFDerivFlatSet r g) ≤
      dimH (Set.univ : Set E) / (r : ℝ≥0) := by
  rw [← Metric.iUnion_inter_closedBall_nat (iteratedFDerivFlatSet r g) 0,
    image_iUnion, dimH_iUnion]
  apply iSup_le
  intro n
  obtain ⟨K, hK⟩ :=
    exists_holderOnWith_iteratedFDerivFlatSet_inter_closedBall hg hr n
  calc
    dimH (g '' (iteratedFDerivFlatSet r g ∩
        Metric.closedBall 0 (n : ℝ))) ≤
        dimH (iteratedFDerivFlatSet r g ∩ Metric.closedBall 0 (n : ℝ)) /
          (r : ℝ≥0) := hK.dimH_image_le (by exact_mod_cast hr)
    _ ≤ dimH (Set.univ : Set E) / (r : ℝ≥0) :=
      ENNReal.div_le_div_right (dimH_mono (subset_univ _)) _

/-- If the Taylor exponent beats the source/target dimension ratio, the
flat-jet image has Hausdorff dimension strictly below the target dimension. -/
theorem dimH_image_iteratedFDerivFlatSet_lt_target
    {a b r : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ r g) (hr : 0 < r) (hdim : a < r * b) :
    dimH (g '' iteratedFDerivFlatSet r g) <
      ((b : ℝ≥0) : ℝ≥0∞) := by
  refine (dimH_image_iteratedFDerivFlatSet_le hg hr).trans_lt ?_
  rw [Real.dimH_univ_eq_finrank]
  rw [ENNReal.div_lt_iff]
  · simp only [Module.finrank_fin_fun]
    exact_mod_cast (show a < b * r by simpa [mul_comm] using hdim)
  · exact Or.inl (by exact_mod_cast hr.ne')
  · exact Or.inl ENNReal.coe_ne_top

/-- In Euclidean spaces, the dimension inequality turns the flat-jet image
bound into target-dimensional Lebesgue nullity. -/
theorem volume_image_iteratedFDerivFlatSet_eq_zero
    {a b r : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ r g) (hr : 0 < r) (hdim : a < r * b) :
    volume (g '' iteratedFDerivFlatSet r g) = 0 := by
  have hzero : (μH[b] : Measure (Fin b → ℝ))
      (g '' iteratedFDerivFlatSet r g) = 0 :=
    hausdorffMeasure_of_dimH_lt (X := Fin b → ℝ)
      (s := g '' iteratedFDerivFlatSet r g) (d := (b : ℝ≥0))
      (dimH_image_iteratedFDerivFlatSet_lt_target hg hr hdim)
  have hmeasure : (μH[b] : Measure (Fin b → ℝ)) = volume := by
    simpa only [Fintype.card_fin] using
      (hausdorffMeasure_pi_real (ι := Fin b))
  rw [hmeasure] at hzero
  exact hzero

/-- The flat-jet base case at the exact classical Morse--Sard regularity.
For a genuinely rectangular map with target dimension at least two, the
identity
`(a - b + 1) * b - a = (b - 1) * (a - b)`
provides the strict dimension inequality required above. -/
theorem volume_image_iteratedFDerivFlatSet_eq_zero_of_morseSardOrder
    {a b : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hba : b < a) (hb : 1 < b)
    (hg : ContDiff ℝ (a - b + 1 : ℕ) g) :
    volume (g '' iteratedFDerivFlatSet (a - b + 1) g) = 0 := by
  apply volume_image_iteratedFDerivFlatSet_eq_zero hg (by omega)
  let d := a - b
  have hd : 1 ≤ d := by
    dsimp [d]
    omega
  have ha : a = d + b := by
    dsimp [d]
    omega
  rw [ha]
  simp only [Nat.add_sub_cancel_right]
  nlinarith

/-!
### The critical-dimensional little-o endpoint

The strict inequality in `volume_image_iteratedFDerivFlatSet_eq_zero` is not
available when the source dimension is exactly `s` times the target
dimension.  If the derivative of order `s` vanishes as well, continuity of
that derivative makes the Taylor coefficient arbitrarily small.  The finite
grid argument below turns this little-o estimate into zero target volume.
-/

/-- Taylor's estimate with an explicit bound for the top derivative along
the segment.  The extra flat derivative in `iteratedFDerivFlatSet (s + 1) g`
is not used in the Taylor polynomial; it will make the bound arbitrarily
small in the compact-uniform version below. -/
theorem flatSucc_dist_le_of_iteratedFDeriv_le {g : E → F} {s : ℕ}
    (hg : ContDiff ℝ s g) (hs : 0 < s) {x y : E}
    (hx : x ∈ iteratedFDerivFlatSet (s + 1) g) {C : ℝ}
    (hC : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ s g (x + t • (y - x))‖ ≤ C) :
    dist (g x) (g y) ≤
      C * dist x y ^ s / ((s - 1).factorial : ℝ) := by
  let phi : ℝ → F := fun t ↦ g (x + t • (y - x))
  have hphi : ContDiff ℝ s phi := by
    exact hg.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hphiOn : ContDiffOn ℝ ((s - 1) + 1 : ℕ) phi (Icc 0 1) := by
    simpa [Nat.sub_add_cancel hs] using hphi.contDiffOn
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin ((s - 1) + 1) phi (Icc 0 1) t‖ ≤
        C * ‖y - x‖ ^ s := by
    intro t ht
    have heqWithin :
        iteratedDerivWithin ((s - 1) + 1) phi (Icc 0 1) t =
          iteratedDeriv ((s - 1) + 1) phi t := by
      apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      · exact hphi.contDiffAt.of_le (by norm_cast; omega)
      · exact ht
    rw [heqWithin, Nat.sub_add_cancel hs]
    rw [iteratedDeriv_line_eq hg x (y - x) t]
    calc
      ‖iteratedFDeriv ℝ s g (x + t • (y - x)) (fun _ ↦ y - x)‖ ≤
          ‖iteratedFDeriv ℝ s g (x + t • (y - x))‖ * ‖y - x‖ ^ s := by
            simpa using (iteratedFDeriv ℝ s g (x + t • (y - x))).le_opNorm
              (fun _ ↦ y - x)
      _ ≤ C * ‖y - x‖ ^ s := by
        gcongr
        exact hC t ht
  have htaylor := taylor_mean_remainder_bound (a := (0 : ℝ)) (b := 1)
    (x := 1) (n := s - 1) zero_le_one hphiOn (by simp) hderiv
  have hx' : x ∈ iteratedFDerivFlatSet s g := by
    intro i hi his
    exact hx i hi (by omega)
  rw [taylorWithinEval_line_eq_of_mem_iteratedFDerivFlatSet hg hx'] at htaylor
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖g x - g y‖ ≤ C * ‖y - x‖ ^ s / ((s - 1).factorial : ℝ) := by
      simpa [phi, norm_sub_rev] using htaylor
    _ = C * ‖x - y‖ ^ s / ((s - 1).factorial : ℝ) := by
      rw [norm_sub_rev]

/-- On a bounded piece of the set where derivatives through order `s`
vanish, the `s`-th order Taylor coefficient is uniformly as small as desired
at sufficiently small scales. -/
theorem exists_uniform_flatSucc_taylor_bound {a b s : ℕ}
    {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ s g) (hs : 0 < s) (R : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ iteratedFDerivFlatSet (s + 1) g ∩
        Metric.closedBall 0 (R : ℝ),
      ∀ y ∈ iteratedFDerivFlatSet (s + 1) g ∩ Metric.closedBall 0 (R : ℝ),
        dist x y < δ →
          dist (g x) (g y) ≤
            ε * dist x y ^ s / ((s - 1).factorial : ℝ) := by
  let D := fun z : Fin a → ℝ ↦ iteratedFDeriv ℝ s g z
  have hDcont : Continuous D := hg.continuous_iteratedFDeriv le_rfl
  have hcompact : IsCompact (Metric.closedBall (0 : Fin a → ℝ) (R : ℝ)) :=
    isCompact_closedBall _ _
  have hDuc : UniformContinuousOn D
      (Metric.closedBall (0 : Fin a → ℝ) (R : ℝ)) :=
    hcompact.uniformContinuousOn_of_continuous hDcont.continuousOn
  rcases Metric.uniformContinuousOn_iff.mp hDuc ε hε with ⟨δ, hδ, hclose⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  apply flatSucc_dist_le_of_iteratedFDeriv_le hg hs hx.1
  intro t ht
  have hz : x + t • (y - x) ∈ Metric.closedBall (0 : Fin a → ℝ) (R : ℝ) :=
    (convex_closedBall (0 : Fin a → ℝ) (R : ℝ)).add_smul_sub_mem hx.2 hy.2 ht
  have hdistzx : dist (x + t • (y - x)) x ≤ dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc
      |t| * ‖y - x‖ ≤ 1 * ‖y - x‖ := by
        gcongr
        rw [abs_of_nonneg ht.1]
        exact ht.2
      _ = ‖x - y‖ := by rw [one_mul, norm_sub_rev]
  have hnear : dist x (x + t • (y - x)) < δ := by
    rw [dist_comm]
    exact hdistzx.trans_lt hxy
  have hDc := hclose x hx.2 (x + t • (y - x)) hz hnear
  have hDx : D x = 0 := hx.1 s hs (by omega)
  have : ‖D (x + t • (y - x))‖ < ε := by
    simpa [hDx, dist_eq_norm, norm_neg] using hDc
  exact this.le

private abbrev morseSardGridIndex (a Q N : ℕ) :=
  ∀ _ : Fin a, Fin (2 * Q * N)

private def morseSardGridCell {a : ℕ} (Q N : ℕ)
    (f : morseSardGridIndex a Q N) : Set (Fin a → ℝ) :=
  Set.pi Set.univ fun i => Icc (-(Q : ℝ) + (f i : ℝ) / N)
    (-(Q : ℝ) + ((f i : ℕ) + 1 : ℝ) / N)

private lemma morseSardGridCell_ediam_le {a Q N : ℕ} (hN : 0 < N)
    (f : morseSardGridIndex a Q N) :
    Metric.ediam (morseSardGridCell Q N f) ≤ (1 : ℝ≥0∞) / N := by
  refine Metric.ediam_pi_le_of_le fun i => ?_
  simp only [Real.ediam_Icc, add_div,
    ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hN), le_refl,
    add_sub_add_left_eq_sub, add_sub_cancel_left, ENNReal.ofReal_one,
    ENNReal.ofReal_natCast]

private lemma closedBall_subset_morseSardGrid {a R N : ℕ} (hN : 0 < N) :
    Metric.closedBall (0 : Fin a → ℝ) (R : ℝ) ⊆
      ⋃ f : morseSardGridIndex a (R + 1) N,
        morseSardGridCell (R + 1) N f := by
  intro x hx
  have hxnorm : ‖x‖ ≤ (R : ℝ) := by
    simpa only [mem_closedBall_zero_iff] using hx
  have hxcoord : ∀ i : Fin a,
      (-(R + 1 : ℕ) : ℝ) < x i ∧ x i < (R + 1 : ℕ) := by
    intro i
    have hi : |x i| ≤ (R : ℝ) := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans hxnorm
    constructor <;> norm_num at * <;>
      linarith [neg_abs_le (x i), le_abs_self (x i)]
  simp only [mem_iUnion, morseSardGridCell, mem_univ_pi]
  let f : morseSardGridIndex a (R + 1) N := fun i =>
    ⟨⌊(x i + (R + 1 : ℕ)) * N⌋₊, by
      apply (Nat.floor_lt (mul_nonneg
        (by norm_num at hxcoord ⊢; linarith [(hxcoord i).1])
        (Nat.cast_nonneg N))).2
      norm_num at hxcoord ⊢
      have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      nlinarith [(hxcoord i).2]⟩
  refine ⟨f, fun i => ⟨?_, ?_⟩⟩
  · calc
      (-(R + 1 : ℕ) : ℝ) + ⌊(x i + (R + 1 : ℕ)) * N⌋₊ / N ≤
          (-(R + 1 : ℕ) : ℝ) + ((x i + (R + 1 : ℕ)) * N) / N := by
        gcongr
        exact Nat.floor_le (mul_nonneg
          (by norm_num at hxcoord ⊢; linarith [(hxcoord i).1])
          (Nat.cast_nonneg N))
      _ = x i := by field_simp; ring
  · calc
      x i = (-(R + 1 : ℕ) : ℝ) + ((x i + (R + 1 : ℕ)) * N) / N := by
        field_simp
        ring
      _ ≤ (-(R + 1 : ℕ) : ℝ) +
          (⌊(x i + (R + 1 : ℕ)) * N⌋₊ + 1) / N := by
        gcongr
        exact (Nat.lt_floor_add_one _).le

private lemma ennreal_morseSardGrid_cancel {a b s Q N : ℕ}
    (hN : 0 < N) (hdim : a = s * b) (c : ℝ≥0∞) :
    (↑((2 * Q * N) ^ a) : ℝ≥0∞) *
        (c * (1 / (N : ℝ≥0∞)) ^ s) ^ b =
      (↑((2 * Q) ^ a) : ℝ≥0∞) * c ^ b := by
  subst a
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNtop : (N : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by simp
  have hcancel : (N : ℝ≥0∞) * (1 / N) = 1 := by
    simpa only [one_div] using ENNReal.mul_inv_cancel hN0 hNtop
  push_cast
  rw [pow_mul, pow_mul]
  rw [← mul_pow, ← mul_pow]
  congr 1
  rw [mul_pow]
  calc
    ((2 : ℝ≥0∞) * Q) ^ s * N ^ s * (c * (1 / N) ^ s) =
        (((2 : ℝ≥0∞) * Q) ^ s * c) * (N ^ s * (1 / N) ^ s) := by
      ac_rfl
    _ = (((2 : ℝ≥0∞) * Q) ^ s * c) * (N * (1 / N)) ^ s := by
      congr 1
      exact (mul_pow (N : ℝ≥0∞) (1 / N) s).symm
    _ = ((2 : ℝ≥0∞) * Q) ^ s * c := by
      rw [hcancel]
      simp

/-- Quantitative bounded-piece estimate at the critical dimension
`a = s * b`.  The right side is independent of the grid scale and tends to
zero with the top-derivative modulus `ε`. -/
theorem volume_image_iteratedFDerivFlatSet_succ_inter_closedBall_le
    {a b s : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ s g) (hs : 0 < s) (hdim : a = s * b) (R : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    volume (g '' (iteratedFDerivFlatSet (s + 1) g ∩
      Metric.closedBall 0 (R : ℝ))) ≤
      (↑((2 * (R + 1)) ^ a) : ℝ≥0∞) *
        (ENNReal.ofReal (ε / ((s - 1).factorial : ℝ))) ^ b := by
  let S := iteratedFDerivFlatSet (s + 1) g ∩
    Metric.closedBall (0 : Fin a → ℝ) (R : ℝ)
  obtain ⟨δ, hδ, hlocal⟩ := exists_uniform_flatSucc_taylor_bound hg hs R hε
  obtain ⟨N, hNlarge⟩ : ∃ N : ℕ, (1 / δ : ℝ) < N :=
    exists_nat_gt (1 / δ)
  have hN : 0 < N := by
    by_contra h
    simp only [not_lt, nonpos_iff_eq_zero] at h
    subst N
    norm_num at hNlarge
    linarith
  have hinvN : 1 / (N : ℝ) < δ := by
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hN)]
    have := (div_lt_iff₀ hδ).mp hNlarge
    nlinarith
  let B : ℝ := ε * (1 / (N : ℝ)) ^ s / ((s - 1).factorial : ℝ)
  have hB : 0 ≤ B := by positivity
  have hdiam (f : morseSardGridIndex a (R + 1) N) :
      Metric.ediam (g '' (S ∩ morseSardGridCell (R + 1) N f)) ≤
        ENNReal.ofReal B := by
    apply Metric.ediam_le_of_forall_dist_le
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hxyed : edist x y ≤ (1 : ℝ≥0∞) / N :=
      Metric.edist_le_of_ediam_le hx.2 hy.2
        (morseSardGridCell_ediam_le hN f)
    have hxy : dist x y ≤ 1 / (N : ℝ) := by
      rw [edist_dist] at hxyed
      have heq : (1 : ℝ≥0∞) / N = ENNReal.ofReal (1 / (N : ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hN)]
        simp
      rw [heq] at hxyed
      exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp hxyed
    have hlt : dist x y < δ := hxy.trans_lt hinvN
    calc
      dist (g x) (g y) ≤
          ε * dist x y ^ s / ((s - 1).factorial : ℝ) :=
        hlocal x hx.1 y hy.1 hlt
      _ ≤ B := by
        dsimp [B]
        gcongr
  have hcell (f : morseSardGridIndex a (R + 1) N) :
      volume (g '' (S ∩ morseSardGridCell (R + 1) N f)) ≤
        (ENNReal.ofReal B) ^ b := by
    calc
      volume (g '' (S ∩ morseSardGridCell (R + 1) N f)) ≤
          Metric.ediam (g '' (S ∩ morseSardGridCell (R + 1) N f)) ^
            Fintype.card (Fin b) := Real.volume_pi_le_diam_pow _
      _ ≤ (ENNReal.ofReal B) ^ b := by
        simpa using pow_le_pow_left' (hdiam f) b
  have hcover : g '' S ⊆ ⋃ f : morseSardGridIndex a (R + 1) N,
      g '' (S ∩ morseSardGridCell (R + 1) N f) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨f, hxf⟩ := mem_iUnion.mp (closedBall_subset_morseSardGrid hN hx.2)
    exact mem_iUnion.mpr ⟨f, mem_image_of_mem g ⟨hx, hxf⟩⟩
  calc
    volume (g '' (iteratedFDerivFlatSet (s + 1) g ∩
        Metric.closedBall 0 (R : ℝ))) = volume (g '' S) := rfl
    _ ≤ volume (⋃ f : morseSardGridIndex a (R + 1) N,
        g '' (S ∩ morseSardGridCell (R + 1) N f)) := measure_mono hcover
    _ ≤ ∑ f : morseSardGridIndex a (R + 1) N,
        volume (g '' (S ∩ morseSardGridCell (R + 1) N f)) :=
      measure_iUnion_fintype_le volume _
    _ ≤ ∑ _f : morseSardGridIndex a (R + 1) N, (ENNReal.ofReal B) ^ b := by
      exact Finset.sum_le_sum fun f _ => hcell f
    _ = (↑((2 * (R + 1) * N) ^ a) : ℝ≥0∞) * (ENNReal.ofReal B) ^ b := by
      simp [morseSardGridIndex, Fintype.card_pi, Fintype.card_fin,
        Finset.prod_const]
    _ = (↑((2 * (R + 1)) ^ a) : ℝ≥0∞) *
        (ENNReal.ofReal (ε / ((s - 1).factorial : ℝ))) ^ b := by
      have hBform : ENNReal.ofReal B =
          ENNReal.ofReal (ε / ((s - 1).factorial : ℝ)) *
            (1 / (N : ℝ≥0∞)) ^ s := by
        dsimp [B]
        rw [show ε * (1 / (N : ℝ)) ^ s / ((s - 1).factorial : ℝ) =
          (ε / ((s - 1).factorial : ℝ)) * (1 / (N : ℝ)) ^ s by ring]
        rw [ENNReal.ofReal_mul (div_nonneg hε.le (by positivity))]
        rw [ENNReal.ofReal_pow (by positivity)]
        rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hN)]
        simp only [ENNReal.ofReal_one, ENNReal.ofReal_natCast]
      rw [hBform]
      exact ennreal_morseSardGrid_cancel hN hdim _

/-- The critical-dimensional bounded-piece endpoint: a `C^s` map from
dimension `s * b` to dimension `b`, restricted to the set where derivatives
through order `s` vanish, has null image. -/
theorem volume_image_iteratedFDerivFlatSet_succ_inter_closedBall_eq_zero
    {a b s : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ s g) (hs : 0 < s) (hb : 0 < b)
    (hdim : a = s * b) (R : ℕ) :
    volume (g '' (iteratedFDerivFlatSet (s + 1) g ∩
      Metric.closedBall 0 (R : ℝ))) = 0 := by
  let A : ℝ≥0∞ := (↑((2 * (R + 1)) ^ a) : ℝ≥0∞)
  let q : ℕ → ℝ≥0∞ := fun n => A *
    (ENNReal.ofReal ((1 / ((n + 1 : ℕ) : ℝ)) /
      ((s - 1).factorial : ℝ))) ^ b
  have hreal : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbase : Tendsto (fun n : ℕ => ENNReal.ofReal
      ((1 / ((n + 1 : ℕ) : ℝ)) / ((s - 1).factorial : ℝ)))
      atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n : ℕ =>
        (1 / ((n + 1 : ℕ) : ℝ)) / ((s - 1).factorial : ℝ))
        atTop (𝓝 0) := by
      convert hreal.div_const ((s - 1).factorial : ℝ) using 1 <;> simp
    change Tendsto (ENNReal.ofReal ∘ fun n : ℕ =>
      (1 / ((n + 1 : ℕ) : ℝ)) / ((s - 1).factorial : ℝ)) atTop (𝓝 0)
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hdiv
  have hq : Tendsto q atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => (ENNReal.ofReal
        ((1 / ((n + 1 : ℕ) : ℝ)) / ((s - 1).factorial : ℝ))) ^ b)
        atTop (𝓝 0) := by
      simpa [ENNReal.rpow_natCast, hb.ne'] using hbase.ennrpow_const (b : ℝ)
    dsimp [q]
    have hAtop : A ≠ (⊤ : ℝ≥0∞) := by
      dsimp [A]
      exact ENNReal.natCast_ne_top _
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul (a := A) (b := 0) hp (Or.inr hAtop)
  apply nonpos_iff_eq_zero.mp
  apply ge_of_tendsto' hq
  intro n
  dsimp [q, A]
  exact volume_image_iteratedFDerivFlatSet_succ_inter_closedBall_le
    (ε := 1 / ((n + 1 : ℕ) : ℝ)) hg hs hdim R (by positivity)

/-- The critical-dimensional little-o endpoint, without a boundedness
restriction. -/
theorem volume_image_iteratedFDerivFlatSet_succ_eq_zero_of_eq
    {a b s : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ s g) (hs : 0 < s) (hb : 0 < b)
    (hdim : a = s * b) :
    volume (g '' iteratedFDerivFlatSet (s + 1) g) = 0 := by
  rw [← Metric.iUnion_inter_closedBall_nat (iteratedFDerivFlatSet (s + 1) g) 0,
    image_iUnion, measure_iUnion_null_iff]
  intro R
  exact volume_image_iteratedFDerivFlatSet_succ_inter_closedBall_eq_zero
    hg hs hb hdim R

/-- A `C^s` map whose derivatives through order `s` vanish has null image as
soon as the source dimension is at most `s` times the positive target
dimension.  The strict case is the earlier Hölder argument; equality is the
little-o grid endpoint. -/
theorem volume_image_iteratedFDerivFlatSet_succ_eq_zero
    {a b s : ℕ} {g : (Fin a → ℝ) → (Fin b → ℝ)}
    (hg : ContDiff ℝ s g) (hs : 0 < s) (hb : 0 < b)
    (hdim : a ≤ s * b) :
    volume (g '' iteratedFDerivFlatSet (s + 1) g) = 0 := by
  rcases hdim.eq_or_lt with heq | hlt
  · exact volume_image_iteratedFDerivFlatSet_succ_eq_zero_of_eq hg hs hb heq
  · apply measure_mono_null (t := g '' iteratedFDerivFlatSet s g) ?_
      (volume_image_iteratedFDerivFlatSet_eq_zero hg hs hlt)
    exact image_mono fun x hx i hi his => hx i hi (by omega)

end AbelFormalization
