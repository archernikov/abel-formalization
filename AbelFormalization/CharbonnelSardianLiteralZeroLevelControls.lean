import AbelFormalization.CharbonnelSardianLiteralZeroRadialBase
import AbelFormalization.CharbonnelMaxwellClosureBound

/-!
# Compact and intermediate-value controls for the literal-zero constituent

This is the analytic portion of Wilkie's Lemma 3.8 for the polynomial
reciprocal radial equation.  Compactness gives a uniform cutoff below which
an `f²` level in a bounded radial region is close to `Z(f)`.  A finite cover
of a compact frontier region, together with the intermediate value theorem
on segments from zero to nonzero points, gives a uniform cutoff below which
every bounded frontier point is near a positive `f²` level.

The first radial parameter is chosen from a compact maximum of the visible
denominator on a slightly enlarged ball.  Its nested bound is independent of
the final positive-level bound.  Thus the resulting modulus is independent
of the differentiability order of the Sardian certificate.
-/

noncomputable section

open Set Function
open scoped BigOperators Topology

namespace AbelFormalization

set_option autoImplicit false

theorem continuous_literalZeroVisibleRadialDenominator {n : ℕ} :
    Continuous (@literalZeroVisibleRadialDenominator n) := by
  have heq : (@literalZeroVisibleRadialDenominator n) =
      ((fun _ : RealEuclidean n ↦ (1 : ℝ)) +
        @maxwellVisibleNormSqValue n) := by
    funext x
    simp [literalZeroVisibleRadialDenominator,
      maxwellVisibleNormSqValue]
  rw [heq]
  exact continuous_const.add
    (continuous_maxwellVisibleNormSqValue (n := n))

theorem isCompact_literalZeroVisibleRadialDenominator_sublevel
    {n : ℕ} (R : ℝ) :
    IsCompact {x : RealEuclidean n |
      literalZeroVisibleRadialDenominator x ≤ R} := by
  convert isCompact_maxwellVisibleNormSqValue_sublevel
    (n := n) (R - 1) using 1
  ext x
  simp only [Set.mem_setOf_eq, literalZeroVisibleRadialDenominator,
    maxwellVisibleNormSqValue]
  constructor <;> intro hx <;> linarith

/-- Compactness converts a neighborhood of the zero set into a uniform
small-positive-level cutoff.  It also handles an empty zero set: the zero
fiber then has no points and the compact minimum is strictly positive. -/
theorem exists_positive_level_close_to_zero_on_compact
    {n : ℕ} (f : RealEuclideanFunction n) (hf : Continuous f)
    (K : Set (RealEuclidean n)) (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x ∈ K, f x ^ 2 < η →
        ∃ z : RealEuclidean n, f z = 0 ∧ dist x z < δ := by
  let O : Set (RealEuclidean n) :=
    ⋃ z ∈ {z : RealEuclidean n | f z = 0}, Metric.ball z δ
  have hO : IsOpen O :=
    isOpen_biUnion (fun z _ ↦ Metric.isOpen_ball)
  let K' := K
  letI : CompactSpace K' := isCompact_iff_compactSpace.mp hK
  let O' : Set K' := (Subtype.val : K' → RealEuclidean n) ⁻¹' O
  have hO' : IsOpen O' := hO.preimage continuous_subtype_val
  let defect : K' → ℝ := fun x ↦ f x.1 ^ 2
  have hdefect : Continuous defect :=
    (hf.comp continuous_subtype_val).pow 2
  have hzero : {x : K' | defect x = 0} ⊆ O' := by
    intro x hx
    change f x.1 ^ 2 = 0 at hx
    have hfx : f x.1 = 0 := sq_eq_zero_iff.mp hx
    change x.1 ∈ O
    exact Set.mem_biUnion hfx (Metric.mem_ball_self hδ)
  obtain ⟨η, hη, hthreshold⟩ :=
    exists_pos_defect_threshold_of_compact defect hdefect hO' hzero
  refine ⟨η, hη, ?_⟩
  intro x hxK hxlevel
  let xK : K' := ⟨x, hxK⟩
  have hxO : xK ∈ O' :=
    hthreshold xK (by
      change |f x ^ 2| < η
      rwa [abs_of_nonneg (sq_nonneg (f x))])
  change x ∈ O at hxO
  rcases Set.mem_iUnion₂.mp hxO with ⟨z, hz, hball⟩
  exact ⟨z, hz, Metric.mem_ball.mp hball⟩

/-- An interval of positive `f²` levels is reached along a short segment
from a zero to a nonzero point. -/
theorem positive_squared_levels_on_short_segment
    {n : ℕ} (f : RealEuclideanFunction n) (hf : Continuous f)
    (x u : RealEuclidean n) {δ : ℝ}
    (hxzero : f x = 0) (hu : f u ≠ 0)
    (hxu : dist x u < δ)
    {e : ℝ} (he : 0 < e) (helevel : e < f u ^ 2) :
    ∃ y : RealEuclidean n, dist x y < δ ∧ f y ^ 2 = e := by
  let path : ℝ → RealEuclidean n := fun t ↦ x + t • (u - x)
  let g : ℝ → ℝ := fun t ↦ f (path t) ^ 2
  have hpath : Continuous path :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hg : Continuous g := (hf.comp hpath).pow 2
  have hgzero : g 0 = 0 := by simp [g, path, hxzero]
  have hgone : g 1 = f u ^ 2 := by simp [g, path]
  have htarget : e ∈ Set.Icc (g 0) (g 1) := by
    rw [hgzero, hgone]
    exact ⟨he.le, helevel.le⟩
  obtain ⟨t, ht, hgt⟩ :=
    (intermediate_value_Icc (f := g)
      (by norm_num : (0 : ℝ) ≤ 1) hg.continuousOn) htarget
  refine ⟨path t, ?_, hgt⟩
  have htnonneg : 0 ≤ t := ht.1
  have htone : t ≤ 1 := ht.2
  have hdist : dist x (path t) ≤ dist x u := by
    calc
      dist x (path t) = ‖t • (u - x)‖ := by
        rw [dist_eq_norm, norm_sub_rev]
        simp only [path, add_sub_cancel_left]
      _ = t * ‖u - x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg htnonneg]
      _ ≤ ‖u - x‖ := by
        nlinarith [norm_nonneg (u - x)]
      _ = dist x u := by
        rw [dist_eq_norm, norm_sub_rev]
  exact hdist.trans_lt hxu

/-- Frontier zeros have arbitrarily close nonzero points. -/
theorem exists_nonzero_near_literalZero_frontier
    {n : ℕ} (f : RealEuclideanFunction n)
    {x : RealEuclidean n}
    (hx : x ∈ frontier {z : RealEuclidean n | f z = 0})
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : RealEuclidean n, dist x u < δ ∧ f u ≠ 0 := by
  let Z : Set (RealEuclidean n) := {z | f z = 0}
  have hxcomp : x ∈ closure Zᶜ := by
    change x ∈ frontier Z at hx
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  rw [mem_closure_iff_nhds] at hxcomp
  obtain ⟨u, huball, hucompl⟩ :=
    hxcomp (Metric.ball x δ) (Metric.ball_mem_nhds x hδ)
  have hudist : dist u x < δ := Metric.mem_ball.mp huball
  exact ⟨u, by simpa only [dist_comm] using hudist, hucompl⟩

/-- A compact frontier region admits one cutoff valid at every point.  The
proof takes a finite ball cover, records one nonzero witness per center, and
uses the minimum of their strictly positive squared levels. -/
theorem exists_uniform_positive_level_near_frontier
    {n : ℕ} (f : RealEuclideanFunction n) (hf : Continuous f)
    (K : Set (RealEuclidean n)) (hK : IsCompact K)
    (hKfrontier : K ⊆ frontier {z : RealEuclidean n | f z = 0})
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x ∈ K, ∀ e : ℝ, 0 < e → e < η →
        ∃ y : RealEuclidean n, dist x y < δ ∧ f y ^ 2 = e := by
  classical
  have hquarter : 0 < δ / 4 := by positivity
  let U : K → Set (RealEuclidean n) :=
    fun c ↦ Metric.ball c.1 (δ / 4)
  have hUopen : ∀ c : K, IsOpen (U c) :=
    fun _ ↦ Metric.isOpen_ball
  have hUcover : K ⊆ ⋃ c : K, U c := by
    intro x hx
    exact Set.mem_iUnion.mpr
      ⟨⟨x, hx⟩, Metric.mem_ball_self hquarter⟩
  obtain ⟨F, hFcover⟩ :=
    hK.elim_finite_subcover U hUopen hUcover
  have hwitness : ∀ c : K,
      ∃ u : RealEuclidean n,
        dist c.1 u < δ / 4 ∧ f u ≠ 0 := by
    intro c
    exact exists_nonzero_near_literalZero_frontier f
      (hKfrontier c.2) hquarter
  choose u huclose hunonzero using hwitness
  by_cases hF : F.Nonempty
  · let level : K → ℝ := fun c ↦ f (u c) ^ 2
    let η := F.inf' hF level
    have hη : 0 < η := by
      apply (Finset.lt_inf'_iff hF (f := level)).mpr
      intro c hc
      exact sq_pos_of_ne_zero (hunonzero c)
    refine ⟨η, hη, ?_⟩
    intro x hxK e he heη
    have hxcover : x ∈ ⋃ c ∈ F, U c := hFcover hxK
    rcases Set.mem_iUnion₂.mp hxcover with ⟨c, hcF, hxc⟩
    have hxcclose : dist x c.1 < δ / 4 := Metric.mem_ball.mp hxc
    have hxu : dist x (u c) < δ / 2 := by
      have htriangle := dist_triangle x c.1 (u c)
      linarith [huclose c]
    have hxeq : f x = 0 := by
      have hZclosed : IsClosed {z : RealEuclidean n | f z = 0} :=
        isClosed_singleton.preimage hf
      exact hZclosed.frontier_subset (hKfrontier hxK)
    have hec : e < f (u c) ^ 2 :=
      heη.trans_le (Finset.inf'_le level hcF)
    obtain ⟨y, hy, hylevel⟩ :=
      positive_squared_levels_on_short_segment f hf x (u c)
        hxeq (hunonzero c) hxu he hec
    exact ⟨y, by linarith, hylevel⟩
  · have hKempty : K = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hxK
      have hxcover : x ∈ ⋃ c ∈ F, U c := hFcover hxK
      have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
      simpa [hFempty] using hxcover
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hxK
    simp [hKempty] at hxK

/-- The finite-cover cutoff needed for the `close` clause, with radial
boundedness fixing a compact sublevel. -/
theorem exists_literalZeroRadial_close_cutoff
    {n : ℕ} (f : RealEuclideanFunction n) (hf : Continuous f)
    {ε₀ ε₁ : ℝ} (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x : RealEuclidean n,
        literalZeroVisibleRadialDenominator x ≤ ε₁⁻¹ →
        f x ^ 2 < η →
          ∃ z : RealEuclidean n,
            f z = 0 ∧ dist x z < ε₀ := by
  let K : Set (RealEuclidean n) :=
    {x | literalZeroVisibleRadialDenominator x ≤ ε₁⁻¹}
  have hK : IsCompact K :=
    isCompact_literalZeroVisibleRadialDenominator_sublevel ε₁⁻¹
  obtain ⟨η, hη, hclose⟩ :=
    exists_positive_level_close_to_zero_on_compact f hf K hK hε₀
  exact ⟨η, hη, fun x hx hlevel ↦ hclose x hx hlevel⟩

/-- The finite-cover cutoff needed for the `reach` clause before solving
the reciprocal radial equation. -/
theorem exists_literalZeroRadial_reach_cutoff
    {n : ℕ} (f : RealEuclideanFunction n) (hf : Continuous f)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x ∈ frontier {z : RealEuclidean n | f z = 0},
        ‖x‖ < ε₀⁻¹ →
          ∀ e : ℝ, 0 < e → e < η →
            ∃ y : RealEuclidean n,
              dist x y < ε₀ / 2 ∧ f y ^ 2 = e := by
  let K : Set (RealEuclidean n) :=
    frontier {z : RealEuclidean n | f z = 0} ∩
      Metric.closedBall 0 ε₀⁻¹
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : RealEuclidean n) ε₀⁻¹).inter_left
      isClosed_frontier
  have hfrontier : K ⊆ frontier {z : RealEuclidean n | f z = 0} :=
    inter_subset_left
  obtain ⟨η, hη, hreach⟩ :=
    exists_uniform_positive_level_near_frontier f hf K hK
      hfrontier (show 0 < ε₀ / 2 by positivity)
  refine ⟨η, hη, ?_⟩
  intro x hx hnorm e he heη
  apply hreach x ?_ e he heη
  refine ⟨hx, ?_⟩
  simpa only [Metric.mem_closedBall, dist_zero_right]
    using hnorm.le

/-! ## The first radial modulus bound -/

/-- A compact maximum on a slightly enlarged ball makes the reciprocal
first-level equation solvable after any displacement of size less than the
first error parameter. -/
theorem exists_literalZeroRadial_first_level_bound
    (n : ℕ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ {ε₁ : ℝ}, 0 < ε₁ → ε₁ < ρ →
        ∀ x y : RealEuclidean n,
          ‖x‖ < ε₀⁻¹ → dist x y < ε₀ →
            literalZeroVisibleRadialDenominator y < ε₁⁻¹ := by
  let R : ℝ := ε₀⁻¹ + ε₀ + 1
  have hR : 0 < R := by
    dsimp [R]
    have := inv_pos.mpr hε₀
    linarith
  let K : Set (RealEuclidean n) := Metric.closedBall 0 R
  obtain ⟨v, hvK, hmax⟩ :=
    (isCompact_closedBall (0 : RealEuclidean n) R).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self hR.le⟩
      continuous_literalZeroVisibleRadialDenominator.continuousOn
  let M : ℝ := literalZeroVisibleRadialDenominator v + 1
  have hM : 0 < M := by
    dsimp [M]
    linarith [literalZeroVisibleRadialDenominator_pos v]
  refine ⟨M⁻¹, inv_pos.mpr hM, ?_⟩
  intro ε₁ hε₁ hε₁ρ x y hxnorm hxydist
  have hmargin : M < ε₁⁻¹ := by
    simpa only [inv_inv] using
      (inv_lt_inv₀ (inv_pos.mpr hM) hε₁).mpr hε₁ρ
  have hnormtriangle : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    calc
      ‖y‖ = ‖(y - x) + x‖ := by simp
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
  have hnormy : ‖y‖ ≤ dist x y + ‖x‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hnormtriangle
  have hyK : y ∈ K := by
    have hynorm : ‖y‖ ≤ R := by
      dsimp [R]
      linarith
    simpa only [K, Metric.mem_closedBall, dist_zero_right]
      using hynorm
  have hvis : literalZeroVisibleRadialDenominator y ≤
      literalZeroVisibleRadialDenominator v := hmax hyK
  dsimp [M] at hmargin
  linarith

/-! ## Nested modulus assembly -/

/-- The two positive-level cutoffs can be joined before the first radial
parameter is chosen.  Both are valid for every positive pair `ε₀, ε₁`. -/
theorem exists_literalZeroRadial_joint_level_cutoff
    {n : ℕ} (f : RealEuclideanFunction n) (hf : Continuous f)
    {ε₀ ε₁ : ℝ} (hε₀ : 0 < ε₀) (hε₁ : 0 < ε₁) :
    ∃ η : ℝ, 0 < η ∧
      (∀ x : RealEuclidean n,
        literalZeroVisibleRadialDenominator x ≤ ε₁⁻¹ →
          f x ^ 2 < η →
            ∃ z : RealEuclidean n,
              f z = 0 ∧ dist x z < ε₀) ∧
      (∀ x ∈ frontier {z : RealEuclidean n | f z = 0},
        ‖x‖ < ε₀⁻¹ →
          ∀ e : ℝ, 0 < e → e < η →
            ∃ y : RealEuclidean n,
              dist x y < ε₀ / 2 ∧ f y ^ 2 = e) := by
  obtain ⟨ηclose, hηclose, hclose⟩ :=
    exists_literalZeroRadial_close_cutoff f hf hε₀ hε₁
  obtain ⟨ηreach, hηreach, hreach⟩ :=
    exists_literalZeroRadial_reach_cutoff f hf hε₀
  refine ⟨min ηclose ηreach, lt_min hηclose hηreach, ?_, ?_⟩
  · intro x hx hlevel
    exact hclose x hx (hlevel.trans_le (min_le_left _ _))
  · intro x hx hnorm e he hlevel
    exact hreach x hx hnorm e he
      (hlevel.trans_le (min_le_right _ _))

private noncomputable def literalZeroRadialFirstBound
    (n : ℕ) (ε₀ : ℝ) : ℝ :=
  if hε₀ : 0 < ε₀ then
    Classical.choose (exists_literalZeroRadial_first_level_bound n hε₀)
  else 1

private theorem literalZeroRadialFirstBound_pos
    (n : ℕ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    0 < literalZeroRadialFirstBound n ε₀ := by
  rw [literalZeroRadialFirstBound, dif_pos hε₀]
  exact (Classical.choose_spec
    (exists_literalZeroRadial_first_level_bound n hε₀)).1

private theorem literalZeroRadialFirstBound_margin
    (n : ℕ) {ε₀ ε₁ : ℝ} (hε₀ : 0 < ε₀)
    (hε₁ : 0 < ε₁)
    (hε₁bound : ε₁ < literalZeroRadialFirstBound n ε₀)
    (x y : RealEuclidean n)
    (hx : ‖x‖ < ε₀⁻¹) (hxy : dist x y < ε₀) :
    literalZeroVisibleRadialDenominator y < ε₁⁻¹ := by
  have hspec := (Classical.choose_spec
    (exists_literalZeroRadial_first_level_bound n hε₀)).2 (ε₁ := ε₁)
  apply hspec hε₁ (by
    simpa only [literalZeroRadialFirstBound, dif_pos hε₀]
      using hε₁bound) x y hx hxy

private noncomputable def literalZeroRadialLastBound
    {n : ℕ} (f : RealEuclideanFunction n) (hf : Continuous f)
    (coords : RealEuclidean 2) : ℝ :=
  if hpositive : ∀ i, 0 < coords i then
    Classical.choose
      (exists_literalZeroRadial_joint_level_cutoff f hf
        (hpositive 0) (hpositive 1))
  else 1

private theorem literalZeroRadialLastBound_pos
    {n : ℕ} (f : RealEuclideanFunction n) (hf : Continuous f)
    (coords : RealEuclidean 2)
    (hpositive : ∀ i, 0 < coords i) :
    0 < literalZeroRadialLastBound f hf coords := by
  rw [literalZeroRadialLastBound, dif_pos hpositive]
  exact (Classical.choose_spec
    (exists_literalZeroRadial_joint_level_cutoff f hf
      (hpositive 0) (hpositive 1))).1

private theorem literalZeroRadialLastBound_controls
    {n : ℕ} (f : RealEuclideanFunction n) (hf : Continuous f)
    (coords : RealEuclidean 2)
    (hpositive : ∀ i, 0 < coords i) :
    (∀ x : RealEuclidean n,
      literalZeroVisibleRadialDenominator x ≤ (coords 1)⁻¹ →
        f x ^ 2 < literalZeroRadialLastBound f hf coords →
          ∃ z : RealEuclidean n,
            f z = 0 ∧ dist x z < coords 0) ∧
    (∀ x ∈ frontier {z : RealEuclidean n | f z = 0},
      ‖x‖ < (coords 0)⁻¹ →
        ∀ e : ℝ, 0 < e →
          e < literalZeroRadialLastBound f hf coords →
            ∃ y : RealEuclidean n,
              dist x y < coords 0 / 2 ∧ f y ^ 2 = e) := by
  have hspec := (Classical.choose_spec
    (exists_literalZeroRadial_joint_level_cutoff f hf
      (hpositive 0) (hpositive 1))).2
  simpa only [literalZeroRadialLastBound, dif_pos hpositive]
    using hspec

/-- The nested order-two radial modulus, chosen from continuity and
compactness alone. -/
def literalZeroRadialModulus
    {n : ℕ} (f : RealEuclideanFunction n) (hf : Continuous f) :
    CharbonnelModulus 2 :=
  CharbonnelModulus.step
    (CharbonnelModulus.step
      (CharbonnelModulus.base 1 zero_lt_one)
      (fun coords : RealEuclidean 1 ↦
        literalZeroRadialFirstBound n (coords 0))
      (fun coords hpositive ↦
        literalZeroRadialFirstBound_pos n (hpositive 0)))
    (literalZeroRadialLastBound f hf)
    (literalZeroRadialLastBound_pos f hf)

/-- The constructed modulus satisfies the precise radial level controls
used by the certificate constructor in the preceding module. -/
theorem literalZeroRadialModulus_levelControls
    {n : ℕ} (f : RealEuclideanFunction n) (hf : Continuous f) :
    CharbonnelLiteralZeroRadialLevelControls f
      (literalZeroRadialModulus f hf) := by
  let μ := literalZeroRadialModulus f hf
  refine ⟨?_, ?_⟩
  · intro ε hε x hvisible hlevel
    have hprefix : ∀ i : Fin 2, 0 < (Fin.init ε) i := by
      intro i
      exact CharbonnelModulus.IsBounded.coord_pos hε i.castSucc
    have hcontrols := literalZeroRadialLastBound_controls f hf
      (Fin.init ε) hprefix
    have hlast : ε 2 < literalZeroRadialLastBound f hf
        (Fin.init ε) := by
      have hlastIndex : (Fin.last (1 + 1) : Fin 3) = 2 :=
        Fin.ext rfl
      simpa only [μ, literalZeroRadialModulus,
        CharbonnelModulus.IsBounded, Fin.init, hlastIndex] using hε.2.2
    have hlevel' : f x ^ 2 < literalZeroRadialLastBound f hf
        (Fin.init ε) := by rw [hlevel]; exact hlast
    exact hcontrols.1 x (by
      have honeIndex : (Fin.castSucc (1 : Fin 2) : Fin 3) = 1 :=
        Fin.ext rfl
      simpa only [Fin.init, honeIndex] using hvisible)
      hlevel'
  · intro ε hε x hx hnorm
    have hε₀ : 0 < ε 0 :=
      CharbonnelModulus.IsBounded.coord_pos hε 0
    have hε₁ : 0 < ε 1 :=
      CharbonnelModulus.IsBounded.coord_pos hε 1
    have hε₂ : 0 < ε 2 :=
      CharbonnelModulus.IsBounded.coord_pos hε 2
    have hprefix : ∀ i : Fin 2, 0 < (Fin.init ε) i := by
      intro i
      exact CharbonnelModulus.IsBounded.coord_pos hε i.castSucc
    have hcontrols := literalZeroRadialLastBound_controls f hf
      (Fin.init ε) hprefix
    have hfirst : ε 1 < literalZeroRadialFirstBound n (ε 0) := by
      have honeIndex : ((Fin.last (0 + 1) : Fin 2).castSucc : Fin 3) = 1 :=
        Fin.ext rfl
      have hzeroIndex : ((Fin.castSucc (0 : Fin 1)).castSucc : Fin 3) = 0 :=
        Fin.ext rfl
      simpa only [μ, literalZeroRadialModulus,
        CharbonnelModulus.IsBounded, Fin.init, honeIndex, hzeroIndex]
        using hε.1.2.2
    have hlast : ε 2 < literalZeroRadialLastBound f hf
        (Fin.init ε) := by
      have hlastIndex : (Fin.last (1 + 1) : Fin 3) = 2 :=
        Fin.ext rfl
      simpa only [μ, literalZeroRadialModulus,
        CharbonnelModulus.IsBounded, Fin.init, hlastIndex] using hε.2.2
    obtain ⟨y, hdistHalf, hlevel⟩ :=
      hcontrols.2 x hx hnorm (ε 2) hε₂ hlast
    have hdist : dist x y < ε 0 :=
      hdistHalf.trans (half_lt_self hε₀)
    have hmargin := literalZeroRadialFirstBound_margin n
      hε₀ hε₁ hfirst x y hnorm hdist
    exact ⟨y, hdist, hlevel, hmargin⟩

/-- Wilkie's literal-zero positive-level input follows from continuity of
all family members; no Sardian certificate, modulus, or level cutoff is
assumed. -/
theorem charbonnelSardianLiteralZeroRadialLevelInput_of_smooth
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    CharbonnelSardianLiteralZeroRadialLevelInput G := by
  intro n _hn f hf
  let hcont : Continuous f := (hsmooth n f hf).continuous
  exact ⟨literalZeroRadialModulus f hcont,
    literalZeroRadialModulus_levelControls f hcont⟩

/-- The complete literal-zero base constructor of the Sardian rank
induction, with just the already-present geometric and smooth family
hypotheses. -/
theorem charbonnelSardianLiteralZeroBaseInput_of_smoothGeometric
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    CharbonnelSardianLiteralZeroBaseInput G :=
  charbonnelSardianLiteralZeroBaseInput_of_radialLevels hG hsmooth
    (charbonnelSardianLiteralZeroRadialLevelInput_of_smooth hsmooth)

end AbelFormalization
