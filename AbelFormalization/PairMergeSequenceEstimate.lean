import AbelFormalization.LowerDerivativeBounds
import AbelFormalization.FiniteHierarchy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scratch: the quantitative sequence estimate in the pair-merging lemma

Write `T = inverse A`.  The manuscript chooses Abel-time coordinates

`sigma = a_j - K`, `delta = a_i - a_j - k`

and then defines

`xi = T (sigma + delta) - T sigma`.

The near-integer estimate bounds `|delta|` by `1 / T (t-N)`.  Once both
endpoints lie below `t-N-1`, the eventual estimate

`T' z <= (T z)^(3/2)`

and the mean-value theorem give

`|xi| <= T(t-N-1)^(3/2) / T(t-N)`.

This file proves that estimate and its convergence to zero.  It deliberately
separates the analytic argument from the finite-pigeonhole step which fixes
the pair, its orientation, and the nearest integer `k` after subsequencing.
-/

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

private theorem tendsto_sub_const_atTop (c : ℝ) :
    Tendsto (fun x : ℝ => x - c) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b + c)] with x hx
  linarith

private theorem pairScale_factorization {A : ℝ → ℝ} (hA : IsAbel A)
    (s : ℝ) :
    ((inverse A (s - 1)) ^ (3 / 2 : ℝ) *
          Real.exp (-(inverse A (s - 1)))) /
        (E (inverse A (s - 1)) / Real.exp (inverse A (s - 1))) =
      (inverse A (s - 1)) ^ (3 / 2 : ℝ) / inverse A s := by
  have hrec : inverse A s = E (inverse A (s - 1)) := by
    simpa only [sub_add_cancel, E] using hA.inverse_add_one (s - 1)
  rw [hrec, Real.exp_neg]
  rw [← div_eq_mul_inv]
  exact div_div_div_cancel_right₀ (Real.exp_ne_zero _) _ _

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- The final scalar factor in the manuscript's pair estimate tends to zero.
The proof uses

`T(s) = E(T(s-1))`

and factors the quotient as

`(T(s-1)^(3/2) * exp (-T(s-1))) / (E(T(s-1)) / exp(T(s-1)))`.
-/
theorem tendsto_pairMerge_scale :
    Tendsto (fun s : ℝ =>
      (inverse A (s - 1)) ^ (3 / 2 : ℝ) / inverse A s)
      atTop (𝓝 0) := by
  let q : ℝ → ℝ := fun s => inverse A (s - 1)
  have hq : Tendsto q atTop atTop :=
    hA.inverse_tendsto_atTop.comp (tendsto_sub_const_atTop 1)
  have hnum : Tendsto (fun s : ℝ =>
      q s ^ (3 / 2 : ℝ) * Real.exp (-q s)) atTop (𝓝 0) :=
    by
      simpa [Function.comp_def] using
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
          (3 / 2 : ℝ) 1 zero_lt_one).comp hq
  have hden : Tendsto (fun s : ℝ =>
      E (q s) / Real.exp (q s)) atTop (𝓝 1) :=
    tendsto_E_div_exp.comp hq
  have hquot := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hquot0 : Tendsto
      ((fun s : ℝ => q s ^ (3 / 2 : ℝ) * Real.exp (-q s)) /
        (fun s : ℝ => E (q s) / Real.exp (q s))) atTop (𝓝 0) := by
    simpa using hquot
  apply hquot0.congr'
  filter_upwards [] with s
  change ((inverse A (s - 1)) ^ (3 / 2 : ℝ) *
        Real.exp (-(inverse A (s - 1)))) /
      (E (inverse A (s - 1)) / Real.exp (inverse A (s - 1))) =
    (inverse A (s - 1)) ^ (3 / 2 : ℝ) / inverse A s
  exact pairScale_factorization hA s

/-- A uniform mean-value estimate for a short inverse-Abel increment.

The number `R` is independent of `sigma`, `delta`, and the comparison point
`v`.  The hypotheses simply say that the whole unordered interval from
`sigma` to `sigma + delta` is contained in `[R,v]`.
-/
theorem exists_pairMerge_inverse_increment_bound :
    ∃ R : ℝ, ∀ {sigma delta v : ℝ},
      R ≤ min sigma (sigma + delta) →
      max sigma (sigma + delta) ≤ v →
      |inverse A (sigma + delta) - inverse A sigma| ≤
        (inverse A v) ^ (3 / 2 : ℝ) * |delta| := by
  obtain ⟨R, hR⟩ :=
    eventually_atTop.mp hA.eventually_inverse_deriv_le_rpow_three_halves
  refine ⟨R, ?_⟩
  intro sigma delta v hlower hupper
  have hdiff : ∀ z ∈ Set.uIcc sigma (sigma + delta),
      DifferentiableAt ℝ (inverse A) z := by
    intro z hz
    exact (hA.inverse_hasDerivAt z).differentiableAt
  have hderiv : ∀ z ∈ Set.uIcc sigma (sigma + delta),
      ‖deriv (inverse A) z‖ ≤ (inverse A v) ^ (3 / 2 : ℝ) := by
    intro z hz
    change min sigma (sigma + delta) ≤ z ∧
      z ≤ max sigma (sigma + delta) at hz
    have hzR : R ≤ z := hlower.trans hz.1
    have hzv : z ≤ v := hz.2.trans hupper
    rw [Real.norm_eq_abs, abs_of_pos (hA.inverse_deriv_pos z)]
    exact (hR z hzR).trans
      (Real.rpow_le_rpow (hA.inverse_pos z).le
        (hA.inverse_strictMono.monotone hzv) (by norm_num))
  have hmv := (convex_uIcc sigma (sigma + delta)).norm_image_sub_le_of_norm_deriv_le
    hdiff hderiv (left_mem_uIcc : sigma ∈ Set.uIcc sigma (sigma + delta))
      (right_mem_uIcc : sigma + delta ∈ Set.uIcc sigma (sigma + delta))
  simpa only [Real.norm_eq_abs, add_sub_cancel_left] using hmv

/-- The near-integer gap tends to zero because its denominator tends to
infinity.  This small lemma also supplies the lower-endpoint control needed
when applying the mean-value estimate to a moving interval.
-/
theorem pairMerge_gap_tendsto_zero
    {X : Type*} {l : Filter X} (t delta : X → ℝ) (N : ℝ)
    (ht : Tendsto t l atTop)
    (hnear : ∀ᶠ x in l,
      |delta x| ≤ (inverse A (t x - N))⁻¹) :
    Tendsto delta l (𝓝 0) := by
  have htime : Tendsto (fun x => t x - N) l atTop :=
    (tendsto_sub_const_atTop N).comp ht
  have hden : Tendsto (fun x => inverse A (t x - N)) l atTop :=
    hA.inverse_tendsto_atTop.comp htime
  have hinv : Tendsto (fun x => (inverse A (t x - N))⁻¹) l (𝓝 0) :=
    hden.inv_tendsto_atTop
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  exact squeeze_zero' (Eventually.of_forall fun x => abs_nonneg (delta x)) hnear hinv

/-- Quantitative form of the sequence-side pair estimate.  The endpoint
hypothesis is slightly weaker than the manuscript's eventual bound by
`t-N-2`; `t-N-1` already suffices.
-/
theorem eventually_pairMerge_inverse_increment_le
    {X : Type*} {l : Filter X}
    (t sigma delta : X → ℝ) (N : ℝ)
    (ht : Tendsto t l atTop)
    (hsigma : Tendsto sigma l atTop)
    (hnear : ∀ᶠ x in l,
      |delta x| ≤ (inverse A (t x - N))⁻¹)
    (hupper : ∀ᶠ x in l,
      max (sigma x) (sigma x + delta x) ≤ t x - N - 1) :
    ∀ᶠ x in l,
      |inverse A (sigma x + delta x) - inverse A (sigma x)| ≤
        (inverse A (t x - N - 1)) ^ (3 / 2 : ℝ) /
          inverse A (t x - N) := by
  obtain ⟨R, hR⟩ := hA.exists_pairMerge_inverse_increment_bound
  have hdelta : Tendsto delta l (𝓝 0) :=
    hA.pairMerge_gap_tendsto_zero t delta N ht hnear
  have hsum : Tendsto (fun x => sigma x + delta x) l atTop :=
    hsigma.atTop_add hdelta
  filter_upwards [hsigma.eventually (eventually_ge_atTop R),
    hsum.eventually (eventually_ge_atTop R), hnear, hupper]
      with x hsigmaR hsumR hgap htop
  have hmv := hR (le_min hsigmaR hsumR) htop
  calc
    |inverse A (sigma x + delta x) - inverse A (sigma x)|
        ≤ (inverse A (t x - N - 1)) ^ (3 / 2 : ℝ) * |delta x| := hmv
    _ ≤ (inverse A (t x - N - 1)) ^ (3 / 2 : ℝ) *
        (inverse A (t x - N))⁻¹ :=
      mul_le_mul_of_nonneg_left hgap
        (Real.rpow_nonneg (hA.inverse_pos (t x - N - 1)).le _)
    _ = (inverse A (t x - N - 1)) ^ (3 / 2 : ℝ) /
        inverse A (t x - N) :=
      (div_eq_mul_inv _ _).symm

/-- Reusable analytic core of the manuscript's pair-merging argument.

It assumes precisely the facts available after the finite pair and nearest
integer have been fixed: `t` and `sigma` diverge, the near-integer gap has
the prescribed reciprocal bound, and the two moving endpoints eventually
lie below `t-N-1`.
-/
theorem pairMerge_inverse_increment_tendsto_zero
    {X : Type*} {l : Filter X}
    (t sigma delta : X → ℝ) (N : ℝ)
    (ht : Tendsto t l atTop)
    (hsigma : Tendsto sigma l atTop)
    (hnear : ∀ᶠ x in l,
      |delta x| ≤ (inverse A (t x - N))⁻¹)
    (hupper : ∀ᶠ x in l,
      max (sigma x) (sigma x + delta x) ≤ t x - N - 1) :
    Tendsto (fun x =>
      inverse A (sigma x + delta x) - inverse A (sigma x)) l (𝓝 0) := by
  have htime : Tendsto (fun x => t x - N) l atTop :=
    (tendsto_sub_const_atTop N).comp ht
  have hscale : Tendsto (fun x =>
      (inverse A (t x - N - 1)) ^ (3 / 2 : ℝ) /
        inverse A (t x - N)) l (𝓝 0) :=
    hA.tendsto_pairMerge_scale.comp htime
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  exact squeeze_zero'
    (Eventually.of_forall fun x => abs_nonneg
      (inverse A (sigma x + delta x) - inverse A (sigma x)))
    (hA.eventually_pairMerge_inverse_increment_le
      t sigma delta N ht hsigma hnear hupper)
    hscale

/-! ## Manuscript-shaped specialization -/

/-- The bounded Abel-time error after fixing an oriented pair and an integer
`k`. -/
def pairMergeDelta (aI aJ : ℕ → ℝ) (k : ℕ) : ℕ → ℝ :=
  fun n => aI n - aJ n - (k : ℝ)

/-- The shifted lower Abel time used for the surviving representative. -/
def pairMergeSigma (aJ : ℕ → ℝ) (K : ℕ) : ℕ → ℝ :=
  fun n => aJ n - (K : ℝ)

/-- The new bounded coordinate in inverse-Abel notation. -/
def pairMergeXi (A : ℝ → ℝ) (aI aJ : ℕ → ℝ)
    (K k : ℕ) : ℕ → ℝ :=
  fun n => inverse A (aI n - ((K + k : ℕ) : ℝ)) -
    inverse A (aJ n - (K : ℝ))

/-- Pointwise identification of the inverse-Abel coordinate with the
iterated-logarithm coordinate used in the manuscript. -/
theorem pairMergeXi_apply_eq_L_iterates
    (sI sJ : ℕ → ℝ) (K k n : ℕ)
    (hsI : 0 < sI n) (hsJ : 0 < sJ n) :
    pairMergeXi A (fun r => A (sI r)) (fun r => A (sJ r)) K k n =
      L^[K + k] (sI n) - L^[K] (sJ n) := by
  have hi := hA.L_iterate_inverse (A (sI n)) (K + k)
  have hj := hA.L_iterate_inverse (A (sJ n)) K
  rw [hA.inverse_apply hsI] at hi
  rw [hA.inverse_apply hsJ] at hj
  dsimp only [pairMergeXi]
  rw [← hi, ← hj]

/-- Direct specialization of `pairMerge_inverse_increment_tendsto_zero` to
the paper's fixed data.  Take `D = ceil C` and `K = N + D + 3`.

The two cluster-upper-bound hypotheses follow from the definition of
`t` as the minimum and the width bound by `C`.  No convergence hypothesis
on `aI` is needed: convergence of `aJ` and the reciprocal gap already force
the second shifted endpoint to diverge.
-/
theorem pairMergeXi_tendsto_zero_of_cluster_upper
    (t aI aJ : ℕ → ℝ) (N D K k : ℕ)
    (hK : K = N + D + 3)
    (ht : Tendsto t atTop atTop)
    (haJ : Tendsto aJ atTop atTop)
    (haIUpper : ∀ᶠ n in atTop, aI n ≤ t n + (D : ℝ))
    (haJUpper : ∀ᶠ n in atTop, aJ n ≤ t n + (D : ℝ))
    (hnear : ∀ᶠ n in atTop,
      |pairMergeDelta aI aJ k n| <
        (inverse A (t n - (N : ℝ)))⁻¹) :
    Tendsto (pairMergeXi A aI aJ K k) atTop (𝓝 0) := by
  have hK' : (K : ℝ) = (N : ℝ) + (D : ℝ) + 3 := by
    exact_mod_cast hK
  have hsigma : Tendsto (pairMergeSigma aJ K) atTop atTop := by
    exact (tendsto_sub_const_atTop (K : ℝ)).comp haJ
  have hnear' : ∀ᶠ n in atTop,
      |pairMergeDelta aI aJ k n| ≤
        (inverse A (t n - (N : ℝ)))⁻¹ :=
    hnear.mono fun _ hn => hn.le
  have hupper : ∀ᶠ n in atTop,
      max (pairMergeSigma aJ K n)
          (pairMergeSigma aJ K n + pairMergeDelta aI aJ k n) ≤
        t n - (N : ℝ) - 1 := by
    filter_upwards [haIUpper, haJUpper] with n hi hj
    apply max_le
    · dsimp only [pairMergeSigma]
      linarith
    · dsimp only [pairMergeSigma, pairMergeDelta]
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
  have hxi := hA.pairMerge_inverse_increment_tendsto_zero
    t (pairMergeSigma aJ K) (pairMergeDelta aI aJ k) (N : ℝ)
      ht hsigma hnear' hupper
  apply hxi.congr'
  filter_upwards [] with n
  dsimp only [pairMergeXi, pairMergeSigma, pairMergeDelta]
  have harg :
      (aJ n - (K : ℝ)) + (aI n - aJ n - (k : ℝ)) =
        aI n - ((K + k : ℕ) : ℝ) := by
    push_cast
    ring
  rw [harg]

/-- Manuscript-facing version of the quantitative result.  Its output is
literally the new logarithmic coordinate

`L^[K+k](sI n) - L^[K](sJ n)`.

The assumptions `sI → ∞` and `sJ → ∞` are exactly the representative
divergence assumptions in `lem:pair`.  They provide eventual positivity,
while `sJ → ∞` also implies `A(sJ) → ∞`.
-/
theorem pairMerge_logCoordinate_tendsto_zero
    (t sI sJ : ℕ → ℝ) (N D K k : ℕ)
    (hK : K = N + D + 3)
    (ht : Tendsto t atTop atTop)
    (hsI : Tendsto sI atTop atTop)
    (hsJ : Tendsto sJ atTop atTop)
    (haIUpper : ∀ᶠ n in atTop, A (sI n) ≤ t n + (D : ℝ))
    (haJUpper : ∀ᶠ n in atTop, A (sJ n) ≤ t n + (D : ℝ))
    (hnear : ∀ᶠ n in atTop,
      |pairMergeDelta (fun r => A (sI r)) (fun r => A (sJ r)) k n| <
        (inverse A (t n - (N : ℝ)))⁻¹) :
    Tendsto (fun n => L^[K + k] (sI n) - L^[K] (sJ n))
      atTop (𝓝 0) := by
  have haJ : Tendsto (fun n => A (sJ n)) atTop atTop :=
    hA.tendsto_atTop.comp hsJ
  have hxi := hA.pairMergeXi_tendsto_zero_of_cluster_upper
    t (fun n => A (sI n)) (fun n => A (sJ n)) N D K k
      hK ht haJ haIUpper haJUpper hnear
  apply hxi.congr'
  filter_upwards [hsI.eventually (eventually_gt_atTop 0),
    hsJ.eventually (eventually_gt_atTop 0)] with n hi hj
  exact hA.pairMergeXi_apply_eq_L_iterates sI sJ K k n hi hj

/-- The two asymptotic coordinate conclusions used in the pair-merging
lemma: the surviving coordinate tends to infinity and the appended bounded
coordinate tends to zero. -/
theorem pairMergeCoordinates_tendsto
    (t aI aJ : ℕ → ℝ) (N D K k : ℕ)
    (hK : K = N + D + 3)
    (ht : Tendsto t atTop atTop)
    (haJ : Tendsto aJ atTop atTop)
    (haIUpper : ∀ᶠ n in atTop, aI n ≤ t n + (D : ℝ))
    (haJUpper : ∀ᶠ n in atTop, aJ n ≤ t n + (D : ℝ))
    (hnear : ∀ᶠ n in atTop,
      |pairMergeDelta aI aJ k n| <
        (inverse A (t n - (N : ℝ)))⁻¹) :
    Tendsto (fun n => inverse A (pairMergeSigma aJ K n)) atTop atTop ∧
      Tendsto (pairMergeXi A aI aJ K k) atTop (𝓝 0) := by
  constructor
  · exact hA.inverse_tendsto_atTop.comp
      ((tendsto_sub_const_atTop (K : ℝ)).comp haJ)
  · exact hA.pairMergeXi_tendsto_zero_of_cluster_upper
      t aI aJ N D K k hK ht haJ haIUpper haJUpper hnear

end IsAbel
end AbelFormalization
