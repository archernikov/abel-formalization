import AbelFormalization.FiniteHierarchy
import Mathlib.Order.Filter.Cofinite

/-!
# Finite Abel hierarchies along an arbitrary filter

The maintained hierarchy theorems use sequences indexed by `ℕ` and the full
filter `atTop`.  Their proofs only use the source through eventual statements
and convergence of the common time parameter.  This file records the same
arguments for an arbitrary source type and filter, without changing any of
the numerical hypotheses.

The last section gives the specialization to
`atTop ⊓ Filter.principal (Λ ∩ Γ N)`.  The restricted filter is allowed to be
bottom.  In particular, none of the hierarchy theorems silently assumes that
the restricted set is infinite.
-/

namespace AbelFormalization

open Set Filter
open scoped Topology

universe u

private theorem filteredHierarchy_tendsto_sub (d : ℝ) :
    Tendsto (fun s : ℝ => s - d) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b + d)] with s hs
  linarith

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- The double-logarithm gap diverges along any source filter satisfying the
same lower-time and separation estimates as the sequential theorem. -/
theorem hierarchy_logLog_gap_tendsto_filter
    {X : Type u} (l : Filter X) (t a b : X → ℝ) {D N c : ℝ}
    (hc : 0 < c) (hN : D + 4 ≤ N)
    (ht : Tendsto t l atTop)
    (horder : ∀ᶠ x in l, t x - D ≤ b x ∧ b x < a x)
    (hgap : ∀ᶠ x in l, c / inverse A (t x - N) ≤ a x - b x) :
    Tendsto (fun x => Real.log (Real.log (inverse A (a x))) -
      Real.log (Real.log (inverse A (b x)))) l atTop := by
  have hb : Tendsto b l atTop :=
    tendsto_atTop_mono' l (horder.mono fun _ h => h.1)
      ((filteredHierarchy_tendsto_sub D).comp ht)
  have hscale : Tendsto (fun x =>
      c * (inverse A (t x - D - 2) / inverse A (t x - N))) l atTop := by
    have h := ((hA.inverse_shift_div_tendsto_atTop
      (d := N - D - 2) (by linarith)).comp
        ((filteredHierarchy_tendsto_sub N).comp ht)).const_mul_atTop hc
    convert h using 1
    funext x
    simp only [Function.comp_apply]
    rw [show t x - N + (N - D - 2) = t x - D - 2 by ring]
  obtain ⟨R, hR⟩ := hA.logLog_inverse_increment_lower_bound
  apply tendsto_atTop_mono' l _ hscale
  filter_upwards [horder, hgap, hb.eventually (eventually_ge_atTop R)] with x hx hg hbR
  have hi : inverse A (t x - D - 2) ≤ inverse A (b x - 2) :=
    hA.inverse_strictMono.monotone (sub_le_sub_right hx.1 2)
  calc
    c * (inverse A (t x - D - 2) / inverse A (t x - N)) =
        (c / inverse A (t x - N)) * inverse A (t x - D - 2) := by ring
    _ ≤ (a x - b x) * inverse A (t x - D - 2) :=
      mul_le_mul_of_nonneg_right hg (hA.inverse_pos _).le
    _ ≤ (a x - b x) * inverse A (b x - 2) :=
      mul_le_mul_of_nonneg_left hi (sub_pos.mpr hx.2).le
    _ ≤ Real.log (Real.log (inverse A (a x))) -
        Real.log (Real.log (inverse A (b x))) := hR (a x) (b x) hbR hx.2

/-- The hierarchy separation estimate along an arbitrary source filter.  As
in the sequential theorem, every real exponent `q` is allowed. -/
theorem hierarchy_separation_filter
    {X : Type u} (l : Filter X) (t a b : X → ℝ) {D N c : ℝ}
    (hc : 0 < c) (hN : D + 4 ≤ N)
    (ht : Tendsto t l atTop)
    (horder : ∀ᶠ x in l, t x - D ≤ b x ∧ b x < a x)
    (hgap : ∀ᶠ x in l, c / inverse A (t x - N) ≤ a x - b x)
    (q : ℝ) :
    Tendsto (fun x => inverse A (a x) / (inverse A (b x)) ^ q) l atTop := by
  have hb : Tendsto b l atTop :=
    tendsto_atTop_mono' l (horder.mono fun _ h => h.1)
      ((filteredHierarchy_tendsto_sub D).comp ht)
  have ha : Tendsto a l atTop :=
    tendsto_atTop_mono' l (horder.mono fun _ h => h.2.le) hb
  have hla : Tendsto (fun x => Real.log (inverse A (a x))) l atTop :=
    Real.tendsto_log_atTop.comp (hA.inverse_tendsto_atTop.comp ha)
  have hlb : Tendsto (fun x => Real.log (inverse A (b x))) l atTop :=
    Real.tendsto_log_atTop.comp (hA.inverse_tendsto_atTop.comp hb)
  have hratio : Tendsto (fun x =>
      Real.log (inverse A (a x)) / Real.log (inverse A (b x))) l atTop := by
    have h := Real.tendsto_exp_atTop.comp
      (hA.hierarchy_logLog_gap_tendsto_filter l t a b hc hN ht horder hgap)
    apply h.congr'
    filter_upwards [hla.eventually (eventually_gt_atTop 0),
      hlb.eventually (eventually_gt_atTop 0)] with x hxA hxB
    simp only [Function.comp_def, Real.exp_sub, Real.exp_log hxA, Real.exp_log hxB]
  have hdiff : Tendsto (fun x =>
      Real.log (inverse A (a x)) - q * Real.log (inverse A (b x))) l atTop := by
    apply tendsto_atTop_mono' l _ hlb
    filter_upwards [hratio.eventually (eventually_ge_atTop (q + 1)),
      hlb.eventually (eventually_gt_atTop 0)] with x hx hxB
    have h := (le_div_iff₀ hxB).mp hx
    nlinarith
  have hlog : Tendsto (fun x =>
      Real.log (inverse A (a x) / (inverse A (b x)) ^ q)) l atTop := by
    convert hdiff using 1
    funext x
    rw [Real.log_div (ne_of_gt (hA.inverse_pos _))
      (ne_of_gt (Real.rpow_pos_of_pos (hA.inverse_pos _) q)),
      Real.log_rpow (hA.inverse_pos _) q]
  apply (Real.tendsto_exp_atTop.comp hlog).congr'
  filter_upwards [] with x
  exact Real.exp_log (div_pos (hA.inverse_pos _)
    (Real.rpow_pos_of_pos (hA.inverse_pos _) q))

omit hA in
private theorem finite_cluster_time_tendsto_filter
    {X : Type u} {h : ℕ} (l : Filter X)
    (t : X → ℝ) (a : Fin (h + 1) → X → ℝ) {D : ℝ}
    (ht : Tendsto t l atTop)
    (horder : ∀ᶠ x in l, StrictAnti (fun i => a i x))
    (hlower : ∀ᶠ x in l, t x - D ≤ a (Fin.last h) x)
    (i : Fin (h + 1)) (k : ℕ) :
    Tendsto (fun x => a i x - k) l atTop := by
  apply tendsto_atTop_mono' l _
    ((filteredHierarchy_tendsto_sub (D + k)).comp ht)
  filter_upwards [horder, hlower] with x hxO hxL
  have hi := hxO.antitone (Fin.le_last i)
  change t x - (D + k) ≤ a i x - k
  linarith

/-- Adjacent representatives in a separated finite cluster have divergent
ratios after any fixed number of logarithmic substitutions, along any source
filter. -/
theorem finite_cluster_adjacent_ratios_filter
    {X : Type u} {h : ℕ} (l : Filter X)
    (t : X → ℝ) (a : Fin (h + 1) → X → ℝ) (k : ℕ) {D N c : ℝ}
    (hc : 0 < c) (hN : D + k + 5 ≤ N) (ht : Tendsto t l atTop)
    (horder : ∀ᶠ x in l, StrictAnti (fun i => a i x))
    (hlower : ∀ᶠ x in l, t x - D ≤ a (Fin.last h) x)
    (hsep : ∀ᶠ x in l, ∀ i j : Fin (h + 1), i ≠ j →
      c / inverse A (t x - N) ≤ integerDistance (a i x - a j x)) :
    ∀ i : Fin h, Tendsto (fun x =>
      L^[k] (inverse A (a i.castSucc x)) /
        L^[k] (inverse A (a i.succ x))) l atTop := by
  intro i
  have hij : i.castSucc < i.succ := by simp
  have ho : ∀ᶠ x in l,
      t x - (D + k) ≤ a i.succ x - k ∧
        a i.succ x - k < a i.castSucc x - k := by
    filter_upwards [horder, hlower] with x hxO hxL
    have hmin := hxO.antitone (Fin.le_last i.succ)
    have hlt := hxO hij
    constructor <;> linarith
  have hg : ∀ᶠ x in l, c / inverse A (t x - N) ≤
      (a i.castSucc x - k) - (a i.succ x - k) := by
    filter_upwards [horder, hsep] with x hxO hxS
    have hb := le_integerDistance_iff.mp
      (hxS i.castSucc i.succ (ne_of_lt hij)) 0
    have hdiff : 0 < a i.castSucc x - a i.succ x := sub_pos.mpr (hxO hij)
    simp only [Int.cast_zero, sub_zero, abs_of_pos hdiff] at hb
    calc
      c / inverse A (t x - N) ≤ a i.castSucc x - a i.succ x := hb
      _ = (a i.castSucc x - k) - (a i.succ x - k) := by ring
  have hr := hA.hierarchy_separation_filter l t
    (fun x => a i.castSucc x - k) (fun x => a i.succ x - k)
    (D := D + k) (N := N) hc (by linarith) ht ho hg 1
  simpa only [hA.L_iterate_inverse, Real.rpow_one] using hr

/-- The smallest representative dominates the logarithm of the largest along
an arbitrary source filter, including for a singleton cluster. -/
theorem finite_cluster_smallest_div_log_largest_filter
    {X : Type u} {h : ℕ} (l : Filter X)
    (t : X → ℝ) (a : Fin (h + 1) → X → ℝ) (k : ℕ) {D N c : ℝ}
    (hc : 0 < c) (hN : D + k + 5 ≤ N) (ht : Tendsto t l atTop)
    (horder : ∀ᶠ x in l, StrictAnti (fun i => a i x))
    (hlower : ∀ᶠ x in l, t x - D ≤ a (Fin.last h) x)
    (hwidth : ∀ᶠ x in l, a 0 x - a (Fin.last h) x < 1)
    (hsep : ∀ᶠ x in l, ∀ i j : Fin (h + 1), i ≠ j →
      c / inverse A (t x - N) ≤ integerDistance (a i x - a j x)) :
    Tendsto (fun x => L^[k] (inverse A (a (Fin.last h) x)) /
      Real.log (L^[k] (inverse A (a 0 x)))) l atTop := by
  have hwrap : ∀ᶠ x in l, c / inverse A (t x - N) ≤
      1 - (a 0 x - a (Fin.last h) x) := by
    by_cases heq : (0 : Fin (h + 1)) = Fin.last h
    · have hden := (hA.inverse_tendsto_atTop.comp
        ((filteredHierarchy_tendsto_sub N).comp ht)).eventually
          (eventually_ge_atTop c)
      filter_upwards [hden] with x hx
      rw [heq, sub_self, sub_zero]
      exact (div_le_one (hA.inverse_pos _)).mpr hx
    · filter_upwards [hsep, hwidth] with x hxS hxW
      have hb := le_integerDistance_iff.mp (hxS 0 (Fin.last h) heq) 1
      have hneg : a 0 x - a (Fin.last h) x - 1 < 0 := by linarith
      simp only [Int.cast_one, abs_of_neg hneg] at hb
      linarith
  have ho : ∀ᶠ x in l,
      t x - (D + k + 1) ≤ a 0 x - k - 1 ∧
        a 0 x - k - 1 < a (Fin.last h) x - k := by
    filter_upwards [horder, hlower, hwidth] with x hxO hxL hxW
    have hmin := hxO.antitone (Fin.le_last (0 : Fin (h + 1)))
    constructor <;> linarith
  have hg : ∀ᶠ x in l, c / inverse A (t x - N) ≤
      (a (Fin.last h) x - k) - (a 0 x - k - 1) := by
    filter_upwards [hwrap] with x hx
    convert hx using 1
    ring
  have hr := hA.hierarchy_separation_filter l t
    (fun x => a (Fin.last h) x - k) (fun x => a 0 x - k - 1)
    (D := D + k + 1) (N := N) hc (by linarith) ht ho hg 1
  simp only [Real.rpow_one] at hr
  have ha0 := finite_cluster_time_tendsto_filter l t a ht horder hlower 0 k
  apply tendsto_atTop_mono' l _ hr
  filter_upwards [ha0.eventually (eventually_gt_atTop 0)] with x hx
  simp only [hA.L_iterate_inverse]
  exact div_le_div_of_nonneg_left (hA.inverse_pos _).le
    (Real.log_pos (hA.one_lt_inverse hx)) (hA.log_inverse_lt_previous _).le

/-- Both conclusions of the finite-cluster separation lemma along an
arbitrary source filter.  Index `0` is largest and `Fin.last h` is smallest. -/
theorem finite_cluster_hierarchy_filter
    {X : Type u} {h : ℕ} (l : Filter X)
    (t : X → ℝ) (a : Fin (h + 1) → X → ℝ) (k : ℕ) {D N c : ℝ}
    (hc : 0 < c) (hN : D + k + 5 ≤ N) (ht : Tendsto t l atTop)
    (horder : ∀ᶠ x in l, StrictAnti (fun i => a i x))
    (hlower : ∀ᶠ x in l, t x - D ≤ a (Fin.last h) x)
    (hwidth : ∀ᶠ x in l, a 0 x - a (Fin.last h) x < 1)
    (hsep : ∀ᶠ x in l, ∀ i j : Fin (h + 1), i ≠ j →
      c / inverse A (t x - N) ≤ integerDistance (a i x - a j x)) :
    (∀ i : Fin h, Tendsto (fun x =>
      L^[k] (inverse A (a i.castSucc x)) /
        L^[k] (inverse A (a i.succ x))) l atTop) ∧
    Tendsto (fun x => L^[k] (inverse A (a (Fin.last h) x)) /
      Real.log (L^[k] (inverse A (a 0 x)))) l atTop :=
  ⟨hA.finite_cluster_adjacent_ratios_filter l t a k hc hN ht horder hlower hsep,
    hA.finite_cluster_smallest_div_log_largest_filter
      l t a k hc hN ht horder hlower hwidth hsep⟩

end IsAbel

/-! ## Restricted tails of natural numbers -/

/-- The tail filter restricted to a set of natural numbers. -/
def restrictedAtTop (s : Set ℕ) : Filter ℕ :=
  atTop ⊓ Filter.principal s

/-- Eventual statements on a restricted tail are exactly tail statements
conditional on membership in the restricting set. -/
theorem eventually_restrictedAtTop_iff {s : Set ℕ} {p : ℕ → Prop} :
    (∀ᶠ n in restrictedAtTop s, p n) ↔
      ∀ᶠ n in atTop, n ∈ s → p n := by
  exact eventually_inf_principal

/-- Threshold form of `eventually_restrictedAtTop_iff`. -/
theorem eventually_restrictedAtTop_iff_exists {s : Set ℕ} {p : ℕ → Prop} :
    (∀ᶠ n in restrictedAtTop s, p n) ↔
      ∃ n₀, ∀ n, n₀ ≤ n → n ∈ s → p n := by
  rw [eventually_restrictedAtTop_iff, eventually_atTop]

/-- Convergence on the full tail remains true after restricting the tail. -/
theorem tendsto_restrictedAtTop_of_tendsto_atTop
    {Y : Type*} {f : ℕ → Y} {l : Filter Y} (hf : Tendsto f atTop l)
    (s : Set ℕ) : Tendsto f (restrictedAtTop s) l :=
  hf.mono_left inf_le_left

/-- A restricted natural tail is nontrivial exactly when its restricting set
is infinite.  The hierarchy results themselves do not require this condition. -/
theorem restrictedAtTop_neBot_iff {s : Set ℕ} :
    (restrictedAtTop s).NeBot ↔ s.Infinite := by
  simpa only [restrictedAtTop, ← Nat.cofinite_eq_atTop] using
    (cofinite_inf_principal_neBot_iff (s := s))

/-- Equivalently, restriction to a finite set gives the bottom filter. -/
@[simp]
theorem restrictedAtTop_eq_bot_iff {s : Set ℕ} :
    restrictedAtTop s = ⊥ ↔ s.Finite := by
  rw [← not_neBot, restrictedAtTop_neBot_iff, Set.not_infinite]

/-- The filter used for a paper-style set `Λ ∩ Γ N`. -/
def separatedRestriction (Λ : Set ℕ) (Γ : ℕ → Set ℕ) (N : ℕ) : Filter ℕ :=
  restrictedAtTop (Λ ∩ Γ N)

@[simp]
theorem eventually_separatedRestriction_iff
    {Λ : Set ℕ} {Γ : ℕ → Set ℕ} {N : ℕ} {p : ℕ → Prop} :
    (∀ᶠ n in separatedRestriction Λ Γ N, p n) ↔
      ∀ᶠ n in atTop, n ∈ Λ ∩ Γ N → p n := by
  exact eventually_restrictedAtTop_iff

@[simp]
theorem separatedRestriction_neBot_iff
    {Λ : Set ℕ} {Γ : ℕ → Set ℕ} {N : ℕ} :
    (separatedRestriction Λ Γ N).NeBot ↔ (Λ ∩ Γ N).Infinite := by
  exact restrictedAtTop_neBot_iff

@[simp]
theorem separatedRestriction_eq_bot_iff
    {Λ : Set ℕ} {Γ : ℕ → Set ℕ} {N : ℕ} :
    separatedRestriction Λ Γ N = ⊥ ↔ (Λ ∩ Γ N).Finite := by
  exact restrictedAtTop_eq_bot_iff

/-- Full-tail convergence supplies the common-time convergence hypothesis on
every paper-style separated restriction. -/
theorem tendsto_separatedRestriction_of_tendsto_atTop
    {Y : Type*} {f : ℕ → Y} {l : Filter Y} (hf : Tendsto f atTop l)
    (Λ : Set ℕ) (Γ : ℕ → Set ℕ) (N : ℕ) :
    Tendsto f (separatedRestriction Λ Γ N) l :=
  tendsto_restrictedAtTop_of_tendsto_atTop hf (Λ ∩ Γ N)

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- Direct finite-cluster wrapper on the paper's restricted filter
`atTop ⊓ principal (Λ ∩ Γ N₀)`.  No infinitude hypothesis is imposed. -/
theorem finite_cluster_hierarchy_separatedRestriction {h : ℕ}
    (Λ : Set ℕ) (Γ : ℕ → Set ℕ) (N₀ : ℕ)
    (t : ℕ → ℝ) (a : Fin (h + 1) → ℕ → ℝ) (k : ℕ) {D N c : ℝ}
    (hc : 0 < c) (hN : D + k + 5 ≤ N)
    (ht : Tendsto t (separatedRestriction Λ Γ N₀) atTop)
    (horder : ∀ᶠ n in separatedRestriction Λ Γ N₀,
      StrictAnti (fun i => a i n))
    (hlower : ∀ᶠ n in separatedRestriction Λ Γ N₀,
      t n - D ≤ a (Fin.last h) n)
    (hwidth : ∀ᶠ n in separatedRestriction Λ Γ N₀,
      a 0 n - a (Fin.last h) n < 1)
    (hsep : ∀ᶠ n in separatedRestriction Λ Γ N₀,
      ∀ i j : Fin (h + 1), i ≠ j →
        c / inverse A (t n - N) ≤ integerDistance (a i n - a j n)) :
    (∀ i : Fin h, Tendsto (fun n =>
      L^[k] (inverse A (a i.castSucc n)) /
        L^[k] (inverse A (a i.succ n)))
          (separatedRestriction Λ Γ N₀) atTop) ∧
    Tendsto (fun n => L^[k] (inverse A (a (Fin.last h) n)) /
      Real.log (L^[k] (inverse A (a 0 n))))
        (separatedRestriction Λ Γ N₀) atTop :=
  hA.finite_cluster_hierarchy_filter (separatedRestriction Λ Γ N₀)
    t a k hc hN ht horder hlower hwidth hsep

end IsAbel

end AbelFormalization
