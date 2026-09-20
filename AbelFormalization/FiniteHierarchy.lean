import AbelFormalization.Hierarchy

/-!
# Separation for a finite cluster after logarithmic substitutions

The cluster has `h + 1` representatives, so the singleton case is included.
Integer distance is the actual infimum of distances to integers; the equivalent
lower bound against every integer is proved below. As in `Hierarchy.lean`, an
upper bound on the largest Abel time is unnecessary for these conclusions.
-/

namespace AbelFormalization

open Set Filter
open scoped Topology

/-- Distance from a real number to the integers, as defined in the manuscript. -/
noncomputable def integerDistance (x : ℝ) : ℝ :=
  sInf (Set.range (fun z : ℤ => |x - (z : ℝ)|))

/-- The infimum formulation is equivalent to the lower bound against every
integer; no choice of a nearest integer is assumed. -/
theorem le_integerDistance_iff {d x : ℝ} :
    d ≤ integerDistance x ↔ ∀ z : ℤ, d ≤ |x - (z : ℝ)| := by
  have hbd : BddBelow (Set.range (fun z : ℤ => |x - (z : ℝ)|)) :=
    ⟨0, by rintro y ⟨z, rfl⟩; exact abs_nonneg _⟩
  have hne : (Set.range (fun z : ℤ => |x - (z : ℝ)|)).Nonempty := ⟨_, 0, rfl⟩
  constructor
  · intro hd z
    exact hd.trans (csInf_le hbd (Set.mem_range_self z))
  · intro hd
    exact le_csInf hne (by rintro y ⟨z, rfl⟩; exact hd z)

private theorem finiteHierarchy_tendsto_sub (d : ℝ) :
    Tendsto (fun s : ℝ => s - d) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b + d)] with s hs
  linarith

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- A fixed number of logarithmic substitutions is an integer shift of Abel time. -/
theorem L_iterate_inverse (s : ℝ) (k : ℕ) :
    L^[k] (inverse A s) = inverse A (s - k) := by
  apply (hA.inverse_eq_iff.mpr ⟨L_iterate_pos (hA.inverse_pos s) k, ?_⟩).symm
  rw [hA.abel_L_iterate (hA.inverse_pos s) k, hA.apply_inverse]

/-- A strict comparison sufficient for the logarithmic denominator in the
finite-cluster conclusion. -/
theorem log_inverse_lt_previous (s : ℝ) :
    Real.log (inverse A s) < inverse A (s - 1) := by
  have hv : inverse A s = Real.exp (inverse A (s - 1)) - 1 := by
    simpa only [sub_add_cancel] using hA.inverse_add_one (s - 1)
  calc
    Real.log (inverse A s) < Real.log (Real.exp (inverse A (s - 1))) :=
      Real.log_lt_log (hA.inverse_pos s) (by rw [hv]; linarith)
    _ = inverse A (s - 1) := Real.log_exp _

omit hA in
private theorem finite_cluster_time_tendsto {h : ℕ}
    (t : ℕ → ℝ) (a : Fin (h + 1) → ℕ → ℝ) {D : ℝ}
    (ht : Tendsto t atTop atTop)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => a i n))
    (hlower : ∀ᶠ n in atTop, t n - D ≤ a (Fin.last h) n)
    (i : Fin (h + 1)) (k : ℕ) :
    Tendsto (fun n => a i n - k) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ ((finiteHierarchy_tendsto_sub (D + k)).comp ht)
  filter_upwards [horder, hlower] with n hnO hnL
  have hi := hnO.antitone (Fin.le_last i)
  change t n - (D + k) ≤ a i n - k
  linarith

/-- Adjacent representatives in a separated finite cluster have divergent ratios
after any fixed number of logarithmic substitutions. -/
theorem finite_cluster_adjacent_ratios {h : ℕ}
    (t : ℕ → ℝ) (a : Fin (h + 1) → ℕ → ℝ) (k : ℕ) {D N c : ℝ}
    (hc : 0 < c) (hN : D + k + 5 ≤ N) (ht : Tendsto t atTop atTop)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => a i n))
    (hlower : ∀ᶠ n in atTop, t n - D ≤ a (Fin.last h) n)
    (hsep : ∀ᶠ n in atTop, ∀ i j : Fin (h + 1), i ≠ j →
      c / inverse A (t n - N) ≤ integerDistance (a i n - a j n)) :
    ∀ i : Fin h, Tendsto (fun n =>
      L^[k] (inverse A (a i.castSucc n)) / L^[k] (inverse A (a i.succ n))) atTop atTop := by
  intro i
  have hij : i.castSucc < i.succ := by simp
  have ho : ∀ᶠ n in atTop,
      t n - (D + k) ≤ a i.succ n - k ∧ a i.succ n - k < a i.castSucc n - k := by
    filter_upwards [horder, hlower] with n hnO hnL
    have hmin := hnO.antitone (Fin.le_last i.succ)
    have hlt := hnO hij
    constructor <;> linarith
  have hg : ∀ᶠ n in atTop, c / inverse A (t n - N) ≤
      (a i.castSucc n - k) - (a i.succ n - k) := by
    filter_upwards [horder, hsep] with n hnO hnS
    have hb := le_integerDistance_iff.mp (hnS i.castSucc i.succ (ne_of_lt hij)) 0
    have hdiff : 0 < a i.castSucc n - a i.succ n := sub_pos.mpr (hnO hij)
    simp only [Int.cast_zero, sub_zero, abs_of_pos hdiff] at hb
    calc
      c / inverse A (t n - N) ≤ a i.castSucc n - a i.succ n := hb
      _ = (a i.castSucc n - k) - (a i.succ n - k) := by ring
  have hr := hA.hierarchy_separation t (fun n => a i.castSucc n - k)
    (fun n => a i.succ n - k) (D := D + k) (N := N) hc (by linarith) ht ho hg 1
  simpa only [hA.L_iterate_inverse, Real.rpow_one] using hr

/-- The smallest representative dominates the logarithm of the largest, also
when the cluster consists of a single representative. -/
theorem finite_cluster_smallest_div_log_largest {h : ℕ}
    (t : ℕ → ℝ) (a : Fin (h + 1) → ℕ → ℝ) (k : ℕ) {D N c : ℝ}
    (hc : 0 < c) (hN : D + k + 5 ≤ N) (ht : Tendsto t atTop atTop)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => a i n))
    (hlower : ∀ᶠ n in atTop, t n - D ≤ a (Fin.last h) n)
    (hwidth : ∀ᶠ n in atTop, a 0 n - a (Fin.last h) n < 1)
    (hsep : ∀ᶠ n in atTop, ∀ i j : Fin (h + 1), i ≠ j →
      c / inverse A (t n - N) ≤ integerDistance (a i n - a j n)) :
    Tendsto (fun n => L^[k] (inverse A (a (Fin.last h) n)) /
      Real.log (L^[k] (inverse A (a 0 n)))) atTop atTop := by
  have hwrap : ∀ᶠ n in atTop, c / inverse A (t n - N) ≤
      1 - (a 0 n - a (Fin.last h) n) := by
    by_cases heq : (0 : Fin (h + 1)) = Fin.last h
    · have hden := (hA.inverse_tendsto_atTop.comp
        ((finiteHierarchy_tendsto_sub N).comp ht)).eventually (eventually_ge_atTop c)
      filter_upwards [hden] with n hn
      rw [heq, sub_self, sub_zero]
      exact (div_le_one (hA.inverse_pos _)).mpr hn
    · filter_upwards [hsep, hwidth] with n hnS hnW
      have hb := le_integerDistance_iff.mp (hnS 0 (Fin.last h) heq) 1
      have hneg : a 0 n - a (Fin.last h) n - 1 < 0 := by linarith
      simp only [Int.cast_one, abs_of_neg hneg] at hb
      linarith
  have ho : ∀ᶠ n in atTop, t n - (D + k + 1) ≤ a 0 n - k - 1 ∧
      a 0 n - k - 1 < a (Fin.last h) n - k := by
    filter_upwards [horder, hlower, hwidth] with n hnO hnL hnW
    have hmin := hnO.antitone (Fin.le_last (0 : Fin (h + 1)))
    constructor <;> linarith
  have hg : ∀ᶠ n in atTop, c / inverse A (t n - N) ≤
      (a (Fin.last h) n - k) - (a 0 n - k - 1) := by
    filter_upwards [hwrap] with n hn
    convert hn using 1
    ring
  have hr := hA.hierarchy_separation t (fun n => a (Fin.last h) n - k)
    (fun n => a 0 n - k - 1) (D := D + k + 1) (N := N) hc (by linarith) ht ho hg 1
  simp only [Real.rpow_one] at hr
  have ha0 := finite_cluster_time_tendsto t a ht horder hlower 0 k
  apply tendsto_atTop_mono' atTop _ hr
  filter_upwards [ha0.eventually (eventually_gt_atTop 0)] with n hn
  simp only [hA.L_iterate_inverse]
  exact div_le_div_of_nonneg_left (hA.inverse_pos _).le
    (Real.log_pos (hA.one_lt_inverse hn)) (hA.log_inverse_lt_previous _).le

/-- Both conclusions of the finite-cluster separation lemma. The coordinate
order is decreasing, with index `0` largest and `Fin.last h` smallest. -/
theorem finite_cluster_hierarchy {h : ℕ}
    (t : ℕ → ℝ) (a : Fin (h + 1) → ℕ → ℝ) (k : ℕ) {D N c : ℝ}
    (hc : 0 < c) (hN : D + k + 5 ≤ N) (ht : Tendsto t atTop atTop)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => a i n))
    (hlower : ∀ᶠ n in atTop, t n - D ≤ a (Fin.last h) n)
    (hwidth : ∀ᶠ n in atTop, a 0 n - a (Fin.last h) n < 1)
    (hsep : ∀ᶠ n in atTop, ∀ i j : Fin (h + 1), i ≠ j →
      c / inverse A (t n - N) ≤ integerDistance (a i n - a j n)) :
    (∀ i : Fin h, Tendsto (fun n =>
      L^[k] (inverse A (a i.castSucc n)) / L^[k] (inverse A (a i.succ n))) atTop atTop) ∧
    Tendsto (fun n => L^[k] (inverse A (a (Fin.last h) n)) /
      Real.log (L^[k] (inverse A (a 0 n)))) atTop atTop :=
  ⟨hA.finite_cluster_adjacent_ratios t a k hc hN ht horder hlower hsep,
    hA.finite_cluster_smallest_div_log_largest t a k hc hN ht horder hlower hwidth hsep⟩

end IsAbel

end AbelFormalization
