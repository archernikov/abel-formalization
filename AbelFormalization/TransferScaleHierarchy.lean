import AbelFormalization.LexicographicInitialForms
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay

/-!
# Quantitative domination for lexicographically separated scales

This file isolates the asymptotic step in the quantitative-reduction lemma.
A positive lexicographic integer weight has a positive first nonzero
coordinate.  On a decreasing hierarchy of positive scales, that coordinate
dominates all later coordinates.  Consequently the corresponding exponential
factor is smaller than every fixed inverse power of the ambient scale.
-/

noncomputable section

namespace AbelFormalization

open Filter Finset
open scoped Topology

/-- The real scalar product of an integer weight vector with a real scale
vector. -/
def lexicographicDot {h : ℕ} (ν : Fin h → ℤ) (u : Fin h → ℝ) : ℝ :=
  ∑ i, (ν i : ℝ) * u i

@[simp]
theorem lexicographicDot_zero_dim (ν : Fin 0 → ℤ) (u : Fin 0 → ℝ) :
    lexicographicDot ν u = 0 := by
  simp [lexicographicDot]

@[simp]
theorem lexicographicDot_cons {h : ℕ} (a : ℤ) (ν : Fin h → ℤ)
    (x : ℝ) (u : Fin h → ℝ) :
    lexicographicDot (Fin.cons a ν) (Fin.cons x u) =
      (a : ℝ) * x + lexicographicDot ν u := by
  simp [lexicographicDot, Fin.sum_univ_succ]

/-- A coordinatewise nonnegative vector bounded by `U` gives the elementary
finite `ℓ1` bound for its integer-weighted scalar product. -/
theorem abs_lexicographicDot_le {h : ℕ} (ν : Fin h → ℤ) (u : Fin h → ℝ)
    (U : ℝ) (hu0 : ∀ i, 0 ≤ u i) (huU : ∀ i, u i ≤ U) :
    |lexicographicDot ν u| ≤ (∑ i, |(ν i : ℝ)|) * U := by
  calc
    |lexicographicDot ν u| ≤ ∑ i, |(ν i : ℝ) * u i| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |(ν i : ℝ)| * u i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hu0 i)]
    _ ≤ ∑ i, |(ν i : ℝ)| * U := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (huU i) (abs_nonneg _)
    _ = (∑ i, |(ν i : ℝ)|) * U := by rw [Finset.sum_mul]

/-- Under the scale assumptions of the quantitative-reduction lemma, every
positive lexicographic integer weight has scalar product much larger than
`log R`.  The index order is the paper's decreasing order: coordinate zero is
the largest scale. -/
theorem tendsto_lexicographicDot_div_log_atTop :
    ∀ {h : ℕ} (ν : Fin (h + 1) → ℤ) (u : Fin (h + 1) → ℕ → ℝ)
      (R : ℕ → ℝ),
      0 < toLex ν →
      (∀ᶠ n in atTop, StrictAnti (fun i => u i n)) →
      (∀ᶠ n in atTop, 0 < u (Fin.last h) n) →
      (∀ᶠ n in atTop, 2 ≤ R n) →
      (∀ i : Fin h, Tendsto (fun n =>
        u i.castSucc n / u i.succ n) atTop atTop) →
      Tendsto (fun n => u (Fin.last h) n / Real.log (R n)) atTop atTop →
      Tendsto (fun n =>
        lexicographicDot ν (fun i => u i n) / Real.log (R n)) atTop atTop := by
  intro h
  induction h with
  | zero =>
      intro ν u R hν _horder _hpos _hR _hratios hscale
      obtain ⟨i, _hibefore, hipos⟩ := hν
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hν0 : (0 : ℝ) < (ν 0 : ℝ) := by exact_mod_cast hipos
      have hlim := hscale.const_mul_atTop hν0
      convert hlim using 1
      funext n
      simp [lexicographicDot, mul_div_assoc]
  | succ h ih =>
      intro ν u R hν horder hpos hR hratios hscale
      obtain ⟨i, hibefore, hipos⟩ := hν
      cases i using Fin.cases with
      | zero =>
          have hν0 : (0 : ℝ) < (ν 0 : ℝ) := by exact_mod_cast hipos
          let C : ℝ := ∑ j : Fin (h + 1), |(ν j.succ : ℝ)|
          have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
          have hratio := (hratios (0 : Fin (h + 1))).eventually_ge_atTop (2 * C)
          apply tendsto_atTop_mono' atTop _
            (hscale.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
          filter_upwards [horder, hpos, hR, hratio] with n hnorder hnpos hnR hnratio
          have hnlast0 : 0 < u (Fin.last (h + 1)) n := hnpos
          have htail0 : ∀ j : Fin (h + 1), 0 ≤ u j.succ n := by
            intro j
            exact (hnlast0.trans_le (hnorder.antitone (Fin.le_last j.succ))).le
          have htail_le : ∀ j : Fin (h + 1), u j.succ n ≤ u 1 n := by
            intro j
            exact hnorder.antitone (Fin.succ_le_succ_iff.mpr (Fin.zero_le j))
          have hu1 : 0 < u 1 n := hnlast0.trans_le
            (hnorder.antitone (Fin.le_last (1 : Fin (h + 2))))
          have hu0 : 0 < u 0 n := hu1.trans (hnorder (by simp : (0 : Fin (h + 2)) < 1))
          have htailabs :
              |lexicographicDot (Fin.tail ν) (fun j : Fin (h + 1) => u j.succ n)| ≤
                C * u 1 n := by
            change |lexicographicDot (Fin.tail ν) (fun j : Fin (h + 1) => u j.succ n)| ≤
              (∑ j : Fin (h + 1), |((Fin.tail ν) j : ℝ)|) * u 1 n
            exact
              abs_lexicographicDot_le (Fin.tail ν)
                (fun j : Fin (h + 1) => u j.succ n) (u 1 n) htail0 htail_le
          have hratio' : (2 * C) * u 1 n ≤ u 0 n := by
            have hratio0 : 2 * C ≤ u 0 n / u 1 n := by simpa using hnratio
            exact (le_div_iff₀ hu1).mp hratio0
          have hCu : C * u 1 n ≤ u 0 n / 2 := by nlinarith
          have htailneg : -C * u 1 n ≤
              lexicographicDot (Fin.tail ν) (fun j : Fin (h + 1) => u j.succ n) := by
            have := neg_le_of_abs_le htailabs
            simpa only [neg_mul] using this
          have hνone : (1 : ℝ) ≤ (ν 0 : ℝ) := by
            exact_mod_cast (Int.add_one_le_iff.mpr (by exact_mod_cast hν0 : (0 : ℤ) < ν 0))
          have hdot : u 0 n / 2 ≤ lexicographicDot ν (fun j => u j n) := by
            rw [show ν = Fin.cons (ν 0) (Fin.tail ν) from (Fin.cons_self_tail ν).symm,
              show (fun j => u j n) = Fin.cons (u 0 n)
                (fun j : Fin (h + 1) => u j.succ n) from
                  (Fin.cons_self_tail (fun j => u j n)).symm,
              lexicographicDot_cons]
            have hhead : u 0 n ≤ (ν 0 : ℝ) * u 0 n := by
              simpa only [one_mul] using mul_le_mul_of_nonneg_right hνone hu0.le
            nlinarith
          have hlast_le : u (Fin.last (h + 1)) n ≤ u 0 n :=
            hnorder.antitone (Fin.zero_le _)
          have hlog : 0 < Real.log (R n) :=
            Real.log_pos (lt_of_lt_of_le one_lt_two hnR)
          calc
            (1 / 2 : ℝ) * (u (Fin.last (h + 1)) n / Real.log (R n)) =
                ((1 / 2 : ℝ) * u (Fin.last (h + 1)) n) / Real.log (R n) := by ring
            _ ≤ lexicographicDot ν (fun j => u j n) / Real.log (R n) := by
              exact (div_le_div_iff_of_pos_right hlog).2 (by nlinarith)
      | succ i =>
          have hν0 : ν 0 = 0 := by
            symm
            exact hibefore 0 (Fin.succ_pos i)
          have htaillex : 0 < toLex (Fin.tail ν) := by
            refine ⟨i, ?_, ?_⟩
            · intro j hj
              change (0 : ℤ) = ν j.succ
              exact hibefore j.succ (Fin.succ_lt_succ_iff.mpr hj)
            · change (0 : ℤ) < ν i.succ
              exact hipos
          have htailorder : ∀ᶠ n in atTop,
              StrictAnti (fun j : Fin (h + 1) => u j.succ n) := by
            filter_upwards [horder] with n hn
            intro j k hjk
            exact hn (Fin.succ_lt_succ_iff.mpr hjk)
          have htailpos : ∀ᶠ n in atTop,
              0 < u (Fin.last (h + 1)) n := hpos
          have htailratios : ∀ j : Fin h, Tendsto (fun n =>
              u j.succ.castSucc n / u j.succ.succ n) atTop atTop := by
            intro j
            exact hratios j.succ
          have htaillimit := ih (Fin.tail ν) (fun j n => u j.succ n) R
            htaillex htailorder htailpos hR (by
              intro j
              convert htailratios j using 1 <;> funext n <;> rfl) (by simpa using hscale)
          apply htaillimit.congr'
          filter_upwards with n
          congr 1
          symm
          calc
            lexicographicDot ν (fun j => u j n) =
                lexicographicDot (Fin.cons (ν 0) (Fin.tail ν))
                  (Fin.cons (u 0 n) (fun j : Fin (h + 1) => u j.succ n)) := by
                    congr 1
                    · exact (Fin.cons_self_tail ν).symm
                    · exact (Fin.cons_self_tail (fun j => u j n)).symm
            _ = (ν 0 : ℝ) * u 0 n +
                lexicographicDot (Fin.tail ν) (fun j : Fin (h + 1) => u j.succ n) :=
              lexicographicDot_cons _ _ _ _
            _ = lexicographicDot (Fin.tail ν)
                (fun j : Fin (h + 1) => u j.succ n) := by simp [hν0]

/-- Subtracting a fixed real constant preserves divergence to positive
infinity. -/
private theorem tendsto_sub_const_atTop {f : ℕ → ℝ}
    (hf : Tendsto f atTop atTop) (c : ℝ) :
    Tendsto (fun n => f n - c) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [hf.eventually_ge_atTop (b + c)] with n hn
  linarith

/-- If `d / log R` tends to infinity and `R` stays at least two, then
`d - M log R` tends to infinity for every fixed real exponent `M`. -/
theorem tendsto_sub_mul_log_atTop {d R : ℕ → ℝ}
    (hd : Tendsto (fun n => d n / Real.log (R n)) atTop atTop)
    (hR : ∀ᶠ n in atTop, 2 ≤ R n) (M : ℝ) :
    Tendsto (fun n => d n - M * Real.log (R n)) atTop atTop := by
  let q : ℕ → ℝ := fun n => d n / Real.log (R n)
  have hq : Tendsto q atTop atTop := hd
  have hqM : Tendsto (fun n => q n - M) atTop atTop :=
    tendsto_sub_const_atTop hq M
  have hbase := hqM.const_mul_atTop (Real.log_pos one_lt_two)
  apply tendsto_atTop_mono' atTop _ hbase
  filter_upwards [hR, hqM.eventually_ge_atTop 0] with n hnR hnq
  have hRpos : 0 < R n := zero_lt_one.trans (one_lt_two.trans_le hnR)
  have hlogpos : 0 < Real.log (R n) := Real.log_pos (one_lt_two.trans_le hnR)
  have hlogle : Real.log 2 ≤ Real.log (R n) := Real.log_le_log (by norm_num) hnR
  have hmul : Real.log 2 * (q n - M) ≤ Real.log (R n) * (q n - M) :=
    mul_le_mul_of_nonneg_right hlogle hnq
  calc
    Real.log 2 * (q n - M) ≤ Real.log (R n) * (q n - M) := hmul
    _ = d n - M * Real.log (R n) := by
      dsimp only [q]
      field_simp

/-- The discarded exponential attached to a positive lexicographic weight
is little-o of every fixed inverse real power of `R`. -/
theorem lexicographicExponential_isLittleO_rpow {h : ℕ}
    (ν : Fin (h + 1) → ℤ) (u : Fin (h + 1) → ℕ → ℝ)
    (R : ℕ → ℝ)
    (hν : 0 < toLex ν)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => u i n))
    (hpos : ∀ᶠ n in atTop, 0 < u (Fin.last h) n)
    (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hratios : ∀ i : Fin h, Tendsto (fun n =>
      u i.castSucc n / u i.succ n) atTop atTop)
    (hscale : Tendsto (fun n =>
      u (Fin.last h) n / Real.log (R n)) atTop atTop)
    (M : ℝ) :
    (fun n => Real.exp (-lexicographicDot ν (fun i => u i n))) =o[atTop]
      (fun n => R n ^ (-M : ℝ)) := by
  have hdot := tendsto_lexicographicDot_div_log_atTop ν u R hν horder hpos hR
    hratios hscale
  have hgap := tendsto_sub_mul_log_atTop hdot hR M
  have hexp :
      (fun n => Real.exp (-lexicographicDot ν (fun i => u i n))) =o[atTop]
        (fun n => Real.exp (-M * Real.log (R n))) := by
    rw [Real.isLittleO_exp_comp_exp_comp]
    convert hgap using 1
    funext n
    ring
  apply hexp.congr' (Filter.EventuallyEq.rfl) ?_
  filter_upwards [hR] with n hnR
  rw [Real.rpow_def_of_pos (zero_lt_one.trans (one_lt_two.trans_le hnR))]
  congr 1
  ring

/-- Standard mathlib formulation of the same conclusion: the discarded
exponential has superpolynomial decay in the scale `R`. -/
theorem lexicographicExponential_superpolynomialDecay {h : ℕ}
    (ν : Fin (h + 1) → ℤ) (u : Fin (h + 1) → ℕ → ℝ)
    (R : ℕ → ℝ)
    (hν : 0 < toLex ν)
    (horder : ∀ᶠ n in atTop, StrictAnti (fun i => u i n))
    (hpos : ∀ᶠ n in atTop, 0 < u (Fin.last h) n)
    (hR : ∀ᶠ n in atTop, 2 ≤ R n)
    (hratios : ∀ i : Fin h, Tendsto (fun n =>
      u i.castSucc n / u i.succ n) atTop atTop)
    (hscale : Tendsto (fun n =>
      u (Fin.last h) n / Real.log (R n)) atTop atTop) :
    Asymptotics.SuperpolynomialDecay atTop R
      (fun n => Real.exp (-lexicographicDot ν (fun i => u i n))) := by
  have hdot := tendsto_lexicographicDot_div_log_atTop ν u R hν horder hpos hR
    hratios hscale
  intro M
  have hgap := tendsto_sub_mul_log_atTop hdot hR (M : ℝ)
  have hexp := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hgap)
  apply hexp.congr'
  filter_upwards [hR] with n hnR
  have hRpos : 0 < R n := zero_lt_one.trans (one_lt_two.trans_le hnR)
  symm
  rw [← Real.exp_log hRpos, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  simp only [Function.comp_apply]
  ring

end AbelFormalization
