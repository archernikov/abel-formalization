import AbelFormalization.Stirling
import AbelFormalization.OrbitBounds

/-! # Decay of every positive-order derivative at infinity

A finite sum of absolute values of derivatives contracts on sufficiently large
exponential steps. The all-order transport formula and compact orbit estimates
then give decay on the entire real tail.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace AbelFormalization

def positiveJetNorm (A : ℝ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 r, |iteratedDeriv j A x|

def jetCoefficientBound (r : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 r,
    ∑ j ∈ Finset.range (n + 1), |(signedStirling n j : ℝ)|

theorem positiveJetNorm_nonneg (A : ℝ → ℝ) (r : ℕ) (x : ℝ) :
    0 ≤ positiveJetNorm A r x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_iteratedDeriv_le_positiveJetNorm {A : ℝ → ℝ} {r j : ℕ}
    (hj : 1 ≤ j) (hjr : j ≤ r) (x : ℝ) :
    |iteratedDeriv j A x| ≤ positiveJetNorm A r x := by
  unfold positiveJetNorm
  exact Finset.single_le_sum (f := fun k => |iteratedDeriv k A x|)
    (fun _ _ => abs_nonneg _) (Finset.mem_Icc.mpr ⟨hj, hjr⟩)

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem abs_iteratedDeriv_transport_bound {r n : ℕ} (hn : 1 ≤ n) (hnr : n ≤ r)
    {u : ℝ} (hu : 0 < u) :
    |iteratedDeriv n A (E u)| ≤ Real.exp (-u) *
      ((∑ j ∈ Finset.range (n + 1), |(signedStirling n j : ℝ)|) * positiveJetNorm A r u) := by
  have hs : |∑ j ∈ Finset.range (n + 1),
      (signedStirling n j : ℝ) * iteratedDeriv j A u| ≤
      (∑ j ∈ Finset.range (n + 1), |(signedStirling n j : ℝ)|) *
        positiveJetNorm A r u := by
    calc
      |∑ j ∈ Finset.range (n + 1), (signedStirling n j : ℝ) * iteratedDeriv j A u|
          ≤ ∑ j ∈ Finset.range (n + 1),
            |(signedStirling n j : ℝ) * iteratedDeriv j A u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (n + 1),
          |(signedStirling n j : ℝ)| * positiveJetNorm A r u := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hj0 : j = 0
        · subst j
          simp [signedStirling_zero hn]
        · rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact abs_iteratedDeriv_le_positiveJetNorm (by omega)
            (le_trans (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj) hnr) u
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hnr' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have he : Real.exp (-((n : ℝ) * u)) ≤ Real.exp (-u) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hnr' hu.le
    nlinarith
  rw [hA.iteratedDeriv_transport n hn hu, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul he hs (abs_nonneg _) (Real.exp_pos _).le

theorem positiveJetNorm_step (r : ℕ) {u : ℝ} (hu : 0 < u) :
    positiveJetNorm A r (E u) ≤
      Real.exp (-u) * (jetCoefficientBound r * positiveJetNorm A r u) := by
  change (∑ n ∈ Finset.Icc 1 r, |iteratedDeriv n A (E u)|) ≤
    Real.exp (-u) * (jetCoefficientBound r * positiveJetNorm A r u)
  calc
    (∑ n ∈ Finset.Icc 1 r, |iteratedDeriv n A (E u)|)
        ≤ ∑ n ∈ Finset.Icc 1 r, Real.exp (-u) *
          ((∑ j ∈ Finset.range (n + 1), |(signedStirling n j : ℝ)|) *
            positiveJetNorm A r u) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hA.abs_iteratedDeriv_transport_bound (Finset.mem_Icc.mp hn).1
        (Finset.mem_Icc.mp hn).2 hu
    _ = _ := by
      unfold jetCoefficientBound
      symm
      rw [Finset.sum_mul, Finset.mul_sum]

theorem positiveJetNorm_continuousOn (r : ℕ) :
    ContinuousOn (positiveJetNorm A r) (Ioi 0) := by
  unfold positiveJetNorm
  apply continuousOn_finsetSum
  intro j _
  apply ContinuousOn.abs
  rw [iteratedDeriv_eq_iterate]
  exact (hA.analytic.iterated_deriv j).continuousOn

theorem tendsto_positiveJetNorm_atTop (r : ℕ) :
    Tendsto (positiveJetNorm A r) atTop (𝓝 0) := by
  have he : Tendsto (fun u : ℝ => Real.exp (-u) * jetCoefficientBound r)
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const
      (jetCoefficientBound r)
  obtain ⟨R, hR⟩ := eventually_atTop.1
    (he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  let U : ℝ := max 1 R
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply hA.tendsto_zero_of_orbit_contraction (q := (1 / 2 : ℝ)) (U := U)
    hU (by norm_num) (by norm_num)
  · exact (hA.positiveJetNorm_continuousOn r).mono fun x hx => hU.trans_le hx.1
  · exact fun x _ => positiveJetNorm_nonneg A r x
  · intro x hx
    have hp := hR x ((le_max_right _ _).trans hx)
    calc
      positiveJetNorm A r (E x)
          ≤ (Real.exp (-x) * jetCoefficientBound r) * positiveJetNorm A r x := by
        simpa only [mul_assoc] using hA.positiveJetNorm_step r (hU.trans_le hx)
      _ ≤ (1 / 2 : ℝ) * positiveJetNorm A r x :=
        mul_le_mul_of_nonneg_right hp.le (positiveJetNorm_nonneg A r x)

/-- Every positive-order derivative tends to zero at positive infinity. -/
theorem tendsto_iteratedDeriv_atTop (r : ℕ) (hr : 1 ≤ r) :
    Tendsto (iteratedDeriv r A) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  exact squeeze_zero (fun _ => abs_nonneg _)
    (fun x => abs_iteratedDeriv_le_positiveJetNorm hr le_rfl x)
    (hA.tendsto_positiveJetNorm_atTop r)

end IsAbel
end AbelFormalization
