import AbelFormalization.ComplexLog

/-!
# Iterated logarithms on disks along a real orbit

The radius of a sufficiently small disk does not increase at any logarithmic
step. The statements hold for every iterate count, as required when that count
depends on the real center tending to infinity.
-/

noncomputable section

namespace AbelFormalization

open Set Function

theorem L_E (x : ℝ) : L (E x) = x := by
  simp [L, E]

theorem complexL_iterate_ofReal {x : ℝ} (hx : 0 < x) (n : ℕ) :
    complexL^[n] (x : ℂ) = (L^[n] x : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ_apply', ih, complexL_ofReal (by
        have := L_iterate_pos hx n
        linarith), iterate_succ_apply']

theorem complexL_E (x : ℝ) : complexL (E x : ℂ) = (x : ℂ) := by
  rw [complexL_ofReal (by simp [E]; positivity), L_E]

theorem complexL_mapsTo_ball_of_radius_le {c r : ℝ}
    (hr : 0 < r) (hc : r ≤ c) :
    MapsTo complexL (Metric.ball (c : ℂ) r) (Metric.ball (L c : ℂ) r) := by
  have hd : r < 1 + c := by linarith
  have hm := complexL_mapsTo_ball hr hd
  rw [complexL_ofReal (by linarith)] at hm
  apply hm.mono_right
  apply Metric.ball_subset_ball
  apply (div_le_iff₀ (sub_pos.mpr hd)).mpr
  nlinarith

/-- The full return to the fundamental disk is analytic and stays in that
disk, regardless of the number of iterates. -/
theorem complexL_iterate_disk {u ρ : ℝ} (hρ : 0 < ρ) (hu : ρ ≤ u) (n : ℕ) :
    AnalyticOnNhd ℂ (complexL^[n]) (Metric.ball (E^[n] u : ℂ) ρ) ∧
      MapsTo (complexL^[n]) (Metric.ball (E^[n] u : ℂ) ρ) (Metric.ball (u : ℂ) ρ) := by
  have hup : 0 < u := hρ.trans_le hu
  induction n with
  | zero =>
      constructor
      · exact analyticOnNhd_id
      · exact mapsTo_id _
  | succ n ih =>
      have hnc : ρ ≤ E^[n] u := hu.trans
        (by simpa using (E_iterate_strictMono hup).monotone (Nat.zero_le n))
      have hec : ρ ≤ E (E^[n] u) := hnc.trans (lt_E (E_iterate_pos hup n)).le
      have hm := complexL_mapsTo_ball_of_radius_le hρ hec
      rw [L_E] at hm
      have ha := complexL_analyticOnNhd_ball (by linarith : ρ < 1 + E (E^[n] u))
      constructor
      · simpa only [iterate_succ, iterate_succ_apply'] using ih.1.comp ha hm
      · simpa only [iterate_succ, iterate_succ_apply'] using ih.2.comp hm

/-- The first logarithm can start from a disk of any fixed radius, provided
its image radius is at most the small radius used for the remaining steps. -/
theorem complexL_iterate_large_disk {u ρ M : ℝ}
    (hρ : 0 < ρ) (hu : ρ ≤ u) (hM : 0 < M) (n : ℕ)
    (hx : M < 1 + E^[n + 1] u)
    (hsmall : M / (1 + E^[n + 1] u - M) ≤ ρ) :
    AnalyticOnNhd ℂ (complexL^[n + 1]) (Metric.ball (E^[n + 1] u : ℂ) M) ∧
      MapsTo (complexL^[n + 1]) (Metric.ball (E^[n + 1] u : ℂ) M)
        (Metric.ball (u : ℂ) ρ) := by
  have hm := complexL_mapsTo_ball hM hx
  rw [iterate_succ_apply', complexL_E] at hm
  have hm' : MapsTo complexL (Metric.ball (E^[n + 1] u : ℂ) M)
      (Metric.ball (E^[n] u : ℂ) ρ) := by
    rw [iterate_succ_apply'] at hsmall ⊢
    apply hm.mono_right
    exact Metric.ball_subset_ball hsmall
  have ha := complexL_analyticOnNhd_ball hx
  have hi := complexL_iterate_disk hρ hu n
  constructor
  · simpa only [iterate_succ] using hi.1.comp ha hm'
  · simpa only [iterate_succ] using hi.2.comp hm'

end AbelFormalization
