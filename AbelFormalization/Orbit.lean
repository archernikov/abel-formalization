import AbelFormalization.Inverse
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Decomposition into a fundamental interval

For a fixed positive `U`, every `x ≥ U` is an iterate of a point in
`[U, E U)`. The number of iterates tends to infinity as `x` tends to infinity.
These are the dynamical facts used in the paper's compact-interval estimates.
-/

noncomputable section

open Set Function Filter

namespace AbelFormalization

/-- The number of integer Abel-time steps above the fundamental interval. -/
def orbitIndex (A : ℝ → ℝ) (U x : ℝ) : ℕ := ⌊A x - A U⌋₊

/-- The point in the fundamental interval obtained by subtracting the whole
number of Abel-time steps. -/
def orbitBase (A : ℝ → ℝ) (U x : ℝ) : ℝ :=
  inverse A (A x - (orbitIndex A U x : ℝ))

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem orbitBase_pos (U x : ℝ) : 0 < orbitBase A U x :=
  hA.inverse_pos _

theorem apply_orbitBase (U x : ℝ) :
    A (orbitBase A U x) = A x - (orbitIndex A U x : ℝ) :=
  hA.apply_inverse _

theorem orbitBase_mem {U x : ℝ} (hU : 0 < U) (hx : U ≤ x) :
    orbitBase A U x ∈ Ico U (E U) := by
  have hxpos : 0 < x := hU.trans_le hx
  have hAUx := hA.strictMonoOn.monotoneOn hU hxpos hx
  have hnlow : (orbitIndex A U x : ℝ) ≤ A x - A U :=
    Nat.floor_le (sub_nonneg.mpr hAUx)
  have hnupper : A x - A U < (orbitIndex A U x : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  constructor
  · have hi := hA.inverse_strictMono.monotone (show A U ≤
        A x - (orbitIndex A U x : ℝ) by linarith)
    simpa only [orbitBase, hA.inverse_apply hU] using hi
  · by_contra h
    have hi := hA.strictMonoOn.monotoneOn (E_pos hU) (hA.orbitBase_pos U x)
      (le_of_not_gt h)
    rw [hA.abel U hU, hA.apply_orbitBase U x] at hi
    linarith

theorem iterate_orbitBase {U x : ℝ} (hx : 0 < x) :
    E^[orbitIndex A U x] (orbitBase A U x) = x := by
  apply hA.injectiveOn (E_iterate_pos (hA.orbitBase_pos U x) _) hx
  rw [hA.abel_iterate (hA.orbitBase_pos U x), hA.apply_orbitBase U x]
  linarith

/-- Every point above `U` is an iterate of a point in the fundamental interval. -/
theorem fundamental_interval_decomposition {U x : ℝ} (hU : 0 < U) (hx : U ≤ x) :
    ∃ (n : ℕ) (u : ℝ), U ≤ u ∧ u < E U ∧ x = E^[n] u := by
  refine ⟨orbitIndex A U x, orbitBase A U x, ?_, ?_, ?_⟩
  · exact (hA.orbitBase_mem hU hx).1
  · exact (hA.orbitBase_mem hU hx).2
  · exact (hA.iterate_orbitBase (hU.trans_le hx)).symm

theorem orbitIndex_tendsto_atTop (U : ℝ) :
    Tendsto (orbitIndex A U) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro n
  have he : ∀ᶠ x : ℝ in atTop, (n : ℝ) + A U ≤ A x :=
    hA.tendsto_atTop.eventually (eventually_ge_atTop _)
  exact he.mono fun x hx => Nat.le_floor (by linarith)

end IsAbel
end AbelFormalization
