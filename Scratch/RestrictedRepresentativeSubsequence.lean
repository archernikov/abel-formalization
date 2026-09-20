import AbelFormalization.RestrictedBaseConvergentSequence
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Filter.AtTopBot.Finite

/-!
# Subsequence classification of finitely many representatives

After compactness has made the bounded-coordinate tuple converge, the outer
induction in the manuscript passes to one further subsequence on which every
representative coordinate is either bounded or tends to positive infinity.
This file isolates that purely sequential reduction.  It uses no Abel or
regular-zero hypothesis.
-/

noncomputable section

open Filter Set

namespace AbelFormalization

set_option autoImplicit false

/-- A real sequence which is not bounded above has a strictly increasing
subsequence of indices along which it tends to positive infinity. -/
theorem exists_strictMono_subsequence_tendsto_atTop_of_not_bddAbove
    (u : ℕ → ℝ) (hu : ¬ BddAbove (Set.range u)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop atTop := by
  have hfrequent : ∀ n : ℕ, ∃ᶠ k in atTop, (n : ℝ) < u k := by
    intro n
    rw [frequently_atTop]
    intro N
    obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun j : Fin N ↦ u j)
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ :=
      (not_bddAbove_iff.mp hu) (max (n : ℝ) C)
    have hNk : N ≤ k := by
      by_contra h
      have hkN : k < N := Nat.lt_of_not_ge h
      have hukC : u k ≤ C := hC ⟨⟨k, hkN⟩, rfl⟩
      exact (not_lt_of_ge hukC) ((le_max_right _ _).trans_lt hk)
    exact ⟨k, hNk, (le_max_left _ _).trans_lt hk⟩
  obtain ⟨φ, hφ, hlarge⟩ := extraction_forall_of_frequently hfrequent
  refine ⟨φ, hφ, ?_⟩
  apply tendsto_atTop_mono' atTop
    (Eventually.of_forall fun n ↦ (hlarge n).le)
  exact tendsto_natCast_atTop_atTop

/-- Every real sequence has a strictly increasing subsequence which is
bounded above or tends to positive infinity. -/
theorem exists_strictMono_subsequence_bddAbove_or_tendsto_atTop
    (u : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (BddAbove (Set.range (u ∘ φ)) ∨ Tendsto (u ∘ φ) atTop atTop) := by
  by_cases hu : BddAbove (Set.range u)
  · exact ⟨id, strictMono_id, Or.inl (by simpa using hu)⟩
  · obtain ⟨φ, hφ, hlim⟩ :=
      exists_strictMono_subsequence_tendsto_atTop_of_not_bddAbove u hu
    exact ⟨φ, hφ, Or.inr hlim⟩

/-- For a finite tuple of real sequences, one common strictly increasing
subsequence makes every coordinate bounded above or divergent to positive
infinity. -/
theorem exists_strictMono_subsequence_representatives_classified
    {m : ℕ} (s : ℕ → Fin m → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i,
      BddAbove (Set.range (fun n ↦ s (φ n) i)) ∨
        Tendsto (fun n ↦ s (φ n) i) atTop atTop := by
  induction m with
  | zero =>
      exact ⟨id, strictMono_id, fun i ↦ Fin.elim0 i⟩
  | succ m ih =>
      obtain ⟨φ, hφ, hhead⟩ :=
        exists_strictMono_subsequence_bddAbove_or_tendsto_atTop
          (fun n ↦ s n (0 : Fin (m + 1)))
      obtain ⟨ψ, hψ, htail⟩ :=
        ih (fun n i ↦ s (φ n) i.succ)
      refine ⟨φ ∘ ψ, hφ.comp hψ, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · rcases hhead with hhead | hhead
        · left
          refine hhead.mono ?_
          rintro y ⟨n, rfl⟩
          exact ⟨ψ n, rfl⟩
        · right
          change Tendsto (((fun n ↦ s n (0 : Fin (m + 1))) ∘ φ) ∘ ψ)
            atTop atTop
          exact hhead.comp hψ.tendsto_atTop
      · simpa only [Function.comp_apply] using htail j

end AbelFormalization
