import AbelFormalization.FilteredFiniteHierarchy
import Mathlib.Order.Cofinal
import Mathlib.Order.Interval.Finset.Nat

/-!
# Nonvacuous divergence on a restricted natural tail

For every set `S`, the restricted filter `atTop ⊓ principal S` is below
`atTop`; consequently the identity tends to infinity along it.  This formal
`Tendsto` statement is vacuous when the restricted filter is bottom.

Cofinality, equivalently unboundedness for a subset of `ℕ`, is precisely the
additional condition saying that the restricted filter is nontrivial.  The
lemmas below keep those two facts separate and then package them together.
-/

namespace AbelFormalization

open Set Filter
open scoped Topology

/-- The restriction of `atTop` to `S` is nontrivial exactly when `S` is
unbounded above. -/
theorem atTop_inf_principal_neBot_iff_not_bddAbove {S : Set ℕ} :
    (atTop ⊓ Filter.principal S).NeBot ↔ ¬ BddAbove S := by
  rw [← Nat.cofinite_eq_atTop, cofinite_inf_principal_neBot_iff]
  exact ⟨Set.Infinite.not_bddAbove, Set.infinite_of_not_bddAbove⟩

/-- For subsets of `ℕ`, nontriviality of the restricted tail is equivalent
to cofinality. -/
theorem atTop_inf_principal_neBot_iff_isCofinal {S : Set ℕ} :
    (atTop ⊓ Filter.principal S).NeBot ↔ IsCofinal S :=
  atTop_inf_principal_neBot_iff_not_bddAbove.trans
    not_bddAbove_iff_isCofinal

/-- The preceding characterization with cofinality written pointwise. -/
theorem atTop_inf_principal_neBot_iff_forall_exists_ge {S : Set ℕ} :
    (atTop ⊓ Filter.principal S).NeBot ↔
      ∀ N : ℕ, ∃ n ∈ S, N ≤ n := by
  simpa only [IsCofinal] using
    (atTop_inf_principal_neBot_iff_isCofinal (S := S))

/-- The identity tends to infinity along every restricted tail.  This does
not assert that the filter is nontrivial. -/
theorem tendsto_id_atTop_inf_principal (S : Set ℕ) :
    Tendsto id (atTop ⊓ Filter.principal S) atTop := by
  exact (tendsto_id : Tendsto (id : ℕ → ℕ) atTop atTop).mono_left inf_le_left

/-- Cofinality gives the honest, nonvacuous form of restricted identity
divergence. -/
theorem neBot_and_tendsto_id_atTop_inf_principal_of_isCofinal
    {S : Set ℕ} (hS : IsCofinal S) :
    (atTop ⊓ Filter.principal S).NeBot ∧
      Tendsto id (atTop ⊓ Filter.principal S) atTop :=
  ⟨atTop_inf_principal_neBot_iff_isCofinal.mpr hS,
    tendsto_id_atTop_inf_principal S⟩

/-- Nonvacuous restricted identity divergence is exactly cofinality of the
restricting set. -/
theorem neBot_and_tendsto_id_atTop_inf_principal_iff_isCofinal
    {S : Set ℕ} :
    ((atTop ⊓ Filter.principal S).NeBot ∧
      Tendsto id (atTop ⊓ Filter.principal S) atTop) ↔ IsCofinal S := by
  constructor
  · exact fun h => atTop_inf_principal_neBot_iff_isCofinal.mp h.1
  · exact neBot_and_tendsto_id_atTop_inf_principal_of_isCofinal

/-- A natural-valued function which is eventually at least its index tends
to infinity on the restricted tail. -/
theorem tendsto_nat_atTop_inf_principal_of_eventually_id_le
    (S : Set ℕ) (t : ℕ → ℕ)
    (ht : ∀ᶠ n in atTop ⊓ Filter.principal S, n ≤ t n) :
    Tendsto t (atTop ⊓ Filter.principal S) atTop :=
  tendsto_atTop_mono' (atTop ⊓ Filter.principal S) ht
    (tendsto_id_atTop_inf_principal S)

/-- A real-valued function which is eventually at least its natural-number
index tends to infinity on the restricted tail.  This is the form consumed
by the filtered finite-hierarchy theorem. -/
theorem tendsto_real_atTop_inf_principal_of_eventually_natCast_le
    (S : Set ℕ) (t : ℕ → ℝ)
    (ht : ∀ᶠ n : ℕ in atTop ⊓ Filter.principal S, (n : ℝ) ≤ t n) :
    Tendsto t (atTop ⊓ Filter.principal S) atTop := by
  apply tendsto_atTop_mono' (atTop ⊓ Filter.principal S) ht
  exact (tendsto_natCast_atTop_atTop (R := ℝ)).mono_left inf_le_left

/-- Cofinality plus an eventual lower bound gives nonvacuous divergence of a
real-valued common time. -/
theorem neBot_and_tendsto_real_atTop_inf_principal_of_isCofinal
    {S : Set ℕ} (hS : IsCofinal S) (t : ℕ → ℝ)
    (ht : ∀ᶠ n : ℕ in atTop ⊓ Filter.principal S, (n : ℝ) ≤ t n) :
    (atTop ⊓ Filter.principal S).NeBot ∧
      Tendsto t (atTop ⊓ Filter.principal S) atTop :=
  ⟨atTop_inf_principal_neBot_iff_isCofinal.mpr hS,
    tendsto_real_atTop_inf_principal_of_eventually_natCast_le S t ht⟩

/-- The same real-valued divergence statement through the maintained
`restrictedAtTop` abbreviation. -/
theorem tendsto_real_restrictedAtTop_of_eventually_natCast_le
    (S : Set ℕ) (t : ℕ → ℝ)
    (ht : ∀ᶠ n : ℕ in restrictedAtTop S, (n : ℝ) ≤ t n) :
    Tendsto t (restrictedAtTop S) atTop :=
  tendsto_real_atTop_inf_principal_of_eventually_natCast_le S t ht

end AbelFormalization
