import AbelFormalization.SeparatedClustersReduction

/-!
# Inverse-power lower bounds exclude eventual common zeros

The separated-cluster certificate is used on an infinite restricted tail of
regular zeros.  Its evaluated generators all vanish there, whereas a genuine
inverse-power lower bound is strictly positive once the scale is at least
one.  This file records that final contradiction explicitly, including the
nonvacuity condition for the restricted filter.
-/

noncomputable section

open Filter

namespace AbelFormalization

set_option autoImplicit false

/-- On a nontrivial filter and a positive scale, a finite family with an
inverse-power lower bound cannot vanish identically eventually. -/
theorem HasInversePowerLowerBound.not_eventually_forall_eq_zero
    {X ι : Type*} [Fintype ι] [Nonempty ι]
    {l : Filter X} [l.NeBot] {R : X → ℝ} {f : ι → X → ℝ}
    (hlower : HasInversePowerLowerBound l R f)
    (hR : ∀ᶠ x in l, 1 ≤ R x) :
    ¬ ∀ᶠ x in l, ∀ i, f i x = 0 := by
  intro hzero
  obtain ⟨c, hc, M, hbound⟩ := hlower
  have hfalse : ∀ᶠ x in l, False := by
    filter_upwards [hR, hbound, hzero] with x hxR hxbound hxzero
    have hmax : finiteFamilyMaxAbs f x = 0 := by
      obtain ⟨i, hi⟩ := exists_abs_eq_finiteFamilyMaxAbs f x
      rw [← hi, hxzero i, abs_zero]
    have hRpos : 0 < R x := zero_lt_one.trans_le hxR
    have hleft : 0 < c / (R x) ^ M :=
      div_pos hc (pow_pos hRpos M)
    rw [hmax] at hxbound
    linarith
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

/-- Pointwise common vanishing is a convenient stronger hypothesis. -/
theorem HasInversePowerLowerBound.not_forall_eq_zero
    {X ι : Type*} [Fintype ι] [Nonempty ι]
    {l : Filter X} [l.NeBot] {R : X → ℝ} {f : ι → X → ℝ}
    (hlower : HasInversePowerLowerBound l R f)
    (hR : ∀ᶠ x in l, 1 ≤ R x)
    (hzero : ∀ x i, f i x = 0) : False := by
  exact hlower.not_eventually_forall_eq_zero hR
    (Eventually.of_forall hzero)

/-- Specialized contradiction on the manuscript's restricted separated
tail.  Infinitude of `Λ ∩ Γ N` supplies exactly the missing `NeBot` fact. -/
theorem HasInversePowerLowerBound.false_of_separatedRestriction_zeros
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {Λ : Set ℕ} {Γ : ℕ → Set ℕ} {N : ℕ}
    {R : ℕ → ℝ} {f : ι → ℕ → ℝ}
    (hInfinite : (Λ ∩ Γ N).Infinite)
    (hlower : HasInversePowerLowerBound
      (separatedRestriction Λ Γ N) R f)
    (hR : ∀ᶠ n in separatedRestriction Λ Γ N, 1 ≤ R n)
    (hzero : ∀ᶠ n in separatedRestriction Λ Γ N,
      ∀ i, f i n = 0) : False := by
  let _ : (separatedRestriction Λ Γ N).NeBot :=
    separatedRestriction_neBot_iff.mpr hInfinite
  exact hlower.not_eventually_forall_eq_zero hR hzero

end AbelFormalization
