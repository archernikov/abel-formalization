import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.KrullDimension.Regular

set_option autoImplicit false

/-!
# Minimal-prime avoidance and principal-quotient dimension descent

This file isolates three commutative-algebra facts used in the finite descent
argument.  In particular, the element chosen by finite prime avoidance is
only known to avoid the minimal primes.  It is not asserted to be a
non-zero-divisor: embedded associated primes can still contain it.
-/

noncomputable section

namespace AbelFormalization

open scoped Pointwise

/-- If an ideal is contained in no minimal prime of a Noetherian ring, then it
contains one element which simultaneously avoids every minimal prime. -/
theorem exists_mem_ideal_avoids_minimalPrimes
    {B : Type*} [CommRing B] [IsNoetherianRing B]
    (C : Ideal B)
    (hC : ∀ p ∈ minimalPrimes B, ¬ C ≤ p) :
    ∃ b : B, b ∈ C ∧ ∀ p ∈ minimalPrimes B, b ∉ p := by
  classical
  by_contra hExists
  have hsub : (C : Set B) ⊆ ⋃ p ∈ minimalPrimes B, (p : Set B) := by
    intro b hb
    have hmem : ∃ p, p ∈ minimalPrimes B ∧ b ∈ p := by
      by_contra hmem
      apply hExists
      refine ⟨b, hb, ?_⟩
      intro p hp hbp
      apply hmem
      exact ⟨p, hp, hbp⟩
    obtain ⟨p, hp, hbp⟩ := hmem
    refine Set.mem_iUnion.2 ⟨p, ?_⟩
    exact Set.mem_iUnion.2 ⟨hp, hbp⟩
  obtain ⟨p, hp, hCp⟩ :=
    (Ideal.subset_union_prime_finite
      (s := minimalPrimes B) (I := C)
      (minimalPrimes.finite_of_isNoetherianRing B)
      (f := id) (⊥ : Ideal B) (⊥ : Ideal B)
      (fun _ hp _ _ ↦ hp.isPrime)).mp hsub
  exact hC p hp hCp

/-- In a ring of Krull dimension at most zero, an element outside every
minimal prime is a unit. -/
theorem isUnit_of_avoids_minimalPrimes_of_krullDimLE_zero
    {B : Type*} [CommRing B] [Ring.KrullDimLE 0 B] {b : B}
    (hb : ∀ p ∈ minimalPrimes B, b ∉ p) : IsUnit b := by
  classical
  by_contra hUnit
  have hNonunit : b ∈ nonunits B := mem_nonunits_iff.mpr hUnit
  obtain ⟨p, hpMax, hbp⟩ := exists_max_ideal_of_mem_nonunits hNonunit
  exact hb p (Ideal.mem_minimalPrimes_iff_isPrime.mpr hpMax.isPrime) hbp

/-- Quotienting by an element which avoids every minimal prime lowers a
positive finite upper bound on Krull dimension by one.  The proof uses the
support-dimension inequality for `B / bB`; it does not require `b` to be a
non-zero-divisor. -/
theorem Ring.KrullDimLE.quotient_span_singleton_of_avoids_minimalPrimes
    {B : Type*} [CommRing B] [IsNoetherianRing B]
    (d : ℕ) [Ring.KrullDimLE (d + 1) B] {b : B}
    (hb : ∀ p ∈ minimalPrimes B, b ∉ p) :
    Ring.KrullDimLE d (B ⧸ Ideal.span {b}) := by
  rw [Ring.krullDimLE_iff]
  have hann : Module.annihilator B B = ⊥ :=
    Module.annihilator_eq_bot.mpr inferInstance
  have hsupp :=
    Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
      (R := B) (M := B) (x := b) (by simpa [hann] using hb)
  have hdim : Module.supportDim B B ≤ (d + 1 : ℕ) := by
    rw [Module.supportDim_self_eq_ringKrullDim]
    exact Ring.krullDimLE_iff.mp
      (show Ring.KrullDimLE (d + 1) B from inferInstance)
  have hquot :
      Module.supportDim B (QuotSMulTop b B) ≤ (d : WithBot ℕ∞) := by
    rw [← ENat.WithBot.add_le_add_one_right_iff]
    simpa only [Nat.cast_add, Nat.cast_one] using hsupp.trans hdim
  have hspan : Ideal.span {b} = b • (⊤ : Ideal B) := by
    simp [← Submodule.ideal_span_singleton_smul]
  rw [ringKrullDim_eq_of_ringEquiv
        (Ideal.quotientEquivAlgOfEq B hspan).toRingEquiv,
      ← Module.supportDim_quotient_eq_ringKrullDim]
  exact hquot

end AbelFormalization
