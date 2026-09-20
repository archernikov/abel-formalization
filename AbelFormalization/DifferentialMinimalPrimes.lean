import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Tactic.Ring

/-!
# Derivations preserve minimal primes over invariant ideals

A localization is used only to clear one power of an element of a minimal
prime. The derivation itself remains
in the original ring. A least-exponent argument requires just one application
of the Leibniz rule and no iterated-derivative formula.
-/

noncomputable section

namespace AbelFormalization

variable {S : Type*} [CommRing S]

/-- Membership in a minimal prime gives a power relation with a multiplier
outside that same prime. -/
theorem exists_notMem_mul_pow_mem_of_mem_minimalPrime
    (I : Ideal S) {q : Ideal S} (hq : q ∈ I.minimalPrimes)
    {x : S} (hx : x ∈ q) : ∃ n : ℕ, ∃ y ∉ q, y * x ^ n ∈ I := by
  let : q.IsPrime := hq.isPrime
  let L := Localization.AtPrime q
  have hxL : algebraMap S L x ∈ (I.map (algebraMap S L)).radical := by
    rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := L) q I hq]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨n, hn⟩ := hxL
  rw [← map_pow] at hn
  obtain ⟨y, hy, hyx⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl L I (x ^ n)).mp hn
  exact ⟨n, y, hy, hyx⟩

variable {K : Type*} [Field K] [Algebra K S]

/-- Preservation of the generators implies preservation of their ideal. -/
theorem derivation_mem_ideal_span (D : Derivation K S S) (s : Set S)
    (hs : ∀ x ∈ s, D x ∈ Ideal.span s) :
    ∀ x ∈ Ideal.span s, D x ∈ Ideal.span s := by
  let I := Ideal.span s
  let J : Ideal S :=
    { carrier := {x | x ∈ I ∧ D x ∈ I}
      zero_mem' := ⟨I.zero_mem, by simp⟩
      add_mem' := by
        intro x y hx hy
        exact ⟨I.add_mem hx.1 hy.1, by simpa only [map_add] using I.add_mem hx.2 hy.2⟩
      smul_mem' := by
        intro a x hx
        refine ⟨I.smul_mem a hx.1, ?_⟩
        change D (a * x) ∈ I
        rw [D.leibniz, smul_eq_mul, smul_eq_mul]
        exact I.add_mem (I.mul_mem_left a hx.2) (I.mul_mem_right (D a) hx.1) }
  have hIJ : I ≤ J := Ideal.span_le.mpr fun x hx => ⟨Ideal.subset_span hx, hs x hx⟩
  intro x hx
  exact (hIJ hx).2

/-- A derivation over a characteristic-zero field preserves every minimal
prime over any ideal it preserves. No Noetherianity is required. -/
theorem derivation_mem_of_mem_minimalPrimes [CharZero K]
    (D : Derivation K S S) (I : Ideal S)
    (hDI : ∀ x ∈ I, D x ∈ I)
    {q : Ideal S} (hq : q ∈ I.minimalPrimes) :
    ∀ x ∈ q, D x ∈ q := by
  classical
  let : q.IsPrime := hq.isPrime
  intro x hx
  by_contra hDx
  have hex : ∃ n : ℕ, ∃ y ∉ q, y * x ^ n ∈ I :=
    exists_notMem_mul_pow_mem_of_mem_minimalPrime I hq hx
  let n := Nat.find hex
  obtain ⟨y, hy, hyx⟩ : ∃ y ∉ q, y * x ^ n ∈ I := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro hn
    apply hy
    apply hq.le
    simpa only [hn, pow_zero, mul_one] using hyx
  have hnu : IsUnit (n : S) := by
    have hnK : IsUnit (n : K) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn0)
    simpa only [map_natCast] using hnK.map (algebraMap K S)
  have hnq : (n : S) ∉ q := q.notMem_of_isUnit hnu
  have hcq : (n : S) * y ^ 2 * D x ∉ q :=
    hq.isPrime.mul_notMem
      (hq.isPrime.mul_notMem hnq (by simpa only [pow_two] using hq.isPrime.mul_notMem hy hy)) hDx
  have hrel : ((n : S) * y ^ 2 * D x) * x ^ (n - 1) ∈ I := by
    have h := I.sub_mem (I.mul_mem_left y (hDI _ hyx)) (I.mul_mem_left (D y) hyx)
    convert h using 1
    simp only [D.leibniz, D.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
    ring
  exact Nat.find_min hex (Nat.sub_one_lt hn0) ⟨(n : S) * y ^ 2 * D x, hcq, hrel⟩

end AbelFormalization
