import AbelFormalization.MinimalPrimeDescent
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Localization.Submodule

set_option autoImplicit false

/-!
# Localization away from all minimal primes

For a Noetherian commutative ring `B`, let `Sigma` consist of the elements
which avoid every minimal prime of `B`.  This file proves that every prime of
the localization `Sigma^-1 B` contracts to a minimal prime of `B`.  Hence the
localization has Krull dimension at most zero and is Artinian.
-/

noncomputable section

namespace AbelFormalization

/-- The multiplicative set of elements which lie outside every minimal prime. -/
def minimalPrimeAvoidanceSubmonoid (B : Type*) [CommRing B] : Submonoid B where
  carrier := {b | ∀ p ∈ minimalPrimes B, b ∉ p}
  one_mem' := by
    intro p hp hOne
    exact hp.isPrime.one_notMem hOne
  mul_mem' := by
    intro a b ha hb p hp hab
    rcases hp.isPrime.mem_or_mem hab with hap | hbp
    · exact ha p hp hap
    · exact hb p hp hbp

@[simp]
theorem mem_minimalPrimeAvoidanceSubmonoid
    {B : Type*} [CommRing B] (b : B) :
    b ∈ minimalPrimeAvoidanceSubmonoid B ↔
      ∀ p ∈ minimalPrimes B, b ∉ p :=
  Iff.rfl

/-- A prime ideal disjoint from the elements avoiding all minimal primes is
itself a minimal prime. -/
theorem mem_minimalPrimes_of_isPrime_disjoint_minimalPrimeAvoidanceSubmonoid
    {B : Type*} [CommRing B] [IsNoetherianRing B]
    {p : Ideal B} (hp : p.IsPrime)
    (hdisj : Disjoint
      (minimalPrimeAvoidanceSubmonoid B : Set B) (p : Set B)) :
    p ∈ minimalPrimes B := by
  classical
  have hsub : (p : Set B) ⊆ ⋃ q ∈ minimalPrimes B, (q : Set B) := by
    intro b hbp
    have hbnot : b ∉ minimalPrimeAvoidanceSubmonoid B := by
      intro hb
      exact Set.disjoint_left.mp hdisj hb hbp
    have hmem : ∃ q, q ∈ minimalPrimes B ∧ b ∈ q := by
      by_contra hmem
      apply hbnot
      intro q hq hbq
      apply hmem
      exact ⟨q, hq, hbq⟩
    obtain ⟨q, hq, hbq⟩ := hmem
    exact Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hq, hbq⟩⟩
  obtain ⟨q, hq, hpq⟩ :=
    (Ideal.subset_union_prime_finite
      (s := minimalPrimes B) (I := p)
      (minimalPrimes.finite_of_isNoetherianRing B)
      (f := id) (⊥ : Ideal B) (⊥ : Ideal B)
      (fun _ hq _ _ ↦ hq.isPrime)).mp hsub
  have hqp : q ≤ p := hq.2 ⟨hp, bot_le⟩ hpq
  have hpq' : p = q := le_antisymm hpq hqp
  exact hpq'.symm ▸ hq

/-- Localizing a Noetherian ring at the elements avoiding all minimal primes
produces a ring of Krull dimension at most zero. -/
theorem minimalPrimeAvoidanceLocalization_krullDimLE_zero
    {B T : Type*} [CommRing B] [IsNoetherianRing B]
    [CommRing T] [Algebra B T]
    [IsLocalization (minimalPrimeAvoidanceSubmonoid B) T] :
    Ring.KrullDimLE 0 T := by
  apply Ring.krullDimLE_zero_iff.mpr
  intro P hP
  obtain ⟨Q, hQ, hPQ⟩ := Ideal.exists_le_maximal P hP.ne_top
  have hPdata :=
    (IsLocalization.isPrime_iff_isPrime_disjoint
      (minimalPrimeAvoidanceSubmonoid B) T P).mp hP
  have hQdata :=
    (IsLocalization.isPrime_iff_isPrime_disjoint
      (minimalPrimeAvoidanceSubmonoid B) T Q).mp hQ.isPrime
  have hPmin : P.under B ∈ minimalPrimes B :=
    mem_minimalPrimes_of_isPrime_disjoint_minimalPrimeAvoidanceSubmonoid
      hPdata.1 hPdata.2
  have hQmin : Q.under B ∈ minimalPrimes B :=
    mem_minimalPrimes_of_isPrime_disjoint_minimalPrimeAvoidanceSubmonoid
      hQdata.1 hQdata.2
  have hPQunder : P.under B ≤ Q.under B :=
    (IsLocalization.orderEmbedding
      (minimalPrimeAvoidanceSubmonoid B) T).monotone hPQ
  have hQPunder : Q.under B ≤ P.under B :=
    hQmin.2 ⟨hPdata.1, bot_le⟩ hPQunder
  have hunder : P.under B = Q.under B :=
    le_antisymm hPQunder hQPunder
  have hPQ' : P = Q :=
    (IsLocalization.orderEmbedding
      (minimalPrimeAvoidanceSubmonoid B) T).injective hunder
  exact hPQ'.symm ▸ hQ

/-- The localization of a Noetherian ring away from all of its minimal primes
is Artinian. -/
theorem minimalPrimeAvoidanceLocalization_isArtinianRing
    {B T : Type*} [CommRing B] [IsNoetherianRing B]
    [CommRing T] [Algebra B T]
    [IsLocalization (minimalPrimeAvoidanceSubmonoid B) T] :
    IsArtinianRing T := by
  letI : IsNoetherianRing T :=
    IsLocalization.isNoetherianRing
      (minimalPrimeAvoidanceSubmonoid B) T (by infer_instance)
  letI : Ring.KrullDimLE 0 T :=
    minimalPrimeAvoidanceLocalization_krullDimLE_zero (B := B) (T := T)
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

end AbelFormalization
