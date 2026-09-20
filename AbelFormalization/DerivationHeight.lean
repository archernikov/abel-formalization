import AbelFormalization.DifferentialMinimalPrimes
import Mathlib.RingTheory.Ideal.Height
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Height from a nonvanishing derivation minor

Minimal primes of differential ideals in characteristic zero are preserved
by the derivation. This gives a chain of strict prime inclusions for a tuple
of functions with a nonvanishing derivation minor. The argument needs no
regularity of arbitrary prime localizations of the ambient ring.
-/

noncomputable section

namespace AbelFormalization

variable {K S : Type*} [Field K] [CharZero K] [CommRing S] [Algebra K S]

/-- A tuple with derivations diagonalized up to a common factor outside a
prime forces that prime to have at least the length of the tuple as height. -/
theorem height_ge_of_diagonal_derivations :
    ∀ {n : ℕ} (f : Fin n → S) (D : Fin n → Derivation K S S) (Δ : S)
      (p : Ideal S) [p.IsPrime],
      (∀ i, f i ∈ p) → Δ ∉ p →
      (∀ i j, D i (f j) = if i = j then Δ else 0) → (n : ℕ∞) ≤ p.height := by
  intro n
  induction n with
  | zero =>
      intro f D Δ p hp hf hΔ hD
      exact zero_le
  | succ n ih =>
      intro f D Δ p hp hf hΔ hD
      classical
      let I : Ideal S := Ideal.span (Set.range (fun i : Fin n => f i.succ))
      have hIp : I ≤ p := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact hf i.succ
      obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hIp
      let : q.IsPrime := hq.isPrime
      have hΔq : Δ ∉ q := fun h => hΔ (hqp h)
      have hD0 : ∀ x ∈ I, D 0 x ∈ I := by
        apply derivation_mem_ideal_span
        rintro _ ⟨i, rfl⟩
        rw [hD, ite_eq_right (Fin.succ_ne_zero i).symm]
        exact I.zero_mem
      have hf0 : f 0 ∉ q := by
        intro h
        have hdq := derivation_mem_of_mem_minimalPrimes (D 0) I hD0 hq (f 0) h
        rw [hD, ite_eq_left rfl] at hdq
        exact hΔq hdq
      have hlt : q < p := lt_of_le_of_ne hqp (by
        intro heq
        apply hf0
        rw [heq]
        exact hf 0)
      have hheight : (n : ℕ∞) ≤ q.height := by
        apply ih (fun i => f i.succ) (fun i => D i.succ) Δ q
        · intro i
          exact hq.1.2 (Ideal.subset_span ⟨i, rfl⟩)
        · exact hΔq
        · intro i j
          simpa only [Fin.succ_inj] using hD i.succ j.succ
      calc
        ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by simp
        _ ≤ q.height + 1 := add_le_add hheight le_rfl
        _ ≤ p.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt

omit [CharZero K] in
/-- Evaluation commutes with a finite sum of derivations. -/
theorem derivation_finset_sum_apply {ι : Type*} (s : Finset ι)
    (D : ι → Derivation K S S) (x : S) : (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Derivation.zero_apply]
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi, Derivation.add_apply, ih]

/-- A nonvanishing square derivation minor gives the same height bound.
The adjugate supplies actual source-ring derivations, so no localization or
extension of derivations is needed in this theorem. -/
theorem height_ge_of_derivation_determinant {n : ℕ}
    (f : Fin n → S) (D : Fin n → Derivation K S S)
    (p : Ideal S) [p.IsPrime] (hf : ∀ i, f i ∈ p)
    (hdet : (Matrix.det (fun i j => D i (f j))) ∉ p) : (n : ℕ∞) ≤ p.height := by
  classical
  let A : Matrix (Fin n) (Fin n) S := fun i j => D i (f j)
  let E : Fin n → Derivation K S S := fun i => ∑ k, A.adjugate i k • D k
  apply height_ge_of_diagonal_derivations f E A.det p hf hdet
  intro i j
  change (∑ k, A.adjugate i k • D k) (f j) = if i = j then A.det else 0
  rw [derivation_finset_sum_apply]
  simp only [Derivation.smul_apply, smul_eq_mul]
  change (A.adjugate * A) i j = if i = j then A.det else 0
  rw [Matrix.adjugate_mul]
  simp [Matrix.one_apply]

end AbelFormalization
