import AbelFormalization.Statement
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FinCases

/-!
# Definability consequences of the Abel equation

The proofs in this file construct definable graphs in the actual language of
`Statement.lean`. They do not assume o-minimality or regular-zero finiteness.
-/

noncomputable section

namespace AbelFormalization

open Set FirstOrder FirstOrder.Language

section Closure

variable (A : ℝ → ℝ)

@[fun_prop] private theorem definable_const {α : Type*} (c : ℝ) :
    @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) (fun _ : α → ℝ => c) := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  exact abelLanguage.definableFun_const α (Set.mem_univ c)

@[fun_prop] private theorem definable_add {α : Type*} {f g : (α → ℝ) → ℝ}
    (hf : @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) f)
    (hg : @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) g) :
    @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) (fun x => f x + g x) := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  have hs := (Set.DefinableFun.fun_symbol (L := abelLanguage) (M := ℝ)
    (.add : abelLanguage.Functions 2)).of_empty (A := (Set.univ : Set ℝ))
  exact Set.DefinableFun.comp (g := fun x => ![f x, g x])
    (by
      intro i
      fin_cases i
      · simpa using hf
      · simpa using hg) hs

@[fun_prop] private theorem definable_mul {α : Type*} {f g : (α → ℝ) → ℝ}
    (hf : @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) f)
    (hg : @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) g) :
    @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) (fun x => f x * g x) := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  have hs := (Set.DefinableFun.fun_symbol (L := abelLanguage) (M := ℝ)
    (.mul : abelLanguage.Functions 2)).of_empty (A := (Set.univ : Set ℝ))
  exact Set.DefinableFun.comp (g := fun x => ![f x, g x])
    (by
      intro i
      fin_cases i
      · simpa using hf
      · simpa using hg) hs

@[fun_prop] private theorem definable_sq {α : Type*} {f : (α → ℝ) → ℝ}
    (hf : @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) f) :
    @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) (fun x => (f x) ^ 2) := by
  simpa only [pow_two] using definable_mul A hf hf

@[fun_prop] private theorem definable_c0 {α : Type*} {f : (α → ℝ) → ℝ}
    (hf : @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) f) :
    @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) (fun x => C0 A (f x)) := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  have hs := (Set.DefinableFun.fun_symbol (L := abelLanguage) (M := ℝ)
    (.c0 : abelLanguage.Functions 1)).of_empty (A := (Set.univ : Set ℝ))
  exact Set.DefinableFun.comp (g := fun x => ![f x])
    (by intro i; fin_cases i; simpa using hf) hs

private theorem definable_lt {α : Type*} {f g : (α → ℝ) → ℝ}
    (hf : @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) f)
    (hg : @Set.DefinableFun ℝ abelLanguage (abelStructure A) _ (Set.univ : Set ℝ) g) :
    @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _ {x | f x < g x} := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  have hs : @Set.Definable ℝ (∅ : Set ℝ) abelLanguage (abelStructure A) _
      {x : Fin 2 → ℝ | x 0 < x 1} := by
    rw [Set.empty_definable_iff]
    refine ⟨Relations.formula₂ (L := abelLanguage) .lt (.var 0) (.var 1), ?_⟩
    rfl
  exact (hs.mono (Set.empty_subset _)).preimage_map
    (F := fun x => ![f x, g x])
    (by
      intro i
      fin_cases i
      · simpa using hf
      · simpa using hg)

end Closure

/-- An existential description of the positive-input inverse graph using only
the named generator, arithmetic, and order. -/
def InverseWitness (A : ℝ → ℝ) (t y : ℝ) (z : Fin 1 → ℝ) : Prop :=
  0 < t ∧ y = 1 + (z 0) ^ 2 ∧ C0 A (z 0) = t

/-- Four square witnesses encode two values of the exponential above one.
Their quotient gives the exponential at an arbitrary real input. -/
def ExponentialWitness (A : ℝ → ℝ) (x y : ℝ) (z : Fin 4 → ℝ) : Prop :=
  1 + (z 0) ^ 2 = x ^ 2 + 2 ∧
  1 + (z 1) ^ 2 = x ^ 2 + x + 2 ∧
  C0 A (z 2) = C0 A (z 0) + 1 ∧
  C0 A (z 3) = C0 A (z 1) + 1 ∧
  y * (2 + (z 2) ^ 2) = 2 + (z 3) ^ 2

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

theorem positive_inverse_iff_witness (t y : ℝ) :
    (0 < t ∧ y = inverse A t) ↔ ∃ z, InverseWitness A t y z := by
  constructor
  · rintro ⟨ht, rfl⟩
    have hy : 0 ≤ inverse A t - 1 := (sub_pos.mpr (hA.one_lt_inverse ht)).le
    refine ⟨![Real.sqrt (inverse A t - 1)], ht, ?_, ?_⟩
    · simp only [Matrix.cons_val_zero, Real.sq_sqrt hy]
      ring
    · simp only [C0, Matrix.cons_val_zero, Real.sq_sqrt hy]
      convert hA.apply_inverse t using 1
      congr 1
      ring
  · rintro ⟨z, ht, hy, hz⟩
    refine ⟨ht, ?_⟩
    have hpos : 0 < y := by rw [hy]; positivity
    apply (hA.inverse_eq_iff.mpr ⟨hpos, ?_⟩).symm
    simpa only [hy, C0] using hz

private theorem exp_eq_of_c0 {u v x : ℝ}
    (hx : 0 < x) (hu : 1 + u ^ 2 = x)
    (hv : C0 A v = C0 A u + 1) : 2 + v ^ 2 = Real.exp x := by
  have he : 1 + v ^ 2 = E x := by
    apply hA.injectiveOn (by change 0 < 1 + v ^ 2; positivity) (E_pos hx)
    simpa only [C0, hu, hA.abel x hx] using hv
  dsimp [E] at he
  linarith

theorem exponential_iff_witness (x y : ℝ) :
    y = Real.exp x ↔ ∃ z, ExponentialWitness A x y z := by
  have hbase : 1 < x ^ 2 + 2 := by nlinarith [sq_nonneg x]
  have hshift : 1 < x ^ 2 + x + 2 := by nlinarith [sq_nonneg (x + 1 / 2)]
  constructor
  · rintro rfl
    let a := x ^ 2 + 2
    let b := x ^ 2 + x + 2
    have ha : 0 < a := lt_trans zero_lt_one hbase
    have hb : 0 < b := lt_trans zero_lt_one hshift
    have hea : 0 ≤ E a - 1 := by have := lt_E ha; dsimp [a] at *; linarith
    have heb : 0 ≤ E b - 1 := by have := lt_E hb; dsimp [b] at *; linarith
    let u := Real.sqrt (a - 1)
    let v := Real.sqrt (b - 1)
    let r := Real.sqrt (E a - 1)
    let s := Real.sqrt (E b - 1)
    have hu : 1 + u ^ 2 = a := by
      dsimp [u]; rw [Real.sq_sqrt (by dsimp [a]; linarith)]; ring
    have hv : 1 + v ^ 2 = b := by
      dsimp [v]; rw [Real.sq_sqrt (by dsimp [b]; linarith)]; ring
    have hr : 1 + r ^ 2 = E a := by
      dsimp [r]; rw [Real.sq_sqrt hea]; ring
    have hs : 1 + s ^ 2 = E b := by
      dsimp [s]; rw [Real.sq_sqrt heb]; ring
    refine ⟨![u, v, r, s], hu, hv, ?_, ?_, ?_⟩
    · change C0 A r = C0 A u + 1
      simpa only [C0, hu, hr] using hA.abel a ha
    · change C0 A s = C0 A v + 1
      simpa only [C0, hv, hs] using hA.abel b hb
    · change Real.exp x * (2 + r ^ 2) = 2 + s ^ 2
      have hr' : 2 + r ^ 2 = Real.exp a := by dsimp [E] at hr; linarith
      have hs' : 2 + s ^ 2 = Real.exp b := by dsimp [E] at hs; linarith
      rw [hr', hs', ← Real.exp_add]
      congr 1
      dsimp [a, b]
      ring
  · rintro ⟨z, h0, h1, h2, h3, h4⟩
    have he0 := hA.exp_eq_of_c0 (lt_trans zero_lt_one hbase) h0 h2
    have he1 := hA.exp_eq_of_c0 (lt_trans zero_lt_one hshift) h1 h3
    rw [he0, he1] at h4
    have hexp : Real.exp (x ^ 2 + x + 2) = Real.exp x * Real.exp (x ^ 2 + 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp] at h4
    exact mul_right_cancel₀ (ne_of_gt (Real.exp_pos _)) h4

end IsAbel

section WitnessDefinability

variable (A : ℝ → ℝ)

private theorem inverseWitness_definable :
    @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _
      {v : Fin 2 ⊕ Fin 1 → ℝ |
        InverseWitness A (v (.inl 0)) (v (.inl 1)) (fun i => v (.inr i))} := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  have h0 : @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _
      {v : Fin 2 ⊕ Fin 1 → ℝ | 0 < v (.inl 0)} :=
    definable_lt A (by fun_prop) (by fun_prop)
  have h1 : @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _
      {v : Fin 2 ⊕ Fin 1 → ℝ | v (.inl 1) = 1 + v (.inr 0) ^ 2} :=
    Set.DefinableFun.ofPred_eq (by fun_prop) (by fun_prop)
  have h2 : @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _
      {v : Fin 2 ⊕ Fin 1 → ℝ | C0 A (v (.inr 0)) = v (.inl 0)} :=
    Set.DefinableFun.ofPred_eq (by fun_prop) (by fun_prop)
  exact h0.inter (h1.inter h2)

private theorem exponentialWitness_definable :
    @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _
      {v : Fin 2 ⊕ Fin 4 → ℝ |
        ExponentialWitness A (v (.inl 0)) (v (.inl 1)) (fun i => v (.inr i))} := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  have h0 : @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _
      {v : Fin 2 ⊕ Fin 4 → ℝ | 1 + v (.inr 0) ^ 2 = v (.inl 0) ^ 2 + 2} :=
    Set.DefinableFun.ofPred_eq (by fun_prop) (by fun_prop)
  have h1 : @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _
      {v : Fin 2 ⊕ Fin 4 → ℝ | 1 + v (.inr 1) ^ 2 = v (.inl 0) ^ 2 + v (.inl 0) + 2} :=
    Set.DefinableFun.ofPred_eq (by fun_prop) (by fun_prop)
  have h2 : @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _
      {v : Fin 2 ⊕ Fin 4 → ℝ | C0 A (v (.inr 2)) = C0 A (v (.inr 0)) + 1} :=
    Set.DefinableFun.ofPred_eq (by fun_prop) (by fun_prop)
  have h3 : @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _
      {v : Fin 2 ⊕ Fin 4 → ℝ | C0 A (v (.inr 3)) = C0 A (v (.inr 1)) + 1} :=
    Set.DefinableFun.ofPred_eq (by fun_prop) (by fun_prop)
  have h4 : @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _
      {v : Fin 2 ⊕ Fin 4 → ℝ | v (.inl 1) * (2 + v (.inr 2) ^ 2) = 2 + v (.inr 3) ^ 2} :=
    Set.DefinableFun.ofPred_eq (by fun_prop) (by fun_prop)
  exact h0.inter (h1.inter (h2.inter (h3.inter h4)))

end WitnessDefinability

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)

include hA

/-- The inverse restricted to positive input is definable from `C₀`. -/
theorem positiveInverseDefinable : PositiveInverseDefinable A (inverse A) := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  change @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _
    {v : Fin 2 → ℝ | 0 < v 0 ∧ v 1 = inverse A (v 0)}
  have h := (inverseWitness_definable A).exists_of_finite
  convert h using 1
  ext v
  exact hA.positive_inverse_iff_witness (v 0) (v 1)

/-- The usual exponential on all real inputs is definable from `C₀`. -/
theorem exponentialDefinable : ExponentialDefinable A := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  change @Set.Definable ℝ (Set.univ : Set ℝ) abelLanguage (abelStructure A) _
    {v : Fin 2 → ℝ | v 1 = Real.exp (v 0)}
  have h := (exponentialWitness_definable A).exists_of_finite
  convert h using 1
  ext v
  exact hA.exponential_iff_witness (v 0) (v 1)

end IsAbel

end AbelFormalization
