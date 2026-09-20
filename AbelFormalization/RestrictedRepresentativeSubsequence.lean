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

open Filter Set Topology

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

/-- Further subsequencing simultaneously classifies every representative
coordinate while preserving injectivity, regular-zero membership, and a
previously obtained limit of the bounded-box coordinate. -/
theorem exists_regularZero_subsequence_representatives_classified
    {m p a : ℕ} {D : RestrictedBox p} {R : ℝ}
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : RestrictedSource m p a → Y}
    (x : ℕ → RestrictedSource m p a) (w₀ : RestrictedBoxSpace p)
    (hxinj : Function.Injective x)
    (hxmem : ∀ n, x n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) F)
    (hw : Tendsto (fun n ↦ (x n).1.2) atTop (𝓝 w₀)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Function.Injective (fun n ↦ x (φ n)) ∧
      (∀ n, x (φ n) ∈ regularZeroSet
        (restrictedBaseOpenDomain D R) F) ∧
      Tendsto (fun n ↦ (x (φ n)).1.2) atTop (𝓝 w₀) ∧
      ∀ i, BddAbove (Set.range (fun n ↦ (x (φ n)).1.1 i)) ∨
        Tendsto (fun n ↦ (x (φ n)).1.1 i) atTop atTop := by
  obtain ⟨φ, hφ, hclass⟩ :=
    exists_strictMono_subsequence_representatives_classified
      (fun n i ↦ (x n).1.1 i)
  refine ⟨φ, hφ, hxinj.comp hφ.injective, fun n ↦ hxmem (φ n), ?_, hclass⟩
  change Tendsto ((fun n ↦ (x n).1.2) ∘ φ) atTop (𝓝 w₀)
  exact hw.comp hφ.tendsto_atTop

/-- Every infinite restricted regular-zero set supplies the fully normalized
sequence used at the start of the manuscript's outer induction: the bounded
coordinate converges in the closed box and every representative coordinate
is bounded above or tends to positive infinity. -/
theorem Set.Infinite.exists_classified_restrictedRegularZeroSequence
    {m p a : ℕ} {D : RestrictedBox p} {R : ℝ}
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : RestrictedSource m p a → Y}
    (hZ : (regularZeroSet (restrictedBaseOpenDomain D R) F).Infinite) :
    ∃ x : ℕ → RestrictedSource m p a, ∃ w₀ : RestrictedBoxSpace p,
      Function.Injective x ∧
      (∀ n, x n ∈ regularZeroSet (restrictedBaseOpenDomain D R) F) ∧
      w₀ ∈ D.closedBox ∧
      Tendsto (fun n ↦ (x n).1.2) atTop (𝓝 w₀) ∧
      ∀ i, BddAbove (Set.range (fun n ↦ (x n).1.1 i)) ∨
        Tendsto (fun n ↦ (x n).1.1 i) atTop atTop := by
  classical
  let e : ℕ ↪ regularZeroSet (restrictedBaseOpenDomain D R) F :=
    hZ.natEmbedding
  let z : ℕ → RestrictedSource m p a := fun n ↦ (e n : _)
  have hzinj : Function.Injective z := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  have hzmem : ∀ n, z n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) F := fun n ↦ (e n).property
  have hwmem : ∀ n, (z n).1.2 ∈ D.closedBox := fun n ↦
    D.openBox_subset_closedBox (hzmem n).1.2
  obtain ⟨w₀, hw₀, ψ, hψ, hlim⟩ :=
    D.isCompact_closedBox.tendsto_subseq hwmem
  let y : ℕ → RestrictedSource m p a := fun n ↦ z (ψ n)
  have hyinj : Function.Injective y := hzinj.comp hψ.injective
  have hymem : ∀ n, y n ∈ regularZeroSet
      (restrictedBaseOpenDomain D R) F := fun n ↦ hzmem (ψ n)
  have hylim : Tendsto (fun n ↦ (y n).1.2) atTop (𝓝 w₀) := by
    change Tendsto ((fun n ↦ (z n).1.2) ∘ ψ) atTop (𝓝 w₀)
    exact hlim
  obtain ⟨φ, hφ, hxinj, hxmem, hxlim, hclass⟩ :=
    exists_regularZero_subsequence_representatives_classified
      y w₀ hyinj hymem hylim
  exact ⟨fun n ↦ y (φ n), w₀, hxinj, hxmem, hw₀, hxlim, hclass⟩

end AbelFormalization
