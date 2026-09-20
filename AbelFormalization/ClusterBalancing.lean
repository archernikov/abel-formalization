import AbelFormalization.FiniteHierarchy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Balancing bounded clusters of Abel times

This file formalizes the finite combinatorial step at the start of the proof
of `prop:separated` in the manuscript.  Starting with finitely many real
times above a fixed attained minimum, repeatedly subtract one from a current
maximum until every time lies in the half-open interval of length one above
that minimum.  The result retains the *ordered list* of changed coordinates:
each prefix therefore records the hypothesis needed by an individual
quantitative logarithmic transfer.

The second half is the infinite-pigeonhole argument used in the manuscript.
For a bounded-width sequence, it supplies one strictly increasing subsequence
on which both the whole change list and the final coordinate order are fixed.
The order uses `Tuple.sort`, hence ties are broken canonically by the original
index.

No property of an Abel function is needed for the balancing itself.  The last
lemma records the later use of the manuscript's positive integer-distance
condition: after integral shifts, distinct original times remain distinct.
-/

noncomputable section

namespace AbelFormalization

open Function Set
open scoped BigOperators

universe u

/-- The times after performing, in order, all unit decrements in `steps`.
The number of occurrences of a coordinate is exactly its logarithmic shift
count. -/
def clusterShiftedTimes {ι : Type u} [DecidableEq ι]
    (a : ι → ℝ) (steps : List ι) : ι → ℝ :=
  fun i => a i - (steps.count i : ℝ)

@[simp]
theorem clusterShiftedTimes_nil {ι : Type u} [DecidableEq ι]
    (a : ι → ℝ) :
    clusterShiftedTimes a [] = a := by
  funext i
  simp [clusterShiftedTimes]

/-- Prepending a decrement is the same as first updating that coordinate by
minus one and then carrying out the remaining decrements. -/
@[simp]
theorem clusterShiftedTimes_cons {ι : Type u} [DecidableEq ι]
    (a : ι → ℝ) (i : ι) (steps : List ι) :
    clusterShiftedTimes a (i :: steps) =
      clusterShiftedTimes (Function.update a i (a i - 1)) steps := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [clusterShiftedTimes]
    ring
  · simp [clusterShiftedTimes, hji, Ne.symm hji]

/-- A complete trace of the balancing algorithm.  `base` is a fixed lower
bound for all current times (in the application, the original cluster
minimum).  The two prefix fields say that every recorded change is legal:
the selected coordinate is a current maximum and is still at least one above
`base`. -/
structure ClusterBalancingPlan {ι : Type u} [DecidableEq ι]
    (a : ι → ℝ) (base : ℝ) where
  steps : List ι
  chosen_is_currentMaximum :
    ∀ pre step suffix, steps = pre ++ step :: suffix →
      ∀ j, clusterShiftedTimes a pre j ≤
        clusterShiftedTimes a pre step
  chosen_is_oneAboveBase :
    ∀ pre step suffix, steps = pre ++ step :: suffix →
      base + 1 ≤ clusterShiftedTimes a pre step
  base_le_final : ∀ i, base ≤ clusterShiftedTimes a steps i
  final_lt_base_add_one : ∀ i, clusterShiftedTimes a steps i < base + 1
  count_le_natFloor : ∀ i, steps.count i ≤ ⌊a i - base⌋₊

/- The trace records only the mathematically used condition that a step is a
current maximum.  The manuscript's index tie-break is one deterministic way
to choose such a trace; arbitrary classical choice followed by the finite
pigeonhole argument gives the same fixed-list conclusion. -/

namespace ClusterBalancingPlan

variable {ι : Type u} [DecidableEq ι]
variable {a : ι → ℝ} {base : ℝ}

/-- The final balanced time vector. -/
def finalTimes (p : ClusterBalancingPlan a base) : ι → ℝ :=
  clusterShiftedTimes a p.steps

/-- Every pair of final times differs by less than one in this orientation.
Together with the swapped statement, this is exactly `max - min < 1`. -/
theorem final_sub_lt_one (p : ClusterBalancingPlan a base) (i j : ι) :
    p.finalTimes i - p.finalTimes j < 1 := by
  dsimp [finalTimes]
  linarith [p.final_lt_base_add_one i, p.base_le_final j]

/-- A coordinate initially equal to `base` is never changed.  This is the
formal version of the manuscript's observation that an original-minimum
coordinate need never be lowered. -/
theorem count_eq_zero_of_eq_base (p : ClusterBalancingPlan a base)
    {i : ι} (hi : a i = base) :
    p.steps.count i = 0 := by
  have h := p.count_le_natFloor i
  rw [hi, sub_self, Nat.floor_zero] at h
  exact Nat.eq_zero_of_le_zero h

/-- Consequently, an attained original minimum remains an attained minimum
of the final vector. -/
theorem finalTimes_eq_base_of_eq_base (p : ClusterBalancingPlan a base)
    {i : ι} (hi : a i = base) :
    p.finalTimes i = base := by
  simp [finalTimes, clusterShiftedTimes, p.count_eq_zero_of_eq_base hi, hi]

end ClusterBalancingPlan

/-- The natural measure used to terminate balancing: the sum of the integral
parts of all heights above `base`. -/
private def clusterBalancingPotential {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (base : ℝ) : ℕ :=
  ∑ i, ⌊a i - base⌋₊

/-- Every finite family lying above `base` has a legal balancing trace.
When `base` is the attained original minimum, this is precisely the
manuscript's "lower a largest current time by one" construction. -/
theorem exists_clusterBalancingPlan {ι : Type u}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ι → ℝ) (base : ℝ) (hbase : ∀ i, base ≤ a i) :
    Nonempty (ClusterBalancingPlan a base) := by
  have inductionStatement :
      ∀ n : ℕ, ∀ a : ι → ℝ,
        clusterBalancingPotential a base = n →
        (∀ i, base ≤ a i) →
        Nonempty (ClusterBalancingPlan a base) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro a hpotential hbase
        by_cases hdone : ∀ i, a i < base + 1
        · refine ⟨{
            steps := []
            chosen_is_currentMaximum := ?_
            chosen_is_oneAboveBase := ?_
            base_le_final := ?_
            final_lt_base_add_one := ?_
            count_le_natFloor := ?_ }⟩
          · intro pre step suffix heq
            simp at heq
          · intro pre step suffix heq
            simp at heq
          · simpa [clusterShiftedTimes] using hbase
          · simpa [clusterShiftedTimes] using hdone
          · intro i
            simp
        · push_neg at hdone
          obtain ⟨imax, himax⟩ := Finite.exists_max a
          obtain ⟨j, hj⟩ := hdone
          have hiAbove : base + 1 ≤ a imax := hj.trans (himax j)
          let a' : ι → ℝ := Function.update a imax (a imax - 1)
          have hbase' : ∀ i, base ≤ a' i := by
            intro i
            by_cases hi : i = imax
            · subst i
              simp [a']
              linarith
            · simpa [a', hi] using hbase i
          have hpotential_lt :
              clusterBalancingPotential a' base <
                clusterBalancingPotential a base := by
            unfold clusterBalancingPotential
            apply Finset.sum_lt_sum
            · intro i hi
              apply Nat.floor_mono
              by_cases hii : i = imax
              · subst i
                simp [a']
              · simp [a', hii]
            · refine ⟨imax, Finset.mem_univ imax, ?_⟩
              simp only [a', Function.update_self]
              rw [show a imax - 1 - base = (a imax - base) - 1 by ring,
                Nat.floor_sub_one]
              exact Nat.sub_one_lt
                (ne_of_gt (Nat.floor_pos.mpr (by linarith)))
          have hpotential_lt_n : clusterBalancingPotential a' base < n := by
            simpa only [hpotential] using hpotential_lt
          obtain ⟨tail⟩ :=
            ih (clusterBalancingPotential a' base) hpotential_lt_n
              a' rfl hbase'
          refine ⟨{
              steps := imax :: tail.steps
              chosen_is_currentMaximum := ?_
              chosen_is_oneAboveBase := ?_
              base_le_final := ?_
              final_lt_base_add_one := ?_
              count_le_natFloor := ?_ }⟩
          · intro pre step suffix heq j
            cases pre with
            | nil =>
                simp only [List.nil_append] at heq
                injection heq with hstep hsuffix
                subst step
                simpa [clusterShiftedTimes] using himax j
            | cons first pre =>
                simp only [List.cons_append] at heq
                injection heq with hfirst htail
                subst first
                have h := tail.chosen_is_currentMaximum
                  pre step suffix htail j
                simpa [a'] using h
          · intro pre step suffix heq
            cases pre with
            | nil =>
                simp only [List.nil_append] at heq
                injection heq with hstep hsuffix
                subst step
                simpa [clusterShiftedTimes] using hiAbove
            | cons first pre =>
                simp only [List.cons_append] at heq
                injection heq with hfirst htail
                subst first
                have h := tail.chosen_is_oneAboveBase
                  pre step suffix htail
                simpa [a'] using h
          · simpa [a'] using tail.base_le_final
          · simpa [a'] using tail.final_lt_base_add_one
          · intro i
            by_cases hi : i = imax
            · subst i
              have hcount := tail.count_le_natFloor imax
              simp only [a', Function.update_self] at hcount
              rw [show a imax - 1 - base = (a imax - base) - 1 by ring,
                Nat.floor_sub_one] at hcount
              have hfloor : 0 < ⌊a imax - base⌋₊ :=
                Nat.floor_pos.mpr (by linarith)
              simp only [List.count_cons_self]
              omega
            · have hcount := tail.count_le_natFloor i
              simp [a', hi] at hcount
              simpa [hi, Ne.symm hi] using hcount
  exact inductionStatement (clusterBalancingPotential a base) a rfl hbase

/-- The per-coordinate floor bound implies the manuscript's uniform length
bound.  The paper uses the deliberately loose factor `floor Cstar + 1`; the
construction above actually gives `floor Cstar`. -/
theorem ClusterBalancingPlan.length_le_card_mul_natFloor_add_one
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    {a : ι → ℝ} {base Cstar : ℝ}
    (p : ClusterBalancingPlan a base)
    (hwidth : ∀ i, a i - base ≤ Cstar) :
    p.steps.length ≤ Fintype.card ι * (⌊Cstar⌋₊ + 1) := by
  calc
    p.steps.length = p.steps.toFinset.sum (fun i => p.steps.count i) :=
      (List.sum_toFinset_count_eq_length p.steps).symm
    _ ≤ p.steps.toFinset.sum (fun _i => ⌊Cstar⌋₊ + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (p.count_le_natFloor i).trans
        ((Nat.floor_mono (hwidth i)).trans (Nat.le_add_right _ _))
    _ = p.steps.toFinset.card * (⌊Cstar⌋₊ + 1) := by simp
    _ ≤ Fintype.card ι * (⌊Cstar⌋₊ + 1) := by
      exact Nat.mul_le_mul_right _ (Finset.card_le_univ _)

/-! ## Canonical final order -/

/-- The final coordinates in decreasing order, with equal values broken by
the original `Fin` index through `Tuple.sort`'s graph order. -/
def ClusterBalancingPlan.finalOrder {n : ℕ} [DecidableEq (Fin n)]
    {a : Fin n → ℝ} {base : ℝ} (p : ClusterBalancingPlan a base) :
    Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => -p.finalTimes i)

/-- The canonical final order is nonincreasing in the balanced times. -/
theorem ClusterBalancingPlan.antitone_finalTimes_comp_finalOrder
    {n : ℕ} [DecidableEq (Fin n)]
    {a : Fin n → ℝ} {base : ℝ} (p : ClusterBalancingPlan a base) :
    Antitone (p.finalTimes ∘ p.finalOrder) := by
  have h := Tuple.monotone_sort (fun i : Fin n => -p.finalTimes i)
  intro i j hij
  have hij' := h hij
  simp only [Function.comp_apply] at hij'
  change p.finalTimes (p.finalOrder j) ≤
    p.finalTimes (p.finalOrder i)
  change -p.finalTimes (p.finalOrder i) ≤
    -p.finalTimes (p.finalOrder j) at hij'
  linarith

/-! ## Infinite-pigeonhole selection -/

/-- Any sequence with values in a finite type is constant on a strictly
increasing subsequence.  This is the precise infinite-pigeonhole wrapper used
for the finite plan/order codes below. -/
theorem exists_strictMono_subsequence_const_of_finite
    {β : Type u} [Finite β] (f : ℕ → β) :
    ∃ (φ : ℕ → ℕ) (b : β), StrictMono φ ∧ ∀ n, f (φ n) = b := by
  obtain ⟨b, hb⟩ := Finite.exists_infinite_fiber f
  have hbSet : (f ⁻¹' ({b} : Set β)).Infinite :=
    Set.infinite_coe_iff.mp hb
  have hunbounded : ∀ N : ℕ, ∃ n > N, f n = b := by
    intro N
    obtain ⟨n, hnmem, hnN⟩ := hbSet.exists_gt N
    exact ⟨n, hnN, by simpa using hnmem⟩
  obtain ⟨φ, hφ, hfixed⟩ := Nat.exists_strictMono_subsequence hunbounded
  exact ⟨φ, b, hφ, hfixed⟩

/-- Along a bounded-width sequence of one nonempty cluster, choose all
balancing traces and then pass to a single subsequence on which the complete
change list and the canonical final order are fixed.  The theorem uses
`Fin (h+1)` so it feeds directly into the finite hierarchy theorems. -/
theorem exists_fixed_clusterBalancing_subsequence {h : ℕ}
    (a : ℕ → Fin (h + 1) → ℝ) (base : ℕ → ℝ) (Cstar : ℝ)
    (hbase : ∀ n i, base n ≤ a n i)
    (hwidth : ∀ n i, a n i - base n ≤ Cstar) :
    ∃ (φ : ℕ → ℕ) (fixedSteps : List (Fin (h + 1)))
        (fixedOrder : Equiv.Perm (Fin (h + 1)))
        (plans : ∀ n, ClusterBalancingPlan (a (φ n)) (base (φ n))),
      StrictMono φ ∧
      fixedSteps.length ≤ (h + 1) * (⌊Cstar⌋₊ + 1) ∧
      (∀ n, (plans n).steps = fixedSteps) ∧
      (∀ n, (plans n).finalOrder = fixedOrder) := by
  classical
  let rawPlan : ∀ n, ClusterBalancingPlan (a n) (base n) :=
    fun n => Classical.choice
      (exists_clusterBalancingPlan (a n) (base n) (hbase n))
  let B : ℕ := (h + 1) * (⌊Cstar⌋₊ + 1)
  have hlength (n : ℕ) : (rawPlan n).steps.length ≤ B := by
    simpa [B] using
      (rawPlan n).length_le_card_mul_natFloor_add_one (hwidth n)
  let Code :=
    {steps : List (Fin (h + 1)) // steps.length ≤ B} ×
      Equiv.Perm (Fin (h + 1))
  letI : Fintype {steps : List (Fin (h + 1)) // steps.length ≤ B} :=
    (List.finite_length_le (Fin (h + 1)) B).fintype
  let code : ℕ → Code := fun n =>
    (⟨(rawPlan n).steps, hlength n⟩, (rawPlan n).finalOrder)
  obtain ⟨φ, fixedCode, hφ, hcode⟩ :=
    exists_strictMono_subsequence_const_of_finite code
  let fixedSteps : List (Fin (h + 1)) := fixedCode.1.1
  let fixedOrder : Equiv.Perm (Fin (h + 1)) := fixedCode.2
  let plans : ∀ n, ClusterBalancingPlan (a (φ n)) (base (φ n)) :=
    fun n => rawPlan (φ n)
  refine ⟨φ, fixedSteps, fixedOrder, plans, hφ, ?_, ?_, ?_⟩
  · exact fixedCode.1.2
  · intro n
    exact congrArg (fun c : Code => c.1.1) (hcode n)
  · intro n
    exact congrArg (fun c : Code => c.2) (hcode n)

/-- The same conclusion in the manuscript's `infinite Λ` form.  Membership
in `Λ` retains a dependent plan witness, while the list and final order are
literal fixed data. -/
theorem exists_infinite_set_fixed_clusterBalancing {h : ℕ}
    (a : ℕ → Fin (h + 1) → ℝ) (base : ℕ → ℝ) (Cstar : ℝ)
    (hbase : ∀ n i, base n ≤ a n i)
    (hwidth : ∀ n i, a n i - base n ≤ Cstar) :
    ∃ (Λ : Set ℕ) (fixedSteps : List (Fin (h + 1)))
        (fixedOrder : Equiv.Perm (Fin (h + 1))),
      Λ.Infinite ∧
      fixedSteps.length ≤ (h + 1) * (⌊Cstar⌋₊ + 1) ∧
      ∀ n ∈ Λ, ∃ p : ClusterBalancingPlan (a n) (base n),
        p.steps = fixedSteps ∧ p.finalOrder = fixedOrder := by
  obtain ⟨φ, fixedSteps, fixedOrder, plans, hφ, hlength, hsteps, horder⟩ :=
    exists_fixed_clusterBalancing_subsequence a base Cstar hbase hwidth
  refine ⟨Set.range φ, fixedSteps, fixedOrder,
    Set.infinite_range_of_injective hφ.injective, hlength, ?_⟩
  rintro n ⟨r, rfl⟩
  exact ⟨plans r, hsteps r, horder r⟩

/-- Simultaneous finite-cluster version.  Cluster `c` has `h c + 1`
coordinates.  A single subsequence fixes every cluster's complete balancing
list and final permutation at once; this is the exact finite choice made in
the first paragraph of the proof of `prop:separated`. -/
theorem exists_simultaneously_fixed_clusterBalancing_subsequence
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    (h : κ → ℕ)
    (a : ℕ → (c : κ) → Fin (h c + 1) → ℝ)
    (base : ℕ → κ → ℝ) (Cstar : ℝ)
    (hbase : ∀ n c i, base n c ≤ a n c i)
    (hwidth : ∀ n c i, a n c i - base n c ≤ Cstar) :
    ∃ (φ : ℕ → ℕ)
        (fixedSteps : ∀ c, List (Fin (h c + 1)))
        (fixedOrder : ∀ c, Equiv.Perm (Fin (h c + 1)))
        (plans : ∀ n c,
          ClusterBalancingPlan (a (φ n) c) (base (φ n) c)),
      StrictMono φ ∧
      (∀ c, (fixedSteps c).length ≤
        (h c + 1) * (⌊Cstar⌋₊ + 1)) ∧
      (∀ n c, (plans n c).steps = fixedSteps c) ∧
      (∀ n c, (plans n c).finalOrder = fixedOrder c) := by
  classical
  let rawPlan : ∀ n c,
      ClusterBalancingPlan (a n c) (base n c) :=
    fun n c => Classical.choice
      (exists_clusterBalancingPlan (a n c) (base n c) (hbase n c))
  let B : κ → ℕ := fun c => (h c + 1) * (⌊Cstar⌋₊ + 1)
  have hlength (n : ℕ) (c : κ) :
      (rawPlan n c).steps.length ≤ B c := by
    simpa [B] using
      (rawPlan n c).length_le_card_mul_natFloor_add_one (hwidth n c)
  let CodeAt (c : κ) :=
    {steps : List (Fin (h c + 1)) // steps.length ≤ B c} ×
      Equiv.Perm (Fin (h c + 1))
  letI : ∀ c, Fintype
      {steps : List (Fin (h c + 1)) // steps.length ≤ B c} :=
    fun c => (List.finite_length_le (Fin (h c + 1)) (B c)).fintype
  let code : ℕ → (∀ c, CodeAt c) := fun n c =>
    (⟨(rawPlan n c).steps, hlength n c⟩, (rawPlan n c).finalOrder)
  obtain ⟨φ, fixedCode, hφ, hcode⟩ :=
    exists_strictMono_subsequence_const_of_finite code
  let fixedSteps : ∀ c, List (Fin (h c + 1)) :=
    fun c => (fixedCode c).1.1
  let fixedOrder : ∀ c, Equiv.Perm (Fin (h c + 1)) :=
    fun c => (fixedCode c).2
  let plans : ∀ n c,
      ClusterBalancingPlan (a (φ n) c) (base (φ n) c) :=
    fun n c => rawPlan (φ n) c
  refine ⟨φ, fixedSteps, fixedOrder, plans, hφ, ?_, ?_, ?_⟩
  · intro c
    exact (fixedCode c).1.2
  · intro n c
    have hc := congrFun (hcode n) c
    exact congrArg (fun x : CodeAt c => x.1.1) hc
  · intro n c
    have hc := congrFun (hcode n) c
    exact congrArg (fun x : CodeAt c => x.2) hc

/-- Infinite-set form of the simultaneous selector, matching the quantifier
shape used in `prop:separated`. -/
theorem exists_infinite_set_simultaneously_fixed_clusterBalancing
    {κ : Type u} [Fintype κ] [DecidableEq κ]
    (h : κ → ℕ)
    (a : ℕ → (c : κ) → Fin (h c + 1) → ℝ)
    (base : ℕ → κ → ℝ) (Cstar : ℝ)
    (hbase : ∀ n c i, base n c ≤ a n c i)
    (hwidth : ∀ n c i, a n c i - base n c ≤ Cstar) :
    ∃ (Λ : Set ℕ)
        (fixedSteps : ∀ c, List (Fin (h c + 1)))
        (fixedOrder : ∀ c, Equiv.Perm (Fin (h c + 1))),
      Λ.Infinite ∧
      (∀ c, (fixedSteps c).length ≤
        (h c + 1) * (⌊Cstar⌋₊ + 1)) ∧
      ∀ n ∈ Λ,
        ∃ plans : ∀ c,
            ClusterBalancingPlan (a n c) (base n c),
          (∀ c, (plans c).steps = fixedSteps c) ∧
          (∀ c, (plans c).finalOrder = fixedOrder c) := by
  obtain ⟨φ, fixedSteps, fixedOrder, plans, hφ, hlength, hsteps, horder⟩ :=
    exists_simultaneously_fixed_clusterBalancing_subsequence
      h a base Cstar hbase hwidth
  refine ⟨Set.range φ, fixedSteps, fixedOrder,
    Set.infinite_range_of_injective hφ.injective, hlength, ?_⟩
  rintro n ⟨r, rfl⟩
  exact ⟨fun c => plans r c, hsteps r, horder r⟩

/-- Summing the per-cluster bounds gives the manuscript's global bound.  In
the application `∑ c, (h c + 1)` is the total number `m` of representatives. -/
theorem sum_clusterBalancing_lengths_le
    {κ : Type u} [Fintype κ] (h : κ → ℕ)
    (steps : ∀ c, List (Fin (h c + 1))) (Cstar : ℝ)
    (hlength : ∀ c, (steps c).length ≤
      (h c + 1) * (⌊Cstar⌋₊ + 1)) :
    (∑ c, (steps c).length) ≤
      (∑ c, (h c + 1)) * (⌊Cstar⌋₊ + 1) := by
  calc
    (∑ c, (steps c).length) ≤
        ∑ c, (h c + 1) * (⌊Cstar⌋₊ + 1) := by
      exact Finset.sum_le_sum fun c _ => hlength c
    _ = (∑ c, (h c + 1)) * (⌊Cstar⌋₊ + 1) := by
      rw [Finset.sum_mul]

/-! ## Strictness supplied by the separation set -/

/-- A positive distance from the original difference to the integers prevents
two coordinates from becoming equal after any integral shift counts. -/
theorem clusterShiftedTimes_ne_of_integerDistance_pos
    {ι : Type u} [DecidableEq ι] (a : ι → ℝ) (steps : List ι)
    {i j : ι} (hsep : 0 < integerDistance (a i - a j)) :
    clusterShiftedTimes a steps i ≠ clusterShiftedTimes a steps j := by
  intro heq
  let z : ℤ := (steps.count i : ℤ) - (steps.count j : ℤ)
  have hz : integerDistance (a i - a j) ≤
      |a i - a j - (z : ℝ)| :=
    (le_integerDistance_iff.mp
      (le_refl (integerDistance (a i - a j)))) z
  have hzero : a i - a j - (z : ℝ) = 0 := by
    dsimp [z]
    push_cast
    dsimp [clusterShiftedTimes] at heq
    linarith
  rw [hzero, abs_zero] at hz
  linarith

/-- Therefore any weakly decreasing enumeration of the balanced times is
strictly decreasing whenever distinct original coordinates have positive
integer distance.  This is the exact bridge from balancing to the hierarchy
hypothesis on the manuscript's set `Gamma_N`. -/
theorem ClusterBalancingPlan.strictAnti_finalTimes_comp_of_separated
    {n : ℕ} [DecidableEq (Fin n)] {a : Fin n → ℝ} {base : ℝ}
    (p : ClusterBalancingPlan a base) (σ : Equiv.Perm (Fin n))
    (hσ : Antitone (p.finalTimes ∘ σ))
    (hsep : ∀ i j : Fin n, i ≠ j →
      0 < integerDistance (a i - a j)) :
    StrictAnti (p.finalTimes ∘ σ) := by
  intro i j hij
  have hle := hσ hij.le
  exact hle.lt_of_ne fun heq =>
    clusterShiftedTimes_ne_of_integerDistance_pos a p.steps
      (hsep (σ i) (σ j) (σ.injective.ne hij.ne)) heq.symm

/-- Canonical-order specialization of
`strictAnti_finalTimes_comp_of_separated`. -/
theorem ClusterBalancingPlan.strictAnti_finalTimes_comp_finalOrder_of_separated
    {n : ℕ} [DecidableEq (Fin n)] {a : Fin n → ℝ} {base : ℝ}
    (p : ClusterBalancingPlan a base)
    (hsep : ∀ i j : Fin n, i ≠ j →
      0 < integerDistance (a i - a j)) :
    StrictAnti (p.finalTimes ∘ p.finalOrder) :=
  p.strictAnti_finalTimes_comp_of_separated p.finalOrder
    p.antitone_finalTimes_comp_finalOrder hsep

end AbelFormalization
