import AbelFormalization.RestrictedOrderedClusterPartition

noncomputable section
set_option autoImplicit false

open Set

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

/-- The representative blocks belonging to the first `k` ordered clusters.
These are exactly the variables retained while the clusters are eliminated
from largest to smallest. -/
def OrderedClusterPrefixBlock
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) (k : ℕ) :=
  {i : Fin m // ∃ c : Fin data.orderedClusterCount,
    c.val < k ∧ i ∈ data.orderedCluster c}

noncomputable instance orderedClusterPrefixBlockFintype
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) (k : ℕ) :
    Fintype (data.OrderedClusterPrefixBlock k) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Every representative belongs to the prefix containing all ordered
clusters. -/
theorem mem_orderedClusterPrefixBlock_top
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) (i : Fin m) :
    ∃ c : Fin data.orderedClusterCount,
      c.val < data.orderedClusterCount ∧
        i ∈ data.orderedCluster c := by
  obtain ⟨c, hc⟩ := data.exists_mem_orderedCluster i
  exact ⟨c, c.isLt, hc⟩

/-- The full prefix is canonically equivalent to the original representative
index type. -/
def orderedClusterPrefixTopEquiv
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) :
    Fin m ≃ data.OrderedClusterPrefixBlock data.orderedClusterCount where
  toFun i := ⟨i, data.mem_orderedClusterPrefixBlock_top i⟩
  invFun i := i.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

/-- Removing the active cluster from the `(c+1)`-prefix leaves the
`c`-prefix. -/
theorem mem_orderedClusterPrefixBlock_of_mem_succ_of_not_mem
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) {i : Fin m}
    (hiPrefix : ∃ d : Fin data.orderedClusterCount,
      d.val < c.val + 1 ∧ i ∈ data.orderedCluster d)
    (hiActive : i ∉ data.orderedCluster c) :
    ∃ d : Fin data.orderedClusterCount,
      d.val < c.val ∧ i ∈ data.orderedCluster d := by
  obtain ⟨d, hdlt, hid⟩ := hiPrefix
  have hne : d.val ≠ c.val := by
    intro h
    have hdc : d = c := Fin.ext h
    subst d
    exact hiActive hid
  have hdltc : d.val < c.val := by omega
  exact ⟨d, hdltc, hid⟩

/-- A prefix decomposes into its last (active) cluster and the strictly
smaller-cluster prefix. -/
def orderedClusterPrefixSuccEquiv
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    data.OrderedClusterPrefixBlock (c.val + 1) ≃
      Fin (data.orderedCluster c).card ⊕
        data.OrderedClusterPrefixBlock c.val where
  toFun i := by
    classical
    by_cases hi : i.1 ∈ data.orderedCluster c
    · exact Sum.inl ((data.orderedCluster c).equivFin ⟨i.1, hi⟩)
    · exact Sum.inr ⟨i.1,
        data.mem_orderedClusterPrefixBlock_of_mem_succ_of_not_mem
          c i.2 hi⟩
  invFun
    | Sum.inl i =>
        ⟨(((data.orderedCluster c).equivFin).symm i).1,
          ⟨c, Nat.lt_succ_self c.val,
            (((data.orderedCluster c).equivFin).symm i).2⟩⟩
    | Sum.inr i =>
        ⟨i.1, by
          obtain ⟨d, hdlt, hid⟩ := i.2
          exact ⟨d, hdlt.trans (Nat.lt_succ_self c.val), hid⟩⟩
  left_inv := by
    classical
    intro i
    by_cases hi : i.1 ∈ data.orderedCluster c
    · simp only [hi, dite_true]
      apply Subtype.ext
      simp
    · simp only [hi, dite_false]
      exact Subtype.ext rfl
  right_inv := by
    classical
    rintro (i | i)
    · have hi : (((data.orderedCluster c).equivFin).symm i).1 ∈
          data.orderedCluster c :=
        (((data.orderedCluster c).equivFin).symm i).2
      simp only [hi, dite_true]
      congr 1
      simpa only using (data.orderedCluster c).equivFin.apply_symm_apply i
    · obtain ⟨d, hdlt, hid⟩ := i.2
      have hnot : i.1 ∉ data.orderedCluster c := by
        intro hic
        exact Finset.disjoint_left.mp
          (data.orderedCluster_disjoint (ne_of_lt hdlt)) hid hic
      simp only [hnot, dite_false]
      exact congrArg Sum.inr (Subtype.ext rfl)

/-- The zero prefix has no representative blocks. -/
def orderedClusterPrefixZeroEquiv
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) :
    data.OrderedClusterPrefixBlock 0 ≃ Fin 0 where
  toFun i := ⟨i.1.val, by
    obtain ⟨c, hc, _⟩ := i.2
    omega⟩
  invFun i := Fin.elim0 i
  left_inv i := Fin.elim0
    ⟨i.1.val, by
      obtain ⟨c, hc, _⟩ := i.2
      omega⟩
  right_inv i := Fin.elim0 i

/-- Cardinality recurrence for ordered-cluster prefixes. -/
theorem card_orderedClusterPrefixBlock_succ
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    Fintype.card (data.OrderedClusterPrefixBlock (c.val + 1)) =
      (data.orderedCluster c).card +
        Fintype.card (data.OrderedClusterPrefixBlock c.val) := by
  rw [Fintype.card_congr (data.orderedClusterPrefixSuccEquiv c),
    Fintype.card_sum, Fintype.card_fin]

@[simp]
theorem card_orderedClusterPrefixBlock_top
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) :
    Fintype.card
        (data.OrderedClusterPrefixBlock data.orderedClusterCount) = m := by
  simpa using
    (Fintype.card_congr data.orderedClusterPrefixTopEquiv).symm

@[simp]
theorem card_orderedClusterPrefixBlock_zero
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) :
    Fintype.card (data.OrderedClusterPrefixBlock 0) = 0 := by
  rw [Fintype.card_congr data.orderedClusterPrefixZeroEquiv,
    Fintype.card_fin]

end RepresentativeClusterSubsequence
end AbelFormalization
