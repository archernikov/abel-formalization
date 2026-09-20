import AbelFormalization.OrderedClusterPrefixAlgebraicStep
import AbelFormalization.SeparatedClustersReduction

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

universe u

/-- Size of the ordered cluster at a natural index, extended by zero beyond
the actual finite cluster list. -/
def orderedClusterSize
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) (k : ℕ) : ℕ :=
  if hk : k < data.orderedClusterCount then
    (data.orderedCluster ⟨k, hk⟩).card
  else 0

/-- Total number of representative blocks in the first `k` ordered
clusters. -/
def orderedClusterPrefixSize
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) (k : ℕ) : ℕ :=
  (Finset.range k).sum data.orderedClusterSize

@[simp]
theorem orderedClusterPrefixSize_zero
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) :
    data.orderedClusterPrefixSize 0 = 0 := by
  simp [orderedClusterPrefixSize]

theorem orderedClusterPrefixSize_succ
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    {k : ℕ} (hk : k < data.orderedClusterCount) :
    data.orderedClusterPrefixSize (k + 1) =
      data.orderedClusterPrefixSize k +
        (data.orderedCluster ⟨k, hk⟩).card := by
  unfold orderedClusterPrefixSize
  rw [Finset.sum_range_succ]
  congr 1
  exact dif_pos hk

/-- The prefix block type has cardinality equal to the sum of the sizes of
the clusters in that prefix. -/
theorem orderedClusterPrefixSize_eq_card
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (k : ℕ) (hk : k ≤ data.orderedClusterCount) :
    data.orderedClusterPrefixSize k =
      Fintype.card (data.OrderedClusterPrefixBlock k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < data.orderedClusterCount := by omega
      let c : Fin data.orderedClusterCount := ⟨k, hklt⟩
      calc
        data.orderedClusterPrefixSize (k + 1) =
            data.orderedClusterPrefixSize k +
              (data.orderedCluster c).card := by
          simpa only [c] using data.orderedClusterPrefixSize_succ hklt
        _ = Fintype.card (data.OrderedClusterPrefixBlock k) +
              (data.orderedCluster c).card := by
          rw [ih (Nat.le_of_lt hklt)]
        _ = (data.orderedCluster c).card +
              Fintype.card (data.OrderedClusterPrefixBlock k) :=
          Nat.add_comm _ _
        _ = Fintype.card
              (data.OrderedClusterPrefixBlock (k + 1)) := by
          simpa only [c] using
            (data.card_orderedClusterPrefixBlock_succ c).symm

@[simp]
theorem orderedClusterPrefixSize_top
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) :
    data.orderedClusterPrefixSize data.orderedClusterCount = m := by
  rw [data.orderedClusterPrefixSize_eq_card _ le_rfl,
    data.card_orderedClusterPrefixBlock_top]

/-- A nested record of the algebraic certificates obtained while descending
from the full prefix ideal to a chosen smaller prefix. -/
inductive OrderedClusterPrefixAlgebraicDescent
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ)
    (initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)) :
    (k : ℕ) → (hk : k ≤ data.orderedClusterCount) →
      Ideal (data.OrderedClusterPrefixRing R higher k) → Type (u + 1)
  | top : OrderedClusterPrefixAlgebraicDescent R data higher initialIdeal
      data.orderedClusterCount le_rfl initialIdeal
  | step (k : ℕ) (hk : k < data.orderedClusterCount)
      {nextIdeal : Ideal
        (data.OrderedClusterPrefixRing R higher (k + 1))}
      (tail : OrderedClusterPrefixAlgebraicDescent R data higher initialIdeal
        (k + 1) hk nextIdeal)
      (certificate : ClusterAlgebraicReductionCertificate
        (data.OrderedClusterPrefixRing R higher k)
        (data.orderedCluster ⟨k, hk⟩).card (fun _ ↦ higher)
        (data.orderedClusterPrefixCurriedIdeal R higher ⟨k, hk⟩
          nextIdeal)) :
      OrderedClusterPrefixAlgebraicDescent R data higher initialIdeal
        k (Nat.le_of_lt hk) certificate.terminalized.coefficientIdeal

/-- Noetherian one-cluster reduction can be chosen coherently through every
ordered prefix, from the largest cluster down to the zero prefix. -/
theorem exists_orderedClusterPrefixAlgebraicDescent
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ)
    (initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount))
    (krullDim : ℕ → ℕ)
    [∀ k, Algebra ℚ (data.OrderedClusterPrefixRing R higher k)]
    [∀ k, IsNoetherianRing
      (data.OrderedClusterPrefixRing R higher k)]
    [∀ k, Ring.KrullDimLE (krullDim k)
      (data.OrderedClusterPrefixRing R higher k)] :
    ∃ finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0),
      Nonempty (OrderedClusterPrefixAlgebraicDescent R data higher
        initialIdeal 0 (Nat.zero_le _) finalIdeal) := by
  let motive := fun (k : ℕ) (hk : k ≤ data.orderedClusterCount) ↦
    ∃ stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k),
      Nonempty (OrderedClusterPrefixAlgebraicDescent R data higher
        initialIdeal k hk stageIdeal)
  exact Nat.decreasingInduction (n := data.orderedClusterCount)
    (motive := motive)
    (fun k hk ih ↦ by
      obtain ⟨nextIdeal, ⟨tail⟩⟩ := ih
      let c : Fin data.orderedClusterCount := ⟨k, hk⟩
      let certificate := Classical.choice
        (data.nonempty_orderedClusterPrefixAlgebraicReductionCertificate
          R higher c nextIdeal (krullDim := krullDim k))
      exact ⟨certificate.terminalized.coefficientIdeal,
        ⟨OrderedClusterPrefixAlgebraicDescent.step k hk tail certificate⟩⟩)
    ⟨initialIdeal, ⟨OrderedClusterPrefixAlgebraicDescent.top⟩⟩
    (Nat.zero_le _)

/-- The cluster-size losses accumulated by a coherent descent give the exact
height remaining at its current prefix. -/
theorem OrderedClusterPrefixAlgebraicDescent.prefixHeight_le
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} {hk : k ≤ data.orderedClusterCount}
    {stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k)}
    (descent : OrderedClusterPrefixAlgebraicDescent R data higher
      initialIdeal k hk stageIdeal)
    (p : ℕ)
    (hheight : ((p + data.orderedClusterPrefixSize
      data.orderedClusterCount : ℕ) : ENat) ≤ initialIdeal.height) :
    ((p + data.orderedClusterPrefixSize k : ℕ) : ENat) ≤
      stageIdeal.height := by
  induction descent with
  | top => simpa using hheight
  | @step k hk nextIdeal tail certificate ih =>
      apply data.orderedClusterPrefixAlgebraicReduction_preserves_baseHeight
        R higher ⟨k, hk⟩ nextIdeal certificate
        (p + data.orderedClusterPrefixSize k)
      have hnext := ih
      rw [data.orderedClusterPrefixSize_succ hk] at hnext
      simpa only [Nat.cast_add, add_assoc] using hnext

/-- After every representative cluster is eliminated, an initial height of
`p+m` leaves height at least `p` in the zero-prefix coefficient ideal. -/
theorem OrderedClusterPrefixAlgebraicDescent.finalHeight_le
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPrefixAlgebraicDescent R data higher
      initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (p : ℕ) (hheight : ((p + m : ℕ) : ENat) ≤ initialIdeal.height) :
    (p : ENat) ≤ finalIdeal.height := by
  have h := descent.prefixHeight_le p (by
    simpa only [data.orderedClusterPrefixSize_top] using hheight)
  simpa using h

end RepresentativeClusterSubsequence
end AbelFormalization
