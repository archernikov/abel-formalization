import AbelFormalization.HermiteRankOneClusterBackwardPropagation
import AbelFormalization.HermiteRankDiagonalPreprocessedQuantitativeData

/-!
# Backward transport between adjacent non-bottom Hermite clusters

At the incoming boundary of cluster `c`, the individual trace presents the
next ideal of stage `c`.  This is definitionally the current ideal of stage
`c + 1`, and hence the coefficient ideal of the latter stage's terminalized
certificate.  This file exposes that dependent ideal identification and uses
it to feed the finite analytic terminal-coefficient bridge.

The two boundary scales are different.  The scale at the incoming boundary
of cluster `c` is the maximum of the inverse-Abel values in that cluster,
whereas the terminal scale of cluster `c + 1` is an inverse-Abel value after
finitely many fixed decrements.  The divergent ordered-cluster gap proves the
required eventual scale domination directly.

The resulting theorem reaches the canonical analytic source values of the
last displayed central family at cluster `c + 1`.  The presently available
`TerminalCoefficientNumericCompatibility` identifies the incoming family and
the denominator-cleared time family, but does not identify these canonical
source representatives with the independently supplied `afterValue` in a
`SimultaneousQuantitativeFiniteAnalyticSegmentData`.  Consequently this module
does not assert the stronger cross-cluster recursion without that missing
representative comparison.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

variable {ι : Type*} {A : ℝ → ℝ} {m p a : ℕ} [Nonempty (Fin m)]

namespace RepresentativeClusterSubsequence

universe u

/-- `tailAt` returns a `step` itself at its own prefix index. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.tailAt_step_self
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} (hk : k < data.orderedClusterCount)
    {nextIdeal : Ideal (data.OrderedClusterPrefixRing R higher (k + 1))}
    (tail : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal (k + 1) hk nextIdeal)
    (certificate : ClusterAlgebraicReductionCertificate
      (data.OrderedClusterPrefixRing R higher k)
      (data.orderedCluster ⟨k, hk⟩).card (fun _ ↦ higher)
      (data.orderedClusterPreprocessedCurriedIdeal R higher ⟨k, hk⟩
        (fixedSteps ⟨k, hk⟩) (fixedOrder ⟨k, hk⟩) nextIdeal)) :
    (OrderedClusterPreprocessedAlgebraicDescent.step k hk tail certificate).tailAt
        k (Nat.le_refl _) (Nat.le_of_lt hk) =
      ⟨certificate.terminalized.coefficientIdeal,
        OrderedClusterPreprocessedAlgebraicDescent.step
          k hk tail certificate⟩ := by
  simp [OrderedClusterPreprocessedAlgebraicDescent.tailAt]

/-- Past the head index, `tailAt` on a `step` is `tailAt` on its stored tail. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.tailAt_step_of_ne
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} (hk : k < data.orderedClusterCount)
    {nextIdeal : Ideal (data.OrderedClusterPrefixRing R higher (k + 1))}
    (tail : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal (k + 1) hk nextIdeal)
    (certificate : ClusterAlgebraicReductionCertificate
      (data.OrderedClusterPrefixRing R higher k)
      (data.orderedCluster ⟨k, hk⟩).card (fun _ ↦ higher)
      (data.orderedClusterPreprocessedCurriedIdeal R higher ⟨k, hk⟩
        (fixedSteps ⟨k, hk⟩) (fixedOrder ⟨k, hk⟩) nextIdeal))
    (j : ℕ) (hkj : k ≤ j) (hj : j ≤ data.orderedClusterCount)
    (hne : j ≠ k) :
    (OrderedClusterPreprocessedAlgebraicDescent.step k hk tail certificate).tailAt
        j hkj hj =
      tail.tailAt j (by omega) hj := by
  simp [OrderedClusterPreprocessedAlgebraicDescent.tailAt, hne]

/-- Dropping any descent to its own index returns the original dependent
descent and its indexing ideal. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.tailAt_self
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} {hk : k ≤ data.orderedClusterCount}
    {stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal k hk stageIdeal) :
    descent.tailAt k (Nat.le_refl _) hk = ⟨stageIdeal, descent⟩ := by
  cases descent with
  | top => rfl
  | step k hk tail certificate =>
      simpa using
        OrderedClusterPreprocessedAlgebraicDescent.tailAt_step_self
          hk tail certificate

/-- `tailAt` is independent of the proof terms witnessing its two bounds. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.tailAt_proof_irrel
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} {hk : k ≤ data.orderedClusterCount}
    {stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal k hk stageIdeal)
    (j : ℕ) (hkj₁ hkj₂ : k ≤ j)
    (hj₁ hj₂ : j ≤ data.orderedClusterCount) :
    descent.tailAt j hkj₁ hj₁ = descent.tailAt j hkj₂ hj₂ := by
  have h₁ : hkj₁ = hkj₂ := Subsingleton.elim _ _
  have h₂ : hj₁ = hj₂ := Subsingleton.elim _ _
  subst hkj₂
  subst hj₂
  rfl

/-- The ideal at a later prefix, retaining only the first projection of the
dependent tail.  This is sufficient for cross-cluster boundary coherence and
does not compare proof-bearing stage records. -/
def OrderedClusterPreprocessedAlgebraicDescent.tailIdealAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} {hk : k ≤ data.orderedClusterCount}
    {stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal k hk stageIdeal)
    (j : ℕ) (hkj : k ≤ j) (hj : j ≤ data.orderedClusterCount) :
    Ideal (data.OrderedClusterPrefixRing R higher j) :=
  (descent.tailAt j hkj hj).1

/-- Dropping a descent to its own index preserves its indexing ideal. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.tailIdealAt_self
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} {hk : k ≤ data.orderedClusterCount}
    {stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal k hk stageIdeal)
    : descent.tailIdealAt k (Nat.le_refl _) hk = stageIdeal := by
  exact congrArg Sigma.fst descent.tailAt_self

/-- `tailIdealAt` is independent of the proof terms witnessing its bounds. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.tailIdealAt_proof_irrel
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} {hk : k ≤ data.orderedClusterCount}
    {stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal k hk stageIdeal)
    (j : ℕ) (hkj₁ hkj₂ : k ≤ j)
    (hj₁ hj₂ : j ≤ data.orderedClusterCount) :
    descent.tailIdealAt j hkj₁ hj₁ =
      descent.tailIdealAt j hkj₂ hj₂ := by
  have h₁ : hkj₁ = hkj₂ := Subsingleton.elim _ _
  have h₂ : hj₁ = hj₂ := Subsingleton.elim _ _
  subst hkj₂
  subst hj₂
  rfl

/-- Past the head index, the ideal projection is computed on the stored
tail. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.tailIdealAt_step_of_ne
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} (hk : k < data.orderedClusterCount)
    {nextIdeal : Ideal (data.OrderedClusterPrefixRing R higher (k + 1))}
    (tail : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal (k + 1) hk nextIdeal)
    (certificate : ClusterAlgebraicReductionCertificate
      (data.OrderedClusterPrefixRing R higher k)
      (data.orderedCluster ⟨k, hk⟩).card (fun _ ↦ higher)
      (data.orderedClusterPreprocessedCurriedIdeal R higher ⟨k, hk⟩
        (fixedSteps ⟨k, hk⟩) (fixedOrder ⟨k, hk⟩) nextIdeal))
    (j : ℕ) (hkj : k ≤ j) (hj : j ≤ data.orderedClusterCount)
    (hne : j ≠ k) :
    (OrderedClusterPreprocessedAlgebraicDescent.step k hk tail certificate).tailIdealAt
        j hkj hj =
      tail.tailIdealAt j (by omega) hj := by
  unfold OrderedClusterPreprocessedAlgebraicDescent.tailIdealAt
  rw [OrderedClusterPreprocessedAlgebraicDescent.tailAt_step_of_ne
    hk tail certificate j hkj hj hne]

/-- Read the next ideal from a dependent tail already dropped to a
nonterminal index.  Its motive depends only on that index, so it can be
shared across descents with different lower-bound proofs. -/
def OrderedClusterPreprocessedAlgebraicDescent.nextIdealOfTail
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    (j : ℕ) (hj : j < data.orderedClusterCount)
    (current : Σ ideal : Ideal (data.OrderedClusterPrefixRing R higher j),
      OrderedClusterPreprocessedAlgebraicDescent R data higher fixedSteps
        fixedOrder initialIdeal j (Nat.le_of_lt hj) ideal) :
    Ideal (data.OrderedClusterPrefixRing R higher (j + 1)) := by
  obtain ⟨_, currentDescent⟩ := current
  cases currentDescent with
  | top => exact (Nat.lt_irrefl _ hj).elim
  | @step _ _ nextIdeal _ _ => exact nextIdeal

/-- The ideal immediately after a displayed nonterminal tail. -/
def OrderedClusterPreprocessedAlgebraicDescent.tailNextIdealAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} {hk : k ≤ data.orderedClusterCount}
    {stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal k hk stageIdeal)
    (j : ℕ) (hkj : k ≤ j) (hj : j < data.orderedClusterCount) :
    Ideal (data.OrderedClusterPrefixRing R higher (j + 1)) :=
  OrderedClusterPreprocessedAlgebraicDescent.nextIdealOfTail j hj
    (descent.tailAt j hkj (Nat.le_of_lt hj))

/-- `tailNextIdealAt` is independent of the proof terms witnessing its
bounds. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.tailNextIdealAt_proof_irrel
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} {hk : k ≤ data.orderedClusterCount}
    {stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal k hk stageIdeal)
    (j : ℕ) (hkj₁ hkj₂ : k ≤ j)
    (hj₁ hj₂ : j < data.orderedClusterCount) :
    descent.tailNextIdealAt j hkj₁ hj₁ =
      descent.tailNextIdealAt j hkj₂ hj₂ := by
  have h₁ : hkj₁ = hkj₂ := Subsingleton.elim _ _
  have h₂ : hj₁ = hj₂ := Subsingleton.elim _ _
  subst hkj₂
  subst hj₂
  rfl

/-- At the head index, the next-ideal projection is the ideal indexing the
stored tail. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.tailNextIdealAt_step_self
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} (hk : k < data.orderedClusterCount)
    {nextIdeal : Ideal (data.OrderedClusterPrefixRing R higher (k + 1))}
    (tail : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal (k + 1) hk nextIdeal)
    (certificate : ClusterAlgebraicReductionCertificate
      (data.OrderedClusterPrefixRing R higher k)
      (data.orderedCluster ⟨k, hk⟩).card (fun _ ↦ higher)
      (data.orderedClusterPreprocessedCurriedIdeal R higher ⟨k, hk⟩
        (fixedSteps ⟨k, hk⟩) (fixedOrder ⟨k, hk⟩) nextIdeal)) :
    (OrderedClusterPreprocessedAlgebraicDescent.step k hk tail certificate).tailNextIdealAt
        k (Nat.le_refl _) hk = nextIdeal := by
  unfold OrderedClusterPreprocessedAlgebraicDescent.tailNextIdealAt
  rw [OrderedClusterPreprocessedAlgebraicDescent.tailAt_step_self
    hk tail certificate]
  unfold OrderedClusterPreprocessedAlgebraicDescent.nextIdealOfTail
  rfl

/-- Past the head index, the next-ideal projection is computed on the stored
tail. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.tailNextIdealAt_step_of_ne
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} (hk : k < data.orderedClusterCount)
    {nextIdeal : Ideal (data.OrderedClusterPrefixRing R higher (k + 1))}
    (tail : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal (k + 1) hk nextIdeal)
    (certificate : ClusterAlgebraicReductionCertificate
      (data.OrderedClusterPrefixRing R higher k)
      (data.orderedCluster ⟨k, hk⟩).card (fun _ ↦ higher)
      (data.orderedClusterPreprocessedCurriedIdeal R higher ⟨k, hk⟩
        (fixedSteps ⟨k, hk⟩) (fixedOrder ⟨k, hk⟩) nextIdeal))
    (j : ℕ) (hkj : k ≤ j) (hj : j < data.orderedClusterCount)
    (hne : j ≠ k) :
    (OrderedClusterPreprocessedAlgebraicDescent.step k hk tail certificate).tailNextIdealAt
        j hkj hj =
      tail.tailNextIdealAt j (by omega) hj := by
  unfold OrderedClusterPreprocessedAlgebraicDescent.tailNextIdealAt
  rw [OrderedClusterPreprocessedAlgebraicDescent.tailAt_step_of_ne
    hk tail certificate j hkj (Nat.le_of_lt hj) hne]

/-- Consecutive first projections of `tailAt` are joined by the literal ideal
stored in the intervening `step`. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.tailIdealAt_succ_eq_tailNextIdealAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {k : ℕ} {hk : k ≤ data.orderedClusterCount}
    {stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal k hk stageIdeal)
    (j : ℕ) (hkj : k ≤ j) (hj : j + 1 < data.orderedClusterCount) :
    descent.tailIdealAt (j + 1) (by omega) (Nat.le_of_lt hj) =
      descent.tailNextIdealAt j hkj (by omega) := by
  induction descent generalizing j with
  | top => omega
  | @step k hk nextIdeal tail certificate ih =>
      by_cases h : j = k
      · subst j
        have hne : k + 1 ≠ k := by omega
        rw [OrderedClusterPreprocessedAlgebraicDescent.tailIdealAt_step_of_ne
          hk tail certificate (k + 1) (by omega) (Nat.le_of_lt hj) hne]
        rw [OrderedClusterPreprocessedAlgebraicDescent.tailNextIdealAt_step_self
          hk tail certificate]
        calc
          _ = tail.tailIdealAt (k + 1) (Nat.le_refl _) hk :=
            tail.tailIdealAt_proof_irrel (k + 1) _ _ _ _
          _ = nextIdeal := tail.tailIdealAt_self
      · have hsucc : k + 1 ≤ j := by omega
        have hnext : j + 1 ≠ k := by omega
        rw [OrderedClusterPreprocessedAlgebraicDescent.tailIdealAt_step_of_ne
          hk tail certificate (j + 1) (by omega) (Nat.le_of_lt hj) hnext]
        rw [OrderedClusterPreprocessedAlgebraicDescent.tailNextIdealAt_step_of_ne
          hk tail certificate j hkj (by omega) h]
        calc
          _ = tail.tailIdealAt (j + 1) (by omega)
                (Nat.le_of_lt hj) :=
            tail.tailIdealAt_proof_irrel (j + 1) _ _ _ _
          _ = tail.tailNextIdealAt j hsucc (by omega) := ih j hsucc hj
          _ = _ := tail.tailNextIdealAt_proof_irrel j _ _ _ _

/-- The current-ideal projection of `stageAt` is the first projection of the
same dependent tail. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.stageAt_currentIdeal_eq_tailIdealAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (j : ℕ) (hj : j < data.orderedClusterCount) :
    (descent.stageAt j hj).currentIdeal =
      descent.tailIdealAt j (Nat.zero_le _) (Nat.le_of_lt hj) := by
  unfold OrderedClusterPreprocessedAlgebraicDescent.stageAt
    OrderedClusterPreprocessedAlgebraicDescent.tailIdealAt
  generalize htail : descent.tailAt j (Nat.zero_le _) (Nat.le_of_lt hj) = t
  obtain ⟨currentIdeal, currentDescent⟩ := t
  cases currentDescent with
  | top => exact (Nat.lt_irrefl _ hj).elim
  | step => rfl

/-- The next-ideal projection of `stageAt` is the corresponding head-tail
projection. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.stageAt_nextIdeal_eq_tailNextIdealAt
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (j : ℕ) (hj : j < data.orderedClusterCount) :
    (descent.stageAt j hj).nextIdeal =
      descent.tailNextIdealAt j (Nat.zero_le _) hj := by
  unfold OrderedClusterPreprocessedAlgebraicDescent.stageAt
    OrderedClusterPreprocessedAlgebraicDescent.tailNextIdealAt
  generalize htail : descent.tailAt j (Nat.zero_le _)
    (Nat.le_of_lt hj) = t
  obtain ⟨_, currentDescent⟩ := t
  cases currentDescent with
  | top => exact (Nat.lt_irrefl _ hj).elim
  | step => rfl

end RepresentativeClusterSubsequence

namespace RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

variable (D : RestrictedBox p)
variable (representative : ι → Fin m)
variable (offset : ι → D.analyticNearClosedBoxSubalgebra)
variable (radius : ℝ)
variable (Fsys : Fin (m + p + a) → RestrictedSource m p a → ℝ)
variable (x : ℕ → RestrictedSource m p a)
variable (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
variable (data : RepresentativeClusterSubsequence
  (fun n i ↦ A ((x n).1.1 i)))
variable (boundary : RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
  D representative offset radius Fsys x w₀ hw₀ data)

noncomputable local instance nonbottomPrefixBlockDecidableEq
    {k : ℕ} : DecidableEq (data.OrderedClusterPrefixBlock k) :=
  Classical.decEq _

/-! ## The dependent algebraic boundary -/

/-- The cluster immediately above `c`.  The explicit inequality keeps the
dependent prefix rings and certificate types visible to callers. -/
abbrev nextOrderedCluster
    (boundary : RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
      D representative offset radius Fsys x w₀ hw₀ data)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    Fin data.orderedClusterCount :=
  ⟨c.val + 1, hc⟩

/-- Adjacent stages in the completed descent share their literal boundary
ideal.  This is definitional for `stageAt`, but naming it avoids repeated
dependent casts in downstream finite-family constructions. -/
@[simp]
theorem clusterStage_next_currentIdeal_eq_current_nextIdeal
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    (boundary.preprocessed.descent.clusterStage
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)).currentIdeal =
      (boundary.preprocessed.descent.clusterStage c).nextIdeal := by
  change (boundary.preprocessed.descent.stageAt (c.val + 1) hc).currentIdeal =
    (boundary.preprocessed.descent.stageAt c.val c.isLt).nextIdeal
  rw [boundary.preprocessed.descent.stageAt_currentIdeal_eq_tailIdealAt,
    boundary.preprocessed.descent.stageAt_nextIdeal_eq_tailNextIdealAt]
  exact boundary.preprocessed.descent.tailIdealAt_succ_eq_tailNextIdealAt
    c.val (Nat.zero_le _) hc

/-- Boundary zero of the lower individual trace is the coefficient ideal of
the next cluster's terminalized certificate. -/
theorem individualBoundaryZeroIdeal_eq_nextCoefficientIdeal
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    individualCentralIdealBoundary (RealAnalyticGerm p)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        (boundary.individualNumericSteps D representative offset radius Fsys x
          w₀ hw₀ data c)
        (boundary.preprocessed.descent.clusterStage c).preprocessingInput 0 =
      (boundary.preprocessed.descent.clusterStage
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)).certificate.terminalized.coefficientIdeal := by
  rw [individualCentralIdealBoundary_zero]
  calc
    (boundary.preprocessed.descent.clusterStage c).nextIdeal =
        (boundary.preprocessed.descent.clusterStage
          (boundary.nextOrderedCluster D representative offset radius Fsys x
            w₀ hw₀ data c hc)).currentIdeal :=
      (boundary.clusterStage_next_currentIdeal_eq_current_nextIdeal D
        representative offset radius Fsys x w₀ hw₀ data c hc).symm
    _ = (boundary.preprocessed.descent.clusterStage
          (boundary.nextOrderedCluster D representative offset radius Fsys x
            w₀ hw₀ data c hc)).certificate.terminalized.coefficientIdeal :=
      (boundary.preprocessed.descent.clusterStage
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)).currentIdeal_eq_coefficientIdeal

/-- Preserve the exact finite boundary-zero generators while viewing them as
a presentation of the next stage's coefficient ideal. -/
noncomputable def nextCoefficientFamilyFromIndividualBoundaryZero
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
        (paperRankHermiteHigherCount boundary.S)
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc).val)
      (boundary.preprocessed.descent.clusterStage
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)).certificate.terminalized.coefficientIdeal :=
  (boundary.individualNumericBoundaryFamily D representative offset radius
      Fsys x w₀ hw₀ data c 0).castIdeal
    (boundary.individualBoundaryZeroIdeal_eq_nextCoefficientIdeal D
      representative offset radius Fsys x w₀ hw₀ data c hc)

@[simp]
theorem nextCoefficientFamilyFromIndividualBoundaryZero_count
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    (boundary.nextCoefficientFamilyFromIndividualBoundaryZero D representative
      offset radius Fsys x w₀ hw₀ data c hc).count =
      (boundary.individualNumericBoundaryFamily D representative offset radius
        Fsys x w₀ hw₀ data c 0).count :=
  rfl

@[simp]
theorem nextCoefficientFamilyFromIndividualBoundaryZero_generator
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (b : Fin ((boundary.nextCoefficientFamilyFromIndividualBoundaryZero D
      representative offset radius Fsys x w₀ hw₀ data c hc).count + 1)) :
    (boundary.nextCoefficientFamilyFromIndividualBoundaryZero D representative
        offset radius Fsys x w₀ hw₀ data c hc).generator b =
      (boundary.individualNumericBoundaryFamily D representative offset radius
        Fsys x w₀ hw₀ data c 0).generator b :=
  rfl

/-! ## Concrete terminal values of the upper cluster -/

/-- The number of retained simultaneous operations at the upper cluster. -/
abbrev nextTerminalExtraSteps
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) : ℕ :=
  (boundary.simultaneousNumericStage D representative offset radius Fsys x w₀
    hw₀ data (boundary.nextOrderedCluster D representative offset radius Fsys x
      w₀ hw₀ data c hc)).certificate.terminalized.extraSteps

/-- The last displayed simultaneous operation of the upper cluster. -/
abbrev nextTerminalOperation
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    Fin (boundary.nextTerminalExtraSteps D representative offset radius Fsys x
      w₀ hw₀ data c hc + 1) :=
  Fin.last (boundary.nextTerminalExtraSteps D representative offset radius Fsys
    x w₀ hw₀ data c hc)

/-- Its displayed central/source families, with the full dependent
coefficient ring retained. -/
abbrev nextTerminalDisplayed
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :=
  (boundary.simultaneousNumericTrace D representative offset radius Fsys x w₀
    hw₀ data (boundary.nextOrderedCluster D representative offset radius Fsys x
      w₀ hw₀ data c hc)).simultaneousDisplayed
    (boundary.nextTerminalOperation D representative offset radius Fsys x w₀
      hw₀ data c hc)

/-- The common balancing-sequence index seen literally by the shifted lower
individual boundary. -/
def nonbottomCommonBalancingIndex
    (hA : IsAbel A) (n : ℕ) : ℕ :=
  boundary.individualQuantitativeSubsequence D representative offset radius
    Fsys x w₀ hw₀ data hA
    (boundary.individualSimultaneousTailShift D representative offset radius
      Fsys x w₀ hw₀ data hA n)

/-- The simultaneous and shifted-individual definitions select the same
balancing index; their two fixed tails merely occur in opposite orders. -/
@[simp]
theorem nonbottomCommonBalancingIndex_eq_simultaneous
    (hA : IsAbel A) (n : ℕ) :
    boundary.nonbottomCommonBalancingIndex D representative offset radius Fsys
        x w₀ hw₀ data hA n =
      boundary.preprocessed.balancingSubsequence
        (boundary.simultaneousQuantitativeReindex D representative offset radius
          Fsys x w₀ hw₀ data hA n) := by
  unfold nonbottomCommonBalancingIndex individualQuantitativeSubsequence
    individualSimultaneousTailShift simultaneousQuantitativeReindex
  congr 1
  omega

/-- The common cross-cluster reindexing is cofinal. -/
theorem nonbottomCommonBalancingIndex_tendsto_atTop
    (hA : IsAbel A) :
    Tendsto (boundary.nonbottomCommonBalancingIndex D representative offset
      radius Fsys x w₀ hw₀ data hA) atTop atTop := by
  have h :=
    boundary.preprocessed.balancingSubsequence_strictMono.tendsto_atTop.comp
      (boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
        offset radius Fsys x w₀ hw₀ data hA)
  apply h.congr'
  exact Filter.Eventually.of_forall fun n ↦
    (boundary.nonbottomCommonBalancingIndex_eq_simultaneous D representative
      offset radius Fsys x w₀ hw₀ data hA n).symm

/-- The translated bounded coordinate used to evaluate every analytic germ
in the upper terminal bridge. -/
def nextTerminalParameter
    (hA : IsAbel A) (n : ℕ) : RestrictedBoxSpace p :=
  (boundary.selectedTranslatedParameter D representative offset radius Fsys x
    w₀ hw₀ data
    (boundary.simultaneousQuantitativeReindex D representative offset radius
      Fsys x w₀ hw₀ data hA n)).2

/-- The exact post-log center family of the last upper simultaneous step. -/
def nextTerminalCenter
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :=
  boundary.simultaneousQuantitativePostLogScale D representative offset radius
    Fsys x w₀ hw₀ data hA
    (boundary.nextOrderedCluster D representative offset radius Fsys x w₀ hw₀
      data c hc)
    (boundary.nextTerminalExtraSteps D representative offset radius Fsys x w₀
      hw₀ data c hc)

/-- The output scale of the last upper simultaneous operation. -/
def nextTerminalScale
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) : ℕ → ℝ :=
  boundary.simultaneousQuantitativeBoundaryScale D representative offset radius
    Fsys x w₀ hw₀ data hA
    (boundary.nextOrderedCluster D representative offset radius Fsys x w₀ hw₀
      data c hc)
    (boundary.nextTerminalExtraSteps D representative offset radius Fsys x w₀
      hw₀ data c hc + 1)

/-- Retained time values at the upper terminal boundary. -/
def nextTerminalTimeValue
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (i : Fin (data.orderedCluster
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc)).card) : ℕ → ℝ :=
  fun n ↦ A (boundary.nextTerminalCenter D representative offset radius Fsys x
    w₀ hw₀ data hA c hc i n)

/-- Smaller-prefix coefficient symbols at the last upper simultaneous
operation. -/
def nextTerminalCoefficientValue
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc).val)
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1)
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc).val) → ℕ → ℝ :=
  fun z n ↦ boundary.simultaneousSmallerPrefixSequenceValue D representative
    offset radius Fsys x w₀ hw₀ data
    (boundary.nextOrderedCluster D representative offset radius Fsys x w₀ hw₀
      data c hc)
    (boundary.nextTerminalExtraSteps D representative offset radius Fsys x w₀
      hw₀ data c hc) z
    (boundary.simultaneousQuantitativeReindex D representative offset radius
      Fsys x w₀ hw₀ data hA n)

/-- Exact terminal positive-derivative and retained-time assignment. -/
def nextTerminalSymbolValue
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    TerminalMultiblockSourceIndex
      (data.orderedCluster
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)).card
      (fun _ : Fin (data.orderedCluster
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)).card ↦ paperRankHermiteHigherCount boundary.S)
      (Fin (data.orderedCluster
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)).card) → ℕ → ℝ :=
  fun z n ↦ realCentralTransferCentralValue A
    (fun i ↦ boundary.nextTerminalCenter D representative offset radius Fsys x
      w₀ hw₀ data hA c hc i n)
    (terminalTotalDerivativeCount (fun _ : Fin (data.orderedCluster
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc)).card ↦ paperRankHermiteHigherCount boundary.S)) z

/-! ## Quantitative facts at the upper terminal boundary -/

theorem nextTerminalParameter_tendsto
    (hA : IsAbel A) :
    Tendsto (boundary.nextTerminalParameter D representative offset radius Fsys
      x w₀ hw₀ data hA) atTop
      (𝓝 (0 : RestrictedBoxSpace p)) := by
  exact (boundary.selectedTranslatedParameter_box_tendsto_zero D representative
    offset radius Fsys x w₀ hw₀ data).comp
      (boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
        offset radius Fsys x w₀ hw₀ data hA)

theorem nextTerminalCenter_tendsto_atTop
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (i : Fin (data.orderedCluster
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc)).card) :
    Tendsto (boundary.nextTerminalCenter D representative offset radius Fsys x
      w₀ hw₀ data hA c hc i) atTop atTop := by
  change Tendsto
    ((boundary.simultaneousNumericPostLogScale D representative offset radius
      Fsys x w₀ hw₀ data
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc)
      (boundary.nextTerminalExtraSteps D representative offset radius Fsys x w₀
        hw₀ data c hc) i) ∘
      boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA) atTop atTop
  exact (boundary.simultaneousNumericPostLogScale_tendsto_atTop D representative
    offset radius Fsys x w₀ hw₀ data hA
    (boundary.nextOrderedCluster D representative offset radius Fsys x w₀ hw₀
      data c hc)
    (boundary.nextTerminalExtraSteps D representative offset radius Fsys x w₀
      hw₀ data c hc) i).comp
      (boundary.simultaneousQuantitativeReindex_tendsto_atTop D representative
        offset radius Fsys x w₀ hw₀ data hA)

theorem nextTerminalCenter_pos
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (i : Fin (data.orderedCluster
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc)).card) (n : ℕ) :
    0 < boundary.nextTerminalCenter D representative offset radius Fsys x w₀
      hw₀ data hA c hc i n :=
  hA.inverse_pos _

theorem nextTerminalCenter_le_scale
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (i : Fin (data.orderedCluster
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc)).card) (n : ℕ) :
    boundary.nextTerminalCenter D representative offset radius Fsys x w₀ hw₀
        data hA c hc i n ≤
      boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc n := by
  let d := boundary.nextOrderedCluster D representative offset radius Fsys x
    w₀ hw₀ data c hc
  let e := data.orderedClusterBalancingToActiveEquiv d
  apply hA.inverse_strictMono.monotone
  apply sub_le_sub_right
  have horder :=
    (boundary.preprocessed.plans
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n) d).antitone_finalTimes_comp_finalOrder
      (Fin.zero_le (e.symm i))
  have hsteps := boundary.preprocessed.plans_steps
    (boundary.simultaneousQuantitativeReindex D representative offset radius
      Fsys x w₀ hw₀ data hA n) d
  have hfinalOrder := boundary.preprocessed.plans_finalOrder
    (boundary.simultaneousQuantitativeReindex D representative offset radius
      Fsys x w₀ hw₀ data hA n) d
  dsimp only [ClusterBalancingPlan.finalTimes, Function.comp_apply] at horder
  rw [hsteps, hfinalOrder] at horder
  simpa only [nextTerminalCenter, nextTerminalScale,
    simultaneousQuantitativePostLogScale, simultaneousQuantitativeBoundaryScale,
    simultaneousQuantitativeRawTime, simultaneousNumericRawTime,
    selectedClusterRawTime,
    RepresentativeClusterSubsequence.orderedClusterSimultaneousPostLogScale,
    RepresentativeClusterSubsequence.orderedClusterPostBalancingFinalOrderTime,
    RepresentativeClusterSubsequence.orderedClusterSimultaneousBoundaryScale,
    d, e] using horder

theorem nextTerminalScale_eq_zeroCenter
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) (n : ℕ) :
    boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc n =
      boundary.nextTerminalCenter D representative offset radius Fsys x w₀
        hw₀ data hA c hc
        (data.orderedClusterBalancingToActiveEquiv
          (boundary.nextOrderedCluster D representative offset radius Fsys x
            w₀ hw₀ data c hc) 0) n := by
  symm
  exact data.orderedClusterSimultaneousPostLogScale_zero_eq_boundaryScale
    (boundary.nextOrderedCluster D representative offset radius Fsys x w₀ hw₀
      data c hc) A
    (boundary.simultaneousQuantitativeRawTime D representative offset radius
      Fsys x w₀ hw₀ data hA
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc))
    (boundary.preprocessed.fixedSteps
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc))
    (boundary.preprocessed.fixedOrder
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc))
    (boundary.nextTerminalExtraSteps D representative offset radius Fsys x w₀
      hw₀ data c hc) n

theorem nextTerminalScale_tendsto_atTop
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    Tendsto (boundary.nextTerminalScale D representative offset radius Fsys x
      w₀ hw₀ data hA c hc) atTop atTop := by
  apply (boundary.nextTerminalCenter_tendsto_atTop D representative offset
    radius Fsys x w₀ hw₀ data hA c hc
    (data.orderedClusterBalancingToActiveEquiv
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc) 0)).congr'
  exact Filter.Eventually.of_forall fun n ↦
    (boundary.nextTerminalScale_eq_zeroCenter D representative offset radius
      Fsys x w₀ hw₀ data hA c hc n).symm

theorem nextTerminalScale_eventually_ge_one
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    ∀ᶠ n in atTop, 1 ≤
      boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc n :=
  (boundary.nextTerminalScale_tendsto_atTop D representative offset radius Fsys
    x w₀ hw₀ data hA c hc).eventually (eventually_ge_atTop 1)

theorem nextTerminalScale_eventually_ge_two
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    ∀ᶠ n in atTop, 2 ≤
      boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc n :=
  (boundary.nextTerminalScale_tendsto_atTop D representative offset radius Fsys
    x w₀ hw₀ data hA c hc).eventually (eventually_ge_atTop 2)

theorem nextTerminalTimeValue_hasPolynomialUpperBound
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc))
    (i : Fin (data.orderedCluster
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc)).card) :
    HasPolynomialUpperBound atTop
      (boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc)
      (boundary.nextTerminalTimeValue D representative offset radius Fsys x w₀
        hw₀ data hA c hc i) := by
  have hmain := segment.main_bound
    (boundary.nextTerminalOperation D representative offset radius Fsys x w₀
      hw₀ data c hc) (Sum.inr (Sum.inr i))
  have hbound := hmain.sub
    (boundary.nextTerminalScale_eventually_ge_one D representative offset radius
      Fsys x w₀ hw₀ data hA c hc)
    (HasPolynomialUpperBound.one atTop
      (boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc))
  apply hbound.congr
  intro n
  simp only [nextTerminalTimeValue, finiteRealJetMainAssignment,
    realCentralTransferMainValue, add_sub_cancel_right]
  apply congrArg A
  rfl

theorem nextTerminalCoefficientValue_hasPolynomialUpperBound
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc))
    (z : ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc).val)
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1)
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc).val)) :
    HasPolynomialUpperBound atTop
      (boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc)
      (boundary.nextTerminalCoefficientValue D representative offset radius
        Fsys x w₀ hw₀ data hA c hc z) := by
  have hlast :
      (boundary.nextTerminalOperation D representative offset radius Fsys x w₀
        hw₀ data c hc).val =
        boundary.nextTerminalExtraSteps D representative offset radius Fsys x
          w₀ hw₀ data c hc := rfl
  unfold nextTerminalCoefficientValue
  simpa only [nextTerminalScale, hlast] using
    segment.smaller_bound
      (boundary.nextTerminalOperation D representative offset radius Fsys x w₀
        hw₀ data c hc) z

theorem nextTerminalSymbolValue_hasPolynomialUpperBound
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc))
    (z : TerminalMultiblockSourceIndex
      (data.orderedCluster
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)).card
      (fun _ : Fin (data.orderedCluster
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)).card ↦ paperRankHermiteHigherCount boundary.S)
      (Fin (data.orderedCluster
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)).card)) :
    HasPolynomialUpperBound atTop
      (boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc)
      (boundary.nextTerminalSymbolValue D representative offset radius Fsys x
        w₀ hw₀ data hA c hc z) := by
  rcases z with z | i
  · rcases z with ⟨i, r⟩
    have htendsto :=
      (hA.tendsto_iteratedDeriv_atTop (r.val + 1)
        (Nat.succ_le_succ (Nat.zero_le r.val))).comp
          (boundary.nextTerminalCenter_tendsto_atTop D representative offset
            radius Fsys x w₀ hw₀ data hA c hc i)
    apply (HasPolynomialUpperBound.of_tendsto htendsto).congr
    intro n
    rfl
  · change HasPolynomialUpperBound atTop
      (boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc)
      (boundary.nextTerminalTimeValue D representative offset radius Fsys x w₀
        hw₀ data hA c hc i)
    exact boundary.nextTerminalTimeValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data hA c hc segment i

theorem nextTerminalFirstDerivative_hasScalarInversePowerLowerBound
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (i : Fin (data.orderedCluster
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc)).card) :
    HasScalarInversePowerLowerBound atTop
      (boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc)
      (fun n ↦ boundary.nextTerminalSymbolValue D representative offset radius
        Fsys x w₀ hw₀ data hA c hc
        (Sum.inl ⟨i, (0 : Fin (paperRankHermiteHigherCount boundary.S + 1))⟩)
        n) := by
  have hvalue :
      (fun n ↦ boundary.nextTerminalSymbolValue D representative offset radius
        Fsys x w₀ hw₀ data hA c hc
        (Sum.inl ⟨i, (0 : Fin (paperRankHermiteHigherCount boundary.S + 1))⟩)
        n) =
      fun n ↦ deriv A
        (boundary.nextTerminalCenter D representative offset radius Fsys x w₀
          hw₀ data hA c hc i n) := by
    funext n
    simp only [nextTerminalSymbolValue, realCentralTransferCentralValue]
    change iteratedDeriv 1 A
      (boundary.nextTerminalCenter D representative offset radius Fsys x w₀ hw₀
        data hA c hc i n) = _
    rw [iteratedDeriv_one]
  rw [hvalue]
  refine ⟨1, zero_lt_one, 2, ?_⟩
  have hderiv :=
    (boundary.nextTerminalCenter_tendsto_atTop D representative offset radius
      Fsys x w₀ hw₀ data hA c hc i).eventually
        hA.eventually_deriv_ge_rpow_neg_two
  filter_upwards [hderiv] with n hn
  have hu : 0 < boundary.nextTerminalCenter D representative offset radius Fsys
      x w₀ hw₀ data hA c hc i n :=
    boundary.nextTerminalCenter_pos D representative offset radius Fsys x w₀
      hw₀ data hA c hc i n
  have hus := boundary.nextTerminalCenter_le_scale D representative offset
    radius Fsys x w₀ hw₀ data hA c hc i n
  have hsquare :
      (boundary.nextTerminalCenter D representative offset radius Fsys x w₀
        hw₀ data hA c hc i n) ^ 2 ≤
      (boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc n) ^ 2 :=
    pow_le_pow_left₀ hu.le hus 2
  rw [abs_of_pos (hA.deriv_pos _ hu), one_div]
  calc
    ((boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc n) ^ 2)⁻¹ ≤
        ((boundary.nextTerminalCenter D representative offset radius Fsys x w₀
          hw₀ data hA c hc i n) ^ 2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le
        (pow_pos hu 2) hsquare
    _ = (boundary.nextTerminalCenter D representative offset radius Fsys x w₀
          hw₀ data hA c hc i n) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hu.le]
      norm_num [Real.rpow_two]
    _ ≤ deriv A (boundary.nextTerminalCenter D representative offset radius
          Fsys x w₀ hw₀ data hA c hc i n) := hn

/-! ## The cross-cluster scale gap -/

/-- Each inverse-Abel value in the lower cluster is eventually below the
terminal scale of the adjacent upper cluster.  The upper shift is the exact
number of decrements applied to its final-order zero coordinate. -/
theorem eventually_lowerInverse_lt_nextTerminalScale
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (i : Fin (data.orderedClusterTailSize c + 1)) :
    ∀ᶠ n in atTop,
      inverse A (data.orderedClusterRawTime
        (boundary.nonbottomCommonBalancingIndex D representative offset radius
          Fsys x w₀ hw₀ data hA n) c i) <
        boundary.nextTerminalScale D representative offset radius Fsys x w₀
          hw₀ data hA c hc n := by
  let d := boundary.nextOrderedCluster D representative offset radius Fsys x
    w₀ hw₀ data c hc
  let upperIndex := boundary.preprocessed.fixedOrder d 0
  let upperShift : ℕ :=
    (boundary.preprocessed.fixedSteps d).count upperIndex +
      (boundary.nextTerminalExtraSteps D representative offset radius Fsys x
        w₀ hw₀ data c hc + 1)
  have hcd : c < d := by
    change c.val < c.val + 1
    omega
  have hgap₀ := data.tendsto_orderedCluster_gap_atTop hcd
    (data.orderedClusterEnumeration_mem c i)
    (data.orderedClusterEnumeration_mem d upperIndex)
  have hgap : Tendsto (fun n ↦
      data.orderedClusterRawTime
          (boundary.nonbottomCommonBalancingIndex D representative offset
            radius Fsys x w₀ hw₀ data hA n) d upperIndex -
        data.orderedClusterRawTime
          (boundary.nonbottomCommonBalancingIndex D representative offset
            radius Fsys x w₀ hw₀ data hA n) c i) atTop atTop := by
    change Tendsto
      ((fun k ↦ data.orderedClusterRawTime k d upperIndex -
        data.orderedClusterRawTime k c i) ∘
          boundary.nonbottomCommonBalancingIndex D representative offset radius
            Fsys x w₀ hw₀ data hA) atTop atTop
    simpa only [RepresentativeClusterSubsequence.orderedClusterRawTime] using
      hgap₀.comp
        (boundary.nonbottomCommonBalancingIndex_tendsto_atTop D representative
          offset radius Fsys x w₀ hw₀ data hA)
  have hdom := hA.eventually_E_iterate_inverse_sub_nat_lt_of_gap hgap
    upperShift 0 0
  filter_upwards [hdom] with n hn
  have hn' :
      inverse A (data.orderedClusterRawTime
        (boundary.nonbottomCommonBalancingIndex D representative offset radius
          Fsys x w₀ hw₀ data hA n) c i) <
      inverse A (data.orderedClusterRawTime
        (boundary.nonbottomCommonBalancingIndex D representative offset radius
          Fsys x w₀ hw₀ data hA n) d upperIndex - (upperShift : ℝ)) := by
    simpa only [Function.iterate_zero_apply, Nat.cast_zero, sub_zero] using hn
  calc
    inverse A (data.orderedClusterRawTime
        (boundary.nonbottomCommonBalancingIndex D representative offset radius
          Fsys x w₀ hw₀ data hA n) c i) <
      inverse A (data.orderedClusterRawTime
        (boundary.nonbottomCommonBalancingIndex D representative offset radius
          Fsys x w₀ hw₀ data hA n) d upperIndex - (upperShift : ℝ)) := hn'
    _ = boundary.nextTerminalScale D representative offset radius Fsys x w₀
        hw₀ data hA c hc n := by
      simp only [nextTerminalScale, simultaneousQuantitativeBoundaryScale,
        simultaneousQuantitativeRawTime, simultaneousNumericRawTime,
        selectedClusterRawTime,
        RepresentativeClusterSubsequence.orderedClusterSimultaneousBoundaryScale,
        clusterShiftedTimes]
      rw [← boundary.nonbottomCommonBalancingIndex_eq_simultaneous D
        representative offset radius Fsys x w₀ hw₀ data hA n]
      unfold upperShift upperIndex d
      congr 1
      push_cast
      ring

/-- The initial lower-cluster scale has its literal finite-maximum form on
the common reindexing. -/
theorem individualMixedInitialScale_eq
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount) (n : ℕ) :
    boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0 n =
      max 2 ((Finset.univ.image (fun i : Fin
        (data.orderedClusterTailSize c + 1) ↦
          inverse A (data.orderedClusterRawTime
            (boundary.nonbottomCommonBalancingIndex D representative offset
              radius Fsys x w₀ hw₀ data hA n) c i))).max' (by simp)) := by
  unfold individualMixedBoundaryScaleOnSimultaneousTail
    RepresentativeClusterSubsequence.orderedClusterIndividualBoundaryScale
    RepresentativeClusterSubsequence.orderedClusterBalancingPrefixScale
    clusterBalancingPrefixScale clusterBalancingPrefixMaximum
    clusterBalancingPrefixValue clusterBalancingPrefixTime
  simp only [Fin.val_zero, List.take_zero, clusterShiftedTimes_nil]
  unfold nonbottomCommonBalancingIndex
  rfl

/-- The cluster gap and the fixed upper shifts give exactly the scale
monotonicity needed by the analytic terminal bridge. -/
theorem individualMixedInitialScale_le_nextTerminalScale
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    ∀ᶠ n in atTop,
      boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
          offset radius Fsys x w₀ hw₀ data hA c 0 n ≤
        boundary.nextTerminalScale D representative offset radius Fsys x w₀
          hw₀ data hA c hc n := by
  have hcoordinates : ∀ᶠ n in atTop, ∀ i : Fin
      (data.orderedClusterTailSize c + 1),
      inverse A (data.orderedClusterRawTime
        (boundary.nonbottomCommonBalancingIndex D representative offset radius
          Fsys x w₀ hw₀ data hA n) c i) <
        boundary.nextTerminalScale D representative offset radius Fsys x w₀
          hw₀ data hA c hc n := by
    exact Filter.eventually_all.mpr fun i ↦
      boundary.eventually_lowerInverse_lt_nextTerminalScale D representative
        offset radius Fsys x w₀ hw₀ data hA c hc i
  filter_upwards [hcoordinates,
    boundary.nextTerminalScale_eventually_ge_two D representative offset radius
      Fsys x w₀ hw₀ data hA c hc] with n hcoordinate htwo
  rw [boundary.individualMixedInitialScale_eq D representative offset radius
    Fsys x w₀ hw₀ data hA c n]
  apply max_le htwo
  apply Finset.max'_le
  intro y hy
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hy
  exact (hcoordinate i).le

theorem individualMixedInitialScale_eventually_ge_one
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount) :
    ∀ᶠ n in atTop, 1 ≤
      boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0 n := by
  exact Filter.Eventually.of_forall fun n ↦ one_le_two.trans
    (two_le_clusterBalancingPrefixScale A
      (fun k ↦ data.orderedClusterRawTime
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA k) c)
      (boundary.preprocessed.fixedSteps c) 0
      (boundary.individualSimultaneousTailShift D representative offset radius
        Fsys x w₀ hw₀ data hA n))

/-! ## The honest finite analytic cross-boundary result -/

/-- Exact numeric compatibility type for transporting the lower boundary-zero
family through the upper terminal time ideal. -/
abbrev NextTerminalCoefficientNumericCompatibility
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData) :=
  ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.TerminalCoefficientNumericCompatibility
    (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
      hw₀ data c hc) localization
    (boundary.nextCoefficientFamilyFromIndividualBoundaryZero D representative
      offset radius Fsys x w₀ hw₀ data c hc)
    atTop
    (boundary.nextTerminalParameter D representative offset radius Fsys x w₀
      hw₀ data hA)
    (boundary.nextTerminalTimeValue D representative offset radius Fsys x w₀
      hw₀ data hA c hc)
    (boundary.nextTerminalCoefficientValue D representative offset radius Fsys
      x w₀ hw₀ data hA c hc)
    (boundary.nextTerminalSymbolValue D representative offset radius Fsys x w₀
      hw₀ data hA c hc)
    (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
      offset radius Fsys x w₀ hw₀ data hA c 0)

/-- Canonical analytic representative values of the last displayed central
family at the upper cluster. -/
noncomputable def nextTerminalAnalyticSourceValue
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData) :=
  (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.terminalAnalyticChange
    (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
      hw₀ data c hc) localization).sourceValue
    (boundary.nextTerminalParameter D representative offset radius Fsys x w₀
      hw₀ data hA)
    (boundary.nextTerminalSymbolValue D representative offset radius Fsys x w₀
      hw₀ data hA c hc)
    (boundary.nextTerminalCoefficientValue D representative offset radius Fsys
      x w₀ hw₀ data hA c hc)

/-- The exact remaining representative comparison needed before the upper
cluster's existing one-cluster recursion can consume the terminal result.
This proposition is named only to expose the obstruction; no theorem below
assumes it. -/
abbrev NextTerminalSourceValueCompatibility
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc))
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData) : Prop :=
  ∀ᶠ n in atTop, ∀ j,
    boundary.nextTerminalAnalyticSourceValue D representative offset radius
        Fsys x w₀ hw₀ data hA c hc localization j n =
      (segment.change
        (boundary.nextTerminalOperation D representative offset radius Fsys x
          w₀ hw₀ data c hc)).afterValue j n

/-- The lower cluster's incoming individual-family lower bound reaches the
canonical analytic source values of the last displayed central family of the
upper cluster.  The coefficient ideal cast, all concrete terminal-coordinate
bounds, and the cross-cluster scale domination are discharged internally.

`segment` and `compatibility` remain explicit because they encode the finite
analytic representatives chosen for this particular upper cluster. -/
theorem nextTerminalAnalyticSource_lower_of_individualMixedInitial_lower
    (hA : IsAbel A)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (segment : boundary.SimultaneousQuantitativeFiniteAnalyticSegmentData D
      representative offset radius Fsys x w₀ hw₀ data hA
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc))
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData)
    (compatibility : boundary.NextTerminalCoefficientNumericCompatibility D
      representative offset radius Fsys x w₀ hw₀ data hA c hc localization)
    (hincoming : HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)) :
    HasInversePowerLowerBound atTop
      (boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc)
      (boundary.nextTerminalAnalyticSourceValue D representative offset radius
        Fsys x w₀ hw₀ data hA c hc localization) := by
  have hincoming' : HasInversePowerLowerBound atTop
      (boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0) :=
    hasInversePowerLowerBound_mono_scale
      (boundary.individualMixedInitialScale_eventually_ge_one D representative
        offset radius Fsys x w₀ hw₀ data hA c)
      (boundary.individualMixedInitialScale_le_nextTerminalScale D
        representative offset radius Fsys x w₀ hw₀ data hA c hc)
      hincoming
  exact
    (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
      hw₀ data c hc).terminalAnalyticSourceValue_lower_of_coefficientValue_lower
      localization
      (boundary.nextCoefficientFamilyFromIndividualBoundaryZero D representative
        offset radius Fsys x w₀ hw₀ data c hc)
      (boundary.nextTerminalParameter D representative offset radius Fsys x w₀
        hw₀ data hA)
      (boundary.nextTerminalTimeValue D representative offset radius Fsys x w₀
        hw₀ data hA c hc)
      (boundary.nextTerminalCoefficientValue D representative offset radius
        Fsys x w₀ hw₀ data hA c hc)
      (boundary.nextTerminalSymbolValue D representative offset radius Fsys x
        w₀ hw₀ data hA c hc)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.nextTerminalParameter_tendsto D representative offset radius
        Fsys x w₀ hw₀ data hA)
      (boundary.nextTerminalScale_eventually_ge_one D representative offset
        radius Fsys x w₀ hw₀ data hA c hc)
      (boundary.nextTerminalTimeValue_hasPolynomialUpperBound D representative
        offset radius Fsys x w₀ hw₀ data hA c hc segment)
      (boundary.nextTerminalCoefficientValue_hasPolynomialUpperBound D
        representative offset radius Fsys x w₀ hw₀ data hA c hc segment)
      (boundary.nextTerminalSymbolValue_hasPolynomialUpperBound D representative
        offset radius Fsys x w₀ hw₀ data hA c hc segment)
      (boundary.nextTerminalFirstDerivative_hasScalarInversePowerLowerBound D
        representative offset radius Fsys x w₀ hw₀ data hA c hc)
      compatibility hincoming'

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
