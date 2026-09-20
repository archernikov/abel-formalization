import AbelFormalization.OrderedClusterPrefixAnalyticDimension
import AbelFormalization.OrderedClusterIndividualPreprocessing

/-!
# Ordered-cluster descent after individual balancing

This module performs the coherent algebraic descent through every ordered
cluster after applying the fixed individual balancing decrements assigned to
that cluster.  At stage `c`, the simultaneous cluster certificate consumes
`orderedClusterPreprocessedCurriedIdeal`, including both the complete
individual-decrement list and the final active-coordinate order.

The construction is parallel to `OrderedClusterPrefixAlgebraicDescent`.  We
keep the two descent types separate so existing users of the direct curry do
not acquire irrelevant balancing parameters.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

universe u

/-- A fixed chronological list of individual balancing decrements for every
ordered cluster. -/
abbrev OrderedClusterIndividualStepPlan
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) :=
  ∀ c : Fin data.orderedClusterCount,
    List (Fin (data.orderedClusterTailSize c + 1))

/-- The final active-coordinate order reached by the balancing plan in every
ordered cluster. -/
abbrev OrderedClusterFinalOrderPlan
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) :=
  ∀ c : Fin data.orderedClusterCount,
    Equiv.Perm (Fin (data.orderedClusterTailSize c + 1))

/-- A coherent ordered-prefix descent in which every simultaneous cluster
certificate is applied only after the fixed individual preprocessing for that
cluster. -/
inductive OrderedClusterPreprocessedAlgebraicDescent
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ)
    (fixedSteps : data.OrderedClusterIndividualStepPlan)
    (fixedOrder : data.OrderedClusterFinalOrderPlan)
    (initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)) :
    (k : ℕ) → (hk : k ≤ data.orderedClusterCount) →
      Ideal (data.OrderedClusterPrefixRing R higher k) → Type (u + 1)
  | top : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal data.orderedClusterCount le_rfl
      initialIdeal
  | step (k : ℕ) (hk : k < data.orderedClusterCount)
      {nextIdeal : Ideal
        (data.OrderedClusterPrefixRing R higher (k + 1))}
      (tail : OrderedClusterPreprocessedAlgebraicDescent R data higher
        fixedSteps fixedOrder initialIdeal (k + 1) hk nextIdeal)
      (certificate : ClusterAlgebraicReductionCertificate
        (data.OrderedClusterPrefixRing R higher k)
        (data.orderedCluster ⟨k, hk⟩).card (fun _ ↦ higher)
        (data.orderedClusterPreprocessedCurriedIdeal R higher ⟨k, hk⟩
          (fixedSteps ⟨k, hk⟩) (fixedOrder ⟨k, hk⟩) nextIdeal)) :
      OrderedClusterPreprocessedAlgebraicDescent R data higher
        fixedSteps fixedOrder initialIdeal k (Nat.le_of_lt hk)
        certificate.terminalized.coefficientIdeal

/-- Noetherian one-cluster reductions can be selected coherently through all
ordered prefixes after the prescribed individual preprocessing. -/
theorem exists_orderedClusterPreprocessedAlgebraicDescent
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ)
    (fixedSteps : data.OrderedClusterIndividualStepPlan)
    (fixedOrder : data.OrderedClusterFinalOrderPlan)
    (initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount))
    (krullDim : ℕ → ℕ)
    [∀ k, Algebra ℚ (data.OrderedClusterPrefixRing R higher k)]
    [∀ k, IsNoetherianRing
      (data.OrderedClusterPrefixRing R higher k)]
    [∀ k, Ring.KrullDimLE (krullDim k)
      (data.OrderedClusterPrefixRing R higher k)] :
    ∃ finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0),
      Nonempty (OrderedClusterPreprocessedAlgebraicDescent R data higher
        fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal) := by
  let motive := fun (k : ℕ) (hk : k ≤ data.orderedClusterCount) ↦
    ∃ stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k),
      Nonempty (OrderedClusterPreprocessedAlgebraicDescent R data higher
        fixedSteps fixedOrder initialIdeal k hk stageIdeal)
  exact Nat.decreasingInduction (n := data.orderedClusterCount)
    (motive := motive)
    (fun k hk ih ↦ by
      obtain ⟨nextIdeal, ⟨tail⟩⟩ := ih
      let c : Fin data.orderedClusterCount := ⟨k, hk⟩
      let certificate := Classical.choice
        (data.nonempty_orderedClusterPreprocessedAlgebraicReductionCertificate
          R higher c (fixedSteps c) (fixedOrder c) nextIdeal
          (krullDim := krullDim k))
      exact ⟨certificate.terminalized.coefficientIdeal,
        ⟨OrderedClusterPreprocessedAlgebraicDescent.step
          k hk tail certificate⟩⟩)
    ⟨initialIdeal,
      ⟨OrderedClusterPreprocessedAlgebraicDescent.top⟩⟩
    (Nat.zero_le _)

/-- Over real-analytic germs, the proved Noetherianity and exact prefix-ring
Krull bounds discharge every assumption of the coherent preprocessed
descent. -/
theorem exists_orderedClusterPreprocessedAlgebraicDescent_realAnalyticGerm
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ)
    (fixedSteps : data.OrderedClusterIndividualStepPlan)
    (fixedOrder : data.OrderedClusterFinalOrderPlan)
    (initialIdeal : Ideal
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher
        data.orderedClusterCount)) :
    ∃ finalIdeal : Ideal
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0),
      Nonempty (OrderedClusterPreprocessedAlgebraicDescent
        (RealAnalyticGerm p) data higher fixedSteps fixedOrder initialIdeal 0
          (Nat.zero_le _) finalIdeal) := by
  letI : Algebra ℚ (RealAnalyticGerm p) :=
    ((algebraMap ℝ (RealAnalyticGerm p)).comp
      (algebraMap ℚ ℝ)).toAlgebra
  letI : ∀ k, Algebra ℚ
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) :=
    fun _ ↦ inferInstance
  letI : ∀ k, IsNoetherianRing
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) :=
    fun _ ↦ inferInstance
  letI : ∀ k, Ring.KrullDimLE
      (orderedClusterPrefixAnalyticKrullBound (p := p) data higher k)
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) :=
    fun k ↦ data.orderedClusterPrefixRing_krullDimLE higher k
  exact data.exists_orderedClusterPreprocessedAlgebraicDescent
    (RealAnalyticGerm p) higher fixedSteps fixedOrder initialIdeal
      (orderedClusterPrefixAnalyticKrullBound (p := p) data higher)

/-- The cluster-size losses accumulated above the current prefix give the
exact lower height retained after all corresponding preprocessing and
simultaneous reductions. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.prefixHeight_le
    {R : Type u} [CommRing R] [IsNoetherianRing R]
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
    (p : ℕ)
    (hheight : ((p + data.orderedClusterPrefixSize
      data.orderedClusterCount : ℕ) : ENat) ≤ initialIdeal.height) :
    ((p + data.orderedClusterPrefixSize k : ℕ) : ENat) ≤
      stageIdeal.height := by
  induction descent with
  | top => simpa using hheight
  | @step k hk nextIdeal tail certificate ih =>
      apply data.orderedClusterPreprocessedAlgebraicReduction_preserves_baseHeight
        R higher ⟨k, hk⟩ (fixedSteps ⟨k, hk⟩)
        (fixedOrder ⟨k, hk⟩) nextIdeal certificate
        (p + data.orderedClusterPrefixSize k)
      have hnext := ih
      rw [data.orderedClusterPrefixSize_succ hk] at hnext
      simpa only [Nat.cast_add, add_assoc] using hnext

/-- After every ordered cluster has been eliminated, an initial height of
`p + m` leaves height at least `p` in the zero-prefix coefficient ideal. -/
theorem OrderedClusterPreprocessedAlgebraicDescent.finalHeight_le
    {R : Type u} [CommRing R] [IsNoetherianRing R]
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
    (p : ℕ) (hheight : ((p + m : ℕ) : ENat) ≤ initialIdeal.height) :
    (p : ENat) ≤ finalIdeal.height := by
  have h := descent.prefixHeight_le p (by
    simpa only [data.orderedClusterPrefixSize_top] using hheight)
  simpa using h

/-- Drop a nested preprocessed descent to any later prefix stage, retaining
the dependent stage ideal. -/
def OrderedClusterPreprocessedAlgebraicDescent.tailAt
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
    Σ ideal : Ideal (data.OrderedClusterPrefixRing R higher j),
      OrderedClusterPreprocessedAlgebraicDescent R data higher
        fixedSteps fixedOrder initialIdeal j hj ideal := by
  induction descent generalizing j with
  | top =>
      have h : j = data.orderedClusterCount := Nat.le_antisymm hj hkj
      subst j
      exact ⟨initialIdeal,
        OrderedClusterPreprocessedAlgebraicDescent.top⟩
  | @step k hk nextIdeal tail certificate ih =>
      by_cases h : j = k
      · subst j
        exact ⟨certificate.terminalized.coefficientIdeal,
          OrderedClusterPreprocessedAlgebraicDescent.step
            k hk tail certificate⟩
      · exact ih j (by omega) hj

/-- Complete local data at a nonterminal stage of a preprocessed ordered
cluster descent. -/
structure OrderedClusterPreprocessedAlgebraicStage
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ)
    (fixedSteps : data.OrderedClusterIndividualStepPlan)
    (fixedOrder : data.OrderedClusterFinalOrderPlan)
    (initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount))
    (j : ℕ) (hj : j < data.orderedClusterCount) where
  currentIdeal : Ideal (data.OrderedClusterPrefixRing R higher j)
  currentDescent : OrderedClusterPreprocessedAlgebraicDescent R data higher
    fixedSteps fixedOrder initialIdeal j (Nat.le_of_lt hj) currentIdeal
  nextIdeal : Ideal (data.OrderedClusterPrefixRing R higher (j + 1))
  tail : OrderedClusterPreprocessedAlgebraicDescent R data higher
    fixedSteps fixedOrder initialIdeal (j + 1) hj nextIdeal
  certificate : ClusterAlgebraicReductionCertificate
    (data.OrderedClusterPrefixRing R higher j)
    (data.orderedCluster ⟨j, hj⟩).card (fun _ ↦ higher)
    (data.orderedClusterPreprocessedCurriedIdeal R higher ⟨j, hj⟩
      (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) nextIdeal)
  currentIdeal_eq_coefficientIdeal :
    currentIdeal = certificate.terminalized.coefficientIdeal

/-- Extract the complete local view at every natural index below the ordered
cluster count. -/
def OrderedClusterPreprocessedAlgebraicDescent.stageAt
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
    OrderedClusterPreprocessedAlgebraicStage R data higher fixedSteps
      fixedOrder initialIdeal j hj := by
  obtain ⟨currentIdeal, currentDescent⟩ :=
    descent.tailAt j (Nat.zero_le _) (Nat.le_of_lt hj)
  cases currentDescent with
  | top => exact (Nat.lt_irrefl _ hj).elim
  | @step j hj nextIdeal tail certificate =>
      exact {
        currentIdeal := certificate.terminalized.coefficientIdeal
        currentDescent :=
          OrderedClusterPreprocessedAlgebraicDescent.step
            j hj tail certificate
        nextIdeal := nextIdeal
        tail := tail
        certificate := certificate
        currentIdeal_eq_coefficientIdeal := rfl
      }

/-- The literal prefix ideal before individual preprocessing at a stage. -/
abbrev OrderedClusterPreprocessedAlgebraicStage.preprocessingInput
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPreprocessedAlgebraicStage R data higher
      fixedSteps fixedOrder initialIdeal j hj) :=
  stage.nextIdeal

/-- The literal prefix ideal after every individual decrement at a stage. -/
abbrev OrderedClusterPreprocessedAlgebraicStage.preprocessingOutput
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPreprocessedAlgebraicStage R data higher
      fixedSteps fixedOrder initialIdeal j hj) :=
  data.orderedClusterIndividuallyPreprocessedIdeal R higher ⟨j, hj⟩
    (fixedSteps ⟨j, hj⟩) stage.nextIdeal

/-- The exact curried ideal consumed by the simultaneous certificate at a
stage. -/
abbrev OrderedClusterPreprocessedAlgebraicStage.reductionInput
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {j : ℕ} {hj : j < data.orderedClusterCount}
    (stage : OrderedClusterPreprocessedAlgebraicStage R data higher
      fixedSteps fixedOrder initialIdeal j hj) :=
  data.orderedClusterPreprocessedCurriedIdeal R higher ⟨j, hj⟩
    (fixedSteps ⟨j, hj⟩) (fixedOrder ⟨j, hj⟩) stage.nextIdeal

end RepresentativeClusterSubsequence
end AbelFormalization
