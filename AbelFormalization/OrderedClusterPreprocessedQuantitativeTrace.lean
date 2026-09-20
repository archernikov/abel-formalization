import AbelFormalization.OrderedClusterPreprocessedAlgebraicDescentTraceData
import AbelFormalization.OrderedClusterIndividualQuantitativeTrace
import AbelFormalization.SeparatedDependentCoefficientwiseTrace

/-!
# Quantitative propagation through the full preprocessed ordered-cluster trace

The flattened algebraic trace contains, for each ordered cluster, its finite
individual balancing segment followed by the first simultaneous central
operation and the extra retained simultaneous operations.  The coefficient
ring changes with the cluster, so a single homogeneous family of generators
cannot describe all global boundaries.

This module packages the remaining individual analytic inputs dependently in
the cluster index.  It compresses each simultaneous portion to one explicit
backward callback whose source is the preceding dependent boundary package
and whose target is the last boundary of the cluster's individual trace.
The individual segment is then proved here by the concrete ordered-cluster
quantitative trace theorem.  Thus the callback is exactly the seam to be
filled by the simultaneous real-jet trace; individual hierarchy, matrix,
weight, identity, and generator-span arguments are not repeated.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped Topology

universe u v

/-- Dependent forward composition across finite boundaries.  This small
combinator permits the type of the propagated package to change at every
successor, as happens when ordered-prefix coefficient rings change. -/
def finLastOfZeroOfSucc
    {n : ℕ} (P : Fin (n + 1) → Type v)
    (step : ∀ i : Fin n, P i.castSucc → P i.succ)
    (hzero : P 0) : P (Fin.last n) :=
  Fin.induction hzero step (Fin.last n)

/-- The same dependent composition starting at an arbitrary finite boundary.
Only successor maps at or above that boundary are required. -/
noncomputable def finLastOfBoundaryOfSucc
    {n : ℕ} (P : Fin (n + 1) → Type v)
    (first : Fin (n + 1))
    (step : ∀ i : Fin n, first.val ≤ i.val →
      P i.castSucc → P i.succ)
    (hfirst : P first) : P (Fin.last n) := by
  let motive := fun (k : ℕ) (_hk : first.val ≤ k) ↦
    ∀ hkn : k ≤ n, Nonempty (P ⟨k, Nat.lt_succ_of_le hkn⟩)
  have hbase : motive first.val (Nat.le_refl _) := by
    intro hkn
    have hindex :
        (⟨first.val, Nat.lt_succ_of_le hkn⟩ : Fin (n + 1)) = first :=
      Fin.ext rfl
    rw [hindex]
    exact ⟨hfirst⟩
  have hsucc : ∀ k (hfk : first.val ≤ k), motive k hfk →
      motive (k + 1) (Nat.le.step hfk) := by
    intro k hfk ih hsuccN
    have hklt : k < n := Nat.lt_of_succ_le hsuccN
    let i : Fin n := ⟨k, hklt⟩
    obtain ⟨hraw⟩ := ih (Nat.le_of_lt hklt)
    have hprevIndex :
        (⟨k, Nat.lt_succ_of_le (Nat.le_of_lt hklt)⟩ : Fin (n + 1)) =
          i.castSucc := Fin.ext rfl
    have hprev : P i.castSucc := by
      rw [← hprevIndex]
      exact hraw
    have hout := step i hfk hprev
    have houtIndex : i.succ =
        (⟨k + 1, Nat.lt_succ_of_le hsuccN⟩ : Fin (n + 1)) :=
      Fin.ext rfl
    rw [← houtIndex]
    exact ⟨hout⟩
  have hlast : motive n (Nat.le_of_lt_succ first.isLt) :=
    @Nat.le_induction first.val motive hbase hsucc n
      (Nat.le_of_lt_succ first.isLt)
  exact Classical.choice (hlast le_rfl)

namespace RepresentativeClusterSubsequence
namespace OrderedClusterPreprocessedAlgebraicDescent

variable {m : ℕ} {time : ℕ → Fin m → ℝ}

/-- All residual analytic data for the individual portions of a full
preprocessed descent.  Every estimate is indexed by its cluster and, where
appropriate, by the individual balancing step. -/
structure IndividualQuantitativeInputs
    (R : Type u) [CommRing R]
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ)
    (fixedSteps : data.OrderedClusterIndividualStepPlan)
    (A : ℝ → ℝ) (φ : ℕ → ℕ)
    (coefficientMap : R →+* (ℕ → ℝ)) where
  boundary : (c : Fin data.orderedClusterCount) →
    data.OrderedClusterIndividualQuantitativeBoundaryData
      higher c A φ (fixedSteps c)
  plans : (c : Fin data.orderedClusterCount) → ∀ n,
    ClusterBalancingPlan
      (data.orderedClusterRawTime (φ n) c)
      (data.orderedClusterMinTime c (φ n))
  fixed_steps : ∀ c n, (plans c n).steps = fixedSteps c
  separationConstant : Fin data.orderedClusterCount → ℝ
  N : Fin data.orderedClusterCount → ℝ
  separationConstant_pos : ∀ c, 0 < separationConstant c
  five_le_N : ∀ c, 5 ≤ N c
  base_tendsto : ∀ c,
    Tendsto (fun n ↦ data.orderedClusterMinTime c (φ n)) atTop atTop
  separated : ∀ c, ∀ᶠ n in atTop,
    ∀ i k : Fin (data.orderedClusterTailSize c + 1), i ≠ k →
      separationConstant c /
          inverse A (data.orderedClusterMinTime c (φ n) - N c) ≤
        integerDistance
          (data.orderedClusterRawTime (φ n) c i -
            data.orderedClusterRawTime (φ n) c k)
  coefficient_bound : ∀ c q r,
    HasPolynomialUpperBound atTop
      (data.orderedClusterIndividualBoundaryScale
        A φ c (fixedSteps c) q)
      (coefficientMap r)
  boundary_coordinate_bound : ∀ c q z,
    HasPolynomialUpperBound atTop
      (data.orderedClusterIndividualBoundaryScale
        A φ c (fixedSteps c) q)
      ((boundary c).value q z)
  base_coordinate_bound : ∀ c j z,
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale
        A φ c (fixedSteps c) j.succ)
      ((boundary c).baseValue j z)
  main_bound : ∀ c j x,
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale
        A φ c (fixedSteps c) j.succ)
      (realJetMainAssignment A
        (data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime (φ q) c)
          (fixedSteps c) j)
        (data.orderedClusterQuantitativeStepDerivativeCount
          higher c (fixedSteps c) j) x)
  central_coordinate_bound : ∀ c j x,
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale
        A φ c (fixedSteps c) j.succ)
      (fun n ↦ realCentralTransferCentralValue A
        (fun i ↦ data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime (φ q) c)
          (fixedSteps c) j i n)
        (data.orderedClusterQuantitativeStepDerivativeCount
          higher c (fixedSteps c) j) x)
  source_coordinate_bound : ∀ c j x,
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale
        A φ c (fixedSteps c) j.castSucc)
      (realJetActualAssignment
        (data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime (φ q) c)
          (fixedSteps c) j)
        (data.orderedClusterQuantitativeStepDerivativeCount
          higher c (fixedSteps c) j)
        ((boundary c).jets j) x)
  jet_error : ∀ c j i
      (r : Fin (data.orderedClusterQuantitativeStepDerivativeCount
        higher c (fixedSteps c) j i)),
    Asymptotics.SuperpolynomialDecay atTop
      (data.orderedClusterBalancingPrefixScale
        A φ c (fixedSteps c) j.succ)
      (fun n ↦ ((boundary c).jets j n i).error r)

namespace FullTransferTraceData

noncomputable local instance orderedClusterPreprocessedQuantitativeBlockDecidableEq
    (data : RepresentativeClusterSubsequence time) (k : ℕ) :
    DecidableEq (data.OrderedClusterPrefixBlock k) :=
  Classical.decEq _

/-- The dependent lower-bound package at a cluster boundary.  Boundary zero
is an arbitrary caller-supplied package type; this permits a terminal
time-ideal or last-central package to be connected without identifying it
with the final coefficient ideal.  Boundary `c+1` is the incoming literal
prefix ideal of cluster `c`, after its individual segment has been traversed
backwards. -/
def ClusterBoundaryLower
    {R : Type u} [CommRing R]
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (_trace : descent.FullTransferTraceData)
    {A : ℝ → ℝ} (φ : ℕ → ℕ)
    (coefficientMap : R →+* (ℕ → ℝ))
    (individual : IndividualQuantitativeInputs
      R data higher fixedSteps A φ coefficientMap)
    (bottomBoundary : Type u)
    (q : Fin (data.orderedClusterCount + 1)) : Type u :=
  Fin.cases bottomBoundary
    (fun c ↦ data.OrderedClusterIndividualBoundaryLower
      R higher c A φ (fixedSteps c)
      (descent.clusterStage c).preprocessingInput coefficientMap
      (individual.boundary c) 0)
    q

/-- The narrow interface for the simultaneous part of every cluster.  The
callback encompasses the flattened `.firstSimultaneous` operation and all
`.extraRetained` operations selected by `trace.stage c`; it must bridge from
the dependent lower package below the cluster to the terminal boundary of
that cluster's individual preprocessing trace. -/
abbrev SimultaneousSegmentBackward
    {R : Type u} [CommRing R]
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    {A : ℝ → ℝ} (φ : ℕ → ℕ)
    (coefficientMap : R →+* (ℕ → ℝ))
    (individual : IndividualQuantitativeInputs
      R data higher fixedSteps A φ coefficientMap)
    (bottomBoundary : Type u) :=
  ∀ c : Fin data.orderedClusterCount,
    trace.ClusterBoundaryLower φ coefficientMap individual
        bottomBoundary c.castSucc →
      data.OrderedClusterIndividualBoundaryLower
        R higher c A φ (fixedSteps c)
        (descent.clusterStage c).preprocessingInput coefficientMap
        (individual.boundary c)
        (Fin.last
          (data.orderedClusterPrefixIndividualSteps c
            (fixedSteps c)).length)

/-- The same simultaneous-segment interface restricted to clusters at or
above an arbitrary starting boundary.  In particular, starting at boundary
one skips cluster zero entirely, so a separately constructed localization
and cluster-zero transfer can feed this global composition directly. -/
abbrev SimultaneousSegmentBackwardFrom
    {R : Type u} [CommRing R]
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    {A : ℝ → ℝ} (φ : ℕ → ℕ)
    (coefficientMap : R →+* (ℕ → ℝ))
    (individual : IndividualQuantitativeInputs
      R data higher fixedSteps A φ coefficientMap)
    (bottomBoundary : Type u)
    (first : Fin (data.orderedClusterCount + 1)) :=
  ∀ c : Fin data.orderedClusterCount, first.val ≤ c.val →
    trace.ClusterBoundaryLower φ coefficientMap individual
        bottomBoundary c.castSucc →
      data.OrderedClusterIndividualBoundaryLower
        R higher c A φ (fixedSteps c)
        (descent.clusterStage c).preprocessingInput coefficientMap
        (individual.boundary c)
        (Fin.last
          (data.orderedClusterPrefixIndividualSteps c
            (fixedSteps c)).length)

/-- Backward propagation through every cluster at or above `first` in the
flattened full transfer trace.  The simultaneous operations are compressed
to the explicit callback; each individual portion is discharged by the
ordered-cluster individual trace theorem. -/
noncomputable def clusterBoundaryLower_last_of_boundary
    {R : Type u} [CommRing R]
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (φ : ℕ → ℕ)
    (coefficientMap : R →+* (ℕ → ℝ))
    (individual : IndividualQuantitativeInputs
      R data higher fixedSteps A φ coefficientMap)
    (bottomBoundary : Type u)
    (first : Fin (data.orderedClusterCount + 1))
    (hsimultaneous : trace.SimultaneousSegmentBackwardFrom
      φ coefficientMap individual bottomBoundary first)
    (hfirst : trace.ClusterBoundaryLower φ coefficientMap individual
      bottomBoundary first) :
    trace.ClusterBoundaryLower φ coefficientMap individual
      bottomBoundary (Fin.last data.orderedClusterCount) := by
  let P := trace.ClusterBoundaryLower φ coefficientMap individual
    bottomBoundary
  apply finLastOfBoundaryOfSucc P first
  · intro c hlower hboundary
    have hterminal := hsimultaneous c hlower hboundary
    have hincoming :=
      (trace.stage c).individualDisplayed.boundaryLower_zero_of_last
        R data higher c hA coefficientMap φ
        (individual.plans c) (individual.fixed_steps c)
        (individual.separationConstant_pos c) (individual.five_le_N c)
        (individual.base_tendsto c) (individual.separated c)
        (individual.boundary c)
        (individual.coefficient_bound c)
        (individual.boundary_coordinate_bound c)
        (individual.base_coordinate_bound c)
        (individual.main_bound c)
        (individual.central_coordinate_bound c)
        (individual.source_coordinate_bound c)
        (individual.jet_error c) hterminal
    exact hincoming
  · exact hfirst

/-- The boundary-zero specialization of
`clusterBoundaryLower_last_of_boundary`.  The boundary-zero package remains
caller chosen; no identification with the final coefficient ideal or a time
ideal is imposed here. -/
noncomputable def clusterBoundaryLower_last_of_bottom
    {R : Type u} [CommRing R]
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (φ : ℕ → ℕ)
    (coefficientMap : R →+* (ℕ → ℝ))
    (individual : IndividualQuantitativeInputs
      R data higher fixedSteps A φ coefficientMap)
    (bottomBoundary : Type u)
    (hsimultaneous : trace.SimultaneousSegmentBackward
      φ coefficientMap individual bottomBoundary)
    (hbottom : trace.ClusterBoundaryLower φ coefficientMap individual
      bottomBoundary 0) :
    trace.ClusterBoundaryLower φ coefficientMap individual
      bottomBoundary (Fin.last data.orderedClusterCount) :=
  trace.clusterBoundaryLower_last_of_boundary hA φ coefficientMap individual
    bottomBoundary 0 (fun c _ ↦ hsimultaneous c) hbottom

/-- Starting at boundary one propagates through clusters `1, ..., last` and
does not require a boundary-zero package.  This is the entry point for a
separate localization plus cluster-zero argument that has already produced
the lower package on cluster zero's incoming prefix-one ideal. -/
noncomputable def clusterBoundaryLower_last_of_one
    {R : Type u} [CommRing R]
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    {descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal}
    (trace : descent.FullTransferTraceData)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (φ : ℕ → ℕ)
    (coefficientMap : R →+* (ℕ → ℝ))
    (individual : IndividualQuantitativeInputs
      R data higher fixedSteps A φ coefficientMap)
    (bottomBoundary : Type u)
    (hcount : 0 < data.orderedClusterCount)
    (hsimultaneous : trace.SimultaneousSegmentBackwardFrom
      φ coefficientMap individual bottomBoundary
        ⟨1, Nat.succ_lt_succ hcount⟩)
    (hone : trace.ClusterBoundaryLower φ coefficientMap individual
      bottomBoundary ⟨1, Nat.succ_lt_succ hcount⟩) :
    trace.ClusterBoundaryLower φ coefficientMap individual
      bottomBoundary (Fin.last data.orderedClusterCount) :=
  trace.clusterBoundaryLower_last_of_boundary hA φ coefficientMap individual
    bottomBoundary ⟨1, Nat.succ_lt_succ hcount⟩ hsimultaneous hone

end FullTransferTraceData
end OrderedClusterPreprocessedAlgebraicDescent
end RepresentativeClusterSubsequence
end AbelFormalization
