import AbelFormalization.IndividualCentralQuantitativeTrace
import AbelFormalization.IndividualCentralQuantitativeTransfer

/-!
# Quantitative propagation through one ordered-cluster individual trace

This module specializes the generic finite individual trace recursion to the
literal block list and canonical balancing-prefix scales of one ordered
cluster.  A boundary datum records one full flat assignment at every trace
boundary, together with stepwise real jets and retained-block assignments.
Its two compatibility fields say exactly that the assignment before step
`j` is the pre-log assignment and the assignment after step `j` is the
post-log assignment used by the one-step real-jet bridge.

The construction of those compatible boundary assignments from the paper's
Hermite sequence is intentionally left as an analytic input.  Once they are
available, the theorem below obtains every step from
`beforeGenerator_lower_of_afterGenerator_lower` and lets
`IndividualCentralDisplayedTraceData.boundaryLower_zero_of_last` handle the
changes of finite generating family between adjacent steps.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped Topology

universe u

namespace RepresentativeClusterSubsequence

variable {m : ℕ} {time : ℕ → Fin m → ℝ}

/-- Coherent full flat assignments at every boundary of the fixed individual
balancing trace.  The equality fields are the exact residual seam between a
concrete Hermite boundary sequence and the step-local real-jet models. -/
structure OrderedClusterIndividualQuantitativeBoundaryData
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (A : ℝ → ℝ) (φ : ℕ → ℕ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1))) where
  value : Fin
      ((data.orderedClusterPrefixIndividualSteps c fixedSteps).length + 1) →
    ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (higher + 1) (c.val + 1)) → ℕ → ℝ
  baseValue : (j : Fin fixedSteps.length) →
    ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (higher + 1) (c.val + 1)) → ℕ → ℝ
  jets : (j : Fin fixedSteps.length) → ∀ n i,
    RealCentralJetSubstitutionData A
      (data.orderedClusterIndividualPostLogScale c A
        (fun q ↦ data.orderedClusterRawTime (φ q) c)
        fixedSteps j i n)
      (data.orderedClusterQuantitativeStepDerivativeCount
        higher c fixedSteps j i)
  pre_eq : ∀ j,
    value
        (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j).castSucc =
      data.orderedClusterIndividualPreLogFlatAssignment higher c
        (fun q ↦ data.orderedClusterRawTime (φ q) c)
        fixedSteps j (baseValue j) (jets j)
  post_eq : ∀ j,
    value (data.orderedClusterIndividualStepIndexEquiv c fixedSteps j).succ =
      data.orderedClusterIndividualPostLogFlatAssignment higher c A
        (fun q ↦ data.orderedClusterRawTime (φ q) c)
        fixedSteps j (baseValue j)

/-- The boundary-indexed scale used by the generic trace recursion is the
canonical full-tuple balancing scale at the corresponding prefix length. -/
def orderedClusterIndividualBoundaryScale
    (data : RepresentativeClusterSubsequence time)
    (A : ℝ → ℝ) (φ : ℕ → ℕ)
    (c : Fin data.orderedClusterCount)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1))) :
    Fin ((data.orderedClusterPrefixIndividualSteps c fixedSteps).length + 1) →
      ℕ → ℝ :=
  fun j ↦ data.orderedClusterBalancingPrefixScale
    A φ c fixedSteps j.val

noncomputable local instance orderedClusterQuantitativeBoundaryBlockDecidableEq
    (data : RepresentativeClusterSubsequence time)
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- A packaged lower bound at one actual ordered-cluster boundary.  Its
finite generating family may differ from the displayed family used by either
neighboring step. -/
abbrev OrderedClusterIndividualBoundaryLower
    (R : Type u) [CommRing R]
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (A : ℝ → ℝ) (φ : ℕ → ℕ)
    (fixedSteps : List (Fin (data.orderedClusterTailSize c + 1)))
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1)))
    (coefficientMap : R →+* (ℕ → ℝ))
    (boundary : data.OrderedClusterIndividualQuantitativeBoundaryData
      higher c A φ fixedSteps)
    (j : Fin
      ((data.orderedClusterPrefixIndividualSteps c fixedSteps).length + 1)) :=
  IndividualCentralDisplayedTraceData.BoundaryLower
    (d := data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) (c.val + 1))
    (steps := data.orderedClusterPrefixIndividualSteps c fixedSteps)
    R I atTop
    (data.orderedClusterIndividualBoundaryScale A φ c fixedSteps)
    coefficientMap boundary.value j

namespace OrderedClusterIndividualDisplayedTraceData

variable (R : Type u) [CommRing R]
variable (data : RepresentativeClusterSubsequence time)
variable (higher : ℕ) (c : Fin data.orderedClusterCount)

/-- A terminal inverse-power lower bound propagates through every individual
balancing decrement of one ordered cluster to a packaged lower bound at the
incoming boundary.

The scale hierarchy, source/central polynomial identities, finite certificate
weight bound, and evaluated matrix bounds are discharged inside the reused
one-step theorem.  The hypotheses here are precisely the boundary
compatibility and scalar growth/error estimates still supplied by the
analytic Hermite construction. -/
noncomputable def boundaryLower_zero_of_last
    {fixedSteps : List (Fin (data.orderedClusterTailSize c + 1))}
    {I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))}
    {traceData : data.OrderedClusterIndividualIdealTraceData
      R higher c fixedSteps I}
    (displayed : data.OrderedClusterIndividualDisplayedTraceData
      R higher c fixedSteps I traceData)
    {A : ℝ → ℝ} (hA : IsAbel A)
    (coefficientMap : R →+* (ℕ → ℝ))
    (φ : ℕ → ℕ)
    (plans : ∀ n, ClusterBalancingPlan
      (data.orderedClusterRawTime (φ n) c)
      (data.orderedClusterMinTime c (φ n)))
    (hfixedSteps : ∀ n, (plans n).steps = fixedSteps)
    {N separationConstant : ℝ}
    (hseparationConstant : 0 < separationConstant)
    (hN : 5 ≤ N)
    (hbaseTop : Tendsto
      (fun n ↦ data.orderedClusterMinTime c (φ n)) atTop atTop)
    (hseparated : ∀ᶠ n in atTop,
      ∀ i k : Fin (data.orderedClusterTailSize c + 1), i ≠ k →
        separationConstant /
            inverse A (data.orderedClusterMinTime c (φ n) - N) ≤
          integerDistance
            (data.orderedClusterRawTime (φ n) c i -
              data.orderedClusterRawTime (φ n) c k))
    (boundary : data.OrderedClusterIndividualQuantitativeBoundaryData
      higher c A φ fixedSteps)
    (hcoefficient : ∀ q r,
      HasPolynomialUpperBound atTop
        (data.orderedClusterIndividualBoundaryScale A φ c fixedSteps q)
        (coefficientMap r))
    (hcoordinate : ∀ q z,
      HasPolynomialUpperBound atTop
        (data.orderedClusterIndividualBoundaryScale A φ c fixedSteps q)
        (boundary.value q z))
    (hbaseValue : ∀ j z,
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (boundary.baseValue j z))
    (hmainBound : ∀ j x,
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (realJetMainAssignment A
          (data.orderedClusterIndividualPostLogScale c A
            (fun q ↦ data.orderedClusterRawTime (φ q) c)
            fixedSteps j)
          (data.orderedClusterQuantitativeStepDerivativeCount
            higher c fixedSteps j) x))
    (hcentralValueBound : ∀ j x,
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (fun n ↦ realCentralTransferCentralValue A
          (fun i ↦ data.orderedClusterIndividualPostLogScale c A
            (fun q ↦ data.orderedClusterRawTime (φ q) c)
            fixedSteps j i n)
          (data.orderedClusterQuantitativeStepDerivativeCount
            higher c fixedSteps j) x))
    (hsourceValueBound : ∀ j x,
      HasPolynomialUpperBound atTop
        (data.orderedClusterBalancingPrefixScale
          A φ c fixedSteps j.castSucc)
        (realJetActualAssignment
          (data.orderedClusterIndividualPostLogScale c A
            (fun q ↦ data.orderedClusterRawTime (φ q) c)
            fixedSteps j)
          (data.orderedClusterQuantitativeStepDerivativeCount
            higher c fixedSteps j) (boundary.jets j) x))
    (hjetError : ∀ j i
      (r : Fin (data.orderedClusterQuantitativeStepDerivativeCount
        higher c fixedSteps j i)),
      Asymptotics.SuperpolynomialDecay atTop
        (data.orderedClusterBalancingPrefixScale A φ c fixedSteps j.succ)
        (fun n ↦ (boundary.jets j n i).error r))
    (hlast : data.OrderedClusterIndividualBoundaryLower
      R higher c A φ fixedSteps I coefficientMap boundary
      (Fin.last
        (data.orderedClusterPrefixIndividualSteps c fixedSteps).length)) :
    data.OrderedClusterIndividualBoundaryLower
      R higher c A φ fixedSteps I coefficientMap boundary 0 := by
  let scale := data.orderedClusterIndividualBoundaryScale
    A φ c fixedSteps
  have hscale : ∀ q, ∀ᶠ n in atTop, 1 ≤ scale q n := by
    intro q
    apply Filter.Eventually.of_forall
    intro n
    exact one_le_two.trans (two_le_clusterBalancingPrefixScale A
      (fun k ↦ data.orderedClusterRawTime (φ k) c)
      fixedSteps q.val n)
  apply IndividualCentralDisplayedTraceData.boundaryLower_zero_of_last
    R displayed atTop scale coefficientMap boundary.value
      hscale hcoefficient hcoordinate
  · intro j' hafter
    let e := data.orderedClusterIndividualStepIndexEquiv c fixedSteps
    let j : Fin fixedSteps.length := e.symm j'
    have hj : e j = j' := e.apply_symm_apply j'
    rw [← hj] at hafter ⊢
    have hcentralLower : HasInversePowerLowerBound atTop
        (data.orderedClusterBalancingPrefixScale
          A φ c fixedSteps j.succ)
        (fun b n ↦ MvPolynomial.eval₂Hom coefficientMap
          (data.orderedClusterIndividualPostLogFlatAssignment higher c A
            (fun q ↦ data.orderedClusterRawTime (φ q) c)
            fixedSteps j (boundary.baseValue j))
          (IndividualCentralTransferData.DisplayedData.afterGenerator R
            (displayed.displayed (e j)) b) n) := by
      simpa only [scale, e, orderedClusterIndividualBoundaryScale,
        Fin.val_succ, orderedClusterIndividualStepIndexEquiv_apply_val,
        boundary.post_eq j] using hafter
    have hcoefficientStep : ∀ r,
        HasPolynomialUpperBound atTop
          (data.orderedClusterBalancingPrefixScale
            A φ c fixedSteps j.succ)
          (coefficientMap r) := by
      intro r
      simpa only [scale, e, orderedClusterIndividualBoundaryScale,
        Fin.val_succ, orderedClusterIndividualStepIndexEquiv_apply_val]
        using hcoefficient (e j).succ r
    have hstep := displayed.beforeGenerator_lower_of_afterGenerator_lower
      R data higher c j hA coefficientMap φ plans hfixedSteps
      hseparationConstant hN hbaseTop hseparated
      (boundary.baseValue j) (boundary.jets j)
      hcoefficientStep (hbaseValue j) (hmainBound j)
      (hcentralValueBound j) (hsourceValueBound j) (hjetError j)
      hcentralLower
    simpa only [scale, e, orderedClusterIndividualBoundaryScale,
      Fin.val_castSucc, orderedClusterIndividualStepIndexEquiv_apply_val,
      boundary.pre_eq j] using hstep
  · exact hlast

end OrderedClusterIndividualDisplayedTraceData
end RepresentativeClusterSubsequence
end AbelFormalization
