import AbelFormalization.IndividualCentralRealJetIdentities
import AbelFormalization.FiniteGeneratorSpanLowerBound

/-!
# Backward quantitative propagation through all individual decrements

This module is independent of the particular analytic estimates used at one
central step.  It packages a lower bound at each ideal boundary using an
existential padded generating family, changes that family to the displayed
post-step family by equality of spans, invokes the caller's one-step transfer,
and applies finite decreasing induction.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped Topology

universe u v w

namespace IndividualCentralDisplayedTraceData

variable (R : Type u) [CommRing R]
variable {Block : Type v} [Fintype Block] [DecidableEq Block]

/-- The quantitative lower-bound state at one boundary of an individual
central trace.  Its generating family is allowed to depend on the boundary. -/
abbrev BoundaryLower
    {d : Block → ℕ} {steps : List Block}
    (I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R))
    {X : Type w} (l : Filter X)
    (scale : Fin (steps.length + 1) → X → ℝ)
    (coefficientEval : R →+* (X → ℝ))
    (value : Fin (steps.length + 1) →
      ClusterOperationSymbol Block d → X → ℝ)
    (j : Fin (steps.length + 1)) :=
  EvaluatedPaddedIdealLowerBound (ClusterOperationSymbol Block d) l
    (scale j) coefficientEval (value j)
    (individualCentralIdealBoundary R d steps I j)

/-- If every displayed decrement propagates a lower bound from its successor
boundary to its predecessor boundary, then the whole finite trace propagates
any terminal boundary lower bound back to boundary zero.

The coefficient and coordinate hypotheses are used only to replace the
terminal family supplied by the induction hypothesis with the displayed
`afterGenerator` family at the same ideal. -/
noncomputable def boundaryLower_zero_of_last
    {d : Block → ℕ} {steps : List Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {traceData : IndividualCentralIdealTraceData R d steps I}
    (displayed : IndividualCentralDisplayedTraceData R d steps I traceData)
    {X : Type w} (l : Filter X)
    (scale : Fin (steps.length + 1) → X → ℝ)
    (coefficientEval : R →+* (X → ℝ))
    (value : Fin (steps.length + 1) →
      ClusterOperationSymbol Block d → X → ℝ)
    (hscale : ∀ j, ∀ᶠ x in l, 1 ≤ scale j x)
    (hcoefficient : ∀ j r,
      HasPolynomialUpperBound l (scale j) (coefficientEval r))
    (hcoordinate : ∀ j z,
      HasPolynomialUpperBound l (scale j) (value j z))
    (hstep : ∀ j : Fin steps.length,
      HasInversePowerLowerBound l (scale j.succ)
        (fun k x ↦ MvPolynomial.eval₂Hom coefficientEval (value j.succ)
          (IndividualCentralTransferData.DisplayedData.afterGenerator R
            (displayed.displayed j) k) x) →
      HasInversePowerLowerBound l (scale j.castSucc)
        (fun k x ↦ MvPolynomial.eval₂Hom coefficientEval (value j.castSucc)
          (IndividualCentralTransferData.DisplayedData.beforeGenerator R
            (displayed.displayed j) k) x))
    (hlast : BoundaryLower R I l scale coefficientEval value
      (Fin.last steps.length)) :
    BoundaryLower R I l scale coefficientEval value 0 := by
  let motive := fun (k : ℕ) (hk : k ≤ steps.length) ↦
    BoundaryLower R I l scale coefficientEval value
      ⟨k, Nat.lt_succ_iff.mpr hk⟩
  have htop : motive steps.length le_rfl := by
    change BoundaryLower R I l scale coefficientEval value
      ⟨steps.length, Nat.lt_succ_self _⟩
    have hindex :
        (⟨steps.length, Nat.lt_succ_self _⟩ : Fin (steps.length + 1)) =
          Fin.last steps.length := Fin.ext rfl
    rw [hindex]
    exact hlast
  have hdescent : motive 0 (Nat.zero_le _) :=
    Nat.decreasingInduction (n := steps.length) (motive := motive)
      (fun k hk ih ↦ by
        let j : Fin steps.length := ⟨k, hk⟩
        let afterGenerator :=
          IndividualCentralTransferData.DisplayedData.afterGenerator R
            (displayed.displayed j)
        have hafter : HasInversePowerLowerBound l (scale j.succ)
            (fun a x ↦ MvPolynomial.eval₂Hom coefficientEval (value j.succ)
              (afterGenerator a) x) := by
          apply ih.lower_of_span_eq afterGenerator
          · exact displayed.after_span_boundary_succ R j
          · exact hscale j.succ
          · exact hcoefficient j.succ
          · exact hcoordinate j.succ
        have hbefore := hstep j hafter
        refine {
          count := (displayed.displayed j).source.count
          generator :=
            IndividualCentralTransferData.DisplayedData.beforeGenerator R
              (displayed.displayed j)
          span_eq := ?_
          lower := hbefore
        }
        exact displayed.before_span R j)
      htop (Nat.zero_le _)
  change BoundaryLower R I l scale coefficientEval value 0 at hdescent
  exact hdescent

end IndividualCentralDisplayedTraceData
end AbelFormalization
