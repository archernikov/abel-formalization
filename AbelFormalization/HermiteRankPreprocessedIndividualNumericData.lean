import AbelFormalization.HermiteRankPreprocessedIndividualQuantitativeInputs
import AbelFormalization.IndividualCentralNumericQuantitativeTransfer

/-!
# Numeric individual data for the preprocessed Hermite boundary

Literal flat Hermite assignments do not concatenate through repeated
individual logarithmic decrements.  After a decrement the selected derivative
coordinates are exact derivatives, whereas a fresh Hermite jet at the next
decrement contains contour-Hermite coefficients.  The first theorem records
the exact discrepancy: equality with the exact derivative jet is equivalent
to vanishing Hermite error, while the analytic construction supplies rapid
decay rather than literal vanishing.

The production interface below therefore uses the coefficientwise numeric
recursion.  It retains only eventual linear-combination identities between
finite displayed families at adjacent boundaries.  It assumes no global
evaluation homomorphism from `RealAnalyticGerm` and no equality of full flat
assignments.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped Topology BigOperators

/-- The exact obstruction to replacing a Hermite source jet by the exact
derivative source jet.  Their normalized central terms cancel, leaving the
Hermite error. -/
theorem RealCentralJetSubstitutionData.exp_mul_sourceJet_sub_exact_eq_error
    {A : ℝ → ℝ} (hA : IsAbel A) {u : ℝ} (hu : 0 < u) {d : ℕ}
    (J : RealCentralJetSubstitutionData A u d) (r : Fin d) :
    Real.exp (((r.val + 1 : ℕ) : ℝ) * u) *
        (J.sourceJet r -
          (hA.realDerivativeJetSubstitutionData hu d).sourceJet r) =
      J.error r := by
  have hJ := J.normalized_sourceJet r
  have hExact :=
    (hA.realDerivativeJetSubstitutionData hu d).normalized_sourceJet r
  rw [hA.realDerivativeJetSubstitutionData_error] at hExact
  linarith

/-- A Hermite source coordinate agrees literally with the exact derivative
coordinate precisely when its Hermite error vanishes. -/
theorem RealCentralJetSubstitutionData.sourceJet_eq_exact_iff_error_eq_zero
    {A : ℝ → ℝ} (hA : IsAbel A) {u : ℝ} (hu : 0 < u) {d : ℕ}
    (J : RealCentralJetSubstitutionData A u d) (r : Fin d) :
    J.sourceJet r =
        (hA.realDerivativeJetSubstitutionData hu d).sourceJet r ↔
      J.error r = 0 := by
  constructor
  · intro h
    have hdiff := J.exp_mul_sourceJet_sub_exact_eq_error hA hu r
    rw [h, sub_self, mul_zero] at hdiff
    exact hdiff.symm
  · intro herror
    have hdiff := J.exp_mul_sourceJet_sub_exact_eq_error hA hu r
    rw [herror] at hdiff
    have hexp : Real.exp (((r.val + 1 : ℕ) : ℝ) * u) ≠ 0 :=
      ne_of_gt (Real.exp_pos _)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hexp)

variable {ι : Type*} {A : ℝ → ℝ} {m p a : ℕ} [Nonempty (Fin m)]

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

noncomputable local instance individualNumericBlockDecidableEq
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- At an actual shifted individual step, replacing the concrete Hermite jet
by the exact derivative jet is a literal equality exactly when that Hermite
coordinate has zero error.  Thus rapid decay alone cannot build the flat
assignment equality required by `IndividualBoundaryChain`. -/
theorem individualQuantitativeHermite_sourceJet_eq_exact_iff_error_eq_zero
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) (n : ℕ) (i : Fin 1)
    (r : Fin (paperRankHermitePositiveDerivativeCount boundary.S)) :
    (boundary.individualQuantitativeRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c j n i).sourceJet r =
      (hA.realDerivativeJetSubstitutionData
        (u := boundary.individualPostLogScale D representative offset radius
          Fsys x w₀ hw₀ data c j i
          (n + boundary.individualQuantitativeTail D representative offset
            radius Fsys x w₀ hw₀ data hA))
        (hA.inverse_pos _) (paperRankHermitePositiveDerivativeCount boundary.S)).sourceJet r ↔
    (boundary.individualQuantitativeRealJetSequence D representative offset
        radius Fsys x w₀ hw₀ data hA c j n i).error r = 0 := by
  exact (boundary.individualQuantitativeRealJetSequence D representative offset
    radius Fsys x w₀ hw₀ data hA c j n i).sourceJet_eq_exact_iff_error_eq_zero
      hA (hA.inverse_pos _) r

/-- The individual algebraic-step list selected at one paper cluster. -/
abbrev individualNumericSteps (c : Fin data.orderedClusterCount) :=
  data.orderedClusterPrefixIndividualSteps c
    (boundary.preprocessed.fixedSteps c)

/-- The displayed individual trace selected at one paper cluster. -/
abbrev individualNumericDisplayed (c : Fin data.orderedClusterCount) :=
  (boundary.preprocessed.transferTrace.stage c).individualDisplayed

/-- The weakest compatibility required to concatenate numeric individual
steps.  Each boundary and each displayed before/after family may have its own
finite cardinality.  Only eventual linear-combination identities and bounds
for their numeric change matrices are retained. -/
structure IndividualNumericBoundaryCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) where
  boundaryCount : Fin ((boundary.individualNumericSteps D representative
    offset radius Fsys x w₀ hw₀ data c).length + 1) → ℕ
  boundaryValue : (q : Fin ((boundary.individualNumericSteps D representative
    offset radius Fsys x w₀ hw₀ data c).length + 1)) →
    Fin (boundaryCount q + 1) → ℕ → ℝ
  afterValue : (j : Fin (boundary.individualNumericSteps D representative
    offset radius Fsys x w₀ hw₀ data c).length) →
    Fin (((boundary.individualNumericDisplayed D representative offset radius
      Fsys x w₀ hw₀ data c).displayed j).central.count + 1) → ℕ → ℝ
  beforeValue : (j : Fin (boundary.individualNumericSteps D representative
    offset radius Fsys x w₀ hw₀ data c).length) →
    Fin (((boundary.individualNumericDisplayed D representative offset radius
      Fsys x w₀ hw₀ data c).displayed j).source.count + 1) → ℕ → ℝ
  afterBoundaryCoefficient :
    (j : Fin (boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length) →
    Fin (boundaryCount j.succ + 1) →
    Fin (((boundary.individualNumericDisplayed D representative offset radius
      Fsys x w₀ hw₀ data c).displayed j).central.count + 1) → ℕ → ℝ
  beforeBoundaryCoefficient :
    (j : Fin (boundary.individualNumericSteps D representative offset radius
      Fsys x w₀ hw₀ data c).length) →
    Fin (((boundary.individualNumericDisplayed D representative offset radius
      Fsys x w₀ hw₀ data c).displayed j).source.count + 1) →
    Fin (boundaryCount j.castSucc + 1) → ℕ → ℝ
  afterBoundaryCoefficient_bound : ∀ j b q,
    HasPolynomialUpperBound atTop
      (data.orderedClusterIndividualBoundaryScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (afterBoundaryCoefficient j b q)
  beforeBoundaryCoefficient_bound : ∀ j q b,
    HasPolynomialUpperBound atTop
      (data.orderedClusterIndividualBoundaryScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.castSucc)
      (beforeBoundaryCoefficient j q b)
  afterBoundaryIdentity : ∀ j, ∀ᶠ n in atTop, ∀ b,
    boundaryValue j.succ b n =
      ∑ q, afterBoundaryCoefficient j b q n * afterValue j q n
  beforeBoundaryIdentity : ∀ j, ∀ᶠ n in atTop, ∀ q,
    beforeValue j q n =
      ∑ b, beforeBoundaryCoefficient j q b n *
        boundaryValue j.castSucc b n

/-- The numeric compatibility record feeds the existing zero-step-safe
reverse recursion directly.  The one-step callbacks may be constructed with
`OrderedClusterIndividualDisplayedTraceData.beforeGenerator_lower_of_afterGenerator_lower_numeric`;
no full assignment equality or coefficient-ring homomorphism is involved. -/
theorem IndividualNumericBoundaryCompatibility.boundaryLower_zero_of_last
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (compatibility : boundary.IndividualNumericBoundaryCompatibility D
      representative offset radius Fsys x w₀ hw₀ data hA c)
    (hstep : ∀ j,
      HasInversePowerLowerBound atTop
        (data.orderedClusterIndividualBoundaryScale A
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA) c
          (boundary.preprocessed.fixedSteps c) j.succ)
        (compatibility.afterValue j) →
      HasInversePowerLowerBound atTop
        (data.orderedClusterIndividualBoundaryScale A
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA) c
          (boundary.preprocessed.fixedSteps c) j.castSucc)
        (compatibility.beforeValue j))
    (hlast : HasInversePowerLowerBound atTop
      (data.orderedClusterIndividualBoundaryScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c)
        (Fin.last (boundary.individualNumericSteps D representative offset
          radius Fsys x w₀ hw₀ data c).length))
      (compatibility.boundaryValue
        (Fin.last (boundary.individualNumericSteps D representative offset
          radius Fsys x w₀ hw₀ data c).length))) :
    HasInversePowerLowerBound atTop
      (data.orderedClusterIndividualBoundaryScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) 0)
      (compatibility.boundaryValue 0) := by
  apply (boundary.individualNumericDisplayed D representative offset radius
    Fsys x w₀ hw₀ data c).boundaryLower_zero_of_last_numeric
      (RealAnalyticGerm p) atTop
      (data.orderedClusterIndividualBoundaryScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c))
      compatibility.boundaryCount compatibility.boundaryValue
      compatibility.afterValue compatibility.beforeValue
      compatibility.afterBoundaryCoefficient
      compatibility.beforeBoundaryCoefficient
  · intro q
    exact Filter.Eventually.of_forall fun n ↦ one_le_two.trans
      (two_le_clusterBalancingPrefixScale A
        (fun k ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA k) c)
        (boundary.preprocessed.fixedSteps c) q.val n)
  · exact compatibility.afterBoundaryCoefficient_bound
  · exact compatibility.beforeBoundaryCoefficient_bound
  · exact compatibility.afterBoundaryIdentity
  · exact compatibility.beforeBoundaryIdentity
  · exact hstep
  · exact hlast

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

end AbelFormalization
