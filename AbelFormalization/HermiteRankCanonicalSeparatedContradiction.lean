import AbelFormalization.HermiteRankAllClusterBackwardContradiction
import AbelFormalization.RestrictedBaseSeparatedContradictionInduction
import AbelFormalization.AbelNumeratorRestrictedRegularZero

/-!
# The canonical separated contradiction

The diagonal quantitative construction chooses every finite analytic trace and
every numerical separation margin needed by the all-cluster backward chain.
This file packages its unconditional contradiction as the normalized callback
used by the existing outer induction on the number of representatives.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Function

/-- Every normalized all-unbounded separated setup canonically supplies a
diagonal quantitative boundary, whose completed backward propagation is
contradictory. -/
theorem IsAbel.restrictedAllUnboundedNormalizedSeparatedContradiction
    {A : ℝ → ℝ} (hA : IsAbel A) :
    RestrictedAllUnboundedNormalizedSeparatedContradiction A := by
  intro m ι _ p a box representative offset radius _hDomain F hF x w₀ data
    _width hsubsequence _hinjective hzero hbox hbox_tendsto
    hrepresentative_tendsto _hcluster_nonempty _hcluster_disjoint
    _hcluster_cover _hminimum_tendsto _hcluster_interval _hcross_cluster
    _hcluster_gap hseparated
  obtain ⟨diagonal⟩ :=
    hA.nonempty_diagonalHermiteRankPreprocessedQuantitativeData_of_normalized
      box representative offset radius F hF x w₀ hbox data hsubsequence
      hzero hrepresentative_tendsto hbox_tendsto hseparated
  exact
    DiagonalHermiteRankPreprocessedQuantitativeData.false_of_canonicalBackwardPropagation
      (diagonal := diagonal) hA box representative offset radius F x w₀ hbox
      data

/-- The canonical backward contradiction closes the outer induction for every
number of representatives. -/
theorem IsAbel.restrictedBaseRegularZeroFiniteForRepresentativeCount_all_of_canonicalBackwardPropagation
    {A : ℝ → ℝ} (hA : IsAbel A) :
    ∀ m, RestrictedBaseRegularZeroFiniteForRepresentativeCount A m :=
  hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_all_of_normalizedSeparated
    hA.restrictedAllUnboundedNormalizedSeparatedContradiction

/-- Consequently every square numerator system in the Abel family has only
finitely many regular zeros. -/
theorem IsAbel.abelNumeratorRegularZeroFinite_of_canonicalBackwardPropagation
    {A : ℝ → ℝ} (hA : IsAbel A) :
    AbelNumeratorRegularZeroFinite A :=
  hA.abelNumeratorRegularZeroFinite_of_restrictedBase
    hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_all_of_canonicalBackwardPropagation

/-- The completed algebraic and quantitative descent supplies the paper's
zero-regularity hypothesis for the concrete Abel family. -/
theorem IsAbel.isZeroRegular_abelGeometricFamily_of_canonicalBackwardPropagation
    {A : ℝ → ℝ} (hA : IsAbel A) :
    IsZeroRegularFunctionFamily (abelGeometricFamily A) :=
  hA.isZeroRegular_abelGeometricFamily_of_restrictedBase
    hA.restrictedBaseRegularZeroFiniteForRepresentativeCount_all_of_canonicalBackwardPropagation

end AbelFormalization
