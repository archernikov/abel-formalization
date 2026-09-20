import AbelFormalization.BottomPolynomialQuantitativeSeed
import AbelFormalization.HermiteRankTopPrefixPreprocessedSequenceBoundary

/-!
# Quantitative bottom seed for the preprocessed Hermite-rank descent

The preprocessed sequence boundary already contains a nonzero real
univariate polynomial in the bottom cluster's time ideal.  This module
chooses a padded finite presentation of that exact ideal and applies the
generic polynomial lower-bound result.  Thus the quantitative backward trace
starts from the polynomial extracted by the paper's rank argument, rather
than from a separately postulated terminal lower bound.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped Polynomial Topology

universe u

namespace RepresentativeClusterSubsequence

variable {ι : Type*}

/-- The nonzero bottom polynomial stored by a preprocessed Hermite-rank trace
gives an evaluated inverse-power lower bound for a finite generating family
of that trace's literal bottom time ideal. -/
noncomputable def PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTimeEvaluatedLowerBound
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    {X : Type u} {l : Filter X} {scale : X → ℝ}
    (coefficientEval :
      data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0 →+*
        (X → ℝ))
    (timeValue :
      Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → X → ℝ)
    (hscalar : ∀ r x,
      coefficientEval
          (algebraMap ℝ
            (data.OrderedClusterPrefixRing
              (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0) r) x =
        r)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hcoefficient : ∀ r,
      HasPolynomialUpperBound l scale (coefficientEval r))
    (hcoordinate : ∀ i,
      HasPolynomialUpperBound l scale (timeValue i))
    (htime : Tendsto (timeValue trace.bottomIndex) l atTop) :
    EvaluatedPaddedIdealLowerBound
      (Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card)
      l scale coefficientEval timeValue
      (trace.descent.stageAt 0 data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.timeIdeal := by
  let family := Classical.choice
    (nonempty_paddedIdealGeneratorFamily _
      (trace.descent.stageAt 0 data.orderedClusterCount_pos_of_nonempty).certificate.terminalized.timeIdeal)
  exact family.evaluatedLowerBound_of_scalarUnivariateEmbedding_mem
    coefficientEval timeValue hscalar hscale hcoefficient hcoordinate
    trace.bottomIndex trace.bottomPolynomial trace.bottomPolynomial_ne htime
    trace.bottomEmbedding_mem

end RepresentativeClusterSubsequence
end AbelFormalization
