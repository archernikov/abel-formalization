import AbelFormalization.HermiteRankBottomQuantitativeSeed
import AbelFormalization.TerminalTimeQuantitativeBridge

/-!
# The bottom Hermite-rank seed at the last simultaneous family

The bottom polynomial lower bound lives in the literal time ideal of cluster
zero.  The terminal localization identity for that same algebraic stage
transfers it to the last displayed central family.  This file is the thin
paper-specific adapter between those two already established results.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped Topology

namespace RepresentativeClusterSubsequence

variable {ι : Type*}

/-- The last displayed simultaneous datum of cluster zero in the selected
preprocessed Hermite-rank trace. -/
noncomputable def PaperRankHermiteTopPrefixPreprocessedTraceData.bottomLastDisplayed
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I) :=
  let c : Fin data.orderedClusterCount :=
    ⟨0, data.orderedClusterCount_pos_of_nonempty⟩
  (trace.transferTrace.stage c).simultaneousDisplayed
    (Fin.last
      (trace.descent.clusterStage c).certificate.terminalized.extraSteps)

/-- The nonzero bottom polynomial, followed by the fixed terminal
localization identity, gives an inverse-power lower bound for the last
central family at cluster zero.

The only extra analytic input is a polynomial upper bound for evaluation of
arbitrary terminal source polynomials.  It is deliberately stated uniformly,
so it immediately covers the finitely many coefficients chosen by the
localization identity. -/
theorem PaperRankHermiteTopPrefixPreprocessedTraceData.bottomLastCentralLower
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (A : ℝ → ℝ)
    (coefficientEval :
      data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0 →+*
        (ℕ → ℝ))
    (u : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → ℕ → ℝ)
    (scale : ℕ → ℝ)
    (hscalar : ∀ r n,
      coefficientEval
          (algebraMap ℝ
            (data.OrderedClusterPrefixRing
              (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0) r) n =
        r)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hcoefficient : ∀ r,
      HasPolynomialUpperBound atTop scale (coefficientEval r))
    (htimeCoordinate : ∀ i,
      HasPolynomialUpperBound atTop scale (fun n ↦ A (u i n)))
    (htime : Tendsto (fun n ↦ A (u trace.bottomIndex n)) atTop atTop)
    (hfirst : ∀ i : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card,
      HasScalarInversePowerLowerBound atTop scale
        (fun n ↦ finiteRealJetCentralEvaluationHom A coefficientEval u
          (terminalTotalDerivativeCount
            (fun _ : Fin (data.orderedCluster
              ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
                paperRankHermiteHigherCount S)) n
          (MvPolynomial.X
            (Sum.inl
              ⟨i, (0 : Fin (paperRankHermiteHigherCount S + 1))⟩))))
    (hterminalPolynomial : ∀ P : TerminalMultiblockSourceRing
        (data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0)
        (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card
        (fun _ : Fin (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
            paperRankHermiteHigherCount S)
        (Fin (data.orderedCluster
          ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card),
      HasPolynomialUpperBound atTop scale
        (fun n ↦ finiteRealJetCentralEvaluationHom A coefficientEval u
          (terminalTotalDerivativeCount
            (fun _ : Fin (data.orderedCluster
              ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
                paperRankHermiteHigherCount S)) n P)) :
    HasInversePowerLowerBound atTop scale
      (fun j n ↦ finiteRealJetCentralEvaluationHom A coefficientEval u
        (terminalTotalDerivativeCount
          (fun _ : Fin (data.orderedCluster
            ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
              paperRankHermiteHigherCount S)) n
        (trace.bottomLastDisplayed.central.generator j)) := by
  let localization := Classical.choice
    trace.bottomLastDisplayed.nonempty_terminalLocalizationData
  let timeLower := trace.bottomTimeEvaluatedLowerBound coefficientEval
    (fun i n ↦ A (u i n)) hscalar hscale hcoefficient htimeCoordinate htime
  exact trace.bottomLastDisplayed.terminal_lower_of_time_lower localization
    A coefficientEval u scale timeLower hscale hcoefficient htimeCoordinate
    hfirst (fun a j ↦ hterminalPolynomial (localization.identity.coefficient a j))

/-- A coordinatewise form of `bottomLastCentralLower`.  Polynomial upper
bounds for the coefficient ring and every central coordinate automatically
give the uniform bound for each terminal source polynomial. -/
theorem PaperRankHermiteTopPrefixPreprocessedTraceData.bottomLastCentralLower_of_coordinate_bounds
    {m p : ℕ} [Nonempty (Fin m)] {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {S : Finset (ι × ℕ)}
    {I : Ideal (MvPolynomial
      (PaperRankRetainedSymbols m
        (m * (paperRankHermitePositiveDerivativeCount S + 1)))
      (RealAnalyticGerm p))}
    (trace : data.PaperRankHermiteTopPrefixPreprocessedTraceData S I)
    (A : ℝ → ℝ)
    (coefficientEval :
      data.OrderedClusterPrefixRing
          (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0 →+*
        (ℕ → ℝ))
    (u : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card → ℕ → ℝ)
    (scale : ℕ → ℝ)
    (hscalar : ∀ r n,
      coefficientEval
          (algebraMap ℝ
            (data.OrderedClusterPrefixRing
              (RealAnalyticGerm p) (paperRankHermiteHigherCount S) 0) r) n =
        r)
    (hscale : ∀ᶠ n in atTop, 1 ≤ scale n)
    (hcoefficient : ∀ r,
      HasPolynomialUpperBound atTop scale (coefficientEval r))
    (htimeCoordinate : ∀ i,
      HasPolynomialUpperBound atTop scale (fun n ↦ A (u i n)))
    (htime : Tendsto (fun n ↦ A (u trace.bottomIndex n)) atTop atTop)
    (hfirst : ∀ i : Fin (data.orderedCluster
        ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card,
      HasScalarInversePowerLowerBound atTop scale
        (fun n ↦ finiteRealJetCentralEvaluationHom A coefficientEval u
          (terminalTotalDerivativeCount
            (fun _ : Fin (data.orderedCluster
              ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
                paperRankHermiteHigherCount S)) n
          (MvPolynomial.X
            (Sum.inl
              ⟨i, (0 : Fin (paperRankHermiteHigherCount S + 1))⟩))))
    (hcentralCoordinate : ∀ z,
      HasPolynomialUpperBound atTop scale
        (fun n ↦ realCentralTransferCentralValue A (fun i ↦ u i n)
          (terminalTotalDerivativeCount
            (fun _ : Fin (data.orderedCluster
              ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
                paperRankHermiteHigherCount S)) z)) :
    HasInversePowerLowerBound atTop scale
      (fun j n ↦ finiteRealJetCentralEvaluationHom A coefficientEval u
        (terminalTotalDerivativeCount
          (fun _ : Fin (data.orderedCluster
            ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
              paperRankHermiteHigherCount S)) n
        (trace.bottomLastDisplayed.central.generator j)) := by
  apply trace.bottomLastCentralLower A coefficientEval u scale hscalar hscale
    hcoefficient htimeCoordinate htime hfirst
  intro P
  let d := terminalTotalDerivativeCount
    (fun _ : Fin (data.orderedCluster
      ⟨0, data.orderedClusterCount_pos_of_nonempty⟩).card ↦
        paperRankHermiteHigherCount S)
  have h := mvPolynomial_eval₂Hom_hasPolynomialUpperBound hscale
    coefficientEval
    (fun z n ↦ realCentralTransferCentralValue A (fun i ↦ u i n) d z)
    hcoefficient hcentralCoordinate P
  apply h.congr
  intro n
  exact (mvPolynomial_eval₂Hom_pi_apply coefficientEval
    (fun z n ↦ realCentralTransferCentralValue A (fun i ↦ u i n) d z)
    P n).symm

end RepresentativeClusterSubsequence
end AbelFormalization
