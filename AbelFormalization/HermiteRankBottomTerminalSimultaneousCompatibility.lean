import AbelFormalization.HermiteRankBottomTerminalQuantitativeLower
import AbelFormalization.HermiteRankPreprocessedSimultaneousQuantitativeBounds

/-!
# Canonical compatibility at the bottom simultaneous boundary

The terminal-localization adapter and the canonical simultaneous segment
choose analytic representatives independently.  Their last central
polynomials are nevertheless the same after two harmless changes of
presentation: the empty ordered-prefix coefficient ring is collapsed to the
analytic-germ ring, and the terminal central variables are included into the
central summand of the flattened simultaneous ring.

This module proves that the two representative families agree on a common
neighborhood and then evaluates that equality along the common quantitative
tail.  It therefore discharges
`BottomTerminalSimultaneousQuantitativeCompatibility` without constructing a
moving-point homomorphism on the whole ring of analytic germs.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped Topology

universe u v w

/-! ## Flattening over an empty coefficient-variable type -/

/-- Flattening commutes with renaming the outer variables and with any
coefficient-ring collapse split by the constant-polynomial inclusion. -/
theorem nestedMvPolynomialFlattening_rename_map_of_C_comp
    (R : Type u) [CommRing R] (Outer : Type v) (Central : Type w)
    (Coeff : Type*) (embedding : Central → Outer)
    (collapse : MvPolynomial Coeff R →+* R)
    (hcollapse :
      (MvPolynomial.C : R →+* MvPolynomial Coeff R).comp collapse =
        RingHom.id (MvPolynomial Coeff R))
    (P : MvPolynomial Central (MvPolynomial Coeff R)) :
    nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff
        (MvPolynomial.rename embedding P) =
      MvPolynomial.rename (fun z : Central ↦ Sum.inl (embedding z))
        (MvPolynomial.map collapse P) := by
  have hrecover :
      MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial Coeff R)
          (MvPolynomial.map collapse P) = P := by
    rw [MvPolynomial.map_map, hcollapse, MvPolynomial.map_id]
  calc
    nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff
        (MvPolynomial.rename embedding P) =
        nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff
          (MvPolynomial.rename embedding
            (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial Coeff R)
              (MvPolynomial.map collapse P))) := by rw [hrecover]
    _ = nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff
          (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial Coeff R)
            (MvPolynomial.rename embedding
              (MvPolynomial.map collapse P))) := by
        rw [MvPolynomial.map_rename]
    _ = MvPolynomial.rename Sum.inl
          (MvPolynomial.rename embedding
            (MvPolynomial.map collapse P)) :=
      nestedMvPolynomialFlattening_map_C _
    _ = MvPolynomial.rename (fun z : Central ↦ Sum.inl (embedding z))
          (MvPolynomial.map collapse P) := by
      rw [MvPolynomial.rename_rename]
      rfl

/-- Central-summand specialization of
`nestedMvPolynomialFlattening_rename_map_of_C_comp`. -/
theorem nestedMvPolynomialFlattening_rename_inr_map_of_C_comp
    (R : Type u) [CommRing R] (Free : Type v) (Central : Type w)
    (Coeff : Type*)
    (collapse : MvPolynomial Coeff R →+* R)
    (hcollapse :
      (MvPolynomial.C : R →+* MvPolynomial Coeff R).comp collapse =
        RingHom.id (MvPolynomial Coeff R))
    (P : MvPolynomial Central (MvPolynomial Coeff R)) :
    nestedMvPolynomialFlatteningAlgEquiv R (Free ⊕ Central) Coeff
        (MvPolynomial.rename Sum.inr P) =
      MvPolynomial.rename (fun z : Central ↦ Sum.inl (Sum.inr z))
        (MvPolynomial.map collapse P) :=
  nestedMvPolynomialFlattening_rename_map_of_C_comp R (Free ⊕ Central)
    Central Coeff Sum.inr collapse hcollapse P

/-- If the coefficient-variable type is empty, the canonical collapse meets
the splitting hypothesis of
`nestedMvPolynomialFlattening_rename_inr_map_of_C_comp`. -/
theorem nestedMvPolynomialFlattening_rename_inr_map_isEmpty
    (R : Type u) [CommRing R] (Free : Type v) (Central : Type w)
    (Coeff : Type*) [IsEmpty Coeff]
    (P : MvPolynomial Central (MvPolynomial Coeff R)) :
    nestedMvPolynomialFlatteningAlgEquiv R (Free ⊕ Central) Coeff
        (MvPolynomial.rename Sum.inr P) =
      MvPolynomial.rename (fun z : Central ↦ Sum.inl (Sum.inr z))
        (MvPolynomial.map
          (MvPolynomial.isEmptyAlgEquiv R Coeff).toRingHom P) := by
  let e := MvPolynomial.isEmptyAlgEquiv R Coeff
  apply nestedMvPolynomialFlattening_rename_inr_map_of_C_comp R Free Central
    Coeff e.toRingHom
  apply RingHom.ext
  intro Q
  change MvPolynomial.C (e Q) = Q
  have hC : e.symm.toRingHom =
      (MvPolynomial.C : R →+* MvPolynomial Coeff R) := by
    simpa only [e] using
      (MvPolynomial.isEmptyAlgEquiv_symm_toRingHom R)
  rw [← hC]
  exact e.symm_apply_apply Q

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

/-- Include a bottom terminal symbol into the central part of the outer
simultaneous variables and then into the left part of the flattened nested
ring. -/
def bottomTerminalSimultaneousVariableEmbedding
    (z : TerminalMultiblockSourceIndex
      (data.orderedCluster (bottomTerminalCluster x data)).card
      (boundary.bottomTerminalHigher D representative offset radius Fsys x w₀
        hw₀ data)
      (Fin (data.orderedCluster (bottomTerminalCluster x data)).card)) :
    boundary.SimultaneousAnalyticActiveSymbol D representative offset radius
        Fsys x w₀ hw₀ data (bottomTerminalCluster x data) ⊕
      boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
        Fsys x w₀ hw₀ data (bottomTerminalCluster x data) :=
  Sum.inl (Sum.inr z)

/-- Flattening the last displayed central generator at cluster zero gives
the mapped terminal generator used by analytic localization, with its symbols
included by `bottomTerminalSimultaneousVariableEmbedding`. -/
theorem bottomTerminalSimultaneousFlattenedGenerator_eq
    (b : Fin (boundary.preprocessed.bottomLastDisplayed.central.count + 1)) :
    nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
        (boundary.SimultaneousAnalyticActiveSymbol D representative offset
          radius Fsys x w₀ hw₀ data (bottomTerminalCluster x data))
        (boundary.SimultaneousAnalyticPrefixSymbol D representative offset
          radius Fsys x w₀ hw₀ data (bottomTerminalCluster x data))
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
            (paperRankHermiteHigherCount boundary.S) 0)
          boundary.preprocessed.bottomLastDisplayed b) =
      MvPolynomial.rename
        (boundary.bottomTerminalSimultaneousVariableEmbedding D representative
          offset radius Fsys x w₀ hw₀ data)
        (boundary.preprocessed.bottomTerminalGeneratorOverGerms b) := by
  let Prefix := boundary.SimultaneousAnalyticPrefixSymbol D representative
    offset radius Fsys x w₀ hw₀ data (bottomTerminalCluster x data)
  let Central := TerminalMultiblockSourceIndex
    (data.orderedCluster (bottomTerminalCluster x data)).card
    (boundary.bottomTerminalHigher D representative offset radius Fsys x w₀
      hw₀ data)
    (Fin (data.orderedCluster (bottomTerminalCluster x data)).card)
  let e₀ := data.orderedClusterPrefixRingZeroAlgEquiv
    (RealAnalyticGerm p) (paperRankHermiteHigherCount boundary.S)
  let eR : data.OrderedClusterPrefixRing (RealAnalyticGerm p)
      (paperRankHermiteHigherCount boundary.S) 0 ≃ₐ[ℝ]
        RealAnalyticGerm p := e₀.restrictScalars ℝ
  have hcollapse :
      (MvPolynomial.C : RealAnalyticGerm p →+*
          data.OrderedClusterPrefixRing (RealAnalyticGerm p)
            (paperRankHermiteHigherCount boundary.S) 0).comp eR.toRingHom =
        RingHom.id (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
          (paperRankHermiteHigherCount boundary.S) 0) := by
    apply RingHom.ext
    intro Q
    change MvPolynomial.C (e₀ Q) = Q
    have hC : e₀.symm.toRingHom =
        (MvPolynomial.C : RealAnalyticGerm p →+*
          data.OrderedClusterPrefixRing (RealAnalyticGerm p)
            (paperRankHermiteHigherCount boundary.S) 0) := by
      simpa only [e₀,
        RepresentativeClusterSubsequence.orderedClusterPrefixRingZeroAlgEquiv]
        using (MvPolynomial.isEmptyAlgEquiv_symm_toRingHom
          (RealAnalyticGerm p))
    rw [← hC]
    exact e₀.symm_apply_apply Q
  have hflatten := nestedMvPolynomialFlattening_rename_map_of_C_comp
    (RealAnalyticGerm p)
    (boundary.SimultaneousAnalyticActiveSymbol D representative offset radius
      Fsys x w₀ hw₀ data (bottomTerminalCluster x data)) Central Prefix
    (Sum.inr : Central →
      boundary.SimultaneousAnalyticActiveSymbol D representative offset radius
        Fsys x w₀ hw₀ data (bottomTerminalCluster x data))
    eR.toRingHom hcollapse
    (boundary.preprocessed.bottomLastDisplayed.central.generator b)
  have hembedding :
      (fun z : Central ↦
        (Sum.inl (Sum.inr z) :
          boundary.SimultaneousAnalyticActiveSymbol D representative offset
              radius Fsys x w₀ hw₀ data (bottomTerminalCluster x data) ⊕
            boundary.SimultaneousAnalyticPrefixSymbol D representative offset
              radius Fsys x w₀ hw₀ data (bottomTerminalCluster x data))) =
        boundary.bottomTerminalSimultaneousVariableEmbedding D representative
          offset radius Fsys x w₀ hw₀ data := by
    funext z
    rfl
  rw [hembedding] at hflatten
  simpa only [
    ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator,
    RepresentativeClusterSubsequence.PaperRankHermiteTopPrefixPreprocessedTraceData.bottomTerminalGeneratorOverGerms,
    RepresentativeClusterSubsequence.orderedClusterPrefixRingZeroAlgEquiv,
    bottomTerminalSimultaneousVariableEmbedding, Prefix, Central, eR,
    e₀] using
      hflatten

/-- The flattened simultaneous target at the last operation of cluster zero
is the embedded mapped terminal generator. -/
theorem bottomTerminalSimultaneousTerminalTarget_eq_embeddedGenerator
    (b : Fin (boundary.preprocessed.bottomLastDisplayed.central.count + 1)) :
    nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
        (boundary.SimultaneousAnalyticActiveSymbol D representative offset
          radius Fsys x w₀ hw₀ data (bottomTerminalCluster x data))
        (boundary.SimultaneousAnalyticPrefixSymbol D representative offset
          radius Fsys x w₀ hw₀ data (bottomTerminalCluster x data))
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
            (paperRankHermiteHigherCount boundary.S) 0)
          ((boundary.simultaneousNumericTrace D representative offset radius
            Fsys x w₀ hw₀ data
              (bottomTerminalCluster x data)).simultaneousDisplayed
            (boundary.bottomSimultaneousTerminalIndex D representative offset
              radius Fsys x w₀ hw₀ data)) b) =
      MvPolynomial.rename
        (boundary.bottomTerminalSimultaneousVariableEmbedding D representative
          offset radius Fsys x w₀ hw₀ data)
        (boundary.preprocessed.bottomTerminalGeneratorOverGerms b) := by
  change nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
        (boundary.SimultaneousAnalyticActiveSymbol D representative offset
          radius Fsys x w₀ hw₀ data (bottomTerminalCluster x data))
        (boundary.SimultaneousAnalyticPrefixSymbol D representative offset
          radius Fsys x w₀ hw₀ data (bottomTerminalCluster x data))
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
            (paperRankHermiteHigherCount boundary.S) 0)
          boundary.preprocessed.bottomLastDisplayed b) = _
  exact boundary.bottomTerminalSimultaneousFlattenedGenerator_eq D
    representative offset radius Fsys x w₀ hw₀ data b

/-- A terminal-localization source representative, renamed into the flattened
simultaneous variable presentation. -/
def bottomTerminalSourceRepresentativeInSimultaneousVariables
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData)
    (b : Fin (boundary.preprocessed.bottomLastDisplayed.central.count + 1))
    (y : RestrictedBoxSpace p) :=
  MvPolynomial.rename
    (boundary.bottomTerminalSimultaneousVariableEmbedding D representative
      offset radius Fsys x w₀ hw₀ data)
    ((boundary.preprocessed.bottomTerminalAnalyticChangeData localization).sourceRepresentative
      b y)

/-- The renamed terminal source representative represents the embedded
terminal generator as a polynomial-valued germ. -/
theorem bottomTerminalSourceRepresentativeInSimultaneousVariables_germ_eq
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData)
    (b : Fin (boundary.preprocessed.bottomLastDisplayed.central.count + 1)) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (MvPolynomial.rename
          (boundary.bottomTerminalSimultaneousVariableEmbedding D
            representative offset radius Fsys x w₀ hw₀ data)
          (boundary.preprocessed.bottomTerminalGeneratorOverGerms b)) =
      (boundary.bottomTerminalSourceRepresentativeInSimultaneousVariables D
        representative offset radius Fsys x w₀ hw₀ data localization b :
          Germ (𝓝 (0 : RestrictedBoxSpace p))
            (MvPolynomial
              (boundary.SimultaneousAnalyticActiveSymbol D representative
                  offset radius Fsys x w₀ hw₀ data
                    (bottomTerminalCluster x data) ⊕
                boundary.SimultaneousAnalyticPrefixSymbol D representative
                  offset radius Fsys x w₀ hw₀ data
                    (bottomTerminalCluster x data)) ℝ)) := by
  exact analyticPolynomialGermHom_rename_of (0 : RestrictedBoxSpace p)
    (boundary.bottomTerminalSimultaneousVariableEmbedding D representative
      offset radius Fsys x w₀ hw₀ data)
    ((boundary.preprocessed.bottomTerminalAnalyticChangeData localization).source_germ_eq b)

/-- The independently selected terminal and simultaneous representatives of
the last central family agree on one neighborhood of the analytic basepoint. -/
theorem eventually_bottomTerminalSourceRepresentative_eq_simultaneousTerminal
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData) :
    ∀ᶠ y in 𝓝 (0 : RestrictedBoxSpace p), ∀ b,
      boundary.bottomTerminalSourceRepresentativeInSimultaneousVariables D
          representative offset radius Fsys x w₀ hw₀ data localization b y =
        (boundary.simultaneousQuantitativeCentralAnalyticChange D representative
          offset radius Fsys x w₀ hw₀ data (bottomTerminalCluster x data)
          (boundary.bottomSimultaneousTerminalIndex D representative offset
            radius Fsys x w₀ hw₀ data)).targetRepresentative b y := by
  apply Filter.eventually_all.mpr
  intro b
  apply analyticPolynomialRepresentatives_eventually_eq
    (0 : RestrictedBoxSpace p)
    (boundary.bottomTerminalSourceRepresentativeInSimultaneousVariables_germ_eq
      D representative offset radius Fsys x w₀ hw₀ data localization b)
    ((boundary.simultaneousQuantitativeCentralAnalyticChange D representative
      offset radius Fsys x w₀ hw₀ data (bottomTerminalCluster x data)
      (boundary.bottomSimultaneousTerminalIndex D representative offset radius
        Fsys x w₀ hw₀ data)).target_germ_eq b)
  exact (boundary.bottomTerminalSimultaneousTerminalTarget_eq_embeddedGenerator
    D representative offset radius Fsys x w₀ hw₀ data b).symm

/-! ## Evaluation on the common quantitative tail -/

/-- The bottom terminal analytic parameter is the simultaneous analytic
parameter after choosing the common quantitative reindexing. -/
theorem bottomTerminalParameter_simultaneousQuantitativeReindex_eq
    (hA : IsAbel A) :
    boundary.bottomTerminalParameter D representative offset radius Fsys x w₀
        hw₀ data
        (boundary.simultaneousQuantitativeReindex D representative offset
          radius Fsys x w₀ hw₀ data hA) =
      boundary.simultaneousQuantitativeAnalyticParameter D representative offset
        radius Fsys x w₀ hw₀ data hA := by
  rfl

/-- On embedded terminal symbols, the exact assignment after the last
simultaneous operation is the literal bottom terminal assignment. -/
theorem bottomTerminalSymbolValue_eq_simultaneousTerminalAfter
    (hA : IsAbel A)
    (z : TerminalMultiblockSourceIndex
      (data.orderedCluster (bottomTerminalCluster x data)).card
      (boundary.bottomTerminalHigher D representative offset radius Fsys x w₀
        hw₀ data)
      (Fin (data.orderedCluster (bottomTerminalCluster x data)).card))
    (n : ℕ) :
    boundary.bottomTerminalSymbolValue D representative offset radius Fsys x w₀
        hw₀ data
        (boundary.simultaneousQuantitativeReindex D representative offset
          radius Fsys x w₀ hw₀ data hA) z n =
      boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D representative
        offset radius Fsys x w₀ hw₀ data hA
        (bottomTerminalCluster x data)
        (boundary.bottomSimultaneousTerminalIndex D representative offset
          radius Fsys x w₀ hw₀ data).val
        (boundary.bottomTerminalSimultaneousVariableEmbedding D representative
          offset radius Fsys x w₀ hw₀ data z) n := by
  change boundary.bottomTerminalSymbolValue D representative offset radius Fsys
      x w₀ hw₀ data
        (boundary.simultaneousQuantitativeReindex D representative offset radius
          Fsys x w₀ hw₀ data hA) z n =
    boundary.simultaneousQuantitativeAnalyticAfterValue D representative offset
      radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data)
      (boundary.bottomSimultaneousTerminalIndex D representative offset radius
        Fsys x w₀ hw₀ data).val (Sum.inr z) n
  rw [boundary.simultaneousQuantitativeAnalyticAfterValue_central D
    representative offset radius Fsys x w₀ hw₀ data hA
    (bottomTerminalCluster x data)
    (boundary.bottomSimultaneousTerminalIndex D representative offset radius
      Fsys x w₀ hw₀ data).val z n]
  rfl

/-- Evaluating the two representative families on the common tail gives the
canonical quantitative compatibility at the bottom boundary. -/
theorem bottomTerminalSimultaneousQuantitativeCompatibility
    (hA : IsAbel A)
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData) :
    boundary.BottomTerminalSimultaneousQuantitativeCompatibility D
      representative offset radius Fsys x w₀ hw₀ data hA localization
      (boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
        representative offset radius Fsys x w₀ hw₀ data hA
        (bottomTerminalCluster x data)) := by
  have hrepresentatives :=
    (boundary.simultaneousQuantitativeAnalyticParameter_tendsto D representative
      offset radius Fsys x w₀ hw₀ data hA).eventually
      (boundary.eventually_bottomTerminalSourceRepresentative_eq_simultaneousTerminal
        D representative offset radius Fsys x w₀ hw₀ data localization)
  filter_upwards [hrepresentatives] with n hn
  intro b
  change MvPolynomial.eval
      (fun z ↦ boundary.bottomTerminalSymbolValue D representative offset
        radius Fsys x w₀ hw₀ data
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA) z n)
      ((boundary.preprocessed.bottomTerminalAnalyticChangeData localization).sourceRepresentative
        b (boundary.bottomTerminalParameter D representative offset radius Fsys
          x w₀ hw₀ data
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA) n)) = _
  rw [boundary.bottomTerminalParameter_simultaneousQuantitativeReindex_eq D
    representative offset radius Fsys x w₀ hw₀ data hA]
  change _ = MvPolynomial.eval
      (fun z ↦ boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D
        representative offset radius Fsys x w₀ hw₀ data hA
        (bottomTerminalCluster x data)
        (boundary.bottomSimultaneousTerminalIndex D representative offset radius
          Fsys x w₀ hw₀ data).val z n)
      ((boundary.simultaneousQuantitativeCentralAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data (bottomTerminalCluster x data)
        (boundary.bottomSimultaneousTerminalIndex D representative offset radius
          Fsys x w₀ hw₀ data)).targetRepresentative b
        (boundary.simultaneousQuantitativeAnalyticParameter D representative
          offset radius Fsys x w₀ hw₀ data hA n))
  rw [← hn b]
  unfold bottomTerminalSourceRepresentativeInSimultaneousVariables
  rw [MvPolynomial.eval_rename]
  have hassignment :
      (fun z ↦ boundary.bottomTerminalSymbolValue D representative offset
        radius Fsys x w₀ hw₀ data
          (boundary.simultaneousQuantitativeReindex D representative offset
            radius Fsys x w₀ hw₀ data hA) z n) =
        ((fun z ↦
          boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D
            representative offset radius Fsys x w₀ hw₀ data hA
            (bottomTerminalCluster x data)
            (boundary.bottomSimultaneousTerminalIndex D representative offset
              radius Fsys x w₀ hw₀ data).val z n) ∘
          boundary.bottomTerminalSimultaneousVariableEmbedding D representative
            offset radius Fsys x w₀ hw₀ data) := by
    funext z
    exact boundary.bottomTerminalSymbolValue_eq_simultaneousTerminalAfter D
      representative offset radius Fsys x w₀ hw₀ data hA z n
  rw [hassignment]

/-- The canonical analytic segment receives the localized terminal lower
bound with no representative compatibility premise. -/
theorem bottomSimultaneousQuantitativeTerminalAfterValue_lower_auto
    (hA : IsAbel A)
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData) :
    HasInversePowerLowerBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data)
        ((boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data
          (bottomTerminalCluster x data)).certificate.terminalized.extraSteps +
            1))
      (boundary.bottomSimultaneousQuantitativeTerminalAfterValue D
        representative offset radius Fsys x w₀ hw₀ data hA
        (boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
          representative offset radius Fsys x w₀ hw₀ data hA
          (bottomTerminalCluster x data))) := by
  exact boundary.bottomSimultaneousQuantitativeTerminalAfterValue_lower D
    representative offset radius Fsys x w₀ hw₀ data hA localization
    (boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D representative
      offset radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data))
    (boundary.bottomTerminalSimultaneousQuantitativeCompatibility D
      representative offset radius Fsys x w₀ hw₀ data hA localization)

/-- Compatibility-free propagation of the canonical bottom lower bound
through the whole simultaneous segment of ordered cluster zero. -/
theorem bottomSimultaneousQuantitativeFirstBeforeValue_lower_auto
    (separation : boundary.IndividualSeparationData D representative offset
      radius Fsys x w₀ hw₀ data)
    (hA : IsAbel A)
    (hN : (((boundary.bottomTerminalExtraSteps D representative offset radius
      Fsys x w₀ hw₀ data + 6 : ℕ) : ℝ)) ≤
        separation.N (bottomTerminalCluster x data))
    (localization :
      boundary.preprocessed.bottomLastDisplayed.TerminalLocalizationData) :
    HasInversePowerLowerBound atTop
      (boundary.simultaneousQuantitativeBoundaryScale D representative offset
        radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data) 0)
      (((boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
          representative offset radius Fsys x w₀ hw₀ data hA
          (bottomTerminalCluster x data)).change
        (boundary.simultaneousNumericStage D representative offset radius Fsys x
          w₀ hw₀ data
          (bottomTerminalCluster x data)).certificate.firstCentralStepIndex).beforeValue) := by
  exact boundary.bottomSimultaneousQuantitativeFirstBeforeValue_lower D
    representative offset radius Fsys x w₀ hw₀ data separation hA hN
    localization
    (boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D representative
      offset radius Fsys x w₀ hw₀ data hA (bottomTerminalCluster x data))
    (boundary.bottomTerminalSimultaneousQuantitativeCompatibility D
      representative offset radius Fsys x w₀ hw₀ data hA localization)

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
