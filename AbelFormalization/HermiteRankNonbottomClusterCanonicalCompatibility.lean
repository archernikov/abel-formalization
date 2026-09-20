import AbelFormalization.HermiteRankNonbottomClusterBackwardBridge
import AbelFormalization.HermiteRankTopIndividualBoundaryCompatibility
import AbelFormalization.FiniteAnalyticNestedCoefficientwiseEvaluation
import AbelFormalization.HermiteRankPreprocessedSimultaneousQuantitativeBounds

/-!
# Canonical finite analytic compatibility across non-bottom Hermite clusters

The incoming individual boundary of cluster `c` and the terminal simultaneous
boundary of cluster `c + 1` present the same coefficient ideal.  The two
finite analytic constructions choose their polynomial representatives
independently.  This file compares those representatives as germs and then
evaluates the resulting eventual polynomial identities on the common
quantitative tail.

The coefficient-to-time comparison uses the boundary-zero self adapter.  The
localization-cleared comparison keeps the smaller-prefix coefficient variables
explicit while flattening the nested polynomial rings.  The final comparison
renames the localized terminal source representatives into the flattened
variables of the last simultaneous central adapter.  No moving-point ring
homomorphism on all real-analytic germs is used.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter Set
open scoped BigOperators Topology

universe u v w

/-! ## Naturality of nested polynomial flattening -/

/-- Flattening commutes with a renaming of the outer variables.  Coefficient
variables are preserved in the right summand. -/
theorem nestedMvPolynomialFlattening_rename_outer
    (R : Type u) [CommRing R]
    {Outer₁ : Type v} {Outer₂ : Type w} (Coeff : Type*)
    (f : Outer₁ → Outer₂)
    (P : MvPolynomial Outer₁ (MvPolynomial Coeff R)) :
    nestedMvPolynomialFlatteningAlgEquiv R Outer₂ Coeff
        (MvPolynomial.rename f P) =
      MvPolynomial.rename
        (Sum.elim (fun i : Outer₁ ↦ Sum.inl (f i))
          (Sum.inr : Coeff → Outer₂ ⊕ Coeff))
        (nestedMvPolynomialFlatteningAlgEquiv R Outer₁ Coeff P) := by
  let lhs : MvPolynomial Outer₁ (MvPolynomial Coeff R) →+*
      MvPolynomial (Outer₂ ⊕ Coeff) R :=
    (nestedMvPolynomialFlatteningAlgEquiv R Outer₂ Coeff).toRingHom.comp
      (MvPolynomial.rename f).toRingHom
  let embedding : Outer₁ ⊕ Coeff → Outer₂ ⊕ Coeff :=
    Sum.elim (fun i ↦ Sum.inl (f i)) Sum.inr
  let rhs : MvPolynomial Outer₁ (MvPolynomial Coeff R) →+*
      MvPolynomial (Outer₂ ⊕ Coeff) R :=
    (MvPolynomial.rename embedding).toRingHom.comp
      (nestedMvPolynomialFlatteningAlgEquiv R Outer₁ Coeff).toRingHom
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro Q
      change nestedMvPolynomialFlatteningAlgEquiv R Outer₂ Coeff
          (MvPolynomial.rename f (MvPolynomial.C Q)) =
        MvPolynomial.rename embedding
          (nestedMvPolynomialFlatteningAlgEquiv R Outer₁ Coeff
            (MvPolynomial.C Q))
      rw [MvPolynomial.rename_C, nestedMvPolynomialFlattening_C,
        nestedMvPolynomialFlattening_C, MvPolynomial.rename_rename]
      rfl
    · intro i
      have h₁ := nestedMvPolynomialFlattening_map_C
        (R := R) (Outer := Outer₁) (Coeff := Coeff) (MvPolynomial.X i)
      have h₂ := nestedMvPolynomialFlattening_map_C
        (R := R) (Outer := Outer₂) (Coeff := Coeff) (MvPolynomial.X (f i))
      simp only [MvPolynomial.map_X] at h₁ h₂
      change nestedMvPolynomialFlatteningAlgEquiv R Outer₂ Coeff
          (MvPolynomial.rename f (MvPolynomial.X i)) =
        MvPolynomial.rename embedding
          (nestedMvPolynomialFlatteningAlgEquiv R Outer₁ Coeff
            (MvPolynomial.X i))
      rw [MvPolynomial.rename_X, h₂, h₁, MvPolynomial.rename_X,
        MvPolynomial.rename_X]
      rw [MvPolynomial.rename_X]
      rfl
  exact DFunLike.congr_fun hhom P

/-- Include a flattened time/coefficient variable into the corresponding
terminal-source/coefficient variable type. -/
def terminalFlattenedRetainedEmbedding
    {h : ℕ} {higher : Fin h → ℕ} {Coeff : Type*} :
    (Fin h ⊕ Coeff) →
      (TerminalMultiblockSourceIndex h higher (Fin h) ⊕ Coeff)
  | Sum.inl i => Sum.inl (Sum.inr i)
  | Sum.inr z => Sum.inr z

/-- Flattening a denominator-cleared retained polynomial preserves both the
terminal symbols and the nested coefficient symbols literally. -/
theorem nestedMvPolynomialFlattening_clearedRetained
    (R : Type u) [CommRing R]
    (Coeff : Type v) {h : ℕ} (higher : Fin h → ℕ)
    (exponent : ℕ)
    (P : MvPolynomial (Fin h) (MvPolynomial Coeff R)) :
    nestedMvPolynomialFlatteningAlgEquiv R
        (TerminalMultiblockSourceIndex h higher (Fin h)) Coeff
        (terminalFirstDerivativeProduct (MvPolynomial Coeff R) (Fin h) h
            higher ^ exponent *
          terminalMultiblockRetainedSourceHom (MvPolynomial Coeff R) (Fin h)
            h higher P) =
      MvPolynomial.rename Sum.inl
          (terminalFirstDerivativeProduct R (Fin h) h higher) ^ exponent *
        MvPolynomial.rename
          (terminalFlattenedRetainedEmbedding
            (h := h) (higher := higher) (Coeff := Coeff))
          (nestedMvPolynomialFlatteningAlgEquiv R (Fin h) Coeff P) := by
  have hfirst :
      terminalFirstDerivativeProduct (MvPolynomial Coeff R) (Fin h) h higher =
        MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial Coeff R)
          (terminalFirstDerivativeProduct R (Fin h) h higher) := by
    simp only [terminalFirstDerivativeProduct_eq_prod, map_prod,
      MvPolynomial.map_X]
  rw [map_mul, map_pow, hfirst,
    nestedMvPolynomialFlattening_map_C]
  change _ * nestedMvPolynomialFlatteningAlgEquiv R
      (TerminalMultiblockSourceIndex h higher (Fin h)) Coeff
        (MvPolynomial.rename
          (Sum.inr : Fin h → TerminalMultiblockSourceIndex h higher (Fin h)) P) = _
  rw [nestedMvPolynomialFlattening_rename_outer]
  have hembedding :
      (Sum.elim
          (fun i : Fin h ↦
            Sum.inl (Sum.inr i : TerminalMultiblockSourceIndex h higher (Fin h)))
          (Sum.inr : Coeff →
            TerminalMultiblockSourceIndex h higher (Fin h) ⊕ Coeff)) =
        terminalFlattenedRetainedEmbedding := by
    funext z
    rcases z with i | z <;> rfl
  rw [hembedding]

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

noncomputable local instance nonbottomCanonicalPrefixDecidableEq
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-! ## A canonical localization and the lower boundary-zero adapter -/

/-- Canonical finite terminal-localization data at the last simultaneous
operation of the upper cluster. -/
noncomputable def nextTerminalLocalizationData
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
      hw₀ data c hc).TerminalLocalizationData :=
  Classical.choice
    ((boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
      hw₀ data c hc).nonempty_terminalLocalizationData)

/-- The fixed self change whose source representatives define the incoming
individual boundary-zero values. -/
abbrev nextIncomingBoundarySelfChange
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :=
  (boundary.individualMixedAnalyticBoundaryData D representative offset radius
    Fsys x w₀ hw₀ data hA c).boundarySelfChange 0

/-- The analytic parameter occurring literally in the shifted incoming
individual value. -/
def nextIncomingBoundaryParameter
    (hA : IsAbel A) (n : ℕ) : RestrictedBoxSpace p :=
  boundary.individualNumericAnalyticParameter D representative offset radius
    Fsys x w₀ hw₀ data hA
    (boundary.individualSimultaneousTailShift D representative offset radius
      Fsys x w₀ hw₀ data hA n)

/-- The boundary-zero mixed symbol assignment on the common tail. -/
def nextIncomingBoundarySymbolValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ClusterOperationSymbol
      (data.OrderedClusterPrefixBlock (c.val + 1))
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)) → ℕ → ℝ :=
  fun z n ↦ boundary.individualMixedBoundarySymbolValue D representative offset
    radius Fsys x w₀ hw₀ data hA c 0 z
      (boundary.individualSimultaneousTailShift D representative offset radius
        Fsys x w₀ hw₀ data hA n)

/-- The two fixed quantitative tails commute, so the incoming and upper
terminal adapters use the same selected box parameter. -/
@[simp]
theorem nextIncomingBoundaryParameter_eq_nextTerminalParameter
    (hA : IsAbel A) (n : ℕ) :
    boundary.nextIncomingBoundaryParameter D representative offset radius Fsys
        x w₀ hw₀ data hA n =
      boundary.nextTerminalParameter D representative offset radius Fsys x w₀
        hw₀ data hA n := by
  unfold nextIncomingBoundaryParameter individualNumericAnalyticParameter
    individualSimultaneousTailShift nextTerminalParameter
    simultaneousQuantitativeReindex
  congr 2
  omega

/-- The selected full paper parameter indices in the two descriptions are
equal. -/
@[simp]
theorem topIndividualCommonSelectedIndex_eq_simultaneousQuantitativeReindex
    (hA : IsAbel A) (n : ℕ) :
    boundary.topIndividualCommonSelectedIndex D representative offset radius
        Fsys x w₀ hw₀ data hA n =
      boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n := by
  unfold topIndividualCommonSelectedIndex individualSimultaneousTailShift
    simultaneousQuantitativeReindex
  omega

/-- The smaller prefix of a simultaneous cluster is the ordinary paper
Hermite prefix at the selected translated parameter. -/
theorem simultaneousSmallerPrefixSequenceValue_eq_selectedTranslated
    (c : Fin data.orderedClusterCount) (r n : ℕ) :
    (fun z ↦ boundary.simultaneousSmallerPrefixSequenceValue D representative
      offset radius Fsys x w₀ hw₀ data c r z n) =
      RepresentativeClusterSubsequence.paperRankHermitePrefixValue data
        (D.translateToZero w₀) representative
        (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
        boundary.Fbranch
        (boundary.selectedTranslatedParameter D representative offset radius
          Fsys x w₀ hw₀ data n) c.val := by
  funext z
  simp only [simultaneousSmallerPrefixSequenceValue,
    RepresentativeClusterSubsequence.paperRankHermiteOrderedClusterSmallerPrefixSequenceValue]
  rcases z with b | z
  · have hnot := orderedClusterPrefixBlock_not_mem_active
      (x := x) (data := data) c b
    simp only [RepresentativeClusterSubsequence.paperRankHermitePrefixValue_free,
      simultaneousPreLogParameter, hnot, dite_false]
  · rcases z with br | b
    · rcases br with ⟨b, q⟩
      have hnot := orderedClusterPrefixBlock_not_mem_active
        (x := x) (data := data) c b
      have he : (paperRankAllCoefficientBlockEquiv m).symm (Sum.inr b.1) =
          b.1 := by
        apply (paperRankAllCoefficientBlockEquiv m).injective
        simp
      simp only [
        RepresentativeClusterSubsequence.paperRankHermitePrefixValue_positiveDerivative,
        paperRankHermiteCoefficientValue, he, simultaneousPreLogParameter,
        hnot, dite_false]
    · have hnot := orderedClusterPrefixBlock_not_mem_active
        (x := x) (data := data) c b
      have he : (paperRankAllCoefficientBlockEquiv m).symm (Sum.inr b.1) =
          b.1 := by
        apply (paperRankAllCoefficientBlockEquiv m).injective
        simp
      simp only [RepresentativeClusterSubsequence.paperRankHermitePrefixValue_time,
        paperRankHermiteCoefficientValue, he, simultaneousPreLogParameter,
        hnot, dite_false]

/-- The lower mixed boundary-zero assignment and the upper terminal
coefficient assignment agree eventually on every prefix symbol. -/
theorem nextIncomingBoundarySymbolValue_eventuallyEq_nextTerminalCoefficientValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    ∀ᶠ n in atTop, ∀ z,
      boundary.nextIncomingBoundarySymbolValue D representative offset radius
          Fsys x w₀ hw₀ data hA c z n =
        boundary.nextTerminalCoefficientValue D representative offset radius
          Fsys x w₀ hw₀ data hA c hc z n := by
  let shift := boundary.individualSimultaneousTailShift D representative offset
    radius Fsys x w₀ hw₀ data hA
  have hshift : Tendsto shift atTop atTop :=
    boundary.topIndividualSimultaneousTailShift_tendsto_atTop D representative
      offset radius Fsys x w₀ hw₀ data hA
  have hmixed := hshift.eventually
    (boundary.individualMixedBoundarySymbolValue_zero_eventuallyEq_hermite D
      representative offset radius Fsys x w₀ hw₀ data hA c)
  have hparameter :=
    boundary.individualHermiteBoundaryParameter_zero_on_commonTail_eventuallyEq
      D representative offset radius Fsys x w₀ hw₀ data hA c
  filter_upwards [hmixed, hparameter] with n hmix hparam
  intro z
  change boundary.individualMixedBoundarySymbolValue D representative offset
      radius Fsys x w₀ hw₀ data hA c 0 z (shift n) = _
  rw [hmix z]
  change RepresentativeClusterSubsequence.paperRankHermitePrefixValue data
      (D.translateToZero w₀) representative
      (restrictedOffsetTranslateToZero w₀ offset) boundary.S boundary.B
      boundary.Fbranch
      (boundary.individualHermiteBoundaryParameter D representative offset
        radius Fsys x w₀ hw₀ data hA c 0 (shift n)) (c.val + 1) z = _
  rw [hparam,
    boundary.topIndividualCommonSelectedIndex_eq_simultaneousQuantitativeReindex
      D representative offset radius Fsys x w₀ hw₀ data hA n]
  symm
  exact congrFun
    (boundary.simultaneousSmallerPrefixSequenceValue_eq_selectedTranslated D
      representative offset radius Fsys x w₀ hw₀ data
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
        hw₀ data c hc)
      (boundary.nextTerminalExtraSteps D representative offset radius Fsys x
        w₀ hw₀ data c hc)
      (boundary.simultaneousQuantitativeReindex D representative offset radius
        Fsys x w₀ hw₀ data hA n)) z

/-- Unfolding the canonical individual boundary data exposes the self-change
source value used at boundary zero. -/
theorem individualMixedBoundaryValueOnSimultaneousTail_zero_eq_selfValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (b : Fin ((boundary.individualNumericBoundaryFamily D representative offset
      radius Fsys x w₀ hw₀ data c 0).count + 1)) (n : ℕ) :
    boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0 b n =
      (boundary.nextIncomingBoundarySelfChange D representative offset radius
        Fsys x w₀ hw₀ data hA c).sourceValue
        (boundary.nextIncomingBoundaryParameter D representative offset radius
          Fsys x w₀ hw₀ data hA)
        (boundary.nextIncomingBoundarySymbolValue D representative offset radius
          Fsys x w₀ hw₀ data hA c) b n := by
  rfl

/-! ## The coefficient-to-time target representatives -/

/-- Rename the lower boundary-zero self representative into the flattened
time/coefficient variables of the upper terminal adapter. -/
def nextCoefficientTimeTargetRepresentative
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (b : Fin ((boundary.nextCoefficientFamilyFromIndividualBoundaryZero D
      representative offset radius Fsys x w₀ hw₀ data c hc).count + 1))
    (y : RestrictedBoxSpace p) :=
  MvPolynomial.rename
    (Sum.inr :
      boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
          Fsys x w₀ hw₀ data
            (boundary.nextOrderedCluster D representative offset radius Fsys x
              w₀ hw₀ data c hc) →
        Fin (data.orderedCluster
          (boundary.nextOrderedCluster D representative offset radius Fsys x
            w₀ hw₀ data c hc)).card ⊕
          boundary.SimultaneousAnalyticPrefixSymbol D representative offset
            radius Fsys x w₀ hw₀ data
              (boundary.nextOrderedCluster D representative offset radius Fsys x
                w₀ hw₀ data c hc))
    ((boundary.nextIncomingBoundarySelfChange D representative offset radius
      Fsys x w₀ hw₀ data hA c).sourceRepresentative b y)

/-- The explicit renamed boundary representative represents the flattened
constant coefficient-to-time target. -/
theorem nextCoefficientTimeTargetRepresentative_germ_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (b : Fin ((boundary.nextCoefficientFamilyFromIndividualBoundaryZero D
      representative offset radius Fsys x w₀ hw₀ data c hc).count + 1)) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
          (Fin (data.orderedCluster
            (boundary.nextOrderedCluster D representative offset radius Fsys x
              w₀ hw₀ data c hc)).card)
          (boundary.SimultaneousAnalyticPrefixSymbol D representative offset
            radius Fsys x w₀ hw₀ data
              (boundary.nextOrderedCluster D representative offset radius Fsys
                x w₀ hw₀ data c hc))
          (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.coefficientIdealTimeTarget
            (boundary.nextCoefficientFamilyFromIndividualBoundaryZero D
              representative offset radius Fsys x w₀ hw₀ data c hc) b)) =
      (boundary.nextCoefficientTimeTargetRepresentative D representative offset
        radius Fsys x w₀ hw₀ data hA c hc b :
          Germ (𝓝 (0 : RestrictedBoxSpace p))
            (MvPolynomial
              (Fin (data.orderedCluster
                  (boundary.nextOrderedCluster D representative offset radius
                    Fsys x w₀ hw₀ data c hc)).card ⊕
                boundary.SimultaneousAnalyticPrefixSymbol D representative
                  offset radius Fsys x w₀ hw₀ data
                    (boundary.nextOrderedCluster D representative offset radius
                      Fsys x w₀ hw₀ data c hc)) ℝ)) := by
  rw [ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.coefficientIdealTimeTarget,
    nestedMvPolynomialFlattening_C]
  exact analyticPolynomialGermHom_rename_of (0 : RestrictedBoxSpace p) Sum.inr
    ((boundary.nextIncomingBoundarySelfChange D representative offset radius
      Fsys x w₀ hw₀ data hA c).source_germ_eq b)

/-- The independently chosen coefficient-to-time target representatives agree
eventually with the renamed incoming self representatives. -/
theorem eventually_nextCoefficientTimeTargetRepresentative_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData) :
    ∀ᶠ y in 𝓝 (0 : RestrictedBoxSpace p), ∀ b,
      (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.coefficientIdealTimeAnalyticChange
        (boundary.nextTerminalDisplayed D representative offset radius Fsys x
          w₀ hw₀ data c hc) localization
        (boundary.nextCoefficientFamilyFromIndividualBoundaryZero D
          representative offset radius Fsys x w₀ hw₀ data c hc)).targetRepresentative
          b y =
        boundary.nextCoefficientTimeTargetRepresentative D representative offset
          radius Fsys x w₀ hw₀ data hA c hc b y := by
  apply Filter.eventually_all.mpr
  intro b
  apply analyticPolynomialRepresentatives_eventually_eq
    (0 : RestrictedBoxSpace p)
    ((ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.coefficientIdealTimeAnalyticChange
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc) localization
      (boundary.nextCoefficientFamilyFromIndividualBoundaryZero D representative
        offset radius Fsys x w₀ hw₀ data c hc)).target_germ_eq b)
    (boundary.nextCoefficientTimeTargetRepresentative_germ_eq D representative
      offset radius Fsys x w₀ hw₀ data hA c hc b)
    rfl

/-- The incoming lower boundary values are the target values of the upper
coefficient-to-time change. -/
theorem nextCoefficientTimeTargetValue_eventually_eq_incoming
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData) :
    ∀ᶠ n in atTop, ∀ b : Fin
      ((boundary.nextCoefficientFamilyFromIndividualBoundaryZero D
        representative offset radius Fsys x w₀ hw₀ data c hc).count + 1),
      boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
          offset radius Fsys x w₀ hw₀ data hA c 0 b n =
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.coefficientIdealTimeAnalyticChange
          (boundary.nextTerminalDisplayed D representative offset radius Fsys x
            w₀ hw₀ data c hc) localization
          (boundary.nextCoefficientFamilyFromIndividualBoundaryZero D
            representative offset radius Fsys x w₀ hw₀ data c hc)).targetValue
          (boundary.nextTerminalParameter D representative offset radius Fsys x
            w₀ hw₀ data hA)
          (boundary.nextTerminalTimeValue D representative offset radius Fsys x
            w₀ hw₀ data hA c hc)
          (boundary.nextTerminalCoefficientValue D representative offset radius
            Fsys x w₀ hw₀ data hA c hc) b n := by
  have hrepresentative :=
    (boundary.nextTerminalParameter_tendsto D representative offset radius Fsys
      x w₀ hw₀ data hA).eventually
      (boundary.eventually_nextCoefficientTimeTargetRepresentative_eq D
        representative offset radius Fsys x w₀ hw₀ data hA c hc localization)
  have hsymbol :=
    boundary.nextIncomingBoundarySymbolValue_eventuallyEq_nextTerminalCoefficientValue
      D representative offset radius Fsys x w₀ hw₀ data hA c hc
  filter_upwards [hrepresentative, hsymbol] with n hrep hsym
  intro b
  rw [boundary.individualMixedBoundaryValueOnSimultaneousTail_zero_eq_selfValue
    D representative offset radius Fsys x w₀ hw₀ data hA c b n]
  change MvPolynomial.eval
      (fun z ↦ boundary.nextIncomingBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c z n)
      ((boundary.nextIncomingBoundarySelfChange D representative offset radius
        Fsys x w₀ hw₀ data hA c).sourceRepresentative b
          (boundary.nextIncomingBoundaryParameter D representative offset radius
            Fsys x w₀ hw₀ data hA n)) =
    MvPolynomial.eval
      (fun z ↦ Sum.elim
        (boundary.nextTerminalTimeValue D representative offset radius Fsys x
          w₀ hw₀ data hA c hc)
        (boundary.nextTerminalCoefficientValue D representative offset radius
          Fsys x w₀ hw₀ data hA c hc) z n)
      ((ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.coefficientIdealTimeAnalyticChange
        (boundary.nextTerminalDisplayed D representative offset radius Fsys x
          w₀ hw₀ data c hc) localization
        (boundary.nextCoefficientFamilyFromIndividualBoundaryZero D
          representative offset radius Fsys x w₀ hw₀ data c hc)).targetRepresentative
          b (boundary.nextTerminalParameter D representative offset radius Fsys
            x w₀ hw₀ data hA n))
  rw [hrep b]
  unfold nextCoefficientTimeTargetRepresentative
  rw [MvPolynomial.eval_rename,
    ← boundary.nextIncomingBoundaryParameter_eq_nextTerminalParameter D
      representative offset radius Fsys x w₀ hw₀ data hA n]
  have hassignment :
      (fun z ↦ boundary.nextIncomingBoundarySymbolValue D representative
        offset radius Fsys x w₀ hw₀ data hA c z n) =
        ((fun z ↦ Sum.elim
          (boundary.nextTerminalTimeValue D representative offset radius Fsys x
            w₀ hw₀ data hA c hc)
          (boundary.nextTerminalCoefficientValue D representative offset radius
            Fsys x w₀ hw₀ data hA c hc) z n) ∘ Sum.inr) := by
    funext z
    exact hsym z
  rw [hassignment]

/-! ## The localization-cleared target comparison -/

/-- An explicit representative of a denominator-cleared upper time
generator, retaining all prefix coefficient variables. -/
def nextTerminalClearedTargetRepresentative
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData)
    (a : Fin (localization.time.count + 1))
    (y : RestrictedBoxSpace p) :=
  MvPolynomial.rename Sum.inl
      (terminalFirstDerivativeProduct ℝ
        (Fin (data.orderedCluster
          (boundary.nextOrderedCluster D representative offset radius Fsys x
            w₀ hw₀ data c hc)).card)
        (data.orderedCluster
          (boundary.nextOrderedCluster D representative offset radius Fsys x
            w₀ hw₀ data c hc)).card
        (fun _ ↦ paperRankHermiteHigherCount boundary.S)) ^
      (boundary.preprocessed.descent.clusterStage
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)).certificate.terminalized.denominatorExponent *
    MvPolynomial.rename terminalFlattenedRetainedEmbedding
      ((ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.coefficientIdealTimeAnalyticChange
        (boundary.nextTerminalDisplayed D representative offset radius Fsys x
          w₀ hw₀ data c hc) localization
        (boundary.nextCoefficientFamilyFromIndividualBoundaryZero D
          representative offset radius Fsys x w₀ hw₀ data c hc)).sourceRepresentative
          a y)

/-- The explicit cleared representative is a representative of the flattened
cleared time target. -/
theorem nextTerminalClearedTargetRepresentative_germ_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData)
    (a : Fin (localization.time.count + 1)) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
          (TerminalMultiblockSourceIndex
            (data.orderedCluster
              (boundary.nextOrderedCluster D representative offset radius Fsys x
                w₀ hw₀ data c hc)).card
            (fun _ ↦ paperRankHermiteHigherCount boundary.S)
            (Fin (data.orderedCluster
              (boundary.nextOrderedCluster D representative offset radius Fsys x
                w₀ hw₀ data c hc)).card))
          (boundary.SimultaneousAnalyticPrefixSymbol D representative offset
            radius Fsys x w₀ hw₀ data
              (boundary.nextOrderedCluster D representative offset radius Fsys
                x w₀ hw₀ data c hc))
          (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.clearedTimeTarget
            (boundary.nextTerminalDisplayed D representative offset radius Fsys
              x w₀ hw₀ data c hc) localization a)) =
      (boundary.nextTerminalClearedTargetRepresentative D representative offset
        radius Fsys x w₀ hw₀ data hA c hc localization a :
          Germ (𝓝 (0 : RestrictedBoxSpace p)) _ ) := by
  let d := boundary.nextOrderedCluster D representative offset radius Fsys x w₀
    hw₀ data c hc
  let h := (data.orderedCluster d).card
  let higher : Fin h → ℕ := fun _ ↦ paperRankHermiteHigherCount boundary.S
  let Coeff := boundary.SimultaneousAnalyticPrefixSymbol D representative offset
    radius Fsys x w₀ hw₀ data d
  let exponent := (boundary.preprocessed.descent.clusterStage d).certificate.terminalized.denominatorExponent
  let timeChange :=
    ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.coefficientIdealTimeAnalyticChange
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc) localization
      (boundary.nextCoefficientFamilyFromIndividualBoundaryZero D representative
        offset radius Fsys x w₀ hw₀ data c hc)
  have htime := timeChange.source_germ_eq a
  have hretained := analyticPolynomialGermHom_rename_of
    (0 : RestrictedBoxSpace p)
    (terminalFlattenedRetainedEmbedding
      (h := h) (higher := higher) (Coeff := Coeff)) htime
  have hfirst := analyticPolynomialGermHom_rename_of
    (0 : RestrictedBoxSpace p)
    (Sum.inl : TerminalMultiblockSourceIndex h higher (Fin h) →
      TerminalMultiblockSourceIndex h higher (Fin h) ⊕ Coeff)
    (analyticPolynomialGermHom_terminalFirstDerivativeProduct
      (0 : RestrictedBoxSpace p) h higher)
  rw [show nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
        (TerminalMultiblockSourceIndex h higher (Fin h)) Coeff
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.clearedTimeTarget
          (boundary.nextTerminalDisplayed D representative offset radius Fsys x
            w₀ hw₀ data c hc) localization a) =
      MvPolynomial.rename Sum.inl
          (terminalFirstDerivativeProduct (RealAnalyticGerm p) (Fin h) h higher) ^
            exponent *
        MvPolynomial.rename
          (terminalFlattenedRetainedEmbedding
            (h := h) (higher := higher) (Coeff := Coeff))
          (nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
            (Fin h) Coeff (localization.time.generator a)) by
      exact nestedMvPolynomialFlattening_clearedRetained
        (RealAnalyticGerm p) Coeff higher exponent
          (localization.time.generator a)]
  rw [map_mul, map_pow, hfirst, hretained]
  exact Germ.coe_eq.mpr (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- The target representatives selected by the terminal analytic change agree
eventually with the explicit denominator-cleared representatives. -/
theorem eventually_nextTerminalClearedTargetRepresentative_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData) :
    ∀ᶠ y in 𝓝 (0 : RestrictedBoxSpace p), ∀ a,
      (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.terminalAnalyticChange
        (boundary.nextTerminalDisplayed D representative offset radius Fsys x
          w₀ hw₀ data c hc) localization).targetRepresentative a y =
        boundary.nextTerminalClearedTargetRepresentative D representative offset
          radius Fsys x w₀ hw₀ data hA c hc localization a y := by
  apply Filter.eventually_all.mpr
  intro a
  apply analyticPolynomialRepresentatives_eventually_eq
    (0 : RestrictedBoxSpace p)
    ((ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.terminalAnalyticChange
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc) localization).target_germ_eq a)
    (boundary.nextTerminalClearedTargetRepresentative_germ_eq D representative
      offset radius Fsys x w₀ hw₀ data hA c hc localization a)
    rfl

/-- Evaluating the explicit cleared representatives gives exactly the
first-derivative denominator times the coefficient-to-time source values. -/
theorem nextTerminalClearedTargetValue_eventually_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData) :
    ∀ᶠ n in atTop, ∀ a,
      (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.terminalAnalyticChange
        (boundary.nextTerminalDisplayed D representative offset radius Fsys x
          w₀ hw₀ data c hc) localization).targetValue
          (boundary.nextTerminalParameter D representative offset radius Fsys x
            w₀ hw₀ data hA)
          (boundary.nextTerminalSymbolValue D representative offset radius Fsys
            x w₀ hw₀ data hA c hc)
          (boundary.nextTerminalCoefficientValue D representative offset radius
            Fsys x w₀ hw₀ data hA c hc) a n =
        (∏ d, boundary.nextTerminalSymbolValue D representative offset radius
          Fsys x w₀ hw₀ data hA c hc
            (Sum.inl ⟨d, (0 : Fin (paperRankHermiteHigherCount boundary.S + 1))⟩)
            n) ^
          (boundary.preprocessed.descent.clusterStage
            (boundary.nextOrderedCluster D representative offset radius Fsys x
              w₀ hw₀ data c hc)).certificate.terminalized.denominatorExponent *
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.coefficientIdealTimeAnalyticChange
          (boundary.nextTerminalDisplayed D representative offset radius Fsys x
            w₀ hw₀ data c hc) localization
          (boundary.nextCoefficientFamilyFromIndividualBoundaryZero D
            representative offset radius Fsys x w₀ hw₀ data c hc)).sourceValue
          (boundary.nextTerminalParameter D representative offset radius Fsys x
            w₀ hw₀ data hA)
          (boundary.nextTerminalTimeValue D representative offset radius Fsys x
            w₀ hw₀ data hA c hc)
          (boundary.nextTerminalCoefficientValue D representative offset radius
            Fsys x w₀ hw₀ data hA c hc) a n := by
  have hrepresentative :=
    (boundary.nextTerminalParameter_tendsto D representative offset radius Fsys
      x w₀ hw₀ data hA).eventually
      (boundary.eventually_nextTerminalClearedTargetRepresentative_eq D
        representative offset radius Fsys x w₀ hw₀ data hA c hc localization)
  filter_upwards [hrepresentative] with n hn
  intro a
  have hassignment :
      ((fun i ↦ Sum.elim
          (boundary.nextTerminalSymbolValue D representative offset radius Fsys
            x w₀ hw₀ data hA c hc)
          (boundary.nextTerminalCoefficientValue D representative offset radius
            Fsys x w₀ hw₀ data hA c hc) i n) ∘
        terminalFlattenedRetainedEmbedding) =
      (fun i ↦ Sum.elim
        (boundary.nextTerminalTimeValue D representative offset radius Fsys x
          w₀ hw₀ data hA c hc)
        (boundary.nextTerminalCoefficientValue D representative offset radius
          Fsys x w₀ hw₀ data hA c hc) i n) := by
    funext z
    rcases z with i | z
    · rfl
    · rfl
  simp only [FiniteAnalyticNestedChangeOfGeneratorsData.targetValue,
    FiniteAnalyticNestedChangeOfGeneratorsData.sourceValue,
    FiniteAnalyticChangeOfGeneratorsData.targetValue,
    FiniteAnalyticChangeOfGeneratorsData.sourceValue, hn a,
    nextTerminalClearedTargetRepresentative, map_mul, map_pow,
    terminalFirstDerivativeProduct_eq_prod, map_prod, MvPolynomial.eval_X,
    MvPolynomial.eval_rename, Function.comp_apply, Sum.elim_inl,
    Sum.elim_inr, terminalFlattenedRetainedEmbedding,
    nextTerminalSymbolValue, nextTerminalTimeValue,
    realCentralTransferCentralValue]
  rw [hassignment]

/-- Both numeric identities required by the terminal coefficient bridge are
canonical. -/
noncomputable def nextTerminalCoefficientNumericCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData) :
    boundary.NextTerminalCoefficientNumericCompatibility D representative offset
      radius Fsys x w₀ hw₀ data hA c hc localization where
  incoming_eq :=
    boundary.nextCoefficientTimeTargetValue_eventually_eq_incoming D
      representative offset radius Fsys x w₀ hw₀ data hA c hc localization
  cleared_eq :=
    boundary.nextTerminalClearedTargetValue_eventually_eq D representative
      offset radius Fsys x w₀ hw₀ data hA c hc localization

/-! ## Comparison with the canonical upper simultaneous segment -/

/-- Embed the flattened terminal central/prefix variables into the active and
prefix variables of the upper simultaneous adapter. -/
def nextTerminalSimultaneousVariableEmbedding
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    (TerminalMultiblockSourceIndex
        (data.orderedCluster
          (boundary.nextOrderedCluster D representative offset radius Fsys x
            w₀ hw₀ data c hc)).card
        (fun _ ↦ paperRankHermiteHigherCount boundary.S)
        (Fin (data.orderedCluster
          (boundary.nextOrderedCluster D representative offset radius Fsys x
            w₀ hw₀ data c hc)).card) ⊕
      boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
        Fsys x w₀ hw₀ data
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc)) →
      (boundary.SimultaneousAnalyticActiveSymbol D representative offset radius
          Fsys x w₀ hw₀ data
            (boundary.nextOrderedCluster D representative offset radius Fsys x
              w₀ hw₀ data c hc) ⊕
        boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
          Fsys x w₀ hw₀ data
            (boundary.nextOrderedCluster D representative offset radius Fsys x
              w₀ hw₀ data c hc))
  | Sum.inl z => Sum.inl (Sum.inr z)
  | Sum.inr q => Sum.inr q

/-- Flattening the last displayed central generator is its terminal central
generator embedded in the simultaneous variable presentation. -/
theorem nextTerminalSimultaneousFlattenedGenerator_eq
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (b : Fin ((boundary.nextTerminalDisplayed D representative offset radius
      Fsys x w₀ hw₀ data c hc).central.count + 1)) :
    nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
        (boundary.SimultaneousAnalyticActiveSymbol D representative offset radius
          Fsys x w₀ hw₀ data
            (boundary.nextOrderedCluster D representative offset radius Fsys x
              w₀ hw₀ data c hc))
        (boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
          Fsys x w₀ hw₀ data
            (boundary.nextOrderedCluster D representative offset radius Fsys x
              w₀ hw₀ data c hc))
        (ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.afterGenerator
          (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
            (paperRankHermiteHigherCount boundary.S)
            (boundary.nextOrderedCluster D representative offset radius Fsys x
              w₀ hw₀ data c hc).val)
          (boundary.nextTerminalDisplayed D representative offset radius Fsys x
            w₀ hw₀ data c hc) b) =
      MvPolynomial.rename
        (boundary.nextTerminalSimultaneousVariableEmbedding D representative
          offset radius Fsys x w₀ hw₀ data c hc)
        (nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
          (TerminalMultiblockSourceIndex
            (data.orderedCluster
              (boundary.nextOrderedCluster D representative offset radius Fsys x
                w₀ hw₀ data c hc)).card
            (fun _ ↦ paperRankHermiteHigherCount boundary.S)
            (Fin (data.orderedCluster
              (boundary.nextOrderedCluster D representative offset radius Fsys x
                w₀ hw₀ data c hc)).card))
          (boundary.SimultaneousAnalyticPrefixSymbol D representative offset
            radius Fsys x w₀ hw₀ data
              (boundary.nextOrderedCluster D representative offset radius Fsys x
                w₀ hw₀ data c hc))
          ((boundary.nextTerminalDisplayed D representative offset radius Fsys x
            w₀ hw₀ data c hc).central.generator b)) := by
  change nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
      (boundary.SimultaneousAnalyticActiveSymbol D representative offset radius
        Fsys x w₀ hw₀ data
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc))
      (boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
        Fsys x w₀ hw₀ data
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc))
      (MvPolynomial.rename Sum.inr
        ((boundary.nextTerminalDisplayed D representative offset radius Fsys x
          w₀ hw₀ data c hc).central.generator b)) = _
  have hflatten := nestedMvPolynomialFlattening_rename_outer
      (Outer₁ := TerminalMultiblockSourceIndex
        (data.orderedCluster
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc)).card
        (fun _ ↦ paperRankHermiteHigherCount boundary.S)
        (Fin (data.orderedCluster
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc)).card))
      (Outer₂ := boundary.SimultaneousAnalyticActiveSymbol D representative offset
        radius Fsys x w₀ hw₀ data
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc))
      (RealAnalyticGerm p)
      (boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
        Fsys x w₀ hw₀ data
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc))
      (Sum.inr : TerminalMultiblockSourceIndex
        (data.orderedCluster
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc)).card
        (fun _ ↦ paperRankHermiteHigherCount boundary.S)
        (Fin (data.orderedCluster
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc)).card) →
          boundary.SimultaneousAnalyticActiveSymbol D representative offset
            radius Fsys x w₀ hw₀ data
              (boundary.nextOrderedCluster D representative offset radius Fsys x
                w₀ hw₀ data c hc))
      ((boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).central.generator b)
  have hembedding :
      (Sum.elim
        (fun i : TerminalMultiblockSourceIndex
            (data.orderedCluster
              (boundary.nextOrderedCluster D representative offset radius Fsys x
                w₀ hw₀ data c hc)).card
            (fun _ ↦ paperRankHermiteHigherCount boundary.S)
            (Fin (data.orderedCluster
              (boundary.nextOrderedCluster D representative offset radius Fsys x
                w₀ hw₀ data c hc)).card) ↦
          Sum.inl (Sum.inr i :
            boundary.SimultaneousAnalyticActiveSymbol D representative offset
              radius Fsys x w₀ hw₀ data
                (boundary.nextOrderedCluster D representative offset radius Fsys
                  x w₀ hw₀ data c hc)))
        (Sum.inr :
          boundary.SimultaneousAnalyticPrefixSymbol D representative offset
              radius Fsys x w₀ hw₀ data
                (boundary.nextOrderedCluster D representative offset radius Fsys
                  x w₀ hw₀ data c hc) →
            boundary.SimultaneousAnalyticActiveSymbol D representative offset
                radius Fsys x w₀ hw₀ data
                  (boundary.nextOrderedCluster D representative offset radius
                    Fsys x w₀ hw₀ data c hc) ⊕
              boundary.SimultaneousAnalyticPrefixSymbol D representative offset
                radius Fsys x w₀ hw₀ data
                  (boundary.nextOrderedCluster D representative offset radius
                    Fsys x w₀ hw₀ data c hc))) =
        boundary.nextTerminalSimultaneousVariableEmbedding D representative
          offset radius Fsys x w₀ hw₀ data c hc := by
    funext z
    rcases z with z | q <;> rfl
  rw [hembedding] at hflatten
  exact hflatten

/-- A terminal-localization source representative renamed into the flattened
upper simultaneous variables. -/
def nextTerminalSourceRepresentativeInSimultaneousVariables
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData)
    (b : Fin ((boundary.nextTerminalDisplayed D representative offset radius
      Fsys x w₀ hw₀ data c hc).central.count + 1))
    (y : RestrictedBoxSpace p) :=
  MvPolynomial.rename
    (boundary.nextTerminalSimultaneousVariableEmbedding D representative offset
      radius Fsys x w₀ hw₀ data c hc)
    ((ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.terminalAnalyticChange
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc) localization).sourceRepresentative b y)

/-- The renamed terminal source representative represents the embedded last
central generator. -/
theorem nextTerminalSourceRepresentativeInSimultaneousVariables_germ_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData)
    (b : Fin ((boundary.nextTerminalDisplayed D representative offset radius
      Fsys x w₀ hw₀ data c hc).central.count + 1)) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (MvPolynomial.rename
          (boundary.nextTerminalSimultaneousVariableEmbedding D representative
            offset radius Fsys x w₀ hw₀ data c hc)
          (nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
            (TerminalMultiblockSourceIndex
              (data.orderedCluster
                (boundary.nextOrderedCluster D representative offset radius Fsys
                  x w₀ hw₀ data c hc)).card
              (fun _ ↦ paperRankHermiteHigherCount boundary.S)
              (Fin (data.orderedCluster
                (boundary.nextOrderedCluster D representative offset radius Fsys
                  x w₀ hw₀ data c hc)).card))
            (boundary.SimultaneousAnalyticPrefixSymbol D representative offset
              radius Fsys x w₀ hw₀ data
                (boundary.nextOrderedCluster D representative offset radius Fsys
                  x w₀ hw₀ data c hc))
            ((boundary.nextTerminalDisplayed D representative offset radius Fsys
              x w₀ hw₀ data c hc).central.generator b))) =
      (boundary.nextTerminalSourceRepresentativeInSimultaneousVariables D
        representative offset radius Fsys x w₀ hw₀ data hA c hc localization b :
          Germ (𝓝 (0 : RestrictedBoxSpace p)) _) := by
  exact analyticPolynomialGermHom_rename_of (0 : RestrictedBoxSpace p)
    (boundary.nextTerminalSimultaneousVariableEmbedding D representative offset
      radius Fsys x w₀ hw₀ data c hc)
    ((ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.terminalAnalyticChange
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc) localization).source_germ_eq b)

/-- The localized terminal source and canonical simultaneous target
representatives agree on one neighborhood of the analytic basepoint. -/
theorem eventually_nextTerminalSourceRepresentative_eq_simultaneousTerminal
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData) :
    ∀ᶠ y in 𝓝 (0 : RestrictedBoxSpace p), ∀ b,
      boundary.nextTerminalSourceRepresentativeInSimultaneousVariables D
          representative offset radius Fsys x w₀ hw₀ data hA c hc localization
          b y =
        (boundary.simultaneousQuantitativeCentralAnalyticChange D representative
          offset radius Fsys x w₀ hw₀ data
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc)
          (boundary.nextTerminalOperation D representative offset radius Fsys x
            w₀ hw₀ data c hc)).targetRepresentative b y := by
  apply Filter.eventually_all.mpr
  intro b
  apply analyticPolynomialRepresentatives_eventually_eq
    (0 : RestrictedBoxSpace p)
    (boundary.nextTerminalSourceRepresentativeInSimultaneousVariables_germ_eq D
      representative offset radius Fsys x w₀ hw₀ data hA c hc localization b)
    ((boundary.simultaneousQuantitativeCentralAnalyticChange D representative
      offset radius Fsys x w₀ hw₀ data
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀ hw₀
        data c hc)
      (boundary.nextTerminalOperation D representative offset radius Fsys x w₀
        hw₀ data c hc)).target_germ_eq b)
  exact (boundary.nextTerminalSimultaneousFlattenedGenerator_eq D representative
    offset radius Fsys x w₀ hw₀ data c hc b).symm

/-- Under the terminal-to-simultaneous embedding, the exact terminal and
prefix assignments are the last simultaneous after assignment. -/
theorem nextTerminalFlattenedSymbolValue_eq_simultaneousAfter
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (z : TerminalMultiblockSourceIndex
        (data.orderedCluster
          (boundary.nextOrderedCluster D representative offset radius Fsys x
            w₀ hw₀ data c hc)).card
        (fun _ ↦ paperRankHermiteHigherCount boundary.S)
        (Fin (data.orderedCluster
          (boundary.nextOrderedCluster D representative offset radius Fsys x
            w₀ hw₀ data c hc)).card) ⊕
      boundary.SimultaneousAnalyticPrefixSymbol D representative offset radius
        Fsys x w₀ hw₀ data
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc))
    (n : ℕ) :
    Sum.elim
        (boundary.nextTerminalSymbolValue D representative offset radius Fsys x
          w₀ hw₀ data hA c hc)
        (boundary.nextTerminalCoefficientValue D representative offset radius
          Fsys x w₀ hw₀ data hA c hc) z n =
      boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D representative
        offset radius Fsys x w₀ hw₀ data hA
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)
        (boundary.nextTerminalExtraSteps D representative offset radius Fsys x
          w₀ hw₀ data c hc)
        (boundary.nextTerminalSimultaneousVariableEmbedding D representative
          offset radius Fsys x w₀ hw₀ data c hc z) n := by
  rcases z with z | q
  · change boundary.nextTerminalSymbolValue D representative offset radius Fsys
      x w₀ hw₀ data hA c hc z n =
      boundary.simultaneousQuantitativeAnalyticAfterValue D representative offset
        radius Fsys x w₀ hw₀ data hA
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)
        (boundary.nextTerminalExtraSteps D representative offset radius Fsys x
          w₀ hw₀ data c hc) (Sum.inr z) n
    rw [boundary.simultaneousQuantitativeAnalyticAfterValue_central D
      representative offset radius Fsys x w₀ hw₀ data hA
      (boundary.nextOrderedCluster D representative offset radius Fsys x w₀ hw₀
        data c hc)
      (boundary.nextTerminalExtraSteps D representative offset radius Fsys x w₀
        hw₀ data c hc) z n]
    rfl
  · rfl

/-- The canonical terminal source values agree with the last after-values of
the canonical upper simultaneous segment. -/
theorem nextTerminalSourceValueCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (localization :
      (boundary.nextTerminalDisplayed D representative offset radius Fsys x w₀
        hw₀ data c hc).TerminalLocalizationData) :
    boundary.NextTerminalSourceValueCompatibility D representative offset radius
      Fsys x w₀ hw₀ data hA c hc
      (boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
        representative offset radius Fsys x w₀ hw₀ data hA
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)) localization := by
  have hrepresentative :=
    (boundary.nextTerminalParameter_tendsto D representative offset radius Fsys
      x w₀ hw₀ data hA).eventually
      (boundary.eventually_nextTerminalSourceRepresentative_eq_simultaneousTerminal
        D representative offset radius Fsys x w₀ hw₀ data hA c hc localization)
  filter_upwards [hrepresentative] with n hn
  intro b
  have hn' :
      boundary.nextTerminalSourceRepresentativeInSimultaneousVariables D
          representative offset radius Fsys x w₀ hw₀ data hA c hc localization b
          (boundary.simultaneousQuantitativeAnalyticParameter D representative
            offset radius Fsys x w₀ hw₀ data hA n) =
        (boundary.simultaneousQuantitativeCentralAnalyticChange D representative
          offset radius Fsys x w₀ hw₀ data
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc)
          (boundary.nextTerminalOperation D representative offset radius Fsys x
            w₀ hw₀ data c hc)).targetRepresentative b
          (boundary.simultaneousQuantitativeAnalyticParameter D representative
            offset radius Fsys x w₀ hw₀ data hA n) := by
    simpa only [nextTerminalParameter,
      simultaneousQuantitativeAnalyticParameter] using hn b
  change MvPolynomial.eval
      (fun z ↦ Sum.elim
        (boundary.nextTerminalSymbolValue D representative offset radius Fsys x
          w₀ hw₀ data hA c hc)
        (boundary.nextTerminalCoefficientValue D representative offset radius
          Fsys x w₀ hw₀ data hA c hc) z n)
      ((ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.terminalAnalyticChange
        (boundary.nextTerminalDisplayed D representative offset radius Fsys x
          w₀ hw₀ data c hc) localization).sourceRepresentative b
          (boundary.nextTerminalParameter D representative offset radius Fsys x
            w₀ hw₀ data hA n)) = _
  change _ = boundary.simultaneousQuantitativeAnalyticAfterGeneratorValue D
    representative offset radius Fsys x w₀ hw₀ data hA
    (boundary.nextOrderedCluster D representative offset radius Fsys x w₀ hw₀
      data c hc)
    (boundary.nextTerminalOperation D representative offset radius Fsys x w₀
      hw₀ data c hc) b n
  unfold simultaneousQuantitativeAnalyticAfterGeneratorValue
  change _ = MvPolynomial.eval
      (fun z ↦ boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D
        representative offset radius Fsys x w₀ hw₀ data hA
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)
        (boundary.nextTerminalOperation D representative offset radius Fsys x
          w₀ hw₀ data c hc).val z n)
      ((boundary.simultaneousQuantitativeCentralAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)
        (boundary.nextTerminalOperation D representative offset radius Fsys x
          w₀ hw₀ data c hc)).targetRepresentative b
          (boundary.simultaneousQuantitativeAnalyticParameter D representative
            offset radius Fsys x w₀ hw₀ data hA n))
  rw [← hn']
  unfold nextTerminalSourceRepresentativeInSimultaneousVariables
  rw [MvPolynomial.eval_rename]
  have hassignment :
      (fun z ↦ Sum.elim
        (boundary.nextTerminalSymbolValue D representative offset radius Fsys x
          w₀ hw₀ data hA c hc)
        (boundary.nextTerminalCoefficientValue D representative offset radius
          Fsys x w₀ hw₀ data hA c hc) z n) =
        ((fun z ↦ boundary.simultaneousQuantitativeAnalyticAfterSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc)
          (boundary.nextTerminalOperation D representative offset radius Fsys x
            w₀ hw₀ data c hc).val z n) ∘
          boundary.nextTerminalSimultaneousVariableEmbedding D representative
            offset radius Fsys x w₀ hw₀ data c hc) := by
    funext z
    exact boundary.nextTerminalFlattenedSymbolValue_eq_simultaneousAfter D
      representative offset radius Fsys x w₀ hw₀ data hA c hc z n
  rw [hassignment]
  rw [show boundary.nextTerminalParameter D representative offset radius Fsys x
      w₀ hw₀ data hA n =
    boundary.simultaneousQuantitativeAnalyticParameter D representative offset
      radius Fsys x w₀ hw₀ data hA n by rfl]

/-! ## Compatibility-free cross-cluster transport -/

/-- The canonical upper terminal after-family inherits any lower bound at the
incoming individual boundary of the preceding cluster, with both finite
representative compatibilities filled internally. -/
theorem nextTerminalSimultaneousAfter_lower_of_individualMixedInitial_lower_auto
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount)
    (hincoming : HasInversePowerLowerBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)
      (boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)) :
    HasInversePowerLowerBound atTop
      (boundary.nextTerminalScale D representative offset radius Fsys x w₀ hw₀
        data hA c hc)
      (((boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
          representative offset radius Fsys x w₀ hw₀ data hA
          (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
            hw₀ data c hc)).change
        (boundary.nextTerminalOperation D representative offset radius Fsys x
          w₀ hw₀ data c hc)).afterValue) := by
  let localization := boundary.nextTerminalLocalizationData D representative
    offset radius Fsys x w₀ hw₀ data c hc
  have hsource :=
    boundary.nextTerminalAnalyticSource_lower_of_individualMixedInitial_lower D
      representative offset radius Fsys x w₀ hw₀ data hA c hc
      (boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
        representative offset radius Fsys x w₀ hw₀ data hA
        (boundary.nextOrderedCluster D representative offset radius Fsys x w₀
          hw₀ data c hc)) localization
      (boundary.nextTerminalCoefficientNumericCompatibility D representative
        offset radius Fsys x w₀ hw₀ data hA c hc localization) hincoming
  exact hsource.congr_of_eventually
    (boundary.nextTerminalSourceValueCompatibility D representative offset
      radius Fsys x w₀ hw₀ data hA c hc localization)

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
