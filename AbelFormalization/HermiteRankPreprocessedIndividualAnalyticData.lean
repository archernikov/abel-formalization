import AbelFormalization.FiniteAnalyticNestedCoefficientwiseEvaluation
import AbelFormalization.HermiteRankIndividualSimultaneousFiniteFamilyCompatibility

/-!
# Canonical finite analytic data for the mixed individual Hermite trace

Every displayed individual step already comes with finite source and central
families.  This module chooses finite analytic changes from the displayed
families to the canonical certificate sources and their central initial
forms.  The independently chosen displayed-boundary representatives are
compared after applying the literal selected-block currying and source
translation maps.

The recursively mixed boundary supplies the exact pre- and post-step
assignments, including equality of all unselected coordinates.  Together
with the existing coordinatewise polynomial bounds, this constructs the
whole `IndividualMixedFiniteAnalyticTraceData` without any extra evaluation
or compatibility hypotheses.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter Set
open scoped BigOperators Topology

universe u v

/-! ## Flattened selected-block coordinate maps -/

/-- Flatten the selected-block currying equivalence. -/
def selectedBlockFlattenedPolynomialHom
    (R : Type u) [CommRing R]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    (d : Block → ℕ) (selected : Block) :
    MvPolynomial (ClusterOperationSymbol Block d) R →+*
      MvPolynomial
        (ClusterOperationSymbol (Fin 1)
            (selectedBlockDerivativeCount d selected) ⊕
          ClusterOperationSymbol (RemainingBlock selected)
            (remainingBlockDerivativeCount d selected)) R :=
  (nestedMvPolynomialFlatteningAlgEquiv R
      (ClusterOperationSymbol (Fin 1)
        (selectedBlockDerivativeCount d selected))
      (ClusterOperationSymbol (RemainingBlock selected)
        (remainingBlockDerivativeCount d selected))).toRingHom.comp
    (selectedBlockCurryAlgEquiv R d selected).toRingHom

/-- Curry a selected block, perform the preliminary source translation, and
flatten the resulting nested polynomial. -/
def selectedBlockSourceFlattenedPolynomialHom
    (R : Type u) [CommRing R]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    (d : Block → ℕ) (selected : Block) :
    MvPolynomial (ClusterOperationSymbol Block d) R →+*
      MvPolynomial
        (ClusterOperationSymbol (Fin 1)
            (selectedBlockDerivativeCount d selected) ⊕
          ClusterOperationSymbol (RemainingBlock selected)
            (remainingBlockDerivativeCount d selected)) R :=
  (nestedMvPolynomialFlatteningAlgEquiv R
      (ClusterOperationSymbol (Fin 1)
        (selectedBlockDerivativeCount d selected))
      (ClusterOperationSymbol (RemainingBlock selected)
        (remainingBlockDerivativeCount d selected))).toRingHom.comp
    ((IndividualCentralTransferData.sourceTranslation R selected).toRingHom.comp
      (selectedBlockCurryAlgEquiv R d selected).toRingHom)

/-- Flattening the displayed source generator cancels the inverse currying
and inverse source translation used to define that generator. -/
theorem selectedBlockSourceFlattenedPolynomialHom_beforeGenerator
    {R : Type u} [CommRing R]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {transferData : IndividualCentralTransferData R d selected I}
    (displayed : IndividualCentralTransferData.DisplayedData R transferData)
    (k : Fin (displayed.source.count + 1)) :
    selectedBlockSourceFlattenedPolynomialHom R d selected
        (IndividualCentralTransferData.DisplayedData.beforeGenerator R displayed k) =
      nestedMvPolynomialFlatteningAlgEquiv R
        (ClusterOperationSymbol (Fin 1)
          (selectedBlockDerivativeCount d selected))
        (ClusterOperationSymbol (RemainingBlock selected)
          (remainingBlockDerivativeCount d selected))
        (displayed.source.generator k) := by
  change nestedMvPolynomialFlatteningAlgEquiv R _ _
      ((IndividualCentralTransferData.sourceTranslation R selected)
        (selectedBlockCurryAlgEquiv R d selected
          ((selectedBlockCurryAlgEquiv R d selected).symm
            ((IndividualCentralTransferData.sourceTranslation R selected).symm
              (displayed.source.generator k))))) = _
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/-- Flattening the displayed post-step generator cancels the inverse
currying used to re-adjoin its active variables. -/
theorem selectedBlockFlattenedPolynomialHom_afterGenerator
    {R : Type u} [CommRing R]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    {d : Block → ℕ} {selected : Block}
    {I : Ideal (MvPolynomial (ClusterOperationSymbol Block d) R)}
    {transferData : IndividualCentralTransferData R d selected I}
    (displayed : IndividualCentralTransferData.DisplayedData R transferData)
    (b : Fin (displayed.central.count + 1)) :
    selectedBlockFlattenedPolynomialHom R d selected
        (IndividualCentralTransferData.DisplayedData.afterGenerator R displayed b) =
      nestedMvPolynomialFlatteningAlgEquiv R
        (ClusterOperationSymbol (Fin 1)
          (selectedBlockDerivativeCount d selected))
        (ClusterOperationSymbol (RemainingBlock selected)
          (remainingBlockDerivativeCount d selected))
        (MvPolynomial.rename
          (Sum.inr : _ → ClusterOperationSymbol (Fin 1)
            (selectedBlockDerivativeCount d selected))
          (displayed.central.generator b)) := by
  change nestedMvPolynomialFlatteningAlgEquiv R _ _
      (selectedBlockCurryAlgEquiv R d selected
        ((selectedBlockCurryAlgEquiv R d selected).symm
          (MvPolynomial.rename
            (Sum.inr : _ → ClusterOperationSymbol (Fin 1)
              (selectedBlockDerivativeCount d selected))
            (displayed.central.generator b)))) = _
  rw [AlgEquiv.apply_symm_apply]

/-- Selected-block flattening commutes with extension of scalar coefficients. -/
theorem map_selectedBlockFlattenedPolynomialHom
    {R T : Type*} [CommRing R] [CommRing T]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    (f : R →+* T) (d : Block → ℕ) (selected : Block)
    (P : MvPolynomial (ClusterOperationSymbol Block d) R) :
    MvPolynomial.map f (selectedBlockFlattenedPolynomialHom R d selected P) =
      selectedBlockFlattenedPolynomialHom T d selected
        (MvPolynomial.map f P) := by
  let lhs : MvPolynomial (ClusterOperationSymbol Block d) R →+*
      MvPolynomial
        (ClusterOperationSymbol (Fin 1)
            (selectedBlockDerivativeCount d selected) ⊕
          ClusterOperationSymbol (RemainingBlock selected)
            (remainingBlockDerivativeCount d selected)) T :=
    (MvPolynomial.map f).comp
      (selectedBlockFlattenedPolynomialHom R d selected)
  let rhs : MvPolynomial (ClusterOperationSymbol Block d) R →+*
      MvPolynomial
        (ClusterOperationSymbol (Fin 1)
            (selectedBlockDerivativeCount d selected) ⊕
          ClusterOperationSymbol (RemainingBlock selected)
            (remainingBlockDerivativeCount d selected)) T :=
    (selectedBlockFlattenedPolynomialHom T d selected).comp
      (MvPolynomial.map f)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs, selectedBlockFlattenedPolynomialHom,
        nestedMvPolynomialFlatteningAlgEquiv, selectedBlockCurryAlgEquiv,
        clusterOperationRenameAlgEquiv, splitClusterCurryAlgEquiv]
    · intro z
      let split := splitClusterBlockSymbolEquiv (Fin 1)
        (RemainingBlock selected) (selectedBlockDerivativeCount d selected)
        (remainingBlockDerivativeCount d selected)
        (selectedBlockSplitOperationEquiv d selected z)
      generalize hsplit : split = y
      rcases y with y | y
      · simp [lhs, rhs, split, selectedBlockFlattenedPolynomialHom,
          nestedMvPolynomialFlatteningAlgEquiv, selectedBlockCurryAlgEquiv,
          clusterOperationRenameAlgEquiv, splitClusterCurryAlgEquiv, hsplit]
      · simp [lhs, rhs, split, selectedBlockFlattenedPolynomialHom,
          nestedMvPolynomialFlatteningAlgEquiv, selectedBlockCurryAlgEquiv,
          clusterOperationRenameAlgEquiv, splitClusterCurryAlgEquiv, hsplit]
  exact DFunLike.congr_fun hhom P

/-- Flattening a nested polynomial commutes with extension of its scalar
coefficients. -/
theorem map_nestedMvPolynomialFlatteningAlgEquiv
    {R T : Type*} [CommRing R] [CommRing T]
    {Outer Coeff : Type*} (f : R →+* T)
    (P : MvPolynomial Outer (MvPolynomial Coeff R)) :
    MvPolynomial.map f
        (nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff P) =
      nestedMvPolynomialFlatteningAlgEquiv T Outer Coeff
        (MvPolynomial.map (MvPolynomial.map f) P) := by
  let lhs : MvPolynomial Outer (MvPolynomial Coeff R) →+*
      MvPolynomial (Outer ⊕ Coeff) T :=
    (MvPolynomial.map f).comp
      (nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff).toRingHom
  let rhs : MvPolynomial Outer (MvPolynomial Coeff R) →+*
      MvPolynomial (Outer ⊕ Coeff) T :=
    (nestedMvPolynomialFlatteningAlgEquiv T Outer Coeff).toRingHom.comp
      (MvPolynomial.map (MvPolynomial.map f))
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro Q
      dsimp only [lhs, rhs]
      simp only [RingHom.comp_apply]
      change MvPolynomial.map f
          (nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff
            (MvPolynomial.C Q)) =
        nestedMvPolynomialFlatteningAlgEquiv T Outer Coeff
          (MvPolynomial.map (MvPolynomial.map f) (MvPolynomial.C Q))
      rw [nestedMvPolynomialFlattening_C, MvPolynomial.map_rename,
        MvPolynomial.map_C, nestedMvPolynomialFlattening_C]
    · intro z
      dsimp only [lhs, rhs]
      simp only [RingHom.comp_apply]
      have hR := nestedMvPolynomialFlattening_map_C
        (R := R) (Outer := Outer) (Coeff := Coeff) (MvPolynomial.X z)
      have hT := nestedMvPolynomialFlattening_map_C
        (R := T) (Outer := Outer) (Coeff := Coeff) (MvPolynomial.X z)
      simp only [MvPolynomial.map_X] at hR hT ⊢
      change MvPolynomial.map f
          (nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff
            (MvPolynomial.X z)) =
        nestedMvPolynomialFlatteningAlgEquiv T Outer Coeff (MvPolynomial.X z)
      rw [hR, MvPolynomial.map_rename, MvPolynomial.map_X, hT]
  exact DFunLike.congr_fun hhom P

/-- The selected-block source translation commutes with extension of the
scalar coefficients in the remaining-block polynomial ring. -/
theorem map_individualCentralSourceTranslation
    {R T : Type*} [CommRing R] [CommRing T]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    (f : R →+* T) (d : Block → ℕ) (selected : Block)
    (P : MvPolynomial
      (ClusterOperationSymbol (Fin 1)
        (selectedBlockDerivativeCount d selected))
      (IndividualCentralCoefficientRing R d selected)) :
    MvPolynomial.map (MvPolynomial.map f)
        (IndividualCentralTransferData.sourceTranslation R selected P) =
      IndividualCentralTransferData.sourceTranslation T selected
        (MvPolynomial.map (MvPolynomial.map f) P) := by
  let lhs : MvPolynomial
        (ClusterOperationSymbol (Fin 1)
          (selectedBlockDerivativeCount d selected))
        (IndividualCentralCoefficientRing R d selected) →+*
      MvPolynomial
        (ClusterOperationSymbol (Fin 1)
          (selectedBlockDerivativeCount d selected))
        (IndividualCentralCoefficientRing T d selected) :=
    (MvPolynomial.map (MvPolynomial.map f)).comp
      (IndividualCentralTransferData.sourceTranslation R selected).toRingHom
  let rhs : MvPolynomial
        (ClusterOperationSymbol (Fin 1)
          (selectedBlockDerivativeCount d selected))
        (IndividualCentralCoefficientRing R d selected) →+*
      MvPolynomial
        (ClusterOperationSymbol (Fin 1)
          (selectedBlockDerivativeCount d selected))
        (IndividualCentralCoefficientRing T d selected) :=
    (IndividualCentralTransferData.sourceTranslation T selected).toRingHom.comp
      (MvPolynomial.map (MvPolynomial.map f))
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro Q
      simp [lhs, rhs, IndividualCentralTransferData.sourceTranslation,
        polynomialCoordinateTranslation]
    · intro z
      rcases z with i | z <;>
        simp [lhs, rhs, IndividualCentralTransferData.sourceTranslation,
          polynomialCoordinateTranslation]
  exact DFunLike.congr_fun hhom P

/-- Selected-block currying commutes with extension of scalar coefficients. -/
theorem map_selectedBlockCurryAlgEquiv
    {R T : Type*} [CommRing R] [CommRing T]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    (f : R →+* T) (d : Block → ℕ) (selected : Block)
    (P : MvPolynomial (ClusterOperationSymbol Block d) R) :
    MvPolynomial.map (MvPolynomial.map f)
        (selectedBlockCurryAlgEquiv R d selected P) =
      selectedBlockCurryAlgEquiv T d selected (MvPolynomial.map f P) := by
  apply (nestedMvPolynomialFlatteningAlgEquiv T
    (ClusterOperationSymbol (Fin 1)
      (selectedBlockDerivativeCount d selected))
    (ClusterOperationSymbol (RemainingBlock selected)
      (remainingBlockDerivativeCount d selected))).injective
  rw [← map_nestedMvPolynomialFlatteningAlgEquiv]
  change MvPolynomial.map f
      (selectedBlockFlattenedPolynomialHom R d selected P) =
    selectedBlockFlattenedPolynomialHom T d selected (MvPolynomial.map f P)
  exact map_selectedBlockFlattenedPolynomialHom f d selected P

/-- The translated selected-block flattening also commutes with extension of
scalar coefficients. -/
theorem map_selectedBlockSourceFlattenedPolynomialHom
    {R T : Type*} [CommRing R] [CommRing T]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    (f : R →+* T) (d : Block → ℕ) (selected : Block)
    (P : MvPolynomial (ClusterOperationSymbol Block d) R) :
    MvPolynomial.map f
        (selectedBlockSourceFlattenedPolynomialHom R d selected P) =
      selectedBlockSourceFlattenedPolynomialHom T d selected
        (MvPolynomial.map f P) := by
  change MvPolynomial.map f
      (nestedMvPolynomialFlatteningAlgEquiv R _ _
        (IndividualCentralTransferData.sourceTranslation R selected
          (selectedBlockCurryAlgEquiv R d selected P))) =
    nestedMvPolynomialFlatteningAlgEquiv T _ _
      (IndividualCentralTransferData.sourceTranslation T selected
        (selectedBlockCurryAlgEquiv T d selected (MvPolynomial.map f P)))
  rw [map_nestedMvPolynomialFlatteningAlgEquiv,
    map_individualCentralSourceTranslation,
    map_selectedBlockCurryAlgEquiv]

/-- A representative stays a representative after selected-block
flattening. -/
theorem analyticPolynomialGermHom_selectedBlockFlattened_of
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    {x : E} (d : Block → ℕ) (selected : Block)
    {P : MvPolynomial (ClusterOperationSymbol Block d) (AnalyticGermAt x)}
    {F : E → MvPolynomial (ClusterOperationSymbol Block d) ℝ}
    (hF : analyticPolynomialGermHom x P =
      (F : Germ (𝓝 x)
        (MvPolynomial (ClusterOperationSymbol Block d) ℝ))) :
    analyticPolynomialGermHom x
        (selectedBlockFlattenedPolynomialHom (AnalyticGermAt x) d selected P) =
      ((fun y ↦ selectedBlockFlattenedPolynomialHom ℝ d selected (F y)) :
        Germ (𝓝 x)
          (MvPolynomial
            (ClusterOperationSymbol (Fin 1)
                (selectedBlockDerivativeCount d selected) ⊕
              ClusterOperationSymbol (RemainingBlock selected)
                (remainingBlockDerivativeCount d selected)) ℝ)) := by
  apply analyticPolynomialGermHom_ringHom_of_representative
    (selectedBlockFlattenedPolynomialHom (AnalyticGermAt x) d selected)
    (selectedBlockFlattenedPolynomialHom ℝ d selected)
  · intro r
    simp [selectedBlockFlattenedPolynomialHom,
      nestedMvPolynomialFlatteningAlgEquiv, selectedBlockCurryAlgEquiv,
      clusterOperationRenameAlgEquiv, splitClusterCurryAlgEquiv]
  · intro r
    simp [selectedBlockFlattenedPolynomialHom,
      nestedMvPolynomialFlatteningAlgEquiv, selectedBlockCurryAlgEquiv,
      clusterOperationRenameAlgEquiv, splitClusterCurryAlgEquiv]
  · intro Q
    exact map_selectedBlockFlattenedPolynomialHom
      (algebraMap ℝ (AnalyticGermAt x)) d selected Q
  · exact hF

/-- A representative stays a representative after currying, source
translation, and flattening. -/
theorem analyticPolynomialGermHom_selectedBlockSourceFlattened_of
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Block : Type v} [Fintype Block] [DecidableEq Block]
    {x : E} (d : Block → ℕ) (selected : Block)
    {P : MvPolynomial (ClusterOperationSymbol Block d) (AnalyticGermAt x)}
    {F : E → MvPolynomial (ClusterOperationSymbol Block d) ℝ}
    (hF : analyticPolynomialGermHom x P =
      (F : Germ (𝓝 x)
        (MvPolynomial (ClusterOperationSymbol Block d) ℝ))) :
    analyticPolynomialGermHom x
        (selectedBlockSourceFlattenedPolynomialHom
          (AnalyticGermAt x) d selected P) =
      ((fun y ↦ selectedBlockSourceFlattenedPolynomialHom ℝ d selected
          (F y)) :
        Germ (𝓝 x)
          (MvPolynomial
            (ClusterOperationSymbol (Fin 1)
                (selectedBlockDerivativeCount d selected) ⊕
              ClusterOperationSymbol (RemainingBlock selected)
                (remainingBlockDerivativeCount d selected)) ℝ)) := by
  apply analyticPolynomialGermHom_ringHom_of_representative
    (selectedBlockSourceFlattenedPolynomialHom
      (AnalyticGermAt x) d selected)
    (selectedBlockSourceFlattenedPolynomialHom ℝ d selected)
  · intro r
    simp [selectedBlockSourceFlattenedPolynomialHom,
      nestedMvPolynomialFlatteningAlgEquiv, selectedBlockCurryAlgEquiv,
      IndividualCentralTransferData.sourceTranslation,
      polynomialCoordinateTranslation, clusterOperationRenameAlgEquiv,
      splitClusterCurryAlgEquiv]
  · intro r
    simp [selectedBlockSourceFlattenedPolynomialHom,
      nestedMvPolynomialFlatteningAlgEquiv, selectedBlockCurryAlgEquiv,
      IndividualCentralTransferData.sourceTranslation,
      polynomialCoordinateTranslation, clusterOperationRenameAlgEquiv,
      splitClusterCurryAlgEquiv]
  · intro Q
    exact map_selectedBlockSourceFlattenedPolynomialHom
      (algebraMap ℝ (AnalyticGermAt x)) d selected Q
  · exact hF

variable {R : Type*} [CommRing R]
variable {Block : Type v} [Fintype Block] [DecidableEq Block]

/-- Flattening selected-block currying preserves evaluation under the two
restricted pieces of a flat assignment. -/
theorem eval_selectedBlockFlattenedPolynomialHom
    (d : Block → ℕ) (selected : Block)
    (value : ClusterOperationSymbol Block d → ℝ)
    (P : MvPolynomial (ClusterOperationSymbol Block d) ℝ) :
    MvPolynomial.eval
        (Sum.elim (selectedBlockActiveAssignment d selected value)
          (selectedBlockCoefficientAssignment d selected value))
        (selectedBlockFlattenedPolynomialHom ℝ d selected P) =
      MvPolynomial.eval value P := by
  have hflatten := eval₂Hom_nestedMvPolynomialFlatteningAlgEquiv
    (RingHom.id ℝ) (selectedBlockActiveAssignment d selected value)
    (selectedBlockCoefficientAssignment d selected value)
    (selectedBlockCurryAlgEquiv ℝ d selected P)
  have hcurry := eval₂Hom_selectedBlockCurryAlgEquiv
    (RingHom.id ℝ) d selected value P
  rw [← MvPolynomial.eval₂_id]
  change MvPolynomial.eval₂Hom (RingHom.id ℝ)
      (Sum.elim (selectedBlockActiveAssignment d selected value)
        (selectedBlockCoefficientAssignment d selected value))
      (nestedMvPolynomialFlatteningAlgEquiv ℝ
        (ClusterOperationSymbol (Fin 1)
          (selectedBlockDerivativeCount d selected))
        (ClusterOperationSymbol (RemainingBlock selected)
          (remainingBlockDerivativeCount d selected))
        (selectedBlockCurryAlgEquiv ℝ d selected P)) = _
  rw [hflatten]
  exact hcurry.symm

namespace RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary

variable {iota : Type*} {A : ℝ → ℝ} {m p a : ℕ} [Nonempty (Fin m)]
variable (D : RestrictedBox p)
variable (representative : iota → Fin m)
variable (offset : iota → D.analyticNearClosedBoxSubalgebra)
variable (radius : ℝ)
variable (Fsys : Fin (m + p + a) → RestrictedSource m p a → ℝ)
variable (x : ℕ → RestrictedSource m p a)
variable (w₀ : RestrictedBoxSpace p) (hw₀ : w₀ ∈ D.closedBox)
variable (data : RepresentativeClusterSubsequence
  (fun n i ↦ A ((x n).1.1 i)))
variable (boundary : RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
  D representative offset radius Fsys x w₀ hw₀ data)

noncomputable local instance individualMixedAnalyticBlockDecidableEq
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-- Active one-block symbols at an individual mixed step. -/
abbrev IndividualMixedAnalyticActiveSymbol
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :=
  RealJetTransferIndex 0
    (data.orderedClusterQuantitativeStepDerivativeCount
      (paperRankHermiteHigherCount boundary.S) c
      (boundary.preprocessed.fixedSteps c) j)

/-- Symbols of all blocks not selected at an individual mixed step. -/
abbrev IndividualMixedAnalyticRemainingSymbol
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :=
  ClusterOperationSymbol
    (RemainingBlock (data.orderedClusterIndividualSelectedBlock c
      (boundary.preprocessed.fixedSteps c) j))
    (remainingBlockDerivativeCount
      (data.orderedClusterPrefixConstantDerivativeCount
        (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
      (data.orderedClusterIndividualSelectedBlock c
        (boundary.preprocessed.fixedSteps c) j))

/-- The literal source assignment used by the coefficientwise transfer. -/
def individualMixedAnalyticSourceValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    boundary.IndividualMixedAnalyticActiveSymbol D representative offset radius
      Fsys x w₀ hw₀ data c j → ℕ → ℝ :=
  realJetActualAssignment
    (data.orderedClusterIndividualPostLogScale c A
      (fun q ↦ data.orderedClusterRawTime
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA q) c)
      (boundary.preprocessed.fixedSteps c) j)
    (data.orderedClusterQuantitativeStepDerivativeCount
      (paperRankHermiteHigherCount boundary.S) c
      (boundary.preprocessed.fixedSteps c) j)
    (boundary.individualMixedTraceJets D representative offset radius Fsys x
      w₀ hw₀ data hA c j)

/-- The post-log selected-block assignment used by the central change. -/
def individualMixedAnalyticAfterValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    boundary.IndividualMixedAnalyticActiveSymbol D representative offset radius
      Fsys x w₀ hw₀ data c j → ℕ → ℝ :=
  individualCentralPostLogActiveAssignment A
    (data.orderedClusterIndividualPostLogScale c A
      (fun q ↦ data.orderedClusterRawTime
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA q) c)
      (boundary.preprocessed.fixedSteps c) j)
    (data.orderedClusterQuantitativeStepDerivativeCount
      (paperRankHermiteHigherCount boundary.S) c
      (boundary.preprocessed.fixedSteps c) j)

/-! ## Canonical nested changes -/

/-- Analytic change from the displayed translated source family to the
canonical certificate sources at one individual step. -/
noncomputable def individualMixedSourceAnalyticChange
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :=
  finiteAnalyticNestedChangeOfGeneratorsDataOfSpan
    (0 : RestrictedBoxSpace p)
    ((boundary.individualNumericDisplayed D representative offset radius Fsys x
      w₀ hw₀ data c).displayed
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j)).source.generator
    (boundary.individualMixedTransferData D representative offset radius Fsys x
      w₀ hw₀ data c j).certificate.source
    (by
      apply Ideal.span_le.2
      rintro _ ⟨q, rfl⟩
      apply Ideal.mem_span_range_iff_exists_fun.mpr
      refine ⟨((boundary.individualNumericDisplayed D representative offset
        radius Fsys x w₀ hw₀ data c).displayed
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j)).identities.sourceCoefficient q,
        ?_⟩
      exact (((boundary.individualNumericDisplayed D representative offset
        radius Fsys x w₀ hw₀ data c).displayed
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j)).identities.source_identity q).symm)

/-- Canonical central initial form with the fresh selected representative
re-adjoined. -/
def individualMixedCanonicalCentralGenerator
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (q : Fin ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.count)) :
    MvPolynomial
      (boundary.IndividualMixedAnalyticActiveSymbol D representative offset
        radius Fsys x w₀ hw₀ data c j)
      (MvPolynomial
        (boundary.IndividualMixedAnalyticRemainingSymbol D representative offset
          radius Fsys x w₀ hw₀ data c j) (RealAnalyticGerm p)) :=
  MvPolynomial.rename
    (Sum.inr : _ → boundary.IndividualMixedAnalyticActiveSymbol D representative
      offset radius Fsys x w₀ hw₀ data c j)
    (IndividualCentralTransferData.centralGenerator (RealAnalyticGerm p)
      (boundary.individualMixedTransferData D representative offset radius Fsys x
        w₀ hw₀ data c j) q)

/-- The displayed central family in the same re-extended nested ring. -/
def individualMixedDisplayedCentralGenerator
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (b : Fin (((boundary.individualNumericDisplayed D representative offset
      radius Fsys x w₀ hw₀ data c).displayed
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j)).central.count + 1)) :
    MvPolynomial
      (boundary.IndividualMixedAnalyticActiveSymbol D representative offset
        radius Fsys x w₀ hw₀ data c j)
      (MvPolynomial
        (boundary.IndividualMixedAnalyticRemainingSymbol D representative offset
          radius Fsys x w₀ hw₀ data c j) (RealAnalyticGerm p)) :=
  MvPolynomial.rename
    (Sum.inr : _ → boundary.IndividualMixedAnalyticActiveSymbol D representative
      offset radius Fsys x w₀ hw₀ data c j)
    (((boundary.individualNumericDisplayed D representative offset radius Fsys x
      w₀ hw₀ data c).displayed
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j)).central.generator b)

/-- Analytic change from the canonical central initial forms to the displayed
post-step central family. -/
noncomputable def individualMixedCentralAnalyticChange
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :=
  finiteAnalyticNestedChangeOfGeneratorsDataOfSpan
    (0 : RestrictedBoxSpace p)
    (boundary.individualMixedCanonicalCentralGenerator D representative offset
      radius Fsys x w₀ hw₀ data c j)
    (boundary.individualMixedDisplayedCentralGenerator D representative offset
      radius Fsys x w₀ hw₀ data c j)
    (by
      apply le_of_eq
      let displayed := (boundary.individualNumericDisplayed D representative
        offset radius Fsys x w₀ hw₀ data c).displayed
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j)
      let transfer := boundary.individualMixedTransferData D representative offset
        radius Fsys x w₀ hw₀ data c j
      have hcore : Ideal.span (Set.range displayed.central.generator) =
          Ideal.span (Set.range (IndividualCentralTransferData.centralGenerator
            (RealAnalyticGerm p) transfer)) :=
        displayed.central.span_eq.trans transfer.central_span_eq_core.symm
      exact (span_rename_inr_range_eq_unusedPolynomialExtension
          displayed.central.generator).trans
        ((congrArg (unusedPolynomialExtension (Fin 1)) hcore).trans
          (span_rename_inr_range_eq_unusedPolynomialExtension
            (IndividualCentralTransferData.centralGenerator
              (RealAnalyticGerm p) transfer)).symm))

/-! ## The common remaining-block assignment -/

/-- The selected step changes no unselected block, so the coefficient-ring
assignment read at the post-boundary is also the predecessor assignment. -/
theorem individualMixedRemainingSymbolValue_eq_before
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    boundary.individualMixedRemainingSymbolValue D representative offset radius
        Fsys x w₀ hw₀ data hA c j =
      selectedBlockCoefficientAssignment
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
        (data.orderedClusterIndividualSelectedBlock c
          (boundary.preprocessed.fixedSteps c) j)
        (boundary.individualMixedBoundarySymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j).castSucc) := by
  let d := data.orderedClusterPrefixConstantDerivativeCount
    (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  change selectedBlockCoefficientAssignment d selected
      (boundary.individualMixedBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).succ) =
    selectedBlockCoefficientAssignment d selected
      (boundary.individualMixedBoundarySymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j).castSucc)
  unfold selectedBlockCoefficientAssignment
  funext z n
  rcases z with b | z
  · have hne : b.1 ≠ data.orderedClusterBalancingPrefixBlock c
        ((boundary.preprocessed.fixedSteps c).get j) := by
      simpa only [selected,
        data.orderedClusterIndividualSelectedBlock_eq] using b.2
    have hne' : b.1 ≠ data.orderedClusterBalancingPrefixBlock c
        (boundary.preprocessed.fixedSteps c)[j.val] := by
      simpa only [List.get_eq_getElem] using hne
    have hbase : (selectedBlockSumEquiv selected).symm b.1 =
        Sum.inr b := by
      simp [selectedBlockSumEquiv, b.2]
    have hsymbol :
        (selectedBlockSplitOperationEquiv d selected).symm
            ((splitClusterBlockSymbolEquiv (Fin 1) (RemainingBlock selected)
              (selectedBlockDerivativeCount d selected)
              (remainingBlockDerivativeCount d selected)).symm
              (Sum.inr (Sum.inl b))) =
          Sum.inl b.1 := by
      apply (selectedBlockSplitOperationEquiv d selected).injective
      rw [Equiv.apply_symm_apply]
      simp [selectedBlockSplitOperationEquiv, clusterOperationSymbolEquiv,
        splitClusterBlockSymbolEquiv, selectedBlockSumEquiv, hne', hbase,
        d, selected]
    rw [hsymbol]
    exact congrFun
      (boundary.individualMixedBoundarySymbolValue_free_succ_eq_of_ne D
        representative offset radius Fsys x w₀ hw₀ data hA c j b.1 b.2) n
  · rcases z with br | b
    · rcases br with ⟨b, r⟩
      have hne : b.1 ≠ data.orderedClusterBalancingPrefixBlock c
          ((boundary.preprocessed.fixedSteps c).get j) := by
        simpa only [selected,
          data.orderedClusterIndividualSelectedBlock_eq] using b.2
      have hne' : b.1 ≠ data.orderedClusterBalancingPrefixBlock c
          (boundary.preprocessed.fixedSteps c)[j.val] := by
        simpa only [List.get_eq_getElem] using hne
      have hbase : (selectedBlockSumEquiv selected).symm b.1 =
          Sum.inr b := by
        simp [selectedBlockSumEquiv, b.2]
      have hsymbol :
          (selectedBlockSplitOperationEquiv d selected).symm
              ((splitClusterBlockSymbolEquiv (Fin 1) (RemainingBlock selected)
                (selectedBlockDerivativeCount d selected)
                (remainingBlockDerivativeCount d selected)).symm
                (Sum.inr (Sum.inr (Sum.inl ⟨b, r⟩)))) =
            Sum.inr (Sum.inl ⟨b.1, r⟩) := by
        apply (selectedBlockSplitOperationEquiv d selected).injective
        rw [Equiv.apply_symm_apply]
        simp [selectedBlockSplitOperationEquiv, clusterOperationSymbolEquiv,
          splitClusterBlockSymbolEquiv, selectedBlockSumEquiv,
          remainingBlockDerivativeCount, hne', d, selected]
        change
          (⟨Sum.inr b, r⟩ :
            Σ b : Fin 1 ⊕ RemainingBlock selected,
              Fin (Sum.elim (selectedBlockDerivativeCount d selected)
                (remainingBlockDerivativeCount d selected) b)) =
            ⟨(selectedBlockSumEquiv selected).symm b.1, _⟩
        apply Sigma.ext
        · exact hbase.symm
        · have hmotive :
              remainingBlockDerivativeCount d selected b =
                Sum.elim (selectedBlockDerivativeCount d selected)
                  (remainingBlockDerivativeCount d selected)
                  ((selectedBlockSumEquiv selected).symm b.1) := by
            rw [hbase]
            rfl
          apply (Fin.heq_ext_iff hmotive).2
          rfl
      rw [hsymbol]
      exact congrFun
        (boundary.individualMixedBoundarySymbolValue_derivative_succ_eq_of_ne D
          representative offset radius Fsys x w₀ hw₀ data hA c j b.1 b.2 r) n
    · have hne : b.1 ≠ data.orderedClusterBalancingPrefixBlock c
          ((boundary.preprocessed.fixedSteps c).get j) := by
        simpa only [selected,
          data.orderedClusterIndividualSelectedBlock_eq] using b.2
      have hne' : b.1 ≠ data.orderedClusterBalancingPrefixBlock c
          (boundary.preprocessed.fixedSteps c)[j.val] := by
        simpa only [List.get_eq_getElem] using hne
      have hbase : (selectedBlockSumEquiv selected).symm b.1 =
          Sum.inr b := by
        simp [selectedBlockSumEquiv, b.2]
      have hsymbol :
          (selectedBlockSplitOperationEquiv d selected).symm
              ((splitClusterBlockSymbolEquiv (Fin 1) (RemainingBlock selected)
                (selectedBlockDerivativeCount d selected)
                (remainingBlockDerivativeCount d selected)).symm
                (Sum.inr (Sum.inr (Sum.inr b)))) =
            Sum.inr (Sum.inr b.1) := by
        apply (selectedBlockSplitOperationEquiv d selected).injective
        rw [Equiv.apply_symm_apply]
        simp [selectedBlockSplitOperationEquiv, clusterOperationSymbolEquiv,
          splitClusterBlockSymbolEquiv, selectedBlockSumEquiv, hne', hbase,
          d, selected]
      rw [hsymbol]
      exact congrFun
        (boundary.individualMixedBoundarySymbolValue_time_succ_eq_of_ne D
          representative offset radius Fsys x w₀ hw₀ data hA c j b.1 b.2) n

/-- The source coefficient representative selected by the common finite
moving family. -/
def individualMixedSupportedCoefficientRepresentative
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (coefficients : boundary.IndividualMixedSourceCoefficientData D
      representative offset radius Fsys x w₀ hw₀ data c j)
    (q : Fin ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.count))
    (e : boundary.IndividualMixedAnalyticActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c j →₀ ℕ)
    (he : e ∈ ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.source q).support) :=
  coefficients.representative ⟨q, ⟨e, he⟩⟩

/-- The selected supported representative has the required coefficient
polynomial germ. -/
theorem individualMixedSupportedCoefficientRepresentative_germ_eq
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (coefficients : boundary.IndividualMixedSourceCoefficientData D
      representative offset radius Fsys x w₀ hw₀ data c j)
    (q : Fin ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.count))
    (e : boundary.IndividualMixedAnalyticActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c j →₀ ℕ)
    (he : e ∈ ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.source q).support) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (((boundary.individualMixedTransferData D representative offset radius
          Fsys x w₀ hw₀ data c j).certificate.source q).coeff e) =
      (boundary.individualMixedSupportedCoefficientRepresentative D
        representative offset radius Fsys x w₀ hw₀ data c j coefficients
        q e he :
        Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial
            (boundary.IndividualMixedAnalyticRemainingSymbol D representative
              offset radius Fsys x w₀ hw₀ data c j) ℝ)) := by
  exact coefficients.germ_eq ⟨q, ⟨e, he⟩⟩

/-- The generic supported evaluation is the concrete coefficient value used
by the mixed individual transfer. -/
theorem nestedSupportedCoefficientValue_eq_individualMixed
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (coefficients : boundary.IndividualMixedSourceCoefficientData D
      representative offset radius Fsys x w₀ hw₀ data c j)
    (q : Fin ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.count))
    (e : boundary.IndividualMixedAnalyticActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c j →₀ ℕ) (n : ℕ) :
    nestedSupportedCoefficientValue
        ((boundary.individualMixedTransferData D representative offset radius
          Fsys x w₀ hw₀ data c j).certificate.source q)
        (boundary.individualMixedSupportedCoefficientRepresentative D
          representative offset radius Fsys x w₀ hw₀ data c j
          coefficients q)
        (boundary.individualNumericAnalyticParameter D representative offset
          radius Fsys x w₀ hw₀ data hA)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j) e n =
      boundary.individualMixedSourceCoefficientValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j coefficients q e n := by
  classical
  unfold nestedSupportedCoefficientValue individualMixedSourceCoefficientValue
  split <;> rename_i h₁
  · split <;> rename_i h₂
    · have hh : h₁ = h₂ := Subsingleton.elim _ _
      subst h₂
      rfl
    · exact (h₂ h₁).elim
  · split <;> rename_i h₂
    · exact (h₁ h₂).elim
    · rfl

/-! ## Numeric values of the two analytic changes -/

/-- Values of the displayed translated source representatives at the literal
one-block source assignment. -/
def individualMixedAnalyticBeforeValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :=
  (boundary.individualMixedSourceAnalyticChange D representative offset radius
    Fsys x w₀ hw₀ data c j).sourceValue
      (boundary.individualNumericAnalyticParameter D representative offset
        radius Fsys x w₀ hw₀ data hA)
      (boundary.individualMixedAnalyticSourceValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j)
      (boundary.individualMixedRemainingSymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j)

/-- Values of the displayed central representatives at the exact post-log
assignment. -/
def individualMixedAnalyticAfterGeneratorValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :=
  (boundary.individualMixedCentralAnalyticChange D representative offset radius
    Fsys x w₀ hw₀ data c j).targetValue
      (boundary.individualNumericAnalyticParameter D representative offset
        radius Fsys x w₀ hw₀ data hA)
      (boundary.individualMixedAnalyticAfterValue D representative offset radius
        Fsys x w₀ hw₀ data hA c j)
      (boundary.individualMixedRemainingSymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j)

/-- Evaluated entries of the displayed-source change matrix. -/
def individualMixedAnalyticSourceCoefficient
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :=
  (boundary.individualMixedSourceAnalyticChange D representative offset radius
    Fsys x w₀ hw₀ data c j).changeCoefficientValue
      (boundary.individualNumericAnalyticParameter D representative offset
        radius Fsys x w₀ hw₀ data hA)
      (boundary.individualMixedAnalyticSourceValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j)
      (boundary.individualMixedRemainingSymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j)

/-- Evaluated entries of the canonical-central change matrix. -/
def individualMixedAnalyticCentralCoefficient
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :=
  (boundary.individualMixedCentralAnalyticChange D representative offset radius
    Fsys x w₀ hw₀ data c j).changeCoefficientValue
      (boundary.individualNumericAnalyticParameter D representative offset
        radius Fsys x w₀ hw₀ data hA)
      (boundary.individualMixedAnalyticAfterValue D representative offset radius
        Fsys x w₀ hw₀ data hA c j)
      (boundary.individualMixedRemainingSymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j)

/-! ## Coefficientwise canonical evaluations -/

/-- The canonical source representative chosen by the source adapter is
eventually the support-local mixed real-jet source evaluation. -/
theorem eventually_individualMixedAnalyticCanonicalSourceValue_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (coefficients : boundary.IndividualMixedSourceCoefficientData D
      representative offset radius Fsys x w₀ hw₀ data c j)
    (q : Fin ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.count)) :
    ∀ᶠ n in atTop,
      (boundary.individualMixedSourceAnalyticChange D representative offset
        radius Fsys x w₀ hw₀ data c j).targetValue
          (boundary.individualNumericAnalyticParameter D representative offset
            radius Fsys x w₀ hw₀ data hA)
          (boundary.individualMixedAnalyticSourceValue D representative offset
            radius Fsys x w₀ hw₀ data hA c j)
          (boundary.individualMixedRemainingSymbolValue D representative offset
            radius Fsys x w₀ hw₀ data hA c j) q n =
        realJetCoefficientwiseSourceEvaluation
          (data.orderedClusterQuantitativeStepDerivativeCount
            (paperRankHermiteHigherCount boundary.S) c
            (boundary.preprocessed.fixedSteps c) j)
          (boundary.individualMixedSourceCoefficientValue D representative
            offset radius Fsys x w₀ hw₀ data hA c j coefficients q)
          (data.orderedClusterIndividualPostLogScale c A
            (fun k ↦ data.orderedClusterRawTime
              (boundary.individualQuantitativeSubsequence D representative
                offset radius Fsys x w₀ hw₀ data hA k) c)
            (boundary.preprocessed.fixedSteps c) j)
          (boundary.individualMixedTraceJets D representative offset radius Fsys
            x w₀ hw₀ data hA c j)
          ((boundary.individualMixedTransferData D representative offset radius
            Fsys x w₀ hw₀ data c j).certificate.source q) n := by
  have hraw :=
    (boundary.individualMixedSourceAnalyticChange D representative offset radius
      Fsys x w₀ hw₀ data c j).eventually_targetValue_eq_coefficientwise
        q
        (boundary.individualMixedSupportedCoefficientRepresentative D
          representative offset radius Fsys x w₀ hw₀ data c j
          coefficients q)
        (boundary.individualMixedSupportedCoefficientRepresentative_germ_eq D
          representative offset radius Fsys x w₀ hw₀ data c j
          coefficients q)
        (boundary.individualNumericAnalyticParameter D representative offset
          radius Fsys x w₀ hw₀ data hA)
        (boundary.individualNumericAnalyticParameter_tendsto D representative
          offset radius Fsys x w₀ hw₀ data hA)
        (boundary.individualMixedAnalyticSourceValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
  filter_upwards [hraw] with n hn
  rw [hn]
  unfold realJetCoefficientwiseSourceEvaluation
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  exact boundary.nestedSupportedCoefficientValue_eq_individualMixed D
    representative offset radius Fsys x w₀ hw₀ data hA c j coefficients
    q e n

/-- The canonical central representative chosen by the central adapter is
eventually the support-local mixed central initial evaluation. -/
theorem eventually_individualMixedAnalyticCanonicalCentralValue_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (coefficients : boundary.IndividualMixedSourceCoefficientData D
      representative offset radius Fsys x w₀ hw₀ data c j)
    (q : Fin ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.count)) :
    ∀ᶠ n in atTop,
      (boundary.individualMixedCentralAnalyticChange D representative offset
        radius Fsys x w₀ hw₀ data c j).sourceValue
          (boundary.individualNumericAnalyticParameter D representative offset
            radius Fsys x w₀ hw₀ data hA)
          (boundary.individualMixedAnalyticAfterValue D representative offset
            radius Fsys x w₀ hw₀ data hA c j)
          (boundary.individualMixedRemainingSymbolValue D representative offset
            radius Fsys x w₀ hw₀ data hA c j) q n =
        realJetCoefficientwiseCentralEvaluation A
          (data.orderedClusterQuantitativeStepDerivativeCount
            (paperRankHermiteHigherCount boundary.S) c
            (boundary.preprocessed.fixedSteps c) j)
          (boundary.individualMixedSourceCoefficientValue D representative
            offset radius Fsys x w₀ hw₀ data hA c j coefficients q)
          (data.orderedClusterIndividualPostLogScale c A
            (fun k ↦ data.orderedClusterRawTime
              (boundary.individualQuantitativeSubsequence D representative
                offset radius Fsys x w₀ hw₀ data hA k) c)
            (boundary.preprocessed.fixedSteps c) j)
          ((boundary.individualMixedTransferData D representative offset radius
            Fsys x w₀ hw₀ data c j).certificate.source q) n := by
  let d := data.orderedClusterPrefixConstantDerivativeCount
    (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  let d₁ := data.orderedClusterQuantitativeStepDerivativeCount
    (paperRankHermiteHigherCount boundary.S) c
    (boundary.preprocessed.fixedSteps c) j
  let P : MvPolynomial (RealJetTransferIndex 0 d₁)
      (IndividualCentralCoefficientRing (RealAnalyticGerm p) d selected) :=
    (boundary.individualMixedTransferData D representative offset radius
      Fsys x w₀ hw₀ data c j).certificate.source q
  let parameter := boundary.individualNumericAnalyticParameter D representative
    offset radius Fsys x w₀ hw₀ data hA
  let outerValue := boundary.individualMixedAnalyticAfterValue D representative
    offset radius Fsys x w₀ hw₀ data hA c j
  let coefficientValue := boundary.individualMixedRemainingSymbolValue D
    representative offset radius Fsys x w₀ hw₀ data hA c j
  let u := data.orderedClusterIndividualPostLogScale c A
    (fun k ↦ data.orderedClusterRawTime
      (boundary.individualQuantitativeSubsequence D representative offset radius
        Fsys x w₀ hw₀ data hA k) c)
    (boundary.preprocessed.fixedSteps c) j
  have hgeneric :=
    eventually_flattenedCentralRepresentativeEvaluation_eq_coefficientwise
      A
      d₁
      P
      ((boundary.individualMixedCentralAnalyticChange D representative offset
        radius Fsys x w₀ hw₀ data c j).sourceRepresentative q)
      (by
        simpa only [P, d₁, d, selected,
          individualMixedCanonicalCentralGenerator,
          IndividualCentralTransferData.centralGenerator,
          individualMixedTransferData,
          RepresentativeClusterSubsequence.orderedClusterQuantitativeStepDerivativeCount]
          using
          (boundary.individualMixedCentralAnalyticChange D representative offset
            radius Fsys x w₀ hw₀ data c j).source_germ_eq q)
      (boundary.individualMixedSupportedCoefficientRepresentative D
        representative offset radius Fsys x w₀ hw₀ data c j coefficients
        q)
      (boundary.individualMixedSupportedCoefficientRepresentative_germ_eq D
        representative offset radius Fsys x w₀ hw₀ data c j coefficients
        q)
      parameter
      (boundary.individualNumericAnalyticParameter_tendsto D representative
        offset radius Fsys x w₀ hw₀ data hA)
      outerValue coefficientValue u
      (fun n z ↦ by
        simp only [outerValue, individualMixedAnalyticAfterValue,
          individualCentralPostLogActiveAssignment_central]
        rfl)
  filter_upwards [hgeneric] with n hn
  change MvPolynomial.eval
      (fun z ↦ Sum.elim outerValue coefficientValue z n)
      ((boundary.individualMixedCentralAnalyticChange D representative offset
        radius Fsys x w₀ hw₀ data c j).sourceRepresentative q
          (parameter n)) = _
  have heta : (fun z ↦ Sum.elim outerValue coefficientValue z n) =
      Sum.elim (fun z ↦ outerValue z n)
        (fun z ↦ coefficientValue z n) := by
    funext z
    rcases z with z | z <;> rfl
  rw [← heta] at hn
  rw [hn]
  unfold realJetCoefficientwiseCentralEvaluation
    ClusterAlgebraicReductionCertificate.FullCentralStepDisplayedData.finiteRealJetCoefficientwiseCentralEvaluation
    finiteSupportInitialEvaluation
  apply Finset.sum_congr rfl
  intro e he
  dsimp only [P, d₁, d, selected, parameter, coefficientValue, u]
  congr 1
  exact boundary.nestedSupportedCoefficientValue_eq_individualMixed D
    representative offset radius Fsys x w₀ hw₀ data hA c j coefficients
    q e n

/-! ## Evaluation of transformed displayed-boundary representatives -/

/-- Evaluating the translated flattened image of a flat polynomial at the
literal source assignment recovers its predecessor-boundary evaluation. -/
theorem eval_individualMixedSourceFlattened_eq_before
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (P : data.OrderedClusterPrefixRing ℝ
      (paperRankHermiteHigherCount boundary.S) (c.val + 1)) (n : ℕ) :
    MvPolynomial.eval
        (Sum.elim
          (fun z ↦ boundary.individualMixedAnalyticSourceValue D
            representative offset radius Fsys x w₀ hw₀ data hA c j z n)
          (fun z ↦ boundary.individualMixedRemainingSymbolValue D
            representative offset radius Fsys x w₀ hw₀ data hA c j z n))
        (selectedBlockSourceFlattenedPolynomialHom ℝ
          (data.orderedClusterPrefixConstantDerivativeCount
            (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
          (data.orderedClusterIndividualSelectedBlock c
            (boundary.preprocessed.fixedSteps c) j) P) =
      MvPolynomial.eval
        (fun z ↦ boundary.individualMixedBoundarySymbolValue D representative
          offset radius Fsys x w₀ hw₀ data hA c
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j).castSucc z n) P := by
  let d := data.orderedClusterPrefixConstantDerivativeCount
    (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  let d₁ := data.orderedClusterQuantitativeStepDerivativeCount
    (paperRankHermiteHigherCount boundary.S) c
    (boundary.preprocessed.fixedSteps c) j
  let u := data.orderedClusterIndividualPostLogScale c A
    (fun q ↦ data.orderedClusterRawTime
      (boundary.individualQuantitativeSubsequence D representative offset radius
        Fsys x w₀ hw₀ data hA q) c)
    (boundary.preprocessed.fixedSteps c) j
  let jets := boundary.individualMixedTraceJets D representative offset radius
    Fsys x w₀ hw₀ data hA c j
  let flatValue := boundary.individualMixedBoundarySymbolValue D representative
    offset radius Fsys x w₀ hw₀ data hA c
    (data.orderedClusterIndividualStepIndexEquiv c
      (boundary.preprocessed.fixedSteps c) j).castSucc
  let remaining := boundary.individualMixedRemainingSymbolValue D representative
    offset radius Fsys x w₀ hw₀ data hA c j
  let coefficientSequence :
      IndividualCentralCoefficientRing ℝ d selected →+* (ℕ → ℝ) :=
    MvPolynomial.eval₂Hom
      RepresentativeClusterSubsequence.constantRealSequenceRingHom remaining
  have hcoefficientAt : coefficientEvaluationAt coefficientSequence n =
      MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun z ↦ remaining z n) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [coefficientEvaluationAt_apply, coefficientSequence,
        MvPolynomial.eval₂Hom_C,
        RepresentativeClusterSubsequence.constantRealSequenceRingHom_apply,
        RingHom.id_apply]
    · intro z
      simp only [coefficientEvaluationAt_apply, coefficientSequence,
        MvPolynomial.eval₂Hom_X']
  have hflatten := eval₂Hom_nestedMvPolynomialFlatteningAlgEquiv
    (RingHom.id ℝ)
    (fun z ↦ boundary.individualMixedAnalyticSourceValue D representative
      offset radius Fsys x w₀ hw₀ data hA c j z n)
    (fun z ↦ remaining z n)
    ((IndividualCentralTransferData.sourceTranslation ℝ selected)
      (selectedBlockCurryAlgEquiv ℝ d selected P))
  have htranslation := eval₂Hom_sourceTranslation_symm_preLog
    ℝ selected coefficientSequence u jets
    ((IndividualCentralTransferData.sourceTranslation ℝ selected)
      (selectedBlockCurryAlgEquiv ℝ d selected P)) n
  have hcurry := eval₂Hom_selectedBlockCurryAlgEquiv
    (RingHom.id ℝ) d selected (fun z ↦ flatValue z n) P
  have hactive :=
    boundary.selectedBlockActiveAssignment_individualMixedBoundary_beforeStep D
      representative offset radius Fsys x w₀ hw₀ data hA c j
  have hremaining :=
    boundary.individualMixedRemainingSymbolValue_eq_before D representative
      offset radius Fsys x w₀ hw₀ data hA c j
  change MvPolynomial.eval
      (Sum.elim
        (fun z ↦ boundary.individualMixedAnalyticSourceValue D representative
          offset radius Fsys x w₀ hw₀ data hA c j z n)
        (fun z ↦ remaining z n))
      (nestedMvPolynomialFlatteningAlgEquiv ℝ
        (ClusterOperationSymbol (Fin 1) d₁)
        (boundary.IndividualMixedAnalyticRemainingSymbol D representative offset
          radius Fsys x w₀ hw₀ data c j)
        ((IndividualCentralTransferData.sourceTranslation ℝ selected)
          (selectedBlockCurryAlgEquiv ℝ d selected P))) = _
  calc
    _ = MvPolynomial.eval₂Hom
          (MvPolynomial.eval₂Hom (RingHom.id ℝ)
            (fun z ↦ remaining z n))
          (fun z ↦ boundary.individualMixedAnalyticSourceValue D
            representative offset radius Fsys x w₀ hw₀ data hA c j z n)
          ((IndividualCentralTransferData.sourceTranslation ℝ selected)
            (selectedBlockCurryAlgEquiv ℝ d selected P)) := by
      rw [← MvPolynomial.eval₂_id]
      exact hflatten
    _ = realJetSourceEvaluationHom coefficientSequence u d₁ jets n
          ((IndividualCentralTransferData.sourceTranslation ℝ selected)
            (selectedBlockCurryAlgEquiv ℝ d selected P)) := by
      rw [← hcoefficientAt]
      rfl
    _ = MvPolynomial.eval₂Hom (coefficientEvaluationAt coefficientSequence n)
          (fun z ↦ individualCentralPreLogActiveAssignment u d₁ jets z n)
          (selectedBlockCurryAlgEquiv ℝ d selected P) := by
      simpa only [AlgEquiv.symm_apply_apply] using htranslation.symm
    _ = MvPolynomial.eval
          (fun z ↦ flatValue z n) P := by
      rw [hcoefficientAt]
      have hactiveN :
          (fun z ↦ individualCentralPreLogActiveAssignment u d₁ jets z n) =
            fun z ↦ selectedBlockActiveAssignment d selected flatValue z n := by
        funext z
        exact (congrFun (congrFun hactive z) n).symm
      rw [hactiveN]
      have hremainingN : (fun z ↦ remaining z n) =
          fun z ↦ selectedBlockCoefficientAssignment d selected flatValue z n := by
        funext z
        exact congrFun (congrFun hremaining z) n
      rw [hremainingN]
      rw [← MvPolynomial.eval₂_id]
      exact hcurry.symm

/-- Evaluating the flattened image of a flat polynomial at the exact
post-log assignment recovers its successor-boundary evaluation. -/
theorem eval_individualMixedFlattened_eq_after
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (P : data.OrderedClusterPrefixRing ℝ
      (paperRankHermiteHigherCount boundary.S) (c.val + 1)) (n : ℕ) :
    MvPolynomial.eval
        (Sum.elim
          (fun z ↦ boundary.individualMixedAnalyticAfterValue D representative
            offset radius Fsys x w₀ hw₀ data hA c j z n)
          (fun z ↦ boundary.individualMixedRemainingSymbolValue D
            representative offset radius Fsys x w₀ hw₀ data hA c j z n))
        (selectedBlockFlattenedPolynomialHom ℝ
          (data.orderedClusterPrefixConstantDerivativeCount
            (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1))
          (data.orderedClusterIndividualSelectedBlock c
            (boundary.preprocessed.fixedSteps c) j) P) =
      MvPolynomial.eval
        (fun z ↦ boundary.individualMixedBoundarySymbolValue D representative
          offset radius Fsys x w₀ hw₀ data hA c
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j).succ z n) P := by
  let d := data.orderedClusterPrefixConstantDerivativeCount
    (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  let flatValue := boundary.individualMixedBoundarySymbolValue D representative
    offset radius Fsys x w₀ hw₀ data hA c
    (data.orderedClusterIndividualStepIndexEquiv c
      (boundary.preprocessed.fixedSteps c) j).succ
  have heval := eval_selectedBlockFlattenedPolynomialHom d selected
    (fun z ↦ flatValue z n) P
  have hactive :=
    boundary.selectedBlockActiveAssignment_individualMixedBoundary_afterStep D
      representative offset radius Fsys x w₀ hw₀ data hA c j
  have hactiveN :
      selectedBlockActiveAssignment d selected (fun z ↦ flatValue z n) =
        fun z ↦ boundary.individualMixedAnalyticAfterValue D representative
          offset radius Fsys x w₀ hw₀ data hA c j z n := by
    funext z
    exact congrFun (congrFun hactive z) n
  have hremainingN :
      selectedBlockCoefficientAssignment d selected (fun z ↦ flatValue z n) =
        fun z ↦ boundary.individualMixedRemainingSymbolValue D representative
          offset radius Fsys x w₀ hw₀ data hA c j z n := by
    rfl
  rw [hactiveN, hremainingN] at heval
  exact heval

/-- The displayed-source representatives used by the step adapter evaluate
eventually as the canonical numeric predecessor family. -/
theorem eventually_individualMixedAnalyticBeforeValue_eq_numeric
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    ∀ᶠ n in atTop, ∀ k,
      boundary.individualMixedAnalyticBeforeValue D representative offset radius
          Fsys x w₀ hw₀ data hA c j k n =
        (boundary.individualMixedNumericBoundaryCompatibility D representative
          offset radius Fsys x w₀ hw₀ data hA c).beforeValue
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j) k n := by
  let step := data.orderedClusterIndividualStepIndexEquiv c
    (boundary.preprocessed.fixedSteps c) j
  let d := data.orderedClusterPrefixConstantDerivativeCount
    (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  let displayed := (boundary.individualNumericDisplayed D representative offset
    radius Fsys x w₀ hw₀ data c).displayed step
  let analytic := boundary.individualMixedAnalyticBoundaryData D representative
    offset radius Fsys x w₀ hw₀ data hA c
  let boundaryChange := analytic.beforeBoundaryChange step
  let change := boundary.individualMixedSourceAnalyticChange D representative
    offset radius Fsys x w₀ hw₀ data c j
  let parameter := boundary.individualNumericAnalyticParameter D representative
    offset radius Fsys x w₀ hw₀ data hA
  have hparameter := boundary.individualNumericAnalyticParameter_tendsto D
    representative offset radius Fsys x w₀ hw₀ data hA
  have hrepresentative : ∀ᶠ n in atTop, ∀ k,
      change.sourceRepresentative k (parameter n) =
        selectedBlockSourceFlattenedPolynomialHom ℝ d selected
          (boundaryChange.targetRepresentative k (parameter n)) := by
    apply Filter.eventually_all.mpr
    intro k
    have htransformed :=
      analyticPolynomialGermHom_selectedBlockSourceFlattened_of d selected
        (boundaryChange.target_germ_eq k)
    have hpolynomial :
        selectedBlockSourceFlattenedPolynomialHom (RealAnalyticGerm p) d
            selected
            (IndividualCentralTransferData.DisplayedData.beforeGenerator
              (RealAnalyticGerm p) displayed k) =
          nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
            (boundary.IndividualMixedAnalyticActiveSymbol D representative offset
              radius Fsys x w₀ hw₀ data c j)
            (boundary.IndividualMixedAnalyticRemainingSymbol D representative
              offset radius Fsys x w₀ hw₀ data c j)
            (displayed.source.generator k) := by
      exact selectedBlockSourceFlattenedPolynomialHom_beforeGenerator displayed k
    exact hparameter.eventually
      (analyticPolynomialRepresentatives_eventually_eq
        (0 : RestrictedBoxSpace p) (change.source_germ_eq k) htransformed
        hpolynomial.symm)
  filter_upwards [hrepresentative] with n hn
  intro k
  change MvPolynomial.eval
      (fun z ↦ Sum.elim
        (boundary.individualMixedAnalyticSourceValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j) z n)
      (change.sourceRepresentative k (parameter n)) = _
  rw [hn k]
  have heta : (fun z ↦ Sum.elim
        (boundary.individualMixedAnalyticSourceValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j) z n) =
      Sum.elim
        (fun z ↦ boundary.individualMixedAnalyticSourceValue D representative
          offset radius Fsys x w₀ hw₀ data hA c j z n)
        (fun z ↦ boundary.individualMixedRemainingSymbolValue D representative
          offset radius Fsys x w₀ hw₀ data hA c j z n) := by
    funext z
    rcases z with z | z <;> rfl
  rw [heta]
  rw [boundary.eval_individualMixedSourceFlattened_eq_before D representative
    offset radius Fsys x w₀ hw₀ data hA c j
    (boundaryChange.targetRepresentative k (parameter n)) n] <;> rfl

/-- The displayed-central representatives used by the step adapter evaluate
eventually as the canonical numeric successor family. -/
theorem eventually_individualMixedAnalyticAfterValue_eq_numeric
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    ∀ᶠ n in atTop, ∀ b,
      boundary.individualMixedAnalyticAfterGeneratorValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j b n =
        (boundary.individualMixedNumericBoundaryCompatibility D representative
          offset radius Fsys x w₀ hw₀ data hA c).afterValue
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j) b n := by
  let step := data.orderedClusterIndividualStepIndexEquiv c
    (boundary.preprocessed.fixedSteps c) j
  let d := data.orderedClusterPrefixConstantDerivativeCount
    (paperRankHermiteHigherCount boundary.S + 1) (c.val + 1)
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  let displayed := (boundary.individualNumericDisplayed D representative offset
    radius Fsys x w₀ hw₀ data c).displayed step
  let analytic := boundary.individualMixedAnalyticBoundaryData D representative
    offset radius Fsys x w₀ hw₀ data hA c
  let boundaryChange := analytic.afterBoundaryChange step
  let change := boundary.individualMixedCentralAnalyticChange D representative
    offset radius Fsys x w₀ hw₀ data c j
  let parameter := boundary.individualNumericAnalyticParameter D representative
    offset radius Fsys x w₀ hw₀ data hA
  have hparameter := boundary.individualNumericAnalyticParameter_tendsto D
    representative offset radius Fsys x w₀ hw₀ data hA
  have hrepresentative : ∀ᶠ n in atTop, ∀ b,
      change.targetRepresentative b (parameter n) =
        selectedBlockFlattenedPolynomialHom ℝ d selected
          (boundaryChange.sourceRepresentative b (parameter n)) := by
    apply Filter.eventually_all.mpr
    intro b
    have htransformed := analyticPolynomialGermHom_selectedBlockFlattened_of
      d selected (boundaryChange.source_germ_eq b)
    have hpolynomial :
        selectedBlockFlattenedPolynomialHom (RealAnalyticGerm p) d selected
            (IndividualCentralTransferData.DisplayedData.afterGenerator
              (RealAnalyticGerm p) displayed b) =
          nestedMvPolynomialFlatteningAlgEquiv (RealAnalyticGerm p)
            (boundary.IndividualMixedAnalyticActiveSymbol D representative offset
              radius Fsys x w₀ hw₀ data c j)
            (boundary.IndividualMixedAnalyticRemainingSymbol D representative
              offset radius Fsys x w₀ hw₀ data c j)
            (boundary.individualMixedDisplayedCentralGenerator D representative
              offset radius Fsys x w₀ hw₀ data c j b) := by
      exact selectedBlockFlattenedPolynomialHom_afterGenerator displayed b
    exact hparameter.eventually
      (analyticPolynomialRepresentatives_eventually_eq
        (0 : RestrictedBoxSpace p) (change.target_germ_eq b) htransformed
        hpolynomial.symm)
  filter_upwards [hrepresentative] with n hn
  intro b
  change MvPolynomial.eval
      (fun z ↦ Sum.elim
        (boundary.individualMixedAnalyticAfterValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j) z n)
      (change.targetRepresentative b (parameter n)) = _
  rw [hn b]
  have heta : (fun z ↦ Sum.elim
        (boundary.individualMixedAnalyticAfterValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j) z n) =
      Sum.elim
        (fun z ↦ boundary.individualMixedAnalyticAfterValue D representative
          offset radius Fsys x w₀ hw₀ data hA c j z n)
        (fun z ↦ boundary.individualMixedRemainingSymbolValue D representative
          offset radius Fsys x w₀ hw₀ data hA c j z n) := by
    funext z
    rcases z with z | z <;> rfl
  rw [heta]
  rw [boundary.eval_individualMixedFlattened_eq_after D representative offset
    radius Fsys x w₀ hw₀ data hA c j
    (boundaryChange.sourceRepresentative b (parameter n)) n] <;> rfl

/-! ## The two displayed-step identities -/

/-- The source analytic adapter supplies the exact numeric identity required
by one mixed individual step. -/
theorem eventually_individualMixedAnalyticSourceIdentity
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (coefficients : boundary.IndividualMixedSourceCoefficientData D
      representative offset radius Fsys x w₀ hw₀ data c j) :
    ∀ᶠ n in atTop, ∀ q,
      realJetCoefficientwiseSourceEvaluation
          (data.orderedClusterQuantitativeStepDerivativeCount
            (paperRankHermiteHigherCount boundary.S) c
            (boundary.preprocessed.fixedSteps c) j)
          (boundary.individualMixedSourceCoefficientValue D representative
            offset radius Fsys x w₀ hw₀ data hA c j coefficients q)
          (data.orderedClusterIndividualPostLogScale c A
            (fun k ↦ data.orderedClusterRawTime
              (boundary.individualQuantitativeSubsequence D representative
                offset radius Fsys x w₀ hw₀ data hA k) c)
            (boundary.preprocessed.fixedSteps c) j)
          (boundary.individualMixedTraceJets D representative offset radius Fsys
            x w₀ hw₀ data hA c j)
          ((boundary.individualMixedTransferData D representative offset radius
            Fsys x w₀ hw₀ data c j).certificate.source q) n =
        ∑ k, boundary.individualMixedAnalyticSourceCoefficient D
            representative offset radius Fsys x w₀ hw₀ data hA c j q k n *
          (boundary.individualMixedNumericBoundaryCompatibility D representative
            offset radius Fsys x w₀ hw₀ data hA c).beforeValue
            (data.orderedClusterIndividualStepIndexEquiv c
              (boundary.preprocessed.fixedSteps c) j) k n := by
  have hchange :=
    (boundary.individualMixedSourceAnalyticChange D representative offset radius
      Fsys x w₀ hw₀ data c j).eventually_targetValue_eq_sum
        (boundary.individualNumericAnalyticParameter D representative offset
          radius Fsys x w₀ hw₀ data hA)
        (boundary.individualNumericAnalyticParameter_tendsto D representative
          offset radius Fsys x w₀ hw₀ data hA)
        (boundary.individualMixedAnalyticSourceValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
  have hcanonical : ∀ᶠ n in atTop, ∀ q,
      (boundary.individualMixedSourceAnalyticChange D representative offset
        radius Fsys x w₀ hw₀ data c j).targetValue
          (boundary.individualNumericAnalyticParameter D representative offset
            radius Fsys x w₀ hw₀ data hA)
          (boundary.individualMixedAnalyticSourceValue D representative offset
            radius Fsys x w₀ hw₀ data hA c j)
          (boundary.individualMixedRemainingSymbolValue D representative offset
            radius Fsys x w₀ hw₀ data hA c j) q n =
        realJetCoefficientwiseSourceEvaluation
          (data.orderedClusterQuantitativeStepDerivativeCount
            (paperRankHermiteHigherCount boundary.S) c
            (boundary.preprocessed.fixedSteps c) j)
          (boundary.individualMixedSourceCoefficientValue D representative
            offset radius Fsys x w₀ hw₀ data hA c j coefficients q)
          (data.orderedClusterIndividualPostLogScale c A
            (fun k ↦ data.orderedClusterRawTime
              (boundary.individualQuantitativeSubsequence D representative
                offset radius Fsys x w₀ hw₀ data hA k) c)
            (boundary.preprocessed.fixedSteps c) j)
          (boundary.individualMixedTraceJets D representative offset radius Fsys
            x w₀ hw₀ data hA c j)
          ((boundary.individualMixedTransferData D representative offset radius
            Fsys x w₀ hw₀ data c j).certificate.source q) n := by
    apply Filter.eventually_all.mpr
    intro q
    exact boundary.eventually_individualMixedAnalyticCanonicalSourceValue_eq D
      representative offset radius Fsys x w₀ hw₀ data hA c j coefficients q
  have hbefore :=
    boundary.eventually_individualMixedAnalyticBeforeValue_eq_numeric D
      representative offset radius Fsys x w₀ hw₀ data hA c j
  filter_upwards [hchange, hcanonical, hbefore] with n hn hcanon hbeforeN
  intro q
  rw [← hcanon q]
  rw [hn q]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [show
    (boundary.individualMixedSourceAnalyticChange D representative offset radius
      Fsys x w₀ hw₀ data c j).changeCoefficientValue
        (boundary.individualNumericAnalyticParameter D representative offset
          radius Fsys x w₀ hw₀ data hA)
        (boundary.individualMixedAnalyticSourceValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j) q k n =
      boundary.individualMixedAnalyticSourceCoefficient D representative offset
        radius Fsys x w₀ hw₀ data hA c j q k n by rfl]
  rw [show
    (boundary.individualMixedSourceAnalyticChange D representative offset radius
      Fsys x w₀ hw₀ data c j).sourceValue
        (boundary.individualNumericAnalyticParameter D representative offset
          radius Fsys x w₀ hw₀ data hA)
        (boundary.individualMixedAnalyticSourceValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j) k n =
      boundary.individualMixedAnalyticBeforeValue D representative offset radius
        Fsys x w₀ hw₀ data hA c j k n by rfl]
  rw [hbeforeN k]

/-- The central analytic adapter supplies the exact numeric identity required
by one mixed individual step. -/
theorem eventually_individualMixedAnalyticCentralIdentity
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (coefficients : boundary.IndividualMixedSourceCoefficientData D
      representative offset radius Fsys x w₀ hw₀ data c j) :
    ∀ᶠ n in atTop, ∀ b,
      (boundary.individualMixedNumericBoundaryCompatibility D representative
          offset radius Fsys x w₀ hw₀ data hA c).afterValue
          (data.orderedClusterIndividualStepIndexEquiv c
            (boundary.preprocessed.fixedSteps c) j) b n =
        ∑ q, boundary.individualMixedAnalyticCentralCoefficient D
            representative offset radius Fsys x w₀ hw₀ data hA c j b q n *
          realJetCoefficientwiseCentralEvaluation A
            (data.orderedClusterQuantitativeStepDerivativeCount
              (paperRankHermiteHigherCount boundary.S) c
              (boundary.preprocessed.fixedSteps c) j)
            (boundary.individualMixedSourceCoefficientValue D representative
              offset radius Fsys x w₀ hw₀ data hA c j coefficients q)
            (data.orderedClusterIndividualPostLogScale c A
              (fun k ↦ data.orderedClusterRawTime
                (boundary.individualQuantitativeSubsequence D representative
                  offset radius Fsys x w₀ hw₀ data hA k) c)
              (boundary.preprocessed.fixedSteps c) j)
            ((boundary.individualMixedTransferData D representative offset radius
              Fsys x w₀ hw₀ data c j).certificate.source q) n := by
  have hchange :=
    (boundary.individualMixedCentralAnalyticChange D representative offset radius
      Fsys x w₀ hw₀ data c j).eventually_targetValue_eq_sum
        (boundary.individualNumericAnalyticParameter D representative offset
          radius Fsys x w₀ hw₀ data hA)
        (boundary.individualNumericAnalyticParameter_tendsto D representative
          offset radius Fsys x w₀ hw₀ data hA)
        (boundary.individualMixedAnalyticAfterValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
  have hcanonical : ∀ᶠ n in atTop, ∀ q,
      (boundary.individualMixedCentralAnalyticChange D representative offset
        radius Fsys x w₀ hw₀ data c j).sourceValue
          (boundary.individualNumericAnalyticParameter D representative offset
            radius Fsys x w₀ hw₀ data hA)
          (boundary.individualMixedAnalyticAfterValue D representative offset
            radius Fsys x w₀ hw₀ data hA c j)
          (boundary.individualMixedRemainingSymbolValue D representative offset
            radius Fsys x w₀ hw₀ data hA c j) q n =
        realJetCoefficientwiseCentralEvaluation A
          (data.orderedClusterQuantitativeStepDerivativeCount
            (paperRankHermiteHigherCount boundary.S) c
            (boundary.preprocessed.fixedSteps c) j)
          (boundary.individualMixedSourceCoefficientValue D representative
            offset radius Fsys x w₀ hw₀ data hA c j coefficients q)
          (data.orderedClusterIndividualPostLogScale c A
            (fun k ↦ data.orderedClusterRawTime
              (boundary.individualQuantitativeSubsequence D representative
                offset radius Fsys x w₀ hw₀ data hA k) c)
            (boundary.preprocessed.fixedSteps c) j)
          ((boundary.individualMixedTransferData D representative offset radius
            Fsys x w₀ hw₀ data c j).certificate.source q) n := by
    apply Filter.eventually_all.mpr
    intro q
    exact boundary.eventually_individualMixedAnalyticCanonicalCentralValue_eq D
      representative offset radius Fsys x w₀ hw₀ data hA c j coefficients q
  have hafter :=
    boundary.eventually_individualMixedAnalyticAfterValue_eq_numeric D
      representative offset radius Fsys x w₀ hw₀ data hA c j
  filter_upwards [hchange, hcanonical, hafter] with n hn hcanon hafterN
  intro b
  rw [← hafterN b]
  rw [show boundary.individualMixedAnalyticAfterGeneratorValue D representative
      offset radius Fsys x w₀ hw₀ data hA c j b n =
    (boundary.individualMixedCentralAnalyticChange D representative offset radius
      Fsys x w₀ hw₀ data c j).targetValue
        (boundary.individualNumericAnalyticParameter D representative offset
          radius Fsys x w₀ hw₀ data hA)
        (boundary.individualMixedAnalyticAfterValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j) b n by rfl]
  rw [hn b]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [show
    (boundary.individualMixedCentralAnalyticChange D representative offset radius
      Fsys x w₀ hw₀ data c j).changeCoefficientValue
        (boundary.individualNumericAnalyticParameter D representative offset
          radius Fsys x w₀ hw₀ data hA)
        (boundary.individualMixedAnalyticAfterValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j)
        (boundary.individualMixedRemainingSymbolValue D representative offset
          radius Fsys x w₀ hw₀ data hA c j) b q n =
      boundary.individualMixedAnalyticCentralCoefficient D representative offset
        radius Fsys x w₀ hw₀ data hA c j b q n by rfl]
  rw [hcanon q]

/-! ## Polynomial bounds for the analytic matrices -/

/-- The exact selected predecessor assignment is bounded by the predecessor
boundary scale. -/
theorem individualMixedPreLogActiveValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (z : boundary.IndividualMixedAnalyticActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c j) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.castSucc)
      (individualCentralPreLogActiveAssignment
        (data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA q) c)
          (boundary.preprocessed.fixedSteps c) j)
        (data.orderedClusterQuantitativeStepDerivativeCount
          (paperRankHermiteHigherCount boundary.S) c
          (boundary.preprocessed.fixedSteps c) j)
        (boundary.individualMixedTraceJets D representative offset radius Fsys x
          w₀ hw₀ data hA c j) z) := by
  let step := data.orderedClusterIndividualStepIndexEquiv c
    (boundary.preprocessed.fixedSteps c) j
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  have hbound := boundary.individualMixedActiveValue_hasPolynomialUpperBound D
    representative offset radius Fsys x w₀ hw₀ data hA c step.castSucc
    selected z
  have hactive :=
    boundary.selectedBlockActiveAssignment_individualMixedBoundary_beforeStep D
      representative offset radius Fsys x w₀ hw₀ data hA c j
  apply hbound.congr
  intro n
  simpa only [individualNumericBoundaryScale,
    RepresentativeClusterSubsequence.orderedClusterIndividualBoundaryScale,
    Fin.val_castSucc,
    RepresentativeClusterSubsequence.orderedClusterIndividualStepIndexEquiv_apply_val]
    using (congrFun (congrFun hactive z) n).symm

/-- The literal source assignment differs from the selected predecessor only
by adding one to its free representative coordinate, hence has the same
polynomial upper bound. -/
theorem individualMixedAnalyticSourceValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (z : boundary.IndividualMixedAnalyticActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c j) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.castSucc)
      (boundary.individualMixedAnalyticSourceValue D representative offset radius
        Fsys x w₀ hw₀ data hA c j z) := by
  let scale := data.orderedClusterBalancingPrefixScale A
    (boundary.individualQuantitativeSubsequence D representative offset radius
      Fsys x w₀ hw₀ data hA) c
    (boundary.preprocessed.fixedSteps c) j.castSucc
  have hscale : ∀ᶠ n in atTop, 1 ≤ scale n :=
    Filter.Eventually.of_forall fun n ↦ one_le_two.trans
      (two_le_clusterBalancingPrefixScale A
        (fun q ↦ data.orderedClusterRawTime
          (boundary.individualQuantitativeSubsequence D representative offset
            radius Fsys x w₀ hw₀ data hA q) c)
        (boundary.preprocessed.fixedSteps c) j.castSucc n)
  rcases z with i | z
  · fin_cases i
    apply ((boundary.individualMixedPreLogActiveValue_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c j
      (Sum.inl 0)).add hscale
        (HasPolynomialUpperBound.one atTop scale)).congr
    intro n
    change Real.exp
        (data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA q) c)
          (boundary.preprocessed.fixedSteps c) j 0 n) =
      E (data.orderedClusterIndividualPostLogScale c A
          (fun q ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA q) c)
          (boundary.preprocessed.fixedSteps c) j 0 n) + 1
    simp only [E]
    ring
  · apply (boundary.individualMixedPreLogActiveValue_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c j
      (Sum.inr z)).congr
    intro n
    rfl

/-- The shared remaining-block assignment also has a predecessor-scale bound,
because it is literally unchanged across the selected decrement. -/
theorem individualMixedRemainingSymbolValue_hasPolynomialUpperBound_before
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (z : boundary.IndividualMixedAnalyticRemainingSymbol D representative offset
      radius Fsys x w₀ hw₀ data c j) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.castSucc)
      (boundary.individualMixedRemainingSymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j z) := by
  have hremaining :=
    boundary.individualMixedRemainingSymbolValue_eq_before D representative
      offset radius Fsys x w₀ hw₀ data hA c j
  rw [hremaining]
  unfold selectedBlockCoefficientAssignment
  simpa only [individualNumericBoundaryScale,
    RepresentativeClusterSubsequence.orderedClusterIndividualBoundaryScale,
    Fin.val_castSucc,
    RepresentativeClusterSubsequence.orderedClusterIndividualStepIndexEquiv_apply_val]
    using boundary.individualMixedBoundarySymbolValue_hasPolynomialUpperBound D
      representative offset radius Fsys x w₀ hw₀ data hA c
      (data.orderedClusterIndividualStepIndexEquiv c
        (boundary.preprocessed.fixedSteps c) j).castSucc _

/-- The exact selected post-log assignment is bounded by the successor
boundary scale. -/
theorem individualMixedAnalyticAfterValue_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (z : boundary.IndividualMixedAnalyticActiveSymbol D representative offset
      radius Fsys x w₀ hw₀ data c j) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (boundary.individualMixedAnalyticAfterValue D representative offset radius
        Fsys x w₀ hw₀ data hA c j z) := by
  let step := data.orderedClusterIndividualStepIndexEquiv c
    (boundary.preprocessed.fixedSteps c) j
  let selected := data.orderedClusterIndividualSelectedBlock c
    (boundary.preprocessed.fixedSteps c) j
  have hbound := boundary.individualMixedActiveValue_hasPolynomialUpperBound D
    representative offset radius Fsys x w₀ hw₀ data hA c step.succ selected z
  have hactive :=
    boundary.selectedBlockActiveAssignment_individualMixedBoundary_afterStep D
      representative offset radius Fsys x w₀ hw₀ data hA c j
  apply hbound.congr
  intro n
  simpa only [individualMixedAnalyticAfterValue, individualNumericBoundaryScale,
    RepresentativeClusterSubsequence.orderedClusterIndividualBoundaryScale,
    Fin.val_succ,
    RepresentativeClusterSubsequence.orderedClusterIndividualStepIndexEquiv_apply_val]
    using (congrFun (congrFun hactive z) n).symm

/-- Analyticity bounds each entry of the displayed-source matrix at the
predecessor boundary scale. -/
theorem individualMixedAnalyticSourceCoefficient_bound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (q : Fin ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.count))
    (k : Fin (((boundary.individualNumericDisplayed D representative offset
      radius Fsys x w₀ hw₀ data c).displayed
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j)).source.count + 1)) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.castSucc)
      (boundary.individualMixedAnalyticSourceCoefficient D representative offset
        radius Fsys x w₀ hw₀ data hA c j q k) := by
  apply (boundary.individualMixedSourceAnalyticChange D representative offset
    radius Fsys x w₀ hw₀ data c j).changeCoefficientValue_hasPolynomialUpperBound
      (boundary.individualNumericAnalyticParameter D representative offset
        radius Fsys x w₀ hw₀ data hA)
      (boundary.individualNumericAnalyticParameter_tendsto D representative
        offset radius Fsys x w₀ hw₀ data hA)
      (boundary.individualMixedAnalyticSourceValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j)
      (boundary.individualMixedRemainingSymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j)
      (Filter.Eventually.of_forall fun n ↦ one_le_two.trans
        (two_le_clusterBalancingPrefixScale A
          (fun r ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA r) c)
          (boundary.preprocessed.fixedSteps c) j.castSucc n))
  · exact boundary.individualMixedAnalyticSourceValue_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c j
  · exact boundary.individualMixedRemainingSymbolValue_hasPolynomialUpperBound_before
      D representative offset radius Fsys x w₀ hw₀ data hA c j

/-- Analyticity bounds each entry of the canonical-central matrix at the
successor boundary scale. -/
theorem individualMixedAnalyticCentralCoefficient_bound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (b : Fin (((boundary.individualNumericDisplayed D representative offset
      radius Fsys x w₀ hw₀ data c).displayed
        (data.orderedClusterIndividualStepIndexEquiv c
          (boundary.preprocessed.fixedSteps c) j)).central.count + 1))
    (q : Fin ((boundary.individualMixedTransferData D representative offset
      radius Fsys x w₀ hw₀ data c j).certificate.count)) :
    HasPolynomialUpperBound atTop
      (data.orderedClusterBalancingPrefixScale A
        (boundary.individualQuantitativeSubsequence D representative offset
          radius Fsys x w₀ hw₀ data hA) c
        (boundary.preprocessed.fixedSteps c) j.succ)
      (boundary.individualMixedAnalyticCentralCoefficient D representative offset
        radius Fsys x w₀ hw₀ data hA c j b q) := by
  apply (boundary.individualMixedCentralAnalyticChange D representative offset
    radius Fsys x w₀ hw₀ data c j).changeCoefficientValue_hasPolynomialUpperBound
      (boundary.individualNumericAnalyticParameter D representative offset
        radius Fsys x w₀ hw₀ data hA)
      (boundary.individualNumericAnalyticParameter_tendsto D representative
        offset radius Fsys x w₀ hw₀ data hA)
      (boundary.individualMixedAnalyticAfterValue D representative offset radius
        Fsys x w₀ hw₀ data hA c j)
      (boundary.individualMixedRemainingSymbolValue D representative offset
        radius Fsys x w₀ hw₀ data hA c j)
      (Filter.Eventually.of_forall fun n ↦ one_le_two.trans
        (two_le_clusterBalancingPrefixScale A
          (fun r ↦ data.orderedClusterRawTime
            (boundary.individualQuantitativeSubsequence D representative offset
              radius Fsys x w₀ hw₀ data hA r) c)
          (boundary.preprocessed.fixedSteps c) j.succ n))
  · exact boundary.individualMixedAnalyticAfterValue_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c j
  · exact boundary.individualMixedRemainingSymbolValue_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c j

/-! ## Canonical step and trace packages -/

/-- Canonical finite analytic data for one mixed individual step. -/
noncomputable def individualMixedFiniteAnalyticStepData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length)
    (coefficients : boundary.IndividualMixedSourceCoefficientData D
      representative offset radius Fsys x w₀ hw₀ data c j) :
    boundary.IndividualMixedFiniteAnalyticStepData D representative offset radius
      Fsys x w₀ hw₀ data hA c j coefficients where
  centralCoefficient :=
    boundary.individualMixedAnalyticCentralCoefficient D representative offset
      radius Fsys x w₀ hw₀ data hA c j
  sourceCoefficient :=
    boundary.individualMixedAnalyticSourceCoefficient D representative offset
      radius Fsys x w₀ hw₀ data hA c j
  central_identity :=
    boundary.eventually_individualMixedAnalyticCentralIdentity D representative
      offset radius Fsys x w₀ hw₀ data hA c j coefficients
  central_coefficient_bound := by
    intro b q
    exact boundary.individualMixedAnalyticCentralCoefficient_bound D
      representative offset radius Fsys x w₀ hw₀ data hA c j b q
  source_identity :=
    boundary.eventually_individualMixedAnalyticSourceIdentity D representative
      offset radius Fsys x w₀ hw₀ data hA c j coefficients
  source_coefficient_bound := by
    intro q k
    exact boundary.individualMixedAnalyticSourceCoefficient_bound D
      representative offset radius Fsys x w₀ hw₀ data hA c j q k

/-- Canonical choice of the common supported source-coefficient family at
one mixed individual step. -/
noncomputable def individualMixedCanonicalSourceCoefficientData
    (c : Fin data.orderedClusterCount)
    (j : Fin (boundary.preprocessed.fixedSteps c).length) :
    boundary.IndividualMixedSourceCoefficientData D representative offset
      radius Fsys x w₀ hw₀ data c j :=
  Classical.choice
    (boundary.nonempty_individualMixedSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c j)

/-- Unconditional finite analytic trace for all mixed individual decrements
in one ordered cluster. -/
noncomputable def individualMixedFiniteAnalyticTraceData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    boundary.IndividualMixedFiniteAnalyticTraceData D representative offset
      radius Fsys x w₀ hw₀ data hA c where
  coefficients := fun j ↦
    boundary.individualMixedCanonicalSourceCoefficientData D representative
      offset radius Fsys x w₀ hw₀ data c j
  step := fun j ↦
    boundary.individualMixedFiniteAnalyticStepData D representative offset radius
      Fsys x w₀ hw₀ data hA c j
      (boundary.individualMixedCanonicalSourceCoefficientData D representative
        offset radius Fsys x w₀ hw₀ data c j)

/-- Existence form of the unconditional canonical mixed individual trace. -/
theorem nonempty_individualMixedFiniteAnalyticTraceData
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    Nonempty
      (boundary.IndividualMixedFiniteAnalyticTraceData D representative offset
        radius Fsys x w₀ hw₀ data hA c) :=
  ⟨boundary.individualMixedFiniteAnalyticTraceData D representative offset
    radius Fsys x w₀ hw₀ data hA c⟩

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
