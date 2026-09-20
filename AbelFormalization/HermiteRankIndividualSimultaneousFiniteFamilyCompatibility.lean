import AbelFormalization.HermiteRankOneClusterBackwardPropagation
import AbelFormalization.HermiteRankPreprocessedSimultaneousQuantitativeBounds

/-!
# Canonical finite-family compatibility at the individual/simultaneous seam

The terminal individual family lives in the flat ordered-prefix ring.  The
first simultaneous source family lives after three algebraic coordinate
changes: currying the active cluster, putting that cluster in the balancing
plan's final order, and translating its free source coordinates.  This file
applies those same changes to the terminal individual family and constructs a
finite analytic change of generators to the first displayed source family.

The two independently chosen analytic representatives are compared as
polynomial-valued germs before evaluation.  The numeric comparison then uses
the literal active/coefficient compatibility already proved in
`HermiteRankIndividualSimultaneousBoundaryCompatibility`.  In particular, no
evaluation homomorphism on the whole ring of moving analytic germs is used.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u v w

/-! ## Two generic polynomial facts used by the seam -/

/-- Evaluating the flattened form of a nested polynomial is the same as first
evaluating its coefficient polynomial and then its outer polynomial. -/
theorem eval₂Hom_nestedMvPolynomialFlatteningAlgEquiv
    {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    {Outer : Type w} {Coeff : Type*}
    (f : R →+* S) (outerValue : Outer → S)
    (coefficientValue : Coeff → S)
    (P : MvPolynomial Outer (MvPolynomial Coeff R)) :
    MvPolynomial.eval₂Hom f (Sum.elim outerValue coefficientValue)
        (nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff P) =
      MvPolynomial.eval₂Hom
        (MvPolynomial.eval₂Hom f coefficientValue) outerValue P := by
  let lhs : MvPolynomial Outer (MvPolynomial Coeff R) →+* S :=
    (MvPolynomial.eval₂Hom f (Sum.elim outerValue coefficientValue)).comp
      (nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff).toRingHom
  let rhs : MvPolynomial Outer (MvPolynomial Coeff R) →+* S :=
    MvPolynomial.eval₂Hom
      (MvPolynomial.eval₂Hom f coefficientValue) outerValue
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro Q
      dsimp only [lhs, rhs]
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      rw [show
          (nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff).toRingHom
              (MvPolynomial.C Q) =
            MvPolynomial.rename Sum.inr Q by
          exact nestedMvPolynomialFlattening_C Q,
        MvPolynomial.eval₂Hom_rename]
      rfl
    · intro z
      have hflatten := nestedMvPolynomialFlattening_map_C
        (R := R) (Outer := Outer) (Coeff := Coeff) (MvPolynomial.X z)
      simp only [MvPolynomial.map_X] at hflatten
      simp [lhs, rhs, hflatten]
  exact DFunLike.congr_fun hhom P

/-- A representative remains a representative after a pair of polynomial
ring homomorphisms which commute with extension of real scalars. -/
theorem analyticPolynomialGermHom_ringHom_of_representative
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {σ : Type v} {τ : Type w} {x : E}
    (germHom : MvPolynomial σ (AnalyticGermAt x) →+*
      MvPolynomial τ (AnalyticGermAt x))
    (realHom : MvPolynomial σ ℝ →+* MvPolynomial τ ℝ)
    (hgerm_C : ∀ r : AnalyticGermAt x,
      germHom (MvPolynomial.C r) = MvPolynomial.C r)
    (hreal_C : ∀ r : ℝ,
      realHom (MvPolynomial.C r) = MvPolynomial.C r)
    (hnatural : ∀ P : MvPolynomial σ ℝ,
      MvPolynomial.map (algebraMap ℝ (AnalyticGermAt x)) (realHom P) =
        germHom (MvPolynomial.map
          (algebraMap ℝ (AnalyticGermAt x)) P))
    {P : MvPolynomial σ (AnalyticGermAt x)}
    {F : E → MvPolynomial σ ℝ}
    (hF : analyticPolynomialGermHom x P =
      (F : Germ (𝓝 x) (MvPolynomial σ ℝ))) :
    analyticPolynomialGermHom x (germHom P) =
      ((fun y ↦ realHom (F y)) : Germ (𝓝 x) (MvPolynomial τ ℝ)) := by
  have hX : ∀ z,
      analyticPolynomialGermHom x (germHom (MvPolynomial.X z)) =
        ((fun _ : E ↦ realHom (MvPolynomial.X z)) :
          Germ (𝓝 x) (MvPolynomial τ ℝ)) := by
    intro z
    have hz := hnatural (MvPolynomial.X z)
    simp only [MvPolynomial.map_X] at hz
    rw [← hz]
    exact analyticPolynomialGermHom_map_algebraMap x
      (realHom (MvPolynomial.X z))
  have hgerm :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (fun z ↦ germHom (MvPolynomial.X z)) = germHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [MvPolynomial.eval₂Hom_C] using (hgerm_C r).symm
    · intro z
      simp
  have hreal :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (fun z ↦ realHom (MvPolynomial.X z)) = realHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [MvPolynomial.eval₂Hom_C] using (hreal_C r).symm
    · intro z
      simp
  have hgeneric := analyticPolynomialGermHom_eval₂Hom_of_representatives
    x (fun z ↦ germHom (MvPolynomial.X z))
      (fun z _ ↦ realHom (MvPolynomial.X z)) hX P F hF
  calc
    analyticPolynomialGermHom x (germHom P) =
        analyticPolynomialGermHom x
          (MvPolynomial.eval₂Hom MvPolynomial.C
            (fun z ↦ germHom (MvPolynomial.X z)) P) := by
      rw [DFunLike.congr_fun hgerm P]
    _ = ((fun y ↦ MvPolynomial.eval₂Hom MvPolynomial.C
          (fun z ↦ realHom (MvPolynomial.X z)) (F y)) :
            Germ (𝓝 x) (MvPolynomial τ ℝ)) := hgeneric
    _ = ((fun y ↦ realHom (F y)) :
          Germ (𝓝 x) (MvPolynomial τ ℝ)) := by
      apply Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall fun y ↦
        DFunLike.congr_fun hreal (F y)

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

noncomputable local instance individualSimultaneousSeamBlockDecidableEq
    (c : Fin data.orderedClusterCount) :
    DecidableEq (data.OrderedClusterPrefixBlock (c.val + 1)) :=
  Classical.decEq _

/-! ## The algebraic family transport -/

/-- The homomorphism which performs the three algebraic coordinate changes
between the terminal individual ring and the first simultaneous source ring. -/
def individualSimultaneousForwardNestedPolynomialHom
    (R : Type*) [CommRing R] (c : Fin data.orderedClusterCount) :
    data.OrderedClusterPrefixRing R
        (paperRankHermiteHigherCount boundary.S) (c.val + 1) →+*
      MvPolynomial
        (boundary.SimultaneousAnalyticActiveSymbol D representative offset
          radius Fsys x w₀ hw₀ data c)
        (data.OrderedClusterPrefixRing R
          (paperRankHermiteHigherCount boundary.S) c.val) :=
  let curry := data.orderedClusterPrefixCurryAlgEquiv R c
    (paperRankHermiteHigherCount boundary.S + 1)
  let reorder := data.orderedClusterFinalOrderAlgEquiv
    (data.OrderedClusterPrefixRing R
      (paperRankHermiteHigherCount boundary.S) c.val)
    (paperRankHermiteHigherCount boundary.S) c
    (boundary.preprocessed.fixedOrder c)
  let translate := simultaneousCentralSourceTranslation
    (data.OrderedClusterPrefixRing R
      (paperRankHermiteHigherCount boundary.S) c.val)
    (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S))
  translate.toRingHom.comp (reorder.toRingHom.comp curry.toRingHom)

/-- Flatten the transported nested polynomial.  This is the polynomial-ring
homomorphism used to compare actual analytic representatives. -/
def individualSimultaneousForwardFlattenedPolynomialHom
    (R : Type*) [CommRing R] (c : Fin data.orderedClusterCount) :
    data.OrderedClusterPrefixRing R
        (paperRankHermiteHigherCount boundary.S) (c.val + 1) →+*
      MvPolynomial
        (boundary.SimultaneousAnalyticActiveSymbol D representative offset
            radius Fsys x w₀ hw₀ data c ⊕
          boundary.SimultaneousAnalyticPrefixSymbol D representative offset
            radius Fsys x w₀ hw₀ data c) R :=
  (nestedMvPolynomialFlatteningAlgEquiv R
      (boundary.SimultaneousAnalyticActiveSymbol D representative offset
        radius Fsys x w₀ hw₀ data c)
      (boundary.SimultaneousAnalyticPrefixSymbol D representative offset
        radius Fsys x w₀ hw₀ data c)).toRingHom.comp
    (boundary.individualSimultaneousForwardNestedPolynomialHom D representative
      offset radius Fsys x w₀ hw₀ data R c)

/-- The forward coordinate change commutes with extension of scalars. -/
theorem map_individualSimultaneousForwardFlattenedPolynomialHom
    {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    (c : Fin data.orderedClusterCount)
    (P : data.OrderedClusterPrefixRing R
      (paperRankHermiteHigherCount boundary.S) (c.val + 1)) :
    MvPolynomial.map f
        (boundary.individualSimultaneousForwardFlattenedPolynomialHom D
          representative offset radius Fsys x w₀ hw₀ data R c P) =
      boundary.individualSimultaneousForwardFlattenedPolynomialHom D
        representative offset radius Fsys x w₀ hw₀ data T c
        (MvPolynomial.map f P) := by
  let lhs : data.OrderedClusterPrefixRing R
        (paperRankHermiteHigherCount boundary.S) (c.val + 1) →+*
      MvPolynomial
        (boundary.SimultaneousAnalyticActiveSymbol D representative offset
            radius Fsys x w₀ hw₀ data c ⊕
          boundary.SimultaneousAnalyticPrefixSymbol D representative offset
            radius Fsys x w₀ hw₀ data c) T :=
    (MvPolynomial.map f).comp
      (boundary.individualSimultaneousForwardFlattenedPolynomialHom D
        representative offset radius Fsys x w₀ hw₀ data R c)
  let rhs : data.OrderedClusterPrefixRing R
        (paperRankHermiteHigherCount boundary.S) (c.val + 1) →+*
      MvPolynomial
        (boundary.SimultaneousAnalyticActiveSymbol D representative offset
            radius Fsys x w₀ hw₀ data c ⊕
          boundary.SimultaneousAnalyticPrefixSymbol D representative offset
            radius Fsys x w₀ hw₀ data c) T :=
    (boundary.individualSimultaneousForwardFlattenedPolynomialHom D
      representative offset radius Fsys x w₀ hw₀ data T c).comp
        (MvPolynomial.map f)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs,
        individualSimultaneousForwardFlattenedPolynomialHom,
        individualSimultaneousForwardNestedPolynomialHom,
        nestedMvPolynomialFlatteningAlgEquiv,
        simultaneousCentralSourceTranslation, polynomialCoordinateTranslation,
        RepresentativeClusterSubsequence.orderedClusterFinalOrderAlgEquiv,
        clusterOperationRenameAlgEquiv,
        RepresentativeClusterSubsequence.orderedClusterPrefixCurryAlgEquiv,
        splitClusterCurryAlgEquiv]
    · intro z
      let split := splitClusterBlockSymbolEquiv
        (Fin (data.orderedCluster c).card)
        (data.OrderedClusterPrefixBlock c.val)
        (fun _ ↦ paperRankHermiteHigherCount boundary.S + 1)
        (data.orderedClusterPrefixConstantDerivativeCount
          (paperRankHermiteHigherCount boundary.S + 1) c.val)
        (data.orderedClusterPrefixOperationEquiv c
          (paperRankHermiteHigherCount boundary.S + 1) z)
      generalize hsplit : split = y
      rcases y with y | y
      · rcases y with i | y
        · simp [lhs, rhs, split,
            individualSimultaneousForwardFlattenedPolynomialHom,
            individualSimultaneousForwardNestedPolynomialHom,
            nestedMvPolynomialFlatteningAlgEquiv,
            simultaneousCentralSourceTranslation,
            polynomialCoordinateTranslation,
            RepresentativeClusterSubsequence.orderedClusterFinalOrderAlgEquiv,
            clusterOperationRenameAlgEquiv,
            RepresentativeClusterSubsequence.orderedClusterPrefixCurryAlgEquiv,
            splitClusterCurryAlgEquiv, hsplit]
        · rcases y with ir | i
          · rcases ir with ⟨i, r⟩
            simp [lhs, rhs, split,
              individualSimultaneousForwardFlattenedPolynomialHom,
              individualSimultaneousForwardNestedPolynomialHom,
              nestedMvPolynomialFlatteningAlgEquiv,
              simultaneousCentralSourceTranslation,
              polynomialCoordinateTranslation,
              RepresentativeClusterSubsequence.orderedClusterFinalOrderAlgEquiv,
              clusterOperationRenameAlgEquiv,
              RepresentativeClusterSubsequence.orderedClusterPrefixCurryAlgEquiv,
              splitClusterCurryAlgEquiv, hsplit]
          · simp [lhs, rhs, split,
              individualSimultaneousForwardFlattenedPolynomialHom,
              individualSimultaneousForwardNestedPolynomialHom,
              nestedMvPolynomialFlatteningAlgEquiv,
              simultaneousCentralSourceTranslation,
              polynomialCoordinateTranslation,
              RepresentativeClusterSubsequence.orderedClusterFinalOrderAlgEquiv,
              clusterOperationRenameAlgEquiv,
              RepresentativeClusterSubsequence.orderedClusterPrefixCurryAlgEquiv,
              splitClusterCurryAlgEquiv, hsplit]
      · simp [lhs, rhs, split,
          individualSimultaneousForwardFlattenedPolynomialHom,
          individualSimultaneousForwardNestedPolynomialHom,
          nestedMvPolynomialFlatteningAlgEquiv,
          simultaneousCentralSourceTranslation, polynomialCoordinateTranslation,
          RepresentativeClusterSubsequence.orderedClusterFinalOrderAlgEquiv,
          clusterOperationRenameAlgEquiv,
          RepresentativeClusterSubsequence.orderedClusterPrefixCurryAlgEquiv,
          splitClusterCurryAlgEquiv, hsplit]
  exact DFunLike.congr_fun hhom P

/-- Pointwise application of the forward coordinate change to an analytic
representative represents the forward-changed analytic-germ polynomial. -/
theorem analyticPolynomialGermHom_individualSimultaneousForward_of
    (c : Fin data.orderedClusterCount)
    {P : data.OrderedClusterPrefixRing (RealAnalyticGerm p)
      (paperRankHermiteHigherCount boundary.S) (c.val + 1)}
    {F : RestrictedBoxSpace p →
      data.OrderedClusterPrefixRing ℝ
        (paperRankHermiteHigherCount boundary.S) (c.val + 1)}
    (hF : analyticPolynomialGermHom (0 : RestrictedBoxSpace p) P =
      (F : Germ (𝓝 (0 : RestrictedBoxSpace p))
        (data.OrderedClusterPrefixRing ℝ
          (paperRankHermiteHigherCount boundary.S) (c.val + 1)))) :
    analyticPolynomialGermHom (0 : RestrictedBoxSpace p)
        (boundary.individualSimultaneousForwardFlattenedPolynomialHom D
          representative offset radius Fsys x w₀ hw₀ data
          (RealAnalyticGerm p) c P) =
      ((fun y ↦
        boundary.individualSimultaneousForwardFlattenedPolynomialHom D
          representative offset radius Fsys x w₀ hw₀ data ℝ c (F y)) :
        Germ (𝓝 (0 : RestrictedBoxSpace p))
          (MvPolynomial
            (boundary.SimultaneousAnalyticActiveSymbol D representative offset
                radius Fsys x w₀ hw₀ data c ⊕
              boundary.SimultaneousAnalyticPrefixSymbol D representative offset
                radius Fsys x w₀ hw₀ data c) ℝ)) := by
  apply analyticPolynomialGermHom_ringHom_of_representative
    (boundary.individualSimultaneousForwardFlattenedPolynomialHom D
      representative offset radius Fsys x w₀ hw₀ data
      (RealAnalyticGerm p) c)
    (boundary.individualSimultaneousForwardFlattenedPolynomialHom D
      representative offset radius Fsys x w₀ hw₀ data ℝ c)
  · intro r
    simp [individualSimultaneousForwardFlattenedPolynomialHom,
      individualSimultaneousForwardNestedPolynomialHom,
      nestedMvPolynomialFlatteningAlgEquiv,
      simultaneousCentralSourceTranslation, polynomialCoordinateTranslation,
      RepresentativeClusterSubsequence.orderedClusterFinalOrderAlgEquiv,
      clusterOperationRenameAlgEquiv,
      RepresentativeClusterSubsequence.orderedClusterPrefixCurryAlgEquiv,
      splitClusterCurryAlgEquiv]
  · intro r
    simp [individualSimultaneousForwardFlattenedPolynomialHom,
      individualSimultaneousForwardNestedPolynomialHom,
      nestedMvPolynomialFlatteningAlgEquiv,
      simultaneousCentralSourceTranslation, polynomialCoordinateTranslation,
      RepresentativeClusterSubsequence.orderedClusterFinalOrderAlgEquiv,
      clusterOperationRenameAlgEquiv,
      RepresentativeClusterSubsequence.orderedClusterPrefixCurryAlgEquiv,
      splitClusterCurryAlgEquiv]
  · intro Q
    exact boundary.map_individualSimultaneousForwardFlattenedPolynomialHom D
      representative offset radius Fsys x w₀ hw₀ data
      (algebraMap ℝ (RealAnalyticGerm p)) c Q
  · exact hF

/-- Apply the forward coordinate change to every generator at the terminal
individual boundary. -/
def individualSimultaneousTransformedTerminalGenerator
    (c : Fin data.orderedClusterCount)
    (b : Fin ((boundary.individualNumericBoundaryFamily D representative offset
      radius Fsys x w₀ hw₀ data c
      (boundary.individualMixedTerminalBoundaryIndex D representative offset
        radius Fsys x w₀ hw₀ data c)).count + 1)) := by
  exact boundary.individualSimultaneousForwardNestedPolynomialHom D
    representative offset radius Fsys x w₀ hw₀ data
    (RealAnalyticGerm p) c
    ((boundary.individualNumericBoundaryFamily D representative offset radius
      Fsys x w₀ hw₀ data c
      (boundary.individualMixedTerminalBoundaryIndex D representative offset
        radius Fsys x w₀ hw₀ data c)).generator b)

/-- The transported terminal family and the first displayed simultaneous
source family generate the same translated reduction input. -/
theorem individualSimultaneousTransformedTerminal_span_eq_firstSource
    (c : Fin data.orderedClusterCount) :
    Ideal.span (Set.range
        (boundary.individualSimultaneousTransformedTerminalGenerator D
          representative offset radius Fsys x w₀ hw₀ data c)) =
      Ideal.span (Set.range
        ((boundary.simultaneousNumericTrace D representative offset radius
          Fsys x w₀ hw₀ data c).simultaneousDisplayed
            (boundary.simultaneousNumericStage D representative offset radius
              Fsys x w₀ hw₀ data c).certificate.firstCentralStepIndex).source.generator) := by
  let terminal := boundary.individualMixedTerminalBoundaryIndex D
    representative offset radius Fsys x w₀ hw₀ data c
  let family := boundary.individualNumericBoundaryFamily D representative
    offset radius Fsys x w₀ hw₀ data c terminal
  let stage := boundary.simultaneousNumericStage D representative offset radius
    Fsys x w₀ hw₀ data c
  let trace := boundary.simultaneousNumericTrace D representative offset radius
    Fsys x w₀ hw₀ data c
  let curry := data.orderedClusterPrefixCurryAlgEquiv
    (RealAnalyticGerm p) c (paperRankHermiteHigherCount boundary.S + 1)
  let reorder := data.orderedClusterFinalOrderAlgEquiv
    (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
      (paperRankHermiteHigherCount boundary.S) c.val)
    (paperRankHermiteHigherCount boundary.S) c
    (boundary.preprocessed.fixedOrder c)
  let translate := simultaneousCentralSourceTranslation
    (data.OrderedClusterPrefixRing (RealAnalyticGerm p)
      (paperRankHermiteHigherCount boundary.S) c.val)
    (terminalTotalDerivativeCount (fun _ :
      Fin (data.orderedCluster c).card ↦
        paperRankHermiteHigherCount boundary.S))
  change Ideal.span (Set.range (fun b ↦
      translate (reorder (curry (family.generator b))))) = _
  calc
    Ideal.span (Set.range (fun b ↦
        translate (reorder (curry (family.generator b))))) =
        (Ideal.span (Set.range (fun b ↦
          reorder (curry (family.generator b))))).map
            translate.toRingHom :=
      span_range_map_eq translate.toRingHom _
    _ = ((Ideal.span (Set.range (fun b ↦
          curry (family.generator b)))).map reorder.toRingHom).map
            translate.toRingHom := by
      exact congrArg (fun J ↦ J.map translate.toRingHom)
        (span_range_map_eq reorder.toRingHom
          (fun b ↦ curry (family.generator b)))
    _ = (((Ideal.span (Set.range family.generator)).map
          curry.toRingHom).map reorder.toRingHom).map
            translate.toRingHom := by
      exact congrArg (fun J ↦
        (J.map reorder.toRingHom).map translate.toRingHom)
          (span_range_map_eq curry.toRingHom family.generator)
    _ = ((stage.preprocessingOutput.map curry.toRingHom).map
          reorder.toRingHom).map translate.toRingHom := by
      rw [family.span_eq]
      change (((data.orderedClusterIndividualIdealBoundary
        (RealAnalyticGerm p) (paperRankHermiteHigherCount boundary.S) c
        (boundary.preprocessed.fixedSteps c) stage.preprocessingInput terminal).map
          curry.toRingHom).map reorder.toRingHom).map translate.toRingHom = _
      rw [trace.individual_terminal_boundary]
    _ = stage.reductionInput.map translate.toRingHom := rfl
    _ = Ideal.span (Set.range
        (trace.simultaneousDisplayed
          stage.certificate.firstCentralStepIndex).source.generator) := by
      symm
      simpa only [trace, stage, translate,
        simultaneousCentralSourceTranslation] using
        trace.simultaneous_first_source_span

/-- Canonical finite analytic change from the transported terminal individual
family to the first displayed simultaneous source family. -/
noncomputable def individualSimultaneousFiniteAnalyticChange
    (c : Fin data.orderedClusterCount) :=
  finiteAnalyticNestedChangeOfGeneratorsDataOfSpan
    (0 : RestrictedBoxSpace p)
    (boundary.individualSimultaneousTransformedTerminalGenerator D
      representative offset radius Fsys x w₀ hw₀ data c)
    ((boundary.simultaneousNumericTrace D representative offset radius Fsys x
      w₀ hw₀ data c).simultaneousDisplayed
        (boundary.simultaneousNumericStage D representative offset radius Fsys
          x w₀ hw₀ data c).certificate.firstCentralStepIndex).source.generator
    (le_of_eq
      (boundary.individualSimultaneousTransformedTerminal_span_eq_firstSource D
        representative offset radius Fsys x w₀ hw₀ data c).symm)

/-! ## Literal evaluation of the coordinate transport -/

/-- The shifted individual analytic parameter and the simultaneous common-tail
parameter are pointwise equal. -/
theorem individualMixedTerminalAnalyticParameterOnSimultaneousTail_eq
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (n : ℕ) :
    (boundary.individualMixedAnalyticBoundaryData D representative offset radius
      Fsys x w₀ hw₀ data hA c).parameter
        (boundary.individualSimultaneousTailShift D representative offset radius
          Fsys x w₀ hw₀ data hA n) =
      boundary.simultaneousQuantitativeAnalyticParameter D representative offset
        radius Fsys x w₀ hw₀ data hA n := by
  change boundary.individualNumericAnalyticParameter D representative offset
      radius Fsys x w₀ hw₀ data hA
        (boundary.individualSimultaneousTailShift D representative offset radius
          Fsys x w₀ hw₀ data hA n) = _
  unfold individualSimultaneousTailShift individualNumericAnalyticParameter
    simultaneousQuantitativeAnalyticParameter simultaneousQuantitativeReindex
  congr 2
  omega

/-- Pulling the final-order assignment back along the final-order symbol
equivalence recovers the literal active part of the flat terminal assignment. -/
theorem individualMixedTerminalFinalActiveValue_comp_finalOrder_eq_active
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    (fun z ↦ boundary.individualMixedTerminalFinalActiveValue D representative
        offset radius Fsys x w₀ hw₀ data hA c
        (clusterOperationSymbolEquiv
          (data.orderedClusterFinalPositionEquiv c
            (boundary.preprocessed.fixedOrder c)).symm
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S))
          (terminalTotalDerivativeCount (fun _ :
            Fin (data.orderedCluster c).card ↦
              paperRankHermiteHigherCount boundary.S))
          (fun _ ↦ rfl) z)) =
      RepresentativeClusterSubsequence.orderedClusterPrefixActiveAssignment
        data c (paperRankHermiteHigherCount boundary.S + 1)
        (boundary.individualMixedTerminalSymbolValueOnSimultaneousTail D
          representative offset radius Fsys x w₀ hw₀ data hA c) := by
  funext z n
  rcases z with i | z
  · simp only [clusterOperationSymbolEquiv_apply_q,
      RepresentativeClusterSubsequence.orderedClusterPrefixActiveAssignment_free,
      individualMixedTerminalFinalActiveValue,
      individualMixedTerminalFinalActiveSymbol]
    rw [boundary.individualMixedTerminalFinalBlock_eq_finalPositionBlock D
      representative offset radius Fsys x w₀ hw₀ data c]
    simp
  · rcases z with ir | i
    · rcases ir with ⟨i, r⟩
      simp only [clusterOperationSymbolEquiv_apply_derivative,
        RepresentativeClusterSubsequence.orderedClusterPrefixActiveAssignment_derivative,
        individualMixedTerminalFinalActiveValue,
        individualMixedTerminalFinalActiveSymbol]
      rw [boundary.individualMixedTerminalFinalBlock_eq_finalPositionBlock D
        representative offset radius Fsys x w₀ hw₀ data c]
      apply congrArg (fun z ↦
        boundary.individualMixedTerminalSymbolValueOnSimultaneousTail D
          representative offset radius Fsys x w₀ hw₀ data hA c z n)
      apply congrArg Sum.inr
      apply congrArg Sum.inl
      apply Sigma.ext
      · simp
      · rfl
    · simp only [clusterOperationSymbolEquiv_apply_time,
        RepresentativeClusterSubsequence.orderedClusterPrefixActiveAssignment_time,
        individualMixedTerminalFinalActiveValue,
        individualMixedTerminalFinalActiveSymbol]
      rw [boundary.individualMixedTerminalFinalBlock_eq_finalPositionBlock D
        representative offset radius Fsys x w₀ hw₀ data c]
      simp

/-- Along the common tail, evaluating the forward-changed version of any
real flat polynomial at the first simultaneous assignment recovers evaluation
of the original polynomial at the terminal individual assignment. -/
theorem eventually_eval_individualSimultaneousForwardFlattened_eq_terminal
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ∀ᶠ n in atTop, ∀ P : data.OrderedClusterPrefixRing ℝ
        (paperRankHermiteHigherCount boundary.S) (c.val + 1),
      MvPolynomial.eval
          (fun z ↦ boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D
            representative offset radius Fsys x w₀ hw₀ data hA c
            (boundary.simultaneousNumericStage D representative offset radius
              Fsys x w₀ hw₀ data c).certificate.firstCentralStepIndex z n)
          (boundary.individualSimultaneousForwardFlattenedPolynomialHom D
            representative offset radius Fsys x w₀ hw₀ data ℝ c P) =
        MvPolynomial.eval
          (fun z ↦
            boundary.individualMixedTerminalSymbolValueOnSimultaneousTail D
              representative offset radius Fsys x w₀ hw₀ data hA c z n) P := by
  let compatibility := boundary.individualSimultaneousBoundaryCompatibility D
    representative offset radius Fsys x w₀ hw₀ data hA c
  filter_upwards [compatibility.coefficient] with n hcoefficient
  intro P
  let r := (boundary.simultaneousNumericStage D representative offset radius
    Fsys x w₀ hw₀ data c).certificate.firstCentralStepIndex
  let terminalValue :=
    boundary.individualMixedTerminalSymbolValueOnSimultaneousTail D
      representative offset radius Fsys x w₀ hw₀ data hA c
  let prefixValue := boundary.simultaneousQuantitativeAnalyticPrefixValue D
    representative offset radius Fsys x w₀ hw₀ data hA c r.val
  let outerValue := boundary.simultaneousQuantitativeAnalyticSourceValue D
    representative offset radius Fsys x w₀ hw₀ data hA c r
  let u := boundary.simultaneousQuantitativePostLogScale D representative offset
    radius Fsys x w₀ hw₀ data hA c r.val
  let d := terminalTotalDerivativeCount (fun _ :
    Fin (data.orderedCluster c).card ↦ paperRankHermiteHigherCount boundary.S)
  let jets := boundary.simultaneousQuantitativeOperationJetSequence D
    representative offset radius Fsys x w₀ hw₀ data hA c r
  let curry := data.orderedClusterPrefixCurryAlgEquiv ℝ c
    (paperRankHermiteHigherCount boundary.S + 1)
  let reorder := data.orderedClusterFinalOrderAlgEquiv
    (data.OrderedClusterPrefixRing ℝ
      (paperRankHermiteHigherCount boundary.S) c.val)
    (paperRankHermiteHigherCount boundary.S) c
    (boundary.preprocessed.fixedOrder c)
  let translate := simultaneousCentralSourceTranslation
    (data.OrderedClusterPrefixRing ℝ
      (paperRankHermiteHigherCount boundary.S) c.val) d
  let coefficientSequence :
      data.OrderedClusterPrefixRing ℝ
          (paperRankHermiteHigherCount boundary.S) c.val →+* (ℕ → ℝ) :=
    MvPolynomial.eval₂Hom
      RepresentativeClusterSubsequence.constantRealSequenceRingHom prefixValue
  have hcoefficientAt : coefficientEvaluationAt coefficientSequence n =
      MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun z ↦ prefixValue z n) := by
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
    (RingHom.id ℝ) (fun z ↦ outerValue z n) (fun z ↦ prefixValue z n)
    (translate (reorder (curry P)))
  have htranslate :=
    eval₂Hom_simultaneousCentralSourceTranslation_symm_preLog
      (data.OrderedClusterPrefixRing ℝ
        (paperRankHermiteHigherCount boundary.S) c.val)
      coefficientSequence u d jets (translate (reorder (curry P))) n
  have hactive :
      ((fun z ↦ simultaneousCentralPreLogActiveAssignment u d jets z n) ∘
        clusterOperationSymbolEquiv
          (data.orderedClusterFinalPositionEquiv c
            (boundary.preprocessed.fixedOrder c)).symm d d
          (fun _ ↦ rfl)) =
        fun z ↦
          RepresentativeClusterSubsequence.orderedClusterPrefixActiveAssignment
            data c (paperRankHermiteHigherCount boundary.S + 1) terminalValue z n := by
    funext z
    change boundary.simultaneousFirstMixedActiveValue D representative offset
        radius Fsys x w₀ hw₀ data hA c
          (clusterOperationSymbolEquiv
            (data.orderedClusterFinalPositionEquiv c
              (boundary.preprocessed.fixedOrder c)).symm d d
            (fun _ ↦ rfl) z) n = _
    rw [← congrFun (congrFun compatibility.active
      (clusterOperationSymbolEquiv
        (data.orderedClusterFinalPositionEquiv c
          (boundary.preprocessed.fixedOrder c)).symm d d
        (fun _ ↦ rfl) z)) n]
    exact congrFun (congrFun
      (boundary.individualMixedTerminalFinalActiveValue_comp_finalOrder_eq_active
        D representative offset radius Fsys x w₀ hw₀ data hA c) z) n
  have hreorder :
      MvPolynomial.eval₂Hom
          (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun z ↦ prefixValue z n))
          (fun z ↦ simultaneousCentralPreLogActiveAssignment u d jets z n)
          (reorder (curry P)) =
        MvPolynomial.eval₂Hom
          (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun z ↦ prefixValue z n))
          (fun z ↦
            RepresentativeClusterSubsequence.orderedClusterPrefixActiveAssignment
              data c (paperRankHermiteHigherCount boundary.S + 1)
              terminalValue z n) (curry P) := by
    change MvPolynomial.eval₂Hom _ _
        (MvPolynomial.rename
          (clusterOperationSymbolEquiv
            (data.orderedClusterFinalPositionEquiv c
              (boundary.preprocessed.fixedOrder c)).symm d d
            (fun _ ↦ rfl)) (curry P)) = _
    rw [MvPolynomial.eval₂Hom_rename]
    rw [hactive]
  have hcurry :=
    RepresentativeClusterSubsequence.eval₂Hom_orderedClusterPrefixCurryAlgEquiv
      (RingHom.id ℝ) data c (paperRankHermiteHigherCount boundary.S + 1)
      (fun z ↦ terminalValue z n) P
  have hforward :
      boundary.individualSimultaneousForwardFlattenedPolynomialHom D
          representative offset radius Fsys x w₀ hw₀ data ℝ c P =
        nestedMvPolynomialFlatteningAlgEquiv ℝ
          (boundary.SimultaneousAnalyticActiveSymbol D representative offset
            radius Fsys x w₀ hw₀ data c)
          (boundary.SimultaneousAnalyticPrefixSymbol D representative offset
            radius Fsys x w₀ hw₀ data c)
          (translate (reorder (curry P))) := by
    rfl
  have hsourceAssignment :
      (fun z ↦
        boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c r z n) =
        Sum.elim (fun z ↦ outerValue z n) (fun z ↦ prefixValue z n) := by
    funext z
    rcases z with z | z <;> rfl
  calc
    MvPolynomial.eval
        (fun z ↦ boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D
          representative offset radius Fsys x w₀ hw₀ data hA c
          (boundary.simultaneousNumericStage D representative offset radius
            Fsys x w₀ hw₀ data c).certificate.firstCentralStepIndex z n)
        (boundary.individualSimultaneousForwardFlattenedPolynomialHom D
          representative offset radius Fsys x w₀ hw₀ data ℝ c P) =
      MvPolynomial.eval₂Hom
        (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun z ↦ prefixValue z n))
        (fun z ↦ outerValue z n) (translate (reorder (curry P))) := by
          rw [hforward]
          rw [hsourceAssignment]
          rw [← MvPolynomial.eval₂_id]
          exact hflatten
    _ = MvPolynomial.eval₂Hom
        (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun z ↦ prefixValue z n))
        (fun z ↦ simultaneousCentralPreLogActiveAssignment u d jets z n)
        (reorder (curry P)) := by
          rw [← hcoefficientAt]
          simpa only [finiteRealJetSourceEvaluationHom,
            simultaneousQuantitativeAnalyticSourceValue,
            finiteRealJetActualAssignment, realCentralTransferActualValue,
            outerValue, u, d, jets, translate, r,
            AlgEquiv.symm_apply_apply] using htranslate.symm
    _ = MvPolynomial.eval₂Hom
        (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun z ↦ prefixValue z n))
        (fun z ↦
          RepresentativeClusterSubsequence.orderedClusterPrefixActiveAssignment
            data c (paperRankHermiteHigherCount boundary.S + 1)
            terminalValue z n) (curry P) := hreorder
    _ = MvPolynomial.eval
        (fun z ↦ terminalValue z n) P := by
          rw [show (fun z ↦ prefixValue z n) = fun z ↦
              RepresentativeClusterSubsequence.orderedClusterPrefixCoefficientAssignment
                data c (paperRankHermiteHigherCount boundary.S + 1)
                terminalValue z n by
            funext z
            exact (hcoefficient z).symm]
          exact hcurry.symm

/-! ## Analytic representative comparisons and the canonical record -/

/-- The source values of the seam adapter are eventually the shifted terminal
individual boundary values. -/
theorem eventually_individualSimultaneousSourceValue_eq_terminalBoundaryValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ∀ᶠ n in atTop, ∀ b,
      (boundary.individualSimultaneousFiniteAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data c).sourceValue
          (boundary.simultaneousQuantitativeAnalyticParameter D representative
            offset radius Fsys x w₀ hw₀ data hA)
          (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
            offset radius Fsys x w₀ hw₀ data hA c
            (boundary.simultaneousNumericStage D representative offset radius
              Fsys x w₀ hw₀ data c).certificate.firstCentralStepIndex)
          (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
            offset radius Fsys x w₀ hw₀ data hA c 0) b n =
        boundary.individualMixedBoundaryValueOnSimultaneousTail D representative
          offset radius Fsys x w₀ hw₀ data hA c
          (boundary.individualMixedTerminalBoundaryIndex D representative offset
            radius Fsys x w₀ hw₀ data c) b n := by
  let terminal := boundary.individualMixedTerminalBoundaryIndex D
    representative offset radius Fsys x w₀ hw₀ data c
  let family := boundary.individualNumericBoundaryFamily D representative
    offset radius Fsys x w₀ hw₀ data c terminal
  let self : FiniteAnalyticChangeOfGeneratorsData
      (0 : RestrictedBoxSpace p) family.generator family.generator :=
    (boundary.individualMixedAnalyticBoundaryData D representative offset radius
      Fsys x w₀ hw₀ data hA c).boundarySelfChange terminal
  let change := boundary.individualSimultaneousFiniteAnalyticChange D
    representative offset radius Fsys x w₀ hw₀ data c
  let parameter := boundary.simultaneousQuantitativeAnalyticParameter D
    representative offset radius Fsys x w₀ hw₀ data hA
  have hparameter := boundary.simultaneousQuantitativeAnalyticParameter_tendsto D
    representative offset radius Fsys x w₀ hw₀ data hA
  have hrepresentative : ∀ᶠ n in atTop, ∀ b,
      change.sourceRepresentative b (parameter n) =
        boundary.individualSimultaneousForwardFlattenedPolynomialHom D
          representative offset radius Fsys x w₀ hw₀ data ℝ c
          (self.sourceRepresentative b (parameter n)) := by
    apply Filter.eventually_all.mpr
    intro b
    have hnear : ∀ᶠ y in 𝓝 (0 : RestrictedBoxSpace p),
        change.sourceRepresentative b y =
          boundary.individualSimultaneousForwardFlattenedPolynomialHom D
            representative offset radius Fsys x w₀ hw₀ data ℝ c
            (self.sourceRepresentative b y) :=
      analyticPolynomialRepresentatives_eventually_eq
        (0 : RestrictedBoxSpace p) (change.source_germ_eq b)
        (boundary.analyticPolynomialGermHom_individualSimultaneousForward_of D
          representative offset radius Fsys x w₀ hw₀ data c
          (self.source_germ_eq b)) rfl
    exact hparameter.eventually hnear
  have hevaluation :=
    boundary.eventually_eval_individualSimultaneousForwardFlattened_eq_terminal
      D representative offset radius Fsys x w₀ hw₀ data hA c
  filter_upwards [hrepresentative, hevaluation] with n hrep heval
  intro b
  change MvPolynomial.eval
      (fun z ↦ boundary.simultaneousQuantitativeAnalyticSourceSymbolValue D
        representative offset radius Fsys x w₀ hw₀ data hA c
        (boundary.simultaneousNumericStage D representative offset radius Fsys x
          w₀ hw₀ data c).certificate.firstCentralStepIndex z n)
      (change.sourceRepresentative b (parameter n)) = _
  rw [hrep b]
  rw [heval (self.sourceRepresentative b (parameter n))]
  change MvPolynomial.eval
      (fun z ↦ boundary.individualMixedTerminalSymbolValueOnSimultaneousTail D
        representative offset radius Fsys x w₀ hw₀ data hA c z n)
      (self.sourceRepresentative b
        (boundary.simultaneousQuantitativeAnalyticParameter D representative
          offset radius Fsys x w₀ hw₀ data hA n)) = _
  rw [← boundary.individualMixedTerminalAnalyticParameterOnSimultaneousTail_eq D
    representative offset radius Fsys x w₀ hw₀ data hA c n]
  rfl

/-- The target values of the seam adapter are eventually the canonical first
simultaneous `beforeValue`. -/
theorem eventually_individualSimultaneousTargetValue_eq_firstBeforeValue
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ∀ᶠ n in atTop, ∀ k,
      (boundary.individualSimultaneousFiniteAnalyticChange D representative
        offset radius Fsys x w₀ hw₀ data c).targetValue
          (boundary.simultaneousQuantitativeAnalyticParameter D representative
            offset radius Fsys x w₀ hw₀ data hA)
          (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
            offset radius Fsys x w₀ hw₀ data hA c
            (boundary.simultaneousNumericStage D representative offset radius
              Fsys x w₀ hw₀ data c).certificate.firstCentralStepIndex)
          (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
            offset radius Fsys x w₀ hw₀ data hA c 0) k n =
        ((boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
          representative offset radius Fsys x w₀ hw₀ data hA c).change
            (boundary.simultaneousNumericStage D representative offset radius
              Fsys x w₀ hw₀ data c).certificate.firstCentralStepIndex).beforeValue
          k n := by
  let r := (boundary.simultaneousNumericStage D representative offset radius
    Fsys x w₀ hw₀ data c).certificate.firstCentralStepIndex
  let change := boundary.individualSimultaneousFiniteAnalyticChange D
    representative offset radius Fsys x w₀ hw₀ data c
  let sourceChange := boundary.simultaneousQuantitativeSourceAnalyticChange D
    representative offset radius Fsys x w₀ hw₀ data c r
  let parameter := boundary.simultaneousQuantitativeAnalyticParameter D
    representative offset radius Fsys x w₀ hw₀ data hA
  have hparameter := boundary.simultaneousQuantitativeAnalyticParameter_tendsto D
    representative offset radius Fsys x w₀ hw₀ data hA
  have hrepresentative : ∀ᶠ n in atTop, ∀ k,
      change.targetRepresentative k (parameter n) =
        sourceChange.sourceRepresentative k (parameter n) := by
    apply Filter.eventually_all.mpr
    intro k
    exact hparameter.eventually
      (analyticPolynomialRepresentatives_eventually_eq
        (0 : RestrictedBoxSpace p) (change.target_germ_eq k)
        (sourceChange.source_germ_eq k) rfl)
  filter_upwards [hrepresentative] with n hn
  intro k
  change MvPolynomial.eval _ (change.targetRepresentative k (parameter n)) = _
  rw [hn k]
  rfl

/-- Numeric entries of the canonical seam change matrix. -/
def individualSimultaneousFiniteFamilyCoefficient
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :=
  (boundary.individualSimultaneousFiniteAnalyticChange D representative offset
    radius Fsys x w₀ hw₀ data c).changeCoefficientValue
      (boundary.simultaneousQuantitativeAnalyticParameter D representative
        offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
        offset radius Fsys x w₀ hw₀ data hA c
        (boundary.simultaneousNumericStage D representative offset radius Fsys x
          w₀ hw₀ data c).certificate.firstCentralStepIndex)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c 0)

/-- Every canonical seam coefficient is polynomially bounded by the terminal
individual scale. -/
theorem individualSimultaneousFiniteFamilyCoefficient_hasPolynomialUpperBound
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) (k b) :
    HasPolynomialUpperBound atTop
      (boundary.individualMixedBoundaryScaleOnSimultaneousTail D representative
        offset radius Fsys x w₀ hw₀ data hA c
        (boundary.individualMixedTerminalBoundaryIndex D representative offset
          radius Fsys x w₀ hw₀ data c))
      (boundary.individualSimultaneousFiniteFamilyCoefficient D representative
        offset radius Fsys x w₀ hw₀ data hA c k b) := by
  let r := (boundary.simultaneousNumericStage D representative offset radius
    Fsys x w₀ hw₀ data c).certificate.firstCentralStepIndex
  let change := boundary.individualSimultaneousFiniteAnalyticChange D
    representative offset radius Fsys x w₀ hw₀ data c
  have hbound := change.changeCoefficientValue_hasPolynomialUpperBound
    (boundary.simultaneousQuantitativeAnalyticParameter D representative offset
      radius Fsys x w₀ hw₀ data hA)
    (boundary.simultaneousQuantitativeAnalyticParameter_tendsto D representative
      offset radius Fsys x w₀ hw₀ data hA)
    (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
      offset radius Fsys x w₀ hw₀ data hA c r)
    (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
      offset radius Fsys x w₀ hw₀ data hA c 0)
    (boundary.simultaneousQuantitativeBoundaryScale_eventually_ge_one D
      representative offset radius Fsys x w₀ hw₀ data hA c 0)
    (fun z ↦
      boundary.simultaneousQuantitativeAnalyticSourceSymbolValue_first_hasPolynomialUpperBound
        D representative offset radius Fsys x w₀ hw₀ data hA c (Sum.inl z))
    (fun z ↦
      boundary.simultaneousQuantitativeAnalyticSourceSymbolValue_first_hasPolynomialUpperBound
        D representative offset radius Fsys x w₀ hw₀ data hA c (Sum.inr z))
    k b
  obtain ⟨C, hC, P, hbound⟩ := hbound
  refine ⟨C, hC, P, ?_⟩
  filter_upwards [hbound,
    boundary.simultaneousQuantitativeBoundaryScale_zero_eventuallyEq_individualMixedTerminal
      D representative offset radius Fsys x w₀ hw₀ data hA c] with n hn hscale
  change |change.changeCoefficientValue
      (boundary.simultaneousQuantitativeAnalyticParameter D representative
        offset radius Fsys x w₀ hw₀ data hA)
      (boundary.simultaneousQuantitativeAnalyticSourceValue D representative
        offset radius Fsys x w₀ hw₀ data hA c r)
      (boundary.simultaneousQuantitativeAnalyticPrefixValue D representative
        offset radius Fsys x w₀ hw₀ data hA c 0) k b n| ≤
    C * (data.orderedClusterIndividualBoundaryScale A
      (boundary.individualQuantitativeSubsequence D representative offset radius
        Fsys x w₀ hw₀ data hA) c (boundary.preprocessed.fixedSteps c)
      (boundary.individualMixedTerminalBoundaryIndex D representative offset
        radius Fsys x w₀ hw₀ data c)
      (n + boundary.simultaneousQuantitativeTail D representative offset radius
        Fsys x w₀ hw₀ data hA)) ^ P
  rw [← hscale]
  exact hn

/-- The analytic seam change evaluates to the exact finite identity required
by `IndividualSimultaneousFiniteFamilyCompatibility`. -/
theorem eventually_individualSimultaneousFiniteFamilyIdentity
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    ∀ᶠ n in atTop, ∀ k,
      ((boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
        representative offset radius Fsys x w₀ hw₀ data hA c).change
          (boundary.simultaneousNumericStage D representative offset radius Fsys
            x w₀ hw₀ data c).certificate.firstCentralStepIndex).beforeValue k n =
        ∑ b, boundary.individualSimultaneousFiniteFamilyCoefficient D
            representative offset radius Fsys x w₀ hw₀ data hA c k b n *
          boundary.individualMixedBoundaryValueOnSimultaneousTail D
            representative offset radius Fsys x w₀ hw₀ data hA c
            (boundary.individualMixedTerminalBoundaryIndex D representative
              offset radius Fsys x w₀ hw₀ data c) b n := by
  let r := (boundary.simultaneousNumericStage D representative offset radius
    Fsys x w₀ hw₀ data c).certificate.firstCentralStepIndex
  let change := boundary.individualSimultaneousFiniteAnalyticChange D
    representative offset radius Fsys x w₀ hw₀ data c
  let parameter := boundary.simultaneousQuantitativeAnalyticParameter D
    representative offset radius Fsys x w₀ hw₀ data hA
  let outerValue := boundary.simultaneousQuantitativeAnalyticSourceValue D
    representative offset radius Fsys x w₀ hw₀ data hA c r
  let coefficientValue := boundary.simultaneousQuantitativeAnalyticPrefixValue D
    representative offset radius Fsys x w₀ hw₀ data hA c 0
  have hchange := change.eventually_targetValue_eq_sum parameter
    (boundary.simultaneousQuantitativeAnalyticParameter_tendsto D representative
      offset radius Fsys x w₀ hw₀ data hA) outerValue coefficientValue
  have htarget :=
    boundary.eventually_individualSimultaneousTargetValue_eq_firstBeforeValue D
      representative offset radius Fsys x w₀ hw₀ data hA c
  have hsource :=
    boundary.eventually_individualSimultaneousSourceValue_eq_terminalBoundaryValue
      D representative offset radius Fsys x w₀ hw₀ data hA c
  filter_upwards [hchange, htarget, hsource] with n hn htarget hsource
  intro k
  rw [← htarget k, hn k]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [hsource b]
  rfl

/-- Canonical unconditional finite-family compatibility between the terminal
individual boundary and the first simultaneous source boundary. -/
noncomputable def individualSimultaneousFiniteFamilyCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    boundary.IndividualSimultaneousFiniteFamilyCompatibility D representative
      offset radius Fsys x w₀ hw₀ data hA c
      (boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
        representative offset radius Fsys x w₀ hw₀ data hA c) where
  coefficient := boundary.individualSimultaneousFiniteFamilyCoefficient D
    representative offset radius Fsys x w₀ hw₀ data hA c
  coefficient_bound := fun k b ↦
    boundary.individualSimultaneousFiniteFamilyCoefficient_hasPolynomialUpperBound
      D representative offset radius Fsys x w₀ hw₀ data hA c k b
  identity :=
    boundary.eventually_individualSimultaneousFiniteFamilyIdentity D
      representative offset radius Fsys x w₀ hw₀ data hA c

/-- Existence form of the unconditional compatibility constructor. -/
theorem nonempty_individualSimultaneousFiniteFamilyCompatibility
    (hA : IsAbel A) (c : Fin data.orderedClusterCount) :
    Nonempty
      (boundary.IndividualSimultaneousFiniteFamilyCompatibility D representative
        offset radius Fsys x w₀ hw₀ data hA c
        (boundary.simultaneousQuantitativeFiniteAnalyticSegmentData D
          representative offset radius Fsys x w₀ hw₀ data hA c)) :=
  ⟨boundary.individualSimultaneousFiniteFamilyCompatibility D representative
    offset radius Fsys x w₀ hw₀ data hA c⟩

end RestrictedBaseHermiteRankTopPrefixPreprocessedSequenceBoundary
end AbelFormalization
