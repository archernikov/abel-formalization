import AbelFormalization.MaxwellAutomaticFirstOrder
import AbelFormalization.MaxwellSection5Smoothness
import AbelFormalization.WilkieCase2AbelMaxwellReduction

/-!
# Abel Case 2 with automatic Maxwell smoothness

For the Abel geometric family, the geometric and smooth family structures
supply both the Charbonnel weak-set structure and the Section 5 trace
membership interface.  Maxwell's almost-everywhere smoothness theorem is
therefore automatic from Charbonnel Theorems 2.1 and 2.2, and the Case 2
endpoint no longer needs an explicit smoothness-package hypothesis.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Abel Case 2 follows from uniform fiber finiteness and Charbonnel
Theorems 2.1 and 2.2.  The required Maxwell almost-everywhere smoothness
package is derived internally for the Abel literal-zero Charbonnel closure. -/
theorem wilkieCase2_abel_projection_or_minorInterval_of_theorems21_22
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hregular : ∀ y, F₀ y = a →
      Function.Surjective (fderiv ℝ F₀ y))
    (hbounded : Bornology.IsBounded
      (wilkieCase2VisibleCylinderFiber F₀ a U))
    (hnonempty : (wilkieCase2VisibleCylinderFiber F₀ a U).Nonempty) :
    realEuclideanTakeLeft ''
        wilkieFiberOver (wilkieCase2Flatten F₀) a U = U ∨
      ∃ cols : Fin q ↪ Fin (n + q), ∃ η : ℝ,
        0 < η ∧ Set.Icc (0 : ℝ) η ⊆
          (fun z ↦ (standardJacobianColumnMinor
            (wilkieCase2Flatten F₀) cols z) ^ 2) ''
            wilkieFiberOver (wilkieCase2Flatten F₀) a U := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  have hmem : CharbonnelSection5TraceMembership
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth
  have hMaxwell : MaxwellAlmostEverywhereSmoothness
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    maxwellAlmostEverywhereSmoothness_of_charbonnel
      hC hmem h21 h22
  exact
    wilkieCase2_abel_projection_or_minorInterval_of_theorem21_and_MaxwellAlmostEverywhereSmoothness
      hA hUFF hq F₀ a U hF₀ h21 hMaxwell hUopen hUconvex
        hregular hbounded hnonempty

/-- Abel Case 2 follows directly from the two remaining Section 5 induction
inputs.  All trace, truncation, one-dimensional base, and closure-nullity
witness inputs are supplied by the Abel literal-zero Charbonnel closure. -/
theorem wilkieCase2_abel_projection_or_minorInterval_of_section5
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hdecomp : ∀ {d : ℕ}, 0 < d →
      CharbonnelFiniteLocallyClosedDecomposition
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A))) d)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hregular : ∀ y, F₀ y = a →
      Function.Surjective (fderiv ℝ F₀ y))
    (hbounded : Bornology.IsBounded
      (wilkieCase2VisibleCylinderFiber F₀ a U))
    (hnonempty : (wilkieCase2VisibleCylinderFiber F₀ a U).Nonempty) :
    realEuclideanTakeLeft ''
        wilkieFiberOver (wilkieCase2Flatten F₀) a U = U ∨
      ∃ cols : Fin q ↪ Fin (n + q), ∃ η : ℝ,
        0 < η ∧ Set.Icc (0 : ℝ) η ⊆
          (fun z ↦ (standardJacobianColumnMinor
            (wilkieCase2Flatten F₀) cols z) ^ 2) ''
            wilkieFiberOver (wilkieCase2Flatten F₀) a U := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  have hmem : CharbonnelSection5TraceMembership
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth
  have htrunc : CharbonnelCompactTruncationMembership
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_compactTruncationMembership hG hsmooth
  have hbase : CharbonnelPPrime
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) 1 :=
    hC.charbonnelPPrime_one
  have hwitness : HasCharbonnelClosureNullityWitnesses
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_hasClosureNullityWitnesses hG hsmooth
  obtain ⟨h21, h22⟩ :=
    charbonnelTheorems21And22_of_section5Induction
      hmem htrunc hbase hanalytic hdecomp hwitness
  exact
    wilkieCase2_abel_projection_or_minorInterval_of_theorems21_22
      hA hUFF hq F₀ a U hF₀ h21 h22 hUopen hUconvex hregular
        hbounded hnonempty

/-- Source-shaped Abel Case 2 endpoint.  Maxwell's meagre finite-selection
step and Charbonnel's analytic successor step produce Theorems 2.1 and 2.2,
and hence both weak selection and almost-everywhere smoothness internally. -/
theorem
    wilkieCase2_abel_projection_or_minorInterval_of_meagreSelection_and_analyticStep
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hregular : ∀ y, F₀ y = a →
      Function.Surjective (fderiv ℝ F₀ y))
    (hbounded : Bornology.IsBounded
      (wilkieCase2VisibleCylinderFiber F₀ a U))
    (hnonempty : (wilkieCase2VisibleCylinderFiber F₀ a U).Nonempty) :
    realEuclideanTakeLeft ''
        wilkieFiberOver (wilkieCase2Flatten F₀) a U = U ∨
      ∃ cols : Fin q ↪ Fin (n + q), ∃ η : ℝ,
        0 < η ∧ Set.Icc (0 : ℝ) η ⊆
          (fun z ↦ (standardJacobianColumnMinor
            (wilkieCase2Flatten F₀) cols z) ^ 2) ''
            wilkieFiberOver (wilkieCase2Flatten F₀) a U := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_theorem21_of_meagreSelection_and_analyticStep
      hG hsmooth hUFF hselection hanalytic
  have hMaxwell : MaxwellAlmostEverywhereSmoothness
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_maxwellAlmostEverywhereSmoothness_of_meagreSelection_and_analyticStep
      hG hsmooth hUFF hselection hanalytic
  exact
    wilkieCase2_abel_projection_or_minorInterval_of_theorem21_and_MaxwellAlmostEverywhereSmoothness
      hA hUFF hq F₀ a U hF₀ h21 hMaxwell hUopen hUconvex hregular
        hbounded hnonempty

end AbelFormalization
