import AbelFormalization.WilkieCase2AbelConditional
import AbelFormalization.Wilkie28WeakSelectionCompactExtraction
import AbelFormalization.Wilkie28WeakSelectionCompactComponentReduction
import AbelFormalization.Wilkie28WeakSelectionFiniteClosedCover
import AbelFormalization.MaxwellAlmostEverywhereSmoothness
import AbelFormalization.MaxwellMeagreClosureSelection
import AbelFormalization.Wilkie28MaxwellWeakSelection
import AbelFormalization.WilkieCase2ExceptionalProductFlatTransport

/-!
# Abel Case 2 reduced to the two Maxwell family theorems

The compact graph-extraction property is the localized form of Wilkie 2.3.
The `haeSmooth` premise is the exact 2.4 output.  Everything else needed for
Case 2, including transport between flat and product coordinates, is proved.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- For an Abel-family tuple, Wilkie's entire Case 2 conclusion follows from
compact local graph extraction and almost-everywhere smoothness at each
reachable affine slice. -/
theorem wilkieCase2_abel_projection_or_minorInterval_of_Maxwell
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hextract : ∀ m (F : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      WilkieCase2Reachable F₀ (m + 1) F →
      Wilkie28CompactIncidenceGraphExtraction
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A)))
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a)
    (haeSmooth : ∀ m (F : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1))
        (hReach : WilkieCase2Reachable F₀ (m + 1) F),
      ∀ s : Wilkie28WeakSelectedWitness
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A)))
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a,
        ∃ B : Set ℝ,
          IsClosed B ∧ interior B = ∅ ∧
            (∀ t ∈ s.U \ B, DifferentiableAt ℝ s.φ t))
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
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  apply wilkieCase2_abel_projection_or_minorInterval_of_smoothSelection
    hA hUFF hq F₀ a U hF₀
  · intro m F i hReach _hFsmooth _hregular
    let H := wilkieCase2Flatten F
    let pivot : RealEuclideanFunction ((m + 1) + q) :=
      fun z ↦ z (Fin.castAdd q i)
    have hH : FunctionTupleInFamily (abelGeometricFamily A) H :=
      wilkieCase2Reachable_flatTupleInFamily hG hReach hF₀
    have hpivot : pivot ∈ abelGeometricFamily A ((m + 1) + q) := by
      simpa [pivot] using hG.polynomial (MvPolynomial.X (Fin.castAdd q i))
    have hweak := wilkie28_weakSelection_of_compactIncidenceGraphExtraction
      hG hsmooth hderiv H pivot a hH hpivot (hextract m F i hReach)
    have hflatSelection :=
      wilkie28_smoothSingularWitnessSelection_of_weakSelection_and_aeSmooth
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A)))
        H pivot a hweak (haeSmooth m F i hReach)
    have hHsmooth : ContDiff ℝ 1 H := by
      rw [contDiff_pi]
      intro j
      exact (hsmooth _ _ (hH j)).of_le (by simp)
    have hHdiff : ∀ z, DifferentiableAt ℝ H z := by
      intro z
      exact hHsmooth.differentiable (by simp) z
    have hpivotDiff : ∀ z, DifferentiableAt ℝ pivot z := by
      intro z
      change DifferentiableAt ℝ
        (ContinuousLinearMap.proj (Fin.castAdd q i) :
          RealEuclidean ((m + 1) + q) →L[ℝ] ℝ) z
      exact (ContinuousLinearMap.proj (Fin.castAdd q i) :
        RealEuclidean ((m + 1) + q) →L[ℝ] ℝ).differentiableAt
    let E := wilkieCase2ProductFlatEquiv (m + 1) q
    have htransport :=
      wilkie28_smoothSingularWitnessSelection_comp_linearEquiv
        E H pivot a hHdiff hpivotDiff hflatSelection
    have hFcomp : H ∘ E = F := by
      funext x
      exact congrArg F (E.symm_apply_apply x)
    have hpivotComp : pivot ∘ E = (fun x ↦ x.1 i) := by
      funext x
      exact wilkieCase2ProductFlatEquiv_visible x i
    rw [hFcomp, hpivotComp] at htransport
    exact htransport
  · exact hUopen
  · exact hUconvex
  · exact hregular
  · exact hbounded
  · exact hnonempty

/-- The proved Maxwell continuous weak-selection theorem discharges Wilkie
2.3 directly on every reachable affine slice.  Thus Case 2 needs only the
family-level continuous-selection and almost-everywhere smoothness outputs,
with no compact graph-extraction premise. -/
theorem
    wilkieCase2_abel_projection_or_minorInterval_of_MaxwellContinuousWeakSelection
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hweak : MaxwellContinuousWeakSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (haeSmooth : ∀ m (F : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1))
        (hReach : WilkieCase2Reachable F₀ (m + 1) F),
      ∀ s : Wilkie28WeakSelectedWitness
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A)))
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a,
        ∃ B : Set ℝ,
          IsClosed B ∧ interior B = ∅ ∧
            (∀ t ∈ s.U \ B, DifferentiableAt ℝ s.φ t))
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
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  apply wilkieCase2_abel_projection_or_minorInterval_of_smoothSelection
    hA hUFF hq F₀ a U hF₀
  · intro m F i hReach _hFsmooth _hregular
    let H := wilkieCase2Flatten F
    let pivot : RealEuclideanFunction ((m + 1) + q) :=
      fun z ↦ z (Fin.castAdd q i)
    have hH : FunctionTupleInFamily (abelGeometricFamily A) H :=
      wilkieCase2Reachable_flatTupleInFamily hG hReach hF₀
    have hpivot : pivot ∈ abelGeometricFamily A ((m + 1) + q) := by
      simpa [pivot] using hG.polynomial (MvPolynomial.X (Fin.castAdd q i))
    have hweakSlice :=
      wilkie28_weakSelection_of_MaxwellContinuousWeakSelection
        hG hsmooth hderiv (by omega) H pivot a hH hpivot hC hweak
    have hflatSelection :=
      wilkie28_smoothSingularWitnessSelection_of_weakSelection_and_aeSmooth
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A)))
        H pivot a hweakSlice (haeSmooth m F i hReach)
    have hHsmooth : ContDiff ℝ 1 H := by
      rw [contDiff_pi]
      intro j
      exact (hsmooth _ _ (hH j)).of_le (by simp)
    have hHdiff : ∀ z, DifferentiableAt ℝ H z := by
      intro z
      exact hHsmooth.differentiable (by simp) z
    have hpivotDiff : ∀ z, DifferentiableAt ℝ pivot z := by
      intro z
      change DifferentiableAt ℝ
        (ContinuousLinearMap.proj (Fin.castAdd q i) :
          RealEuclidean ((m + 1) + q) →L[ℝ] ℝ) z
      exact (ContinuousLinearMap.proj (Fin.castAdd q i) :
        RealEuclidean ((m + 1) + q) →L[ℝ] ℝ).differentiableAt
    let E := wilkieCase2ProductFlatEquiv (m + 1) q
    have htransport :=
      wilkie28_smoothSingularWitnessSelection_comp_linearEquiv
        E H pivot a hHdiff hpivotDiff hflatSelection
    have hFcomp : H ∘ E = F := by
      funext x
      exact congrArg F (E.symm_apply_apply x)
    have hpivotComp : pivot ∘ E = (fun x ↦ x.1 i) := by
      funext x
      exact wilkieCase2ProductFlatEquiv_visible x i
    rw [hFcomp, hpivotComp] at htransport
    exact htransport
  · exact hUopen
  · exact hUconvex
  · exact hregular
  · exact hbounded
  · exact hnonempty

/-- Charbonnel Theorem 2.1 now supplies the weak-selection half of Case 2;
the only remaining Maxwell family theorem in this endpoint is 2.4,
almost-everywhere smoothness. -/
theorem
    wilkieCase2_abel_projection_or_minorInterval_of_theorem21_and_MaxwellAlmostEverywhereSmoothness
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
    (hMaxwell : MaxwellAlmostEverywhereSmoothness
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
  apply
    wilkieCase2_abel_projection_or_minorInterval_of_MaxwellContinuousWeakSelection
      hA hUFF hq F₀ a U hF₀
      (maxwellContinuousWeakSelection_of_theorem21 hC h21)
  · intro m F i hReach s
    exact wilkie28_aeSmooth_of_MaxwellAlmostEverywhereSmoothness
      hMaxwell (by omega) s
  · exact hUopen
  · exact hUconvex
  · exact hregular
  · exact hbounded
  · exact hnonempty

/-- For an Abel family, WS5--WS6 give continuous weak selection through the
category closure theorem.  Thus the only remaining family-level input in
Case 2 is Maxwell's almost-everywhere smoothness conclusion. -/
theorem
    wilkieCase2_abel_projection_or_minorInterval_of_MaxwellAlmostEverywhereSmoothness_direct
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hMaxwell : MaxwellAlmostEverywhereSmoothness
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
  let hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  have hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    charbonnelClosure_closureInteriorRegularity hC
  apply
    wilkieCase2_abel_projection_or_minorInterval_of_MaxwellContinuousWeakSelection
      hA hUFF hq F₀ a U hF₀
      (maxwellContinuousWeakSelection_of_closureInteriorRegularity
        hC hregularity)
  · intro m F i hReach s
    exact wilkie28_aeSmooth_of_MaxwellAlmostEverywhereSmoothness
      hMaxwell (by omega) s
  · exact hUopen
  · exact hUconvex
  · exact hregular
  · exact hbounded
  · exact hnonempty

/-- Source-shaped Case 2 endpoint.  One family-level instance of Maxwell's
almost-everywhere smoothness theorem supplies the specialized smoothness
premise at every reachable affine slice; the remaining hypothesis is exactly
the compact local graph-extraction form of Maxwell weak selection. -/
theorem
    wilkieCase2_abel_projection_or_minorInterval_of_MaxwellAlmostEverywhereSmoothness
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hextract : ∀ m (F : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      WilkieCase2Reachable F₀ (m + 1) F →
      Wilkie28CompactIncidenceGraphExtraction
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A)))
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a)
    (hMaxwell : MaxwellAlmostEverywhereSmoothness
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
      ∃ cols : Fin q ↪ Fin (n + q), ∃ eta : ℝ,
        0 < eta ∧ Set.Icc (0 : ℝ) eta ⊆
          (fun z ↦ (standardJacobianColumnMinor
            (wilkieCase2Flatten F₀) cols z) ^ 2) ''
            wilkieFiberOver (wilkieCase2Flatten F₀) a U := by
  apply wilkieCase2_abel_projection_or_minorInterval_of_Maxwell
    hA hUFF hq F₀ a U hF₀ hextract
  · intro m F i hReach s
    exact
      wilkie28_aeSmooth_of_MaxwellAlmostEverywhereSmoothness
        hMaxwell (by omega) s
  · exact hUopen
  · exact hUconvex
  · exact hregular
  · exact hbounded
  · exact hnonempty

/-- WS5 and compactness localize the Maxwell 2.3 premise further: it is
enough to extract a graph from one compact connected component with visible
projection having interior.  Component membership is automatic by
`MaxwellCompactComponentMembership`. -/
theorem wilkieCase2_abel_projection_or_minorInterval_of_Maxwell_components
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hextract : ∀ m (F : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      WilkieCase2Reachable F₀ (m + 1) F →
      Wilkie28CompactComponentGraphExtraction
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A)))
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a)
    (haeSmooth : ∀ m (F : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1))
        (hReach : WilkieCase2Reachable F₀ (m + 1) F),
      ∀ s : Wilkie28WeakSelectedWitness
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A)))
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a,
        ∃ B : Set ℝ,
          IsClosed B ∧ interior B = ∅ ∧
            (∀ t ∈ s.U \ B, DifferentiableAt ℝ s.φ t))
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
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  apply wilkieCase2_abel_projection_or_minorInterval_of_Maxwell
    hA hUFF hq F₀ a U hF₀
  · intro m F i hReach
    let H := wilkieCase2Flatten F
    let pivot : RealEuclideanFunction ((m + 1) + q) :=
      fun z ↦ z (Fin.castAdd q i)
    have hH : FunctionTupleInFamily (abelGeometricFamily A) H :=
      wilkieCase2Reachable_flatTupleInFamily hG hReach hF₀
    have hpivot : pivot ∈ abelGeometricFamily A ((m + 1) + q) := by
      simpa [pivot] using hG.polynomial (MvPolynomial.X (Fin.castAdd q i))
    obtain ⟨hincidenceClosed, hincidenceMem, _hprojectionMem,
        _hprojectionEq⟩ :=
      wilkie28WeakSelectionIncidence_sourceData
        hG hsmooth hderiv H pivot a hH hpivot
    exact
      wilkie28_compactIncidenceGraphExtraction_of_componentGraphExtraction
        hC H pivot a hincidenceClosed hincidenceMem
          (hextract m F i hReach)
  · exact haeSmooth
  · exact hUopen
  · exact hUconvex
  · exact hregular
  · exact hbounded
  · exact hnonempty

/-- A still more concrete Abel Case 2 endpoint: it is enough to find, in
every large reachable compact component, a polynomial-sign cut whose visible
projection has interior and is single-valued.  The explicit graph construction
is supplied by `Wilkie28WeakSelectionCompactComponentReduction`. -/
theorem wilkieCase2_abel_projection_or_minorInterval_of_Maxwell_polynomialBranches
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hbranch : ∀ m (F : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      WilkieCase2Reachable F₀ (m + 1) F →
      Wilkie28LargeComponentPolynomialGraphBranch
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a)
    (haeSmooth : ∀ m (F : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1))
        (hReach : WilkieCase2Reachable F₀ (m + 1) F),
      ∀ s : Wilkie28WeakSelectedWitness
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A)))
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a,
        ∃ B : Set ℝ,
          IsClosed B ∧ interior B = ∅ ∧
            (∀ t ∈ s.U \ B, DifferentiableAt ℝ s.φ t))
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
  apply wilkieCase2_abel_projection_or_minorInterval_of_Maxwell_components
    hA hUFF hq F₀ a U hF₀
  · intro m F i hReach
    exact
      wilkie28_componentGraphExtraction_of_largeComponentPolynomialGraphBranch
        hC.toPositiveArityWeakSetStructure (by omega)
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a
        (hbranch m F i hReach)
  · exact haeSmooth
  · exact hUopen
  · exact hUconvex
  · exact hregular
  · exact hbounded
  · exact hnonempty

/-- A finite-cover form of the Maxwell 2.3 endpoint.  At every reachable
stage it suffices to cover each compact component with large visible
projection by finitely many closed polynomial-sign pieces on which visible
projection is injective.  The finite closed-union argument chooses a piece
whose projection still contains an interval. -/
theorem wilkieCase2_abel_projection_or_minorInterval_of_Maxwell_finiteClosedCovers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hcovers : ∀ m (F : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      WilkieCase2Reachable F₀ (m + 1) F →
      Wilkie28LargeComponentFiniteClosedPolynomialGraphCover
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a)
    (haeSmooth : ∀ m (F : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1))
        (hReach : WilkieCase2Reachable F₀ (m + 1) F),
      ∀ s : Wilkie28WeakSelectedWitness
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A)))
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a,
        ∃ B : Set ℝ,
          IsClosed B ∧ interior B = ∅ ∧
            (∀ t ∈ s.U \ B, DifferentiableAt ℝ s.φ t))
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
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  apply wilkieCase2_abel_projection_or_minorInterval_of_Maxwell_polynomialBranches
    hA hUFF hq F₀ a U hF₀
  · intro m F i hReach
    let H := wilkieCase2Flatten F
    let pivot : RealEuclideanFunction ((m + 1) + q) :=
      fun z ↦ z (Fin.castAdd q i)
    have hH : FunctionTupleInFamily (abelGeometricFamily A) H :=
      wilkieCase2Reachable_flatTupleInFamily hG hReach hF₀
    have hpivot : pivot ∈ abelGeometricFamily A ((m + 1) + q) := by
      simpa [pivot] using hG.polynomial (MvPolynomial.X (Fin.castAdd q i))
    obtain ⟨hincidenceClosed, _hincidenceMem, _hprojectionMem,
        _hprojectionEq⟩ :=
      wilkie28WeakSelectionIncidence_sourceData
        hG hsmooth hderiv H pivot a hH hpivot
    exact
      wilkie28_largeComponentPolynomialGraphBranch_of_finiteClosedCover
        H pivot a hincidenceClosed (hcovers m F i hReach)
  · exact haeSmooth
  · exact hUopen
  · exact hUconvex
  · exact hregular
  · exact hbounded
  · exact hnonempty

/-- A combined Maxwell endpoint: if compact localization directly extracts a
differentiable incidence graph at every reachable affine stage, the full Abel
Case 2 conclusion follows without a separate almost-everywhere smoothness
premise. -/
theorem wilkieCase2_abel_projection_or_minorInterval_of_Maxwell_differentiableGraphs
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hextract : ∀ m (F : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      WilkieCase2Reachable F₀ (m + 1) F →
      Wilkie28CompactIncidenceDifferentiableGraphExtraction
        (charbonnelClosure
          (literalZeroSetFamily (abelGeometricFamily A)))
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hregular : ∀ y, F₀ y = a →
      Function.Surjective (fderiv ℝ F₀ y))
    (hbounded : Bornology.IsBounded
      (wilkieCase2VisibleCylinderFiber F₀ a U))
    (hnonempty : (wilkieCase2VisibleCylinderFiber F₀ a U).Nonempty) :
    realEuclideanTakeLeft ''
        wilkieFiberOver (wilkieCase2Flatten F₀) a U = U ∨
      ∃ cols : Fin q ↪ Fin (n + q), ∃ eta : ℝ,
        0 < eta ∧ Set.Icc (0 : ℝ) eta ⊆
          (fun z ↦ (standardJacobianColumnMinor
            (wilkieCase2Flatten F₀) cols z) ^ 2) ''
            wilkieFiberOver (wilkieCase2Flatten F₀) a U := by
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  apply wilkieCase2_abel_projection_or_minorInterval_of_smoothSelection
    hA hUFF hq F₀ a U hF₀
  · intro m F i hReach _hFsmooth _hregular
    let H := wilkieCase2Flatten F
    let pivot : RealEuclideanFunction ((m + 1) + q) :=
      fun z ↦ z (Fin.castAdd q i)
    have hH : FunctionTupleInFamily (abelGeometricFamily A) H :=
      wilkieCase2Reachable_flatTupleInFamily hG hReach hF₀
    have hpivot : pivot ∈ abelGeometricFamily A ((m + 1) + q) := by
      simpa [pivot] using hG.polynomial (MvPolynomial.X (Fin.castAdd q i))
    have hflatSelection :=
      wilkie28_smoothSingularWitnessSelection_of_compactIncidenceDifferentiableGraphExtraction
        hG hsmooth hderiv H pivot a hH hpivot (hextract m F i hReach)
    have hHsmooth : ContDiff ℝ 1 H := by
      rw [contDiff_pi]
      intro j
      exact (hsmooth _ _ (hH j)).of_le (by simp)
    have hHdiff : ∀ z, DifferentiableAt ℝ H z := by
      intro z
      exact hHsmooth.differentiable (by simp) z
    have hpivotDiff : ∀ z, DifferentiableAt ℝ pivot z := by
      intro z
      change DifferentiableAt ℝ
        (ContinuousLinearMap.proj (Fin.castAdd q i) :
          RealEuclidean ((m + 1) + q) →L[ℝ] ℝ) z
      exact (ContinuousLinearMap.proj (Fin.castAdd q i) :
        RealEuclidean ((m + 1) + q) →L[ℝ] ℝ).differentiableAt
    let E := wilkieCase2ProductFlatEquiv (m + 1) q
    have htransport :=
      wilkie28_smoothSingularWitnessSelection_comp_linearEquiv
        E H pivot a hHdiff hpivotDiff hflatSelection
    have hFcomp : H ∘ E = F := by
      funext x
      exact congrArg F (E.symm_apply_apply x)
    have hpivotComp : pivot ∘ E = (fun x ↦ x.1 i) := by
      funext x
      exact wilkieCase2ProductFlatEquiv_visible x i
    rw [hFcomp, hpivotComp] at htransport
    exact htransport
  · exact hUopen
  · exact hUconvex
  · exact hregular
  · exact hbounded
  · exact hnonempty

/-- A finite closed regular-implicit cover simultaneously supplies Maxwell
weak selection and selector differentiability at every reachable stage.  It
therefore closes both source inputs of Wilkie 2.8 on this branch. -/
theorem wilkieCase2_abel_projection_or_minorInterval_of_Maxwell_finiteClosedRegularImplicitCovers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hcovers : ∀ m (F : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      WilkieCase2Reachable F₀ (m + 1) F →
      Wilkie28LargeComponentFiniteClosedRegularImplicitCover
        (wilkieCase2Flatten F)
        (fun z : RealEuclidean ((m + 1) + q) ↦ z (Fin.castAdd q i)) a)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hregular : ∀ y, F₀ y = a →
      Function.Surjective (fderiv ℝ F₀ y))
    (hbounded : Bornology.IsBounded
      (wilkieCase2VisibleCylinderFiber F₀ a U))
    (hnonempty : (wilkieCase2VisibleCylinderFiber F₀ a U).Nonempty) :
    realEuclideanTakeLeft ''
        wilkieFiberOver (wilkieCase2Flatten F₀) a U = U ∨
      ∃ cols : Fin q ↪ Fin (n + q), ∃ eta : ℝ,
        0 < eta ∧ Set.Icc (0 : ℝ) eta ⊆
          (fun z ↦ (standardJacobianColumnMinor
            (wilkieCase2Flatten F₀) cols z) ^ 2) ''
            wilkieFiberOver (wilkieCase2Flatten F₀) a U := by
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))) :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  apply wilkieCase2_abel_projection_or_minorInterval_of_Maxwell_differentiableGraphs
    hA hUFF hq F₀ a U hF₀
  · intro m F i hReach
    let H := wilkieCase2Flatten F
    let pivot : RealEuclideanFunction ((m + 1) + q) :=
      fun z ↦ z (Fin.castAdd q i)
    have hH : FunctionTupleInFamily (abelGeometricFamily A) H :=
      wilkieCase2Reachable_flatTupleInFamily hG hReach hF₀
    have hpivot : pivot ∈ abelGeometricFamily A ((m + 1) + q) := by
      simpa [pivot] using hG.polynomial (MvPolynomial.X (Fin.castAdd q i))
    obtain ⟨hincidenceClosed, hincidenceMem, _hprojectionMem,
        _hprojectionEq⟩ :=
      wilkie28WeakSelectionIncidence_sourceData
        hG hsmooth hderiv H pivot a hH hpivot
    exact
      wilkie28_compactIncidenceDifferentiableGraphExtraction_of_largeComponentFiniteClosedRegularImplicitCover
        hC (by omega) H pivot a hincidenceClosed hincidenceMem
          (hcovers m F i hReach)
  · exact hUopen
  · exact hUconvex
  · exact hregular
  · exact hbounded
  · exact hnonempty

end AbelFormalization
