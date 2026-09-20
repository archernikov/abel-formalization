import AbelFormalization.WilkieCase2AbelConditional
import AbelFormalization.Wilkie28WeakSelectionCompactExtraction
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

end AbelFormalization
