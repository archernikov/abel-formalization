import AbelFormalization.WilkieCase2ReachableExceptionalMembership
import AbelFormalization.CharbonnelComplementPipeline

/-!
# Wilkie Case 2 for an Abel-family tuple, conditional only on selection

The Abel-family and uniform-fiber hypotheses discharge the weak-structure
and exceptional-set membership inputs at every affine descendant.  The one
remaining source input is smooth singular-witness selection for those
reachable maps.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- The recursive fixed-minor alternative for one Abel-family tuple. -/
theorem wilkieCase2_abel_fixedMinorAlternative_of_smoothSelection
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hselection : ∀ m (G : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      WilkieCase2Reachable F₀ (m + 1) G → ContDiff ℝ 1 G →
      (∀ y, G y = a → Function.Surjective (fderiv ℝ G y)) →
      Wilkie28MathlibOnly.SmoothSingularWitnessSelection
        G (fun x ↦ x.1 i) a)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hregular : ∀ y, F₀ y = a →
      Function.Surjective (fderiv ℝ F₀ y))
    (hbounded : Bornology.IsBounded
      (wilkieCase2VisibleCylinderFiber F₀ a U))
    (hnonempty : (wilkieCase2VisibleCylinderFiber F₀ a U).Nonempty) :
    wilkieCase2RecursiveAlternative F₀ a U := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hC :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  have hF₀smooth : ContDiff ℝ 1 F₀ :=
    contDiff_product_of_flatTupleInFamily hsmooth F₀ hF₀
  exact wilkieCase2_originalMap_fixedMinorAlternative
    hq F₀ a U hC
    (fun m G i hReach ↦
      wilkieCase2Reachable_exceptional_mem_abelCharbonnel
        hA hF₀ hReach a i)
    hselection hF₀smooth hUopen hUconvex hregular hbounded hnonempty

/-- The projection-or-fixed-minor interval conclusion of Wilkie's Case 2
argument for one Abel-family tuple. -/
theorem wilkieCase2_abel_projection_or_minorInterval_of_smoothSelection
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {n q : ℕ} (hq : 0 < q)
    (F₀ : WilkieCase2StageMap n q) (a : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hF₀ : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten F₀))
    (hselection : ∀ m (G : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      WilkieCase2Reachable F₀ (m + 1) G → ContDiff ℝ 1 G →
      (∀ y, G y = a → Function.Surjective (fderiv ℝ G y)) →
      Wilkie28MathlibOnly.SmoothSingularWitnessSelection
        G (fun x ↦ x.1 i) a)
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
  have halt := wilkieCase2_abel_fixedMinorAlternative_of_smoothSelection
    hA hUFF hq F₀ a U hF₀ hselection hUopen hUconvex
    hregular hbounded hnonempty
  obtain ⟨_hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have hflatSmooth : ContDiff ℝ 1 (wilkieCase2Flatten F₀) := by
    rw [contDiff_pi]
    intro j
    exact (hsmooth _ _ (hF₀ j)).of_le (by simp)
  have hF₀smooth : ContDiff ℝ 1 F₀ :=
    contDiff_product_of_flatTupleInFamily hsmooth F₀ hF₀
  have hF₀diff : ∀ y, DifferentiableAt ℝ F₀ y := by
    intro y
    exact hF₀smooth.differentiable (by simp) y
  have hflatRegular := wilkieCase2Flatten_regular F₀ hF₀diff a hregular
  let E := wilkieCase2ProductFlatEquiv n q
  have hflatBounded : Bornology.IsBounded
      (wilkieFiberOver (wilkieCase2Flatten F₀) a U) := by
    rw [← wilkieCase2Flatten_cylinder_image]
    exact E.lipschitzWith.isBounded_image hbounded
  exact wilkieCase2RecursiveAlternative_finalFork
    F₀ a U hflatSmooth hUopen hUconvex hflatRegular hflatBounded halt

end AbelFormalization
