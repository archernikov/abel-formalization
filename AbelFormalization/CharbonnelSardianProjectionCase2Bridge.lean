import AbelFormalization.CharbonnelSardianProjectionFromAboveLevelAlternative
import AbelFormalization.WilkieCase2AutomaticMaxwell

/-!
# Abel Case 2 bridge for the Sardian projection constructor

The old tuple in the one-coordinate Sardian projection step has `q + 1`
equations on `n + (q + 1)` variables.  It is therefore an instance of the
Case 2 map with `n` visible and `q + 1` hidden coordinates.  This module
identifies the two presentations and converts Case 2's fixed-minor interval
into the small positive last levels required by the projected Sardian family.

The other Case 2 outcome says that the old fiber projects onto the whole
visible set.  Eliminating that outcome is the remaining boundary-localization
step in the from-above proof; it is retained explicitly in the conclusions
below.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Regard the old Sardian tuple as a product-coordinate Case 2 stage map. -/
def sardianProjectionOldTupleStageMap
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q) :
    WilkieCase2StageMap n (q + 1) :=
  fun y ↦ sardianProjectionOldTuple old
    (wilkieCase2ProductFlatEquiv n (q + 1) y)

/-- Flattening the product-coordinate presentation recovers the old tuple
definitionally up to the product/flat continuous linear equivalence. -/
@[simp]
theorem wilkieCase2Flatten_sardianProjectionOldTupleStageMap
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q) :
    wilkieCase2Flatten (sardianProjectionOldTupleStageMap old) =
      sardianProjectionOldTuple old := by
  funext v
  simp [wilkieCase2Flatten, sardianProjectionOldTupleStageMap]

/-- The flat level cylinder of the old tuple is exactly its named fiber. -/
@[simp]
theorem wilkieFiberOver_sardianProjectionOldTuple
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1)) :
    wilkieFiberOver (sardianProjectionOldTuple old) e U =
      sardianProjectionOldTupleFiber old U e := by
  ext v
  change
    (sardianProjectionOldTuple old v = e ∧
        realEuclideanTakeLeft v ∈ U) ↔
      (realEuclideanTakeLeft v ∈ U ∧
        ∀ i, sardianProjectionOldTuple old v i = e i)
  constructor
  · rintro ⟨htuple, hvU⟩
    exact ⟨hvU, fun i ↦ congrFun htuple i⟩
  · rintro ⟨hvU, htuple⟩
    exact ⟨funext htuple, hvU⟩

/-- The flattened product-coordinate Case 2 cylinder is therefore the named
old-tuple fiber as well. -/
@[simp]
theorem wilkieFiberOver_sardianProjectionOldTupleStageMap
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1)) :
    wilkieFiberOver
        (wilkieCase2Flatten (sardianProjectionOldTupleStageMap old)) e U =
      sardianProjectionOldTupleFiber old U e := by
  rw [wilkieCase2Flatten_sardianProjectionOldTupleStageMap,
    wilkieFiberOver_sardianProjectionOldTuple]

/-- The product-coordinate Case 2 cylinder maps exactly onto the named flat
old-tuple fiber. -/
theorem sardianProjectionOldTupleStageMap_cylinder_image
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1)) :
    wilkieCase2ProductFlatEquiv n (q + 1) ''
        wilkieCase2VisibleCylinderFiber
          (sardianProjectionOldTupleStageMap old) e U =
      sardianProjectionOldTupleFiber old U e := by
  rw [wilkieCase2Flatten_cylinder_image,
    wilkieFiberOver_sardianProjectionOldTupleStageMap]

/-- Boundedness of the named flat fiber supplies the product-coordinate
boundedness hypothesis used by Case 2. -/
theorem isBounded_sardianProjectionOldTupleStageMap_cylinder
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1))
    (hbounded : Bornology.IsBounded
      (sardianProjectionOldTupleFiber old U e)) :
    Bornology.IsBounded
      (wilkieCase2VisibleCylinderFiber
        (sardianProjectionOldTupleStageMap old) e U) := by
  let E := wilkieCase2ProductFlatEquiv n (q + 1)
  have hinverseBounded : Bornology.IsBounded
      (E.symm '' sardianProjectionOldTupleFiber old U e) :=
    E.symm.lipschitzWith.isBounded_image hbounded
  apply hinverseBounded.subset
  intro y hy
  refine ⟨E y, ?_, ?_⟩
  · rw [← sardianProjectionOldTupleStageMap_cylinder_image old U e]
    exact ⟨y, hy, rfl⟩
  · exact E.symm_apply_apply y

/-- Nonemptiness of the flat old-tuple fiber supplies the corresponding
product-coordinate Case 2 hypothesis. -/
theorem nonempty_sardianProjectionOldTupleStageMap_cylinder
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1))
    (hnonempty : (sardianProjectionOldTupleFiber old U e).Nonempty) :
    (wilkieCase2VisibleCylinderFiber
      (sardianProjectionOldTupleStageMap old) e U).Nonempty := by
  obtain ⟨v, hv⟩ := hnonempty
  rw [← sardianProjectionOldTupleStageMap_cylinder_image old U e] at hv
  obtain ⟨y, hy, _⟩ := hv
  exact ⟨y, hy⟩

/-- The old tuple inherits its recorded differentiability after the ambient
coordinate reindexing. -/
theorem contDiff_sardianProjectionOldTuple
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q) :
    ContDiff ℝ (order + 1) (sardianProjectionOldTuple old) := by
  rw [contDiff_pi]
  intro i
  exact (old.equation_contDiff i).comp
    (sardianProjectionOldInputReindex n q).toContinuousLinearEquiv.contDiff

/-- Regularity of the old tuple's flat level transports across the
product/flat continuous linear equivalence used by Case 2. -/
theorem sardianProjectionOldTupleStageMap_regular
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (e : RealEuclidean (q + 1))
    (hregular : ∀ v, sardianProjectionOldTuple old v = e →
      Function.Surjective (fderiv ℝ (sardianProjectionOldTuple old) v)) :
    ∀ y, sardianProjectionOldTupleStageMap old y = e →
      Function.Surjective
        (fderiv ℝ (sardianProjectionOldTupleStageMap old) y) := by
  let E := wilkieCase2ProductFlatEquiv n (q + 1)
  intro y hy
  have htupleDiff : DifferentiableAt ℝ (sardianProjectionOldTuple old) (E y) :=
    (contDiff_sardianProjectionOldTuple old).differentiable
      (by positivity) (E y)
  have hchain :
      fderiv ℝ (sardianProjectionOldTupleStageMap old) y =
        (fderiv ℝ (sardianProjectionOldTuple old) (E y)).comp
          (E : ((Fin n → ℝ) × (Fin (q + 1) → ℝ)) →L[ℝ]
            RealEuclidean (n + (q + 1))) := by
    exact (htupleDiff.hasFDerivAt.comp y E.hasFDerivAt).fderiv
  have hy' : sardianProjectionOldTuple old (E y) = e := by
    simpa only [E, sardianProjectionOldTupleStageMap] using hy
  rw [hchain]
  exact (hregular (E y) hy').comp E.surjective

/-- Case 2's fixed-minor interval is already the minor branch of the
projected Sardian family.  Thus its projection-or-minor conclusion becomes
projection-surjectivity or the required small positive last levels. -/
theorem sardianProjection_projection_or_smallLevels_of_case2Alternative
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (e : RealEuclidean (q + 1)) (hepos : ∀ i, 0 < e i)
    (hcase :
      realEuclideanTakeLeft '' sardianProjectionOldTupleFiber old U e = U ∨
        ∃ columns : Fin (q + 1) ↪ Fin (n + (q + 1)),
          ∃ η : ℝ, 0 < η ∧ Set.Icc (0 : ℝ) η ⊆
            (fun v ↦ (standardJacobianColumnMinor
              (sardianProjectionOldTuple old) columns v) ^ 2) ''
              sardianProjectionOldTupleFiber old U e) :
    realEuclideanTakeLeft '' sardianProjectionOldTupleFiber old U e = U ∨
      ∃ η : ℝ, 0 < η ∧
        ∀ t : ℝ, 0 < t → t < η →
          ∃ x ∈ U,
            realEuclideanAppend x (charbonnelAppendLastParameter e t) ∈
              (sardianProjectionAlgebraicFamily
                hG hsmooth hderiv hn old).carrier := by
  rcases hcase with hprojection | ⟨columns, η, hη, hminor⟩
  · exact Or.inl hprojection
  · apply Or.inr
    apply exists_small_levels_in_sardianProjectionAlgebraicFamily
      hG hsmooth hderiv hn old U e hepos
    apply Or.inr
    refine ⟨columns, η, hη, ?_⟩
    intro t ht
    obtain ⟨v, hvFiber, hvLevel⟩ := hminor ht
    refine ⟨v, hvFiber, ?_⟩
    simpa only [sardianProjectionLastEquation] using hvLevel

/-- For an Abel old tuple, the automatic Case 2 theorem supplies the
preceding alternative from Charbonnel Theorems 2.1 and 2.2.  The hypotheses
left here are precisely the local geometric inputs of Case 2: an open convex
visible set, a regular attained value, and a bounded nonempty cylinder. -/
theorem sardianProjection_projection_or_smallLevels_of_theorems21_22
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent
      (abelGeometricFamily A) (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (e : RealEuclidean (q + 1)) (hepos : ∀ i, 0 < e i)
    (h21 : CharbonnelTheorem21
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (h22 : CharbonnelTheorem22
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hregular : ∀ v, sardianProjectionOldTuple old v = e →
      Function.Surjective (fderiv ℝ (sardianProjectionOldTuple old) v))
    (hbounded : Bornology.IsBounded
      (sardianProjectionOldTupleFiber old U e))
    (hnonempty : (sardianProjectionOldTupleFiber old U e).Nonempty) :
    realEuclideanTakeLeft '' sardianProjectionOldTupleFiber old U e = U ∨
      ∃ η : ℝ, 0 < η ∧
        ∀ t : ℝ, 0 < t → t < η →
          ∃ x ∈ U,
            realEuclideanAppend x (charbonnelAppendLastParameter e t) ∈
              (sardianProjectionAlgebraicFamily
                hA.geometric_smooth_derivativeClosed_abelGeometricFamily.1
                hA.geometric_smooth_derivativeClosed_abelGeometricFamily.2.1
                hA.geometric_smooth_derivativeClosed_abelGeometricFamily.2.2
                hn old).carrier := by
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have htuple : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten (sardianProjectionOldTupleStageMap old)) := by
    rw [wilkieCase2Flatten_sardianProjectionOldTupleStageMap]
    exact sardianProjectionOldTuple_inFamily hG old
  have hcase :=
    wilkieCase2_abel_projection_or_minorInterval_of_theorems21_22
      hA hUFF (by omega : 0 < q + 1)
      (sardianProjectionOldTupleStageMap old) e U htuple h21 h22
      hUopen hUconvex
      (sardianProjectionOldTupleStageMap_regular old e hregular)
      (isBounded_sardianProjectionOldTupleStageMap_cylinder
        old U e hbounded)
      (nonempty_sardianProjectionOldTupleStageMap_cylinder
        old U e hnonempty)
  have hcase' :
      realEuclideanTakeLeft '' sardianProjectionOldTupleFiber old U e = U ∨
        ∃ columns : Fin (q + 1) ↪ Fin (n + (q + 1)),
          ∃ η : ℝ, 0 < η ∧ Set.Icc (0 : ℝ) η ⊆
            (fun v ↦ (standardJacobianColumnMinor
              (sardianProjectionOldTuple old) columns v) ^ 2) ''
              sardianProjectionOldTupleFiber old U e := by
    simpa only [wilkieCase2Flatten_sardianProjectionOldTupleStageMap,
      wilkieFiberOver_sardianProjectionOldTuple] using hcase
  exact sardianProjection_projection_or_smallLevels_of_case2Alternative
    hG hsmooth hderiv hn old U e hepos hcase'

/-- Direct category weak selection reduces the Sardian Case 2 bridge to
Maxwell's almost-everywhere smoothness theorem alone. -/
theorem sardianProjection_projection_or_smallLevels_of_MaxwellAlmostEverywhereSmoothness
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent
      (abelGeometricFamily A) (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (e : RealEuclidean (q + 1)) (hepos : ∀ i, 0 < e i)
    (hMaxwell : MaxwellAlmostEverywhereSmoothness
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hregular : ∀ v, sardianProjectionOldTuple old v = e →
      Function.Surjective (fderiv ℝ (sardianProjectionOldTuple old) v))
    (hbounded : Bornology.IsBounded
      (sardianProjectionOldTupleFiber old U e))
    (hnonempty : (sardianProjectionOldTupleFiber old U e).Nonempty) :
    realEuclideanTakeLeft '' sardianProjectionOldTupleFiber old U e = U ∨
      ∃ η : ℝ, 0 < η ∧
        ∀ t : ℝ, 0 < t → t < η →
          ∃ x ∈ U,
            realEuclideanAppend x (charbonnelAppendLastParameter e t) ∈
              (sardianProjectionAlgebraicFamily
                hA.geometric_smooth_derivativeClosed_abelGeometricFamily.1
                hA.geometric_smooth_derivativeClosed_abelGeometricFamily.2.1
                hA.geometric_smooth_derivativeClosed_abelGeometricFamily.2.2
                hn old).carrier := by
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  have htuple : FunctionTupleInFamily (abelGeometricFamily A)
      (wilkieCase2Flatten (sardianProjectionOldTupleStageMap old)) := by
    rw [wilkieCase2Flatten_sardianProjectionOldTupleStageMap]
    exact sardianProjectionOldTuple_inFamily hG old
  have hcase :=
    wilkieCase2_abel_projection_or_minorInterval_of_MaxwellAlmostEverywhereSmoothness_direct
      hA hUFF (by omega : 0 < q + 1)
      (sardianProjectionOldTupleStageMap old) e U htuple hMaxwell
      hUopen hUconvex
      (sardianProjectionOldTupleStageMap_regular old e hregular)
      (isBounded_sardianProjectionOldTupleStageMap_cylinder
        old U e hbounded)
      (nonempty_sardianProjectionOldTupleStageMap_cylinder
        old U e hnonempty)
  have hcase' :
      realEuclideanTakeLeft '' sardianProjectionOldTupleFiber old U e = U ∨
        ∃ columns : Fin (q + 1) ↪ Fin (n + (q + 1)),
          ∃ η : ℝ, 0 < η ∧ Set.Icc (0 : ℝ) η ⊆
            (fun v ↦ (standardJacobianColumnMinor
              (sardianProjectionOldTuple old) columns v) ^ 2) ''
              sardianProjectionOldTupleFiber old U e := by
    simpa only [wilkieCase2Flatten_sardianProjectionOldTupleStageMap,
      wilkieFiberOver_sardianProjectionOldTuple] using hcase
  exact sardianProjection_projection_or_smallLevels_of_case2Alternative
    hG hsmooth hderiv hn old U e hepos hcase'

/-- Source-shaped form of the Sardian Case 2 bridge.  Maxwell's meagre
finite-selection step and Charbonnel's analytic successor step construct
Theorems 2.1 and 2.2 internally; the conclusion therefore retains only the
local geometric data needed at the selected positive level. -/
theorem
    sardianProjection_projection_or_smallLevels_of_meagreSelection_and_analyticStep
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent
      (abelGeometricFamily A) (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (e : RealEuclidean (q + 1)) (hepos : ∀ i, 0 < e i)
    (hselection : HasMaxwellMeagreClosureComponentSelection
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure
        (literalZeroSetFamily (abelGeometricFamily A))))
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hregular : ∀ v, sardianProjectionOldTuple old v = e →
      Function.Surjective (fderiv ℝ (sardianProjectionOldTuple old) v))
    (hbounded : Bornology.IsBounded
      (sardianProjectionOldTupleFiber old U e))
    (hnonempty : (sardianProjectionOldTupleFiber old U e).Nonempty) :
    realEuclideanTakeLeft '' sardianProjectionOldTupleFiber old U e = U ∨
      ∃ η : ℝ, 0 < η ∧
        ∀ t : ℝ, 0 < t → t < η →
          ∃ x ∈ U,
            realEuclideanAppend x (charbonnelAppendLastParameter e t) ∈
              (sardianProjectionAlgebraicFamily
                hA.geometric_smooth_derivativeClosed_abelGeometricFamily.1
                hA.geometric_smooth_derivativeClosed_abelGeometricFamily.2.1
                hA.geometric_smooth_derivativeClosed_abelGeometricFamily.2.2
                hn old).carrier := by
  obtain ⟨hG, hsmooth, _hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  obtain ⟨h21, h22⟩ :=
    literalZeroSet_charbonnelTheorems21And22_of_meagreSelection_and_analyticStep
      hG hsmooth hUFF hselection hanalytic
  exact sardianProjection_projection_or_smallLevels_of_theorems21_22
    hA hUFF hn old U e hepos h21 h22 hUopen hUconvex hregular
      hbounded hnonempty

end AbelFormalization
