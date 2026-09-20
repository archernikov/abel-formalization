import AbelFormalization.CharbonnelAffineSectionRankInduction
import AbelFormalization.CharbonnelSection5ElementaryInputs

/-!
# The vertical incidence construction in Charbonnel section 5.3(a)

For `S ⊆ ℝ^(n+1)`, this file introduces one set in the coordinates

`((y,t),(x,r)) ∈ ℝ^(n+1) × ℝ^(n+1)`.

It records that `(y,t) ∈ S` and that `y` lies in the closed sup-norm ball
with centre `x` and radius `r`.  The ball condition is written as a finite
family of weak polynomial inequalities, including `0 ≤ r`.  Consequently
the incidence set belongs to the literal-zero Charbonnel closure whenever
`S` does, using only products, intersections, and the polynomial-sign bridge.

After fixing `(x,r)` by an affine slice, last-coordinate projection is a
continuous surjection onto
`charbonnelVerticalImageOver S (Metric.closedBall x r)`.  Thus WS5 for the
single incidence set supplies the uniform local vertical-component bound
used in Charbonnel 5.3(a).  The section generally has several points above
one last coordinate, so the needed comparison is stated as a projection,
not as a homeomorphism.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Polynomial coordinates for the moving closed ball -/

/-- The coordinate occupied by `y_i` in the layout `((y,t),(x,r))`. -/
def charbonnelVerticalIncidenceYIndex
    (n : ℕ) (i : Fin n) : Fin ((n + 1) + (n + 1)) :=
  Fin.castAdd (n + 1) (Fin.castAdd 1 i)

/-- The coordinate occupied by `x_i` in the layout `((y,t),(x,r))`. -/
def charbonnelVerticalIncidenceCenterIndex
    (n : ℕ) (i : Fin n) : Fin ((n + 1) + (n + 1)) :=
  Fin.natAdd (n + 1) (Fin.castAdd 1 i)

/-- The coordinate occupied by `r` in the layout `((y,t),(x,r))`. -/
def charbonnelVerticalIncidenceRadiusIndex
    (n : ℕ) : Fin ((n + 1) + (n + 1)) :=
  Fin.natAdd (n + 1) (Fin.last n)

/-- The weak polynomial inequality
`(y_i-x_i)^2 ≤ r^2` for the moving ball. -/
def charbonnelVerticalBallCoordinatePolynomial
    (n : ℕ) (i : Fin n) :
    MvPolynomial (Fin ((n + 1) + (n + 1))) ℝ :=
  MvPolynomial.X (charbonnelVerticalIncidenceRadiusIndex n) ^ 2 -
    (MvPolynomial.X (charbonnelVerticalIncidenceYIndex n i) -
      MvPolynomial.X (charbonnelVerticalIncidenceCenterIndex n i)) ^ 2

/-- The canonical point with coordinate layout `((y,t),(x,r))`. -/
def charbonnelVerticalIncidencePoint {n : ℕ}
    (y : RealEuclidean n) (t : ℝ)
    (x : RealEuclidean n) (r : ℝ) :
    RealEuclidean ((n + 1) + (n + 1)) :=
  realEuclideanAppend (charbonnelAppendLastCoordinate y t)
    (charbonnelAppendLastCoordinate x r)

@[simp]
theorem charbonnelVerticalIncidencePoint_yIndex
    {n : ℕ} (y : RealEuclidean n) (t : ℝ)
    (x : RealEuclidean n) (r : ℝ) (i : Fin n) :
    charbonnelVerticalIncidencePoint y t x r
        (charbonnelVerticalIncidenceYIndex n i) = y i := by
  simp [charbonnelVerticalIncidencePoint,
    charbonnelVerticalIncidenceYIndex]

@[simp]
theorem charbonnelVerticalIncidencePoint_centerIndex
    {n : ℕ} (y : RealEuclidean n) (t : ℝ)
    (x : RealEuclidean n) (r : ℝ) (i : Fin n) :
    charbonnelVerticalIncidencePoint y t x r
        (charbonnelVerticalIncidenceCenterIndex n i) = x i := by
  rw [charbonnelVerticalIncidencePoint,
    charbonnelVerticalIncidenceCenterIndex,
    realEuclideanAppend_natAdd]
  exact charbonnelAppendLastCoordinate_castAdd x r i

@[simp]
theorem charbonnelVerticalIncidencePoint_radiusIndex
    {n : ℕ} (y : RealEuclidean n) (t : ℝ)
    (x : RealEuclidean n) (r : ℝ) :
    charbonnelVerticalIncidencePoint y t x r
        (charbonnelVerticalIncidenceRadiusIndex n) = r := by
  rw [charbonnelVerticalIncidencePoint,
    charbonnelVerticalIncidenceRadiusIndex,
    realEuclideanAppend_natAdd]
  exact charbonnelAppendLastCoordinate_last x r

@[simp]
theorem charbonnelVerticalBallCoordinatePolynomial_eval_point
    {n : ℕ} (y : RealEuclidean n) (t : ℝ)
    (x : RealEuclidean n) (r : ℝ) (i : Fin n) :
    MvPolynomial.eval (charbonnelVerticalIncidencePoint y t x r)
        (charbonnelVerticalBallCoordinatePolynomial n i) =
      r ^ 2 - (y i - x i) ^ 2 := by
  simp [charbonnelVerticalBallCoordinatePolynomial]

/-- The semialgebraic moving-ball relation in `((y,t),(x,r))` coordinates.
The coordinate `t` is deliberately unused. -/
def charbonnelVariableClosedBallRelation (n : ℕ) :
    Set (RealEuclidean ((n + 1) + (n + 1))) :=
  {v | 0 ≤ MvPolynomial.eval v
      (MvPolynomial.X (charbonnelVerticalIncidenceRadiusIndex n))} ∩
    ⋂ i : Fin n,
      {v | 0 ≤ MvPolynomial.eval v
        (charbonnelVerticalBallCoordinatePolynomial n i)}

theorem polynomialSignConstructible_charbonnelVariableClosedBallRelation
    (n : ℕ) :
    PolynomialSignConstructible ((n + 1) + (n + 1))
      (charbonnelVariableClosedBallRelation n) := by
  have hnonnegative : ∀
      P : MvPolynomial (Fin ((n + 1) + (n + 1))) ℝ,
      PolynomialSignConstructible ((n + 1) + (n + 1))
        {v | 0 ≤ MvPolynomial.eval v P} := by
    intro P
    rw [show {v : RealEuclidean ((n + 1) + (n + 1)) |
          0 ≤ MvPolynomial.eval v P} =
        {v | MvPolynomial.eval v P = 0} ∪
          {v | 0 < MvPolynomial.eval v P} by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · intro hv
        rcases hv.eq_or_lt with hv | hv
        · exact Or.inl hv.symm
        · exact Or.inr hv
      · rintro (hv | hv)
        · exact hv.symm.le
        · exact hv.le]
    exact .union (.zero P) (.pos P)
  exact .inter
    (hnonnegative
      (MvPolynomial.X (charbonnelVerticalIncidenceRadiusIndex n)))
    (polynomialSignConstructible_iInter_fin _ fun i ↦
      hnonnegative (charbonnelVerticalBallCoordinatePolynomial n i))

/-- On canonical coordinates and for a nonnegative radius, the polynomial
moving-ball relation is exactly membership in the metric closed ball. -/
theorem charbonnelVerticalIncidencePoint_mem_variableClosedBallRelation_iff
    {n : ℕ} (y : RealEuclidean n) (t : ℝ)
    (x : RealEuclidean n) {r : ℝ} (hr : 0 ≤ r) :
    charbonnelVerticalIncidencePoint y t x r ∈
        charbonnelVariableClosedBallRelation n ↔
      y ∈ Metric.closedBall x r := by
  rw [closedBall_pi x hr]
  simp only [charbonnelVariableClosedBallRelation, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_iInter, MvPolynomial.eval_X,
    charbonnelVerticalIncidencePoint_radiusIndex,
    charbonnelVerticalBallCoordinatePolynomial_eval_point,
    Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall,
    Real.dist_eq]
  constructor
  · rintro ⟨_hr, hsquare⟩ i
    exact abs_le_of_sq_le_sq (sub_nonneg.mp (hsquare i)) hr
  · intro hcoordinate
    refine ⟨hr, ?_⟩
    intro i
    apply sub_nonneg.mpr
    have habs : |y i - x i| ≤ r := hcoordinate i
    have hsquare :=
      (sq_le_sq₀ (abs_nonneg (y i - x i)) hr).2 habs
    simpa only [sq_abs] using hsquare

/-! ## The incidence carrier and its Charbonnel membership -/

/-- The parameterized incidence carrier
`{((y,t),(x,r)) | (y,t) ∈ S ∧ y ∈ closedBall x r}`.

The displayed semantic description is exact on `0 ≤ r`, which is the
only part of the carrier used below. -/
def charbonnelVerticalIncidence {n : ℕ}
    (S : Set (RealEuclidean (n + 1))) :
    Set (RealEuclidean ((n + 1) + (n + 1))) :=
  realEuclideanSetProduct S Set.univ ∩
    charbonnelVariableClosedBallRelation n

theorem charbonnelVerticalIncidencePoint_mem_iff
    {n : ℕ} (S : Set (RealEuclidean (n + 1)))
    (y : RealEuclidean n) (t : ℝ)
    (x : RealEuclidean n) {r : ℝ} (hr : 0 ≤ r) :
    charbonnelVerticalIncidencePoint y t x r ∈
        charbonnelVerticalIncidence S ↔
      charbonnelAppendLastCoordinate y t ∈ S ∧
        y ∈ Metric.closedBall x r := by
  simp only [charbonnelVerticalIncidence, Set.mem_inter_iff,
    realEuclideanSetProduct, Set.mem_ofPred_eq,
    charbonnelVerticalIncidencePoint,
    realEuclideanTakeLeft_append,
    Set.mem_univ, and_true]
  change
    charbonnelAppendLastCoordinate y t ∈ S ∧
        charbonnelVerticalIncidencePoint y t x r ∈
          charbonnelVariableClosedBallRelation n ↔
      charbonnelAppendLastCoordinate y t ∈ S ∧
        y ∈ Metric.closedBall x r
  rw [charbonnelVerticalIncidencePoint_mem_variableClosedBallRelation_iff
    y t x hr]

/-- The moving vertical incidence carrier is constructed from `S` by WS3,
WS2, and WS1 (implemented by the corresponding description algebra). -/
theorem literalZeroSet_charbonnelClosure_verticalIncidence_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) (n + 1)) :
    charbonnelVerticalIncidence S ∈
      charbonnelClosure (literalZeroSetFamily G)
        ((n + 1) + (n + 1)) := by
  have huniv : (Set.univ : Set (RealEuclidean (n + 1))) ∈
      charbonnelClosure (literalZeroSetFamily G) (n + 1) :=
    ((polynomialSignConstructible_univ (n + 1)).isProjectedZeroSet hG)
      |>.mem_literalZeroSet_charbonnelClosure (by omega)
  have hproduct : realEuclideanSetProduct S
      (Set.univ : Set (RealEuclidean (n + 1))) ∈
      charbonnelClosure (literalZeroSetFamily G)
        ((n + 1) + (n + 1)) :=
    literalZeroSet_charbonnelClosure_product hG hsmooth hS huniv
  have hball : charbonnelVariableClosedBallRelation n ∈
      charbonnelClosure (literalZeroSetFamily G)
        ((n + 1) + (n + 1)) :=
    ((polynomialSignConstructible_charbonnelVariableClosedBallRelation n)
      |>.isProjectedZeroSet hG)
      |>.mem_literalZeroSet_charbonnelClosure (by omega)
  exact literalZeroSet_charbonnelClosure_inter hG hsmooth hproduct hball

/-! ## Fixed-parameter affine slices and their vertical projection -/

/-- The affine slice on which the right block is the fixed parameter pair
`(x,r)`. -/
def charbonnelVerticalIncidenceParameterSlice {n : ℕ}
    (x : RealEuclidean n) (r : ℝ) :
    AffineSubspace ℝ (RealEuclidean ((n + 1) + (n + 1))) :=
  ({charbonnelAppendLastCoordinate x r} :
      AffineSubspace ℝ (RealEuclidean (n + 1))).comap
    (realEuclideanTakeRightLinearMap (n + 1) (n + 1)).toAffineMap

@[simp]
theorem mem_charbonnelVerticalIncidenceParameterSlice_iff
    {n : ℕ} (x : RealEuclidean n) (r : ℝ)
    (v : RealEuclidean ((n + 1) + (n + 1))) :
    v ∈ charbonnelVerticalIncidenceParameterSlice x r ↔
      realEuclideanTakeRight v = charbonnelAppendLastCoordinate x r := by
  simp [charbonnelVerticalIncidenceParameterSlice]

/-- The fixed-parameter affine section of the incidence carrier. -/
def charbonnelVerticalIncidenceSection {n : ℕ}
    (S : Set (RealEuclidean (n + 1)))
    (x : RealEuclidean n) (r : ℝ) :
    Set (RealEuclidean ((n + 1) + (n + 1))) :=
  charbonnelVerticalIncidence S ∩
    (charbonnelVerticalIncidenceParameterSlice x r :
      Set (RealEuclidean ((n + 1) + (n + 1))))

theorem charbonnelVerticalIncidencePoint_mem_section_iff
    {n : ℕ} (S : Set (RealEuclidean (n + 1)))
    (y : RealEuclidean n) (t : ℝ)
    (x : RealEuclidean n) {r : ℝ} (hr : 0 ≤ r) :
    charbonnelVerticalIncidencePoint y t x r ∈
        charbonnelVerticalIncidenceSection S x r ↔
      charbonnelAppendLastCoordinate y t ∈ S ∧
        y ∈ Metric.closedBall x r := by
  constructor
  · intro hv
    exact
      (charbonnelVerticalIncidencePoint_mem_iff S y t x hr).mp hv.1
  · intro hv
    refine ⟨
      (charbonnelVerticalIncidencePoint_mem_iff S y t x hr).mpr hv, ?_⟩
    apply (mem_charbonnelVerticalIncidenceParameterSlice_iff x r _).mpr
    exact realEuclideanTakeRight_append
      (charbonnelAppendLastCoordinate y t)
      (charbonnelAppendLastCoordinate x r)

/-- Splitting an `(n+1)`-tuple after its first `n` coordinates and restoring
its last coordinate gives the original tuple. -/
@[simp]
theorem charbonnelAppendLastCoordinate_takeLeft_last
    {n : ℕ} (v : RealEuclidean (n + 1)) :
    charbonnelAppendLastCoordinate
        (realEuclideanTakeLeft (n := n) (m := 1) v)
        (v (Fin.last n)) = v := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [charbonnelAppendLastCoordinate_last]
  · rw [charbonnelAppendLastCoordinate_castSucc]
    have hj : j.castSucc = Fin.castAdd 1 j := Fin.ext rfl
    rw [hj]
    rfl

/-- Last-coordinate projection from the full incidence ambient space. -/
def charbonnelVerticalIncidenceValue {n : ℕ}
    (v : RealEuclidean ((n + 1) + (n + 1))) : ℝ :=
  realEuclideanTakeLeft v (Fin.last n)

@[simp]
theorem charbonnelVerticalIncidenceValue_point
    {n : ℕ} (y : RealEuclidean n) (t : ℝ)
    (x : RealEuclidean n) (r : ℝ) :
    charbonnelVerticalIncidenceValue
      (charbonnelVerticalIncidencePoint y t x r) = t := by
  simp [charbonnelVerticalIncidenceValue,
    charbonnelVerticalIncidencePoint]

theorem continuous_charbonnelVerticalIncidenceValue {n : ℕ} :
    Continuous (@charbonnelVerticalIncidenceValue n) := by
  change Continuous
    (fun v : RealEuclidean ((n + 1) + (n + 1)) ↦
      v (Fin.castAdd (n + 1) (Fin.last n)))
  exact continuous_apply (Fin.castAdd (n + 1) (Fin.last n))

/-- Every point of a fixed-parameter section projects into the corresponding
vertical image. -/
theorem charbonnelVerticalIncidenceValue_mem_verticalImage
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (x : RealEuclidean n) {r : ℝ} (hr : 0 ≤ r)
    {v : RealEuclidean ((n + 1) + (n + 1))}
    (hv : v ∈ charbonnelVerticalIncidenceSection S x r) :
    charbonnelVerticalIncidenceValue v ∈
      charbonnelVerticalImageOver S (Metric.closedBall x r) := by
  let y : RealEuclidean n :=
    realEuclideanTakeLeft
      (realEuclideanTakeLeft v : RealEuclidean (n + 1))
  have hright :
      realEuclideanTakeRight (n := n + 1) (m := n + 1) v =
      charbonnelAppendLastCoordinate x r :=
    (mem_charbonnelVerticalIncidenceParameterSlice_iff x r v).mp hv.2
  have hvPoint : v = charbonnelVerticalIncidencePoint y
      (charbonnelVerticalIncidenceValue v) x r := by
    calc
      v = realEuclideanAppend
          (realEuclideanTakeLeft (n := n + 1) (m := n + 1) v)
          (realEuclideanTakeRight (n := n + 1) (m := n + 1) v) :=
        (realEuclideanAppend_takeLeft_takeRight
          (n := n + 1) (m := n + 1) v).symm
      _ = realEuclideanAppend
          (charbonnelAppendLastCoordinate y
            (charbonnelVerticalIncidenceValue v))
          (charbonnelAppendLastCoordinate x r) := by
        simp only [y, charbonnelVerticalIncidenceValue,
          charbonnelAppendLastCoordinate_takeLeft_last, hright]
      _ = charbonnelVerticalIncidencePoint y
          (charbonnelVerticalIncidenceValue v) x r := rfl
  rw [hvPoint] at hv
  obtain ⟨hS, hball⟩ :=
    (charbonnelVerticalIncidencePoint_mem_section_iff
      S y (charbonnelVerticalIncidenceValue v) x hr).mp hv
  exact ⟨y, hball, hS⟩

/-- The continuous last-coordinate projection from a fixed incidence section
onto its vertical image. -/
def charbonnelVerticalIncidenceSectionProjection
    {n : ℕ} (S : Set (RealEuclidean (n + 1)))
    (x : RealEuclidean n) {r : ℝ} (hr : 0 ≤ r) :
    charbonnelVerticalIncidenceSection S x r →
      charbonnelVerticalImageOver S (Metric.closedBall x r) :=
  fun v ↦ ⟨charbonnelVerticalIncidenceValue v,
    charbonnelVerticalIncidenceValue_mem_verticalImage x hr v.property⟩

theorem continuous_charbonnelVerticalIncidenceSectionProjection
    {n : ℕ} (S : Set (RealEuclidean (n + 1)))
    (x : RealEuclidean n) {r : ℝ} (hr : 0 ≤ r) :
    Continuous
      (charbonnelVerticalIncidenceSectionProjection S x hr) := by
  apply Continuous.subtype_mk
  change Continuous
    (fun v : charbonnelVerticalIncidenceSection S x r ↦
      charbonnelVerticalIncidenceValue (v :
        RealEuclidean ((n + 1) + (n + 1))))
  exact continuous_charbonnelVerticalIncidenceValue.comp continuous_subtype_val

theorem surjective_charbonnelVerticalIncidenceSectionProjection
    {n : ℕ} (S : Set (RealEuclidean (n + 1)))
    (x : RealEuclidean n) {r : ℝ} (hr : 0 ≤ r) :
    Function.Surjective
      (charbonnelVerticalIncidenceSectionProjection S x hr) := by
  rintro ⟨t, ht⟩
  obtain ⟨y, hyBall, hyS⟩ := ht
  let v := charbonnelVerticalIncidencePoint y t x r
  have hv : v ∈ charbonnelVerticalIncidenceSection S x r :=
    (charbonnelVerticalIncidencePoint_mem_section_iff
      S y t x hr).mpr ⟨hyS, hyBall⟩
  refine ⟨⟨v, hv⟩, ?_⟩
  apply Subtype.ext
  simp only [charbonnelVerticalIncidenceSectionProjection, v,
    charbonnelVerticalIncidenceValue_point]

/-- The vertical image cannot have more connected components than its full
fixed-parameter incidence section. -/
theorem enatCard_connectedComponents_verticalImage_le_incidenceSection
    {n : ℕ} (S : Set (RealEuclidean (n + 1)))
    (x : RealEuclidean n) {r : ℝ} (hr : 0 ≤ r) :
    ENat.card (ConnectedComponents
      (charbonnelVerticalImageOver S (Metric.closedBall x r) : Set ℝ)) ≤
    ENat.card (ConnectedComponents
      (charbonnelVerticalIncidenceSection S x r :
        Set (RealEuclidean ((n + 1) + (n + 1))))) := by
  exact enatCard_connectedComponents_le_of_continuous_surjective
    (continuous_charbonnelVerticalIncidenceSectionProjection S x hr)
    (surjective_charbonnelVerticalIncidenceSectionProjection S x hr)

/-! ## WS5 gives Charbonnel's uniform local component bound -/

/-- Charbonnel 5.3(a): WS5 applied to the single moving-ball incidence set
uniformly bounds the components of every positive-radius local vertical
image.  All closure membership used to invoke WS5 was proved above from the
literal-zero description algebra. -/
theorem literalZeroSet_charbonnelClosure_uniformLocalVerticalComponentBound
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n : ℕ} {S : Set (RealEuclidean (n + 1))}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) (n + 1)) :
    CharbonnelUniformLocalVerticalComponentBound S := by
  have hincidence : charbonnelVerticalIncidence S ∈
      charbonnelClosure (literalZeroSetFamily G)
        ((n + 1) + (n + 1)) :=
    literalZeroSet_charbonnelClosure_verticalIncidence_mem hG hsmooth hS
  obtain ⟨N, hN⟩ :=
    literalZeroSet_charbonnelClosure_ws5_affineSections
      hG hsmooth hUFF (by omega) hincidence
  refine ⟨N, ?_⟩
  intro x r hr
  exact
    (enatCard_connectedComponents_verticalImage_le_incidenceSection
      S x hr.le).trans (by
        have hsection := hN (charbonnelVerticalIncidenceParameterSlice x r)
        change ENat.card (ConnectedComponents
          (charbonnelVerticalIncidenceSection S x r :
            Set (RealEuclidean ((n + 1) + (n + 1))))) ≤
              (N : ℕ∞) at hsection
        exact hsection)

end AbelFormalization
