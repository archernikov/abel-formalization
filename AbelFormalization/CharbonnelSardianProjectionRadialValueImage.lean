import AbelFormalization.CharbonnelSardianProjectionFromAboveLevelAlternative
import AbelFormalization.CharbonnelComplementPipeline
import AbelFormalization.CharbonnelSection5ElementaryInputs

/-!
# The radial value image belongs to the literal-zero Charbonnel closure

The source applies WS5 to the radial image of a fixed old tuple fiber.  WS1
through WS4 build the fiber and an equation graph; the Charbonnel closure's
separate projection constructor then puts the scalar image in the same weak
family.  Membership of the visible set `U` is explicit: compactness by
itself does not imply weak-family membership.  No complement or projected
boundary approximation is used.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- One literal-zero residual for all fixed old tuple levels. -/
def sardianProjectionFixedOldTupleResidual
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (e : RealEuclidean (q + 1)) :
    RealEuclideanFunction (n + (q + 1)) :=
  fun v ↦ ∑ i : Fin (q + 1),
    (sardianProjectionOldTuple old v i - e i) ^ 2

theorem sardianProjectionFixedOldTupleResidual_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (e : RealEuclidean (q + 1)) :
    sardianProjectionFixedOldTupleResidual old e ∈ G (n + (q + 1)) := by
  let square : Fin (q + 1) → RealEuclideanFunction (n + (q + 1)) :=
    fun i v ↦ (sardianProjectionOldTuple old v i - e i) ^ 2
  have hsquare : ∀ i ∈ (Finset.univ : Finset (Fin (q + 1))),
      square i ∈ G (n + (q + 1)) := by
    intro i _
    have hcomponent := (sardianProjectionOldTuple_inFamily hG old) i
    have hconstant := hG.const_mem (n := n + (q + 1)) (e i)
    have hdifference := hG.sub_mem hcomponent hconstant
    simpa [square] using hG.sq_mem hdifference
  have hsum := hG.finset_sum_mem Finset.univ square hsquare
  convert hsum using 1
  funext v
  simp [sardianProjectionFixedOldTupleResidual,
    Finset.sum_apply, square]

@[simp]
theorem sardianProjectionFixedOldTupleResidual_eq_zero_iff
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (e : RealEuclidean (q + 1))
    (v : RealEuclidean (n + (q + 1))) :
    sardianProjectionFixedOldTupleResidual old e v = 0 ↔
      ∀ i : Fin (q + 1), sardianProjectionOldTuple old v i = e i := by
  rw [sardianProjectionFixedOldTupleResidual,
    Finset.sum_sq_eq_zero_iff]
  simp only [Finset.mem_univ, forall_const, sub_eq_zero]

/-- The named old fiber is in the literal-zero Charbonnel closure when its
visible set is already in that closure.  Fixed equation levels cost only one
literal-zero generator and an intersection. -/
theorem sardianProjectionOldTupleFiber_mem_literalZeroCharbonnelClosure
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (hU : U ∈ charbonnelClosure (literalZeroSetFamily G) n)
    (e : RealEuclidean (q + 1)) :
    sardianProjectionOldTupleFiber old U e ∈
      charbonnelClosure (literalZeroSetFamily G) (n + (q + 1)) := by
  let C := charbonnelClosure (literalZeroSetFamily G)
  let hC : PositiveArityWeakSetStructure C :=
    literalZeroSet_charbonnelClosure_positiveArityWeakSetStructure
      hG hsmooth
  have huniv : (Set.univ : Set (RealEuclidean (q + 1))) ∈ C (q + 1) :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_univ (q + 1))
  have hproduct :
      realEuclideanSetProduct U
        (Set.univ : Set (RealEuclidean (q + 1))) ∈ C (n + (q + 1)) :=
    hC.ws3_prod hn (by omega) hU huniv
  let E : Set (RealEuclidean (n + (q + 1))) :=
    {v | sardianProjectionFixedOldTupleResidual old e v = 0}
  have hEbase : E ∈ literalZeroSetFamily G (n + (q + 1)) :=
    ⟨sardianProjectionFixedOldTupleResidual old e,
      sardianProjectionFixedOldTupleResidual_mem hG old e, rfl⟩
  have hE : E ∈ C (n + (q + 1)) :=
    mem_charbonnelClosure_of_mem (by omega) hEbase
  have hfiberEq :
      sardianProjectionOldTupleFiber old U e =
        realEuclideanSetProduct U
          (Set.univ : Set (RealEuclidean (q + 1))) ∩ E := by
    ext v
    simp only [sardianProjectionOldTupleFiber,
      realEuclideanSetProduct, E, mem_setOf_eq, mem_inter_iff,
      mem_univ, and_true,
      sardianProjectionFixedOldTupleResidual_eq_zero_iff]
  rw [hfiberEq]
  exact hC.ws1_inter (by omega) hproduct hE

/-- Polynomial-denominator graph equation in scalar-first coordinates.
The denominator is positive, so its zero locus is the graph of the exact
radial reciprocal used in the projected constituent. -/
def sardianProjectionRadialValueGraphResidual (n q : ℕ) :
    RealEuclideanFunction (1 + (n + (q + 1))) :=
  fun w ↦ (realEuclideanTakeLeft w 0) *
    sardianProjectionRadialDenominator n q (realEuclideanTakeRight w) - 1

theorem sardianProjectionRadialValueGraphResidual_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G) (n q : ℕ) :
    sardianProjectionRadialValueGraphResidual n q ∈
      G (1 + (n + (q + 1))) := by
  let D := n + (q + 1)
  have hdenominator := hG.affine_comp
    (sardianProjectionRadialDenominator_mem hG n q)
    (realEuclideanTakeRightLinearMap 1 D).toAffineMap
  have hdenominator' :
      (fun w : RealEuclidean (1 + D) ↦
        sardianProjectionRadialDenominator n q
          (realEuclideanTakeRight w)) ∈ G (1 + D) := by
    change (fun w : RealEuclidean (1 + D) ↦
      sardianProjectionRadialDenominator n q
        (realEuclideanTakeRight w)) ∈ G (1 + D) at hdenominator
    exact hdenominator
  have hscalar :
      (fun w : RealEuclidean (1 + D) ↦
        realEuclideanTakeLeft w 0) ∈ G (1 + D) := by
    simpa [realEuclideanTakeLeft] using
      (hG.polynomial (MvPolynomial.X (Fin.castAdd D (0 : Fin 1))))
  have hmul := hG.mul hscalar hdenominator'
  have hsub := hG.sub_mem hmul (hG.const_mem (n := 1 + D) 1)
  convert hsub using 1
  funext w
  simp [sardianProjectionRadialValueGraphResidual,
    Pi.mul_apply, Pi.sub_apply]

@[simp]
theorem sardianProjectionRadialValueGraphResidual_append_eq_zero_iff
    (n q : ℕ) (t : RealEuclidean 1)
    (v : RealEuclidean (n + (q + 1))) :
    sardianProjectionRadialValueGraphResidual n q
        (realEuclideanAppend t v) = 0 ↔
      t 0 = sardianProjectionRadialReciprocal n q v := by
  have hdenNonzero :
      sardianProjectionRadialDenominator n q v ≠ 0 :=
    ne_of_gt (sardianProjectionRadialDenominator_pos n q v)
  simp only [sardianProjectionRadialValueGraphResidual,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append,
    sub_eq_zero, sardianProjectionRadialReciprocal]
  exact mul_eq_one_iff_eq_inv₀ hdenNonzero

/-- Positive scalar-first radial values of the named old tuple fiber. -/
def sardianProjectionRadialValueImage
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1)) :
    Set (RealEuclidean 1) :=
  {t | ∃ v ∈ sardianProjectionOldTupleFiber old U e,
    t 0 = sardianProjectionRadialReciprocal n q v}

theorem sardianProjectionRadialValueImage_pos
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1))
    {t : RealEuclidean 1}
    (ht : t ∈ sardianProjectionRadialValueImage old U e) :
    0 < t 0 := by
  obtain ⟨v, _hv, hlevel⟩ := ht
  rw [hlevel]
  change 0 < (sardianProjectionRadialDenominator n q v)⁻¹
  exact inv_pos.mpr (sardianProjectionRadialDenominator_pos n q v)

/-- The radial image is a member of the actual prior weak-stage family
`charbonnelClosure (literalZeroSetFamily G)`.  This uses its independently
proved projection constructor; WS1--WS4 alone have no projection field. -/
theorem sardianProjectionRadialValueImage_mem_literalZeroCharbonnelClosure
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (hU : U ∈ charbonnelClosure (literalZeroSetFamily G) n)
    (e : RealEuclidean (q + 1)) :
    sardianProjectionRadialValueImage old U e ∈
      charbonnelClosure (literalZeroSetFamily G) 1 := by
  let D := n + (q + 1)
  let C := charbonnelClosure (literalZeroSetFamily G)
  let hC : PositiveArityWeakSetStructure C :=
    literalZeroSet_charbonnelClosure_positiveArityWeakSetStructure
      hG hsmooth
  let fiber := sardianProjectionOldTupleFiber old U e
  have hfiber : fiber ∈ C D :=
    sardianProjectionOldTupleFiber_mem_literalZeroCharbonnelClosure
      hG hsmooth hn old U hU e
  have hunivOne : (Set.univ : Set (RealEuclidean 1)) ∈ C 1 :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_univ 1)
  have hproduct :
      realEuclideanSetProduct
        (Set.univ : Set (RealEuclidean 1)) fiber ∈ C (1 + D) :=
    hC.ws3_prod (by omega) (by omega) hunivOne hfiber
  let E : Set (RealEuclidean (1 + D)) :=
    {w | sardianProjectionRadialValueGraphResidual n q w = 0}
  have hEbase : E ∈ literalZeroSetFamily G (1 + D) :=
    ⟨sardianProjectionRadialValueGraphResidual n q,
      sardianProjectionRadialValueGraphResidual_mem hG n q, rfl⟩
  have hE : E ∈ C (1 + D) :=
    mem_charbonnelClosure_of_mem (by omega) hEbase
  let A : Set (RealEuclidean (1 + D)) :=
    realEuclideanSetProduct (Set.univ : Set (RealEuclidean 1)) fiber ∩ E
  have hA : A ∈ C (1 + D) :=
    hC.ws1_inter (by omega) hproduct hE
  have hprojection :
      realEuclideanExistentialProjection A ∈ C 1 :=
    charbonnelClosure_projection (by omega) hA
  have hImageEq :
      realEuclideanExistentialProjection A =
        sardianProjectionRadialValueImage old U e := by
    ext t
    change (∃ v : RealEuclidean D,
      realEuclideanAppend t v ∈ A) ↔
        (∃ v ∈ fiber,
          t 0 = sardianProjectionRadialReciprocal n q v)
    constructor
    · rintro ⟨v, ⟨⟨_huniv, hvfiber⟩, hgraph⟩⟩
      have hvfiber' : v ∈ fiber := by
        simpa only [realEuclideanTakeRight_append] using hvfiber
      have hlevel : t 0 = sardianProjectionRadialReciprocal n q v :=
        (sardianProjectionRadialValueGraphResidual_append_eq_zero_iff
          n q t v).mp hgraph
      exact ⟨v, hvfiber', hlevel⟩
    · rintro ⟨v, hvfiber, hlevel⟩
      refine ⟨v, ⟨⟨Set.mem_univ _, ?_⟩, ?_⟩⟩
      · simpa only [realEuclideanTakeRight_append] using hvfiber
      · exact (sardianProjectionRadialValueGraphResidual_append_eq_zero_iff
          n q t v).mpr hlevel
  rw [← hImageEq]
  exact hprojection

/-- Once the maintained WS5 input (uniform fiber finiteness) is available,
the scalar radial range has a finite point-and-interval decomposition. -/
theorem sardianProjectionRadialValueImage_unaryPieceDecomposable
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (hU : U ∈ charbonnelClosure (literalZeroSetFamily G) n)
    (e : RealEuclidean (q + 1)) :
    UnaryPieceDecomposable
      (realEuclideanOneCoordinateImage
        (sardianProjectionRadialValueImage old U e)) := by
  let hC :=
    literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF
  exact hC.coordinateImage_unaryPieceDecomposable
    (sardianProjectionRadialValueImage_mem_literalZeroCharbonnelClosure
      hG hsmooth hn old U hU e)

end AbelFormalization
