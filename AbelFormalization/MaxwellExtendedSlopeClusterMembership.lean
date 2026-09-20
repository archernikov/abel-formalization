import AbelFormalization.MaxwellExtendedSlopeClusters
import AbelFormalization.MaxwellDifferenceQuotientTraceTopology
import AbelFormalization.CharbonnelLinearEquivClosure
import AbelFormalization.CharbonnelTraceMembership
import Mathlib.LinearAlgebra.Pi

/-!
# Charbonnel membership for Maxwell's extended slope clusters

This file supplies the set-family algebra missing from the definitions in
`MaxwellPseudofunction` and `MaxwellExtendedSlopeClusters`.  Its standing
hypothesis is deliberately the weak-structure interface on the *generated*
Charbonnel family.  From WS1--WS3 it first derives arbitrary linear
pullbacks, by adjoining the value of the linear map, imposing its polynomial
graph equation, and projecting.  The remainder applies that calculus to the
difference-quotient and reciprocal relations and then uses the native
Charbonnel constructors for zero sections, unions, and closures.

No selection, compactness, or slope-cluster coverage assertion is used here.
Those are analytic inputs to the later Maxwell pseudofunction argument rather
than membership facts.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

theorem maxwellFinArity_pos {p : ℕ} (i : Fin p) : 0 < p :=
  lt_of_le_of_lt (Nat.zero_le i.val) i.isLt

/-! ## Linear pullbacks derived from the weak-family clauses -/

/-- The sum-of-squares polynomial cutting out the graph of a linear map in
flat `(source,target)` coordinates. -/
def maxwellLinearGraphResidualPolynomial {m n : ℕ}
    (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n) :
    MvPolynomial (Fin (m + n)) ℝ :=
  ∑ i : Fin n,
    ((∑ j : Fin m,
        MvPolynomial.C (L (Pi.single j 1) i) *
          MvPolynomial.X (Fin.castAdd n j)) -
      MvPolynomial.X (Fin.natAdd m i)) ^ 2

/-- A scalar coordinate of a linear map is its dot product with the values
of the map on the standard coordinate directions. -/
theorem maxwellLinearMap_apply_eq_sum {m n : ℕ}
    (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n)
    (x : RealEuclidean m) (i : Fin n) :
    L x i = ∑ j : Fin m, L (Pi.single j 1) i * x j := by
  classical
  let Li : RealEuclidean m →ₗ[ℝ] ℝ :=
    { toFun := fun v ↦ L v i
      map_add' := by
        intro v w
        simp
      map_smul' := by
        intro c v
        simp }
  have hsingle (j : Fin m) :
      (fun k ↦ if j = k then (1 : ℝ) else 0) = Pi.single j 1 := by
    ext k
    simp [Pi.single_apply, eq_comm]
  simpa only [Li, hsingle, smul_eq_mul, mul_comm] using!
    LinearMap.pi_apply_eq_sum_univ Li x

@[simp]
theorem maxwellLinearGraphResidualPolynomial_eval_append {m n : ℕ}
    (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n)
    (x : RealEuclidean m) (y : RealEuclidean n) :
    MvPolynomial.eval (realEuclideanAppend x y)
        (maxwellLinearGraphResidualPolynomial L) =
      ∑ i : Fin n, (L x i - y i) ^ 2 := by
  classical
  simp only [maxwellLinearGraphResidualPolynomial, map_sum,
    MvPolynomial.eval_pow, map_sub, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, realEuclideanAppend_castAdd,
    realEuclideanAppend_natAdd]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [maxwellLinearMap_apply_eq_sum L x i]

@[simp]
theorem maxwellLinearGraphResidualPolynomial_eval_append_eq_zero_iff
    {m n : ℕ} (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n)
    (x : RealEuclidean m) (y : RealEuclidean n) :
    MvPolynomial.eval (realEuclideanAppend x y)
        (maxwellLinearGraphResidualPolynomial L) = 0 ↔
      L x = y := by
  rw [maxwellLinearGraphResidualPolynomial_eval_append,
    Finset.sum_sq_eq_zero_iff]
  constructor
  · intro h
    funext i
    exact sub_eq_zero.mp (h i (Finset.mem_univ i))
  · intro h i _hi
    exact sub_eq_zero.mpr (congrFun h i)

/-- The graph constraint used in the incidence presentation of a linear
pullback. -/
def maxwellLinearGraphConstraint {m n : ℕ}
    (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n) :
    Set (RealEuclidean (m + n)) :=
  {w | MvPolynomial.eval w (maxwellLinearGraphResidualPolynomial L) = 0}

theorem polynomialSignConstructible_maxwellLinearGraphConstraint
    {m n : ℕ} (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n) :
    PolynomialSignConstructible (m + n)
      (maxwellLinearGraphConstraint L) :=
  .zero (maxwellLinearGraphResidualPolynomial L)

@[simp]
theorem realEuclideanAppend_mem_maxwellLinearGraphConstraint_iff
    {m n : ℕ} (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n)
    (x : RealEuclidean m) (y : RealEuclidean n) :
    realEuclideanAppend x y ∈ maxwellLinearGraphConstraint L ↔
      L x = y := by
  exact maxwellLinearGraphResidualPolynomial_eval_append_eq_zero_iff L x y

/-- Incidence presentation of `L ⁻¹' A`: the target value is an
existentially quantified final block. -/
def maxwellLinearPreimageIncidence {m n : ℕ}
    (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n)
    (A : Set (RealEuclidean n)) : Set (RealEuclidean (m + n)) :=
  realEuclideanSetProduct Set.univ A ∩ maxwellLinearGraphConstraint L

theorem realEuclideanExistentialProjection_maxwellLinearPreimageIncidence
    {m n : ℕ} (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n)
    (A : Set (RealEuclidean n)) :
    realEuclideanExistentialProjection
        (maxwellLinearPreimageIncidence L A) = L ⁻¹' A := by
  ext x
  simp [realEuclideanExistentialProjection,
    maxwellLinearPreimageIncidence, realEuclideanSetProduct]

/-- WS1--WS3 and the polynomial-sign clause imply closure under arbitrary
linear pullback in positive source and target arities. -/
theorem PositiveArityWeakSetStructure.linear_preimage_mem
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure S n)
    (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n) :
    L ⁻¹' A ∈ charbonnelClosure S m := by
  have huniv : (Set.univ : Set (RealEuclidean m)) ∈
      charbonnelClosure S m :=
    hC.ws2_polynomialSign hm (polynomialSignConstructible_univ m)
  have hproduct : realEuclideanSetProduct
      (Set.univ : Set (RealEuclidean m)) A ∈
        charbonnelClosure S (m + n) :=
    hC.ws3_prod hm hn huniv hA
  have hgraph : maxwellLinearGraphConstraint L ∈
      charbonnelClosure S (m + n) :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_maxwellLinearGraphConstraint L)
  have hincidence : maxwellLinearPreimageIncidence L A ∈
      charbonnelClosure S (m + n) :=
    hC.ws1_inter (by omega) hproduct hgraph
  rw [← realEuclideanExistentialProjection_maxwellLinearPreimageIncidence
    L A]
  exact charbonnelClosure_projection hm hincidence

/-! ## The directional difference-quotient relation -/

/-- Read the original base point from quotient-witness coordinates
`(((x,epsilon),y),(z₁,z₂))`. -/
def maxwellQuotientWitnessBaseLinearMap (p : ℕ) :
    RealEuclidean (((p + 1) + 1) + 2) →ₗ[ℝ] RealEuclidean p :=
  (realEuclideanTakeLeftLinearMap p 1).comp
    ((realEuclideanTakeLeftLinearMap (p + 1) 1).comp
      (realEuclideanTakeLeftLinearMap ((p + 1) + 1) 2))

/-- Read the shifted base point `x + epsilon eᵢ` from quotient-witness
coordinates. -/
def maxwellQuotientWitnessShiftedBaseLinearMap (p : ℕ) (i : Fin p) :
    RealEuclidean (((p + 1) + 1) + 2) →ₗ[ℝ] RealEuclidean p where
  toFun w :=
    maxwellQuotientWitnessBaseLinearMap p w +
      (realEuclideanTakeRight (n := p) (m := 1)
          (realEuclideanTakeLeft (n := p + 1) (m := 1)
            (realEuclideanTakeLeft (n := (p + 1) + 1) (m := 2) w)) 0) •
        (Pi.single i 1 : RealEuclidean p)
  map_add' := by
    intro v w
    funext j
    simp [maxwellQuotientWitnessBaseLinearMap,
      realEuclideanTakeLeft, realEuclideanTakeRight,
      add_smul]
    ring
  map_smul' := by
    intro c v
    funext j
    simp [maxwellQuotientWitnessBaseLinearMap,
      realEuclideanTakeLeft, realEuclideanTakeRight,
      smul_add, mul_smul]
    ring

/-- Read `(x,z₁)` from quotient-witness coordinates. -/
def maxwellQuotientWitnessFirstRelationLinearMap (p : ℕ) :
    RealEuclidean (((p + 1) + 1) + 2) →ₗ[ℝ] RealEuclidean (p + 1) where
  toFun w := realEuclideanAppend
    (maxwellQuotientWitnessBaseLinearMap p w)
    (fun _ : Fin 1 ↦
      realEuclideanTakeRight (n := (p + 1) + 1) (m := 2) w 0)
  map_add' := by
    intro v w
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [maxwellQuotientWitnessBaseLinearMap,
        realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [maxwellQuotientWitnessBaseLinearMap,
        realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

/-- Read `(x + epsilon eᵢ,z₂)` from quotient-witness coordinates. -/
def maxwellQuotientWitnessSecondRelationLinearMap (p : ℕ) (i : Fin p) :
    RealEuclidean (((p + 1) + 1) + 2) →ₗ[ℝ] RealEuclidean (p + 1) where
  toFun w := realEuclideanAppend
    (maxwellQuotientWitnessShiftedBaseLinearMap p i w)
    (fun _ : Fin 1 ↦
      realEuclideanTakeRight (n := (p + 1) + 1) (m := 2) w 1)
  map_add' := by
    intro v w
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [maxwellQuotientWitnessShiftedBaseLinearMap,
        maxwellQuotientWitnessBaseLinearMap, realEuclideanAppend,
        realEuclideanTakeLeft, realEuclideanTakeRight, add_smul]
      <;> ring
  map_smul' := by
    intro c v
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [maxwellQuotientWitnessShiftedBaseLinearMap,
        maxwellQuotientWitnessBaseLinearMap, realEuclideanAppend,
        realEuclideanTakeLeft, realEuclideanTakeRight,
        smul_add, mul_smul]
      <;> ring

@[simp]
theorem maxwellQuotientWitnessBaseLinearMap_append
    {p : ℕ} (x : RealEuclidean p) (epsilon y : ℝ)
    (z : RealEuclidean 2) :
    maxwellQuotientWitnessBaseLinearMap p
        (realEuclideanAppend
          (realEuclideanAppend
            (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
            (fun _ : Fin 1 ↦ y)) z) = x := by
  change realEuclideanTakeLeft
      (n := p) (m := 1)
      (realEuclideanTakeLeft
        (n := p + 1) (m := 1)
        (realEuclideanTakeLeft
          (n := (p + 1) + 1) (m := 2)
          (realEuclideanAppend
            (realEuclideanAppend
              (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
              (fun _ : Fin 1 ↦ y)) z))) = x
  rw [realEuclideanTakeLeft_append, realEuclideanTakeLeft_append,
    realEuclideanTakeLeft_append]

@[simp]
theorem maxwellQuotientWitnessShiftedBaseLinearMap_append
    {p : ℕ} (i : Fin p) (x : RealEuclidean p) (epsilon y : ℝ)
    (z : RealEuclidean 2) :
    maxwellQuotientWitnessShiftedBaseLinearMap p i
        (realEuclideanAppend
          (realEuclideanAppend
            (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
            (fun _ : Fin 1 ↦ y)) z) =
      x + epsilon • (Pi.single i 1 : RealEuclidean p) := by
  change maxwellQuotientWitnessBaseLinearMap p
      (realEuclideanAppend
        (realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
          (fun _ : Fin 1 ↦ y)) z) +
      (realEuclideanTakeRight (n := p) (m := 1)
        (realEuclideanTakeLeft (n := p + 1) (m := 1)
          (realEuclideanTakeLeft (n := (p + 1) + 1) (m := 2)
            (realEuclideanAppend
              (realEuclideanAppend
                (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
                (fun _ : Fin 1 ↦ y)) z))) 0) •
        (Pi.single i 1 : RealEuclidean p) = _
  rw [maxwellQuotientWitnessBaseLinearMap_append,
    realEuclideanTakeLeft_append, realEuclideanTakeLeft_append,
    realEuclideanTakeRight_append]

@[simp]
theorem maxwellQuotientWitnessFirstRelationLinearMap_append
    {p : ℕ} (x : RealEuclidean p) (epsilon y : ℝ)
    (z : RealEuclidean 2) :
    maxwellQuotientWitnessFirstRelationLinearMap p
        (realEuclideanAppend
          (realEuclideanAppend
            (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
            (fun _ : Fin 1 ↦ y)) z) =
      realEuclideanAppend x (fun _ : Fin 1 ↦ z 0) := by
  change realEuclideanAppend
      (maxwellQuotientWitnessBaseLinearMap p
        (realEuclideanAppend
          (realEuclideanAppend
            (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
            (fun _ : Fin 1 ↦ y)) z))
      (fun _ : Fin 1 ↦
        realEuclideanTakeRight (n := (p + 1) + 1) (m := 2)
          (realEuclideanAppend
            (realEuclideanAppend
              (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
              (fun _ : Fin 1 ↦ y)) z) 0) = _
  rw [maxwellQuotientWitnessBaseLinearMap_append,
    realEuclideanTakeRight_append]

@[simp]
theorem maxwellQuotientWitnessSecondRelationLinearMap_append
    {p : ℕ} (i : Fin p) (x : RealEuclidean p) (epsilon y : ℝ)
    (z : RealEuclidean 2) :
    maxwellQuotientWitnessSecondRelationLinearMap p i
        (realEuclideanAppend
          (realEuclideanAppend
            (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
            (fun _ : Fin 1 ↦ y)) z) =
      realEuclideanAppend
        (x + epsilon • (Pi.single i 1 : RealEuclidean p))
        (fun _ : Fin 1 ↦ z 1) := by
  change realEuclideanAppend
      (maxwellQuotientWitnessShiftedBaseLinearMap p i
        (realEuclideanAppend
          (realEuclideanAppend
            (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
            (fun _ : Fin 1 ↦ y)) z))
      (fun _ : Fin 1 ↦
        realEuclideanTakeRight (n := (p + 1) + 1) (m := 2)
          (realEuclideanAppend
            (realEuclideanAppend
              (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
              (fun _ : Fin 1 ↦ y)) z) 1) = _
  rw [maxwellQuotientWitnessShiftedBaseLinearMap_append,
    realEuclideanTakeRight_append]

/-- The coordinate occupied by `epsilon` in
`(((x,epsilon),y),(z₁,z₂))`. -/
def maxwellQuotientWitnessStepIndex (p : ℕ) :
    Fin (((p + 1) + 1) + 2) :=
  Fin.castAdd 2 (Fin.castAdd 1 (Fin.last p))

/-- The coordinate occupied by the slope `y`. -/
def maxwellQuotientWitnessSlopeIndex (p : ℕ) :
    Fin (((p + 1) + 1) + 2) :=
  Fin.castAdd 2 (Fin.last (p + 1))

/-- The coordinate occupied by `z₁`. -/
def maxwellQuotientWitnessFirstValueIndex (p : ℕ) :
    Fin (((p + 1) + 1) + 2) :=
  Fin.natAdd ((p + 1) + 1) 0

/-- The coordinate occupied by `z₂`. -/
def maxwellQuotientWitnessSecondValueIndex (p : ℕ) :
    Fin (((p + 1) + 1) + 2) :=
  Fin.natAdd ((p + 1) + 1) 1

/-- The polynomial equation `epsilon*y = z₂-z₁`. -/
def maxwellQuotientWitnessEquationPolynomial (p : ℕ) :
    MvPolynomial (Fin (((p + 1) + 1) + 2)) ℝ :=
  MvPolynomial.X (maxwellQuotientWitnessStepIndex p) *
      MvPolynomial.X (maxwellQuotientWitnessSlopeIndex p) -
    (MvPolynomial.X (maxwellQuotientWitnessSecondValueIndex p) -
      MvPolynomial.X (maxwellQuotientWitnessFirstValueIndex p))

/-- The purely semialgebraic part of the quotient incidence: nonzero step
and the cross-multiplied quotient equation. -/
def maxwellQuotientWitnessConstraint (p : ℕ) :
    Set (RealEuclidean (((p + 1) + 1) + 2)) :=
  ({w | 0 < MvPolynomial.eval w
      (MvPolynomial.X (maxwellQuotientWitnessStepIndex p))} ∪
    {w | MvPolynomial.eval w
      (MvPolynomial.X (maxwellQuotientWitnessStepIndex p)) < 0}) ∩
    {w | MvPolynomial.eval w
      (maxwellQuotientWitnessEquationPolynomial p) = 0}

theorem polynomialSignConstructible_maxwellQuotientWitnessConstraint
    (p : ℕ) :
    PolynomialSignConstructible (((p + 1) + 1) + 2)
      (maxwellQuotientWitnessConstraint p) :=
  .inter
    (.union
      (.pos (MvPolynomial.X (maxwellQuotientWitnessStepIndex p)))
      (.neg (MvPolynomial.X (maxwellQuotientWitnessStepIndex p))))
    (.zero (maxwellQuotientWitnessEquationPolynomial p))

/-- The full incidence whose last two coordinates are the two values of the
original scalar relation. -/
def maxwellDifferenceQuotientIncidence {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Set (RealEuclidean (((p + 1) + 1) + 2)) :=
  (((maxwellQuotientWitnessBaseLinearMap p ⁻¹' U ∩
      maxwellQuotientWitnessShiftedBaseLinearMap p i ⁻¹' U) ∩
    maxwellQuotientWitnessFirstRelationLinearMap p ⁻¹' R) ∩
    maxwellQuotientWitnessSecondRelationLinearMap p i ⁻¹' R) ∩
    maxwellQuotientWitnessConstraint p

@[simp]
theorem realEuclideanAppend_append_append_mem_maxwellDifferenceQuotientIncidence_iff
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) (x : RealEuclidean p) (epsilon y : ℝ)
    (z : RealEuclidean 2) :
    realEuclideanAppend
        (realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
          (fun _ : Fin 1 ↦ y)) z ∈
      maxwellDifferenceQuotientIncidence U R i ↔
    x ∈ U ∧
      x + epsilon • (Pi.single i 1 : RealEuclidean p) ∈ U ∧
      realEuclideanAppend x (fun _ : Fin 1 ↦ z 0) ∈ R ∧
      realEuclideanAppend
          (x + epsilon • (Pi.single i 1 : RealEuclidean p))
          (fun _ : Fin 1 ↦ z 1) ∈ R ∧
      epsilon ≠ 0 ∧ epsilon * y = z 1 - z 0 := by
  simp only [maxwellDifferenceQuotientIncidence, Set.mem_inter_iff,
    Set.mem_preimage, maxwellQuotientWitnessBaseLinearMap_append,
    maxwellQuotientWitnessShiftedBaseLinearMap_append,
    maxwellQuotientWitnessFirstRelationLinearMap_append,
    maxwellQuotientWitnessSecondRelationLinearMap_append]
  simp only [maxwellQuotientWitnessConstraint, Set.mem_inter_iff,
    Set.mem_union, Set.mem_setOf_eq, MvPolynomial.eval_X,
    maxwellQuotientWitnessEquationPolynomial, map_sub, map_mul,
    maxwellQuotientWitnessStepIndex, maxwellQuotientWitnessSlopeIndex,
    maxwellQuotientWitnessFirstValueIndex,
    maxwellQuotientWitnessSecondValueIndex,
    realEuclideanAppend_castAdd, realEuclideanAppend_natAdd,
    realEuclideanAppend_last_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, sub_eq_zero]
  constructor
  · rintro ⟨⟨⟨⟨hx, hxshift⟩, hz₁⟩, hz₂⟩,
      hstep, hequation⟩
    refine ⟨hx, hxshift, hz₁, hz₂, ?_, hequation⟩
    rcases hstep with hpos | hneg
    · exact ne_of_gt hpos
    · exact ne_of_lt hneg
  · rintro ⟨hx, hxshift, hz₁, hz₂, hstep, hequation⟩
    refine ⟨⟨⟨⟨hx, hxshift⟩, hz₁⟩, hz₂⟩, ?_, hequation⟩
    rcases lt_or_gt_of_ne hstep with hneg | hpos
    · exact Or.inr hneg
    · exact Or.inl hpos

/-- The incidence projects exactly to Maxwell's directional quotient
relation. -/
theorem realEuclideanExistentialProjection_maxwellDifferenceQuotientIncidence
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    realEuclideanExistentialProjection
        (maxwellDifferenceQuotientIncidence U R i) =
      maxwellDifferenceQuotientRelation U R i := by
  ext w
  let xepsilon : RealEuclidean (p + 1) := realEuclideanTakeLeft w
  let x : RealEuclidean p := realEuclideanTakeLeft xepsilon
  let epsilon : ℝ := realEuclideanTakeRight xepsilon 0
  let y : ℝ := realEuclideanTakeRight w 0
  have hxepsilon : xepsilon =
      realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon) := by
    calc
      xepsilon = realEuclideanAppend (realEuclideanTakeLeft xepsilon)
          (realEuclideanTakeRight xepsilon) :=
        (realEuclideanAppend_takeLeft_takeRight xepsilon).symm
      _ = realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon) := by
        congr 1
        funext j
        have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        rfl
  have hw : w = realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
      (fun _ : Fin 1 ↦ y) := by
    calc
      w = realEuclideanAppend xepsilon (realEuclideanTakeRight w) :=
        (realEuclideanAppend_takeLeft_takeRight w).symm
      _ = realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
          (fun _ : Fin 1 ↦ y) := by
        rw [hxepsilon]
        congr 1
        funext j
        have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        rfl
  rw [hw]
  simp only [realEuclideanExistentialProjection, Set.mem_setOf_eq,
    realEuclideanAppend_append_append_mem_maxwellDifferenceQuotientIncidence_iff,
    realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff]
  constructor
  · rintro ⟨z, hx, hxshift, hz₁, hz₂, hstep, hequation⟩
    exact ⟨hx, hxshift, hstep, z 0, z 1, hz₁, hz₂, hequation⟩
  · rintro ⟨hx, hxshift, hstep, z₁, z₂, hz₁, hz₂, hequation⟩
    exact ⟨![z₁, z₂], hx, hxshift, hz₁, hz₂, hstep,
      by simpa using hequation⟩

/-- The directional quotient relation belongs to the Charbonnel family,
derived from membership of its domain and source relation and the weak-family
clauses. -/
theorem maxwellDifferenceQuotientRelation_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellDifferenceQuotientRelation U R i ∈
      charbonnelClosure S ((p + 1) + 1) := by
  have hp : 0 < p := maxwellFinArity_pos i
  have hbase := hC.linear_preimage_mem (by omega) hp hU
    (maxwellQuotientWitnessBaseLinearMap p)
  have hshift := hC.linear_preimage_mem (by omega) hp hU
    (maxwellQuotientWitnessShiftedBaseLinearMap p i)
  have hfirst := hC.linear_preimage_mem (by omega) (by omega) hR
    (maxwellQuotientWitnessFirstRelationLinearMap p)
  have hsecond := hC.linear_preimage_mem (by omega) (by omega) hR
    (maxwellQuotientWitnessSecondRelationLinearMap p i)
  have hconstraint : maxwellQuotientWitnessConstraint p ∈
      charbonnelClosure S (((p + 1) + 1) + 2) :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_maxwellQuotientWitnessConstraint p)
  have hincidence : maxwellDifferenceQuotientIncidence U R i ∈
      charbonnelClosure S (((p + 1) + 1) + 2) := by
    exact hC.ws1_inter (by omega)
      (hC.ws1_inter (by omega)
        (hC.ws1_inter (by omega)
          (hC.ws1_inter (by omega) hbase hshift) hfirst) hsecond)
      hconstraint
  rw [← realEuclideanExistentialProjection_maxwellDifferenceQuotientIncidence
    U R i]
  exact charbonnelClosure_projection (by omega) hincidence

/-- Closing the quotient relation and pulling it back along the linear
zero-step insertion keeps the finite slope trace in the same Charbonnel
family. -/
theorem maxwellDifferenceQuotientZeroTrace_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellDifferenceQuotientZeroTrace U R i ∈
      charbonnelClosure S (p + 1) := by
  have hquotient := maxwellDifferenceQuotientRelation_mem_charbonnelClosure
    hC i hU hR
  have hclosed : closure (maxwellDifferenceQuotientRelation U R i) ∈
      charbonnelClosure S ((p + 1) + 1) :=
    charbonnelClosure_topologicalClosure hquotient
  have hp : 0 < p := maxwellFinArity_pos i
  have hpull := hC.linear_preimage_mem (by omega) (by omega) hclosed
    (maxwellInsertZeroStepLinearMap p)
  change (maxwellInsertZeroStepLinearMap p) ⁻¹'
      closure (maxwellDifferenceQuotientRelation U R i) ∈
    charbonnelClosure S (p + 1)
  exact hpull

/-- The maintained quotient/trace certificate is therefore an actual
consequence of the weak-family membership hypotheses. -/
theorem maxwellDifferenceQuotientTraceCertificate_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    MaxwellDifferenceQuotientTraceCertificate
      (charbonnelClosure S) U R i where
  quotient_mem :=
    maxwellDifferenceQuotientRelation_mem_charbonnelClosure hC i hU hR
  trace_mem :=
    maxwellDifferenceQuotientZeroTrace_mem_charbonnelClosure hC i hU hR
  trace_closed := isClosed_maxwellDifferenceQuotientZeroTrace U R i

/-! ## Positive and negative reciprocal relations -/

/-- A vector with one coordinate is determined by that coordinate. -/
theorem realEuclidean_one_eq_const (y : RealEuclidean 1) :
    y = (fun _ : Fin 1 ↦ y 0) := by
  funext j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  rfl

/-- From `((x,r),y)` retain `(x,y)`. -/
def maxwellReciprocalWitnessSourceLinearMap (p : ℕ) :
    RealEuclidean ((p + 1) + 1) →ₗ[ℝ] RealEuclidean (p + 1) where
  toFun w := realEuclideanAppend
    (realEuclideanTakeLeft (n := p) (m := 1)
      (realEuclideanTakeLeft (n := p + 1) (m := 1) w))
    (realEuclideanTakeRight (n := p + 1) (m := 1) w)
  map_add' := by
    intro v w
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

@[simp]
theorem maxwellReciprocalWitnessSourceLinearMap_append_append
    {p : ℕ} (x : RealEuclidean p) (r : ℝ)
    (y : RealEuclidean 1) :
    maxwellReciprocalWitnessSourceLinearMap p
        (realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ r)) y) =
      realEuclideanAppend x y := by
  change realEuclideanAppend
      (realEuclideanTakeLeft (n := p) (m := 1)
        (realEuclideanTakeLeft (n := p + 1) (m := 1)
          (realEuclideanAppend
            (realEuclideanAppend x (fun _ : Fin 1 ↦ r)) y)))
      (realEuclideanTakeRight (n := p + 1) (m := 1)
        (realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ r)) y)) = _
  rw [realEuclideanTakeLeft_append, realEuclideanTakeLeft_append,
    realEuclideanTakeRight_append]

/-- The reciprocal coordinate `r` in `((x,r),y)`. -/
def maxwellReciprocalWitnessReciprocalIndex (p : ℕ) :
    Fin ((p + 1) + 1) := Fin.castAdd 1 (Fin.last p)

/-- The old slope value `y` in `((x,r),y)`. -/
def maxwellReciprocalWitnessValueIndex (p : ℕ) :
    Fin ((p + 1) + 1) := Fin.last (p + 1)

/-- The polynomial equation `y*r = 1`. -/
def maxwellReciprocalWitnessEquationPolynomial (p : ℕ) :
    MvPolynomial (Fin ((p + 1) + 1)) ℝ :=
  MvPolynomial.X (maxwellReciprocalWitnessValueIndex p) *
      MvPolynomial.X (maxwellReciprocalWitnessReciprocalIndex p) - 1

/-- Positive reciprocal witnesses. -/
def maxwellPositiveReciprocalWitnessConstraint (p : ℕ) :
    Set (RealEuclidean ((p + 1) + 1)) :=
  {w | MvPolynomial.eval w
      (maxwellReciprocalWitnessEquationPolynomial p) = 0} ∩
    {w | 0 < MvPolynomial.eval w
      (MvPolynomial.X (maxwellReciprocalWitnessReciprocalIndex p))}

/-- Negative reciprocal witnesses. -/
def maxwellNegativeReciprocalWitnessConstraint (p : ℕ) :
    Set (RealEuclidean ((p + 1) + 1)) :=
  {w | MvPolynomial.eval w
      (maxwellReciprocalWitnessEquationPolynomial p) = 0} ∩
    {w | MvPolynomial.eval w
      (MvPolynomial.X (maxwellReciprocalWitnessReciprocalIndex p)) < 0}

theorem polynomialSignConstructible_maxwellPositiveReciprocalWitnessConstraint
    (p : ℕ) :
    PolynomialSignConstructible ((p + 1) + 1)
      (maxwellPositiveReciprocalWitnessConstraint p) :=
  .inter (.zero (maxwellReciprocalWitnessEquationPolynomial p))
    (.pos (MvPolynomial.X (maxwellReciprocalWitnessReciprocalIndex p)))

theorem polynomialSignConstructible_maxwellNegativeReciprocalWitnessConstraint
    (p : ℕ) :
    PolynomialSignConstructible ((p + 1) + 1)
      (maxwellNegativeReciprocalWitnessConstraint p) :=
  .inter (.zero (maxwellReciprocalWitnessEquationPolynomial p))
    (.neg (MvPolynomial.X (maxwellReciprocalWitnessReciprocalIndex p)))

/-- The positive reciprocal incidence before forgetting the old slope. -/
def maxwellPositiveReciprocalIncidence {p : ℕ}
    (G : MaxwellRelation p 1) :
    Set (RealEuclidean ((p + 1) + 1)) :=
  maxwellReciprocalWitnessSourceLinearMap p ⁻¹' G ∩
    maxwellPositiveReciprocalWitnessConstraint p

/-- The negative reciprocal incidence before forgetting the old slope. -/
def maxwellNegativeReciprocalIncidence {p : ℕ}
    (G : MaxwellRelation p 1) :
    Set (RealEuclidean ((p + 1) + 1)) :=
  maxwellReciprocalWitnessSourceLinearMap p ⁻¹' G ∩
    maxwellNegativeReciprocalWitnessConstraint p

@[simp]
theorem realEuclideanAppend_append_mem_maxwellPositiveReciprocalIncidence_iff
    {p : ℕ} (G : MaxwellRelation p 1)
    (x : RealEuclidean p) (r : ℝ) (y : RealEuclidean 1) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ r))
        y ∈
      maxwellPositiveReciprocalIncidence G ↔
    realEuclideanAppend x y ∈ G ∧
      y 0 * r = 1 ∧ 0 < r := by
  simp only [maxwellPositiveReciprocalIncidence, Set.mem_inter_iff,
    Set.mem_preimage,
    maxwellReciprocalWitnessSourceLinearMap_append_append,
    maxwellPositiveReciprocalWitnessConstraint, Set.mem_setOf_eq,
    maxwellReciprocalWitnessEquationPolynomial, map_sub, map_mul, map_one,
    MvPolynomial.eval_X, maxwellReciprocalWitnessReciprocalIndex,
    maxwellReciprocalWitnessValueIndex, realEuclideanAppend_castAdd,
    realEuclideanAppend_last_one, sub_eq_zero]

@[simp]
theorem realEuclideanAppend_append_mem_maxwellNegativeReciprocalIncidence_iff
    {p : ℕ} (G : MaxwellRelation p 1)
    (x : RealEuclidean p) (r : ℝ) (y : RealEuclidean 1) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ r))
        y ∈
      maxwellNegativeReciprocalIncidence G ↔
    realEuclideanAppend x y ∈ G ∧
      y 0 * r = 1 ∧ r < 0 := by
  simp only [maxwellNegativeReciprocalIncidence, Set.mem_inter_iff,
    Set.mem_preimage,
    maxwellReciprocalWitnessSourceLinearMap_append_append,
    maxwellNegativeReciprocalWitnessConstraint, Set.mem_setOf_eq,
    maxwellReciprocalWitnessEquationPolynomial, map_sub, map_mul, map_one,
    MvPolynomial.eval_X, maxwellReciprocalWitnessReciprocalIndex,
    maxwellReciprocalWitnessValueIndex, realEuclideanAppend_castAdd,
    realEuclideanAppend_last_one, sub_eq_zero]

theorem realEuclideanExistentialProjection_maxwellPositiveReciprocalIncidence
    {p : ℕ} (G : MaxwellRelation p 1) :
    realEuclideanExistentialProjection
        (maxwellPositiveReciprocalIncidence G) =
      maxwellPositiveReciprocalRelation G := by
  ext w
  let x : RealEuclidean p := realEuclideanTakeLeft w
  let r : ℝ := realEuclideanTakeRight w 0
  have hw : w = realEuclideanAppend x (fun _ : Fin 1 ↦ r) := by
    calc
      w = realEuclideanAppend (realEuclideanTakeLeft w)
          (realEuclideanTakeRight w) :=
        (realEuclideanAppend_takeLeft_takeRight w).symm
      _ = realEuclideanAppend x (fun _ : Fin 1 ↦ r) := by
        congr 1
        funext j
        have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        rfl
  rw [hw]
  simp only [realEuclideanExistentialProjection, Set.mem_setOf_eq,
    realEuclideanAppend_append_mem_maxwellPositiveReciprocalIncidence_iff,
    realEuclideanAppend_scalar_mem_maxwellPositiveReciprocalRelation_iff]
  constructor
  · rintro ⟨y, hy, heq, hpos⟩
    have hy' : realEuclideanAppend x (fun _ : Fin 1 ↦ y 0) ∈ G := by
      rw [← realEuclidean_one_eq_const y]
      exact hy
    exact ⟨y 0, hy', heq, hpos⟩
  · rintro ⟨y, hy, heq, hpos⟩
    exact ⟨fun _ : Fin 1 ↦ y, hy, heq, hpos⟩

theorem realEuclideanExistentialProjection_maxwellNegativeReciprocalIncidence
    {p : ℕ} (G : MaxwellRelation p 1) :
    realEuclideanExistentialProjection
        (maxwellNegativeReciprocalIncidence G) =
      maxwellNegativeReciprocalRelation G := by
  ext w
  let x : RealEuclidean p := realEuclideanTakeLeft w
  let r : ℝ := realEuclideanTakeRight w 0
  have hw : w = realEuclideanAppend x (fun _ : Fin 1 ↦ r) := by
    calc
      w = realEuclideanAppend (realEuclideanTakeLeft w)
          (realEuclideanTakeRight w) :=
        (realEuclideanAppend_takeLeft_takeRight w).symm
      _ = realEuclideanAppend x (fun _ : Fin 1 ↦ r) := by
        congr 1
        funext j
        have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
        subst j
        rfl
  rw [hw]
  simp only [realEuclideanExistentialProjection, Set.mem_setOf_eq,
    realEuclideanAppend_append_mem_maxwellNegativeReciprocalIncidence_iff,
    realEuclideanAppend_scalar_mem_maxwellNegativeReciprocalRelation_iff]
  constructor
  · rintro ⟨y, hy, heq, hneg⟩
    have hy' : realEuclideanAppend x (fun _ : Fin 1 ↦ y 0) ∈ G := by
      rw [← realEuclidean_one_eq_const y]
      exact hy
    exact ⟨y 0, hy', heq, hneg⟩
  · rintro ⟨y, hy, heq, hneg⟩
    exact ⟨fun _ : Fin 1 ↦ y, hy, heq, hneg⟩

theorem maxwellPositiveReciprocalRelation_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {G : MaxwellRelation p 1}
    (hG : G ∈ charbonnelClosure S (p + 1)) :
    maxwellPositiveReciprocalRelation G ∈
      charbonnelClosure S (p + 1) := by
  have hpull := hC.linear_preimage_mem (by omega) (by omega) hG
    (maxwellReciprocalWitnessSourceLinearMap p)
  have hconstraint : maxwellPositiveReciprocalWitnessConstraint p ∈
      charbonnelClosure S ((p + 1) + 1) :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_maxwellPositiveReciprocalWitnessConstraint p)
  have hincidence : maxwellPositiveReciprocalIncidence G ∈
      charbonnelClosure S ((p + 1) + 1) :=
    hC.ws1_inter (by omega) hpull hconstraint
  rw [← realEuclideanExistentialProjection_maxwellPositiveReciprocalIncidence G]
  exact charbonnelClosure_projection (by omega) hincidence

theorem maxwellNegativeReciprocalRelation_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {G : MaxwellRelation p 1}
    (hG : G ∈ charbonnelClosure S (p + 1)) :
    maxwellNegativeReciprocalRelation G ∈
      charbonnelClosure S (p + 1) := by
  have hpull := hC.linear_preimage_mem (by omega) (by omega) hG
    (maxwellReciprocalWitnessSourceLinearMap p)
  have hconstraint : maxwellNegativeReciprocalWitnessConstraint p ∈
      charbonnelClosure S ((p + 1) + 1) :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_maxwellNegativeReciprocalWitnessConstraint p)
  have hincidence : maxwellNegativeReciprocalIncidence G ∈
      charbonnelClosure S ((p + 1) + 1) :=
    hC.ws1_inter (by omega) hpull hconstraint
  rw [← realEuclideanExistentialProjection_maxwellNegativeReciprocalIncidence G]
  exact charbonnelClosure_projection (by omega) hincidence

/-! ## Multivalued loci -/

/-- Read `(x,y₁)` from fiber-pair coordinates `(x,(y₁,y₂))`. -/
def maxwellFiberPairFirstLinearMap (p : ℕ) :
    RealEuclidean (p + 2) →ₗ[ℝ] RealEuclidean (p + 1) where
  toFun w := realEuclideanAppend (realEuclideanTakeLeft w)
    (fun _ : Fin 1 ↦ realEuclideanTakeRight (n := p) (m := 2) w 0)
  map_add' := by
    intro v w
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

/-- Read `(x,y₂)` from fiber-pair coordinates `(x,(y₁,y₂))`. -/
def maxwellFiberPairSecondLinearMap (p : ℕ) :
    RealEuclidean (p + 2) →ₗ[ℝ] RealEuclidean (p + 1) where
  toFun w := realEuclideanAppend (realEuclideanTakeLeft w)
    (fun _ : Fin 1 ↦ realEuclideanTakeRight (n := p) (m := 2) w 1)
  map_add' := by
    intro v w
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

@[simp]
theorem maxwellFiberPairFirstLinearMap_append
    {p : ℕ} (x : RealEuclidean p) (y : RealEuclidean 2) :
    maxwellFiberPairFirstLinearMap p (realEuclideanAppend x y) =
      realEuclideanAppend x (fun _ : Fin 1 ↦ y 0) := by
  change realEuclideanAppend
      (realEuclideanTakeLeft (n := p) (m := 2)
        (realEuclideanAppend x y))
      (fun _ : Fin 1 ↦
        realEuclideanTakeRight (n := p) (m := 2)
          (realEuclideanAppend x y) 0) = _
  rw [realEuclideanTakeLeft_append, realEuclideanTakeRight_append]

@[simp]
theorem maxwellFiberPairSecondLinearMap_append
    {p : ℕ} (x : RealEuclidean p) (y : RealEuclidean 2) :
    maxwellFiberPairSecondLinearMap p (realEuclideanAppend x y) =
      realEuclideanAppend x (fun _ : Fin 1 ↦ y 1) := by
  change realEuclideanAppend
      (realEuclideanTakeLeft (n := p) (m := 2)
        (realEuclideanAppend x y))
      (fun _ : Fin 1 ↦
        realEuclideanTakeRight (n := p) (m := 2)
          (realEuclideanAppend x y) 1) = _
  rw [realEuclideanTakeLeft_append, realEuclideanTakeRight_append]

def maxwellFiberPairFirstValueIndex (p : ℕ) : Fin (p + 2) :=
  Fin.natAdd p 0

def maxwellFiberPairSecondValueIndex (p : ℕ) : Fin (p + 2) :=
  Fin.natAdd p 1

/-- The semialgebraic condition `y₁ ≠ y₂`. -/
def maxwellFiberPairDistinctConstraint (p : ℕ) :
    Set (RealEuclidean (p + 2)) :=
  {w | 0 < MvPolynomial.eval w
      (MvPolynomial.X (maxwellFiberPairSecondValueIndex p) -
        MvPolynomial.X (maxwellFiberPairFirstValueIndex p))} ∪
  {w | MvPolynomial.eval w
      (MvPolynomial.X (maxwellFiberPairSecondValueIndex p) -
        MvPolynomial.X (maxwellFiberPairFirstValueIndex p)) < 0}

theorem polynomialSignConstructible_maxwellFiberPairDistinctConstraint
    (p : ℕ) :
    PolynomialSignConstructible (p + 2)
      (maxwellFiberPairDistinctConstraint p) :=
  .union
    (.pos (MvPolynomial.X (maxwellFiberPairSecondValueIndex p) -
      MvPolynomial.X (maxwellFiberPairFirstValueIndex p)))
    (.neg (MvPolynomial.X (maxwellFiberPairSecondValueIndex p) -
      MvPolynomial.X (maxwellFiberPairFirstValueIndex p)))

/-- Two distinct values of one scalar relation over a common base point. -/
def maxwellMultivaluedIncidence {p : ℕ} (G : MaxwellRelation p 1) :
    Set (RealEuclidean (p + 2)) :=
  (maxwellFiberPairFirstLinearMap p ⁻¹' G ∩
    maxwellFiberPairSecondLinearMap p ⁻¹' G) ∩
    maxwellFiberPairDistinctConstraint p

@[simp]
theorem realEuclideanAppend_mem_maxwellMultivaluedIncidence_iff
    {p : ℕ} (G : MaxwellRelation p 1)
    (x : RealEuclidean p) (y : RealEuclidean 2) :
    realEuclideanAppend x y ∈ maxwellMultivaluedIncidence G ↔
      realEuclideanAppend x (fun _ : Fin 1 ↦ y 0) ∈ G ∧
      realEuclideanAppend x (fun _ : Fin 1 ↦ y 1) ∈ G ∧
      y 0 ≠ y 1 := by
  simp only [maxwellMultivaluedIncidence, Set.mem_inter_iff,
    Set.mem_preimage,
    maxwellFiberPairFirstLinearMap_append,
    maxwellFiberPairSecondLinearMap_append]
  simp only [maxwellFiberPairDistinctConstraint, Set.mem_union,
    Set.mem_setOf_eq, map_sub, MvPolynomial.eval_X,
    maxwellFiberPairFirstValueIndex, maxwellFiberPairSecondValueIndex,
    realEuclideanAppend_natAdd, sub_pos, sub_neg]
  constructor
  · rintro ⟨⟨hy₁, hy₂⟩, hlt | hgt⟩
    · exact ⟨hy₁, hy₂, ne_of_lt hlt⟩
    · exact ⟨hy₁, hy₂, ne_of_gt hgt⟩
  · rintro ⟨hy₁, hy₂, hne⟩
    refine ⟨⟨hy₁, hy₂⟩, ?_⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl hlt
    · exact Or.inr hgt

theorem realEuclideanExistentialProjection_maxwellMultivaluedIncidence
    {p : ℕ} (G : MaxwellRelation p 1) :
    realEuclideanExistentialProjection (maxwellMultivaluedIncidence G) =
      maxwellMultivaluedLocus G := by
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_setOf_eq,
    realEuclideanAppend_mem_maxwellMultivaluedIncidence_iff,
    mem_maxwellMultivaluedLocus_iff]
  constructor
  · rintro ⟨y, hy₁, hy₂, hne⟩
    exact ⟨(fun _ : Fin 1 ↦ y 0), (fun _ : Fin 1 ↦ y 1),
      hy₁, hy₂, by
        intro h
        apply hne
        exact congrFun h 0⟩
  · rintro ⟨y₁, y₂, hy₁, hy₂, hne⟩
    have hy₁' : realEuclideanAppend x (fun _ : Fin 1 ↦ y₁ 0) ∈ G := by
      rw [← realEuclidean_one_eq_const y₁]
      exact hy₁
    have hy₂' : realEuclideanAppend x (fun _ : Fin 1 ↦ y₂ 0) ∈ G := by
      rw [← realEuclidean_one_eq_const y₂]
      exact hy₂
    refine ⟨![y₁ 0, y₂ 0], hy₁', hy₂', ?_⟩
    intro h
    apply hne
    funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simpa using h

/-- The multivalued locus of a scalar relation in the generated family is
again in the generated family. -/
theorem maxwellMultivaluedLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {G : MaxwellRelation p 1}
    (hG : G ∈ charbonnelClosure S (p + 1)) :
    maxwellMultivaluedLocus G ∈ charbonnelClosure S p := by
  have hfirst := hC.linear_preimage_mem (by omega) (by omega) hG
    (maxwellFiberPairFirstLinearMap p)
  have hsecond := hC.linear_preimage_mem (by omega) (by omega) hG
    (maxwellFiberPairSecondLinearMap p)
  have hdistinct : maxwellFiberPairDistinctConstraint p ∈
      charbonnelClosure S (p + 2) :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_maxwellFiberPairDistinctConstraint p)
  have hincidence : maxwellMultivaluedIncidence G ∈
      charbonnelClosure S (p + 2) :=
    hC.ws1_inter (by omega)
      (hC.ws1_inter (by omega) hfirst hsecond) hdistinct
  rw [← realEuclideanExistentialProjection_maxwellMultivaluedIncidence G]
  exact charbonnelClosure_projection hp hincidence

/-! ## Zero sections and infinite cluster bases -/

/-- Cutting by the last-coordinate zero hyperplane and projecting gives the
literal zero section. -/
theorem realEuclideanExistentialProjection_inter_lastCoordinateZero
    {p : ℕ} (A : Set (RealEuclidean (p + 1))) :
    realEuclideanExistentialProjection
        (A ∩ charbonnelLastCoordinateZeroHyperplane p) =
      charbonnelZeroSection A := by
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_setOf_eq,
    Set.mem_inter_iff, charbonnelZeroSection]
  constructor
  · rintro ⟨y, hyA, hyzero⟩
    have hy0 : y 0 = 0 := by
      simpa [charbonnelLastCoordinateZeroHyperplane,
        realEuclideanAppend_last_one] using hyzero
    have hy : y = (fun _ : Fin 1 ↦ 0) := by
      funext j
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simpa using hy0
    rw [hy] at hyA
    exact hyA
  · intro hx
    refine ⟨(fun _ : Fin 1 ↦ 0), ?_, ?_⟩
    · exact hx
    · simp [charbonnelLastCoordinateZeroHyperplane,
        realEuclideanAppend_last_one]

/-- Zero sections of generated-family members remain in the generated
family. -/
theorem charbonnelZeroSection_mem_charbonnelClosure
    {S : EuclideanSetFamily} {p : ℕ} (hp : 0 < p)
    {A : Set (RealEuclidean (p + 1))}
    (hA : A ∈ charbonnelClosure S (p + 1)) :
    charbonnelZeroSection A ∈ charbonnelClosure S p := by
  have hcut : A ∩ charbonnelLastCoordinateZeroHyperplane p ∈
      charbonnelClosure S (p + 1) :=
    charbonnelClosure_integerAffineInter hA
      (isIntegerAffineSet_charbonnelLastCoordinateZeroHyperplane p)
  rw [← realEuclideanExistentialProjection_inter_lastCoordinateZero A]
  exact charbonnelClosure_projection hp hcut

theorem maxwellPositiveInfinityBase_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {G : MaxwellRelation p 1}
    (hG : G ∈ charbonnelClosure S (p + 1)) :
    maxwellPositiveInfinityBase G ∈ charbonnelClosure S p := by
  have hreciprocal :=
    maxwellPositiveReciprocalRelation_mem_charbonnelClosure hC hp hG
  have hclosed : closure (maxwellPositiveReciprocalRelation G) ∈
      charbonnelClosure S (p + 1) :=
    charbonnelClosure_topologicalClosure hreciprocal
  have hzero := charbonnelZeroSection_mem_charbonnelClosure hp hclosed
  have heq : maxwellPositiveInfinityBase G =
      charbonnelZeroSection (closure (maxwellPositiveReciprocalRelation G)) := by
    ext x
    change realEuclideanAppend x (0 : RealEuclidean 1) ∈
        closure (maxwellPositiveReciprocalRelation G) ↔
      realEuclideanAppend x (fun _ : Fin 1 ↦ 0) ∈
        closure (maxwellPositiveReciprocalRelation G)
    have hz : (0 : RealEuclidean 1) = (fun _ : Fin 1 ↦ 0) := by
      funext j
      rfl
    rw [hz]
  rw [heq]
  exact hzero

theorem maxwellNegativeInfinityBase_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {G : MaxwellRelation p 1}
    (hG : G ∈ charbonnelClosure S (p + 1)) :
    maxwellNegativeInfinityBase G ∈ charbonnelClosure S p := by
  have hreciprocal :=
    maxwellNegativeReciprocalRelation_mem_charbonnelClosure hC hp hG
  have hclosed : closure (maxwellNegativeReciprocalRelation G) ∈
      charbonnelClosure S (p + 1) :=
    charbonnelClosure_topologicalClosure hreciprocal
  have hzero := charbonnelZeroSection_mem_charbonnelClosure hp hclosed
  have heq : maxwellNegativeInfinityBase G =
      charbonnelZeroSection (closure (maxwellNegativeReciprocalRelation G)) := by
    ext x
    change realEuclideanAppend x (0 : RealEuclidean 1) ∈
        closure (maxwellNegativeReciprocalRelation G) ↔
      realEuclideanAppend x (fun _ : Fin 1 ↦ 0) ∈
        closure (maxwellNegativeReciprocalRelation G)
    have hz : (0 : RealEuclidean 1) = (fun _ : Fin 1 ↦ 0) := by
      funext j
      rfl
    rw [hz]
  rw [heq]
  exact hzero

/-! ## Infinity fillers and restriction of relations -/

/-- The affine hyperplane on which the last scalar coordinate is `1`. -/
def maxwellLastCoordinateOneHyperplane (p : ℕ) :
    Set (RealEuclidean (p + 1)) :=
  {w | w (Fin.last p) = 1}

theorem isIntegerAffineSet_maxwellLastCoordinateOneHyperplane (p : ℕ) :
    IsIntegerAffineSet (maxwellLastCoordinateOneHyperplane p) := by
  refine ⟨1,
    (fun _ j ↦ if j = Fin.last p then 1 else 0),
    (fun _ ↦ -1), ?_⟩
  ext w
  simp [maxwellLastCoordinateOneHyperplane] <;>
    constructor <;> intro h <;> linarith

/-- A final one-dimensional block equals the constant vector `1` exactly
when its unique ambient coordinate is `1`. -/
theorem realEuclideanTakeRight_one_eq_iff_last_eq_one
    {p : ℕ} (w : RealEuclidean (p + 1)) :
    realEuclideanTakeRight w = (1 : RealEuclidean 1) ↔
      w (Fin.last p) = 1 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    change w (Fin.natAdd p (0 : Fin 1)) = 1 at h0
    have hindex : Fin.natAdd p (0 : Fin 1) = Fin.last p := Fin.ext rfl
    rw [hindex] at h0
    exact h0
  · intro h
    funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    change w (Fin.natAdd p (0 : Fin 1)) = 1
    have hindex : Fin.natAdd p (0 : Fin 1) = Fin.last p := Fin.ext rfl
    rw [hindex]
    exact h

/-- A product-and-affine-cut presentation of Maxwell's dummy value over
infinite-only base points. -/
def maxwellInfinityFillerCarrier {p : ℕ}
    (U : Set (RealEuclidean p)) (G : MaxwellRelation p 1) :
    Set (RealEuclidean (p + 1)) :=
  realEuclideanSetProduct
      (U ∩ (maxwellPositiveInfinityBase G ∪
        maxwellNegativeInfinityBase G)) Set.univ ∩
    maxwellLastCoordinateOneHyperplane p

theorem maxwellInfinityFillerCarrier_eq {p : ℕ}
    (U : Set (RealEuclidean p)) (G : MaxwellRelation p 1) :
    maxwellInfinityFillerCarrier U G =
      maxwellInfinityFillerRelation U G := by
  ext w
  simp only [maxwellInfinityFillerCarrier, realEuclideanSetProduct,
    Set.mem_inter_iff, Set.mem_union, Set.mem_univ, and_true,
    maxwellLastCoordinateOneHyperplane, Set.mem_setOf_eq,
    maxwellInfinityFillerRelation]
  rw [← realEuclideanTakeRight_one_eq_iff_last_eq_one w]
  aesop

theorem maxwellInfinityFillerRelation_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {U : Set (RealEuclidean p)}
    {G : MaxwellRelation p 1}
    (hU : U ∈ charbonnelClosure S p)
    (hG : G ∈ charbonnelClosure S (p + 1)) :
    maxwellInfinityFillerRelation U G ∈
      charbonnelClosure S (p + 1) := by
  have hpositive := maxwellPositiveInfinityBase_mem_charbonnelClosure
    hC hp hG
  have hnegative := maxwellNegativeInfinityBase_mem_charbonnelClosure
    hC hp hG
  have hinfinity : maxwellPositiveInfinityBase G ∪
      maxwellNegativeInfinityBase G ∈ charbonnelClosure S p :=
    charbonnelClosure_union hpositive hnegative
  have hbase : U ∩ (maxwellPositiveInfinityBase G ∪
      maxwellNegativeInfinityBase G) ∈ charbonnelClosure S p :=
    hC.ws1_inter hp hU hinfinity
  have huniv : (Set.univ : Set (RealEuclidean 1)) ∈
      charbonnelClosure S 1 :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_univ 1)
  have hproduct : realEuclideanSetProduct
      (U ∩ (maxwellPositiveInfinityBase G ∪
        maxwellNegativeInfinityBase G)) Set.univ ∈
      charbonnelClosure S (p + 1) :=
    hC.ws3_prod hp (by omega) hbase huniv
  have hcarrier : maxwellInfinityFillerCarrier U G ∈
      charbonnelClosure S (p + 1) :=
    charbonnelClosure_integerAffineInter hproduct
      (isIntegerAffineSet_maxwellLastCoordinateOneHyperplane p)
  rw [maxwellInfinityFillerCarrier_eq U G] at hcarrier
  exact hcarrier

/-- Restricting a scalar relation to a generated-family base set preserves
membership. -/
theorem maxwellRelationRestrict_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {U : Set (RealEuclidean p)}
    {G : MaxwellRelation p 1}
    (hU : U ∈ charbonnelClosure S p)
    (hG : G ∈ charbonnelClosure S (p + 1)) :
    maxwellRelationRestrict G U ∈ charbonnelClosure S (p + 1) := by
  have hpull := hC.linear_preimage_mem (by omega) hp hU
    (realEuclideanTakeLeftLinearMap p 1)
  have hinter : G ∩
      (realEuclideanTakeLeftLinearMap p 1) ⁻¹' U ∈
      charbonnelClosure S (p + 1) :=
    hC.ws1_inter (by omega) hG hpull
  change G ∩ (realEuclideanTakeLeftLinearMap p 1) ⁻¹' U ∈
    charbonnelClosure S (p + 1)
  exact hinter

/-! ## Exceptional loci and derivative pseudographs -/

theorem maxwellCoordinateRawBadLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellCoordinateRawBadLocus U R i ∈ charbonnelClosure S p := by
  have hp : 0 < p := maxwellFinArity_pos i
  let G := maxwellDifferenceQuotientZeroTrace U R i
  have hG : G ∈ charbonnelClosure S (p + 1) :=
    maxwellDifferenceQuotientZeroTrace_mem_charbonnelClosure hC i hU hR
  have hRmulti := maxwellMultivaluedLocus_mem_charbonnelClosure
    hC hp hR
  have hpositive := maxwellPositiveInfinityBase_mem_charbonnelClosure
    hC hp hG
  have hnegative := maxwellNegativeInfinityBase_mem_charbonnelClosure
    hC hp hG
  have hGmulti := maxwellMultivaluedLocus_mem_charbonnelClosure
    hC hp hG
  unfold maxwellCoordinateRawBadLocus
  change maxwellMultivaluedLocus R ∪
      maxwellPositiveInfinityBase G ∪
      maxwellNegativeInfinityBase G ∪
      maxwellMultivaluedLocus G ∈ charbonnelClosure S p
  simpa only [Set.union_assoc] using
    (charbonnelClosure_union hRmulti
      (charbonnelClosure_union hpositive
        (charbonnelClosure_union hnegative hGmulti)))

theorem maxwellCoordinateExceptionalLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellCoordinateExceptionalLocus U R i ∈
      charbonnelClosure S p := by
  exact charbonnelClosure_topologicalClosure
    (maxwellCoordinateRawBadLocus_mem_charbonnelClosure hC i hU hR)

/-- Finite unions of generated-family members stay in the generated family.
The weak-family hypothesis is used only for the empty initial union. -/
theorem charbonnelClosure_iUnion_fin
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n k : ℕ} (hn : 0 < n) (A : Fin k → Set (RealEuclidean n))
    (hA : ∀ i, A i ∈ charbonnelClosure S n) :
    (⋃ i, A i) ∈ charbonnelClosure S n := by
  exact charbonnelClosure_iUnion_fin_mem
    (hC.ws2_polynomialSign hn (polynomialSignConstructible_empty n)) hA

theorem maxwellFirstOrderExceptionalLocus_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p) {U : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1}
    (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellFirstOrderExceptionalLocus U R ∈
      charbonnelClosure S p := by
  unfold maxwellFirstOrderExceptionalLocus
  exact charbonnelClosure_iUnion_fin hC hp _
    (fun i ↦ maxwellCoordinateExceptionalLocus_mem_charbonnelClosure
      hC i hU hR)

theorem maxwellDerivativePseudograph_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    maxwellDerivativePseudograph U R i ∈
      charbonnelClosure S (p + 1) := by
  have hp : 0 < p := maxwellFinArity_pos i
  let G := maxwellDifferenceQuotientZeroTrace U R i
  have hG : G ∈ charbonnelClosure S (p + 1) :=
    maxwellDifferenceQuotientZeroTrace_mem_charbonnelClosure hC i hU hR
  have hfiller : maxwellInfinityFillerRelation U G ∈
      charbonnelClosure S (p + 1) :=
    maxwellInfinityFillerRelation_mem_charbonnelClosure hC hp hU hG
  have hunion : G ∪ maxwellInfinityFillerRelation U G ∈
      charbonnelClosure S (p + 1) :=
    charbonnelClosure_union hG hfiller
  exact maxwellRelationRestrict_mem_charbonnelClosure
    hC hp hU hunion

/-! ## A single reusable output package -/

/-- All algebraic membership conclusions used by one coordinate of
Maxwell's first-order construction. -/
structure MaxwellExtendedSlopeClusterMembership
    (S : EuclideanSetFamily) {p : ℕ}
    (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) : Prop where
  quotient_mem : maxwellDifferenceQuotientRelation U R i ∈
    charbonnelClosure S ((p + 1) + 1)
  zeroTrace_mem : maxwellDifferenceQuotientZeroTrace U R i ∈
    charbonnelClosure S (p + 1)
  positiveReciprocal_mem : maxwellPositiveReciprocalRelation
      (maxwellDifferenceQuotientZeroTrace U R i) ∈
    charbonnelClosure S (p + 1)
  negativeReciprocal_mem : maxwellNegativeReciprocalRelation
      (maxwellDifferenceQuotientZeroTrace U R i) ∈
    charbonnelClosure S (p + 1)
  positiveInfinityBase_mem : maxwellPositiveInfinityBase
      (maxwellDifferenceQuotientZeroTrace U R i) ∈
    charbonnelClosure S p
  negativeInfinityBase_mem : maxwellNegativeInfinityBase
      (maxwellDifferenceQuotientZeroTrace U R i) ∈
    charbonnelClosure S p
  infinityFiller_mem : maxwellInfinityFillerRelation U
      (maxwellDifferenceQuotientZeroTrace U R i) ∈
    charbonnelClosure S (p + 1)
  rawBadLocus_mem : maxwellCoordinateRawBadLocus U R i ∈
    charbonnelClosure S p
  exceptionalLocus_mem : maxwellCoordinateExceptionalLocus U R i ∈
    charbonnelClosure S p
  derivativePseudograph_mem : maxwellDerivativePseudograph U R i ∈
    charbonnelClosure S (p + 1)

theorem maxwellExtendedSlopeClusterMembership
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hU : U ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1)) :
    MaxwellExtendedSlopeClusterMembership S U R i := by
  have hp : 0 < p := maxwellFinArity_pos i
  let G := maxwellDifferenceQuotientZeroTrace U R i
  have hquotient := maxwellDifferenceQuotientRelation_mem_charbonnelClosure
    hC i hU hR
  have htrace : G ∈ charbonnelClosure S (p + 1) :=
    maxwellDifferenceQuotientZeroTrace_mem_charbonnelClosure hC i hU hR
  have hpositiveReciprocal :=
    maxwellPositiveReciprocalRelation_mem_charbonnelClosure hC hp htrace
  have hnegativeReciprocal :=
    maxwellNegativeReciprocalRelation_mem_charbonnelClosure hC hp htrace
  have hpositiveInfinity :=
    maxwellPositiveInfinityBase_mem_charbonnelClosure hC hp htrace
  have hnegativeInfinity :=
    maxwellNegativeInfinityBase_mem_charbonnelClosure hC hp htrace
  have hfiller := maxwellInfinityFillerRelation_mem_charbonnelClosure
    hC hp hU htrace
  have hraw := maxwellCoordinateRawBadLocus_mem_charbonnelClosure
    hC i hU hR
  have hexceptional :=
    maxwellCoordinateExceptionalLocus_mem_charbonnelClosure hC i hU hR
  have hderivative := maxwellDerivativePseudograph_mem_charbonnelClosure
    hC i hU hR
  exact ⟨hquotient, htrace, hpositiveReciprocal,
    hnegativeReciprocal, hpositiveInfinity, hnegativeInfinity,
    hfiller, hraw, hexceptional, hderivative⟩

/-- Specialization to the literal-zero Charbonnel family used in the Abel
pipeline. -/
theorem literalZeroSet_maxwellExtendedSlopeClusterMembership
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p)
    (hU : U ∈ charbonnelClosure (literalZeroSetFamily G) p)
    (hR : R ∈ charbonnelClosure (literalZeroSetFamily G) (p + 1)) :
    MaxwellExtendedSlopeClusterMembership
      (literalZeroSetFamily G) U R i :=
  maxwellExtendedSlopeClusterMembership
    (literalZeroSet_charbonnelClosure_positiveArityWeakSetStructure
      hG hsmooth) i hU hR

end AbelFormalization
