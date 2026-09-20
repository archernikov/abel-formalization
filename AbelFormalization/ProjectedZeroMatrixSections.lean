import AbelFormalization.AbelGeometricFamily
import AbelFormalization.ProjectedFiberComponents

/-!
# The matrix-parameter fiber used in the W5 argument

This file encodes the manuscript's map
`(x, z, M) ↦ (f (x, z), Mx, M)` in flat `Fin` coordinates.  Keeping `M`
in the target is the point that makes the resulting component bound uniform
over both the matrix and the affine-fiber value.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- A square matrix represented by its canonical flat coordinate vector. -/
abbrev FlatSquareMatrix (n : ℕ) := RealEuclidean (n * n)

/-- The `(i,j)` entry of a flat square matrix. -/
def flatSquareMatrixEntry {n : ℕ} (M : FlatSquareMatrix n)
    (i j : Fin n) : ℝ :=
  M (finProdFinEquiv (i, j))

/-- Matrix-vector multiplication for a flat square matrix. -/
def flatSquareMatrixMulVec {n : ℕ} (M : FlatSquareMatrix n)
    (x : RealEuclidean n) : RealEuclidean n :=
  fun i ↦ ∑ j, flatSquareMatrixEntry M i j * x j

/-- The source coordinate occupied by the visible variable `x_j` in
`(x,z,M)`. -/
def matrixFiberXIndex (n q : ℕ) (j : Fin n) :
    Fin (n + (q + n * n)) :=
  Fin.castAdd (q + n * n) j

/-- The source coordinate occupied by the matrix entry `M_k` in `(x,z,M)`. -/
def matrixFiberMatrixIndex (n q : ℕ) (k : Fin (n * n)) :
    Fin (n + (q + n * n)) :=
  Fin.natAdd n (Fin.natAdd q k)

/-- The polynomial whose value is row `i` of `Mx`, with both `x` and `M`
viewed as variables in the full source `(x,z,M)`. -/
def matrixFiberMulVecPolynomial (n q : ℕ) (i : Fin n) :
    MvPolynomial (Fin (n + (q + n * n))) ℝ :=
  ∑ j : Fin n,
    MvPolynomial.X (matrixFiberMatrixIndex n q (finProdFinEquiv (i, j))) *
      MvPolynomial.X (matrixFiberXIndex n q j)

/-- The manuscript's matrix-parameter map
`H_f(x,z,M) = (f(x,z), Mx, M)`, in flat coordinates. -/
def projectedZeroMatrixFiberMap {n q : ℕ}
    (f : RealEuclideanFunction (n + q)) :
    RealEuclidean (n + (q + n * n)) → RealEuclidean ((1 + n) + n * n) :=
  fun v ↦
    let x := realEuclideanTakeLeft v
    let zM := realEuclideanTakeRight v
    let z := realEuclideanTakeLeft zM
    let M := realEuclideanTakeRight zM
    realEuclideanAppend
      (realEuclideanAppend (fun _ : Fin 1 ↦ f (realEuclideanAppend x z))
        (flatSquareMatrixMulVec M x)) M

/-- The target `(0,b,M)` for the matrix-parameter map. -/
def projectedZeroMatrixFiberTarget {n : ℕ}
    (M : FlatSquareMatrix n) (b : RealEuclidean n) :
    RealEuclidean ((1 + n) + n * n) :=
  realEuclideanAppend
    (realEuclideanAppend (fun _ : Fin 1 ↦ 0) b) M

@[simp]
theorem matrixFiberMulVecPolynomial_eval_append
    {n q : ℕ} (i : Fin n) (x : RealEuclidean n)
    (z : RealEuclidean q) (M : FlatSquareMatrix n) :
    MvPolynomial.eval (realEuclideanAppend x (realEuclideanAppend z M))
        (matrixFiberMulVecPolynomial n q i) =
      flatSquareMatrixMulVec M x i := by
  simp [matrixFiberMulVecPolynomial, flatSquareMatrixMulVec,
    flatSquareMatrixEntry, matrixFiberMatrixIndex, matrixFiberXIndex]

theorem functionTupleInFamily_projectedZeroMatrixFiberMap
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n q : ℕ}
    {f : RealEuclideanFunction (n + q)} (hf : f ∈ G (n + q)) :
    FunctionTupleInFamily G (projectedZeroMatrixFiberMap f) := by
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro k'
    refine Fin.addCases ?_ ?_ k'
    · intro i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      have hsource : (fun v ↦ f (realEuclideanAppend
          (realEuclideanTakeLeft v)
          (realEuclideanTakeLeft (realEuclideanTakeRight v)))) ∈
            G (n + (q + n * n)) := by
        convert hG.affine_comp hf
          (realEuclideanVisibleLeftWitnessLinearMap n q (n * n)).toAffineMap using 1
        funext v
        apply congrArg f
        funext j
        refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j <;>
          simp [realEuclideanVisibleLeftWitnessLinearMap,
            realEuclideanTakeLeft, realEuclideanTakeRight]
      simpa only [projectedZeroMatrixFiberMap,
        realEuclideanAppend_castAdd] using hsource
    · intro i
      simpa [projectedZeroMatrixFiberMap, matrixFiberMulVecPolynomial,
        flatSquareMatrixMulVec, flatSquareMatrixEntry,
        matrixFiberMatrixIndex, matrixFiberXIndex,
        realEuclideanTakeLeft, realEuclideanTakeRight,
        realEuclideanAppend] using
        hG.polynomial (matrixFiberMulVecPolynomial n q i)
  · intro k'
    simpa [projectedZeroMatrixFiberMap, matrixFiberMatrixIndex,
      realEuclideanTakeLeft, realEuclideanTakeRight,
      realEuclideanAppend] using
      hG.polynomial
        (MvPolynomial.X (matrixFiberMatrixIndex n q k'))

theorem projectedZeroMatrixFiberMap_append_eq_target_iff
    {n q : ℕ} (f : RealEuclideanFunction (n + q))
    (x : RealEuclidean n) (z : RealEuclidean q)
    (M' M : FlatSquareMatrix n) (b : RealEuclidean n) :
    projectedZeroMatrixFiberMap f
          (realEuclideanAppend x (realEuclideanAppend z M')) =
        projectedZeroMatrixFiberTarget M b ↔
      f (realEuclideanAppend x z) = 0 ∧
        flatSquareMatrixMulVec M x = b ∧ M' = M := by
  constructor
  · intro h
    have hf := congrFun h
      (Fin.castAdd (n * n) (Fin.castAdd n (0 : Fin 1)))
    have hmul : flatSquareMatrixMulVec M' x = b := by
      funext i
      have hi := congrFun h
        (Fin.castAdd (n * n) (Fin.natAdd 1 i))
      simpa [projectedZeroMatrixFiberMap,
        projectedZeroMatrixFiberTarget] using hi
    have hM : M' = M := by
      funext k
      have hk := congrFun h (Fin.natAdd (1 + n) k)
      simpa [projectedZeroMatrixFiberMap,
        projectedZeroMatrixFiberTarget] using hk
    refine ⟨?_, ?_, hM⟩
    · simpa [projectedZeroMatrixFiberMap,
        projectedZeroMatrixFiberTarget] using hf
    · simpa [hM] using hmul
  · rintro ⟨hf, hmul, rfl⟩
    ext k
    refine Fin.addCases ?_ ?_ k
    · intro k'
      refine Fin.addCases ?_ ?_ k'
      · intro i
        have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
        subst i
        simpa [projectedZeroMatrixFiberMap,
          projectedZeroMatrixFiberTarget] using hf
      · intro i
        simpa [projectedZeroMatrixFiberMap,
          projectedZeroMatrixFiberTarget] using congrFun hmul i
    · intro k'
      simp [projectedZeroMatrixFiberMap,
        projectedZeroMatrixFiberTarget]

/-- The visible-coordinate projection of the fiber at `(0,b,M)` is exactly
the intersection of the projected zero set of `f` with `Mx=b`. -/
theorem flatProjectedFiberSet_projectedZeroMatrixFiberMap
    {n q : ℕ} (f : RealEuclideanFunction (n + q))
    (M : FlatSquareMatrix n) (b : RealEuclidean n) :
    flatProjectedFiberSet (n := n) (q := q + n * n)
        (projectedZeroMatrixFiberMap f)
        (projectedZeroMatrixFiberTarget M b) =
      {x | (∃ z : RealEuclidean q,
          f (realEuclideanAppend x z) = 0) ∧
        flatSquareMatrixMulVec M x = b} := by
  ext x
  constructor
  · rintro ⟨zM, hzM⟩
    let z : RealEuclidean q := realEuclideanTakeLeft zM
    let M' : FlatSquareMatrix n := realEuclideanTakeRight zM
    have hzMdecomp : zM = realEuclideanAppend z M' := by
      exact (realEuclideanAppend_take zM).symm
    rw [hzMdecomp] at hzM
    rcases (projectedZeroMatrixFiberMap_append_eq_target_iff
      f x z M' M b).mp hzM with ⟨hz, hmul, hM⟩
    exact ⟨⟨z, hz⟩, hmul⟩
  · rintro ⟨⟨z, hz⟩, hmul⟩
    refine ⟨realEuclideanAppend z M, ?_⟩
    exact (projectedZeroMatrixFiberMap_append_eq_target_iff
      f x z M M b).mpr ⟨hz, hmul, rfl⟩

/-- One component bound works simultaneously for every flat matrix `M` and
every right-hand side `b`.  This is the exact W5 estimate for a fixed
projected-zero presentation. -/
theorem exists_projectedZero_matrixSection_component_bound
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n q : ℕ} {A : Set (RealEuclidean n)}
    {f : RealEuclideanFunction (n + q)}
    (hf : f ∈ G (n + q))
    (hA : A = {x | ∃ z : RealEuclidean q,
      f (realEuclideanAppend x z) = 0}) :
    ∃ N : ℕ, ∀ (M : FlatSquareMatrix n) (b : RealEuclidean n),
      ENat.card (ConnectedComponents
        ((A ∩ {x | flatSquareMatrixMulVec M x = b}) :
          Set (RealEuclidean n))) ≤ N := by
  have htuple := functionTupleInFamily_projectedZeroMatrixFiberMap hG hf
  obtain ⟨N, hN⟩ :=
    hUFF.exists_flatProjectedFiber_component_bound
      (projectedZeroMatrixFiberMap f) htuple
  refine ⟨N, fun M b ↦ ?_⟩
  rw [hA]
  change ENat.card (ConnectedComponents
    ({x | (∃ z : RealEuclidean q,
      f (realEuclideanAppend x z) = 0) ∧
      flatSquareMatrixMulVec M x = b} : Set (RealEuclidean n))) ≤ N
  rw [← flatProjectedFiberSet_projectedZeroMatrixFiberMap f M b]
  exact hN (projectedZeroMatrixFiberTarget M b)

/-- W5's matrix-section estimate for every projected zero set of `G`. -/
theorem IsProjectedZeroSet.exists_matrixSection_component_bound
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {n : ℕ} {A : Set (RealEuclidean n)}
    (hA : IsProjectedZeroSet G A) :
    ∃ N : ℕ, ∀ (M : FlatSquareMatrix n) (b : RealEuclidean n),
      ENat.card (ConnectedComponents
        ((A ∩ {x | flatSquareMatrixMulVec M x = b}) :
          Set (RealEuclidean n))) ≤ N := by
  obtain ⟨q, f, hf, hAf⟩ := hA
  exact exists_projectedZero_matrixSection_component_bound
    hG hUFF hf hAf

/-- Abel-family specialization of the W5 matrix-section estimate. -/
theorem exists_abelProjectedZero_matrixSection_component_bound
    {Afun : ℝ → ℝ}
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily Afun))
    {n : ℕ} {A : Set (RealEuclidean n)}
    (hA : IsProjectedZeroSet (abelGeometricFamily Afun) A) :
    ∃ N : ℕ, ∀ (M : FlatSquareMatrix n) (b : RealEuclidean n),
      ENat.card (ConnectedComponents
        ((A ∩ {x | flatSquareMatrixMulVec M x = b}) :
          Set (RealEuclidean n))) ≤ N :=
  hA.exists_matrixSection_component_bound
    (isGeometricFunctionFamily_abelGeometricFamily Afun) hUFF

end AbelFormalization
