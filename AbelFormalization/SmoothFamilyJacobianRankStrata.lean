import AbelFormalization.SmoothFamilyRectangularRankLocus
import Mathlib.Data.Fin.Embedding

/-!
# Square minors and pointwise Jacobian rank strata

This file provides only the finite linear algebra behind a rank decomposition.
A `k × k` minor selects both `k` output rows and `k` source columns.  Some such
minor is nonzero exactly when the matrix rank is at least `k`; exact rank `k`
is therefore characterized by one nonzero `k`-minor and the vanishing of all
`(k+1)`-minors.  Applied to a smooth family tuple, all of the corresponding
minor functions remain in the original geometric derivative-closed family.

No manifold stratification or global triviality statement is asserted here.
-/

noncomputable section

open Set Function
open scoped ContDiff Matrix

namespace AbelFormalization

set_option autoImplicit false

/-- A square minor of a standard rectangular Jacobian, with independently
selected output rows and source columns. -/
def standardJacobianMinor {a b k : ℕ}
    (g : RealEuclidean a → RealEuclidean b)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a) :
    RealEuclideanFunction a :=
  fun x ↦ ((standardRectangularJacobian g x).submatrix rows cols).det

/-- A finite matrix has rank at least `k` exactly when one `k × k` square
submatrix has nonzero determinant. -/
theorem matrix_le_rank_iff_exists_square_minor_ne_zero
    {K : Type*} [Field K] {a b k : ℕ}
    (A : Matrix (Fin b) (Fin a) K) :
    k ≤ A.rank ↔
      ∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin a,
        (A.submatrix rows cols).det ≠ 0 := by
  classical
  constructor
  · intro hk
    obtain ⟨κ, col, hcol, hspan, hli⟩ :=
      exists_linearIndependent' K A.col
    letI : Finite κ := Finite.of_injective col hcol
    letI : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = A.rank := by
      rw [← finrank_span_eq_card hli, hspan,
        ← Matrix.rank_eq_finrank_span_cols]
    have hkcard : k ≤ Fintype.card κ := by
      rw [hcard]
      exact hk
    let pick : Fin k ↪ κ :=
      (Fin.castLEEmb hkcard).trans (Fintype.equivFin κ).symm.toEmbedding
    let cols : Fin k ↪ Fin a :=
      ⟨col ∘ pick, hcol.comp pick.injective⟩
    have hcolsLI : LinearIndependent K (A.submatrix id cols).col := by
      change LinearIndependent K ((A.col ∘ col) ∘ pick)
      exact hli.comp pick pick.injective
    have hcolumnRank : (A.submatrix id cols).rank = k := by
      rw [Matrix.rank_eq_finrank_span_cols,
        finrank_span_eq_card hcolsLI, Fintype.card_fin]
    have htransposeRank : ((A.submatrix id cols)ᵀ).rank = k := by
      rw [Matrix.rank_transpose, hcolumnRank]
    obtain ⟨rows, hrows⟩ :=
      exists_column_minor_of_rank_eq ((A.submatrix id cols)ᵀ)
        htransposeRank
    refine ⟨rows, cols, ?_⟩
    have hmatrix :
        ((A.submatrix id cols)ᵀ).submatrix id rows =
          (A.submatrix rows cols)ᵀ := by
      ext i j
      rfl
    rw [hmatrix] at hrows
    simpa only [Matrix.det_transpose] using hrows
  · rintro ⟨rows, cols, hminor⟩
    calc
      k = (A.submatrix rows cols).rank := by
        symm
        simpa only [Fintype.card_fin] using
          Matrix.rank_of_det_ne_zero hminor
      _ ≤ A.rank := Matrix.rank_submatrix_le A rows cols

/-- Rank is at most `k` exactly when every `(k+1) × (k+1)` square minor
vanishes. -/
theorem matrix_rank_le_iff_all_succ_square_minors_eq_zero
    {K : Type*} [Field K] {a b k : ℕ}
    (A : Matrix (Fin b) (Fin a) K) :
    A.rank ≤ k ↔
      ∀ rows : Fin (k + 1) ↪ Fin b, ∀ cols : Fin (k + 1) ↪ Fin a,
        (A.submatrix rows cols).det = 0 := by
  classical
  constructor
  · intro hrank rows cols
    by_contra hminor
    have hsucc : k + 1 ≤ A.rank := by
      calc
        k + 1 = (A.submatrix rows cols).rank := by
          symm
          simpa only [Fintype.card_fin] using
            Matrix.rank_of_det_ne_zero hminor
        _ ≤ A.rank := Matrix.rank_submatrix_le A rows cols
    exact (Nat.not_succ_le_self k) (hsucc.trans hrank)
  · intro hminor
    by_contra hrank
    have hsucc : k + 1 ≤ A.rank :=
      Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hrank)
    obtain ⟨rows, cols, hne⟩ :=
      (matrix_le_rank_iff_exists_square_minor_ne_zero A).mp hsucc
    exact hne (hminor rows cols)

/-- Exact matrix rank is characterized by one nonzero minor of that size and
the vanishing of all minors of the next size. -/
theorem matrix_rank_eq_iff_square_minors
    {K : Type*} [Field K] {a b k : ℕ}
    (A : Matrix (Fin b) (Fin a) K) :
    A.rank = k ↔
      (∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin a,
        (A.submatrix rows cols).det ≠ 0) ∧
      (∀ rows : Fin (k + 1) ↪ Fin b,
        ∀ cols : Fin (k + 1) ↪ Fin a,
          (A.submatrix rows cols).det = 0) := by
  constructor
  · intro hrank
    constructor
    · apply (matrix_le_rank_iff_exists_square_minor_ne_zero A).mp
      exact hrank.symm.le
    · apply (matrix_rank_le_iff_all_succ_square_minors_eq_zero A).mp
      exact hrank.le
  · rintro ⟨hlower, hupper⟩
    exact le_antisymm
      ((matrix_rank_le_iff_all_succ_square_minors_eq_zero A).mpr hupper)
      ((matrix_le_rank_iff_exists_square_minor_ne_zero A).mpr hlower)

/-- Every square Jacobian minor belongs to a geometric family closed under
coordinate differentiation. -/
theorem IsGeometricFunctionFamily.standardJacobianMinor_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b k : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g)
    (rows : Fin k ↪ Fin b) (cols : Fin k ↪ Fin a) :
    standardJacobianMinor g rows cols ∈ G a := by
  let M : Matrix (Fin k) (Fin k) (RealEuclideanFunction a) :=
    fun i j x ↦ fderiv ℝ (fun y ↦ g y (rows i)) x
      ((Pi.basisFun ℝ (Fin a)) (cols j))
  have hM : ∀ i j, M i j ∈ G a := by
    intro i j
    simpa only [M, Pi.basisFun_apply] using
      hderiv a (fun y ↦ g y (rows i)) (hg (rows i)) (cols j)
  have hdet : Matrix.det M ∈ G a := hG.matrix_det_mem M hM
  convert hdet using 1
  funext x
  change Matrix.det
      ((Pi.evalRingHom (fun _ : RealEuclidean a ↦ ℝ) x).mapMatrix M) =
    (Pi.evalRingHom (fun _ : RealEuclidean a ↦ ℝ) x) (Matrix.det M)
  exact ((Pi.evalRingHom (fun _ : RealEuclidean a ↦ ℝ) x).map_det M).symm

/-- The rank of the standard rectangular Jacobian is the dimension of the
range of the Fréchet derivative. -/
theorem standardRectangularJacobian_rank_eq_finrank_range_fderiv
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {x : RealEuclidean a} (hg : DifferentiableAt ℝ g x) :
    (standardRectangularJacobian g x).rank =
      Module.finrank ℝ (LinearMap.range (fderiv ℝ g x).toLinearMap) := by
  have hmap : (fderiv ℝ g x).toLinearMap =
      (standardRectangularJacobian g x).mulVecLin := by
    apply LinearMap.ext
    intro v
    exact fderiv_eq_standardRectangularJacobian_mulVec hg v
  change Module.finrank ℝ
      (LinearMap.range (standardRectangularJacobian g x).mulVecLin) =
    Module.finrank ℝ (LinearMap.range (fderiv ℝ g x).toLinearMap)
  rw [← hmap]

/-- Pointwise exact derivative rank is expressed by nonvanishing and vanishing
of the corresponding Jacobian minors. -/
theorem finrank_range_fderiv_eq_iff_standardJacobianMinors
    {a b k : ℕ} {g : RealEuclidean a → RealEuclidean b}
    {x : RealEuclidean a} (hg : DifferentiableAt ℝ g x) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ g x).toLinearMap) = k ↔
      (∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin a,
        standardJacobianMinor g rows cols x ≠ 0) ∧
      (∀ rows : Fin (k + 1) ↪ Fin b,
        ∀ cols : Fin (k + 1) ↪ Fin a,
          standardJacobianMinor g rows cols x = 0) := by
  rw [← standardRectangularJacobian_rank_eq_finrank_range_fderiv hg]
  simpa only [standardJacobianMinor] using
    matrix_rank_eq_iff_square_minors (standardRectangularJacobian g x)

/-- The pointwise locus on which the derivative has rank exactly `k`. -/
def standardJacobianRankLocus {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (k : ℕ) :
    Set (RealEuclidean a) :=
  {x | Module.finrank ℝ (LinearMap.range (fderiv ℝ g x).toLinearMap) = k}

/-- For a tuple in an everywhere-smooth family, exact-rank-locus membership is
the finite minor condition at that point. -/
theorem IsEverywhereSmoothFunctionFamily.mem_standardJacobianRankLocus_iff
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) (k : ℕ) (x : RealEuclidean a) :
    x ∈ standardJacobianRankLocus g k ↔
      (∃ rows : Fin k ↪ Fin b, ∃ cols : Fin k ↪ Fin a,
        standardJacobianMinor g rows cols x ≠ 0) ∧
      (∀ rows : Fin (k + 1) ↪ Fin b,
        ∀ cols : Fin (k + 1) ↪ Fin a,
          standardJacobianMinor g rows cols x = 0) := by
  have hgSmooth : ContDiff ℝ ∞ g := by
    rw [contDiff_pi]
    intro i
    exact hsmooth a (fun y ↦ g y i) (hg i)
  exact finrank_range_fderiv_eq_iff_standardJacobianMinors
    ((hgSmooth.differentiable (by simp)).differentiableAt)

end AbelFormalization
