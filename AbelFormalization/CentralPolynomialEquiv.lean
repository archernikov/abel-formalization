import AbelFormalization.StirlingParameterHom
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Ideal.Height

set_option autoImplicit false

/-!
# The final central polynomial change of coordinates

Its project-level predecessor is `AbelFormalization.StirlingParameterHom`.
The later complete central-ideal assembly can import this file and
`AbelFormalization.CentralLaurentContraction`; neither one needs to import the
other.

For each block `b`, the variables are indexed by `Fin (d b)`, where index `r`
represents the positive derivative order `r + 1`.  The forward map is the
lower-triangular signed-Stirling change of basis, with diagonal one.  Every
retained time variable is translated by one.  The inverse is constructed from
the nonsingular inverse of the finite unitriangular matrix; thus no
invertibility hypothesis on the coefficient ring or on the matrix is assumed.
-/

noncomputable section

open scoped BigOperators

namespace AbelFormalization

universe u v w

/-- Polynomial symbols consist of a dependent family of finite derivative
blocks and a family of retained time symbols. -/
abbrev CentralPolynomialIndex (Block : Type v) (d : Block → ℕ) (Time : Type w) :=
  (Σ b : Block, Fin (d b)) ⊕ Time

/-- The polynomial ring on the finite blocks and retained time symbols. -/
abbrev CentralPolynomial (R : Type u) [CommSemiring R]
    (Block : Type v) (d : Block → ℕ)
    (Time : Type w) :=
  MvPolynomial (CentralPolynomialIndex Block d Time) R

variable (R : Type u) [CommRing R]
variable (Block : Type v) (d : Block → ℕ) (Time : Type w)

/-- The signed-Stirling matrix on a block of length `n`.  Rows and columns use
the zero-based indices for the positive orders `i+1` and `j+1`. -/
def centralSignedStirlingMatrix (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j ↦
    if j ≤ i then (signedStirling (i.val + 1) (j.val + 1) : R) else 0

@[simp]
theorem centralSignedStirlingMatrix_apply_of_le (n : ℕ) {i j : Fin n} (hji : j ≤ i) :
    centralSignedStirlingMatrix R n i j =
      (signedStirling (i.val + 1) (j.val + 1) : R) := by
  simp [centralSignedStirlingMatrix, hji]

@[simp]
theorem centralSignedStirlingMatrix_apply_of_lt (n : ℕ) {i j : Fin n} (hij : i < j) :
    centralSignedStirlingMatrix R n i j = 0 := by
  simp [centralSignedStirlingMatrix, not_le_of_gt hij]

/-- The matrix is genuinely lower triangular. -/
theorem centralSignedStirlingMatrix_isLowerTriangular (n : ℕ) :
    (centralSignedStirlingMatrix R n).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  exact centralSignedStirlingMatrix_apply_of_lt R n hij

/-- The diagonal is one, using the leading coefficient of the falling
factorial rather than an assumption on the matrix. -/
@[simp]
theorem centralSignedStirlingMatrix_diag (n : ℕ) (i : Fin n) :
    centralSignedStirlingMatrix R n i i = 1 := by
  simp [centralSignedStirlingMatrix, signedStirling_self]

/-- Unitriangularity forces determinant one over every commutative ring. -/
@[simp]
theorem centralSignedStirlingMatrix_det (n : ℕ) :
    (centralSignedStirlingMatrix R n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _
    (centralSignedStirlingMatrix_isLowerTriangular R n)]
  simp only [centralSignedStirlingMatrix_diag, Finset.prod_const_one]

theorem centralSignedStirlingMatrix_isUnit_det (n : ℕ) :
    IsUnit (centralSignedStirlingMatrix R n).det := by
  rw [centralSignedStirlingMatrix_det]
  exact isUnit_one

/-- The actual matrix inverse is a right inverse. -/
@[simp]
theorem centralSignedStirlingMatrix_mul_inv (n : ℕ) :
    centralSignedStirlingMatrix R n * (centralSignedStirlingMatrix R n)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (centralSignedStirlingMatrix_isUnit_det R n)

/-- The actual matrix inverse is also a left inverse. -/
@[simp]
theorem centralSignedStirlingMatrix_inv_mul (n : ℕ) :
    (centralSignedStirlingMatrix R n)⁻¹ * centralSignedStirlingMatrix R n = 1 :=
  Matrix.nonsing_inv_mul _ (centralSignedStirlingMatrix_isUnit_det R n)

/-- A block-diagonal linear substitution together with an independent
translation of every time variable. -/
def centralBlockAffineVariable
    (A : ∀ b : Block, Matrix (Fin (d b)) (Fin (d b)) R)
    (c : Time → R) :
    CentralPolynomialIndex Block d Time → CentralPolynomial R Block d Time
  | Sum.inl ⟨b, i⟩ =>
      ∑ j : Fin (d b), MvPolynomial.C (A b i j) *
        MvPolynomial.X
          (Sum.inl ⟨b, j⟩ : CentralPolynomialIndex Block d Time)
  | Sum.inr t =>
      MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time) +
        MvPolynomial.C (c t)

/-- The algebra homomorphism induced by `centralBlockAffineVariable`. -/
def centralBlockAffineHom
    (A : ∀ b : Block, Matrix (Fin (d b)) (Fin (d b)) R)
    (c : Time → R) :
    CentralPolynomial R Block d Time →ₐ[R] CentralPolynomial R Block d Time :=
  MvPolynomial.aeval (centralBlockAffineVariable R Block d Time A c)

@[simp]
theorem centralBlockAffineHom_C
    (A : ∀ b : Block, Matrix (Fin (d b)) (Fin (d b)) R)
    (c : Time → R) (r : R) :
    centralBlockAffineHom R Block d Time A c (MvPolynomial.C r) =
      MvPolynomial.C r := by
  simp [centralBlockAffineHom]

@[simp]
theorem centralBlockAffineHom_X_block
    (A : ∀ b : Block, Matrix (Fin (d b)) (Fin (d b)) R)
    (c : Time → R) (b : Block) (i : Fin (d b)) :
    centralBlockAffineHom R Block d Time A c
        (MvPolynomial.X
          (Sum.inl ⟨b, i⟩ : CentralPolynomialIndex Block d Time)) =
      ∑ j : Fin (d b), MvPolynomial.C (A b i j) *
        MvPolynomial.X
          (Sum.inl ⟨b, j⟩ : CentralPolynomialIndex Block d Time) := by
  simp [centralBlockAffineHom, centralBlockAffineVariable]

@[simp]
theorem centralBlockAffineHom_X_time
    (A : ∀ b : Block, Matrix (Fin (d b)) (Fin (d b)) R)
    (c : Time → R) (t : Time) :
    centralBlockAffineHom R Block d Time A c
        (MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time)) =
      MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time) +
        MvPolynomial.C (c t) := by
  simp [centralBlockAffineHom, centralBlockAffineVariable]

/-- Composition is blockwise matrix multiplication.  Notice the order
`B * A`: `A` is the outer homomorphism and `B` the inner one. -/
theorem centralBlockAffineHom_comp
    (A B : ∀ b : Block, Matrix (Fin (d b)) (Fin (d b)) R)
    (c e : Time → R) :
    (centralBlockAffineHom R Block d Time A c).comp
        (centralBlockAffineHom R Block d Time B e) =
      centralBlockAffineHom R Block d Time (fun b ↦ B b * A b)
        (fun t ↦ c t + e t) := by
  classical
  apply MvPolynomial.algHom_ext
  intro x
  rcases x with ⟨b, i⟩ | t
  · simp only [AlgHom.comp_apply, centralBlockAffineHom_X_block]
    calc
      centralBlockAffineHom R Block d Time A c
          (∑ j : Fin (d b), MvPolynomial.C (B b i j) *
            MvPolynomial.X
              (Sum.inl ⟨b, j⟩ : CentralPolynomialIndex Block d Time)) =
          ∑ j : Fin (d b), ∑ k : Fin (d b),
            MvPolynomial.C (B b i j * A b j k) *
              MvPolynomial.X
                (Sum.inl ⟨b, k⟩ : CentralPolynomialIndex Block d Time) := by
            simp [Finset.mul_sum, mul_assoc]
      _ = ∑ k : Fin (d b), ∑ j : Fin (d b),
            MvPolynomial.C (B b i j * A b j k) *
              MvPolynomial.X
                (Sum.inl ⟨b, k⟩ : CentralPolynomialIndex Block d Time) :=
        Finset.sum_comm
      _ = ∑ k : Fin (d b), MvPolynomial.C ((B b * A b) i k) *
            MvPolynomial.X
              (Sum.inl ⟨b, k⟩ : CentralPolynomialIndex Block d Time) := by
            simp [Matrix.mul_apply, Finset.sum_mul]
  · simp [AlgHom.comp_apply, add_assoc]

/-- Identity matrices and zero translations induce the identity algebra
homomorphism. -/
theorem centralBlockAffineHom_one_zero :
    centralBlockAffineHom R Block d Time
        (fun b ↦ (1 : Matrix (Fin (d b)) (Fin (d b)) R))
        (fun _ ↦ 0) =
      AlgHom.id R (CentralPolynomial R Block d Time) := by
  classical
  apply MvPolynomial.algHom_ext
  intro x
  rcases x with ⟨b, i⟩ | t
  · simp [Matrix.one_apply]
  · simp

/-- The forward homomorphism: signed-Stirling on every finite block and
`t ↦ t + 1` on every retained time variable. -/
def centralPolynomialForwardHom :
    CentralPolynomial R Block d Time →ₐ[R] CentralPolynomial R Block d Time :=
  centralBlockAffineHom R Block d Time
    (fun b ↦ centralSignedStirlingMatrix R (d b)) (fun _ ↦ 1)

/-- The explicit inverse homomorphism: the nonsingular inverse on every
finite block and `t ↦ t - 1` on retained time variables. -/
def centralPolynomialInverseHom :
    CentralPolynomial R Block d Time →ₐ[R] CentralPolynomial R Block d Time :=
  centralBlockAffineHom R Block d Time
    (fun b ↦ (centralSignedStirlingMatrix R (d b))⁻¹) (fun _ ↦ -1)

theorem centralPolynomialForwardHom_comp_inverseHom :
    (centralPolynomialForwardHom R Block d Time).comp
        (centralPolynomialInverseHom R Block d Time) =
      AlgHom.id R (CentralPolynomial R Block d Time) := by
  calc
    (centralPolynomialForwardHom R Block d Time).comp
        (centralPolynomialInverseHom R Block d Time) =
      centralBlockAffineHom R Block d Time
        (fun b ↦ (centralSignedStirlingMatrix R (d b))⁻¹ *
          centralSignedStirlingMatrix R (d b))
        (fun _ ↦ (1 : R) + (-1)) :=
      centralBlockAffineHom_comp R Block d Time _ _ _ _
    _ = centralBlockAffineHom R Block d Time
        (fun b ↦ (1 : Matrix (Fin (d b)) (Fin (d b)) R))
        (fun _ ↦ 0) := by
      have hm :
          (fun b ↦ (centralSignedStirlingMatrix R (d b))⁻¹ *
              centralSignedStirlingMatrix R (d b)) =
            (fun b ↦ (1 : Matrix (Fin (d b)) (Fin (d b)) R)) := by
        funext b
        exact centralSignedStirlingMatrix_inv_mul R (d b)
      have hc : (fun _ : Time ↦ (1 : R) + (-1)) = (fun _ ↦ 0) := by
        funext t
        simp
      rw [hm, hc]
    _ = AlgHom.id R (CentralPolynomial R Block d Time) :=
      centralBlockAffineHom_one_zero R Block d Time

theorem centralPolynomialInverseHom_comp_forwardHom :
    (centralPolynomialInverseHom R Block d Time).comp
        (centralPolynomialForwardHom R Block d Time) =
      AlgHom.id R (CentralPolynomial R Block d Time) := by
  calc
    (centralPolynomialInverseHom R Block d Time).comp
        (centralPolynomialForwardHom R Block d Time) =
      centralBlockAffineHom R Block d Time
        (fun b ↦ centralSignedStirlingMatrix R (d b) *
          (centralSignedStirlingMatrix R (d b))⁻¹)
        (fun _ ↦ (-1 : R) + 1) :=
      centralBlockAffineHom_comp R Block d Time _ _ _ _
    _ = centralBlockAffineHom R Block d Time
        (fun b ↦ (1 : Matrix (Fin (d b)) (Fin (d b)) R))
        (fun _ ↦ 0) := by
      have hm :
          (fun b ↦ centralSignedStirlingMatrix R (d b) *
              (centralSignedStirlingMatrix R (d b))⁻¹) =
            (fun b ↦ (1 : Matrix (Fin (d b)) (Fin (d b)) R)) := by
        funext b
        exact centralSignedStirlingMatrix_mul_inv R (d b)
      have hc : (fun _ : Time ↦ (-1 : R) + 1) = (fun _ ↦ 0) := by
        funext t
        simp
      rw [hm, hc]
    _ = AlgHom.id R (CentralPolynomial R Block d Time) :=
      centralBlockAffineHom_one_zero R Block d Time

/-- The paper's final central polynomial equivalence `Φ`. -/
def centralPolynomialPhi :
    CentralPolynomial R Block d Time ≃ₐ[R] CentralPolynomial R Block d Time :=
  AlgEquiv.ofAlgHom
    (centralPolynomialForwardHom R Block d Time)
    (centralPolynomialInverseHom R Block d Time)
    (centralPolynomialForwardHom_comp_inverseHom R Block d Time)
    (centralPolynomialInverseHom_comp_forwardHom R Block d Time)

/-- Coefficients are fixed. -/
@[simp]
theorem centralPolynomialPhi_C (r : R) :
    centralPolynomialPhi R Block d Time (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [centralPolynomialPhi, centralPolynomialForwardHom]

/-- On every block, `Φ` is exactly the lower-triangular signed-Stirling
matrix, including explicit zeros above the diagonal. -/
@[simp]
theorem centralPolynomialPhi_X_block (b : Block) (i : Fin (d b)) :
    centralPolynomialPhi R Block d Time
        (MvPolynomial.X
          (Sum.inl ⟨b, i⟩ : CentralPolynomialIndex Block d Time)) =
      ∑ j : Fin (d b),
        MvPolynomial.C
          (if j ≤ i then (signedStirling (i.val + 1) (j.val + 1) : R) else 0) *
        MvPolynomial.X
          (Sum.inl ⟨b, j⟩ : CentralPolynomialIndex Block d Time) := by
  simp [centralPolynomialPhi, centralPolynomialForwardHom,
    centralSignedStirlingMatrix]

/-- Every retained time variable is translated by one. -/
@[simp]
theorem centralPolynomialPhi_X_time (t : Time) :
    centralPolynomialPhi R Block d Time
        (MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time)) =
      MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time) + 1 := by
  simp [centralPolynomialPhi, centralPolynomialForwardHom]

/-- The inverse sends retained time variables to `t - 1`. -/
@[simp]
theorem centralPolynomialPhi_symm_X_time (t : Time) :
    (centralPolynomialPhi R Block d Time).symm
        (MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time)) =
      MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time) - 1 := by
  simp [centralPolynomialPhi, centralPolynomialInverseHom, sub_eq_add_neg]

/-- Mapping any ideal through the final central equivalence preserves its
height.  No primality, properness, Noetherianity, or domain hypothesis is
needed. -/
@[simp]
theorem centralPolynomialPhi_height_map
    (I : Ideal (CentralPolynomial R Block d Time)) :
    (I.map (centralPolynomialPhi R Block d Time).toRingHom).height = I.height :=
  (centralPolynomialPhi R Block d Time).toRingEquiv.height_map I

/-- The reverse transport preserves height as well. -/
@[simp]
theorem centralPolynomialPhi_height_comap
    (I : Ideal (CentralPolynomial R Block d Time)) :
    (I.comap (centralPolynomialPhi R Block d Time).toRingHom).height = I.height :=
  (centralPolynomialPhi R Block d Time).toRingEquiv.height_comap I

end AbelFormalization
