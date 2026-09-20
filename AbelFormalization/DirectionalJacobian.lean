import AbelFormalization.RestrictedAbelJets
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Jacobian representatives inside a function algebra

Directional derivative closure supplies algebra-valued representatives for
all entries of a Jacobian matrix.  Since determinants are finite polynomial
expressions in their entries, the determinant has a representative in the
same algebra.  This is the formal expression-language step used for the
Jacobian factors in exponential adjunction.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A determinant of function-valued matrix entries belongs to a subalgebra
whenever every entry does. -/
theorem matrix_det_mem_subalgebra
    (B : Subalgebra ℝ (X → ℝ)) (M : Matrix κ κ (X → ℝ))
    (hM : ∀ i j, M i j ∈ B) : M.det ∈ B := by
  let MB : Matrix κ κ B := fun i j ↦ ⟨M i j, hM i j⟩
  have hmap := B.val.map_det MB
  have hmatrix : B.val.mapMatrix MB = M := by
    ext i j x
    rfl
  rw [hmatrix] at hmap
  rw [← hmap]
  exact (MB.det).property

/-- Evaluating a determinant over a function ring is the determinant of the
pointwise evaluated matrix. -/
theorem matrix_det_apply_function
    (M : Matrix κ κ (X → ℝ)) (x : X) :
    M.det x = Matrix.det (fun i j ↦ M i j x) := by
  have hmap := (Pi.evalRingHom (fun _ : X ↦ ℝ) x).map_det M
  have hmatrix : (Pi.evalRingHom (fun _ : X ↦ ℝ) x).mapMatrix M =
      (fun i j ↦ M i j x) := by
    ext i j
    rfl
  rw [hmatrix] at hmap
  exact hmap

/-- Representatives for every directional derivative entry can be chosen
simultaneously from a directionally closed function algebra. -/
theorem exists_directionalDerivativeMatrix
    (B : Subalgebra ℝ (X → ℝ)) (Omega : Set X)
    (basis : κ → X) (F : κ → X → ℝ)
    (hF : ∀ i, F i ∈ B)
    (hclosed : ∀ j, DirectionallyClosedOn B Omega (basis j)) :
    ∃ D : Matrix κ κ (X → ℝ),
      (∀ i j, D i j ∈ B) ∧
      (∀ x ∈ Omega, ∀ i j,
        DifferentiableAt ℝ (F i) x ∧
          D i j x = fderiv ℝ (F i) x (basis j)) := by
  have hchoice : ∀ i j, ∃ df : X → ℝ,
      df ∈ B ∧ HasDirectionalDerivOn Omega (basis j) (F i) df :=
    fun i j ↦ hclosed j (F i) (hF i)
  choose D hDmem hDderiv using hchoice
  refine ⟨D, hDmem, ?_⟩
  intro x hx i j
  have h := hDderiv i j x hx
  exact ⟨h.1, h.2.symm⟩

/-- The determinant of the actual directional Jacobian has a representative
in the same algebra, agreeing pointwise throughout the working domain. -/
theorem exists_directionalJacobianDeterminant
    (B : Subalgebra ℝ (X → ℝ)) (Omega : Set X)
    (basis : κ → X) (F : κ → X → ℝ)
    (hF : ∀ i, F i ∈ B)
    (hclosed : ∀ j, DirectionallyClosedOn B Omega (basis j)) :
    ∃ D : Matrix κ κ (X → ℝ), ∃ J : X → ℝ,
      (∀ i j, D i j ∈ B) ∧ J ∈ B ∧
      (∀ x ∈ Omega, ∀ i j,
        DifferentiableAt ℝ (F i) x ∧
          D i j x = fderiv ℝ (F i) x (basis j)) ∧
      (∀ x ∈ Omega,
        J x = Matrix.det (fun i j ↦ fderiv ℝ (F i) x (basis j))) := by
  obtain ⟨D, hDmem, hD⟩ :=
    exists_directionalDerivativeMatrix B Omega basis F hF hclosed
  refine ⟨D, D.det, hDmem, matrix_det_mem_subalgebra B D hDmem, hD, ?_⟩
  intro x hx
  rw [matrix_det_apply_function]
  congr 1
  funext i j
  exact (hD x hx i j).2

/-- Specialization to a finite exponential list over all shifted Abel jets.
It constructs expression-level representatives for the whole directional
Jacobian and its determinant. -/
theorem IsAbel.exists_restrictedAbelTower_directionalJacobianDeterminant
    {A : ℝ → ℝ} (hA : IsAbel A)
    {ι : Type*} {m p a ell : ℕ} {Dbox : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra Dbox)
    (T : RestrictedExpressionTower Dbox
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (j : ℕ) (basis : κ → RestrictedSource m p a)
    (F : κ → RestrictedSource m p a → ℝ)
    (hF : ∀ i, F i ∈ T.level j) :
    ∃ D : Matrix κ κ (RestrictedSource m p a → ℝ),
      ∃ J : RestrictedSource m p a → ℝ,
      (∀ i k, D i k ∈ T.level j) ∧ J ∈ T.level j ∧
      (∀ x ∈ restrictedAbelJetDomain (a := a) Dbox representative offset,
        ∀ i k, DifferentiableAt ℝ (F i) x ∧
          D i k x = fderiv ℝ (F i) x (basis k)) ∧
      (∀ x ∈ restrictedAbelJetDomain (a := a) Dbox representative offset,
        J x = Matrix.det (fun i k ↦ fderiv ℝ (F i) x (basis k))) := by
  apply exists_directionalJacobianDeterminant (T.level j)
    (restrictedAbelJetDomain (a := a) Dbox representative offset)
    basis F hF
  intro k
  exact hA.restrictedAbelTower_directionallyClosedOn_level
    representative offset T (basis k) j

end AbelFormalization
