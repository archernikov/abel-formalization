import AbelFormalization.RestrictedSystemLastGeneratorLift
import AbelFormalization.DirectionalJacobian

/-!
# Expression-level construction of the critical-point system

For a curve cut out by `r` equations in an `(r+1)`-dimensional coordinate
space, the manuscript appends squared distance to a center, takes the
determinant of the resulting derivative matrix, and then appends that
determinant to the original equations.  This file proves that the entire
construction remains in any directionally closed function algebra.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Append one final component to a finite tuple of functions. -/
def functionTupleSnoc {r : ℕ} (F : Fin r → X → ℝ) (last : X → ℝ) :
    Fin (r + 1) → X → ℝ :=
  Fin.lastCases last F

@[simp]
theorem functionTupleSnoc_last {r : ℕ} (F : Fin r → X → ℝ)
    (last : X → ℝ) :
    functionTupleSnoc F last (Fin.last r) = last := by
  simp [functionTupleSnoc]

@[simp]
theorem functionTupleSnoc_castSucc {r : ℕ} (F : Fin r → X → ℝ)
    (last : X → ℝ) (i : Fin r) :
    functionTupleSnoc F last i.castSucc = F i := by
  simp [functionTupleSnoc]

theorem functionTupleSnoc_mem_subalgebra
    {r : ℕ} (B : Subalgebra ℝ (X → ℝ))
    (F : Fin r → X → ℝ) (last : X → ℝ)
    (hF : ∀ i, F i ∈ B) (hlast : last ∈ B) :
    ∀ i, functionTupleSnoc F last i ∈ B := by
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa using hlast
  · simpa using hF j

/-- Squared Euclidean distance expressed through a supplied coordinate
tuple. -/
def algebraicSquaredDistance {r : ℕ}
    (coordinate : Fin r → X → ℝ) (center : Fin r → ℝ) : X → ℝ :=
  ∑ i, (coordinate i - fun _ ↦ center i) ^ 2

@[simp]
theorem algebraicSquaredDistance_apply {r : ℕ}
    (coordinate : Fin r → X → ℝ) (center : Fin r → ℝ) (x : X) :
    algebraicSquaredDistance coordinate center x =
      ∑ i, (coordinate i x - center i) ^ 2 := by
  simp [algebraicSquaredDistance]

theorem algebraicSquaredDistance_mem_subalgebra
    {r : ℕ} (B : Subalgebra ℝ (X → ℝ))
    (coordinate : Fin r → X → ℝ) (center : Fin r → ℝ)
    (hcoordinate : ∀ i, coordinate i ∈ B) :
    algebraicSquaredDistance coordinate center ∈ B := by
  unfold algebraicSquaredDistance
  apply Subalgebra.sum_mem
  intro i hi
  apply B.pow_mem
  apply B.sub_mem (hcoordinate i)
  change (algebraMap ℝ (X → ℝ) (center i)) ∈ B
  exact B.algebraMap_mem (center i)

/-- Expression-level critical-system construction.  `H` consists of `r`
curve equations, `basis` supplies the `(r+1)` derivative directions, and
`coordinate` supplies the corresponding Euclidean coordinate functions used
for squared distance. -/
theorem exists_criticalSystemExpressions
    {r : ℕ} (B : Subalgebra ℝ (X → ℝ)) (Omega : Set X)
    (H : Fin r → X → ℝ)
    (basis : Fin (r + 1) → X)
    (coordinate : Fin (r + 1) → X → ℝ)
    (center : Fin (r + 1) → ℝ)
    (hH : ∀ i, H i ∈ B)
    (hcoordinate : ∀ i, coordinate i ∈ B)
    (hclosed : ∀ j, DirectionallyClosedOn B Omega (basis j)) :
    ∃ rho K : X → ℝ,
      ∃ derivative : Matrix (Fin (r + 1)) (Fin (r + 1)) (X → ℝ),
      rho = algebraicSquaredDistance coordinate center ∧
      rho ∈ B ∧ K ∈ B ∧
      (∀ i, functionTupleSnoc H K i ∈ B) ∧
      (∀ i j, derivative i j ∈ B) ∧
      (∀ x ∈ Omega, ∀ i j,
        DifferentiableAt ℝ (functionTupleSnoc H rho i) x ∧
          derivative i j x =
            fderiv ℝ (functionTupleSnoc H rho i) x (basis j)) ∧
      (∀ x ∈ Omega,
        K x = Matrix.det (fun i j ↦
          fderiv ℝ (functionTupleSnoc H rho i) x (basis j))) := by
  let rho := algebraicSquaredDistance coordinate center
  have hrho : rho ∈ B :=
    algebraicSquaredDistance_mem_subalgebra B coordinate center hcoordinate
  have htuple : ∀ i, functionTupleSnoc H rho i ∈ B :=
    functionTupleSnoc_mem_subalgebra B H rho hH hrho
  obtain ⟨derivative, K, hderivative, hK, hderivEq, hKEq⟩ :=
    exists_directionalJacobianDeterminant B Omega basis
      (functionTupleSnoc H rho) htuple hclosed
  refine ⟨rho, K, derivative, rfl, hrho, hK,
    functionTupleSnoc_mem_subalgebra B H K hH hK,
    hderivative, hderivEq, hKEq⟩

/-- The preceding construction specialized to an Abel expression tower,
where directional closure is already available in every direction. -/
theorem IsAbel.exists_restrictedAbelTower_criticalSystemExpressions
    {A : ℝ → ℝ} (hA : IsAbel A)
    {ι : Type*} {m p a ell r : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (level : ℕ) (H : Fin r → RestrictedSource m p a → ℝ)
    (basis : Fin (r + 1) → RestrictedSource m p a)
    (coordinate : Fin (r + 1) → RestrictedSource m p a → ℝ)
    (center : Fin (r + 1) → ℝ)
    (hH : ∀ i, H i ∈ T.level level)
    (hcoordinate : ∀ i, coordinate i ∈ T.level level) :
    ∃ rho K : RestrictedSource m p a → ℝ,
      ∃ derivative : Matrix (Fin (r + 1)) (Fin (r + 1))
        (RestrictedSource m p a → ℝ),
      rho = algebraicSquaredDistance coordinate center ∧
      rho ∈ T.level level ∧ K ∈ T.level level ∧
      (∀ i, functionTupleSnoc H K i ∈ T.level level) ∧
      (∀ i j, derivative i j ∈ T.level level) ∧
      (∀ x ∈ restrictedAbelJetDomain (a := a) D representative offset,
        ∀ i j, DifferentiableAt ℝ (functionTupleSnoc H rho i) x ∧
          derivative i j x =
            fderiv ℝ (functionTupleSnoc H rho i) x (basis j)) ∧
      (∀ x ∈ restrictedAbelJetDomain (a := a) D representative offset,
        K x = Matrix.det (fun i j ↦
          fderiv ℝ (functionTupleSnoc H rho i) x (basis j))) := by
  apply exists_criticalSystemExpressions (T.level level)
    (restrictedAbelJetDomain (a := a) D representative offset)
    H basis coordinate center hH hcoordinate
  intro j
  exact hA.restrictedAbelTower_directionallyClosedOn_level
    representative offset T (basis j) level

end AbelFormalization
