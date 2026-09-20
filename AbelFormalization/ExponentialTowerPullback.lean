import AbelFormalization.PolynomialGraphLift
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Pullback and base enlargement for finite exponential towers

Finite exponential towers are stable under precomposition of all their
functions.  They may also be regarded as towers over a larger initial
function algebra.  These two operations formalize the auxiliary-variable
extensions used in exponential adjunction.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {X Y : Type*}

/-- Precomposition carries the generator adjoined at a given exponential
step to the corresponding generator of the pulled-back tower. -/
theorem image_exponentialStepGenerators_precomp
    {ell : ℕ} (exponent : Fin ell → X → ℝ) (phi : Y → X) (j : ℕ) :
    functionPrecompAlgHom phi '' exponentialStepGenerators exponent j =
      exponentialStepGenerators
        (fun i ↦ functionPrecompAlgHom phi (exponent i)) j := by
  ext f
  constructor
  · rintro ⟨g, ⟨hj, rfl⟩, rfl⟩
    exact ⟨hj, rfl⟩
  · rintro ⟨hj, rfl⟩
    refine ⟨exponentialGenerator exponent ⟨j, hj⟩, ⟨hj, rfl⟩, ?_⟩
    rfl

/-- Every level commutes with pullback of functions. -/
theorem map_exponentialLevels_precomp
    (base : Subalgebra ℝ (X → ℝ)) {ell : ℕ}
    (exponent : Fin ell → X → ℝ) (phi : Y → X) :
    ∀ j,
      (exponentialLevels base exponent j).map (functionPrecompAlgHom phi) =
        exponentialLevels (base.map (functionPrecompAlgHom phi))
          (fun i ↦ functionPrecompAlgHom phi (exponent i)) j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [exponentialLevels]
      rw [Algebra.map_sup, ih, AlgHom.map_adjoin,
        image_exponentialStepGenerators_precomp]

/-- Pull an exponential tower back along a map of source spaces. -/
def FiniteExponentialTower.pullback
    {ell : ℕ} {base : Subalgebra ℝ (X → ℝ)}
    (T : FiniteExponentialTower base ell) (phi : Y → X) :
    FiniteExponentialTower (base.map (functionPrecompAlgHom phi)) ell where
  exponent i := functionPrecompAlgHom phi (T.exponent i)
  exponent_mem_level i := by
    rw [← map_exponentialLevels_precomp base T.exponent phi i.val]
    rw [Subalgebra.mem_map]
    exact ⟨T.exponent i, T.exponent_mem i, rfl⟩

@[simp]
theorem FiniteExponentialTower.pullback_exponent_apply
    {ell : ℕ} {base : Subalgebra ℝ (X → ℝ)}
    (T : FiniteExponentialTower base ell) (phi : Y → X)
    (i : Fin ell) (y : Y) :
    (T.pullback phi).exponent i y = T.exponent i (phi y) :=
  rfl

@[simp]
theorem FiniteExponentialTower.pullback_generator_apply
    {ell : ℕ} {base : Subalgebra ℝ (X → ℝ)}
    (T : FiniteExponentialTower base ell) (phi : Y → X)
    (i : Fin ell) (y : Y) :
    (T.pullback phi).generator i y = T.generator i (phi y) :=
  rfl

theorem FiniteExponentialTower.pullback_level
    {ell : ℕ} {base : Subalgebra ℝ (X → ℝ)}
    (T : FiniteExponentialTower base ell) (phi : Y → X) (j : ℕ) :
    (T.level j).map (functionPrecompAlgHom phi) =
      (T.pullback phi).level j := by
  exact map_exponentialLevels_precomp base T.exponent phi j

/-- Enlarging the initial algebra enlarges every level of a fixed sequence
of proposed exponents. -/
theorem exponentialLevels_mono_base
    {base₁ base₂ : Subalgebra ℝ (X → ℝ)} (hbase : base₁ ≤ base₂)
    {ell : ℕ} (exponent : Fin ell → X → ℝ) :
    ∀ j, exponentialLevels base₁ exponent j ≤
      exponentialLevels base₂ exponent j := by
  intro j
  induction j with
  | zero => exact hbase
  | succ j ih =>
      exact sup_le_sup ih le_rfl

/-- Regard a tower as a tower over a larger base algebra. -/
def FiniteExponentialTower.changeBase
    {ell : ℕ} {base₁ base₂ : Subalgebra ℝ (X → ℝ)}
    (T : FiniteExponentialTower base₁ ell) (hbase : base₁ ≤ base₂) :
    FiniteExponentialTower base₂ ell where
  exponent := T.exponent
  exponent_mem_level i :=
    exponentialLevels_mono_base hbase T.exponent i.val (T.exponent_mem i)

@[simp]
theorem FiniteExponentialTower.changeBase_exponent
    {ell : ℕ} {base₁ base₂ : Subalgebra ℝ (X → ℝ)}
    (T : FiniteExponentialTower base₁ ell) (hbase : base₁ ≤ base₂)
    (i : Fin ell) :
    (T.changeBase hbase).exponent i = T.exponent i :=
  rfl

/-- Pull back a tower and then place it over any base containing the
pullback of the original base. -/
def FiniteExponentialTower.pullbackChangeBase
    {ell : ℕ} {base : Subalgebra ℝ (X → ℝ)}
    (T : FiniteExponentialTower base ell) (phi : Y → X)
    (base' : Subalgebra ℝ (Y → ℝ))
    (hbase : base.map (functionPrecompAlgHom phi) ≤ base') :
    FiniteExponentialTower base' ell :=
  (T.pullback phi).changeBase hbase

@[simp]
theorem FiniteExponentialTower.pullbackChangeBase_generator_apply
    {ell : ℕ} {base : Subalgebra ℝ (X → ℝ)}
    (T : FiniteExponentialTower base ell) (phi : Y → X)
    (base' : Subalgebra ℝ (Y → ℝ))
    (hbase : base.map (functionPrecompAlgHom phi) ≤ base')
    (i : Fin ell) (y : Y) :
    (T.pullbackChangeBase phi base' hbase).generator i y =
      T.generator i (phi y) :=
  rfl

/-- Every function from an old level, pulled back along the source map,
belongs to the corresponding level after pullback and base enlargement. -/
theorem FiniteExponentialTower.precomp_mem_pullbackChangeBase_level
    {ell : ℕ} {base : Subalgebra ℝ (X → ℝ)}
    (T : FiniteExponentialTower base ell) (phi : Y → X)
    (base' : Subalgebra ℝ (Y → ℝ))
    (hbase : base.map (functionPrecompAlgHom phi) ≤ base')
    {j : ℕ} {f : X → ℝ} (hf : f ∈ T.level j) :
    functionPrecompAlgHom phi f ∈
      (T.pullbackChangeBase phi base' hbase).level j := by
  have hmap : functionPrecompAlgHom phi f ∈
      (T.level j).map (functionPrecompAlgHom phi) := by
    rw [Subalgebra.mem_map]
    exact ⟨f, hf, rfl⟩
  rw [T.pullback_level phi j] at hmap
  exact exponentialLevels_mono_base hbase (T.pullback phi).exponent j hmap

end AbelFormalization
