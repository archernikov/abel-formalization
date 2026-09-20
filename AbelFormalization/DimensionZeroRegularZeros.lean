import AbelFormalization.RegularConstraintFiber

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A vector space with a basis indexed by `Fin 0` is a one-point space, so
every subset is finite. -/
theorem set_finite_of_basis_fin_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (basis : Module.Basis (Fin 0) ℝ E) (s : Set E) : s.Finite := by
  letI : Subsingleton E :=
    ⟨fun x y ↦ basis.repr.injective (Subsingleton.elim _ _)⟩
  exact Set.toFinite s

/-- The zero-dimensional branch of regular-zero finiteness. -/
theorem finite_regularZeroSet_of_basis_fin_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (basis : Module.Basis (Fin 0) ℝ E)
    (Omega : Set E) (F : Fin 0 → E → ℝ) :
    (regularZeroSet Omega (constraintMap F)).Finite :=
  set_finite_of_basis_fin_zero basis _

end AbelFormalization
