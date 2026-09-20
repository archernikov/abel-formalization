import AbelFormalization.FiniteWeightQuotient

set_option autoImplicit false

/-!
# The subtype of a homogeneous finite-product submodule

A coordinatewise homogeneous submodule of a finite product is not only equal
to the product of its coordinate submodules as a submodule.  Its subtype is
linearly equivalent to the dependent product of the coordinate subtypes.  The
equivalence below is the literal coordinate map in both directions.
-/

noncomputable section

namespace AbelFormalization

section HomogeneousSubtype

variable {R : Type*} [CommRing R] {n : ℕ}
variable {M : Fin n → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The subtype of a coordinatewise homogeneous submodule is the product of
the subtypes of its coordinate submodules.  Both maps preserve the underlying
coordinates definitionally. -/
def finiteWeightHomogeneousSubtypeEquiv
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K) :
    K ≃ₗ[R] (∀ i, finiteWeightCoordinateSubmodule K i) where
  toFun := fun x i =>
    ⟨x.1 i, (mem_finiteWeightCoordinateSubmodule_iff K i (x.1 i)).2
      (hK x.1 x.2 i)⟩
  invFun := fun y =>
    ⟨fun i => (y i : M i),
      (finiteWeightHomogeneous_eq_pi_coordinateSubmodule K hK).ge
        ((Submodule.mem_pi).2 fun i _ => (y i).2)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    rfl
  right_inv := by
    intro y
    funext i
    apply Subtype.ext
    rfl
  map_add' := by
    intro x y
    funext i
    apply Subtype.ext
    rfl
  map_smul' := by
    intro c x
    funext i
    apply Subtype.ext
    rfl

/-- The forward equivalence is literal coordinate evaluation after forgetting
the coordinate-submodule subtype. -/
@[simp]
theorem finiteWeightHomogeneousSubtypeEquiv_apply
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (x : K) (i : Fin n) :
    ((finiteWeightHomogeneousSubtypeEquiv K hK x) i : M i) = x.1 i := rfl

/-- The inverse equivalence is literal assembly of the underlying coordinate
values. -/
@[simp]
theorem finiteWeightHomogeneousSubtypeEquiv_symm_apply
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (y : ∀ i, finiteWeightCoordinateSubmodule K i) (i : Fin n) :
    ((finiteWeightHomogeneousSubtypeEquiv K hK).symm y).1 i = (y i : M i) := rfl

/-- The ambient vector underlying the inverse equivalence is the function of
the underlying coordinate values. -/
@[simp]
theorem finiteWeightHomogeneousSubtypeEquiv_symm_apply_val
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (y : ∀ i, finiteWeightCoordinateSubmodule K i) :
    ((finiteWeightHomogeneousSubtypeEquiv K hK).symm y).1 =
      fun i => (y i : M i) := rfl

/-- A single coordinate in the product corresponds to the same single
coordinate in the ambient homogeneous submodule. -/
@[simp]
theorem finiteWeightHomogeneousSubtypeEquiv_symm_single_val
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (i : Fin n) (v : finiteWeightCoordinateSubmodule K i) :
    ((finiteWeightHomogeneousSubtypeEquiv K hK).symm (Pi.single i v)).1 =
      Pi.single i (v : M i) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

end HomogeneousSubtype

end AbelFormalization
