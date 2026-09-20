import AbelFormalization.FiniteWeightInvariantCoordinates
import Mathlib.Algebra.Module.Submodule.Pointwise

set_option autoImplicit false

/-!
# Scalar multiples of finite-weight invariant submodules

Pointwise multiplication of a submodule by a scalar is the image under the
corresponding scalar endomorphism.  It preserves coordinatewise homogeneity
and commutes with every linear map.  Consequently, scalar multiples of an
invariant homogeneous finite-weight submodule remain invariant and
homogeneous.

Inside the coordinate product attached to a homogeneous submodule `K`, the
pullback of `b • K` is exactly `b • ⊤`.
-/

noncomputable section

namespace AbelFormalization

open scoped Pointwise

section General

variable {R X Y : Type*}
variable [CommRing R]
variable [AddCommGroup X] [Module R X]
variable [AddCommGroup Y] [Module R Y]

/-- Membership in a pointwise scalar multiple, with the witness equation in
the direction used by submodule-map proofs. -/
theorem mem_pointwise_smul_submodule_iff
    (b : R) (K : Submodule R X) (x : X) :
    x ∈ b • K ↔ ∃ y ∈ K, b • y = x :=
  Submodule.mem_smul_pointwise_iff_exists x b K

/-- A linear map commutes with pointwise scalar multiplication of
submodules. -/
theorem map_pointwise_smul_submodule
    (f : X →ₗ[R] Y) (b : R) (K : Submodule R X) :
    (b • K).map f = b • K.map f := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (mem_pointwise_smul_submodule_iff b K x).mp hx with
      ⟨z, hz, rfl⟩
    rw [map_smul]
    exact Submodule.smul_mem_pointwise_smul (f z) b (K.map f)
      (Submodule.mem_map_of_mem hz)
  · intro hy
    rcases (mem_pointwise_smul_submodule_iff b (K.map f) y).mp hy with
      ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    rw [← map_smul]
    exact Submodule.mem_map_of_mem
      (Submodule.smul_mem_pointwise_smul x b K hx)

end General

section FiniteWeight

variable {R : Type*} [CommRing R] {n : ℕ}
variable {M : Fin n → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Pointwise scalar multiplication preserves coordinatewise homogeneity. -/
theorem finiteWeight_pointwise_smul_homogeneous
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (b : R) :
    ∀ x ∈ b • K, ∀ i, Pi.single i (x i) ∈ b • K := by
  classical
  intro x hx i
  rcases (mem_pointwise_smul_submodule_iff b K x).mp hx with
    ⟨y, hy, rfl⟩
  rw [Pi.smul_apply, Pi.single_smul]
  exact Submodule.smul_mem_pointwise_smul (Pi.single i (y i)) b K
    (hK y hy i)

/-- Pointwise scalar multiplication preserves invariance under a linear
equivalence. -/
theorem finiteWeight_pointwise_smul_invariant
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (K : Submodule R (∀ i, M i))
    (hJK : K.map J.toLinearMap = K)
    (b : R) :
    (b • K).map J.toLinearMap = b • K := by
  rw [map_pointwise_smul_submodule, hJK]

/-- Multiplication by a unit does not change a submodule. -/
theorem finiteWeight_pointwise_smul_eq_self_of_isUnit
    (K : Submodule R (∀ i, M i))
    {b : R} (hb : IsUnit b) :
    b • K = K :=
  Submodule.smul_eq_self_of_isUnit hb

/-- Membership in a coordinate pullback is membership of the assembled
ambient vector. -/
@[simp]
theorem mem_finiteWeightCoordinatePullback_iff
    (K U : Submodule R (∀ i, M i))
    (x : ∀ i, finiteWeightCoordinateSubmodule K i) :
    x ∈ finiteWeightCoordinatePullback K U ↔
      finiteWeightCoordinateInclusionMap K x ∈ U :=
  Iff.rfl

/-- In the coordinate product belonging to a homogeneous `K`, the pullback
of the scalar multiple `b • K` is the scalar multiple of the whole coordinate
product. -/
theorem finiteWeightCoordinatePullback_pointwise_smul
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (b : R) :
    finiteWeightCoordinatePullback K (b • K) =
      b • (⊤ : Submodule R
        (∀ i, finiteWeightCoordinateSubmodule K i)) := by
  ext x
  constructor
  · intro hx
    have hx' : finiteWeightCoordinateInclusionMap K x ∈ b • K :=
      (mem_finiteWeightCoordinatePullback_iff K (b • K) x).mp hx
    rcases (mem_pointwise_smul_submodule_iff b K
      (finiteWeightCoordinateInclusionMap K x)).mp hx' with
      ⟨z, hz, hzx⟩
    have hzrange : z ∈ LinearMap.range
        (finiteWeightCoordinateInclusionMap K) := by
      rw [range_finiteWeightCoordinateInclusionMap K hK]
      exact hz
    rcases hzrange with ⟨y, hyz⟩
    apply (mem_pointwise_smul_submodule_iff b
      (⊤ : Submodule R
        (∀ i, finiteWeightCoordinateSubmodule K i)) x).mpr
    refine ⟨y, Submodule.mem_top, ?_⟩
    apply finiteWeightCoordinateInclusionMap_injective K
    rw [map_smul, hyz]
    exact hzx
  · intro hx
    rcases (mem_pointwise_smul_submodule_iff b
      (⊤ : Submodule R
        (∀ i, finiteWeightCoordinateSubmodule K i)) x).mp hx with
      ⟨y, _hy, hyx⟩
    apply (mem_finiteWeightCoordinatePullback_iff K (b • K) x).mpr
    rw [← hyx, map_smul]
    apply Submodule.smul_mem_pointwise_smul
    exact (range_finiteWeightCoordinateInclusionMap K hK).le ⟨y, rfl⟩

end FiniteWeight

end AbelFormalization
