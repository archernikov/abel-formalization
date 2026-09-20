import AbelFormalization.FiniteWeightHomogeneousSubtype
import AbelFormalization.FiniteWeightSemilinearIteration

set_option autoImplicit false

/-!
# Coordinates inside an invariant homogeneous submodule

A homogeneous finite-product submodule is itself a finite product of its
coordinate submodules.  This file restricts an invariant equivalence to that
product and shows that finite-weight descent there is the same descent as in
the ambient product.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [CommRing R] {n : ℕ}
variable {M : Fin n → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Inclusion of one coordinate submodule into its ambient coordinate. -/
def finiteWeightCoordinateInclusion (K : Submodule R (∀ i, M i)) (i : Fin n) :
    finiteWeightCoordinateSubmodule K i →ₗ[R] M i :=
  (finiteWeightCoordinateSubmodule K i).subtype

/-- Coordinatewise inclusion from the product belonging to `K` into the
ambient finite product. -/
def finiteWeightCoordinateInclusionMap (K : Submodule R (∀ i, M i)) :
    (∀ i, finiteWeightCoordinateSubmodule K i) →ₗ[R] (∀ i, M i) :=
  finiteWeightPiMap (σ := RingHom.id R)
    (finiteWeightCoordinateInclusion K)

@[simp]
theorem finiteWeightCoordinateInclusionMap_apply
    (K : Submodule R (∀ i, M i))
    (x : ∀ i, finiteWeightCoordinateSubmodule K i) (i : Fin n) :
    finiteWeightCoordinateInclusionMap K x i = (x i : M i) := rfl

theorem finiteWeightCoordinateInclusionMap_injective
    (K : Submodule R (∀ i, M i)) :
    Function.Injective (finiteWeightCoordinateInclusionMap K) := by
  intro x y hxy
  funext i
  apply Subtype.ext
  exact congrFun hxy i

@[simp]
theorem ker_finiteWeightCoordinateInclusionMap
    (K : Submodule R (∀ i, M i)) :
    LinearMap.ker (finiteWeightCoordinateInclusionMap K) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (finiteWeightCoordinateInclusionMap_injective K)

@[simp]
theorem finiteWeightCoordinateInclusionMap_single
    (K : Submodule R (∀ i, M i)) (i : Fin n)
    (v : finiteWeightCoordinateSubmodule K i) :
    finiteWeightCoordinateInclusionMap K (Pi.single i v) =
      Pi.single i (v : M i) := by
  exact finiteWeightPiMap_single
    (σ := RingHom.id R) (finiteWeightCoordinateInclusion K) i v

theorem finiteWeightCoordinateInclusionMap_prefix
    (K : Submodule R (∀ i, M i)) (k : ℕ)
    (x : ∀ i, finiteWeightCoordinateSubmodule K i) :
    finiteWeightCoordinateInclusionMap K
        (finiteWeightPrefixProjection R
          (fun i ↦ finiteWeightCoordinateSubmodule K i) k x) =
      finiteWeightPrefixProjection R M k
        (finiteWeightCoordinateInclusionMap K x) := by
  exact finiteWeightPiMap_prefixProjection
    (σ := RingHom.id R) (finiteWeightCoordinateInclusion K) k x

/-- For a homogeneous `K`, the range of coordinatewise inclusion is exactly
`K`. -/
theorem range_finiteWeightCoordinateInclusionMap
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K) :
    LinearMap.range (finiteWeightCoordinateInclusionMap K) = K := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    apply (finiteWeightHomogeneous_eq_pi_coordinateSubmodule K hK).ge
    exact (Submodule.mem_pi).mpr fun i _ ↦ (y i).property
  · intro hx
    have hxpi :=
      (finiteWeightHomogeneous_eq_pi_coordinateSubmodule K hK).le hx
    refine ⟨fun i ↦ ⟨x i, (Submodule.mem_pi.mp hxpi i (Set.mem_univ i))⟩, ?_⟩
    rfl

/-- Restrict `J` to an invariant homogeneous submodule and express the
restriction in the product of coordinate submodules. -/
def finiteWeightInvariantCoordinateEquiv
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hJK : K.map J.toLinearMap = K) :
    (∀ i, finiteWeightCoordinateSubmodule K i) ≃ₗ[R]
      (∀ i, finiteWeightCoordinateSubmodule K i) :=
  (finiteWeightHomogeneousSubtypeEquiv K hK).symm |>.trans
    (J.ofSubmodules K K hJK) |>.trans
      (finiteWeightHomogeneousSubtypeEquiv K hK)

/-- The restricted coordinate equivalence intertwines with ambient
coordinatewise inclusion. -/
theorem finiteWeightCoordinateInclusionMap_intertwines
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hJK : K.map J.toLinearMap = K)
    (x : ∀ i, finiteWeightCoordinateSubmodule K i) :
    finiteWeightCoordinateInclusionMap K
        (finiteWeightInvariantCoordinateEquiv J K hK hJK x) =
      J (finiteWeightCoordinateInclusionMap K x) := by
  rfl

/-- Lower triangularity passes to the coordinate product of an invariant
homogeneous submodule. -/
theorem finiteWeightInvariantCoordinateEquiv_triangular
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i),
      J (Pi.single i v) = Pi.single i v +
        finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hJK : K.map J.toLinearMap = K) :
    ∀ i (v : finiteWeightCoordinateSubmodule K i),
      finiteWeightInvariantCoordinateEquiv J K hK hJK (Pi.single i v) =
        Pi.single i v +
          finiteWeightPrefixProjection R
            (fun i ↦ finiteWeightCoordinateSubmodule K i) i.val
            (finiteWeightInvariantCoordinateEquiv J K hK hJK
              (Pi.single i v)) := by
  classical
  intro i v
  apply finiteWeightCoordinateInclusionMap_injective K
  rw [map_add, finiteWeightCoordinateInclusionMap_intertwines,
    finiteWeightCoordinateInclusionMap_single,
    finiteWeightCoordinateInclusionMap_prefix,
    finiteWeightCoordinateInclusionMap_intertwines,
    finiteWeightCoordinateInclusionMap_single]
  exact htri i (v : M i)

/-- The submodule of coordinate vectors whose assembled ambient vector lies
in `U`. -/
def finiteWeightCoordinatePullback
    (K U : Submodule R (∀ i, M i)) :
    Submodule R (∀ i, finiteWeightCoordinateSubmodule K i) :=
  U.comap (finiteWeightCoordinateInclusionMap K)

/-- If `U ≤ K`, assembling its coordinate pullback recovers `U`. -/
theorem map_finiteWeightCoordinatePullback_eq
    (K U : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hUK : U ≤ K) :
    (finiteWeightCoordinatePullback K U).map
        (finiteWeightCoordinateInclusionMap K) = U := by
  apply le_antisymm
  · exact Submodule.map_le_iff_le_comap.mpr le_rfl
  · intro x hx
    let y := finiteWeightHomogeneousSubtypeEquiv K hK ⟨x, hUK hx⟩
    refine ⟨y, ?_, ?_⟩
    · exact hx
    · rfl

/-- Ambient homogeneity passes to the coordinate pullback. -/
theorem finiteWeightCoordinatePullback_homogeneous
    (K U : Submodule R (∀ i, M i))
    (hU : ∀ x ∈ U, ∀ i, Pi.single i (x i) ∈ U) :
    ∀ x ∈ finiteWeightCoordinatePullback K U, ∀ i,
      Pi.single i (x i) ∈ finiteWeightCoordinatePullback K U := by
  classical
  intro x hx i
  change finiteWeightCoordinateInclusionMap K (Pi.single i (x i)) ∈ U
  rw [finiteWeightCoordinateInclusionMap_single]
  exact hU _ hx i

/-- Descent inside the coordinate product of `K`, followed by inclusion,
equals ambient descent from every submodule `U ≤ K`. -/
theorem map_finiteWeightCoordinate_descentIterate_eq
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hJK : K.map J.toLinearMap = K)
    (U : Submodule R (∀ i, M i)) (hUK : U ≤ K) (j : ℕ) :
    (finiteWeightDescentIterate
        (finiteWeightInvariantCoordinateEquiv J K hK hJK)
        (finiteWeightCoordinatePullback K U) j).map
          (finiteWeightCoordinateInclusionMap K) =
      finiteWeightDescentIterate J U j := by
  have htransport := map_finiteWeightDescentIterate_eq
    (σ := RingHom.id R)
    (finiteWeightCoordinateInclusion K)
    (finiteWeightInvariantCoordinateEquiv J K hK hJK) J
    (finiteWeightCoordinateInclusionMap_intertwines J K hK hJK)
    (finiteWeightCoordinatePullback K U)
    (by
      change LinearMap.ker (finiteWeightCoordinateInclusionMap K) ≤
        finiteWeightCoordinatePullback K U
      rw [ker_finiteWeightCoordinateInclusionMap]
      exact bot_le) j
  change
    (finiteWeightDescentIterate
        (finiteWeightInvariantCoordinateEquiv J K hK hJK)
        (finiteWeightCoordinatePullback K U) j).map
          (finiteWeightCoordinateInclusionMap K) =
      finiteWeightDescentIterate J
        ((finiteWeightCoordinatePullback K U).map
          (finiteWeightCoordinateInclusionMap K)) j at htransport
  rw [map_finiteWeightCoordinatePullback_eq K U hK hUK] at htransport
  exact htransport

end AbelFormalization
