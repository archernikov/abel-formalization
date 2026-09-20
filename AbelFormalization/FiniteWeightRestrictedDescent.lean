import AbelFormalization.FiniteWeightRestrictedQuotient
import AbelFormalization.FiniteWeightSemilinearIteration

set_option autoImplicit false

/-!
# Descent through a principal coefficient quotient

This file specializes semilinear iteration transport to the coordinate
quotient of an invariant homogeneous submodule.  It records both equality of
the quotient iterations and the lifting of eventual quotient invariance.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [CommRing R] {n : ℕ}
variable {M : Fin n → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The coordinate restriction and its principal coordinate quotient
intertwine in the orientation used by semilinear iteration transport. -/
theorem finiteWeightRestrictedPiQuotientMap_intertwines'
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hJK : K.map J.toLinearMap = K) (b : R)
    (x : ∀ i, finiteWeightCoordinateSubmodule K i) :
    finiteWeightRestrictedPiQuotientMap K b
        (finiteWeightInvariantCoordinateEquiv J K hK hJK x) =
      finiteWeightRestrictedEquivOfInvariant J K hK hJK b
        (finiteWeightRestrictedPiQuotientMap K b x) :=
  (finiteWeightRestrictedPiQuotientMap_intertwines
    J K hK hJK b x).symm

/-- Every descent iterate commutes with the principal coordinate quotient,
provided its kernel `(b)` is contained in the initial submodule. -/
theorem map_finiteWeightInvariantCoordinate_descentIterate_eq
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hJK : K.map J.toLinearMap = K) (b : R)
    (U : Submodule R (∀ i, finiteWeightCoordinateSubmodule K i))
    (hkernel : Ideal.span {b} •
      (⊤ : Submodule R (∀ i, finiteWeightCoordinateSubmodule K i)) ≤ U)
    (j : ℕ) :
    (finiteWeightDescentIterate
        (finiteWeightInvariantCoordinateEquiv J K hK hJK) U j).map
          (finiteWeightRestrictedPiQuotientMap K b) =
      finiteWeightDescentIterate
        (finiteWeightRestrictedEquivOfInvariant J K hK hJK b)
        (U.map (finiteWeightRestrictedPiQuotientMap K b)) j := by
  have h := map_finiteWeightDescentIterate_eq
    (σ := Ideal.Quotient.mk (Ideal.span {b}))
    (finiteWeightRestrictedCoordinateQuotientMap K b)
    (finiteWeightInvariantCoordinateEquiv J K hK hJK)
    (finiteWeightRestrictedEquivOfInvariant J K hK hJK b)
    (finiteWeightRestrictedPiQuotientMap_intertwines'
      J K hK hJK b) U
    (by
      change LinearMap.ker (finiteWeightRestrictedPiQuotientMap K b) ≤ U
      rw [ker_finiteWeightRestrictedPiQuotientMap]
      exact hkernel) j
  change
    (finiteWeightDescentIterate
        (finiteWeightInvariantCoordinateEquiv J K hK hJK) U j).map
          (finiteWeightRestrictedPiQuotientMap K b) =
      finiteWeightDescentIterate
        (finiteWeightRestrictedEquivOfInvariant J K hK hJK b)
        (U.map (finiteWeightRestrictedPiQuotientMap K b)) j at h
  exact h

/-- If the quotient iteration is invariant, then the corresponding iterate
in the coordinate product of `K` is invariant as well. -/
theorem finiteWeightInvariantCoordinate_iterate_invariant_of_quotient
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hJK : K.map J.toLinearMap = K) (b : R)
    (U : Submodule R (∀ i, finiteWeightCoordinateSubmodule K i))
    (hkernel : Ideal.span {b} •
      (⊤ : Submodule R (∀ i, finiteWeightCoordinateSubmodule K i)) ≤ U)
    (j : ℕ)
    (hinv : (finiteWeightDescentIterate
        (finiteWeightRestrictedEquivOfInvariant J K hK hJK b)
        (U.map (finiteWeightRestrictedPiQuotientMap K b)) j).map
          (finiteWeightRestrictedEquivOfInvariant J K hK hJK b).toLinearMap =
      finiteWeightDescentIterate
        (finiteWeightRestrictedEquivOfInvariant J K hK hJK b)
        (U.map (finiteWeightRestrictedPiQuotientMap K b)) j) :
    (finiteWeightDescentIterate
        (finiteWeightInvariantCoordinateEquiv J K hK hJK) U j).map
          (finiteWeightInvariantCoordinateEquiv J K hK hJK).toLinearMap =
      finiteWeightDescentIterate
        (finiteWeightInvariantCoordinateEquiv J K hK hJK) U j := by
  let A := finiteWeightInvariantCoordinateEquiv J K hK hJK
  let Abar := finiteWeightRestrictedEquivOfInvariant J K hK hJK b
  let qf := finiteWeightRestrictedCoordinateQuotientMap K b
  let V := finiteWeightDescentIterate A U j
  have hcomm : ∀ x, finiteWeightPiMap qf (A x) =
      Abar (finiteWeightPiMap qf x) := by
    intro x
    exact finiteWeightRestrictedPiQuotientMap_intertwines'
      J K hK hJK b x
  have hker0 : LinearMap.ker (finiteWeightPiMap qf) ≤ U := by
    change LinearMap.ker (finiteWeightRestrictedPiQuotientMap K b) ≤ U
    rw [ker_finiteWeightRestrictedPiQuotientMap]
    exact hkernel
  apply invariant_of_map_finiteWeightPiMap_invariant qf A Abar hcomm V
  · exact ker_finiteWeightPiMap_le_descentIterate
      qf A Abar hcomm U hker0 j
  · have hmap := map_finiteWeightInvariantCoordinate_descentIterate_eq
      J K hK hJK b U hkernel j
    change V.map (finiteWeightPiMap qf) =
      finiteWeightDescentIterate Abar
        (U.map (finiteWeightPiMap qf)) j at hmap
    rw [hmap]
    exact hinv

end AbelFormalization
