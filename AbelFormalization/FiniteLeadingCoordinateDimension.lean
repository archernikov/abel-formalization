import AbelFormalization.FiniteWeightInitialLength
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fin.Rev

set_option autoImplicit false

/-!
# Dimension from the actual least nonzero coordinates

The leading indices below arise from actual
vectors, with every earlier coordinate equal to zero. The full initial
submodule is identified with the subspace supported on those indices.
Its dimension follows from the proved initial-length identity, not from
an assumed echelon form or an assumed Hilbert-function identity.

Arbitrary enumeration of a finite coordinate set is allowed. Reversing
that enumeration interprets least coordinates as greatest terms.
-/

noncomputable section

namespace AbelFormalization

variable {K : Type*} [Field K] {n : ℕ}

/-- The actual vanishing condition for the scalar coordinate prefix. -/
theorem finiteWeightPrefixProjection_eq_zero_iff_scalar
    (x : Fin n → K) (k : ℕ) :
    finiteWeightPrefixProjection K (fun _ : Fin n => K) k x = 0 ↔
      ∀ i : Fin n, i.val < k → x i = 0 := by
  constructor
  · intro h i hi
    have he := congrFun h i
    simpa only [finiteWeightPrefixProjection_apply, ite_eq_left hi, Pi.zero_apply] using he
  · intro h
    ext i
    by_cases hi : i.val < k
    · simp only [finiteWeightPrefixProjection_apply, ite_eq_left hi, h i hi, Pi.zero_apply]
    · simp only [finiteWeightPrefixProjection_apply, ite_eq_right hi, Pi.zero_apply]

/-- The indices which occur as the least nonzero coordinate of a vector
of the actual subspace. -/
def finiteLeadingCoordinates (U : Submodule K (Fin n → K)) : Set (Fin n) :=
  {i | ∃ x ∈ U, x i ≠ 0 ∧ ∀ j : Fin n, j < i → x j = 0}

/-- Every nonzero finite vector has an actual least nonzero coordinate. -/
theorem exists_least_nonzero_coordinate {x : Fin n → K} (hx : x ≠ 0) :
    ∃ i : Fin n, x i ≠ 0 ∧ ∀ j : Fin n, j < i → x j = 0 := by
  classical
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx
    ext i
    exact not_not.mp (fun hi => h ⟨i, hi⟩)
  let s : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  refine ⟨s.min' hs, (Finset.mem_filter.mp (Finset.min'_mem s hs)).2, ?_⟩
  intro j hj
  by_contra hjne
  have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjne⟩
  exact (not_le_of_gt hj) (Finset.min'_le s j hjs)

/-- Membership of an actual initial piece is witnessed by an original
vector with vanishing lower coordinates and the prescribed i-th value. -/
theorem mem_finiteWeightInitialPiece_scalar
    (U : Submodule K (Fin n → K)) (i : Fin n) (v : K) :
    v ∈ finiteWeightInitialPiece U i ↔
      ∃ x ∈ U, x i = v ∧ ∀ j : Fin n, j < i → x j = 0 := by
  constructor
  · rintro ⟨x, hx, hxi⟩
    exact ⟨x, hx.1, hxi,
      (finiteWeightPrefixProjection_eq_zero_iff_scalar x i.val).mp hx.2⟩
  · rintro ⟨x, hx, hxi, hlow⟩
    exact ⟨x, ⟨hx,
      (finiteWeightPrefixProjection_eq_zero_iff_scalar x i.val).mpr hlow⟩, hxi⟩

/-- A nonzero initial piece over the field contains every scalar: scale
an actual nonzero coordinate witness to the prescribed scalar. -/
theorem finiteWeightInitialPiece_eq_top_of_leading
    (U : Submodule K (Fin n → K)) {i : Fin n}
    (hi : i ∈ finiteLeadingCoordinates U) :
    finiteWeightInitialPiece U i = ⊤ := by
  obtain ⟨x, hx, hxi, hlow⟩ := hi
  have hv : x i ∈ finiteWeightInitialPiece U i :=
    (mem_finiteWeightInitialPiece_scalar U i (x i)).mpr ⟨x, hx, rfl, hlow⟩
  have hone : (1 : K) ∈ finiteWeightInitialPiece U i := by
    simpa only [smul_eq_mul, inv_mul_cancel₀ hxi] using
      (finiteWeightInitialPiece U i).smul_mem (x i)⁻¹ hv
  apply top_unique
  intro v _
  simpa only [smul_eq_mul, mul_one] using
    (finiteWeightInitialPiece U i).smul_mem v hone

/-- Initial-piece membership is exactly the support condition on actual
leading coordinates. This also covers the zero scalar. -/
theorem mem_finiteWeightInitialPiece_iff_leading
    (U : Submodule K (Fin n → K)) (i : Fin n) (v : K) :
    v ∈ finiteWeightInitialPiece U i ↔ v ≠ 0 → i ∈ finiteLeadingCoordinates U := by
  constructor
  · intro hv hvne
    obtain ⟨x, hx, hxi, hlow⟩ := (mem_finiteWeightInitialPiece_scalar U i v).mp hv
    refine ⟨x, hx, ?_, hlow⟩
    rw [hxi]
    exact hvne
  · intro h
    by_cases hv : v = 0
    · simpa only [hv] using (finiteWeightInitialPiece U i).zero_mem
    · rw [finiteWeightInitialPiece_eq_top_of_leading U (h hv)]
      trivial

/-- The actual scalar subspace supported on a chosen coordinate set. -/
def finiteCoordinateSupportSubmodule (K : Type*) [Field K] {n : ℕ}
    (S : Set (Fin n)) : Submodule K (Fin n → K) where
  carrier := {x | ∀ i, i ∉ S → x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp only [Pi.add_apply, hx i hi, hy i hi, add_zero]
  smul_mem' := by
    intro c x hx i hi
    simp only [Pi.smul_apply, hx i hi, smul_zero]

/-- The full actual initial submodule is precisely the coordinate support
subspace indexed by actual least nonzero coordinates. -/
theorem finiteWeightInitial_eq_support_leading
    (U : Submodule K (Fin n → K)) :
    finiteWeightInitial U = finiteCoordinateSupportSubmodule K (finiteLeadingCoordinates U) := by
  ext x
  rw [mem_finiteWeightInitial_iff]
  change (∀ i, x i ∈ finiteWeightInitialPiece U i) ↔
    ∀ i, i ∉ finiteLeadingCoordinates U → x i = 0
  simp only [mem_finiteWeightInitialPiece_iff_leading]
  constructor
  · intro h i hi
    by_contra hxi
    exact hi (h i hxi)
  · intro h i hxi
    by_contra hi
    exact hxi (h i hi)

/-- Restriction to the permitted coordinates is a genuine linear
isomorphism, with inverse extension by zero. -/
def finiteCoordinateSupportEquiv (K : Type*) [Field K] {n : ℕ}
    (S : Set (Fin n)) : finiteCoordinateSupportSubmodule K S ≃ₗ[K] (S → K) := by
  classical
  exact
    { toFun := fun x i => (x : Fin n → K) i
      invFun := fun y => ⟨fun i => if h : i ∈ S then y ⟨i, h⟩ else 0, by
        intro i hi
        simp only [dite_eq_right hi]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · simp only [dite_eq_left hi]
        · simpa only [dite_eq_right hi] using (x.property i hi).symm
      right_inv := by
        intro y
        funext i
        simp only [dite_eq_left i.property]
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- The support subspace has one scalar degree of freedom per permitted
coordinate. -/
theorem finrank_finiteCoordinateSupportSubmodule (S : Set (Fin n)) :
    Module.finrank K (finiteCoordinateSupportSubmodule K S) = S.ncard := by
  classical
  calc
    Module.finrank K (finiteCoordinateSupportSubmodule K S) =
        Module.finrank K (S → K) := (finiteCoordinateSupportEquiv K S).finrank_eq
    _ = Fintype.card S := Module.finrank_pi K
    _ = S.ncard := Set.fintypeCard_eq_ncard S

/-- The proved exact-sequence length identity yields finrank preservation
for the actual finite-dimensional initial subspace. -/
theorem finiteWeightInitial_finrank (U : Submodule K (Fin n → K)) :
    Module.finrank K (finiteWeightInitial U) = Module.finrank K U := by
  have h := finiteWeightInitial_length U
  rw [Module.length_eq_finrank, Module.length_eq_finrank] at h
  exact_mod_cast h

/-- The dimension of an arbitrary finite-coordinate subspace is exactly
the number of coordinates that actually occur as least nonzero coordinates. -/
theorem finrank_eq_ncard_finiteLeadingCoordinates (U : Submodule K (Fin n → K)) :
    Module.finrank K U = (finiteLeadingCoordinates U).ncard := by
  rw [← finiteWeightInitial_finrank U, finiteWeightInitial_eq_support_leading]
  exact finrank_finiteCoordinateSupportSubmodule _

section Enumeration

variable {ι : Type*}

/-- An arbitrary enumeration equips a finite coordinate set with the order
used to select its actual leading coordinate. -/
def enumeratedLeadingCoordinates (e : Fin n ≃ ι)
    (U : Submodule K (ι → K)) : Set (Fin n) :=
  {i | ∃ x ∈ U, x (e i) ≠ 0 ∧ ∀ j : Fin n, j < i → x (e j) = 0}

/-- Reindexing only changes the names of coordinates; the leading
witnesses are still vectors of the original subspace. -/
theorem finiteLeadingCoordinates_map_enumeration (e : Fin n ≃ ι)
    (U : Submodule K (ι → K)) :
    finiteLeadingCoordinates (U.map (LinearEquiv.funCongrLeft K K e).toLinearMap) =
      enumeratedLeadingCoordinates e U := by
  ext i
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, hxi, hlow⟩
    exact ⟨x, hx, hxi, hlow⟩
  · rintro ⟨x, hx, hxi, hlow⟩
    exact ⟨LinearEquiv.funCongrLeft K K e x, ⟨x, hx, rfl⟩, hxi, hlow⟩

/-- Any chosen enumeration yields the same dimension count. In
particular it may list actual monomials in decreasing order. -/
theorem finrank_eq_ncard_enumeratedLeadingCoordinates (e : Fin n ≃ ι)
    (U : Submodule K (ι → K)) :
    Module.finrank K U = (enumeratedLeadingCoordinates e U).ncard := by
  rw [← finiteLeadingCoordinates_map_enumeration e U,
    ← finrank_eq_ncard_finiteLeadingCoordinates]
  exact (LinearEquiv.funCongrLeft K K e).finrank_map_eq U |>.symm

end Enumeration

/-- The actual greatest nonzero coordinates of vectors in the subspace. -/
def finiteGreatestCoordinates (U : Submodule K (Fin n → K)) : Set (Fin n) :=
  {i | ∃ x ∈ U, x i ≠ 0 ∧ ∀ j : Fin n, i < j → x j = 0}

/-- Reversing the actual finite order interchanges least and greatest
coordinate witnesses, including the empty coordinate set. -/
theorem enumeratedLeadingCoordinates_rev (U : Submodule K (Fin n → K)) :
    enumeratedLeadingCoordinates Fin.revPerm U = Fin.rev '' finiteGreatestCoordinates U := by
  ext i
  constructor
  · rintro ⟨x, hx, hxi, hlow⟩
    refine ⟨i.rev, ⟨x, hx, hxi, ?_⟩, Fin.rev_rev i⟩
    intro j hj
    have he := hlow j.rev (Fin.rev_lt_iff.mpr hj)
    simpa only [Fin.revPerm_apply, Fin.rev_rev] using he
  · rintro ⟨i, ⟨x, hx, hxi, hhigh⟩, rfl⟩
    refine ⟨x, hx, ?_, ?_⟩
    · simpa only [Fin.revPerm_apply, Fin.rev_rev] using hxi
    · intro j hj
      exact hhigh j.rev (Fin.lt_rev_iff.mp hj)

/-- The greatest-coordinate version needed for leading terms in a finite
homogeneous polynomial-module piece. -/
theorem finrank_eq_ncard_finiteGreatestCoordinates (U : Submodule K (Fin n → K)) :
    Module.finrank K U = (finiteGreatestCoordinates U).ncard := by
  rw [← Set.ncard_image_of_injective _ Fin.rev_injective,
    ← enumeratedLeadingCoordinates_rev]
  exact finrank_eq_ncard_enumeratedLeadingCoordinates Fin.revPerm U

end AbelFormalization
