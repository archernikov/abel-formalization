import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Submodule.Map

set_option autoImplicit false

/-!
# Prefix lengths detect invariance under a finite triangular map

The coordinates are actual finite product coordinates, with arbitrary
modules at the individual ordered weights. Prefix lengths detect
invariance of homogeneous submodules under a triangular linear equivalence.
-/

noncomputable section

namespace AbelFormalization

section Length

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- An inclusion of submodules in a finite-length module is equality if
their lengths agree. -/
theorem submodule_eq_of_le_of_length_eq
    [IsArtinian R V] [IsNoetherian R V] {A B : Submodule R V}
    (hAB : A ≤ B) (hlen : Module.length R A = Module.length R B) : A = B := by
  by_contra hne
  have hlt : A < B := (lt_iff_le_and_ne).mpr ⟨hAB, hne⟩
  have hstrict := Submodule.height_strictMono hlt
  rw [← Module.length_submodule, ← Module.length_submodule] at hstrict
  exact (ne_of_lt hstrict) hlen

theorem length_map_linearEquiv (J : V ≃ₗ[R] V) (N : Submodule R V) :
    Module.length R (N.map J.toLinearMap) = Module.length R N :=
  (Submodule.equivMapOfInjective J.toLinearMap J.injective N).length_eq.symm

end Length

section Prefixes

variable (R : Type*) [Ring R] {n : ℕ}
variable (M : Fin n → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Projection onto the coordinates with index strictly less than `k`. -/
def finiteWeightPrefixProjection (k : ℕ) : (∀ i, M i) →ₗ[R] (∀ i, M i) where
  toFun x i := if i.val < k then x i else 0
  map_add' x y := by
    ext i
    by_cases hi : i.val < k <;> simp [hi]
  map_smul' c x := by
    ext i
    by_cases hi : i.val < k <;> simp [hi]

/-- The actual low-weight coordinate submodule. -/
def finiteWeightPrefix (k : ℕ) : Submodule R (∀ i, M i) :=
  (finiteWeightPrefixProjection R M k).range

variable {R M}

@[simp]
theorem finiteWeightPrefixProjection_apply (k : ℕ) (x : ∀ i, M i) (i : Fin n) :
    finiteWeightPrefixProjection R M k x i = if i.val < k then x i else 0 := rfl

theorem finiteWeightPrefixProjection_comp_of_le {k l : ℕ} (hlk : l ≤ k)
    (x : ∀ i, M i) :
    finiteWeightPrefixProjection R M k (finiteWeightPrefixProjection R M l x) =
      finiteWeightPrefixProjection R M l x := by
  ext i
  by_cases hi : i.val < l
  · simp [finiteWeightPrefixProjection_apply, hi, lt_of_lt_of_le hi hlk]
  · simp [finiteWeightPrefixProjection_apply, hi]

@[simp]
theorem finiteWeightPrefixProjection_idempotent (k : ℕ) (x : ∀ i, M i) :
    finiteWeightPrefixProjection R M k (finiteWeightPrefixProjection R M k x) =
      finiteWeightPrefixProjection R M k x :=
  finiteWeightPrefixProjection_comp_of_le le_rfl x

theorem finiteWeightPrefixProjection_eq_self_iff (k : ℕ) (x : ∀ i, M i) :
    finiteWeightPrefixProjection R M k x = x ↔ ∀ i, k ≤ i.val → x i = 0 := by
  constructor
  · intro h i hi
    have hcoord := congrFun h i
    simpa [finiteWeightPrefixProjection_apply, not_lt.mpr hi] using hcoord.symm
  · intro h
    ext i
    by_cases hi : i.val < k
    · simp [finiteWeightPrefixProjection_apply, hi]
    · simp [finiteWeightPrefixProjection_apply, hi, h i (le_of_not_gt hi)]

theorem mem_finiteWeightPrefix_iff (k : ℕ) (x : ∀ i, M i) :
    x ∈ finiteWeightPrefix R M k ↔ finiteWeightPrefixProjection R M k x = x := by
  constructor
  · rintro ⟨v, rfl⟩
    exact finiteWeightPrefixProjection_idempotent k v
  · intro hx
    exact ⟨x, hx⟩

theorem finiteWeightPrefixProjection_single (k : ℕ) (i : Fin n) (v : M i) :
    finiteWeightPrefixProjection R M k (Pi.single i v) =
      if i.val < k then Pi.single i v else 0 := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    by_cases hi : i.val < k <;> simp [finiteWeightPrefixProjection_apply, hi]
  · by_cases hi : i.val < k <;>
      simp [finiteWeightPrefixProjection_apply, hji, hi]

/-- For a coordinatewise homogeneous submodule, its prefix image is
exactly its intersection with the corresponding coordinate submodule. -/
theorem map_finiteWeightPrefixProjection_eq_inf
    (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N) (k : ℕ) :
    N.map (finiteWeightPrefixProjection R M k) = N ⊓ finiteWeightPrefix R M k := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ⟨x, rfl⟩⟩
    rw [← LinearMap.sum_single_apply M (finiteWeightPrefixProjection R M k x)]
    apply N.sum_mem
    intro i hi
    by_cases hik : i.val < k
    · simpa [finiteWeightPrefixProjection_apply, hik] using hN x hx i
    · simp [finiteWeightPrefixProjection_apply, hik]
  · intro x hx
    exact ⟨x, hx.1, (mem_finiteWeightPrefix_iff k x).mp hx.2⟩

/-- A unipotent triangular map preserves every low-weight prefix.
Its structural hypothesis is the literal coordinate form of `J-id`
strictly lowering the weight of a homogeneous vector. -/
theorem triangular_map_preserves_finiteWeightPrefix
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (k : ℕ) {x : ∀ i, M i} (hx : x ∈ finiteWeightPrefix R M k) :
    J x ∈ finiteWeightPrefix R M k := by
  classical
  have hxzero := (finiteWeightPrefixProjection_eq_self_iff k x).mp
    ((mem_finiteWeightPrefix_iff k x).mp hx)
  apply (mem_finiteWeightPrefix_iff k (J x)).mpr
  conv_rhs => rw [← LinearMap.sum_single_apply M x, map_sum]
  conv_lhs => rw [← LinearMap.sum_single_apply M x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hik : i.val < k
  · calc
      finiteWeightPrefixProjection R M k (J (Pi.single i (x i))) =
          finiteWeightPrefixProjection R M k
            (Pi.single i (x i) +
              finiteWeightPrefixProjection R M i.val (J (Pi.single i (x i)))) :=
        congrArg (finiteWeightPrefixProjection R M k) (htri i (x i))
      _ = Pi.single i (x i) +
          finiteWeightPrefixProjection R M i.val (J (Pi.single i (x i))) := by
        rw [map_add, finiteWeightPrefixProjection_single, ite_eq_left hik,
          finiteWeightPrefixProjection_comp_of_le (Nat.le_of_lt hik)]
      _ = J (Pi.single i (x i)) := (htri i (x i)).symm
  · simp [hxzero i (le_of_not_gt hik)]

/-- Triangularity gives an actual inclusion, before any comparison of
lengths: the image of the old prefix lies in the prefix image of `J N`. -/
theorem map_inf_prefix_le_prefix_map
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N : Submodule R (∀ i, M i)) (k : ℕ) :
    (N ⊓ finiteWeightPrefix R M k).map J.toLinearMap ≤
      (N.map J.toLinearMap).map (finiteWeightPrefixProjection R M k) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨J x, ⟨x, hx.1, rfl⟩, ?_⟩
  exact (mem_finiteWeightPrefix_iff k (J x)).mp
    (triangular_map_preserves_finiteWeightPrefix J htri k hx.2)

/-- For homogeneous `N`, every prefix-image length weakly increases
under an actual unipotent lower-triangular linear equivalence. -/
theorem finiteWeightPrefix_length_le_map
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N) (k : ℕ) :
    Module.length R (N.map (finiteWeightPrefixProjection R M k)) ≤
      Module.length R ((N.map J.toLinearMap).map (finiteWeightPrefixProjection R M k)) := by
  rw [map_finiteWeightPrefixProjection_eq_inf N hN k,
    ← length_map_linearEquiv J (N ⊓ finiteWeightPrefix R M k)]
  rw [Module.length_submodule, Module.length_submodule]
  exact Order.height_mono (map_inf_prefix_le_prefix_map J htri N k)

variable [IsArtinian R (∀ i, M i)] [IsNoetherian R (∀ i, M i)]

/-- Equality of all prefix-image lengths detects actual `J`-invariance.
This proves the decisive finite-length implication without exterior powers
and without assuming an identity about initial submodules. -/
theorem triangular_invariant_of_finiteWeightPrefix_lengths_eq
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N)
    (hlen : ∀ k : ℕ,
      Module.length R ((N.map J.toLinearMap).map (finiteWeightPrefixProjection R M k)) =
        Module.length R (N.map (finiteWeightPrefixProjection R M k))) :
    N.map J.toLinearMap = N := by
  classical
  have hprefix (k : ℕ) : (N ⊓ finiteWeightPrefix R M k).map J.toLinearMap =
      (N.map J.toLinearMap).map (finiteWeightPrefixProjection R M k) := by
    apply submodule_eq_of_le_of_length_eq (map_inf_prefix_le_prefix_map J htri N k)
    rw [length_map_linearEquiv, hlen k, map_finiteWeightPrefixProjection_eq_inf N hN k]
  have hle : N ≤ N.map J.toLinearMap := by
    intro x hx
    rw [← LinearMap.sum_single_apply M x]
    apply (N.map J.toLinearMap).sum_mem
    intro i hi
    let v : ∀ i, M i := Pi.single i (x i)
    have hv : v ∈ N := hN x hx i
    have hp : finiteWeightPrefixProjection R M i.val (J v) ∈
        (N.map J.toLinearMap).map (finiteWeightPrefixProjection R M i.val) :=
      ⟨J v, ⟨v, hv, rfl⟩, rfl⟩
    rw [← hprefix i.val] at hp
    obtain ⟨w, hw, hJw⟩ := hp
    have hJw' : J w = finiteWeightPrefixProjection R M i.val (J v) := hJw
    refine ⟨v - w, N.sub_mem hv hw.1, ?_⟩
    change J (v - w) = v
    rw [map_sub, hJw']
    exact sub_eq_iff_eq_add.mpr (htri i (x i))
  exact (submodule_eq_of_le_of_length_eq hle (length_map_linearEquiv J N).symm).symm

end Prefixes

end AbelFormalization
