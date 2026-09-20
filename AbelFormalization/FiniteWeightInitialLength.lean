import AbelFormalization.FiniteWeightLengthDescent

set_option autoImplicit false

/-!
# Exact sequences for finite-weight initial submodules

Each initial piece is the actual projection of
the submodule whose earlier coordinates vanish. The prefix-length equality
is derived from explicit exact sequences, rather than assumed.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [Ring R] {n : ℕ}
variable {M : Fin n → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem finiteWeightPrefixProjection_comp_eq_left_of_le {k l : ℕ} (hkl : k ≤ l)
    (x : ∀ i, M i) :
    finiteWeightPrefixProjection R M k (finiteWeightPrefixProjection R M l x) =
      finiteWeightPrefixProjection R M k x := by
  ext i
  by_cases hi : i.val < k
  · simp [finiteWeightPrefixProjection_apply, hi, lt_of_lt_of_le hi hkl]
  · simp [finiteWeightPrefixProjection_apply, hi]

theorem finiteWeightPrefixProjection_succ (i : Fin n) (x : ∀ j, M j) :
    finiteWeightPrefixProjection R M (i.val + 1) x =
      finiteWeightPrefixProjection R M i.val x + Pi.single i (x i) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [finiteWeightPrefixProjection_apply]
  · have hval : j.val ≠ i.val := fun h => hji (Fin.ext h)
    by_cases hj : j.val < i.val
    · simp [finiteWeightPrefixProjection_apply, hj, Nat.lt_succ_of_lt hj,
        hji]
    · have hjsucc : ¬j.val < i.val + 1 := by
        intro h
        exact hval (Nat.le_antisymm (Nat.lt_succ_iff.mp h) (Nat.le_of_not_gt hj))
      simp [finiteWeightPrefixProjection_apply, hj, hjsucc,
        hji]

@[simp]
theorem finiteWeightPrefixProjection_zero : finiteWeightPrefixProjection R M 0 = 0 := by
  ext x i
  simp [finiteWeightPrefixProjection_apply]

theorem finiteWeightPrefixProjection_eq_id_of_le {k : ℕ} (hnk : n ≤ k) :
    finiteWeightPrefixProjection R M k = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  simp [finiteWeightPrefixProjection_apply, lt_of_lt_of_le i.isLt hnk]

/-- The image of a submodule under an actual coordinate prefix projection. -/
def finiteWeightPrefixImage (U : Submodule R (∀ i, M i)) (k : ℕ) :
    Submodule R (∀ i, M i) := U.map (finiteWeightPrefixProjection R M k)

/-- The i-th least-weight piece of all elements of U whose lower
coordinates vanish. -/
def finiteWeightInitialPiece (U : Submodule R (∀ i, M i)) (i : Fin n) :
    Submodule R (M i) :=
  (U ⊓ (finiteWeightPrefixProjection R M i.val).ker).map (LinearMap.proj i)

theorem single_mem_finiteWeightPrefixImage_succ
    (U : Submodule R (∀ i, M i)) (i : Fin n) {v : M i}
    (hv : v ∈ finiteWeightInitialPiece U i) :
    Pi.single i v ∈ finiteWeightPrefixImage U (i.val + 1) := by
  obtain ⟨x, hx, hxi⟩ := hv
  refine ⟨x, hx.1, ?_⟩
  have hxzero : finiteWeightPrefixProjection R M i.val x = 0 := hx.2
  change finiteWeightPrefixProjection R M (i.val + 1) x = Pi.single i v
  rw [finiteWeightPrefixProjection_succ, hxzero, zero_add]
  exact congrArg (Pi.single i) hxi

theorem prefix_mem_finiteWeightPrefixImage
    (U : Submodule R (∀ i, M i)) (i : Fin n) {x : ∀ j, M j}
    (hx : x ∈ finiteWeightPrefixImage U (i.val + 1)) :
    finiteWeightPrefixProjection R M i.val x ∈ finiteWeightPrefixImage U i.val := by
  obtain ⟨v, hv, rfl⟩ := hx
  exact ⟨v, hv, (finiteWeightPrefixProjection_comp_eq_left_of_le
    (Nat.le_succ i.val) v).symm⟩

/-- The first map in the exact sequence for adjoining one coordinate. -/
def finiteWeightPieceToPrefix (U : Submodule R (∀ i, M i)) (i : Fin n) :
    finiteWeightInitialPiece U i →ₗ[R] finiteWeightPrefixImage U (i.val + 1) :=
  LinearMap.codRestrict _
    ((LinearMap.single R M i).domRestrict (finiteWeightInitialPiece U i))
    (fun v => single_mem_finiteWeightPrefixImage_succ U i v.property)

/-- The second map simply forgets the last coordinate of a prefix image. -/
def finiteWeightPrefixToPrefix (U : Submodule R (∀ i, M i)) (i : Fin n) :
    finiteWeightPrefixImage U (i.val + 1) →ₗ[R] finiteWeightPrefixImage U i.val :=
  LinearMap.codRestrict _
    ((finiteWeightPrefixProjection R M i.val).domRestrict
      (finiteWeightPrefixImage U (i.val + 1)))
    (fun x => prefix_mem_finiteWeightPrefixImage U i x.property)

@[simp]
theorem finiteWeightPieceToPrefix_coe (U : Submodule R (∀ i, M i))
    (i : Fin n) (v : finiteWeightInitialPiece U i) :
    ((finiteWeightPieceToPrefix U i v) : ∀ j, M j) = Pi.single i (v : M i) := rfl

@[simp]
theorem finiteWeightPrefixToPrefix_coe (U : Submodule R (∀ i, M i))
    (i : Fin n) (x : finiteWeightPrefixImage U (i.val + 1)) :
    ((finiteWeightPrefixToPrefix U i x) : ∀ j, M j) =
      finiteWeightPrefixProjection R M i.val (x : ∀ j, M j) := rfl

theorem finiteWeightPieceToPrefix_injective (U : Submodule R (∀ i, M i))
    (i : Fin n) : Function.Injective (finiteWeightPieceToPrefix U i) := by
  intro v w h
  apply Subtype.ext
  have hi := congrFun (congrArg Subtype.val h) i
  simpa using hi

theorem finiteWeightPrefixToPrefix_surjective (U : Submodule R (∀ i, M i))
    (i : Fin n) : Function.Surjective (finiteWeightPrefixToPrefix U i) := by
  intro x
  obtain ⟨v, hv, hvx⟩ := x.property
  refine ⟨⟨finiteWeightPrefixProjection R M (i.val + 1) v, ⟨v, hv, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  change finiteWeightPrefixProjection R M i.val
    (finiteWeightPrefixProjection R M (i.val + 1) v) = (x : ∀ j, M j)
  rw [finiteWeightPrefixProjection_comp_eq_left_of_le (Nat.le_succ i.val)]
  exact hvx

/-- The first image is exactly the kernel of forgetting the last
coordinate. Both maps are explicit maps of the actual prefix modules. -/
theorem finiteWeightPrefix_exact (U : Submodule R (∀ i, M i)) (i : Fin n) :
    Function.Exact (finiteWeightPieceToPrefix U i) (finiteWeightPrefixToPrefix U i) := by
  intro x
  constructor
  · intro hx
    have hxzero : finiteWeightPrefixProjection R M i.val (x : ∀ j, M j) = 0 :=
      congrArg Subtype.val hx
    obtain ⟨v, hv, hvx⟩ := x.property
    have hvzero : finiteWeightPrefixProjection R M i.val v = 0 := by
      calc
        finiteWeightPrefixProjection R M i.val v =
            finiteWeightPrefixProjection R M i.val
              (finiteWeightPrefixProjection R M (i.val + 1) v) :=
          (finiteWeightPrefixProjection_comp_eq_left_of_le (Nat.le_succ i.val) v).symm
        _ = finiteWeightPrefixProjection R M i.val (x : ∀ j, M j) :=
          congrArg (finiteWeightPrefixProjection R M i.val) hvx
        _ = 0 := hxzero
    let vi : finiteWeightInitialPiece U i := ⟨v i, ⟨v, ⟨hv, hvzero⟩, rfl⟩⟩
    refine ⟨vi, ?_⟩
    apply Subtype.ext
    change Pi.single i (v i) = (x : ∀ j, M j)
    rw [← hvx, finiteWeightPrefixProjection_succ, hvzero, zero_add]
  · rintro ⟨v, rfl⟩
    apply Subtype.ext
    change finiteWeightPrefixProjection R M i.val (Pi.single i (v : M i)) = 0
    simp [finiteWeightPrefixProjection_single]

/-- Length additivity for the actual prefix images, derived from the
explicit short exact sequence. No finite-length hypothesis is needed. -/
theorem finiteWeightPrefixImage_length_succ (U : Submodule R (∀ i, M i)) (i : Fin n) :
    Module.length R (finiteWeightPrefixImage U (i.val + 1)) =
      Module.length R (finiteWeightInitialPiece U i) +
        Module.length R (finiteWeightPrefixImage U i.val) :=
  Module.length_eq_add_of_exact (finiteWeightPieceToPrefix U i)
    (finiteWeightPrefixToPrefix U i) (finiteWeightPieceToPrefix_injective U i)
    (finiteWeightPrefixToPrefix_surjective U i) (finiteWeightPrefix_exact U i)

/-- The actual full initial submodule, collecting every possible
least-weight component, not the initial forms of a selected generating list. -/
def finiteWeightInitial (U : Submodule R (∀ i, M i)) : Submodule R (∀ i, M i) :=
  Submodule.pi Set.univ (finiteWeightInitialPiece U)

@[simp]
theorem mem_finiteWeightInitial_iff (U : Submodule R (∀ i, M i)) (x : ∀ i, M i) :
    x ∈ finiteWeightInitial U ↔ ∀ i, x i ∈ finiteWeightInitialPiece U i := by
  simp [finiteWeightInitial, Submodule.mem_pi]

theorem single_mem_finiteWeightInitial (U : Submodule R (∀ i, M i)) (i : Fin n)
    {v : M i} (hv : v ∈ finiteWeightInitialPiece U i) :
    Pi.single i v ∈ finiteWeightInitial U := by
  classical
  apply (mem_finiteWeightInitial_iff U _).mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa using hv
  · simp [hji]

theorem finiteWeightInitial_homogeneous (U : Submodule R (∀ i, M i)) :
    ∀ x ∈ finiteWeightInitial U, ∀ i, Pi.single i (x i) ∈ finiteWeightInitial U := by
  intro x hx i
  exact single_mem_finiteWeightInitial U i ((mem_finiteWeightInitial_iff U x).mp hx i)

/-- All least-coordinate forms of all elements of U; a zero coordinate
contributes only the zero vector and does not alter the generated submodule. -/
def finiteWeightInitialGenerators (U : Submodule R (∀ i, M i)) : Set (∀ i, M i) :=
  {v | ∃ x ∈ U, ∃ i : Fin n, finiteWeightPrefixProjection R M i.val x = 0 ∧
    v = Pi.single i (x i)}

/-- The product-of-pieces construction is exactly the full span of the
least-weight components of all U-elements. -/
theorem finiteWeightInitial_eq_span (U : Submodule R (∀ i, M i)) :
    finiteWeightInitial U = Submodule.span R (finiteWeightInitialGenerators U) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← LinearMap.sum_single_apply M x]
    apply (Submodule.span R (finiteWeightInitialGenerators U)).sum_mem
    intro i hi
    obtain ⟨v, hv, hvi⟩ := (mem_finiteWeightInitial_iff U x).mp hx i
    apply Submodule.subset_span
    exact ⟨v, hv.1, i, hv.2, congrArg (Pi.single i) hvi.symm⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, i, hlow, rfl⟩
    exact single_mem_finiteWeightInitial U i ⟨x, ⟨hx, hlow⟩, rfl⟩

/-- Initial formation fixes every coordinatewise homogeneous submodule. -/
theorem finiteWeightInitial_eq_of_homogeneous (U : Submodule R (∀ i, M i))
    (hU : ∀ x ∈ U, ∀ i, Pi.single i (x i) ∈ U) : finiteWeightInitial U = U := by
  classical
  apply le_antisymm
  · intro x hx
    rw [← LinearMap.sum_single_apply M x]
    apply U.sum_mem
    intro i hi
    obtain ⟨v, hv, hvi⟩ := (mem_finiteWeightInitial_iff U x).mp hx i
    change v i = x i at hvi
    rw [← hvi]
    exact hU v hv.1 i
  · intro x hx
    apply (mem_finiteWeightInitial_iff U x).mpr
    intro i
    refine ⟨Pi.single i (x i), ⟨hU x hx i, ?_⟩, ?_⟩
    · change finiteWeightPrefixProjection R M i.val (Pi.single i (x i)) = 0
      simp [finiteWeightPrefixProjection_single]
    · simp

/-- Initial formation leaves every projected kernel piece unchanged. -/
theorem finiteWeightInitialPiece_initial (U : Submodule R (∀ i, M i)) (i : Fin n) :
    finiteWeightInitialPiece (finiteWeightInitial U) i = finiteWeightInitialPiece U i := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_finiteWeightInitial_iff U x).mp hx.1 i
  · intro v hv
    refine ⟨Pi.single i v, ⟨single_mem_finiteWeightInitial U i hv, ?_⟩, ?_⟩
    · change finiteWeightPrefixProjection R M i.val (Pi.single i v) = 0
      simp [finiteWeightPrefixProjection_single]
    · simp

@[simp]
theorem finiteWeightPrefixImage_zero (U : Submodule R (∀ i, M i)) :
    finiteWeightPrefixImage U 0 = ⊥ := by
  simp [finiteWeightPrefixImage]

theorem finiteWeightPrefixImage_eq_self_of_le (U : Submodule R (∀ i, M i))
    {k : ℕ} (hnk : n ≤ k) : finiteWeightPrefixImage U k = U := by
  rw [finiteWeightPrefixImage, finiteWeightPrefixProjection_eq_id_of_le hnk,
    Submodule.map_id]

/-- Initial formation preserves every prefix length. The proof uses the
explicit exact sequence repeatedly, and never cancels infinite lengths. -/
theorem finiteWeightInitial_prefix_length (U : Submodule R (∀ i, M i)) (k : ℕ) :
    Module.length R (finiteWeightPrefixImage (finiteWeightInitial U) k) =
      Module.length R (finiteWeightPrefixImage U k) := by
  have hbounded : ∀ k : ℕ, k ≤ n →
      Module.length R (finiteWeightPrefixImage (finiteWeightInitial U) k) =
        Module.length R (finiteWeightPrefixImage U k) := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [finiteWeightPrefixImage_zero, finiteWeightPrefixImage_zero]
    | succ k ih =>
      intro hk
      let i : Fin n := ⟨k, Nat.lt_of_succ_le hk⟩
      have hrec := finiteWeightPrefixImage_length_succ (finiteWeightInitial U) i
      rw [finiteWeightInitialPiece_initial, ih (Nat.le_of_succ_le hk)] at hrec
      exact hrec.trans (finiteWeightPrefixImage_length_succ U i).symm
  by_cases hk : k ≤ n
  · exact hbounded k hk
  · have hnk : n ≤ k := le_of_not_ge hk
    rw [finiteWeightPrefixImage_eq_self_of_le _ hnk,
      finiteWeightPrefixImage_eq_self_of_le _ hnk]
    have h := hbounded n le_rfl
    rw [finiteWeightPrefixImage_eq_self_of_le _ (le_refl n),
      finiteWeightPrefixImage_eq_self_of_le _ (le_refl n)] at h
    exact h

/-- In particular, the full initial submodule has the same actual module
length as the original submodule. -/
theorem finiteWeightInitial_length (U : Submodule R (∀ i, M i)) :
    Module.length R (finiteWeightInitial U) = Module.length R U := by
  have h := finiteWeightInitial_prefix_length U n
  rw [finiteWeightPrefixImage_eq_self_of_le _ (le_refl n),
    finiteWeightPrefixImage_eq_self_of_le _ (le_refl n)] at h
  exact h

end AbelFormalization
