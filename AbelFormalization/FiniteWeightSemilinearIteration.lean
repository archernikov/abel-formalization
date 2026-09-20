import AbelFormalization.FiniteWeightIteration
import AbelFormalization.FiniteWeightQuotient

set_option autoImplicit false

/-!
# Semilinear transport of finite-weight descent

A coordinatewise semilinear quotient commutes with the finite-weight descent
iteration once its kernel is contained in the initial submodule and the source
and target automorphisms intertwine.  The kernel hypotheses needed at later
steps follow from coordinatewise homogeneity and intertwining.
-/

noncomputable section

namespace AbelFormalization

variable {R S : Type*} [Ring R] [Ring S]
variable {σ : R →+* S} [RingHomSurjective σ]
variable {n : ℕ}
variable {M : Fin n → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable {N : Fin n → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module S (N i)]

/-- The kernel of a coordinatewise map is homogeneous for the finite weight
decomposition. -/
theorem ker_finiteWeightPiMap_homogeneous
    (f : ∀ i, M i →ₛₗ[σ] N i) :
    ∀ x ∈ LinearMap.ker (finiteWeightPiMap f), ∀ i,
      Pi.single i (x i) ∈ LinearMap.ker (finiteWeightPiMap f) := by
  classical
  intro x hx i
  apply (mem_ker_finiteWeightPiMap_iff f _).mpr
  intro j
  by_cases hji : j = i
  · subst j
    simpa using (mem_ker_finiteWeightPiMap_iff f x).mp hx i
  · simp [hji]

omit [RingHomSurjective σ] in
/-- Intertwining equivalences preserve the kernel of the coordinatewise map. -/
theorem map_ker_finiteWeightPiMap_eq
    (f : ∀ i, M i →ₛₗ[σ] N i)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (J' : (∀ i, N i) ≃ₗ[S] (∀ i, N i))
    (hcomm : ∀ x, finiteWeightPiMap f (J x) =
      J' (finiteWeightPiMap f x)) :
    (LinearMap.ker (finiteWeightPiMap f)).map J.toLinearMap =
      LinearMap.ker (finiteWeightPiMap f) := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply LinearMap.mem_ker.mpr
    change finiteWeightPiMap f (J x) = 0
    rw [hcomm, LinearMap.mem_ker.mp hx, map_zero]
  · intro y hy
    refine ⟨J.symm y, ?_, J.apply_symm_apply y⟩
    apply LinearMap.mem_ker.mpr
    apply J'.injective
    rw [← hcomm, J.apply_symm_apply, LinearMap.mem_ker.mp hy, map_zero]

/-- Intertwining maps identify the image of a submodule after applying the
source equivalence with the image obtained by applying the target
equivalence. -/
theorem map_map_finiteWeightPiMap_eq
    (f : ∀ i, M i →ₛₗ[σ] N i)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (J' : (∀ i, N i) ≃ₗ[S] (∀ i, N i))
    (hcomm : ∀ x, finiteWeightPiMap f (J x) =
      J' (finiteWeightPiMap f x))
    (U : Submodule R (∀ i, M i)) :
    (U.map J.toLinearMap).map (finiteWeightPiMap f) =
      (U.map (finiteWeightPiMap f)).map J'.toLinearMap := by
  apply le_antisymm
  · rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨finiteWeightPiMap f x, ⟨x, hx, rfl⟩, ?_⟩
    simpa using (hcomm x).symm
  · rintro y ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨J x, ⟨x, hx, rfl⟩, ?_⟩
    simpa using hcomm x

/-- Coordinatewise semilinear images of homogeneous submodules are
homogeneous. -/
theorem map_finiteWeightPiMap_homogeneous
    (f : ∀ i, M i →ₛₗ[σ] N i)
    (U : Submodule R (∀ i, M i))
    (hU : ∀ x ∈ U, ∀ i, Pi.single i (x i) ∈ U) :
    ∀ y ∈ U.map (finiteWeightPiMap f), ∀ i,
      Pi.single i (y i) ∈ U.map (finiteWeightPiMap f) := by
  classical
  rintro y ⟨x, hx, rfl⟩ i
  refine ⟨Pi.single i (x i), hU x hx i, ?_⟩
  rw [finiteWeightPiMap_single]
  rfl

/-- An intertwining coordinatewise map sends an invariant source submodule
to an invariant target submodule. -/
theorem map_finiteWeightPiMap_invariant
    (f : ∀ i, M i →ₛₗ[σ] N i)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (J' : (∀ i, N i) ≃ₗ[S] (∀ i, N i))
    (hcomm : ∀ x, finiteWeightPiMap f (J x) =
      J' (finiteWeightPiMap f x))
    (U : Submodule R (∀ i, M i))
    (hinv : U.map J.toLinearMap = U) :
    (U.map (finiteWeightPiMap f)).map J'.toLinearMap =
      U.map (finiteWeightPiMap f) := by
  rw [← map_map_finiteWeightPiMap_eq f J J' hcomm, hinv]

/-- Equality of semilinear images lifts to equality of submodules once both
submodules contain the kernel. -/
theorem eq_of_map_eq_map_of_ker_le
    (g : (∀ i, M i) →ₛₗ[σ] (∀ i, N i))
    (U V : Submodule R (∀ i, M i))
    (hkerU : LinearMap.ker g ≤ U)
    (hkerV : LinearMap.ker g ≤ V)
    (hmap : U.map g = V.map g) : U = V := by
  apply le_antisymm
  · intro x hx
    have hfx : g x ∈ V.map g := by
      rw [← hmap]
      exact Submodule.mem_map_of_mem hx
    rcases hfx with ⟨y, hy, hyx⟩
    have hdiff : x - y ∈ LinearMap.ker g := by
      apply LinearMap.mem_ker.mpr
      rw [map_sub, hyx, sub_self]
    simpa only [sub_add_cancel] using V.add_mem (hkerV hdiff) hy
  · intro y hy
    have hfy : g y ∈ U.map g := by
      rw [hmap]
      exact Submodule.mem_map_of_mem hy
    rcases hfy with ⟨x, hx, hxy⟩
    have hdiff : y - x ∈ LinearMap.ker g := by
      apply LinearMap.mem_ker.mpr
      rw [map_sub, hxy, sub_self]
    simpa only [sub_add_cancel] using U.add_mem (hkerU hdiff) hx

/-- Invariance of the image under an intertwining target equivalence lifts
to invariance upstairs when the source submodule contains the kernel. -/
theorem invariant_of_map_finiteWeightPiMap_invariant
    (f : ∀ i, M i →ₛₗ[σ] N i)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (J' : (∀ i, N i) ≃ₗ[S] (∀ i, N i))
    (hcomm : ∀ x, finiteWeightPiMap f (J x) =
      J' (finiteWeightPiMap f x))
    (U : Submodule R (∀ i, M i))
    (hker : LinearMap.ker (finiteWeightPiMap f) ≤ U)
    (hinv : (U.map (finiteWeightPiMap f)).map J'.toLinearMap =
      U.map (finiteWeightPiMap f)) :
    U.map J.toLinearMap = U := by
  apply eq_of_map_eq_map_of_ker_le (finiteWeightPiMap f)
  · rw [← map_ker_finiteWeightPiMap_eq f J J' hcomm]
    exact Submodule.map_mono hker
  · exact hker
  · rw [map_map_finiteWeightPiMap_eq f J J' hcomm, hinv]

/-- If the coordinatewise kernel is contained in a submodule, it remains
contained after one finite-weight descent step. -/
theorem ker_finiteWeightPiMap_le_descentStep
    (f : ∀ i, M i →ₛₗ[σ] N i)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (J' : (∀ i, N i) ≃ₗ[S] (∀ i, N i))
    (hcomm : ∀ x, finiteWeightPiMap f (J x) =
      J' (finiteWeightPiMap f x))
    (U : Submodule R (∀ i, M i))
    (hker : LinearMap.ker (finiteWeightPiMap f) ≤ U) :
    LinearMap.ker (finiteWeightPiMap f) ≤
      finiteWeightDescentStep J U := by
  rw [finiteWeightDescentStep]
  rw [← finiteWeightInitial_eq_of_homogeneous
    (LinearMap.ker (finiteWeightPiMap f))
    (ker_finiteWeightPiMap_homogeneous f)]
  apply finiteWeightInitial_mono
  rw [← map_ker_finiteWeightPiMap_eq f J J' hcomm]
  exact Submodule.map_mono hker

/-- The coordinatewise kernel is contained in every source iterate. -/
theorem ker_finiteWeightPiMap_le_descentIterate
    (f : ∀ i, M i →ₛₗ[σ] N i)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (J' : (∀ i, N i) ≃ₗ[S] (∀ i, N i))
    (hcomm : ∀ x, finiteWeightPiMap f (J x) =
      J' (finiteWeightPiMap f x))
    (N₀ : Submodule R (∀ i, M i))
    (hker : LinearMap.ker (finiteWeightPiMap f) ≤ N₀) :
    ∀ j, LinearMap.ker (finiteWeightPiMap f) ≤
      finiteWeightDescentIterate J N₀ j := by
  intro j
  induction j with
  | zero => exact hker
  | succ j ih =>
      exact ker_finiteWeightPiMap_le_descentStep f J J' hcomm _ ih

/-- A coordinatewise semilinear quotient intertwining the equivalences
commutes with one finite-weight descent step. -/
theorem map_finiteWeightDescentStep_eq
    (f : ∀ i, M i →ₛₗ[σ] N i)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (J' : (∀ i, N i) ≃ₗ[S] (∀ i, N i))
    (hcomm : ∀ x, finiteWeightPiMap f (J x) =
      J' (finiteWeightPiMap f x))
    (U : Submodule R (∀ i, M i))
    (hker : LinearMap.ker (finiteWeightPiMap f) ≤ U) :
    (finiteWeightDescentStep J U).map (finiteWeightPiMap f) =
      finiteWeightDescentStep J' (U.map (finiteWeightPiMap f)) := by
  unfold finiteWeightDescentStep
  rw [map_finiteWeightInitial_eq_finiteWeightInitial_map]
  · rw [map_map_finiteWeightPiMap_eq f J J' hcomm]
  · rw [← map_ker_finiteWeightPiMap_eq f J J' hcomm]
    exact Submodule.map_mono hker

/-- The image of every source iterate is the corresponding target iterate. -/
theorem map_finiteWeightDescentIterate_eq
    (f : ∀ i, M i →ₛₗ[σ] N i)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (J' : (∀ i, N i) ≃ₗ[S] (∀ i, N i))
    (hcomm : ∀ x, finiteWeightPiMap f (J x) =
      J' (finiteWeightPiMap f x))
    (N₀ : Submodule R (∀ i, M i))
    (hker : LinearMap.ker (finiteWeightPiMap f) ≤ N₀) :
    ∀ j,
      (finiteWeightDescentIterate J N₀ j).map (finiteWeightPiMap f) =
        finiteWeightDescentIterate J' (N₀.map (finiteWeightPiMap f)) j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [finiteWeightDescentIterate_succ,
        finiteWeightDescentIterate_succ,
        map_finiteWeightDescentStep_eq f J J' hcomm _
          (ker_finiteWeightPiMap_le_descentIterate
            f J J' hcomm N₀ hker j), ih]

end AbelFormalization
