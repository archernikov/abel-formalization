import AbelFormalization.FiniteWeightIteration
import AbelFormalization.FiniteWeightQuotient

set_option autoImplicit false

/-!
# Order lemmas for finite-weight descent

The finite-weight descent step is monotone.  Consequently, its iterates are
monotone in the initial submodule, fixed points remain fixed, and any iterate
starting between two fixed points remains between them.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [Ring R] {n : ℕ}
variable {M : Fin n → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The finite-weight descent step is monotone in its input submodule. -/
theorem finiteWeightDescentStep_mono
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    {U V : Submodule R (∀ i, M i)} (hUV : U ≤ V) :
    finiteWeightDescentStep J U ≤ finiteWeightDescentStep J V := by
  unfold finiteWeightDescentStep
  exact finiteWeightInitial_mono (Submodule.map_mono hUV)

/-- Every finite-weight descent iterate is monotone in the initial
submodule. -/
theorem finiteWeightDescentIterate_mono
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    {U V : Submodule R (∀ i, M i)} (hUV : U ≤ V) (j : ℕ) :
    finiteWeightDescentIterate J U j ≤
      finiteWeightDescentIterate J V j := by
  induction j with
  | zero => exact hUV
  | succ j ih =>
      change finiteWeightDescentStep J
          (finiteWeightDescentIterate J U j) ≤
        finiteWeightDescentStep J
          (finiteWeightDescentIterate J V j)
      exact finiteWeightDescentStep_mono J ih

/-- Restarting the iteration at time `a` and running for `b` more steps is
the same as running the original iteration for `a + b` steps. -/
theorem finiteWeightDescentIterate_add
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (N : Submodule R (∀ i, M i)) (a b : ℕ) :
    finiteWeightDescentIterate J N (a + b) =
      finiteWeightDescentIterate J
        (finiteWeightDescentIterate J N a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [Nat.add_succ]
      change finiteWeightDescentStep J
          (finiteWeightDescentIterate J N (a + b)) =
        finiteWeightDescentStep J
          (finiteWeightDescentIterate J
            (finiteWeightDescentIterate J N a) b)
      rw [ih]

/-- An actual fixed point of the descent step stays fixed under every
iterate. -/
theorem finiteWeightDescentIterate_eq_self_of_fixed
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (N : Submodule R (∀ i, M i))
    (hfixed : finiteWeightDescentStep J N = N) (j : ℕ) :
    finiteWeightDescentIterate J N j = N := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change finiteWeightDescentStep J
        (finiteWeightDescentIterate J N j) = N
      rw [ih, hfixed]

/-- A homogeneous `J`-invariant submodule stays fixed under every descent
iterate. -/
theorem finiteWeightDescentIterate_eq_self_of_invariant
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (N : Submodule R (∀ i, M i))
    (hN : ∀ x ∈ N, ∀ i, Pi.single i (x i) ∈ N)
    (hJN : N.map J.toLinearMap = N) (j : ℕ) :
    finiteWeightDescentIterate J N j = N := by
  exact finiteWeightDescentIterate_eq_self_of_fixed J N
    (finiteWeightDescentStep_eq_self_of_invariant J N hN hJN) j

/-- If the initial submodule lies between two fixed points, then every
iterate lies between the same fixed points. -/
theorem finiteWeightDescentIterate_between_fixed
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (D N K : Submodule R (∀ i, M i))
    (hDfixed : finiteWeightDescentStep J D = D)
    (hKfixed : finiteWeightDescentStep J K = K)
    (hDN : D ≤ N) (hNK : N ≤ K) (j : ℕ) :
    D ≤ finiteWeightDescentIterate J N j ∧
      finiteWeightDescentIterate J N j ≤ K := by
  constructor
  · calc
      D = finiteWeightDescentIterate J D j :=
        (finiteWeightDescentIterate_eq_self_of_fixed J D hDfixed j).symm
      _ ≤ finiteWeightDescentIterate J N j :=
        finiteWeightDescentIterate_mono J hDN j
  · calc
      finiteWeightDescentIterate J N j ≤
          finiteWeightDescentIterate J K j :=
        finiteWeightDescentIterate_mono J hNK j
      _ = K := finiteWeightDescentIterate_eq_self_of_fixed J K hKfixed j

/-- If the initial submodule lies between two homogeneous `J`-invariant
submodules, then every iterate lies between those submodules. -/
theorem finiteWeightDescentIterate_between
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (D N K : Submodule R (∀ i, M i))
    (hD : ∀ x ∈ D, ∀ i, Pi.single i (x i) ∈ D)
    (hJD : D.map J.toLinearMap = D)
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hJK : K.map J.toLinearMap = K)
    (hDN : D ≤ N) (hNK : N ≤ K) (j : ℕ) :
    D ≤ finiteWeightDescentIterate J N j ∧
      finiteWeightDescentIterate J N j ≤ K := by
  exact finiteWeightDescentIterate_between_fixed J D N K
    (finiteWeightDescentStep_eq_self_of_invariant J D hD hJD)
    (finiteWeightDescentStep_eq_self_of_invariant J K hK hJK)
    hDN hNK j

end AbelFormalization
