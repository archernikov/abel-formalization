import AbelFormalization.OrderedClusterAlgebraicDescent
import AbelFormalization.AnalyticGermNoetherian
import Mathlib.RingTheory.KrullDimension.Polynomial

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

universe u

/-- Exact number of polynomial variables contributed by a constant-size
cluster-operation block family. -/
theorem card_clusterOperationSymbol_const
    (Block : Type u) [Fintype Block] (D : ℕ) :
    Fintype.card (ClusterOperationSymbol Block (fun _ ↦ D)) =
      (D + 2) * Fintype.card Block := by
  classical
  simp [ClusterOperationSymbol, CentralPolynomialIndex, Nat.mul_add,
    Nat.mul_comm]
  omega

/-- Exact Krull-dimension bound for one ordered prefix over analytic germs. -/
theorem orderedClusterPrefixRing_krullDimLE_exact
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (p higher k : ℕ) :
    Ring.KrullDimLE
      (p + Fintype.card
        (ClusterOperationSymbol (data.OrderedClusterPrefixBlock k)
          (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) k)))
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) := by
  rw [Ring.krullDimLE_iff,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    realAnalyticGerm_dimension]
  simp only [Nat.card_eq_fintype_card, Nat.cast_add]
  exact le_rfl

/-- The exact bound written in terms of the number of blocks in the prefix. -/
theorem orderedClusterPrefixRing_krullDimLE
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (p higher k : ℕ) :
    Ring.KrullDimLE
      (p + (higher + 3) *
        Fintype.card (data.OrderedClusterPrefixBlock k))
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) := by
  simpa only [card_clusterOperationSymbol_const, Nat.add_assoc] using
    data.orderedClusterPrefixRing_krullDimLE_exact p higher k

/-- Every ordered prefix has dimension at most the dimension of the analytic
germ base plus the number of variables in the full `m`-block operation ring. -/
theorem orderedClusterPrefixRing_krullDimLE_uniform
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (p higher k : ℕ) :
    Ring.KrullDimLE (p + (higher + 3) * m)
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) := by
  have hcard :
      Fintype.card (data.OrderedClusterPrefixBlock k) ≤ m := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective
        (fun i : data.OrderedClusterPrefixBlock k ↦ i.1)
        Subtype.val_injective
  letI := data.orderedClusterPrefixRing_krullDimLE p higher k
  exact Order.KrullDimLE.mono
    (Nat.add_le_add_left (Nat.mul_le_mul_left (higher + 3) hcard) p) _

/-- The uniform prefix bound packaged in exactly the dependent-function form
required by `exists_orderedClusterPrefixAlgebraicDescent`. -/
theorem orderedClusterPrefixRing_krullDimLE_all
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (p higher : ℕ) :
    ∀ k, Ring.KrullDimLE (p + (higher + 3) * m)
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) :=
  fun k ↦ data.orderedClusterPrefixRing_krullDimLE_uniform p higher k

/-- The analytic-germ specialization of ordered-cluster algebraic descent,
with its dimension hypothesis discharged by the exact stagewise prefix bound. -/
theorem exists_orderedClusterPrefixAlgebraicDescent_realAnalyticGerm
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (p higher : ℕ)
    (initialIdeal : Ideal
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher
        data.orderedClusterCount)) :
    ∃ finalIdeal : Ideal
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0),
      Nonempty (OrderedClusterPrefixAlgebraicDescent
        (RealAnalyticGerm p) data higher initialIdeal 0
          (Nat.zero_le _) finalIdeal) := by
  letI : Algebra ℚ (RealAnalyticGerm p) :=
    ((algebraMap ℝ (RealAnalyticGerm p)).comp (algebraMap ℚ ℝ)).toAlgebra
  letI : ∀ k, Algebra ℚ
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) :=
    fun _ ↦ inferInstance
  letI : ∀ k, IsNoetherianRing
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) :=
    fun _ ↦ inferInstance
  letI : ∀ k, Ring.KrullDimLE
      (p + (higher + 3) *
        Fintype.card (data.OrderedClusterPrefixBlock k))
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) :=
    fun k ↦ data.orderedClusterPrefixRing_krullDimLE p higher k
  exact data.exists_orderedClusterPrefixAlgebraicDescent
    (RealAnalyticGerm p) higher initialIdeal
      (fun k ↦ p + (higher + 3) *
        Fintype.card (data.OrderedClusterPrefixBlock k))

end RepresentativeClusterSubsequence
end AbelFormalization
