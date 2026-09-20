import AbelFormalization.OrderedClusterAlgebraicDescent
import AbelFormalization.AnalyticGermNoetherian
import Mathlib.RingTheory.KrullDimension.Polynomial

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

/-- Exact natural Krull-dimension bound for an analytic-germ prefix ring. -/
abbrev test_orderedClusterPrefixAnalyticKrullBound
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher k : ℕ) : ℕ :=
  p + Nat.card
    (ClusterOperationSymbol (data.OrderedClusterPrefixBlock k)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) k))

theorem test_orderedClusterPrefixRing_krullDimLE
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher k : ℕ) :
    Ring.KrullDimLE
      (test_orderedClusterPrefixAnalyticKrullBound (p := p) data higher k)
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) := by
  rw [Ring.krullDimLE_iff,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    realAnalyticGerm_dimension]
  simp [test_orderedClusterPrefixAnalyticKrullBound, Nat.cast_add]

theorem test_exists_orderedClusterPrefixAnalyticAlgebraicDescent
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ)
    (initialIdeal : Ideal
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher
        data.orderedClusterCount)) :
    ∃ finalIdeal : Ideal
        (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher 0),
      Nonempty (OrderedClusterPrefixAlgebraicDescent
        (RealAnalyticGerm p) data higher initialIdeal 0
          (Nat.zero_le _) finalIdeal) := by
  letI : Algebra ℚ (RealAnalyticGerm p) :=
    ((algebraMap ℝ (RealAnalyticGerm p)).comp
      (algebraMap ℚ ℝ)).toAlgebra
  letI (k : ℕ) : Ring.KrullDimLE
      (test_orderedClusterPrefixAnalyticKrullBound (p := p) data higher k)
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) :=
    test_orderedClusterPrefixRing_krullDimLE data higher k
  exact data.exists_orderedClusterPrefixAlgebraicDescent
    (RealAnalyticGerm p) higher initialIdeal
      (test_orderedClusterPrefixAnalyticKrullBound (p := p) data higher)

end RepresentativeClusterSubsequence
end AbelFormalization
