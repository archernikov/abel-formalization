import AbelFormalization.OrderedClusterAlgebraicDescent
import AbelFormalization.AnalyticGermNoetherian
import Mathlib.RingTheory.KrullDimension.Polynomial

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

/-- The exact natural Krull-dimension bound for a prefix polynomial ring over
the ring of real-analytic germs in `p` variables. -/
abbrev orderedClusterPrefixAnalyticKrullBound
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher k : ℕ) : ℕ :=
  p + Nat.card
    (ClusterOperationSymbol (data.OrderedClusterPrefixBlock k)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) k))

/-- Each analytic-germ prefix ring has the dimension predicted by the number
of its finite polynomial variables. -/
theorem orderedClusterPrefixRing_krullDimLE
    {m p : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher k : ℕ) :
    Ring.KrullDimLE
      (orderedClusterPrefixAnalyticKrullBound (p := p) data higher k)
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) := by
  rw [Ring.krullDimLE_iff,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    realAnalyticGerm_dimension]
  simp [orderedClusterPrefixAnalyticKrullBound, Nat.cast_add]

/-- The ordered-prefix algebraic descent over real-analytic germs needs no
dimension or Noetherianity assumptions beyond the proved analytic-germ
theorems. -/
theorem exists_orderedClusterPrefixAlgebraicDescent_realAnalyticGerm
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
  letI : ∀ k, Algebra ℚ
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) :=
    fun _ ↦ inferInstance
  letI : ∀ k, IsNoetherianRing
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) :=
    fun _ ↦ inferInstance
  letI : ∀ k, Ring.KrullDimLE
      (orderedClusterPrefixAnalyticKrullBound (p := p) data higher k)
      (data.OrderedClusterPrefixRing (RealAnalyticGerm p) higher k) :=
    fun k ↦ data.orderedClusterPrefixRing_krullDimLE higher k
  exact data.exists_orderedClusterPrefixAlgebraicDescent
    (RealAnalyticGerm p) higher initialIdeal
      (orderedClusterPrefixAnalyticKrullBound (p := p) data higher)

end RepresentativeClusterSubsequence
end AbelFormalization
