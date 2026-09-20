import AbelFormalization.HermiteRankPreprocessedIndividualBoundaryValues

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

set_option autoImplicit false

universe u

example
    {R : Type u} [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    {data : RepresentativeClusterSubsequence time}
    {higher : ℕ}
    {fixedSteps : data.OrderedClusterIndividualStepPlan}
    {fixedOrder : data.OrderedClusterFinalOrderPlan}
    {initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount)}
    {finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0)}
    (descent : OrderedClusterPreprocessedAlgebraicDescent R data higher
      fixedSteps fixedOrder initialIdeal 0 (Nat.zero_le _) finalIdeal)
    (c : Fin data.orderedClusterCount)
    (hc : c.val + 1 < data.orderedClusterCount) :
    (descent.clusterStage ⟨c.val + 1, hc⟩).currentIdeal =
      (descent.clusterStage c).nextIdeal := by
  rfl

end RepresentativeClusterSubsequence
end AbelFormalization
