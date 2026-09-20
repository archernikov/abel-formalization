import AbelFormalization.OrderedClusterPrefixCurrying
import AbelFormalization.ClusterAlgebraicReduction

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

universe u

/-- The flat polynomial ring in all operation variables belonging to the
first `k` ordered clusters. -/
abbrev OrderedClusterPrefixRing
    (R : Type u) [CommSemiring R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher k : ℕ) :=
  MvPolynomial
    (ClusterOperationSymbol (data.OrderedClusterPrefixBlock k)
      (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) k)) R

/-- The exact active-cluster ideal obtained by currying a prefix-stage ideal
over the smaller-prefix coefficient ring. -/
def orderedClusterPrefixCurriedIdeal
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    Ideal
      (MvPolynomial
        (ClusterOperationSymbol (Fin (data.orderedCluster c).card)
          (terminalTotalDerivativeCount (fun _ ↦ higher)))
        (data.OrderedClusterPrefixRing R higher c.val)) :=
  I.map (data.orderedClusterPrefixCurryAlgEquiv R c (higher + 1)).toRingHom

/-- Canonical one-cluster algebraic reduction of a prefix-stage ideal. -/
theorem nonempty_orderedClusterPrefixAlgebraicReductionCertificate
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1)))
    {krullDim : ℕ}
    [Algebra ℚ (data.OrderedClusterPrefixRing R higher c.val)]
    [IsNoetherianRing (data.OrderedClusterPrefixRing R higher c.val)]
    [Ring.KrullDimLE krullDim
      (data.OrderedClusterPrefixRing R higher c.val)] :
    Nonempty
      (ClusterAlgebraicReductionCertificate
        (data.OrderedClusterPrefixRing R higher c.val)
        (data.orderedCluster c).card (fun _ ↦ higher)
        (data.orderedClusterPrefixCurriedIdeal R higher c I)) := by
  exact exists_clusterAlgebraicReductionCertificate
    (krullDim := krullDim) (fun _ ↦ higher)
    (MonomialOrder.lex : MonomialOrder
      (Fin (clusterTerminalReindexCard (fun _ :
        Fin (data.orderedCluster c).card ↦ higher))))
    (clusterTerminalFiniteReindex (fun _ :
      Fin (data.orderedCluster c).card ↦ higher))
    (data.orderedClusterPrefixCurriedIdeal R higher c I)

/-- Currying a prefix-stage ideal preserves its height exactly. -/
theorem orderedClusterPrefixCurriedIdeal_height
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1))) :
    (data.orderedClusterPrefixCurriedIdeal R higher c I).height = I.height :=
  (data.orderedClusterPrefixCurryAlgEquiv R c (higher + 1)).toRingEquiv.height_map I

/-- The one-cluster height loss has the manuscript's exact form on the
canonical ordered-prefix rings. -/
theorem orderedClusterPrefixAlgebraicReduction_preserves_baseHeight
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ) (c : Fin data.orderedClusterCount)
    (I : Ideal (data.OrderedClusterPrefixRing R higher (c.val + 1)))
    (certificate : ClusterAlgebraicReductionCertificate
      (data.OrderedClusterPrefixRing R higher c.val)
      (data.orderedCluster c).card (fun _ ↦ higher)
      (data.orderedClusterPrefixCurriedIdeal R higher c I))
    (q : ℕ)
    (hheight : (q : ENat) + ((data.orderedCluster c).card : ENat) ≤
      I.height) :
    (q : ENat) ≤ certificate.terminalized.coefficientIdeal.height := by
  apply clusterAlgebraicReduction_preserves_baseHeight certificate
  rw [data.orderedClusterPrefixCurriedIdeal_height R higher c I]
  exact hheight

end RepresentativeClusterSubsequence
end AbelFormalization
