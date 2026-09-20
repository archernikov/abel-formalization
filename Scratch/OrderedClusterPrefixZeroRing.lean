import AbelFormalization.OrderedClusterAlgebraicDescent

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

universe u

noncomputable instance test_orderedClusterPrefixBlockZeroIsEmpty
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) :
    IsEmpty (data.OrderedClusterPrefixBlock 0) :=
  data.orderedClusterPrefixZeroEquiv.isEmpty

example
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) (higher : ℕ) :
    IsEmpty
      (ClusterOperationSymbol (data.OrderedClusterPrefixBlock 0)
        (data.orderedClusterPrefixConstantDerivativeCount (higher + 1) 0)) :=
  inferInstance

/-- The zero-prefix polynomial ring has no variables. -/
def test_orderedClusterPrefixRingZeroAlgEquiv
    (R : Type u) [CommSemiring R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) (higher : ℕ) :
    data.OrderedClusterPrefixRing R higher 0 ≃ₐ[R] R :=
  MvPolynomial.isEmptyAlgEquiv R _

end RepresentativeClusterSubsequence
end AbelFormalization
