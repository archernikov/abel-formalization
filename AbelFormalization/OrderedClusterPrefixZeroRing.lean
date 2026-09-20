import AbelFormalization.OrderedClusterAlgebraicDescent

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

universe u

/-- The block type in the zero prefix is empty. -/
noncomputable instance orderedClusterPrefixBlockZeroIsEmpty
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) :
    IsEmpty (data.OrderedClusterPrefixBlock 0) :=
  data.orderedClusterPrefixZeroEquiv.isEmpty

/-- The zero-prefix ring has no polynomial variables and is canonically the
coefficient ring. -/
def orderedClusterPrefixRingZeroAlgEquiv
    (R : Type u) [CommSemiring R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) (higher : ℕ) :
    data.OrderedClusterPrefixRing R higher 0 ≃ₐ[R] R :=
  MvPolynomial.isEmptyAlgEquiv R _

end RepresentativeClusterSubsequence
end AbelFormalization
