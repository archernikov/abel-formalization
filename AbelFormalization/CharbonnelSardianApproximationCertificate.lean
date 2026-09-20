import AbelFormalization.CharbonnelBoundaryApproximation
import AbelFormalization.CharbonnelSardianEmptyInterior

/-!
# Sardian approximation certificates

This file joins the independently formalized parts of Wilkie's approximation
argument:

* a finite family of Sardian constituents at one common parameter depth;
* at least one derivative for every constituent equation;
* the asymmetric closure/boundary approximation clauses in 3.6;
* Hausdorff-nullity of the finite constituent family.

The resulting certificate can be fed directly to the trace descent of Lemma
3.3 once the two Charbonnel smallness facts are available for the ambient
description family.  It does not assert that every description has such a
certificate; that is the later rank induction.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A finite common-depth Sardian approximation with the constituent shape
and the two asymmetric approximation clauses of Wilkie's condition 3.6 for
`A`.  If the common hidden arity is `K`, then the carrier stores `K + 1`
positive approximation parameters, so its modulus has depth `K + 1`.

The positive differentiability order records the source's `C¹` requirement.
The equations here are restricted to the chosen geometric family `G`, which
is the specialization used by the surrounding development. -/
structure CharbonnelSardianApproximationCertificate
    (G : (d : ℕ) → Set (RealEuclideanFunction d))
    (order n : ℕ) (A : Set (RealEuclidean n)) where
  order_pos : 0 < order
  commonHiddenArity : ℕ
  family : CharbonnelFiniteSardianFamily
    G order n commonHiddenArity
  modulus : CharbonnelModulus (commonHiddenArity + 1)
  approximates :
    CharbonnelModulus.IsClosureBoundaryApproximation
      modulus family.carrier A

namespace CharbonnelSardianApproximationCertificate

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n : ℕ} {A : Set (RealEuclidean n)}

/-- The approximating carrier is projected-zero. -/
theorem carrier_isProjectedZeroSet
    (hG : IsGeometricFunctionFamily G)
    (certificate : CharbonnelSardianApproximationCertificate G order n A) :
    IsProjectedZeroSet G certificate.family.carrier :=
  certificate.family.carrier_isProjectedZeroSet hG

/-- Hence the approximating carrier belongs to the Charbonnel closure over
literal zero-set generators. -/
theorem carrier_mem_literalZeroSet_charbonnelClosure
    (hG : IsGeometricFunctionFamily G)
    (certificate : CharbonnelSardianApproximationCertificate G order n A) :
    certificate.family.carrier ∈
      charbonnelClosure (literalZeroSetFamily G)
        (n + (certificate.commonHiddenArity + 1)) :=
  (certificate.carrier_isProjectedZeroSet hG).mem_literalZeroSet_charbonnelClosure
    (by omega)

/-- The carrier has a literal-zero description of rank one. -/
theorem exists_rank_one_description
    (hG : IsGeometricFunctionFamily G)
    (certificate : CharbonnelSardianApproximationCertificate G order n A) :
    ∃ description :
        CharbonnelDescription (literalZeroSetFamily G)
          (n + (certificate.commonHiddenArity + 1)),
      description.carrier = certificate.family.carrier ∧
        description.rank = 1 :=
  certificate.family.exists_rank_one_description hG

/-- One derivative of the constituent equations makes the finite
approximating carrier Hausdorff-null and therefore interiorless. -/
theorem carrier_interior_eq_empty
    (certificate : CharbonnelSardianApproximationCertificate G order n A) :
    interior certificate.family.carrier = ∅ :=
  certificate.family.carrier_interior_eq_empty
    (Nat.ne_of_gt certificate.order_pos)

/-- A Sardian approximation certificate and the Charbonnel trace hypotheses
yield a closed empty-interior carrier containing the boundary of
`closure A`.  For closed `A`, this is the conclusion used in Wilkie's
Theorem 3.1. -/
theorem exists_closed_emptyInterior_boundaryCarrier
    (hG : IsGeometricFunctionFamily G)
    (htrace : CharbonnelApproximationTraceTameness
      (charbonnelClosure (literalZeroSetFamily G)))
    (certificate : CharbonnelSardianApproximationCertificate G order n A) :
    ∃ B : Set (RealEuclidean n),
      IsClosed B ∧
        B ∈ charbonnelClosure (literalZeroSetFamily G) n ∧
        interior B = ∅ ∧ frontier (closure A) ⊆ B := by
  exact certificate.approximates.exists_boundaryCarrier htrace
    certificate.family.visible_pos
    (certificate.carrier_mem_literalZeroSet_charbonnelClosure hG)
    certificate.carrier_interior_eq_empty

end CharbonnelSardianApproximationCertificate

end AbelFormalization
