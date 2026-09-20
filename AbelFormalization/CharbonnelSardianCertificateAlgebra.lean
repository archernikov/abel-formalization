import AbelFormalization.CharbonnelSardianApproximationCertificate

/-!
# Algebra of Sardian approximation certificates

Wilkie's Lemma 3.7 combines finitely many approximations after first padding
them to one parameter depth and shrinking their moduli to a common refinement.
This file proves the part of that construction which starts once the depths
are already equal.  The remaining padding operation is kept separate: it has
dependent parameter indices and is needed only to turn independently chosen
certificates into equal-depth certificates.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

namespace CharbonnelFiniteSardianFamily

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n K : ℕ}

/-- Concatenate two finite Sardian families which already use the same
visible arity, differentiability order, and common parameter depth. -/
def union
    (left right : CharbonnelFiniteSardianFamily G order n K) :
    CharbonnelFiniteSardianFamily G order n K :=
  ⟨left.visible_pos, left.constituents ++ right.constituents⟩

@[simp]
theorem carrier_union
    (left right : CharbonnelFiniteSardianFamily G order n K) :
    (left.union right).carrier = left.carrier ∪ right.carrier := by
  ext v
  simp only [carrier, union, List.mem_append, mem_union]
  constructor
  · rintro ⟨piece, hleft | hright, hv⟩
    · exact Or.inl ⟨piece, hleft, hv⟩
    · exact Or.inr ⟨piece, hright, hv⟩
  · rintro (⟨piece, hpiece, hv⟩ | ⟨piece, hpiece, hv⟩)
    · exact ⟨piece, Or.inl hpiece, hv⟩
    · exact ⟨piece, Or.inr hpiece, hv⟩

end CharbonnelFiniteSardianFamily

namespace CharbonnelSardianApproximationCertificate

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n : ℕ} {A B : Set (RealEuclidean n)}

/-- The data of a Sardian approximation certificate with its common hidden
arity exposed as an index.  This indexed view lets certificates be transported
to a common depth without dependent elimination on two structure projections.
-/
structure AtHiddenArity
    (G : (d : ℕ) → Set (RealEuclideanFunction d))
    (order n : ℕ) (A : Set (RealEuclidean n)) (K : ℕ) where
  order_pos : 0 < order
  family : CharbonnelFiniteSardianFamily G order n K
  modulus : CharbonnelModulus (K + 1)
  approximates :
    CharbonnelModulus.IsClosureBoundaryApproximation
      modulus family.carrier A

/-- Expose the hidden-arity field of a certificate as a type index. -/
def toAtHiddenArity
    (certificate : CharbonnelSardianApproximationCertificate G order n A) :
    AtHiddenArity G order n A certificate.commonHiddenArity :=
  { order_pos := certificate.order_pos
    family := certificate.family
    modulus := certificate.modulus
    approximates := certificate.approximates }

/-- Forget the explicit hidden-arity index. -/
def AtHiddenArity.toCertificate {K : ℕ}
    (certificate : AtHiddenArity G order n A K) :
    CharbonnelSardianApproximationCertificate G order n A :=
  { order_pos := certificate.order_pos
    commonHiddenArity := K
    family := certificate.family
    modulus := certificate.modulus
    approximates := certificate.approximates }

/-- Equal-depth indexed certificates combine by concatenating their finite
families and taking the infimum of their moduli. -/
def AtHiddenArity.union {K : ℕ}
    (left : AtHiddenArity G order n A K)
    (right : AtHiddenArity G order n B K) :
    AtHiddenArity G order n (A ∪ B) K := by
  let family := left.family.union right.family
  let modulus := CharbonnelModulus.infimum left.modulus right.modulus
  refine
    { order_pos := left.order_pos
      family := family
      modulus := modulus
      approximates := ?_ }
  rw [show family.carrier = left.family.carrier ∪ right.family.carrier by
    exact CharbonnelFiniteSardianFamily.carrier_union left.family right.family]
  exact
    (left.approximates.mono_modulus
      (CharbonnelModulus.infimum_refines_left
        left.modulus right.modulus)).union
      (right.approximates.mono_modulus
        (CharbonnelModulus.infimum_refines_right
          left.modulus right.modulus))

/-- Two Sardian approximation certificates of the same parameter depth
combine to a certificate for the union.  Their moduli are replaced by their
pointwise infimum, exactly as in the common-modulus step of Wilkie 3.7. -/
def unionOfSameHiddenArity
    (left : CharbonnelSardianApproximationCertificate G order n A)
    (right : CharbonnelSardianApproximationCertificate G order n B)
    (hhidden : left.commonHiddenArity = right.commonHiddenArity) :
    CharbonnelSardianApproximationCertificate G order n (A ∪ B) :=
  let rightAtLeft :
      AtHiddenArity G order n B left.commonHiddenArity :=
    hhidden.symm ▸ right.toAtHiddenArity
  (left.toAtHiddenArity.union rightAtLeft).toCertificate

end CharbonnelSardianApproximationCertificate

end AbelFormalization
