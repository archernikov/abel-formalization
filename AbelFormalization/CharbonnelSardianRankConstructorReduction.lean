import AbelFormalization.CharbonnelSardianCertificatePadding
import AbelFormalization.CharbonnelComplementPipeline

/-!
# Constructor reduction for the Sardian approximation rank step

Wilkie's condition 3.6 refers to `closure A` in both approximation clauses.
Consequently, a certificate for `A` is already a certificate for `closure A`.
His Lemma 3.7 combines certificates for a union; the preceding module pads
their independently chosen hidden depths before that union.  These two
description constructors therefore need no additional analytic rank premise.

The remaining source inputs are stated at their actual constructors.  The
literal-zero base is Wilkie 3.8.  The projection input is Wilkie 3.10;
projecting away `q` coordinates budgets `q` extra differentiability orders
from the lower-rank certificate because each one-coordinate critical-value
branch appends Jacobian minors.  The integer-
affine input is the nonlocal part of 3.13, based on the frontier-hyperplane
slice of 3.12 and lower-rank replacement descriptions.  It retains the full
lower-rank hypothesis rather than pretending that an arbitrary affine cut
can be made from the operand certificate alone.

No inhabitant of any of the three remaining inputs is asserted here.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

namespace CharbonnelModulus

/-- The asymmetric clauses of condition 3.6 depend only on the closure of
the target. -/
theorem IsClosureBoundaryApproximation.topologicalClosure
    {n k : ℕ} {modulus : CharbonnelModulus k}
    {T : Set (RealEuclidean (n + k))}
    {A : Set (RealEuclidean n)}
    (h : IsClosureBoundaryApproximation modulus T A) :
    IsClosureBoundaryApproximation modulus T (closure A) := by
  simpa only [IsClosureBoundaryApproximation, closure_closure] using h

end CharbonnelModulus

namespace CharbonnelSardianApproximationCertificate

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n : ℕ} {A B : Set (RealEuclidean n)}

/-- Closure of the target keeps the same finite Sardian family and modulus.
This is the semantic closure constructor in condition 3.6. -/
def topologicalClosure
    (certificate : CharbonnelSardianApproximationCertificate G order n A) :
    CharbonnelSardianApproximationCertificate G order n (closure A) :=
  { order_pos := certificate.order_pos
    commonHiddenArity := certificate.commonHiddenArity
    family := certificate.family
    modulus := certificate.modulus
    approximates := certificate.approximates.topologicalClosure }

end CharbonnelSardianApproximationCertificate

namespace CharbonnelDescription

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {n : ℕ}

/-- Wilkie 3.7: two descriptions whose carriers have Sardian certificates
have certificates for the union, even when their hidden depths differ. -/
theorem HasSardianApproximations.union
    {left right : CharbonnelDescription (literalZeroSetFamily G) n}
    (hleft : left.HasSardianApproximations G)
    (hright : right.HasSardianApproximations G) :
    (CharbonnelDescription.union left right).HasSardianApproximations G := by
  intro order horder
  obtain ⟨leftCertificate⟩ := hleft order horder
  obtain ⟨rightCertificate⟩ := hright order horder
  exact ⟨leftCertificate.unionOfAnyHiddenArity rightCertificate⟩

/-- The rank-four topological-closure constructor requires no new analytic
certificate: condition 3.6 is already about the closure of the target. -/
theorem HasSardianApproximations.topologicalClosure
    {inner : CharbonnelDescription (literalZeroSetFamily G) n}
    (hinner : inner.HasSardianApproximations G) :
    (CharbonnelDescription.topologicalClosure inner).HasSardianApproximations G := by
  intro order horder
  obtain ⟨certificate⟩ := hinner order horder
  exact ⟨certificate.topologicalClosure⟩

end CharbonnelDescription

/-! ## The three remaining source constructors -/

/-- The literal-zero rank-zero case of Wilkie 3.8, specialized to equations
in the chosen function family.  The premise must eventually build the
finite Sardian constituent and nested modulus used in that lemma. -/
def CharbonnelSardianLiteralZeroBaseInput
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  ∀ {n : ℕ}, 0 < n →
    ∀ (f : RealEuclideanFunction n), f ∈ G n →
      ∀ order : ℕ, 0 < order →
        Nonempty (CharbonnelSardianApproximationCertificate
          G order n {x | f x = 0})

/-- The positive-hidden-arity projection constructor of Wilkie 3.10.  The
`q` extra input orders budget one Jacobian-minor differentiation for each
erased coordinate.  Projection with `q = 0` is already the identity and is
discharged in the rank assembly below.

To establish this premise for a concrete `G`, the source argument needs
coordinate derivative closure of `G`, avoidance of singular values by a
nested modulus, and the regular-fiber escape-or-critical boundary-hit lemma.
The geometric-family properties alone do not supply derivative closure. -/
def CharbonnelSardianProjectionConstructorInput
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  ∀ {n q order : ℕ} (hn : 0 < n) (hq : 0 < q)
    {A : Set (RealEuclidean (n + q))}, 0 < order →
      CharbonnelSardianApproximationCertificate G (order + q) (n + q) A →
        Nonempty (CharbonnelSardianApproximationCertificate
          G order n (realEuclideanExistentialProjection A))

/-- The integer-affine description branch of Wilkie 3.13.  Its hyperplane
slice argument invokes lower-rank replacement descriptions which can have
different ambient arities, so the premise carries the full strong-induction
hypothesis.  This is deliberately a nonlocal branch input, rather than an
unsupported certificate-level affine-intersection operator. -/
def CharbonnelSardianIntegerAffineRankInput
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  ∀ r : ℕ,
    (∀ {m : ℕ}
      (lower : CharbonnelDescription (literalZeroSetFamily G) m),
        lower.rank < r → lower.HasSardianApproximations G) →
    ∀ {n : ℕ}
      (inner : CharbonnelDescription (literalZeroSetFamily G) n)
      (L : Set (RealEuclidean n)) (hL : IsIntegerAffineSet L),
        (CharbonnelDescription.integerAffineInter inner L hL).rank = r →
          (CharbonnelDescription.integerAffineInter inner L hL).HasSardianApproximations G

/-! ## Numeric rank assembly with union and closure discharged -/

/-- Wilkie's general rank step follows from the three explicit source
constructor inputs.  Binary union and target closure are proved above;
projection uses the lower-rank certificate with `q` extra derivatives. -/
theorem charbonnelSardianApproximationRankStep_of_constructorInputs
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hbase : CharbonnelSardianLiteralZeroBaseInput G)
    (hprojection : CharbonnelSardianProjectionConstructorInput G)
    (haffine : CharbonnelSardianIntegerAffineRankInput G) :
    CharbonnelSardianApproximationRankStep G := by
  intro r ih n description hrank
  cases description with
  | base hn A hA =>
      obtain ⟨f, hf, rfl⟩ := hA
      intro order horder
      exact hbase hn f hf order horder
  | union left right =>
      have hleftRank : left.rank < r := by
        simp only [CharbonnelDescription.rank_union] at hrank
        omega
      have hrightRank : right.rank < r := by
        simp only [CharbonnelDescription.rank_union] at hrank
        omega
      exact (ih left hleftRank).union (ih right hrightRank)
  | integerAffineInter inner L hL =>
      exact haffine r ih inner L hL hrank
  | @projection visible hidden hvisible inner =>
      have hinnerRank : inner.rank < r := by
        simp only [CharbonnelDescription.rank_projection] at hrank
        omega
      intro order horder
      by_cases hhidden : 0 < hidden
      · obtain ⟨certificate⟩ :=
          (ih inner hinnerRank) (order + hidden) (by omega)
        exact hprojection hvisible hhidden horder certificate
      · have hzero : hidden = 0 := by omega
        subst hidden
        have hinner := (ih inner hinnerRank) order horder
        simpa only [Nat.add_zero, CharbonnelDescription.carrier_projection,
          realEuclideanExistentialProjection_zero] using hinner
  | topologicalClosure inner =>
      have hinnerRank : inner.rank < r := by
        simp only [CharbonnelDescription.rank_topologicalClosure] at hrank
        omega
      exact (ih inner hinnerRank).topologicalClosure

/-- The corresponding all-description result uses the already proved
strong-induction skeleton in `CharbonnelComplementPipeline`. -/
theorem CharbonnelDescription.hasSardianApproximations_of_constructorInputs
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hbase : CharbonnelSardianLiteralZeroBaseInput G)
    (hprojection : CharbonnelSardianProjectionConstructorInput G)
    (haffine : CharbonnelSardianIntegerAffineRankInput G)
    {n : ℕ}
    (description : CharbonnelDescription (literalZeroSetFamily G) n) :
    description.HasSardianApproximations G :=
  description.hasSardianApproximations_of_rankStep
    (charbonnelSardianApproximationRankStep_of_constructorInputs
      hbase hprojection haffine)

/-- With the trace input from section 5, the reduced rank constructors give
the closed empty-interior boundary carriers used before Wilkie's separate
cell-decomposition argument. -/
theorem literalZeroSet_charbonnelClosure_closedBoundaryCarrierProperty_of_constructorInputs
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (htrace : CharbonnelApproximationTraceTameness
      (charbonnelClosure (literalZeroSetFamily G)))
    (hbase : CharbonnelSardianLiteralZeroBaseInput G)
    (hprojection : CharbonnelSardianProjectionConstructorInput G)
    (haffine : CharbonnelSardianIntegerAffineRankInput G) :
    CharbonnelClosedBoundaryCarrierProperty G :=
  literalZeroSet_charbonnelClosure_closedBoundaryCarrierProperty
    hG htrace
    (charbonnelSardianApproximationRankStep_of_constructorInputs
      hbase hprojection haffine)

end AbelFormalization
