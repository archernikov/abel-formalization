import AbelFormalization.CharbonnelSardianProjectionPaddedFamilyPrefixLift
import AbelFormalization.CharbonnelSardianCertificatePadding

/-!
# Assemble the from-below part of Wilkie's Sardian projection step

The mixed-depth projected family has the exact old-carrier prefix section
lift.  We use the already constructed successor modulus `appendUnit`, whose
last bound is the positive constant `1`.  Its initial bounded parameter
vector is precisely the prefix of the projected parameter vector.  Thus an
old approximation certificate supplies the from-below clause for the new
projected family without an additional carrier or modulus hypothesis.

The from-above boundary clause and its regular-value/minor analysis remain
separate obligations of Wilkie 3.10.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The parameter prefix in the projection reduction is exactly the
initial segment used by the recursive modulus. -/
@[simp]
theorem sardianProjectionParameterPrefix_eq_init {k : ℕ}
    (ε : RealEuclidean ((k + 1) + 1)) :
    sardianProjectionParameterPrefix ε = Fin.init ε :=
  rfl

namespace CharbonnelModulus

/-- The constant-unit successor bound implies all bounds of the old modulus
on the old parameter prefix. -/
theorem isBounded_appendUnit_sardianProjectionParameterPrefix
    {k : ℕ} (oldModulus : CharbonnelModulus k)
    (ε : RealEuclidean ((k + 1) + 1))
    (hε : oldModulus.appendUnit.IsBounded ε) :
    oldModulus.IsBounded (sardianProjectionParameterPrefix ε) := by
  have hinit :=
    ((isBounded_appendUnit_iff oldModulus ε).mp hε).1
  simpa only [sardianProjectionParameterPrefix_eq_init] using hinit

end CharbonnelModulus

/-- The old from-below clause passes to the assembled mixed-depth projected
Sardian family with the explicit constant-unit successor modulus. -/
theorem approximatesFromBelow_sardianProjectionAlgebraicPaddedFamily
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n K : ℕ} (hn : 0 < n)
    (A : Set (RealEuclidean (n + 1)))
    (oldFamily : CharbonnelFiniteSardianFamily G
      (order + 1) (n + 1) K)
    (oldModulus : CharbonnelModulus (K + 1))
    (hbelow : CharbonnelModulus.ApproximatesFromBelow
      oldModulus oldFamily.carrier (closure A)) :
    CharbonnelModulus.ApproximatesFromBelow
      oldModulus.appendUnit
      (sardianProjectionAlgebraicPaddedFamily
        hG hsmooth hderiv hn oldFamily).carrier
      (closure (realEuclideanExistentialProjection A)) := by
  exact approximatesFromBelow_projection_of_prefixSection
    A oldFamily.carrier
    (sardianProjectionAlgebraicPaddedFamily
      hG hsmooth hderiv hn oldFamily).carrier
    oldModulus oldModulus.appendUnit
    (fun ε hε ↦
      CharbonnelModulus.isBounded_appendUnit_sardianProjectionParameterPrefix
        oldModulus ε hε)
    (fun ε x hnew ↦
      sardianProjectionAlgebraicPaddedFamily_prefixSectionLift
        hG hsmooth hderiv hn oldFamily ε x hnew)
    hbelow

/-- An old Sardian certificate supplies the from-below half of the
projected family directly.  Its from-above certificate field is not used by
this elementary projection reduction. -/
theorem approximatesFromBelow_sardianProjectionAlgebraicPaddedFamily_of_certificate
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n : ℕ} (hn : 0 < n)
    {A : Set (RealEuclidean (n + 1))}
    (oldCertificate : CharbonnelSardianApproximationCertificate
      G (order + 1) (n + 1) A) :
    CharbonnelModulus.ApproximatesFromBelow
      oldCertificate.modulus.appendUnit
      (sardianProjectionAlgebraicPaddedFamily
        hG hsmooth hderiv hn oldCertificate.family).carrier
      (closure (realEuclideanExistentialProjection A)) :=
  approximatesFromBelow_sardianProjectionAlgebraicPaddedFamily
    hG hsmooth hderiv hn A oldCertificate.family
    oldCertificate.modulus
    oldCertificate.approximates.approximatesFromBelow

end AbelFormalization
