import AbelFormalization.ClusterAlgebraicReduction
import AbelFormalization.TerminalLocalizationIdentities
import AbelFormalization.LocalizationLowerBoundTransport
import AbelFormalization.TransferInitialCertificate

/-!
# Generator identities attached to a cluster certificate

The algebraic cluster certificate contains an ideal inclusion after
multiplication by one common power of the product of first derivative
variables.  This module specializes that inclusion to finite displayed
generating families and records its quantitative consequence under any
real-valued evaluation.
-/

noncomputable section

namespace AbelFormalization

open Filter
open scoped BigOperators

set_option autoImplicit false

universe u

/-- A terminalized cluster certificate gives literal identities for every
finite generating list of its retained time ideal and every finite generating
list of its terminal ideal. -/
theorem TerminalizedClusterCertificate.exists_generatorIdentities
    {R : Type u} [CommRing R]
    {h : Nat} {higher : Fin h → Nat}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    (certificate : TerminalizedClusterCertificate R h higher Q)
    {L J : Type*} [Fintype L] [Fintype J]
    (c : L → MvPolynomial (Fin h) R)
    (G : J → TerminalMultiblockSourceRing R h higher (Fin h))
    (hc : Ideal.span (Set.range c) = certificate.timeIdeal)
    (hG : Ideal.span (Set.range G) = certificate.terminalIdeal) :
    ∃ b : L → J → TerminalMultiblockSourceRing R h higher (Fin h),
      ∀ l,
        terminalFirstDerivativeProduct R (Fin h) h higher ^
              certificate.denominatorExponent *
            terminalMultiblockRetainedSourceHom R (Fin h) h higher (c l) =
          ∑ j, b l j * G j := by
  let retainedHom :=
    terminalMultiblockRetainedSourceHom R (Fin h) h higher
  have hcMap :
      Ideal.span (Set.range (fun l => retainedHom (c l))) =
        certificate.timeIdeal.map retainedHom := by
    rw [span_range_map_eq retainedHom c, hc]
  exact ideal_smul_le_exists_generator_identities
    (certificate.timeIdeal.map retainedHom)
    certificate.terminalIdeal
    (fun l => retainedHom (c l)) G
    (terminalFirstDerivativeProduct R (Fin h) h higher ^
      certificate.denominatorExponent)
    hcMap hG certificate.denominator_clears_time_extension

/-- Quantitative form of the cluster localization identities.  It is
parameterized by an arbitrary family of ring-homomorphic evaluations; later
analytic modules only have to provide bounds for coordinates and for fixed
polynomials under those evaluations. -/
theorem TerminalizedClusterCertificate.hasInversePowerLowerBound_terminalGenerators
    {R : Type u} [CommRing R]
    {h : Nat} {higher : Fin h → Nat}
    {Q : Ideal (CentralPolynomial R (Fin h)
      (terminalTotalDerivativeCount higher) (Fin h))}
    (certificate : TerminalizedClusterCertificate R h higher Q)
    {L J X : Type*} [Fintype L] [Nonempty L]
    [Fintype J] [Nonempty J]
    (c : L → MvPolynomial (Fin h) R)
    (G : J → TerminalMultiblockSourceRing R h higher (Fin h))
    (hc : Ideal.span (Set.range c) = certificate.timeIdeal)
    (hG : Ideal.span (Set.range G) = certificate.terminalIdeal)
    (eval : X →
      TerminalMultiblockSourceRing R h higher (Fin h) →+* ℝ)
    {l : Filter X} {S : X → ℝ}
    (hS : ∀ᶠ x in l, 1 ≤ S x)
    (hfirst : ∀ d : Fin h,
      HasScalarInversePowerLowerBound l S
        (fun x => eval x
          (MvPolynomial.X
            (Sum.inl ⟨d, (0 : Fin (higher d + 1))⟩))))
    (hcLower : HasInversePowerLowerBound l S
      (fun k x => eval x
        (terminalMultiblockRetainedSourceHom R (Fin h) h higher
          (c k))))
    (hpoly : ∀ P : TerminalMultiblockSourceRing R h higher (Fin h),
      HasPolynomialUpperBound l S (fun x => eval x P)) :
    HasInversePowerLowerBound l S (fun j x => eval x (G j)) := by
  obtain ⟨b, hb⟩ := certificate.exists_generatorIdentities c G hc hG
  apply hasInversePowerLowerBound_of_clearedLocalizationIdentities_of_finite
    (fun d x => eval x
      (MvPolynomial.X
        (Sum.inl ⟨d, (0 : Fin (higher d + 1))⟩)))
    certificate.denominatorExponent
    (fun k x => eval x
      (terminalMultiblockRetainedSourceHom R (Fin h) h higher (c k)))
    (fun j x => eval x (G j))
    (fun k j x => eval x (b k j)) hS hfirst hcLower
    (fun k j => hpoly (b k j))
  filter_upwards [] with x k
  have hid := congrArg (eval x) (hb k)
  simpa [terminalFirstDerivativeProduct_eq_prod] using hid

end AbelFormalization
