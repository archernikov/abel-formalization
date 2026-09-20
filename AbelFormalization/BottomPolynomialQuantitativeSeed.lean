import AbelFormalization.FiniteGeneratorSpanLowerBound
import AbelFormalization.OrderedClusterAlgebraicDescentTraceData
import AbelFormalization.PolynomialEventualLowerBound
import AbelFormalization.PolynomialExtraction
import AbelFormalization.RealQuantitativeTransferAssembly

/-!
# Quantitative seed from a scalar polynomial in a time ideal

The bottom-height argument produces a nonzero scalar univariate polynomial
inside a multivariate time ideal.  This file evaluates that embedded
polynomial, obtains its eventual lower bound, and transfers the bound through
span inclusion to an arbitrary padded finite presentation of the time ideal.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped Polynomial Topology

universe u v

/-- Evaluating the scalar polynomial embedded in coordinate `i` is ordinary
univariate evaluation at that coordinate, whenever the coefficient map fixes
the ground real scalars. -/
theorem eval₂Hom_scalarUnivariateEmbedding
    {R : Type u} [CommRing R] [Algebra ℝ R]
    {X : Type v} {d : ℕ}
    (coefficientEval : R →+* (X → ℝ))
    (timeValue : Fin d → X → ℝ)
    (hscalar : ∀ r x, coefficientEval (algebraMap ℝ R r) x = r)
    (i : Fin d) (P : ℝ[X]) (x : X) :
    MvPolynomial.eval₂Hom coefficientEval timeValue
        (scalarUnivariateEmbedding ℝ R i P) x =
      P.eval (timeValue i x) := by
  let coefficientAt : R →+* ℝ :=
    (Pi.evalRingHom (fun _ : X ↦ ℝ) x).comp coefficientEval
  have hcomp : coefficientAt.comp (algebraMap ℝ R) = RingHom.id ℝ := by
    ext r
    exact hscalar r x
  rw [mvPolynomial_eval₂Hom_pi_apply]
  change MvPolynomial.eval₂Hom coefficientAt (fun j ↦ timeValue j x)
      (scalarUnivariateEmbedding ℝ R i P) = _
  rw [scalarUnivariateEmbedding, RingHom.comp_apply,
    MvPolynomial.eval₂Hom_map_hom, hcomp]
  change MvPolynomial.eval (fun j ↦ timeValue j x)
      (P.toMvPolynomial i) = _
  exact MvPolynomial.eval_toMvPolynomial (fun j ↦ timeValue j x) i P

namespace RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily

/-- A padded generating family of a time ideal inherits the lower bound of
any nonzero scalar univariate polynomial contained in that ideal. -/
theorem lower_of_scalarUnivariateEmbedding_mem
    {R : Type u} [CommRing R] [Algebra ℝ R]
    {X : Type v} {d : ℕ} {l : Filter X} {scale : X → ℝ}
    {I : Ideal (MvPolynomial (Fin d) R)}
    (family : RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
      (MvPolynomial (Fin d) R) I)
    (coefficientEval : R →+* (X → ℝ))
    (timeValue : Fin d → X → ℝ)
    (hscalar : ∀ r x, coefficientEval (algebraMap ℝ R r) x = r)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hcoefficient : ∀ r : R,
      HasPolynomialUpperBound l scale (coefficientEval r))
    (hcoordinate : ∀ i : Fin d,
      HasPolynomialUpperBound l scale (timeValue i))
    (i : Fin d) (P : ℝ[X]) (hP : P ≠ 0)
    (htime : Tendsto (timeValue i) l atTop)
    (hmem : scalarUnivariateEmbedding ℝ R i P ∈ I) :
    HasInversePowerLowerBound l scale
      (fun k x ↦ MvPolynomial.eval₂Hom coefficientEval timeValue
        (family.generator k) x) := by
  let target : Fin 1 → MvPolynomial (Fin d) R :=
    fun _ ↦ scalarUnivariateEmbedding ℝ R i P
  have htargetSpan : Ideal.span (Set.range target) ≤
      Ideal.span (Set.range family.generator) := by
    apply Ideal.span_le.2
    rintro q ⟨k, rfl⟩
    rw [family.span_eq]
    exact hmem
  have htarget : HasInversePowerLowerBound l scale
      (fun k x ↦ MvPolynomial.eval₂Hom coefficientEval timeValue
        (target k) x) := by
    have heq :
        (fun k x ↦ MvPolynomial.eval₂Hom coefficientEval timeValue
          (target k) x) =
        (fun _ : Fin 1 ↦ fun x ↦ P.eval (timeValue i x)) := by
      funext k x
      exact eval₂Hom_scalarUnivariateEmbedding coefficientEval timeValue
        hscalar i P x
    rw [heq]
    exact nonzeroPolynomial_hasInversePowerLowerBound P hP htime scale
  exact hasInversePowerLowerBound_mvPolynomial_eval₂Hom_of_span_le
    family.generator target coefficientEval timeValue hscale hcoefficient
      hcoordinate htargetSpan htarget

/-- Witness-producing form of
`lower_of_scalarUnivariateEmbedding_mem`, ready to initialize a dependent
boundary trace. -/
noncomputable def evaluatedLowerBound_of_scalarUnivariateEmbedding_mem
    {R : Type u} [CommRing R] [Algebra ℝ R]
    {X : Type v} {d : ℕ} {l : Filter X} {scale : X → ℝ}
    {I : Ideal (MvPolynomial (Fin d) R)}
    (family : RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
      (MvPolynomial (Fin d) R) I)
    (coefficientEval : R →+* (X → ℝ))
    (timeValue : Fin d → X → ℝ)
    (hscalar : ∀ r x, coefficientEval (algebraMap ℝ R r) x = r)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hcoefficient : ∀ r : R,
      HasPolynomialUpperBound l scale (coefficientEval r))
    (hcoordinate : ∀ i : Fin d,
      HasPolynomialUpperBound l scale (timeValue i))
    (i : Fin d) (P : ℝ[X]) (hP : P ≠ 0)
    (htime : Tendsto (timeValue i) l atTop)
    (hmem : scalarUnivariateEmbedding ℝ R i P ∈ I) :
    EvaluatedPaddedIdealLowerBound (Fin d) l scale coefficientEval
      timeValue I :=
  {
    count := family.count
    generator := family.generator
    span_eq := family.span_eq
    lower := family.lower_of_scalarUnivariateEmbedding_mem coefficientEval
      timeValue hscalar hscale hcoefficient hcoordinate i P hP htime hmem
  }

end RepresentativeClusterSubsequence.PaddedIdealGeneratorFamily
end AbelFormalization
