import AbelFormalization.FiniteAnalyticChangeOfGenerators

/-!
# Finite analytic changes in a nested polynomial ring

Ordered-cluster central transfer uses an outer polynomial ring whose
coefficients are themselves polynomials over analytic germs.  This module
flattens that nested ring along `MvPolynomial.sumAlgEquiv`, applies the
existing finite analytic change-of-generators construction, and evaluates
the resulting representatives with independent outer and coefficient-symbol
assignments.

Only the finite source, target, and change matrix are represented.  No
evaluation homomorphism on the full analytic-germ ring is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter
open scoped BigOperators Topology

universe u v w s t q

/-- Flatten an outer polynomial with polynomial coefficients into one
polynomial on the sum of the outer and coefficient variable types. -/
def nestedMvPolynomialFlatteningAlgEquiv
    (R : Type u) [CommSemiring R] (Outer : Type v) (Coeff : Type w) :
    MvPolynomial Outer (MvPolynomial Coeff R) ≃ₐ[R]
      MvPolynomial (Outer ⊕ Coeff) R :=
  (MvPolynomial.sumAlgEquiv R Outer Coeff).symm

/-- Finite analytic change data for nested polynomials, implemented by
flattening all three finite polynomial families simultaneously. -/
abbrev FiniteAnalyticNestedChangeOfGeneratorsData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Outer : Type v} {Coeff : Type w}
    {Source : Type s} {Target : Type t}
    [Fintype Source] [Fintype Target]
    (x : E)
    (source : Source →
      MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x)))
    (target : Target →
      MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x))) :=
  FiniteAnalyticChangeOfGeneratorsData x
    (fun a ↦ nestedMvPolynomialFlatteningAlgEquiv (AnalyticGermAt x)
      Outer Coeff (source a))
    (fun b ↦ nestedMvPolynomialFlatteningAlgEquiv (AnalyticGermAt x)
      Outer Coeff (target b))

/-- A nested finite span inclusion remains a span inclusion after flattening. -/
theorem nestedMvPolynomialFlattening_span_le
    {R : Type u} [CommRing R]
    {Outer : Type v} {Coeff : Type w}
    {Source : Type s} {Target : Type t}
    [Fintype Source] [Fintype Target]
    (source : Source → MvPolynomial Outer (MvPolynomial Coeff R))
    (target : Target → MvPolynomial Outer (MvPolynomial Coeff R))
    (hspan : Ideal.span (Set.range target) ≤
      Ideal.span (Set.range source)) :
    Ideal.span (Set.range (fun b ↦
        nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff (target b))) ≤
      Ideal.span (Set.range (fun a ↦
        nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff (source a))) := by
  let flatten := nestedMvPolynomialFlatteningAlgEquiv R Outer Coeff
  rw [show Ideal.span (Set.range (fun a ↦ flatten (source a))) =
      (Ideal.span (Set.range source)).map flatten.toRingHom by
    exact span_range_map_eq flatten.toRingHom source]
  apply Ideal.span_le.2
  rintro _ ⟨b, rfl⟩
  exact Ideal.mem_map_of_mem flatten.toRingHom
    (hspan Ideal.mem_span_range_self)

/-- Canonical finite analytic representatives for a nested span inclusion. -/
noncomputable def finiteAnalyticNestedChangeOfGeneratorsDataOfSpan
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Outer : Type v} {Coeff : Type w}
    {Source : Type s} {Target : Type t}
    [Fintype Source] [Fintype Target]
    (x : E)
    (source : Source →
      MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x)))
    (target : Target →
      MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x)))
    (hspan : Ideal.span (Set.range target) ≤
      Ideal.span (Set.range source)) :
    FiniteAnalyticNestedChangeOfGeneratorsData x source target :=
  finiteAnalyticChangeOfGeneratorsDataOfSpan x
    (fun a ↦ nestedMvPolynomialFlatteningAlgEquiv (AnalyticGermAt x)
      Outer Coeff (source a))
    (fun b ↦ nestedMvPolynomialFlatteningAlgEquiv (AnalyticGermAt x)
      Outer Coeff (target b))
    (nestedMvPolynomialFlattening_span_le source target hspan)

namespace FiniteAnalyticNestedChangeOfGeneratorsData

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Outer : Type v} {Coeff : Type w}
variable {Source : Type s} {Target : Type t}
variable [Fintype Source] [Fintype Target]
variable {x : E}
variable {source : Source →
  MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x))}
variable {target : Target →
  MvPolynomial Outer (MvPolynomial Coeff (AnalyticGermAt x))}

/-- Evaluate a flattened source representative under separate outer and
coefficient-symbol assignments. -/
def sourceValue
    (data : FiniteAnalyticNestedChangeOfGeneratorsData x source target)
    {X : Type q} (parameter : X → E)
    (outerValue : Outer → X → ℝ) (coefficientValue : Coeff → X → ℝ)
    (a : Source) (n : X) : ℝ :=
  FiniteAnalyticChangeOfGeneratorsData.sourceValue data parameter
    (Sum.elim outerValue coefficientValue) a n

/-- Evaluate a flattened target representative under separate outer and
coefficient-symbol assignments. -/
def targetValue
    (data : FiniteAnalyticNestedChangeOfGeneratorsData x source target)
    {X : Type q} (parameter : X → E)
    (outerValue : Outer → X → ℝ) (coefficientValue : Coeff → X → ℝ)
    (b : Target) (n : X) : ℝ :=
  FiniteAnalyticChangeOfGeneratorsData.targetValue data parameter
    (Sum.elim outerValue coefficientValue) b n

/-- Evaluate one entry of the flattened finite change matrix. -/
def changeCoefficientValue
    (data : FiniteAnalyticNestedChangeOfGeneratorsData x source target)
    {X : Type q} (parameter : X → E)
    (outerValue : Outer → X → ℝ) (coefficientValue : Coeff → X → ℝ)
    (b : Target) (a : Source) (n : X) : ℝ :=
  FiniteAnalyticChangeOfGeneratorsData.coefficientValue data parameter
    (Sum.elim outerValue coefficientValue) b a n

/-- Analyticity bounds every evaluated entry of the nested change matrix
from coordinatewise bounds for its two symbol families. -/
theorem changeCoefficientValue_hasPolynomialUpperBound
    (data : FiniteAnalyticNestedChangeOfGeneratorsData x source target)
    {X : Type (max v w)} {l : Filter X} {scale : X → ℝ}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (outerValue : Outer → X → ℝ) (coefficientValue : Coeff → X → ℝ)
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (houter : ∀ i, HasPolynomialUpperBound l scale (outerValue i))
    (hcoefficient : ∀ j,
      HasPolynomialUpperBound l scale (coefficientValue j))
    (b : Target) (a : Source) :
    HasPolynomialUpperBound l scale
      (data.changeCoefficientValue parameter outerValue coefficientValue b a) := by
  apply FiniteAnalyticChangeOfGeneratorsData.coefficientValue_hasPolynomialUpperBound
    data parameter hparameter
    (Sum.elim outerValue coefficientValue) hscale
  rintro (i | j)
  · exact houter i
  · exact hcoefficient j

/-- The flattened analytic identity evaluates eventually under arbitrary
moving outer and coefficient-symbol assignments. -/
theorem eventually_targetValue_eq_sum
    (data : FiniteAnalyticNestedChangeOfGeneratorsData x source target)
    {X : Type q} {l : Filter X}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (outerValue : Outer → X → ℝ) (coefficientValue : Coeff → X → ℝ) :
    ∀ᶠ n in l, ∀ b,
      data.targetValue parameter outerValue coefficientValue b n =
        ∑ a, data.changeCoefficientValue parameter outerValue
          coefficientValue b a n *
          data.sourceValue parameter outerValue coefficientValue a n := by
  exact FiniteAnalyticChangeOfGeneratorsData.eventually_targetValue_eq_sum
    data parameter hparameter
    (Sum.elim outerValue coefficientValue)

end FiniteAnalyticNestedChangeOfGeneratorsData
end AbelFormalization
