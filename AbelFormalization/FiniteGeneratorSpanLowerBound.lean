import AbelFormalization.TransferCoefficientBounds

/-!
# Quantitative transfer between finite generating families

Two neighboring algebraic operations may display different finite families
for the same boundary ideal.  Membership in a finite span supplies a fixed
change-of-generators matrix.  If evaluation of every ring coefficient is
polynomially bounded, the existing finite linear-combination estimate moves
an inverse-power lower bound across that boundary.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open Filter Set
open scoped Topology

universe u v

/-- A lower bound for an evaluated finite family transfers to any finite
family whose span contains it, provided every scalar coefficient has a
polynomial upper bound at the same scale. -/
theorem hasInversePowerLowerBound_eval_of_span_le
    {R : Type u} [CommRing R]
    {X : Type v} {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    {l : Filter X} {scale : X → ℝ}
    (source : ι → R) (target : κ → R)
    (eval : X → R →+* ℝ)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hcoefficient : ∀ r : R,
      HasPolynomialUpperBound l scale (fun x ↦ eval x r))
    (hspan : Ideal.span (Set.range target) ≤
      Ideal.span (Set.range source))
    (htarget : HasInversePowerLowerBound l scale
      (fun k x ↦ eval x (target k))) :
    HasInversePowerLowerBound l scale
      (fun i x ↦ eval x (source i)) := by
  classical
  have hmem : ∀ k, target k ∈ Ideal.span (Set.range source) := by
    intro k
    exact hspan Ideal.mem_span_range_self
  choose coefficient hcoefficientIdentity using fun k ↦
    Ideal.mem_span_range_iff_exists_fun.mp (hmem k)
  let evaluatedCoefficient : κ → ι → X → ℝ :=
    fun k i x ↦ eval x (coefficient k i)
  have hcoefficientBound : HasUniformPolynomialUpperBound l scale
      evaluatedCoefficient := by
    apply hasUniformPolynomialUpperBound_of_finite
      evaluatedCoefficient hscale
    intro k i
    exact hcoefficient (coefficient k i)
  have hidentity : ∀ᶠ x in l, ∀ k,
      eval x (target k) =
        ∑ i, evaluatedCoefficient k i x * eval x (source i) := by
    apply Filter.Eventually.of_forall
    intro x k
    calc
      eval x (target k) = eval x (∑ i, coefficient k i * source i) :=
        congrArg (eval x) (hcoefficientIdentity k).symm
      _ = ∑ i, evaluatedCoefficient k i x * eval x (source i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_mul]
  exact hasInversePowerLowerBound_of_linearCombinations
    (fun i x ↦ eval x (source i))
    (fun k x ↦ eval x (target k))
    evaluatedCoefficient hscale hidentity hcoefficientBound htarget

/-- In particular, inverse-power lower bounds can be transported in either
direction between evaluated finite generating families of the same ideal. -/
theorem hasInversePowerLowerBound_eval_of_span_eq
    {R : Type u} [CommRing R]
    {X : Type v} {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    {l : Filter X} {scale : X → ℝ}
    (source : ι → R) (target : κ → R)
    (eval : X → R →+* ℝ)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hcoefficient : ∀ r : R,
      HasPolynomialUpperBound l scale (fun x ↦ eval x r))
    (hspan : Ideal.span (Set.range source) =
      Ideal.span (Set.range target))
    (htarget : HasInversePowerLowerBound l scale
      (fun k x ↦ eval x (target k))) :
    HasInversePowerLowerBound l scale
      (fun i x ↦ eval x (source i)) := by
  exact hasInversePowerLowerBound_eval_of_span_le source target eval
    hscale hcoefficient hspan.ge htarget

/-- Fixed multivariate-polynomial evaluation supplies the coefficient bounds
needed by `hasInversePowerLowerBound_eval_of_span_le` from bounds on the
ground ring and on every coordinate. -/
theorem hasInversePowerLowerBound_mvPolynomial_eval₂Hom_of_span_le
    {R : Type u} [CommRing R]
    {X : Type v} {σ ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    {l : Filter X} {scale : X → ℝ}
    (source : ι → MvPolynomial σ R)
    (target : κ → MvPolynomial σ R)
    (coefficientEval : R →+* (X → ℝ))
    (coordinateValue : σ → X → ℝ)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hcoefficient : ∀ r : R,
      HasPolynomialUpperBound l scale (coefficientEval r))
    (hcoordinate : ∀ z : σ,
      HasPolynomialUpperBound l scale (coordinateValue z))
    (hspan : Ideal.span (Set.range target) ≤
      Ideal.span (Set.range source))
    (htarget : HasInversePowerLowerBound l scale
      (fun k x ↦ MvPolynomial.eval₂Hom coefficientEval coordinateValue
        (target k) x)) :
    HasInversePowerLowerBound l scale
      (fun i x ↦ MvPolynomial.eval₂Hom coefficientEval coordinateValue
        (source i) x) := by
  let eval : X → MvPolynomial σ R →+* ℝ := fun x ↦
    (Pi.evalRingHom (fun _ : X ↦ ℝ) x).comp
      (MvPolynomial.eval₂Hom coefficientEval coordinateValue)
  have hevalCoefficient : ∀ P : MvPolynomial σ R,
      HasPolynomialUpperBound l scale (fun x ↦ eval x P) := by
    intro P
    apply (mvPolynomial_eval₂Hom_hasPolynomialUpperBound hscale
      coefficientEval coordinateValue hcoefficient hcoordinate P).congr
    intro x
    rfl
  exact hasInversePowerLowerBound_eval_of_span_le source target eval
    hscale hevalCoefficient hspan htarget

/-- Equality-of-spans form of the fixed-polynomial evaluation bridge. -/
theorem hasInversePowerLowerBound_mvPolynomial_eval₂Hom_of_span_eq
    {R : Type u} [CommRing R]
    {X : Type v} {σ ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    {l : Filter X} {scale : X → ℝ}
    (source : ι → MvPolynomial σ R)
    (target : κ → MvPolynomial σ R)
    (coefficientEval : R →+* (X → ℝ))
    (coordinateValue : σ → X → ℝ)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hcoefficient : ∀ r : R,
      HasPolynomialUpperBound l scale (coefficientEval r))
    (hcoordinate : ∀ z : σ,
      HasPolynomialUpperBound l scale (coordinateValue z))
    (hspan : Ideal.span (Set.range source) =
      Ideal.span (Set.range target))
    (htarget : HasInversePowerLowerBound l scale
      (fun k x ↦ MvPolynomial.eval₂Hom coefficientEval coordinateValue
        (target k) x)) :
    HasInversePowerLowerBound l scale
      (fun i x ↦ MvPolynomial.eval₂Hom coefficientEval coordinateValue
        (source i) x) := by
  exact hasInversePowerLowerBound_mvPolynomial_eval₂Hom_of_span_le
    source target coefficientEval coordinateValue hscale hcoefficient
      hcoordinate hspan.ge htarget

/-- An ideal together with one padded finite generating family whose
evaluation has an inverse-power lower bound.  Existentially packaging the
family lets neighboring operations use different generator counts. -/
structure EvaluatedPaddedIdealLowerBound
    {R : Type u} [CommRing R] {X : Type v} (σ : Type*)
    (l : Filter X) (scale : X → ℝ)
    (coefficientEval : R →+* (X → ℝ))
    (coordinateValue : σ → X → ℝ)
    (I : Ideal (MvPolynomial σ R)) where
  count : ℕ
  generator : Fin (count + 1) → MvPolynomial σ R
  span_eq : Ideal.span (Set.range generator) = I
  lower : HasInversePowerLowerBound l scale
    (fun k x ↦ MvPolynomial.eval₂Hom coefficientEval coordinateValue
      (generator k) x)

namespace EvaluatedPaddedIdealLowerBound

/-- Any other padded finite family spanning the packaged ideal inherits the
lower bound under the standard coefficient and coordinate bounds. -/
theorem lower_of_span_eq
    {R : Type u} [CommRing R] {X : Type v} {σ : Type*}
    {l : Filter X} {scale : X → ℝ}
    {coefficientEval : R →+* (X → ℝ)}
    {coordinateValue : σ → X → ℝ}
    {I : Ideal (MvPolynomial σ R)}
    (data : EvaluatedPaddedIdealLowerBound σ l scale coefficientEval
      coordinateValue I)
    {c : ℕ} (generator : Fin (c + 1) → MvPolynomial σ R)
    (hspan : Ideal.span (Set.range generator) = I)
    (hscale : ∀ᶠ x in l, 1 ≤ scale x)
    (hcoefficient : ∀ r : R,
      HasPolynomialUpperBound l scale (coefficientEval r))
    (hcoordinate : ∀ z : σ,
      HasPolynomialUpperBound l scale (coordinateValue z)) :
    HasInversePowerLowerBound l scale
      (fun k x ↦ MvPolynomial.eval₂Hom coefficientEval coordinateValue
        (generator k) x) := by
  exact hasInversePowerLowerBound_mvPolynomial_eval₂Hom_of_span_eq
    generator data.generator coefficientEval coordinateValue hscale
      hcoefficient hcoordinate (hspan.trans data.span_eq.symm) data.lower

end EvaluatedPaddedIdealLowerBound

end AbelFormalization
