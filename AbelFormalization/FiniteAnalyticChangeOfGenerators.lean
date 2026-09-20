import AbelFormalization.AnalyticPolynomialEvaluationBounds
import AbelFormalization.PolynomialGermIdentities
import AbelFormalization.TransferFiniteBounds
import Mathlib.RingTheory.Ideal.Operations

/-!
# Finite analytic change of generators

A finite span inclusion between polynomial families over analytic germs gives
a finite coefficient matrix.  This module chooses that matrix, chooses actual
polynomial-valued analytic representatives for every source, target, and
coefficient polynomial at once, and shrinks to one neighborhood on which all
change-of-generators identities hold literally.

The resulting identities may be evaluated under every assignment of the
independent polynomial symbols.  The final section evaluates them along a
convergent parameter family, derives uniform coefficient bounds, and performs
numeric lower-bound transport.  Applications do not need a ring homomorphism
evaluating every analytic germ along a sequence.
-/

noncomputable section
set_option autoImplicit false

open Filter Set
open scoped BigOperators Topology

namespace AbelFormalization

universe u v w z

/-- A finite analytic change of generators together with simultaneous actual
representatives on one common neighborhood.

The three support and analyticity fields make the representatives directly
usable by fixed-support polynomial evaluation bounds.  `polynomial_identity`
and `evaluation_identity` are pointwise statements on the same neighborhood;
the assignment in the latter is completely arbitrary.
-/
structure FiniteAnalyticChangeOfGeneratorsData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {Source : Type w} {Target : Type z}
    [Fintype Source] [Fintype Target]
    (x : E)
    (source : Source → MvPolynomial ι (AnalyticGermAt x))
    (target : Target → MvPolynomial ι (AnalyticGermAt x)) where
  coefficient : Target → Source → MvPolynomial ι (AnalyticGermAt x)
  germ_identity : ∀ t,
    target t = ∑ s, coefficient t s * source s
  sourceRepresentative : Source → E → MvPolynomial ι ℝ
  targetRepresentative : Target → E → MvPolynomial ι ℝ
  coefficientRepresentative : Target → Source → E → MvPolynomial ι ℝ
  neighborhood : Set E
  neighborhood_open : IsOpen neighborhood
  base_mem : x ∈ neighborhood
  source_support_subset : ∀ s y,
    (sourceRepresentative s y).support ⊆ (source s).support
  target_support_subset : ∀ t y,
    (targetRepresentative t y).support ⊆ (target t).support
  coefficient_support_subset : ∀ t s y,
    (coefficientRepresentative t s y).support ⊆
      (coefficient t s).support
  source_coefficient_analytic : ∀ s e,
    AnalyticOnNhd ℝ (fun y ↦ (sourceRepresentative s y).coeff e)
      neighborhood
  target_coefficient_analytic : ∀ t e,
    AnalyticOnNhd ℝ (fun y ↦ (targetRepresentative t y).coeff e)
      neighborhood
  coefficient_coefficient_analytic : ∀ t s e,
    AnalyticOnNhd ℝ (fun y ↦
      (coefficientRepresentative t s y).coeff e) neighborhood
  source_germ_eq : ∀ s,
    analyticPolynomialGermHom x (source s) =
      (sourceRepresentative s : Germ (𝓝 x) (MvPolynomial ι ℝ))
  target_germ_eq : ∀ t,
    analyticPolynomialGermHom x (target t) =
      (targetRepresentative t : Germ (𝓝 x) (MvPolynomial ι ℝ))
  coefficient_germ_eq : ∀ t s,
    analyticPolynomialGermHom x (coefficient t s) =
      (coefficientRepresentative t s :
        Germ (𝓝 x) (MvPolynomial ι ℝ))
  polynomial_identity : ∀ y ∈ neighborhood, ∀ t,
    targetRepresentative t y =
      ∑ s, coefficientRepresentative t s y * sourceRepresentative s y
  evaluation_identity : ∀ y ∈ neighborhood, ∀ t, ∀ assignment : ι → ℝ,
    MvPolynomial.eval assignment (targetRepresentative t y) =
      ∑ s, MvPolynomial.eval assignment
          (coefficientRepresentative t s y) *
        MvPolynomial.eval assignment (sourceRepresentative s y)

/-- Every finite span inclusion over analytic-germ coefficients admits a
finite analytic change-of-generators adapter.

All representatives are selected in one invocation of
`exists_analyticPolynomialRepresentatives`.  A second finite-neighborhood
step makes every algebraic identity literal before any assignment of the
polynomial symbols is chosen.
-/
theorem nonempty_finiteAnalyticChangeOfGeneratorsData
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {Source : Type w} {Target : Type z}
    [Fintype Source] [Fintype Target]
    (x : E)
    (source : Source → MvPolynomial ι (AnalyticGermAt x))
    (target : Target → MvPolynomial ι (AnalyticGermAt x))
    (hspan : Ideal.span (Set.range target) ≤
      Ideal.span (Set.range source)) :
    Nonempty (FiniteAnalyticChangeOfGeneratorsData x source target) := by
  classical
  have htarget : ∀ t, target t ∈ Ideal.span (Set.range source) := by
    intro t
    exact hspan Ideal.mem_span_range_self
  choose coefficient hcoefficient using fun t ↦
    Ideal.mem_span_range_iff_exists_fun.mp (htarget t)
  have hgermIdentity : ∀ t,
      target t = ∑ s, coefficient t s * source s := by
    intro t
    exact (hcoefficient t).symm
  let polynomial : Source ⊕ Target ⊕ (Target × Source) →
      MvPolynomial ι (AnalyticGermAt x) := fun k ↦
    match k with
    | Sum.inl s => source s
    | Sum.inr (Sum.inl t) => target t
    | Sum.inr (Sum.inr ts) => coefficient ts.1 ts.2
  obtain ⟨representative, U, hUopen, hxU, hsupport, hanalytic, hgerm⟩ :=
    exists_analyticPolynomialRepresentatives x polynomial
  let sourceRepresentative : Source → E → MvPolynomial ι ℝ :=
    fun s ↦ representative (Sum.inl s)
  let targetRepresentative : Target → E → MvPolynomial ι ℝ :=
    fun t ↦ representative (Sum.inr (Sum.inl t))
  let coefficientRepresentative : Target → Source → E → MvPolynomial ι ℝ :=
    fun t s ↦ representative (Sum.inr (Sum.inr (t, s)))
  have hsourceSupport : ∀ s y,
      (sourceRepresentative s y).support ⊆ (source s).support := by
    intro s y
    simpa only [sourceRepresentative, polynomial] using
      hsupport (Sum.inl s) y
  have htargetSupport : ∀ t y,
      (targetRepresentative t y).support ⊆ (target t).support := by
    intro t y
    simpa only [targetRepresentative, polynomial] using
      hsupport (Sum.inr (Sum.inl t)) y
  have hcoefficientSupport : ∀ t s y,
      (coefficientRepresentative t s y).support ⊆
        (coefficient t s).support := by
    intro t s y
    simpa only [coefficientRepresentative, polynomial] using
      hsupport (Sum.inr (Sum.inr (t, s))) y
  have hsourceAnalytic : ∀ s e,
      AnalyticOnNhd ℝ (fun y ↦ (sourceRepresentative s y).coeff e) U := by
    intro s e
    simpa only [sourceRepresentative] using hanalytic (Sum.inl s) e
  have htargetAnalytic : ∀ t e,
      AnalyticOnNhd ℝ (fun y ↦ (targetRepresentative t y).coeff e) U := by
    intro t e
    simpa only [targetRepresentative] using
      hanalytic (Sum.inr (Sum.inl t)) e
  have hcoefficientAnalytic : ∀ t s e,
      AnalyticOnNhd ℝ
        (fun y ↦ (coefficientRepresentative t s y).coeff e) U := by
    intro t s e
    simpa only [coefficientRepresentative] using
      hanalytic (Sum.inr (Sum.inr (t, s))) e
  have hsourceGerm : ∀ s,
      analyticPolynomialGermHom x (source s) =
        (sourceRepresentative s : Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
    intro s
    simpa only [sourceRepresentative, polynomial] using hgerm (Sum.inl s)
  have htargetGerm : ∀ t,
      analyticPolynomialGermHom x (target t) =
        (targetRepresentative t : Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
    intro t
    simpa only [targetRepresentative, polynomial] using
      hgerm (Sum.inr (Sum.inl t))
  have hcoefficientGerm : ∀ t s,
      analyticPolynomialGermHom x (coefficient t s) =
        (coefficientRepresentative t s :
          Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
    intro t s
    simpa only [coefficientRepresentative, polynomial] using
      hgerm (Sum.inr (Sum.inr (t, s)))
  have heventual : ∀ t, targetRepresentative t =ᶠ[𝓝 x]
      fun y ↦ ∑ s, coefficientRepresentative t s y *
        sourceRepresentative s y := by
    intro t
    have h := analyticPolynomialIdentity_eventually x Finset.univ
      (target t) (coefficient t) source (targetRepresentative t)
      (coefficientRepresentative t) sourceRepresentative (htargetGerm t)
      (fun s _ ↦ hcoefficientGerm t s) (fun s _ ↦ hsourceGerm s)
      (by simpa using hgermIdentity t)
    filter_upwards [h] with y hy
    exact hy
  obtain ⟨V, hVopen, hxV, hpolynomial, hevaluation⟩ :=
    exists_open_polynomialIdentities_forall_eval x targetRepresentative
      (fun t y ↦ ∑ s, coefficientRepresentative t s y *
        sourceRepresentative s y) heventual
  refine ⟨{
    coefficient := coefficient
    germ_identity := hgermIdentity
    sourceRepresentative := sourceRepresentative
    targetRepresentative := targetRepresentative
    coefficientRepresentative := coefficientRepresentative
    neighborhood := U ∩ V
    neighborhood_open := hUopen.inter hVopen
    base_mem := ⟨hxU, hxV⟩
    source_support_subset := hsourceSupport
    target_support_subset := htargetSupport
    coefficient_support_subset := hcoefficientSupport
    source_coefficient_analytic := ?_
    target_coefficient_analytic := ?_
    coefficient_coefficient_analytic := ?_
    source_germ_eq := hsourceGerm
    target_germ_eq := htargetGerm
    coefficient_germ_eq := hcoefficientGerm
    polynomial_identity := ?_
    evaluation_identity := ?_
  }⟩
  · intro s e y hy
    exact hsourceAnalytic s e y hy.1
  · intro t e y hy
    exact htargetAnalytic t e y hy.1
  · intro t s e y hy
    exact hcoefficientAnalytic t s e y hy.1
  · intro y hy t
    exact hpolynomial y hy.2 t
  · intro y hy t assignment
    simpa only [map_sum, map_mul] using hevaluation y hy.2 t assignment

/-- Canonical noncomputable choice of the finite analytic adapter produced by
`nonempty_finiteAnalyticChangeOfGeneratorsData`. -/
noncomputable def finiteAnalyticChangeOfGeneratorsDataOfSpan
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {Source : Type w} {Target : Type z}
    [Fintype Source] [Fintype Target]
    (x : E)
    (source : Source → MvPolynomial ι (AnalyticGermAt x))
    (target : Target → MvPolynomial ι (AnalyticGermAt x))
    (hspan : Ideal.span (Set.range target) ≤
      Ideal.span (Set.range source)) :
    FiniteAnalyticChangeOfGeneratorsData x source target :=
  Classical.choice
    (nonempty_finiteAnalyticChangeOfGeneratorsData x source target hspan)

namespace FiniteAnalyticChangeOfGeneratorsData

universe q

/-! ## Evaluation along a convergent parameter family -/

/-- Numeric values of the source representatives along a parameter map and a
moving assignment of the independent polynomial symbols. -/
def sourceValue
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {Source : Type w} {Target : Type z}
    [Fintype Source] [Fintype Target]
    {x : E}
    {source : Source → MvPolynomial ι (AnalyticGermAt x)}
    {target : Target → MvPolynomial ι (AnalyticGermAt x)}
    (data : FiniteAnalyticChangeOfGeneratorsData x source target)
    {X : Type q} (parameter : X → E) (symbolValue : ι → X → ℝ)
    (s : Source) (n : X) : ℝ :=
  MvPolynomial.eval (fun i ↦ symbolValue i n)
    (data.sourceRepresentative s (parameter n))

/-- Numeric values of the target representatives along the same parameter
map and moving symbol assignment. -/
def targetValue
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {Source : Type w} {Target : Type z}
    [Fintype Source] [Fintype Target]
    {x : E}
    {source : Source → MvPolynomial ι (AnalyticGermAt x)}
    {target : Target → MvPolynomial ι (AnalyticGermAt x)}
    (data : FiniteAnalyticChangeOfGeneratorsData x source target)
    {X : Type q} (parameter : X → E) (symbolValue : ι → X → ℝ)
    (t : Target) (n : X) : ℝ :=
  MvPolynomial.eval (fun i ↦ symbolValue i n)
    (data.targetRepresentative t (parameter n))

/-- Numeric values of the change-of-generators coefficient representatives
along the same parameter map and moving symbol assignment. -/
def coefficientValue
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {Source : Type w} {Target : Type z}
    [Fintype Source] [Fintype Target]
    {x : E}
    {source : Source → MvPolynomial ι (AnalyticGermAt x)}
    {target : Target → MvPolynomial ι (AnalyticGermAt x)}
    (data : FiniteAnalyticChangeOfGeneratorsData x source target)
    {X : Type q} (parameter : X → E) (symbolValue : ι → X → ℝ)
    (t : Target) (s : Source) (n : X) : ℝ :=
  MvPolynomial.eval (fun i ↦ symbolValue i n)
    (data.coefficientRepresentative t s (parameter n))

/-- Every evaluated coefficient representative is polynomially bounded when
the parameter tends to the analytic base point and each moving symbol is
polynomially bounded. -/
theorem coefficientValue_hasPolynomialUpperBound
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {Source : Type w} {Target : Type z}
    [Fintype Source] [Fintype Target]
    {x : E}
    {source : Source → MvPolynomial ι (AnalyticGermAt x)}
    {target : Target → MvPolynomial ι (AnalyticGermAt x)}
    (data : FiniteAnalyticChangeOfGeneratorsData x source target)
    {X : Type v} {l : Filter X} {scale : X → ℝ}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (symbolValue : ι → X → ℝ)
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (hsymbol : ∀ i,
      HasPolynomialUpperBound l scale (symbolValue i))
    (t : Target) (s : Source) :
    HasPolynomialUpperBound l scale
      (data.coefficientValue parameter symbolValue t s) := by
  exact analyticMvPolynomialEvaluation_hasPolynomialUpperBound
    (data.coefficientRepresentative t s) (data.coefficient t s).support
    data.neighborhood x data.base_mem parameter hparameter
    (data.coefficient_support_subset t s)
    (fun e _ ↦ data.coefficient_coefficient_analytic t s e)
    symbolValue hscale hsymbol

/-- Finiteness makes the individual coefficient bounds uniform over the
whole target-by-source change-of-generators matrix. -/
theorem coefficientValue_hasUniformPolynomialUpperBound
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {Source : Type w} {Target : Type z}
    [Fintype Source] [Nonempty Source]
    [Fintype Target] [Nonempty Target]
    {x : E}
    {source : Source → MvPolynomial ι (AnalyticGermAt x)}
    {target : Target → MvPolynomial ι (AnalyticGermAt x)}
    (data : FiniteAnalyticChangeOfGeneratorsData x source target)
    {X : Type v} {l : Filter X} {scale : X → ℝ}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (symbolValue : ι → X → ℝ)
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (hsymbol : ∀ i,
      HasPolynomialUpperBound l scale (symbolValue i)) :
    HasUniformPolynomialUpperBound l scale
      (data.coefficientValue parameter symbolValue) := by
  apply hasUniformPolynomialUpperBound_of_finite
    (data.coefficientValue parameter symbolValue) hscale
  intro t s
  exact data.coefficientValue_hasPolynomialUpperBound parameter hparameter
    symbolValue hscale hsymbol t s

/-- On the tail where the parameter lies in the adapter's neighborhood, the
evaluated target family is literally the coefficientwise linear combination
of the evaluated source family. -/
theorem eventually_targetValue_eq_sum
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {Source : Type w} {Target : Type z}
    [Fintype Source] [Fintype Target]
    {x : E}
    {source : Source → MvPolynomial ι (AnalyticGermAt x)}
    {target : Target → MvPolynomial ι (AnalyticGermAt x)}
    (data : FiniteAnalyticChangeOfGeneratorsData x source target)
    {X : Type q} {l : Filter X}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (symbolValue : ι → X → ℝ) :
    ∀ᶠ n in l, ∀ t,
      data.targetValue parameter symbolValue t n =
        ∑ s, data.coefficientValue parameter symbolValue t s n *
          data.sourceValue parameter symbolValue s n := by
  have hneighborhood : ∀ᶠ n in l, parameter n ∈ data.neighborhood :=
    hparameter.eventually (data.neighborhood_open.mem_nhds data.base_mem)
  filter_upwards [hneighborhood] with n hn
  intro t
  simpa only [targetValue, coefficientValue, sourceValue] using
    data.evaluation_identity (parameter n) hn t
      (fun i ↦ symbolValue i n)

/-- Quantitative change of generators without a global germ-evaluation map.
A lower bound for the evaluated target family propagates to the evaluated
source family using only the finite moving coefficient representatives. -/
theorem sourceValue_lower_of_targetValue_lower
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type v} {Source : Type w} {Target : Type z}
    [Fintype Source] [Nonempty Source]
    [Fintype Target] [Nonempty Target]
    {x : E}
    {source : Source → MvPolynomial ι (AnalyticGermAt x)}
    {target : Target → MvPolynomial ι (AnalyticGermAt x)}
    (data : FiniteAnalyticChangeOfGeneratorsData x source target)
    {X : Type v} {l : Filter X} {scale : X → ℝ}
    (parameter : X → E) (hparameter : Tendsto parameter l (𝓝 x))
    (symbolValue : ι → X → ℝ)
    (hscale : ∀ᶠ n in l, 1 ≤ scale n)
    (hsymbol : ∀ i,
      HasPolynomialUpperBound l scale (symbolValue i))
    (htarget : HasInversePowerLowerBound l scale
      (data.targetValue parameter symbolValue)) :
    HasInversePowerLowerBound l scale
      (data.sourceValue parameter symbolValue) := by
  exact hasInversePowerLowerBound_of_linearCombinations
    (data.sourceValue parameter symbolValue)
    (data.targetValue parameter symbolValue)
    (data.coefficientValue parameter symbolValue) hscale
    (data.eventually_targetValue_eq_sum parameter hparameter symbolValue)
    (data.coefficientValue_hasUniformPolynomialUpperBound parameter hparameter
      symbolValue hscale hsymbol)
    htarget

end FiniteAnalyticChangeOfGeneratorsData

end AbelFormalization
