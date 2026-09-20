import AbelFormalization.GeneralCodimensionLagrangeGenericMorse
import AbelFormalization.LiftedComponentFiniteness
import AbelFormalization.SquaredDistanceProper

/-!
# Finite components of globally regular constraint loci

Let `H : ℝ^a → ℝ^k` be a tuple in a smooth geometric function family
closed under coordinate differentiation.  If the derivative of `H` is
surjective at every point of its zero locus, a generic squared-distance
center makes every zero of the augmented `a+k` dimensional Lagrange system
regular.  The family's `0`-regularity makes those augmented zeros finite.

Every connected component of the closed zero locus contains a minimum of
squared distance.  The implicit-function theorem turns this componentwise
minimum into a constrained local minimum, and the Lagrange theorem supplies
its unique multiplier.  Thus every component lifts to the finite augmented
regular-zero type, so `LiftedComponentFiniteness` applies.

The conclusions here concern one specified zero locus or fiber.  No bound
uniform in a target or in a family is asserted.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Constraint zero loci and componentwise minima -/

/-- The simultaneous zero locus of a finite scalar constraint tuple. -/
def constraintZeroLocus {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) : Set (RealEuclidean a) :=
  {x | ∀ i, H i x = 0}

@[simp]
theorem mem_constraintZeroLocus {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (x : RealEuclidean a) :
    x ∈ constraintZeroLocus H ↔ ∀ i, H i x = 0 :=
  Iff.rfl

/-- Continuous constraints have a closed simultaneous zero locus. -/
theorem isClosed_constraintZeroLocus {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a)
    (hH : ∀ i, Continuous (H i)) :
    IsClosed (constraintZeroLocus H) := by
  have hmap : Continuous (constraintMap H) :=
    continuous_pi fun i ↦ hH i
  have hset : constraintZeroLocus H =
      constraintMap H ⁻¹' {(0 : RealEuclidean k)} := by
    ext x
    simp only [mem_constraintZeroLocus, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun hx ↦ funext hx, fun hx i ↦ congrFun hx i⟩
  rw [hset]
  exact isClosed_singleton.preimage hmap

/-- On a regular zero locus, a minimum on the point's connected component is
a local minimum along the ambient constraint fiber. -/
theorem componentMinimizer_isLocalMinOn_constraintZeroLocus
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (rho : RealEuclideanFunction a) (x : constraintZeroLocus H)
    (hmin : x ∈ componentMinimizers
      (fun y : constraintZeroLocus H ↦ rho (y : RealEuclidean a)))
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hsurj : (constraintFDeriv H x).range = ⊤) :
    IsLocalMinOn rho {y | ∀ i, H i y = H i x} (x : RealEuclidean a) := by
  have hlocalConstraint : ∃ V ∈ nhds (x : RealEuclidean a),
      V ∩ {y | ∀ i, H i y = H i x} ⊆ constraintZeroLocus H := by
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    intro y hy
    exact fun i ↦ (hy.2 i).trans (x.property i)
  obtain ⟨U, hU, hcomponent⟩ :=
    localConstraintFiber_of_surjectiveDerivative
      H x hH hsurj hlocalConstraint
  change IsMinOn
    (fun y : constraintZeroLocus H ↦ rho (y : RealEuclidean a))
      (connectedComponent x) x at hmin
  rw [IsLocalMinOn]
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin]
    with y hyU hyfiber
  obtain ⟨hyM, hycomponent⟩ := hcomponent y hyU hyfiber
  exact hmin hycomponent

/-- A componentwise squared-distance minimum on a regular zero locus has one
and only one Lagrange multiplier solving the augmented square system. -/
theorem existsUnique_lagrangeCriticalSystemMap_eq_zero_of_componentMinimizer
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (rho : RealEuclideanFunction a) (x : constraintZeroLocus H)
    (hmin : x ∈ componentMinimizers
      (fun y : constraintZeroLocus H ↦ rho (y : RealEuclidean a)))
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hrho : HasStrictFDerivAt rho (fderiv ℝ rho x) x)
    (hsurj : (constraintFDeriv H x).range = ⊤) :
    ∃! lambda : RealEuclidean k,
      lagrangeCriticalSystemMap H rho
        (realEuclideanAppend (x : RealEuclidean a) lambda) = 0 := by
  have hlocal : IsLocalExtrOn rho
      {y | ∀ i, H i y = H i x} (x : RealEuclidean a) :=
    Or.inl (componentMinimizer_isLocalMinOn_constraintZeroLocus
      H rho x hmin hH hsurj)
  obtain ⟨lambda, hlambda⟩ :=
    exists_lagrangeCriticalSystemMap_eq_zero_of_isLocalExtrOn
      H rho x x.property hlocal hH hrho hsurj
  refine ⟨lambda, hlambda, ?_⟩
  intro mu hmu
  have hlambdaStationarity :=
    (lagrangeCriticalSystemMap_append_eq_zero_iff
      H rho (x : RealEuclidean a) lambda).mp hlambda |>.2
  have hmuStationarity :=
    (lagrangeCriticalSystemMap_append_eq_zero_iff
      H rho (x : RealEuclidean a) mu).mp hmu |>.2
  exact (lagrangeStationarityCovector_eq_zero_unique_of_surjective
    (lambda := lambda) (mu := mu)
    H rho x hsurj hlambdaStationarity hmuStationarity).symm

/-! ## Finite components in arbitrary codimension -/

/-- A globally regular zero locus cut out by members of a smooth,
coordinate-derivative-closed geometric family has finitely many connected
components whenever the family is `0`-regular. -/
theorem finite_connectedComponents_constraintZeroLocus_generalCodimension
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (hHmem : ∀ i, H i ∈ G a)
    (hsurj : ∀ x : RealEuclidean a, x ∈ constraintZeroLocus H →
      (constraintFDeriv H x).range = ⊤) :
    Finite (ConnectedComponents (constraintZeroLocus H)) := by
  let M : Set (RealEuclidean a) := constraintZeroLocus H
  have hHinf : ∀ i, ContDiff ℝ ∞ (H i) :=
    fun i ↦ hsmooth a (H i) (hHmem i)
  have hMclosed : IsClosed M := by
    exact isClosed_constraintZeroLocus H (fun i ↦ (hHinf i).continuous)
  obtain ⟨center, hcenter⟩ :=
    hsmooth.exists_standardSquaredDistanceCenter_regular_lagrangeCriticalSystem
      H hHmem (fun x hx ↦ hsurj x hx)
  let rho : RealEuclideanFunction a := standardSquaredDistance center
  let criticalMap : RealEuclidean (a + k) → RealEuclidean (a + k) :=
    lagrangeCriticalSystemMap H rho
  have hrhomem : rho ∈ G a := by
    simpa only [rho, standardSquaredDistance] using
      hG.standardSquaredDistance_mem center
  have hrhoinf : ContDiff ℝ ∞ rho :=
    hsmooth a rho hrhomem
  have hcriticalMem : FunctionTupleInFamily G criticalMap := by
    simpa only [criticalMap, rho] using
      hG.lagrangeSquaredDistanceCriticalSystemMap_mem
        hderiv H hHmem center
  have hregularFinite :
      (regularZeroSet Set.univ criticalMap).Finite :=
    hzero.regularZeroSet_univ_finite hsmooth criticalMap hcriticalMem
  let criticalZeros : Set (RealEuclidean (a + k)) :=
    regularZeroSet Set.univ criticalMap
  letI : Finite criticalZeros := Set.finite_coe_iff.mpr (by
    simpa only [criticalZeros] using hregularFinite)
  let primal : criticalZeros → M := fun z ↦
    ⟨lagrangePrimalProjection a k z.1, by
      intro i
      have hcoord := congrFun z.property.2.1 (Fin.natAdd a i)
      simpa only [criticalMap,
        lagrangeCriticalSystemMap_apply_natAdd,
        lagrangeConstraintEquation, Pi.zero_apply] using hcoord⟩
  have hcompact : ∀ R : ℝ,
      IsCompact {x : M | rho (x : RealEuclidean a) ≤ R} := by
    intro R
    apply isCompact_subtype_sublevel_of_isClosed hMclosed rho
    intro c
    simpa only [rho, standardSquaredDistance] using
      isCompact_algebraicSquaredDistance_basis_sublevel
        (Pi.basisFun ℝ (Fin a)) center c
  apply finite_connectedComponents_of_finite_lifted_componentMinimizers
    (fun x : M ↦ rho (x : RealEuclidean a))
    (hrhoinf.continuous.comp continuous_subtype_val)
    hcompact primal
  intro x hxmin
  have hHstrict : ∀ i,
      HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x := by
    intro i
    exact (hHinf i).contDiffAt.hasStrictFDerivAt (by norm_num)
  have hrhostrict : HasStrictFDerivAt rho (fderiv ℝ rho x) x :=
    hrhoinf.contDiffAt.hasStrictFDerivAt (by norm_num)
  obtain ⟨lambda, hlambda, _⟩ :=
    existsUnique_lagrangeCriticalSystemMap_eq_zero_of_componentMinimizer
      H rho x hxmin hHstrict hrhostrict (hsurj x x.property)
  let z : RealEuclidean (a + k) :=
    realEuclideanAppend (x : RealEuclidean a) lambda
  have hzregular : z ∈ regularZeroSet Set.univ criticalMap := by
    refine ⟨Set.mem_univ z, ?_, ?_⟩
    · simpa only [z, criticalMap] using hlambda
    · apply LinearMap.range_eq_top.mp
      simpa only [z, criticalMap, rho] using hcenter z (by
        simpa only [z, criticalMap, rho] using hlambda)
  let zcritical : criticalZeros := ⟨z, by
    simpa only [criticalZeros] using hzregular⟩
  refine ⟨zcritical, ?_⟩
  apply Subtype.ext
  change lagrangePrimalProjection a k
    (realEuclideanAppend (x : RealEuclidean a) lambda) =
      (x : RealEuclidean a)
  exact lagrangePrimalProjection_append (x : RealEuclidean a) lambda

/-- A regular fiber of a family map `ℝ^a → ℝ^k` has finitely many
connected components.  Both dimensions are arbitrary. -/
theorem finite_connectedComponents_fiber_of_surjective_generalCodimension
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    {a k : ℕ} (g : RealEuclidean a → RealEuclidean k)
    (hg : FunctionTupleInFamily G g) (t : RealEuclidean k)
    (hsurj : ∀ x, g x = t → Function.Surjective (fderiv ℝ g x)) :
    Finite (ConnectedComponents (g ⁻¹' {t})) := by
  let H : Fin k → RealEuclideanFunction a :=
    fun i x ↦ g x i - t i
  have hHmem : ∀ i, H i ∈ G a := by
    intro i
    exact hG.sub_mem (hg i) (hG.const_mem (t i))
  have hgInf : ContDiff ℝ ∞ g := by
    rw [contDiff_pi]
    intro i
    exact hsmooth a (fun x ↦ g x i) (hg i)
  have hHdiff : ∀ x i, DifferentiableAt ℝ (H i) x := by
    intro x i
    exact (hsmooth a (H i) (hHmem i)).differentiable (by simp)
      |>.differentiableAt
  have hconstraint : ∀ x, x ∈ constraintZeroLocus H →
      (constraintFDeriv H x).range = ⊤ := by
    intro x hx
    have hgxt : g x = t := by
      funext i
      exact sub_eq_zero.mp (hx i)
    have hderivEq : constraintFDeriv H x = fderiv ℝ g x := by
      have htupleDeriv :
          fderiv ℝ (constraintMap H) x = constraintFDeriv H x := by
        change fderiv ℝ (fun y i ↦ H i y) x =
          ContinuousLinearMap.pi (fun i ↦ fderiv ℝ (H i) x)
        exact fderiv_pi (fun i ↦ hHdiff x i)
      calc
        constraintFDeriv H x = fderiv ℝ (constraintMap H) x :=
          htupleDeriv.symm
        _ = fderiv ℝ (fun y ↦ g y - t) x := by rfl
        _ = fderiv ℝ g x := by rw [fderiv_sub_const]
    rw [hderivEq]
    exact LinearMap.range_eq_top.mpr (hsurj x hgxt)
  have hfinite :=
    finite_connectedComponents_constraintZeroLocus_generalCodimension
      hG hsmooth hderiv hzero H hHmem hconstraint
  have hset : constraintZeroLocus H = g ⁻¹' {t} := by
    ext x
    simp only [mem_constraintZeroLocus, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · intro hx
      funext i
      exact sub_eq_zero.mp (hx i)
    · intro hx i
      exact sub_eq_zero.mpr (congrFun hx i)
  rwa [hset] at hfinite

/-- The arbitrary-codimension regular-fiber conclusion for the concrete Abel
geometric family, given its separated `0`-regularity input. -/
theorem IsAbel.finite_connectedComponents_abelGeometricFiber_of_surjective_generalCodimension
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hzero : IsZeroRegularFunctionFamily (abelGeometricFamily A))
    {a k : ℕ} (g : RealEuclidean a → RealEuclidean k)
    (hg : FunctionTupleInFamily (abelGeometricFamily A) g)
    (t : RealEuclidean k)
    (hsurj : ∀ x, g x = t → Function.Surjective (fderiv ℝ g x)) :
    Finite (ConnectedComponents (g ⁻¹' {t})) := by
  exact finite_connectedComponents_fiber_of_surjective_generalCodimension
    (isGeometricFunctionFamily_abelGeometricFamily A)
    hA.isEverywhereSmooth_abelGeometricFamily
    hA.isCoordinateDerivativeClosed_abelGeometricFamily
    hzero g hg t hsurj

/-- Numerator regular-zero finiteness gives the same pointwise conclusion for
the concrete Abel family in arbitrary codimension. -/
theorem IsAbel.finite_connectedComponents_abelGeometricFiber_of_numerator_generalCodimension
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hfinite : AbelNumeratorRegularZeroFinite A)
    {a k : ℕ} (g : RealEuclidean a → RealEuclidean k)
    (hg : FunctionTupleInFamily (abelGeometricFamily A) g)
    (t : RealEuclidean k)
    (hsurj : ∀ x, g x = t → Function.Surjective (fderiv ℝ g x)) :
    Finite (ConnectedComponents (g ⁻¹' {t})) := by
  exact hA.finite_connectedComponents_abelGeometricFiber_of_surjective_generalCodimension
    (hA.isZeroRegular_abelGeometricFamily_of_numerator hfinite)
    g hg t hsurj

end AbelFormalization
