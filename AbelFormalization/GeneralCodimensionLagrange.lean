import AbelFormalization.LagrangeCriticalDeterminant
import AbelFormalization.LionRegularCodimensionOne
import AbelFormalization.ProjectedZeroFamily
import AbelFormalization.SquaredDistanceDifferentiation

/-!
# The Lagrange critical system in arbitrary codimension

For `k` constraints on `ℝ^a`, the Lagrange multiplier equations use the
augmented variables `(x, lambda) ∈ ℝ^(a+k)`.  There are `a` stationarity
equations and `k` constraint equations, hence a square system of `a+k`
equations in `a+k` variables.

This file constructs that system, proves its component formulas, and shows
that all of its equations remain in a geometric function family closed under
coordinate differentiation.  It also proves the elementary Lagrange bridge:
at a regular constrained local extremum there is a unique multiplier making
the augmented system vanish.

No regularity or finiteness assertion is made about the zero set of the
augmented system.  Those require a separate transversality argument.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-! ## Augmented coordinates -/

/-- Projection from augmented variables `(x, lambda)` to the primal
coordinates `x`. -/
def lagrangePrimalProjection (a k : ℕ) :
    RealEuclidean (a + k) →ₗ[ℝ] RealEuclidean a where
  toFun z i := z (Fin.castAdd k i)
  map_add' x y := by
    funext i
    rfl
  map_smul' c x := by
    funext i
    rfl

@[simp]
theorem lagrangePrimalProjection_apply {a k : ℕ}
    (z : RealEuclidean (a + k)) (i : Fin a) :
    lagrangePrimalProjection a k z i = z (Fin.castAdd k i) :=
  rfl

@[simp]
theorem lagrangePrimalProjection_append {a k : ℕ}
    (x : RealEuclidean a) (lambda : RealEuclidean k) :
    lagrangePrimalProjection a k (realEuclideanAppend x lambda) = x := by
  funext i
  simp

/-- The `i`th multiplier coordinate on the augmented space. -/
def lagrangeMultiplierCoordinate {a k : ℕ} (i : Fin k) :
    RealEuclideanFunction (a + k) :=
  fun z ↦ z (Fin.natAdd a i)

@[simp]
theorem lagrangeMultiplierCoordinate_append {a k : ℕ}
    (i : Fin k) (x : RealEuclidean a) (lambda : RealEuclidean k) :
    lagrangeMultiplierCoordinate (a := a) i
      (realEuclideanAppend x lambda) = lambda i := by
  simp [lagrangeMultiplierCoordinate]

/-! ## Equations and their component formulas -/

/-- A constraint equation pulled back to the augmented space. -/
def lagrangeConstraintEquation {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (i : Fin k) :
    RealEuclideanFunction (a + k) :=
  fun z ↦ H i (lagrangePrimalProjection a k z)

@[simp]
theorem lagrangeConstraintEquation_append {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (i : Fin k)
    (x : RealEuclidean a) (lambda : RealEuclidean k) :
    lagrangeConstraintEquation H i (realEuclideanAppend x lambda) = H i x := by
  simp [lagrangeConstraintEquation]

/-- The `j`th coordinate derivative of a primal function, pulled back to the
augmented space. -/
def lagrangePulledCoordinateFDeriv {a k : ℕ}
    (f : RealEuclideanFunction a) (j : Fin a) :
    RealEuclideanFunction (a + k) :=
  fun z ↦ fderiv ℝ f (lagrangePrimalProjection a k z) (Pi.single j 1)

@[simp]
theorem lagrangePulledCoordinateFDeriv_append {a k : ℕ}
    (f : RealEuclideanFunction a) (j : Fin a)
    (x : RealEuclidean a) (lambda : RealEuclidean k) :
    lagrangePulledCoordinateFDeriv (k := k) f j
        (realEuclideanAppend x lambda) =
      fderiv ℝ f x (Pi.single j 1) := by
  simp [lagrangePulledCoordinateFDeriv]

/-- The covector form of the Lagrange stationarity equation. -/
def lagrangeStationarityCovector {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (rho : RealEuclideanFunction a)
    (x : RealEuclidean a) (lambda : RealEuclidean k) :
    StrongDual ℝ (RealEuclidean a) :=
  fderiv ℝ rho x - ∑ i, lambda i • fderiv ℝ (H i) x

/-- The `j`th scalar stationarity equation on augmented variables. -/
def lagrangeStationarityEquation {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (rho : RealEuclideanFunction a)
    (j : Fin a) : RealEuclideanFunction (a + k) :=
  lagrangePulledCoordinateFDeriv (k := k) rho j -
    ∑ i, lagrangeMultiplierCoordinate (a := a) i *
      lagrangePulledCoordinateFDeriv (k := k) (H i) j

@[simp]
theorem lagrangeStationarityEquation_append {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (rho : RealEuclideanFunction a)
    (j : Fin a) (x : RealEuclidean a) (lambda : RealEuclidean k) :
    lagrangeStationarityEquation H rho j
        (realEuclideanAppend x lambda) =
      fderiv ℝ rho x (Pi.single j 1) -
        ∑ i, lambda i * fderiv ℝ (H i) x (Pi.single j 1) := by
  simp [lagrangeStationarityEquation]

theorem lagrangeStationarityEquation_append_eq_covector_apply {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (rho : RealEuclideanFunction a)
    (j : Fin a) (x : RealEuclidean a) (lambda : RealEuclidean k) :
    lagrangeStationarityEquation H rho j
        (realEuclideanAppend x lambda) =
      lagrangeStationarityCovector H rho x lambda (Pi.single j 1) := by
  simp [lagrangeStationarityCovector]

/-- The coordinate stationarity equations vanish exactly when the stationarity
covector vanishes. -/
theorem lagrangeStationarityEquations_zero_iff_covector_eq_zero {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (rho : RealEuclideanFunction a)
    (x : RealEuclidean a) (lambda : RealEuclidean k) :
    (∀ j, lagrangeStationarityEquation H rho j
        (realEuclideanAppend x lambda) = 0) ↔
      lagrangeStationarityCovector H rho x lambda = 0 := by
  constructor
  · intro hcoordinate
    apply ContinuousLinearMap.ext
    intro v
    let B : Module.Basis (Fin a) ℝ (RealEuclidean a) :=
      Pi.basisFun ℝ (Fin a)
    have hv : (∑ j, v j • B j) = v := by
      simpa only [B, Pi.basisFun_repr] using B.sum_repr v
    have hbasis : ∀ j,
        lagrangeStationarityCovector H rho x lambda (B j) = 0 := by
      intro j
      simpa only [B, Pi.basisFun_apply,
        lagrangeStationarityEquation_append_eq_covector_apply] using
        hcoordinate j
    rw [← hv, map_sum]
    simp [hbasis]
  · intro hcovector j
    rw [lagrangeStationarityEquation_append_eq_covector_apply,
      hcovector]
    rfl

/-! ## The square augmented system -/

/-- The square Lagrange equation tuple.  The first `a` rows are stationarity
and the final `k` rows are the original constraints. -/
def lagrangeCriticalSystemEquations {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (rho : RealEuclideanFunction a) :
    Fin (a + k) → RealEuclideanFunction (a + k) :=
  Fin.addCases (lagrangeStationarityEquation H rho)
    (lagrangeConstraintEquation H)

@[simp]
theorem lagrangeCriticalSystemEquations_castAdd {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (rho : RealEuclideanFunction a)
    (j : Fin a) :
    lagrangeCriticalSystemEquations H rho (Fin.castAdd k j) =
      lagrangeStationarityEquation H rho j := by
  simp [lagrangeCriticalSystemEquations]

@[simp]
theorem lagrangeCriticalSystemEquations_natAdd {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (rho : RealEuclideanFunction a)
    (i : Fin k) :
    lagrangeCriticalSystemEquations H rho (Fin.natAdd a i) =
      lagrangeConstraintEquation H i := by
  simp [lagrangeCriticalSystemEquations]

/-- The square map associated to the Lagrange equation tuple. -/
def lagrangeCriticalSystemMap {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (rho : RealEuclideanFunction a) :
    RealEuclidean (a + k) → RealEuclidean (a + k) :=
  constraintMap (lagrangeCriticalSystemEquations H rho)

@[simp]
theorem lagrangeCriticalSystemMap_apply_castAdd {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (rho : RealEuclideanFunction a)
    (z : RealEuclidean (a + k)) (j : Fin a) :
    lagrangeCriticalSystemMap H rho z (Fin.castAdd k j) =
      lagrangeStationarityEquation H rho j z := by
  simp [lagrangeCriticalSystemMap, constraintMap]

@[simp]
theorem lagrangeCriticalSystemMap_apply_natAdd {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (rho : RealEuclideanFunction a)
    (z : RealEuclidean (a + k)) (i : Fin k) :
    lagrangeCriticalSystemMap H rho z (Fin.natAdd a i) =
      lagrangeConstraintEquation H i z := by
  simp [lagrangeCriticalSystemMap, constraintMap]

/-- Vanishing of the square coordinate system is exactly primal feasibility
plus the covector Lagrange equation. -/
theorem lagrangeCriticalSystemMap_append_eq_zero_iff {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (rho : RealEuclideanFunction a)
    (x : RealEuclidean a) (lambda : RealEuclidean k) :
    lagrangeCriticalSystemMap H rho (realEuclideanAppend x lambda) = 0 ↔
      (∀ i, H i x = 0) ∧
        lagrangeStationarityCovector H rho x lambda = 0 := by
  constructor
  · intro hsystem
    have hconstraint : ∀ i, H i x = 0 := by
      intro i
      have hi := congrFun hsystem (Fin.natAdd a i)
      simpa using hi
    have hstationarity : ∀ j,
        lagrangeStationarityEquation H rho j
          (realEuclideanAppend x lambda) = 0 := by
      intro j
      have hj := congrFun hsystem (Fin.castAdd k j)
      simpa using hj
    exact ⟨hconstraint,
      (lagrangeStationarityEquations_zero_iff_covector_eq_zero
        H rho x lambda).mp hstationarity⟩
  · rintro ⟨hconstraint, hstationarity⟩
    funext q
    refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) q
    · rw [lagrangeCriticalSystemMap_apply_castAdd,
        lagrangeStationarityEquation_append_eq_covector_apply,
        hstationarity]
      rfl
    · simpa using hconstraint i

/-! ## Closure in a geometric family -/

theorem IsGeometricFunctionFamily.lagrangeMultiplierCoordinate_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {a k : ℕ} (i : Fin k) :
    lagrangeMultiplierCoordinate (a := a) i ∈ G (a + k) := by
  change (fun z : RealEuclidean (a + k) ↦ z (Fin.natAdd a i)) ∈
    G (a + k)
  simpa using
    hG.polynomial (MvPolynomial.X (Fin.natAdd a i))

theorem IsGeometricFunctionFamily.lagrangeConstraintEquation_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {a k : ℕ}
    (H : Fin k → RealEuclideanFunction a) (hH : ∀ i, H i ∈ G a)
    (i : Fin k) :
    lagrangeConstraintEquation H i ∈ G (a + k) := by
  change (H i ∘ (lagrangePrimalProjection a k).toAffineMap) ∈ G (a + k)
  exact hG.affine_comp (hH i) (lagrangePrimalProjection a k).toAffineMap

theorem IsGeometricFunctionFamily.lagrangePulledCoordinateFDeriv_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a k : ℕ} (f : RealEuclideanFunction a) (hf : f ∈ G a) (j : Fin a) :
    lagrangePulledCoordinateFDeriv (k := k) f j ∈ G (a + k) := by
  have hd := hderiv a f hf j
  change ((fun x : RealEuclidean a ↦
    fderiv ℝ f x (Pi.single j 1)) ∘
      (lagrangePrimalProjection a k).toAffineMap) ∈ G (a + k)
  exact hG.affine_comp hd (lagrangePrimalProjection a k).toAffineMap

theorem IsGeometricFunctionFamily.lagrangeStationarityEquation_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (rho : RealEuclideanFunction a)
    (hH : ∀ i, H i ∈ G a) (hrho : rho ∈ G a) (j : Fin a) :
    lagrangeStationarityEquation H rho j ∈ G (a + k) := by
  unfold lagrangeStationarityEquation
  apply hG.sub_mem
  · exact hG.lagrangePulledCoordinateFDeriv_mem hderiv rho hrho j
  · apply hG.finset_sum_mem Finset.univ
    intro i hi
    exact hG.mul (hG.lagrangeMultiplierCoordinate_mem i)
      (hG.lagrangePulledCoordinateFDeriv_mem hderiv (H i) (hH i) j)

theorem IsGeometricFunctionFamily.lagrangeCriticalSystemEquations_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (rho : RealEuclideanFunction a)
    (hH : ∀ i, H i ∈ G a) (hrho : rho ∈ G a) :
    ∀ q, lagrangeCriticalSystemEquations H rho q ∈ G (a + k) := by
  intro q
  refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) q
  · simpa using hG.lagrangeStationarityEquation_mem hderiv H rho hH hrho j
  · simpa using hG.lagrangeConstraintEquation_mem H hH i

theorem IsGeometricFunctionFamily.lagrangeCriticalSystemMap_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (rho : RealEuclideanFunction a)
    (hH : ∀ i, H i ∈ G a) (hrho : rho ∈ G a) :
    FunctionTupleInFamily G (lagrangeCriticalSystemMap H rho) := by
  intro q
  simpa [lagrangeCriticalSystemMap, constraintMap] using
    hG.lagrangeCriticalSystemEquations_mem hderiv H rho hH hrho q

/-! ## Squared distance specialization -/

/-- Squared distance from `center` in the standard coordinates of `ℝ^a`. -/
def standardSquaredDistance {a : ℕ} (center : RealEuclidean a) :
    RealEuclideanFunction a :=
  algebraicSquaredDistance
    (fun i x ↦ (Pi.basisFun ℝ (Fin a)).equivFun x i) center

@[simp]
theorem fderiv_standardSquaredDistance_apply_single {a : ℕ}
    (center x : RealEuclidean a) (j : Fin a) :
    fderiv ℝ (standardSquaredDistance center) x (Pi.single j 1) =
      2 * (x j - center j) := by
  unfold standardSquaredDistance
  rw [fderiv_algebraicSquaredDistance_basis_apply]
  simp [Pi.single_apply]

@[simp]
theorem lagrangeStationarityEquation_standardSquaredDistance_append
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (center x : RealEuclidean a) (lambda : RealEuclidean k) (j : Fin a) :
    lagrangeStationarityEquation H (standardSquaredDistance center) j
        (realEuclideanAppend x lambda) =
      2 * (x j - center j) -
        ∑ i, lambda i * fderiv ℝ (H i) x (Pi.single j 1) := by
  rw [lagrangeStationarityEquation_append,
    fderiv_standardSquaredDistance_apply_single]

theorem IsGeometricFunctionFamily.lagrangeSquaredDistanceCriticalSystemMap_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (hH : ∀ i, H i ∈ G a) (center : RealEuclidean a) :
    FunctionTupleInFamily G
      (lagrangeCriticalSystemMap H (standardSquaredDistance center)) := by
  apply hG.lagrangeCriticalSystemMap_mem hderiv H
    (standardSquaredDistance center) hH
  simpa [standardSquaredDistance] using hG.standardSquaredDistance_mem center

/-! ## Regular constraints and Lagrange multipliers -/

/-- Surjectivity of the simultaneous constraint derivative makes the
individual constraint differentials linearly independent. -/
theorem linearIndependent_constraintFDeriv_components_of_surjective
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (x : RealEuclidean a)
    (hsurj : (constraintFDeriv H x).range = ⊤) :
    LinearIndependent ℝ (fun i ↦ fderiv ℝ (H i) x) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let ei : RealEuclidean k := Pi.single i 1
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.mp hsurj ei
  have hcomponent : ∀ j,
      fderiv ℝ (H j) x v = ei j := by
    intro j
    have hj := congrFun hv j
    simpa [constraintFDeriv] using hj
  have heval := congrArg
    (fun L : StrongDual ℝ (RealEuclidean a) ↦ L v) hc
  simpa [hcomponent, ei, Pi.single_apply] using heval

/-- At a regular constrained local extremum, the Lagrange multiplier can be
normalized so that the objective differential has coefficient one. -/
theorem exists_lagrangeStationarityCovector_eq_zero_of_isLocalExtrOn
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (rho : RealEuclideanFunction a) (x : RealEuclidean a)
    (hlocal : IsLocalExtrOn rho {y | ∀ i, H i y = H i x} x)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hrho : HasStrictFDerivAt rho (fderiv ℝ rho x) x)
    (hsurj : (constraintFDeriv H x).range = ⊤) :
    ∃ lambda : RealEuclidean k,
      lagrangeStationarityCovector H rho x lambda = 0 := by
  obtain ⟨Lambda, Lambda0, hnonzero, hrelation⟩ :=
    hlocal.exists_multipliers_of_hasStrictFDerivAt hH hrho
  have hLambda0 : Lambda0 ≠ 0 := by
    intro hLambda0
    have hsum : (∑ i, Lambda i • fderiv ℝ (H i) x) = 0 := by
      simpa [hLambda0] using hrelation
    have hLambda : ∀ i, Lambda i = 0 :=
      (Fintype.linearIndependent_iff.mp
        (linearIndependent_constraintFDeriv_components_of_surjective
          H x hsurj)) Lambda hsum
    apply hnonzero
    apply Prod.ext
    · funext i
      exact hLambda i
    · exact hLambda0
  let lambda : RealEuclidean k := fun i ↦ -Lambda0⁻¹ * Lambda i
  have hsumNormalized :
      (∑ i, lambda i • fderiv ℝ (H i) x) = fderiv ℝ rho x := by
    let S : StrongDual ℝ (RealEuclidean a) :=
      ∑ i, Lambda i • fderiv ℝ (H i) x
    have hS : S = -(Lambda0 • fderiv ℝ rho x) := by
      exact eq_neg_of_add_eq_zero_left hrelation
    calc
      (∑ i, lambda i • fderiv ℝ (H i) x) =
          (-Lambda0⁻¹) • S := by
        simp [lambda, S, Finset.smul_sum, smul_smul]
      _ = (-Lambda0⁻¹) • (-(Lambda0 • fderiv ℝ rho x)) := by
        rw [hS]
      _ = fderiv ℝ rho x := by
        rw [smul_neg, smul_smul]
        have hcoefficient : (-Lambda0⁻¹) * Lambda0 = (-1 : ℝ) := by
          simp [hLambda0]
        have hinner : (-1 : ℝ) • fderiv ℝ rho x =
            -(fderiv ℝ rho x) :=
          neg_one_smul ℝ (fderiv ℝ rho x)
        rw [hcoefficient, hinner, neg_neg]
  refine ⟨lambda, ?_⟩
  simp [lagrangeStationarityCovector, hsumNormalized]

/-- A regular constrained local extremum on the zero fiber is a zero of the
square augmented Lagrange system. -/
theorem exists_lagrangeCriticalSystemMap_eq_zero_of_isLocalExtrOn
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (rho : RealEuclideanFunction a) (x : RealEuclidean a)
    (hzero : ∀ i, H i x = 0)
    (hlocal : IsLocalExtrOn rho {y | ∀ i, H i y = H i x} x)
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hrho : HasStrictFDerivAt rho (fderiv ℝ rho x) x)
    (hsurj : (constraintFDeriv H x).range = ⊤) :
    ∃ lambda : RealEuclidean k,
      lagrangeCriticalSystemMap H rho
        (realEuclideanAppend x lambda) = 0 := by
  obtain ⟨lambda, hlambda⟩ :=
    exists_lagrangeStationarityCovector_eq_zero_of_isLocalExtrOn
      H rho x hlocal hH hrho hsurj
  exact ⟨lambda,
    (lagrangeCriticalSystemMap_append_eq_zero_iff H rho x lambda).2
      ⟨hzero, hlambda⟩⟩

/-- For regular constraints, the multiplier in the stationarity equation is
unique. -/
theorem lagrangeStationarityCovector_eq_zero_unique_of_surjective
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (rho : RealEuclideanFunction a) (x : RealEuclidean a)
    (hsurj : (constraintFDeriv H x).range = ⊤)
    {lambda mu : RealEuclidean k}
    (hlambda : lagrangeStationarityCovector H rho x lambda = 0)
    (hmu : lagrangeStationarityCovector H rho x mu = 0) :
    lambda = mu := by
  have hsumLambda :
      (∑ i, lambda i • fderiv ℝ (H i) x) = fderiv ℝ rho x := by
    have h : fderiv ℝ rho x -
        (∑ i, lambda i • fderiv ℝ (H i) x) = 0 := by
      simpa [lagrangeStationarityCovector] using hlambda
    exact (sub_eq_zero.mp h).symm
  have hsumMu :
      (∑ i, mu i • fderiv ℝ (H i) x) = fderiv ℝ rho x := by
    have h : fderiv ℝ rho x -
        (∑ i, mu i • fderiv ℝ (H i) x) = 0 := by
      simpa [lagrangeStationarityCovector] using hmu
    exact (sub_eq_zero.mp h).symm
  have hcoeff : ∀ i, lambda i = mu i :=
    (Fintype.linearIndependent_iffₛ.mp
      (linearIndependent_constraintFDeriv_components_of_surjective
        H x hsurj)) lambda mu (hsumLambda.trans hsumMu.symm)
  exact funext hcoeff

end AbelFormalization
