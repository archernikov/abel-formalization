import AbelFormalization.AbelNumeratorRestrictedGraphSystem
import AbelFormalization.FiniteExplicitRegularZeroGraphLift
import AbelFormalization.RestrictedRegularZeroInduction
import AbelFormalization.RestrictedPairMergeExceptionalFlatSystem
import AbelFormalization.AbelGeometricRegularZero

/-!
# From restricted regular zeros to Abel numerator regular zeros

This file realizes a finite numerator system as a restricted square graph
system and transfers regularity across the two canonical coordinate changes.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

namespace AbelNumeratorSystemPolynomialPresentation

variable {A : ℝ → ℝ} {n : ℕ} {F : Fin n → RealEuclideanFunction n}
    (P : AbelNumeratorSystemPolynomialPresentation A F)

/-- Linear rebracketing from an original point and free jet values to the
restricted graph source. -/
def productToRestrictedGraphSourceLinearEquiv :
    (RealEuclidean n × RealEuclidean P.generatorCount) ≃ₗ[ℝ]
      P.RestrictedGraphSource where
  toFun q := ((q.2, Fin.elim0), q.1)
  invFun y := (y.2, y.1.1)
  left_inv := by
    intro q
    rfl
  right_inv := by
    intro y
    ext i
    · rfl
    · exact Fin.elim0 i
    · rfl
  map_add' := by
    intro q r
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        exact Fin.elim0 i
    · rfl
  map_smul' := by
    intro c q
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        exact Fin.elim0 i
    · rfl

/-- Continuous-linear form of the graph-source rebracketing. -/
def productToRestrictedGraphSource :
    (RealEuclidean n × RealEuclidean P.generatorCount) ≃L[ℝ]
      P.RestrictedGraphSource :=
  P.productToRestrictedGraphSourceLinearEquiv.toContinuousLinearEquiv

@[simp]
theorem productToRestrictedGraphSource_apply
    (q : RealEuclidean n × RealEuclidean P.generatorCount) :
    P.productToRestrictedGraphSource q = ((q.2, Fin.elim0), q.1) :=
  rfl

/-- Independent polynomial variables before the graph equations are imposed. -/
def productRestrictedGraphVariable :
    Fin n ⊕ Fin P.generatorCount →
      RealEuclidean n × RealEuclidean P.generatorCount → ℝ
  | Sum.inl i => fun q ↦ q.1 i
  | Sum.inr j => fun q ↦ iteratedDeriv (P.derivativeOrder j) A (q.2 j)

/-- The numerator block with its selected Abel jets treated as independent
positive variables. -/
def productLiftedNumerator :
    RealEuclidean n × RealEuclidean P.generatorCount → RealEuclidean n :=
  fun q i ↦ MvPolynomial.eval (fun z ↦ P.productRestrictedGraphVariable z q)
    (P.polynomial i)

@[simp]
theorem productLiftedNumerator_apply
    (q : RealEuclidean n × RealEuclidean P.generatorCount) (i : Fin n) :
    P.productLiftedNumerator q i =
      P.restrictedLiftedNumerator i (P.productToRestrictedGraphSource q) := by
  unfold productLiftedNumerator restrictedLiftedNumerator
  apply congrArg (fun v ↦ MvPolynomial.eval v (P.polynomial i))
  funext z
  rcases z with k | j
  · rfl
  · change iteratedDeriv (P.derivativeOrder j) A (q.2 j) =
      iteratedDeriv (P.derivativeOrder j) A (q.2 j + 0)
    rw [add_zero]

@[simp]
theorem productLiftedNumerator_graphValue
    (x : RealEuclidean n) :
    P.productLiftedNumerator (x, P.graphValue x) = constraintMap F x := by
  funext i
  rw [P.productLiftedNumerator_apply]
  exact P.restrictedLiftedNumerator_graphSource i x

/-- Reorder the product output of the explicit graph lift into graph rows
followed by numerator rows. -/
def productToRestrictedGraphOutput :
    (RealEuclidean n × RealEuclidean P.generatorCount) ≃L[ℝ]
      RealEuclidean (P.generatorCount + n) :=
  (ContinuousLinearEquiv.prodComm ℝ
      (RealEuclidean n) (RealEuclidean P.generatorCount)).trans
    (finFunctionProductContinuousLinearEquiv P.generatorCount n)

@[simp]
theorem productToRestrictedGraphOutput_apply
    (q : RealEuclidean n × RealEuclidean P.generatorCount)
    (e : Fin (P.generatorCount + n)) :
    P.productToRestrictedGraphOutput q e =
      Fin.addCases q.2 q.1 e := by
  rfl

/-- After source rebracketing and output permutation, the explicit graph lift
is exactly the restricted augmented family. -/
theorem productToRestrictedGraphOutput_explicitGraphLiftSystem
    (q : RealEuclidean n × RealEuclidean P.generatorCount) :
    P.productToRestrictedGraphOutput
        (finiteExplicitGraphLiftSystem P.productLiftedNumerator P.graphValue q) =
      constraintMap P.restrictedAugmentedEquationFamily
        (P.productToRestrictedGraphSource q) := by
  funext e
  refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) e
  · simp [productToRestrictedGraphOutput_apply,
      finiteExplicitGraphLiftSystem, finiteImplicitGraphLiftSystem,
      finiteExplicitGraphEquation, restrictedAugmentedEquationFamily,
      restrictedGraphEquation, restrictedSCoordinate,
      restrictedAffineArgument, graphValue, constraintMap]
    ring
  · simp [productToRestrictedGraphOutput_apply,
      finiteExplicitGraphLiftSystem, finiteImplicitGraphLiftSystem,
      restrictedAugmentedEquationFamily, constraintMap]

/-- The polynomial numerator block is differentiable wherever all independent
jet arguments are positive. -/
theorem differentiableAt_productLiftedNumerator_of_isAbel
    {A : ℝ → ℝ} (hA : IsAbel A)
    {n : ℕ} {F : Fin n → RealEuclideanFunction n}
    (P : AbelNumeratorSystemPolynomialPresentation A F)
    (q : RealEuclidean n × RealEuclidean P.generatorCount)
    (hq : ∀ j, 0 < q.2 j) :
    DifferentiableAt ℝ P.productLiftedNumerator q := by
  apply differentiableAt_pi.mpr
  intro i
  unfold productLiftedNumerator
  have hv : ∀ z : Fin n ⊕ Fin P.generatorCount,
      AnalyticAt ℝ (fun y ↦ P.productRestrictedGraphVariable z y) q := by
    intro z
    rcases z with k | j
    · exact ((ContinuousLinearMap.proj (R := ℝ) k).comp
        (ContinuousLinearMap.fst ℝ (RealEuclidean n)
          (RealEuclidean P.generatorCount))).analyticAt q
    · have houter : AnalyticAt ℝ
          (iteratedDeriv (P.derivativeOrder j) A) (q.2 j) := by
        rw [iteratedDeriv_eq_iterate]
        exact (hA.analytic.iterated_deriv (P.derivativeOrder j))
          (q.2 j) (hq j)
      exact houter.comp (f := fun y : RealEuclidean n ×
          RealEuclidean P.generatorCount ↦ y.2 j)
        (((ContinuousLinearMap.proj (R := ℝ) j).comp
          (ContinuousLinearMap.snd ℝ (RealEuclidean n)
            (RealEuclidean P.generatorCount))).analyticAt q)
  simpa only [MvPolynomial.aeval_eq_eval] using
    (AnalyticAt.aeval_mvPolynomial hv (P.polynomial i)).differentiableAt

/-- The canonical vector of positive graph values is differentiable. -/
theorem differentiableAt_graphValue
    {A : ℝ → ℝ} {n : ℕ} {F : Fin n → RealEuclideanFunction n}
    (P : AbelNumeratorSystemPolynomialPresentation A F)
    (x : RealEuclidean n) :
    DifferentiableAt ℝ P.graphValue x := by
  apply differentiableAt_pi.mpr
  intro j
  exact (differentiableAt_const (c := (1 : ℝ))).add
    ((analyticAt_realEuclideanAffineMap (P.argument j) x).differentiableAt.pow 2)

/-- Canonical graph points lie in the fixed restricted open cylinder with
threshold `1/2`. -/
theorem graphSource_mem_restrictedBaseOpenDomain_half
    {A : ℝ → ℝ} {n : ℕ} {F : Fin n → RealEuclideanFunction n}
    (P : AbelNumeratorSystemPolynomialPresentation A F)
    (x : RealEuclidean n) :
    P.graphSource x ∈ restrictedBaseOpenDomain
      abelNumeratorGraphEmptyBox (1 / 2 : ℝ) := by
  constructor
  · intro j
    change (1 / 2 : ℝ) < 1 + (P.argument j x) ^ 2
    nlinarith [sq_nonneg (P.argument j x)]
  · intro j
    exact Fin.elim0 j

/-- The corresponding weak closed cylinder is contained in the positive
domain of all zero-offset Abel jets. -/
theorem restrictedBaseClosedDomain_half_subset_restrictedAbelJetDomain
    {A : ℝ → ℝ} {n a : ℕ} {F : Fin n → RealEuclideanFunction n}
    (P : AbelNumeratorSystemPolynomialPresentation A F) :
    restrictedBaseClosedDomain (m := P.generatorCount) (a := a)
        abelNumeratorGraphEmptyBox (1 / 2 : ℝ) ⊆
      restrictedAbelJetDomain (a := a) abelNumeratorGraphEmptyBox
        (fun j : Fin P.generatorCount ↦ j)
        (fun j ↦ abelNumeratorGraphZeroOffset j) := by
  intro y hy
  constructor
  · exact hy.2
  · intro j
    change 0 < y.1.1 j + 0
    have hj := hy.1 j
    norm_num at hj ⊢
    linarith

/-- The canonical graph embedding remembers the original point. -/
theorem graphSource_injective
    {A : ℝ → ℝ} {n : ℕ} {F : Fin n → RealEuclideanFunction n}
    (P : AbelNumeratorSystemPolynomialPresentation A F) :
    Function.Injective P.graphSource := by
  intro x y hxy
  exact congrArg Prod.snd hxy

/-- Original regular zeros are exactly the canonical graph points that are
regular zeros of the restricted augmented system. -/
theorem mem_regularZeroSet_constraintMap_iff_restrictedAugmented
    {A : ℝ → ℝ} (hA : IsAbel A)
    {n : ℕ} {F : Fin n → RealEuclideanFunction n}
    (P : AbelNumeratorSystemPolynomialPresentation A F)
    (x : RealEuclidean n) :
    x ∈ regularZeroSet Set.univ (constraintMap F) ↔
      P.graphSource x ∈ regularZeroSet
        (restrictedBaseOpenDomain abelNumeratorGraphEmptyBox (1 / 2 : ℝ))
        (constraintMap P.restrictedAugmentedEquationFamily) := by
  let e := P.productToRestrictedGraphSource
  let q := P.productToRestrictedGraphOutput
  let Ω : Set P.RestrictedGraphSource :=
    restrictedBaseOpenDomain abelNumeratorGraphEmptyBox (1 / 2 : ℝ)
  let L := finiteExplicitGraphLiftSystem
    P.productLiftedNumerator P.graphValue
  have hpositive : ∀ j, 0 < P.graphValue x j := by
    intro j
    change 0 < 1 + (P.argument j x) ^ 2
    positivity
  have hFtilde : DifferentiableAt ℝ P.productLiftedNumerator
      (x, P.graphValue x) :=
    P.differentiableAt_productLiftedNumerator_of_isAbel hA _ hpositive
  have hzeta : DifferentiableAt ℝ P.graphValue x :=
    P.differentiableAt_graphValue x
  have hexplicit :=
    mem_regularZeroSet_finiteExplicitGraphLift_iff
      (Omega := Set.univ) hFtilde hzeta
  have hsubstitution :
      finiteGraphSubstitution P.productLiftedNumerator P.graphValue =
        constraintMap F := by
    funext y
    exact P.productLiftedNumerator_graphValue y
  rw [hsubstitution] at hexplicit
  simp only [Set.preimage_univ] at hexplicit
  have hfun :
      q.symm ∘ constraintMap P.restrictedAugmentedEquationFamily ∘ e = L := by
    funext y
    apply q.injective
    change q (q.symm
      (constraintMap P.restrictedAugmentedEquationFamily (e y))) = q (L y)
    rw [q.apply_symm_apply]
    exact (P.productToRestrictedGraphOutput_explicitGraphLiftSystem y).symm
  have hset := regularZeroSet_preimage_continuousLinearEquiv
    e q.symm Ω (constraintMap P.restrictedAugmentedEquationFamily)
  have hmem := Set.ext_iff.mp hset (x, P.graphValue x)
  rw [hfun] at hmem
  have hdomain : (x, P.graphValue x) ∈ e ⁻¹' Ω := by
    change P.graphSource x ∈
      restrictedBaseOpenDomain abelNumeratorGraphEmptyBox (1 / 2 : ℝ)
    exact P.graphSource_mem_restrictedBaseOpenDomain_half x
  have hrestrict :
      (x, P.graphValue x) ∈ regularZeroSet Set.univ L ↔
        (x, P.graphValue x) ∈ regularZeroSet (e ⁻¹' Ω) L := by
    simp only [regularZeroSet, Set.mem_ofPred_eq, Set.mem_univ, true_and,
      hdomain]
  exact hexplicit.trans (hrestrict.trans (by
    simpa only [e, Ω, productToRestrictedGraphSource_apply,
      graphSource, Set.mem_preimage] using hmem))

end AbelNumeratorSystemPolynomialPresentation

/-- If the restricted level-zero theorem is known uniformly in the number of
representative coordinates, every square Abel numerator system has finitely
many regular zeros. -/
theorem IsAbel.abelNumeratorRegularZeroFinite_of_restrictedBase
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hbase : ∀ m, RestrictedBaseRegularZeroFiniteForRepresentativeCount A m) :
    AbelNumeratorRegularZeroFinite A := by
  intro n F hF
  let P := Classical.choice
    (nonempty_abelNumeratorSystemPolynomialPresentation hF)
  have hfixed : RestrictedBaseRegularZeroFinite A
      abelNumeratorGraphEmptyBox
      (fun j : Fin P.generatorCount ↦ j)
      (fun j ↦ abelNumeratorGraphZeroOffset j) :=
    hbase P.generatorCount abelNumeratorGraphEmptyBox
      (fun j ↦ j) (fun j ↦ abelNumeratorGraphZeroOffset j)
  have hrestricted :
      (regularZeroSet
        (restrictedBaseOpenDomain abelNumeratorGraphEmptyBox (1 / 2 : ℝ))
        (constraintMap P.restrictedAugmentedEquationFamily)).Finite := by
    apply hfixed (a := n) (1 / 2 : ℝ)
      P.restrictedBaseClosedDomain_half_subset_restrictedAbelJetDomain
      P.restrictedAugmentedEquationFamily
    exact P.restrictedAugmentedEquationFamily_mem
  have hset : regularZeroSet Set.univ (constraintMap F) =
      P.graphSource ⁻¹' regularZeroSet
        (restrictedBaseOpenDomain abelNumeratorGraphEmptyBox (1 / 2 : ℝ))
        (constraintMap P.restrictedAugmentedEquationFamily) := by
    ext x
    exact P.mem_regularZeroSet_constraintMap_iff_restrictedAugmented hA x
  rw [hset]
  exact Set.Finite.preimage
    (Set.injOn_of_injective P.graphSource_injective) hrestricted

end AbelFormalization
