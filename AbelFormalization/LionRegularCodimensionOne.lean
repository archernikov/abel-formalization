import AbelFormalization.SmoothRegularZeroBridge
import AbelFormalization.SquaredDistanceGenericMorse
import AbelFormalization.SquaredDistanceProper
import AbelFormalization.RegularConstraintFiber
import AbelFormalization.RestrictedAdjunctionClosedness
import AbelFormalization.AbelGeometricRegularZero

/-!
# The regular codimension-one part of Lion's finiteness argument

This file records the part of the Lion--Ambrozy passage that follows from the
available differential-topology pipeline.  For a globally smooth geometric
family closed under coordinate differentiation, `0`-regularity forces every
everywhere-regular codimension-one fiber to have finitely many connected
components.

The proof uses the existing generic squared-distance critical system.  Its
components remain in the function family, so `0`-regularity makes its regular
zero set finite.  Properness of squared distance and the implicit-function
local connectedness theorem then give finite connected components.

This is a pointwise statement for one fiber.  The further passage to one bound
uniform in the target, and the rank-stratification needed for singular and
higher-codimension fibers, are precisely the remaining content of Lion's UFF
theorem; they are not consequences of the topology lemmas alone.
-/

noncomputable section

open Set Function Filter
open scoped BigOperators ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

theorem IsGeometricFunctionFamily.finset_sum_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    {I : Type*} (s : Finset I) (f : I → RealEuclideanFunction n)
    (hf : ∀ i ∈ s, f i ∈ G n) :
    (∑ i ∈ s, f i) ∈ G n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hG.zero_mem (n := n)
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact hG.add (hf i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

theorem IsGeometricFunctionFamily.finset_prod_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    {I : Type*} (s : Finset I) (f : I → RealEuclideanFunction n)
    (hf : ∀ i ∈ s, f i ∈ G n) :
    (∏ i ∈ s, f i) ∈ G n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hG.one_mem (n := n)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact hG.mul (hf i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- Determinants of finite square matrices of family members remain in a
geometric family. -/
theorem IsGeometricFunctionFamily.matrix_det_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (RealEuclideanFunction n))
    (hM : ∀ i j, M i j ∈ G n) :
    Matrix.det M ∈ G n := by
  rw [Matrix.det_apply']
  apply hG.finset_sum_mem Finset.univ
  intro σ hσ
  apply hG.mul
  · exact hG.const_mem ((Equiv.Perm.sign σ : ℤ) : ℝ)
  · apply hG.finset_prod_mem Finset.univ
    intro i hi
    exact hM (σ i) i

/-- The Jacobian determinant of a square tuple belongs to a
coordinate-derivative-closed geometric family. -/
theorem IsGeometricFunctionFamily.standardJacobianDeterminant_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {n : ℕ} (F : Fin n → RealEuclideanFunction n)
    (hF : ∀ i, F i ∈ G n) :
    (fun x ↦ Matrix.det (fun i j ↦
      fderiv ℝ (F i) x ((Pi.basisFun ℝ (Fin n)) j))) ∈ G n := by
  let M : Matrix (Fin n) (Fin n) (RealEuclideanFunction n) :=
    fun i j x ↦ fderiv ℝ (F i) x ((Pi.basisFun ℝ (Fin n)) j)
  have hM : ∀ i j, M i j ∈ G n := by
    intro i j
    simpa only [M, Pi.basisFun_apply] using hderiv n (F i) (hF i) j
  have hdet := hG.matrix_det_mem M hM
  convert hdet using 1
  funext x
  change Matrix.det
      ((Pi.evalRingHom (fun _ : RealEuclidean n ↦ ℝ) x).mapMatrix M) =
    (Pi.evalRingHom (fun _ : RealEuclidean n ↦ ℝ) x) (Matrix.det M)
  exact ((Pi.evalRingHom (fun _ : RealEuclidean n ↦ ℝ) x).map_det M).symm

/-- Squared distance in standard coordinates belongs to every geometric
family. -/
theorem IsGeometricFunctionFamily.standardSquaredDistance_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    (center : Fin n → ℝ) :
    algebraicSquaredDistance
      (fun i x ↦ (Pi.basisFun ℝ (Fin n)).equivFun x i) center ∈ G n := by
  unfold algebraicSquaredDistance
  apply hG.finset_sum_mem Finset.univ
  intro i hi
  apply hG.sq_mem
  apply hG.sub_mem
  · simpa using hG.polynomial (MvPolynomial.X i)
  · exact hG.const_mem (center i)

/-- The squared-distance critical equation for a codimension-one tuple stays
in a geometric, coordinate-derivative-closed family. -/
theorem IsGeometricFunctionFamily.squaredDistanceCriticalEquation_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {r : ℕ} (H : Fin r → RealEuclideanFunction (r + 1))
    (hH : ∀ i, H i ∈ G (r + 1))
    (center : Fin (r + 1) → ℝ) :
    squaredDistanceCriticalEquation H (Pi.basisFun ℝ (Fin (r + 1))) center ∈
      G (r + 1) := by
  let B := Pi.basisFun ℝ (Fin (r + 1))
  let rho := algebraicSquaredDistance (fun i x ↦ B.equivFun x i) center
  have hrho : rho ∈ G (r + 1) := by
    simpa only [B, rho] using hG.standardSquaredDistance_mem center
  have htuple : ∀ i, functionTupleSnoc H rho i ∈ G (r + 1) := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [functionTupleSnoc_last] using hrho
    · simpa only [functionTupleSnoc_castSucc] using hH j
  have hdet := hG.standardJacobianDeterminant_mem hderiv
    (functionTupleSnoc H rho) htuple
  change (fun x ↦ Matrix.det (fun i j ↦
    fderiv ℝ (functionTupleSnoc H rho i) x (B j))) ∈ G (r + 1)
  exact hdet

/-- `0`-regularity controls the regular-zero set of every square tuple in the
family. -/
theorem IsZeroRegularFunctionFamily.regularZeroSet_univ_finite
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hzero : IsZeroRegularFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ} (F : RealEuclidean n → RealEuclidean n)
    (hF : FunctionTupleInFamily G F) :
    (regularZeroSet Set.univ F).Finite := by
  have hFcont : ContDiff ℝ 1 F := by
    rw [contDiff_pi]
    intro i
    exact (hsmooth n (fun x ↦ F x i) (hF i)).of_le (by simp)
  have hfinite := hzero n F hF (0 : RealEuclidean n)
  rw [smoothRegularFiber_eq_regularZeroSet_univ_sub F hFcont 0] at hfinite
  simpa using hfinite

/-- Every closed regular codimension-one locus locally cut out by members of
the family has finitely many connected components.  This is the reusable
geometric core: the locus need not be the entire global zero set. -/
theorem finite_connectedComponents_closed_regular_codimensionOne_locus
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    {r : ℕ} {M : Set (RealEuclidean (r + 1))}
    (hMclosed : IsClosed M)
    (H : Fin r → RealEuclideanFunction (r + 1))
    (hHmem : ∀ i, H i ∈ G (r + 1))
    (hMzero : ∀ x ∈ M, ∀ i, H i x = 0)
    (hlocalConstraint : ∀ x : M, ∃ U ∈ nhds (x : RealEuclidean (r + 1)),
      U ∩ {y | ∀ i, H i y = H i x} ⊆ M)
    (hsurj : ∀ x ∈ M, (constraintFDeriv H x).range = ⊤) :
    Finite (ConnectedComponents M) := by
  let B : Module.Basis (Fin (r + 1)) ℝ (RealEuclidean (r + 1)) :=
    Pi.basisFun ℝ (Fin (r + 1))
  have hHinf : ∀ i, ContDiff ℝ ∞ (H i) :=
    fun i ↦ hsmooth (r + 1) (H i) (hHmem i)
  have hHtwo : ∀ x ∈ M, ∀ i, ContDiffAt ℝ 2 (H i) x := by
    intro x hx i
    exact (hHinf i).contDiffAt.of_le (by simp)
  obtain ⟨center, hcenter⟩ :=
    exists_squaredDistanceCenter_regular_criticalSystem M H B
      hMzero hHtwo hsurj
  let rho : RealEuclideanFunction (r + 1) :=
    algebraicSquaredDistance (fun i x ↦ B.equivFun x i) center
  let K : RealEuclideanFunction (r + 1) :=
    squaredDistanceCriticalEquation H B center
  let criticalMap : RealEuclidean (r + 1) → RealEuclidean (r + 1) :=
    criticalSystemMap H K
  have hrhomem : rho ∈ G (r + 1) := by
    simpa only [rho, B] using hG.standardSquaredDistance_mem center
  have hKmem : K ∈ G (r + 1) := by
    simpa only [K, B] using
      hG.squaredDistanceCriticalEquation_mem hderiv H hHmem center
  have hcriticalMem : FunctionTupleInFamily G criticalMap := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [criticalMap, criticalSystemMap_apply_last] using hKmem
    · simpa only [criticalMap, criticalSystemMap_apply_castSucc] using hHmem j
  have hregularFinite : (regularZeroSet Set.univ criticalMap).Finite :=
    hzero.regularZeroSet_univ_finite hsmooth criticalMap hcriticalMem
  have hrhoinf : ContDiff ℝ ∞ rho :=
    hsmooth (r + 1) rho hrhomem
  have hcompact : ∀ R : ℝ, IsCompact {x : M | rho (x : RealEuclidean (r + 1)) ≤ R} := by
    intro R
    apply isCompact_subtype_sublevel_of_isClosed hMclosed rho
    intro c
    simpa only [rho] using
      isCompact_algebraicSquaredDistance_basis_sublevel B center c
  apply finite_connectedComponents_of_finite_regularCriticalSystem_of_surjectiveConstraint
    H rho B criticalMap hrhoinf.continuous hcompact hregularFinite
  · intro x hxcritical
    have hxK : K x = 0 := by
      change criticalDeterminant H rho B x = 0 at hxcritical
      exact hxcritical
    refine ⟨Set.mem_univ _, ?_, ?_⟩
    · funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa only [criticalMap, criticalSystemMap_apply_last, Pi.zero_apply] using hxK
      · simpa only [criticalMap, criticalSystemMap_apply_castSucc, Pi.zero_apply] using
          hMzero x x.property j
    · exact LinearMap.range_eq_top.mp
        (by simpa only [criticalMap, K] using hcenter x x.property hxK)
  · exact hlocalConstraint
  · intro x
    exact hsurj x x.property
  · intro x i
    exact (hHinf i).contDiffAt.hasStrictFDerivAt (by norm_num)
  · intro x
    exact hrhoinf.contDiffAt.hasStrictFDerivAt (by norm_num)

/-- Every regular codimension-one zero locus cut out by members of the family
has finitely many connected components. -/
theorem finite_connectedComponents_zeroLocus_codimensionOne
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    {r : ℕ} (H : Fin r → RealEuclideanFunction (r + 1))
    (hHmem : ∀ i, H i ∈ G (r + 1))
    (hsurj : ∀ x, (∀ i, H i x = 0) →
      (constraintFDeriv H x).range = ⊤) :
    Finite (ConnectedComponents {x | ∀ i, H i x = 0}) := by
  let M : Set (RealEuclidean (r + 1)) := {x | ∀ i, H i x = 0}
  have hHinf : ∀ i, ContDiff ℝ ∞ (H i) :=
    fun i ↦ hsmooth (r + 1) (H i) (hHmem i)
  have hMclosed : IsClosed M := by
    have hmapContinuous : Continuous (constraintMap H) :=
      continuous_pi fun i ↦ (hHinf i).continuous
    have hMeq : M = constraintMap H ⁻¹' {(0 : Fin r → ℝ)} := by
      ext x
      simp only [M, Set.mem_ofPred_eq, Set.mem_preimage,
        Set.mem_singleton_iff]
      exact ⟨fun hx ↦ funext hx, fun hx i ↦ congrFun hx i⟩
    rw [hMeq]
    exact isClosed_singleton.preimage hmapContinuous
  change Finite (ConnectedComponents M)
  apply finite_connectedComponents_closed_regular_codimensionOne_locus
    hG hsmooth hderiv hzero hMclosed H hHmem
  · intro x hx i
    exact hx i
  · intro x
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    intro y hy
    exact fun i ↦ (hy.2 i).trans (x.property i)
  · intro x hx
    exact hsurj x hx

/-- A fiber of a family map from `ℝ^(r+1)` to `ℝ^r` has finitely many
connected components when the derivative is surjective at every point of that
fiber. -/
theorem finite_connectedComponents_fiber_of_surjective_codimensionOne
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    {r : ℕ} (g : RealEuclidean (r + 1) → RealEuclidean r)
    (hg : FunctionTupleInFamily G g) (t : RealEuclidean r)
    (hsurj : ∀ x, g x = t → Function.Surjective (fderiv ℝ g x)) :
    Finite (ConnectedComponents (g ⁻¹' {t})) := by
  let H : Fin r → RealEuclideanFunction (r + 1) :=
    fun i x ↦ g x i - t i
  have hHmem : ∀ i, H i ∈ G (r + 1) := by
    intro i
    exact hG.sub_mem (hg i) (hG.const_mem (t i))
  have hgInf : ContDiff ℝ ∞ g := by
    rw [contDiff_pi]
    intro i
    exact hsmooth (r + 1) (fun x ↦ g x i) (hg i)
  have hHdiff : ∀ x i, DifferentiableAt ℝ (H i) x := by
    intro x i
    exact (hsmooth (r + 1) (H i) (hHmem i)).differentiable (by simp)
      |>.differentiableAt
  have hconstraint : ∀ x, (∀ i, H i x = 0) →
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
        constraintFDeriv H x = fderiv ℝ (constraintMap H) x := htupleDeriv.symm
        _ = fderiv ℝ (fun y ↦ g y - t) x := by rfl
        _ = fderiv ℝ g x := by rw [fderiv_sub_const]
    rw [hderivEq]
    exact LinearMap.range_eq_top.mpr (hsurj x hgxt)
  have hfinite := finite_connectedComponents_zeroLocus_codimensionOne
    hG hsmooth hderiv hzero H hHmem hconstraint
  have hset : {x | ∀ i, H i x = 0} = g ⁻¹' {t} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      funext i
      exact sub_eq_zero.mp (hx i)
    · intro hx i
      exact sub_eq_zero.mpr (congrFun hx i)
  rwa [hset] at hfinite

/-- The preceding finiteness statement in the cardinal form used by
`HasUniformFiberFiniteness`.  The bound here is for the specified target. -/
theorem exists_component_bound_fiber_of_surjective_codimensionOne
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    {r : ℕ} (g : RealEuclidean (r + 1) → RealEuclidean r)
    (hg : FunctionTupleInFamily G g) (t : RealEuclidean r)
    (hsurj : ∀ x, g x = t → Function.Surjective (fderiv ℝ g x)) :
    ∃ N : ℕ, ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ N := by
  let _ : Finite (ConnectedComponents (g ⁻¹' {t})) :=
    finite_connectedComponents_fiber_of_surjective_codimensionOne
      hG hsmooth hderiv hzero g hg t hsurj
  refine ⟨Nat.card (ConnectedComponents (g ⁻¹' {t})), ?_⟩
  rw [ENat.card_eq_coe_natCard]

/-- For an everywhere-submersive codimension-one family map, the four Lion
hypotheses give a (possibly target-dependent) natural component bound for
every fiber.  Full UFF is the stronger quantifier order `∃ N, ∀ t`. -/
theorem forall_exists_component_bound_of_surjective_codimensionOne
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    {r : ℕ} (g : RealEuclidean (r + 1) → RealEuclidean r)
    (hg : FunctionTupleInFamily G g)
    (hsurj : ∀ x, Function.Surjective (fderiv ℝ g x)) :
    ∀ t, ∃ N : ℕ, ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ N := by
  intro t
  exact exists_component_bound_fiber_of_surjective_codimensionOne
    hG hsmooth hderiv hzero g hg t (fun x hx ↦ hsurj x)

/-- The pointwise codimension-one conclusion for the concrete localized Abel
family, once its already-separated `0`-regularity input is available. -/
theorem IsAbel.finite_connectedComponents_abelGeometricFiber_of_surjective_codimensionOne
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hzero : IsZeroRegularFunctionFamily (abelGeometricFamily A))
    {r : ℕ} (g : RealEuclidean (r + 1) → RealEuclidean r)
    (hg : FunctionTupleInFamily (abelGeometricFamily A) g)
    (t : RealEuclidean r)
    (hsurj : ∀ x, g x = t → Function.Surjective (fderiv ℝ g x)) :
    Finite (ConnectedComponents (g ⁻¹' {t})) := by
  exact finite_connectedComponents_fiber_of_surjective_codimensionOne
    (isGeometricFunctionFamily_abelGeometricFamily A)
    hA.isEverywhereSmooth_abelGeometricFamily
    hA.isCoordinateDerivativeClosed_abelGeometricFamily
    hzero g hg t hsurj

/-- Numerator-level regular-zero finiteness therefore already gives the same
pointwise codimension-one conclusion for the concrete Abel family. -/
theorem IsAbel.finite_connectedComponents_abelGeometricFiber_of_numerator
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hfinite : AbelNumeratorRegularZeroFinite A)
    {r : ℕ} (g : RealEuclidean (r + 1) → RealEuclidean r)
    (hg : FunctionTupleInFamily (abelGeometricFamily A) g)
    (t : RealEuclidean r)
    (hsurj : ∀ x, g x = t → Function.Surjective (fderiv ℝ g x)) :
    Finite (ConnectedComponents (g ⁻¹' {t})) := by
  exact hA.finite_connectedComponents_abelGeometricFiber_of_surjective_codimensionOne
    (hA.isZeroRegular_abelGeometricFamily_of_numerator hfinite) g hg t hsurj

end AbelFormalization
