import AbelFormalization.CharbonnelClosureDescription
import AbelFormalization.ProjectedZeroComplementCriterion

/-!
# Positive-arity weak structures and Charbonnel generators

This file records the precise positive-dimensional set-family interface used
before the theorem of the complement.  A weak structure has clauses WS1--WS4;
an o-minimal weak structure additionally has the component and closed-lift
clauses WS5--WS6.  `PositiveArityDCAllOrders` is the source-shaped `DC^N`
condition: the hidden arity is fixed, while its `C^N` defining function may
depend on `N`.

There are two deliberate points of terminology.

* `ws2_polynomialSign` uses the project's concrete finite polynomial-sign
  presentation of semialgebraic sets.  It does not appeal to quantifier
  elimination or to an unspecified `Semialgebraic` predicate.
* `ProjectedZeroWeakStructureCertificate` is stronger than the source-shaped
  interface below: it has clauses in arity zero and supplies one globally
  smooth defining function for every differentiability order.

The conversion theorems below forget exactly those strengthenings.  The final
section records only generator-level facts for the Charbonnel closure.  In
particular, this file does not claim WS5, WS6, or `DC^N` for arbitrary
Charbonnel descriptions, and it proves no complement closure.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## The source-shaped positive-arity interfaces -/

/-- The linear equivalence which permutes the coordinates of `ℝⁿ` by `σ`.
The choice of `σ` versus `σ.symm` is immaterial for the WS4 closure clause. -/
def realEuclideanCoordinatePermutation {n : ℕ}
    (σ : Equiv.Perm (Fin n)) :
    RealEuclidean n ≃ₗ[ℝ] RealEuclidean n where
  toFun x i := x (σ i)
  invFun x i := x (σ.symm i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp
  map_add' x y := by
    rfl
  map_smul' c x := by
    rfl

/-- WS1--WS4 for a family indexed only semantically by positive arities.

The `ws2_polynomialSign` field is the maintained concrete presentation of the
source's semialgebraic clause: finite combinations of polynomial equality and
strict-sign conditions.  Its name keeps that representation visible. -/
structure PositiveArityWeakSetStructure (S : EuclideanSetFamily) : Prop where
  ws1_inter : ∀ {n : ℕ}, 0 < n →
    ∀ {A B : Set (RealEuclidean n)}, A ∈ S n → B ∈ S n → A ∩ B ∈ S n
  ws2_polynomialSign : ∀ {n : ℕ}, 0 < n →
    ∀ {A : Set (RealEuclidean n)}, PolynomialSignConstructible n A → A ∈ S n
  ws3_prod : ∀ {n m : ℕ}, 0 < n → 0 < m →
    ∀ {A : Set (RealEuclidean n)} {B : Set (RealEuclidean m)},
      A ∈ S n → B ∈ S m → realEuclideanSetProduct A B ∈ S (n + m)
  ws4_linearEquiv : ∀ {n : ℕ}, 0 < n →
    ∀ {A : Set (RealEuclidean n)}, A ∈ S n →
      ∀ e : RealEuclidean n ≃ₗ[ℝ] RealEuclidean n,
        e '' A ∈ S n

/-- WS1--WS6 in the positive-dimensional form used by the source.

WS5 is stated directly with an extended-cardinal component bound, avoiding a
separate `min ∅ = ∞` convention.  In WS6, writing the larger arity as `n + q`
is equivalent to choosing an `m ≥ n`. -/
structure PositiveArityOMinimalWeakSetStructure
    (S : EuclideanSetFamily) : Prop
    extends PositiveArityWeakSetStructure S where
  ws5_affineSections : ∀ {n : ℕ}, 0 < n →
    ∀ {A : Set (RealEuclidean n)}, A ∈ S n →
      ∃ N : ℕ, ∀ V : AffineSubspace ℝ (RealEuclidean n),
        ENat.card (ConnectedComponents
          ((A ∩ (V : Set (RealEuclidean n))) : Set (RealEuclidean n))) ≤ N
  ws6_closedLift : ∀ {n : ℕ}, 0 < n →
    ∀ {A : Set (RealEuclidean n)}, A ∈ S n →
      ∃ (q : ℕ) (B : Set (RealEuclidean (n + q))),
        IsClosed B ∧ B ∈ S (n + q) ∧
          A = realEuclideanExistentialProjection B

/-- The source-shaped all-orders `DC^N` condition for a positive-arity set
family.  The hidden arity `q` is chosen once for `A`; for each `N`, the
defining function may change.  Membership of a function in the set-family is
expressed by membership of its graph. -/
def PositiveArityDCAllOrders (S : EuclideanSetFamily) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (A : Set (RealEuclidean n)), A ∈ S n →
    ∃ q : ℕ, ∀ N : ℕ,
      ∃ f : RealEuclideanFunction (n + q),
        ContDiff ℝ N f ∧
        realEuclideanGraph f ∈ S ((n + q) + 1) ∧
        A = {x | ∃ z : RealEuclidean q,
          f (realEuclideanAppend x z) = 0}

/-- The two independent source inputs to the theorem of the complement.  This
is only an input package; it contains no assertion that the Charbonnel closure
is complement-closed. -/
structure PositiveArityComplementTheoremInput
    (S : EuclideanSetFamily) : Prop where
  weakStructure : PositiveArityOMinimalWeakSetStructure S
  dcAllOrders : PositiveArityDCAllOrders S

/-! ## Forgetting the stronger projected-zero certificate -/

/-- The project's stronger W1--W6 certificate supplies the exact
positive-arity source interface for the projected-zero base family. -/
theorem ProjectedZeroWeakStructureCertificate.toPositiveArityOMinimalWeakStructure
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (certificate : ProjectedZeroWeakStructureCertificate G) :
    PositiveArityOMinimalWeakSetStructure (projectedZeroSetFamily G) := by
  refine
    { toPositiveArityWeakSetStructure :=
        { ws1_inter := ?_
          ws2_polynomialSign := ?_
          ws3_prod := ?_
          ws4_linearEquiv := ?_ }
      ws5_affineSections := ?_
      ws6_closedLift := ?_ }
  · intro n _hn A B hA hB
    exact certificate.w1_inter hA hB
  · intro n _hn A hA
    exact certificate.w2_polynomialSign hA
  · intro n m _hn _hm A B hA hB
    exact certificate.w3_prod hA hB
  · intro n _hn A hA e
    exact certificate.w4_linearEquiv hA e
  · intro n hn A hA
    exact certificate.w5_affineSections n hn A hA
  · intro n _hn A hA
    obtain ⟨q, B, hclosed, hB, hprojection⟩ :=
      certificate.w6_closedLift hA
    refine ⟨q, B, hclosed, hB, ?_⟩
    simpa only [realEuclideanExistentialProjection] using hprojection

/-- The stronger all-orders certificate forgets to the source-shaped
condition by reusing its one globally smooth function at every order. -/
theorem ProjectedZeroWeakStructureCertificate.toPositiveArityDCAllOrders
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (certificate : ProjectedZeroWeakStructureCertificate G) :
    PositiveArityDCAllOrders (projectedZeroSetFamily G) := by
  intro n _hn A hA
  obtain ⟨q, f, _hf, hsmooth, hgraph, hprojection⟩ :=
    certificate.dc_allOrders n A hA
  refine ⟨q, ?_⟩
  intro N
  exact ⟨f, hsmooth N, hgraph, hprojection⟩

/-- A projected-zero W1--W6/DC certificate therefore gives precisely the
positive-arity input package, without a complement conclusion. -/
theorem ProjectedZeroWeakStructureCertificate.toPositiveArityComplementInput
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (certificate : ProjectedZeroWeakStructureCertificate G) :
    PositiveArityComplementTheoremInput (projectedZeroSetFamily G) :=
  ⟨certificate.toPositiveArityOMinimalWeakStructure,
    certificate.toPositiveArityDCAllOrders⟩

/-- Smoothness and uniform fiber finiteness supply all positive-arity weak
structure and `DC^N` inputs for a geometric projected-zero family. -/
theorem projectedZeroPositiveArityComplementInput
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G) :
    PositiveArityComplementTheoremInput (projectedZeroSetFamily G) :=
  (projectedZeroWeakStructureCertificate hG hsmooth hUFF).toPositiveArityComplementInput

/-- Abel-family specialization of the positive-arity source inputs. -/
theorem IsAbel.projectedZeroPositiveArityComplementInput
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A)) :
    PositiveArityComplementTheoremInput
      (projectedZeroSetFamily (abelGeometricFamily A)) :=
  (hA.projectedZeroWeakStructureCertificate hUFF).toPositiveArityComplementInput

/-! ## Rank-zero generator preservation -/

/-- Any positive-arity base member has a literal rank-zero Charbonnel
description. -/
theorem exists_rank_zero_charbonnelDescription_of_mem
    {S : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    {A : Set (RealEuclidean n)} (hA : A ∈ S n) :
    ∃ description : CharbonnelDescription S n,
      description.carrier = A ∧ description.rank = 0 := by
  exact ⟨.base hn A hA, rfl, rfl⟩

/-- WS1 preserves literal generators, hence rank zero. -/
theorem PositiveArityWeakSetStructure.exists_rank_zero_inter_description
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    {n : ℕ} (hn : 0 < n) {A B : Set (RealEuclidean n)}
    (hA : A ∈ S n) (hB : B ∈ S n) :
    ∃ description : CharbonnelDescription S n,
      description.carrier = A ∩ B ∧ description.rank = 0 :=
  exists_rank_zero_charbonnelDescription_of_mem hn
    (hS.ws1_inter hn hA hB)

/-- WS2 polynomial-sign sets are literal generators, hence rank zero. -/
theorem PositiveArityWeakSetStructure.exists_rank_zero_polynomialSign_description
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : PolynomialSignConstructible n A) :
    ∃ description : CharbonnelDescription S n,
      description.carrier = A ∧ description.rank = 0 :=
  exists_rank_zero_charbonnelDescription_of_mem hn
    (hS.ws2_polynomialSign hn hA)

/-- WS3 preserves literal generators, hence rank zero. -/
theorem PositiveArityWeakSetStructure.exists_rank_zero_prod_description
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {A : Set (RealEuclidean n)} {B : Set (RealEuclidean m)}
    (hA : A ∈ S n) (hB : B ∈ S m) :
    ∃ description : CharbonnelDescription S (n + m),
      description.carrier = realEuclideanSetProduct A B ∧
        description.rank = 0 :=
  exists_rank_zero_charbonnelDescription_of_mem (by omega)
    (hS.ws3_prod hn hm hA hB)

/-- Source WS4 linear equivalences preserve literal generators. -/
theorem PositiveArityWeakSetStructure.exists_rank_zero_linearEquiv_description
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ S n) (e : RealEuclidean n ≃ₗ[ℝ] RealEuclidean n) :
    ∃ description : CharbonnelDescription S n,
      description.carrier = e '' A ∧
        description.rank = 0 :=
  exists_rank_zero_charbonnelDescription_of_mem hn
    (hS.ws4_linearEquiv hn hA e)

/-- Coordinate permutations are the special case of source WS4 used by the
coordinate-reindexing constructions. -/
theorem PositiveArityWeakSetStructure.exists_rank_zero_coordinatePermutation_description
    {S : EuclideanSetFamily} (hS : PositiveArityWeakSetStructure S)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ S n) (σ : Equiv.Perm (Fin n)) :
    ∃ description : CharbonnelDescription S n,
      description.carrier = realEuclideanCoordinatePermutation σ '' A ∧
        description.rank = 0 :=
  hS.exists_rank_zero_linearEquiv_description hn hA
    (realEuclideanCoordinatePermutation σ)

/-- The stronger project W4 also makes every linear-equivalence image a
rank-zero projected-zero generator. -/
theorem ProjectedZeroWeakStructureCertificate.exists_rank_zero_linearEquiv_description
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (certificate : ProjectedZeroWeakStructureCertificate G)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : IsProjectedZeroSet G A)
    (e : RealEuclidean n ≃ₗ[ℝ] RealEuclidean n) :
    ∃ description : CharbonnelDescription (projectedZeroSetFamily G) n,
      description.carrier = e '' A ∧ description.rank = 0 :=
  IsProjectedZeroSet.exists_rank_zero_charbonnelDescription hn
    (certificate.w4_linearEquiv hA e)

/-- WS6 can choose a closed lift which remains a literal rank-zero generator
inside the Charbonnel closure. -/
theorem PositiveArityOMinimalWeakSetStructure.exists_closed_rank_zero_lift
    {S : EuclideanSetFamily}
    (hS : PositiveArityOMinimalWeakSetStructure S)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ S n) :
    ∃ (q : ℕ) (B : Set (RealEuclidean (n + q)))
      (description : CharbonnelDescription S (n + q)),
      IsClosed B ∧ description.carrier = B ∧ description.rank = 0 ∧
        A = realEuclideanExistentialProjection B := by
  obtain ⟨q, B, hclosed, hB, hprojection⟩ := hS.ws6_closedLift hn hA
  obtain ⟨description, hcarrier, hrank⟩ :=
    exists_rank_zero_charbonnelDescription_of_mem (S := S) (by omega) hB
  exact ⟨q, B, description, hclosed, hcarrier, hrank, hprojection⟩

/-- The source-shaped `DC^N` witnesses have rank-zero graph descriptions in
the Charbonnel closure.  The function is still allowed to depend on `N`. -/
theorem PositiveArityDCAllOrders.exists_rank_zero_graph_descriptions
    {S : EuclideanSetFamily} (hDC : PositiveArityDCAllOrders S)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ S n) :
    ∃ q : ℕ, ∀ N : ℕ,
      ∃ (f : RealEuclideanFunction (n + q))
        (description : CharbonnelDescription S ((n + q) + 1)),
        ContDiff ℝ N f ∧
        description.carrier = realEuclideanGraph f ∧
        description.rank = 0 ∧
        A = {x | ∃ z : RealEuclidean q,
          f (realEuclideanAppend x z) = 0} := by
  obtain ⟨q, hq⟩ := hDC n hn A hA
  refine ⟨q, ?_⟩
  intro N
  obtain ⟨f, hsmooth, hgraph, hprojection⟩ := hq N
  obtain ⟨description, hcarrier, hrank⟩ :=
    exists_rank_zero_charbonnelDescription_of_mem (S := S) (by omega) hgraph
  exact ⟨f, description, hsmooth, hcarrier, hrank, hprojection⟩

/-! ## The four explicit Charbonnel operations -/

/-- Specialized name for binary-union closure of the projected-zero
Charbonnel family. -/
theorem projectedZeroCharbonnelClosure_union
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {n : ℕ} {A B : Set (RealEuclidean n)}
    (hA : A ∈ projectedZeroCharbonnelClosure G n)
    (hB : B ∈ projectedZeroCharbonnelClosure G n) :
    A ∪ B ∈ projectedZeroCharbonnelClosure G n :=
  charbonnelClosure_union hA hB

/-- Specialized name for intersection with an integer-affine set. -/
theorem projectedZeroCharbonnelClosure_integerAffineInter
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {n : ℕ} {A L : Set (RealEuclidean n)}
    (hA : A ∈ projectedZeroCharbonnelClosure G n)
    (hL : IsIntegerAffineSet L) :
    A ∩ L ∈ projectedZeroCharbonnelClosure G n :=
  charbonnelClosure_integerAffineInter hA hL

/-- Specialized name for positive-target coordinate projection. -/
theorem projectedZeroCharbonnelClosure_projection
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {n k : ℕ} (hn : 0 < n) {A : Set (RealEuclidean (n + k))}
    (hA : A ∈ projectedZeroCharbonnelClosure G (n + k)) :
    realEuclideanExistentialProjection A ∈
      projectedZeroCharbonnelClosure G n :=
  charbonnelClosure_projection hn hA

/-- Specialized name for topological-closure preservation. -/
theorem projectedZeroCharbonnelClosure_topologicalClosure
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {n : ℕ} {A : Set (RealEuclidean n)}
    (hA : A ∈ projectedZeroCharbonnelClosure G n) :
    closure A ∈ projectedZeroCharbonnelClosure G n :=
  charbonnelClosure_topologicalClosure hA

/-- The projected-zero Charbonnel family also has no zero-arity members. -/
theorem projectedZeroCharbonnelClosure_zero
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) :
    projectedZeroCharbonnelClosure G 0 = ∅ :=
  charbonnelClosure_zero (projectedZeroSetFamily G)

end AbelFormalization
