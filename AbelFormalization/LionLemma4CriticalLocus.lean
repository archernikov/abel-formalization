import AbelFormalization.LionLemma4CriticalCarpet
import AbelFormalization.LionCarpetedLeafFiber
import AbelFormalization.LagrangeCriticalDeterminant

/-!
# The critical locus in Lion's Lemma 4

After replacing the carpet by `delta'_a`, Lion appends its differential to
the form detecting regularity of `(f,g)`.  In coordinates, the coefficients
of

`theta_a = df_1 ∧ ... ∧ df_q ∧ dg_1 ∧ ... ∧ dg_p ∧ d(delta'_a)`

are the maximal column minors of the Jacobian of `(f,g,delta'_a)`.  This file
constructs those coefficient functions, proves that they remain in the
geometric family, and identifies their common zero locus with failure of
surjectivity of the appended derivative.  It also proves the critical-point
step used in Lemma 4: every connected component of a regular fiber contains
a carpet maximizer in that common zero locus.
-/

noncomputable section

open Set Function Filter
open scoped BigOperators ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

namespace LionCarpetedLeaf

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)} {n q p : ℕ}

/-- The coordinate tuple `(f,g,delta'_a)` whose derivative represents
Lion's form `theta_a`. -/
def criticalAugmentedTuple
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ) :
    RealEuclidean n → RealEuclidean ((q + p) + 1) :=
  fun x i ↦ functionTupleSnoc
    (fun k y ↦ L.definingTupleAppend g y k)
    (L.criticalCarpet g center height) i x

@[simp]
theorem criticalAugmentedTuple_castSucc
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ)
    (x : RealEuclidean n) (i : Fin (q + p)) :
    L.criticalAugmentedTuple g center height x i.castSucc =
      L.definingTupleAppend g x i := by
  simp [criticalAugmentedTuple]

@[simp]
theorem criticalAugmentedTuple_last
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ)
    (x : RealEuclidean n) :
    L.criticalAugmentedTuple g center height x (Fin.last (q + p)) =
      L.criticalCarpet g center height x := by
  simp [criticalAugmentedTuple]

/-- Every coordinate of `(f,g,delta'_a)` remains in the geometric family. -/
theorem criticalAugmentedTuple_mem
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    FunctionTupleInFamily G
      (L.criticalAugmentedTuple g center height) := by
  intro i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · have hlast := L.criticalCarpet_mem hG hderiv center hheight g hg
    convert hlast using 1
    funext x
    exact L.criticalAugmentedTuple_last g center height x
  · simpa [criticalAugmentedTuple] using
      L.definingTupleAppend_mem g hg k

/-- One coordinate coefficient of `theta_a`, indexed by a choice of source
columns. -/
def criticalCoefficient
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ)
    (cols : Fin ((q + p) + 1) ↪ Fin n) :
    RealEuclideanFunction n :=
  standardJacobianColumnMinor
    (L.criticalAugmentedTuple g center height) cols

/-- Every coefficient of `theta_a` belongs to the family. -/
theorem criticalCoefficient_mem
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (cols : Fin ((q + p) + 1) ↪ Fin n) :
    L.criticalCoefficient g center height cols ∈ G n := by
  exact hG.standardJacobianColumnMinor_mem hderiv
    (L.criticalAugmentedTuple g center height)
    (L.criticalAugmentedTuple_mem hG hderiv g hg center hheight) cols

/-- The squared coordinate norm of `theta_a`.  Its zero set is the common
zero set of all critical coefficients. -/
def criticalMinorSum
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ) :
    RealEuclideanFunction n :=
  fun x ↦ ∑ cols : Fin ((q + p) + 1) ↪ Fin n,
    L.criticalCoefficient g center height cols x ^ 2

theorem criticalMinorSum_nonneg
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ) (x : RealEuclidean n) :
    0 ≤ L.criticalMinorSum g center height x := by
  exact Finset.sum_nonneg fun cols _ ↦
    sq_nonneg (L.criticalCoefficient g center height cols x)

theorem criticalMinorSum_eq_zero_iff
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ) (x : RealEuclidean n) :
    L.criticalMinorSum g center height x = 0 ↔
      ∀ cols : Fin ((q + p) + 1) ↪ Fin n,
        L.criticalCoefficient g center height cols x = 0 := by
  classical
  rw [criticalMinorSum]
  constructor
  · intro hzero cols
    exact ((Finset.sum_sq_eq_zero_iff Finset.univ
      (fun c : Fin ((q + p) + 1) ↪ Fin n ↦
        L.criticalCoefficient g center height c x)).1 hzero)
      cols (Finset.mem_univ cols)
  · intro hzero
    exact (Finset.sum_sq_eq_zero_iff Finset.univ
      (fun c : Fin ((q + p) + 1) ↪ Fin n ↦
        L.criticalCoefficient g center height c x)).2
      (fun cols _ ↦ hzero cols)

/-- The squared norm of `theta_a` remains in the function family. -/
theorem criticalMinorSum_mem
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height) :
    L.criticalMinorSum g center height ∈ G n := by
  classical
  have hsum := hG.finset_sum_mem
    (Finset.univ : Finset (Fin ((q + p) + 1) ↪ Fin n))
    (fun cols ↦ fun x ↦
      L.criticalCoefficient g center height cols x ^ 2)
    (by
      intro cols _
      exact hG.sq_mem
        (L.criticalCoefficient_mem hG hderiv g hg center hheight cols))
  convert hsum using 1
  funext x
  simp only [criticalMinorSum, Finset.sum_apply]

/-- Pointwise zero-locus/rank identification for Lion's `theta_a`. -/
theorem criticalMinorSum_eq_zero_iff_not_surjective
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (x : RealEuclidean n) :
    L.criticalMinorSum g center height x = 0 ↔
      ¬ Function.Surjective
        (fderiv ℝ (L.criticalAugmentedTuple g center height) x) := by
  rw [L.criticalMinorSum_eq_zero_iff g center height x]
  have hrank :=
    hsmooth.fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
      (L.criticalAugmentedTuple g center height)
      (L.criticalAugmentedTuple_mem hG hderiv g hg center hheight) x
  constructor
  · intro hzero hsurj
    obtain ⟨cols, hcols⟩ := hrank.mp hsurj
    exact hcols (hzero cols)
  · intro hnonsurj cols
    by_contra hcols
    apply hnonsurj
    exact hrank.mpr ⟨cols, hcols⟩

/-- The ambient zero locus of Lion's form `theta_a`. -/
def criticalLocus
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ) : Set (RealEuclidean n) :=
  {x | L.criticalMinorSum g center height x = 0}

theorem mem_criticalLocus_iff_not_surjective
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (x : RealEuclidean n) :
    x ∈ L.criticalLocus g center height ↔
      ¬ Function.Surjective
        (fderiv ℝ (L.criticalAugmentedTuple g center height) x) := by
  exact L.criticalMinorSum_eq_zero_iff_not_surjective
    hG hsmooth hderiv g hg center hheight x

/-- Lion's `S_a`: the trace of the zero locus of `theta_a` on `X'`. -/
def criticalTrace
    (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (center : RealEuclidean n) (height : ℝ) : Set (RealEuclidean n) :=
  (L.carrier ∩ L.regularLocus g) ∩ L.criticalLocus g center height

theorem mem_criticalTrace_iff
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (x : RealEuclidean n) :
    x ∈ L.criticalTrace g center height ↔
      x ∈ L.carrier ∩ L.regularLocus g ∧
        ¬ Function.Surjective
          (fderiv ℝ (L.criticalAugmentedTuple g center height) x) := by
  rw [criticalTrace, Set.mem_inter_iff,
    L.mem_criticalLocus_iff_not_surjective
      hG hsmooth hderiv g hg center hheight x]

/-! ## Component maxima are critical -/

/-- On a regular leaf fiber, a componentwise carpet maximum is a constrained
local maximum in the ambient source. -/
theorem carpet_isLocalMaxOn_definingTupleFiber_of_componentMaximizer
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (t : RealEuclidean p) (x : L.fiber g t)
    (hmax : x ∈ componentMaximizers
      (fun z : L.fiber g t ↦ L.delta z))
    (hsurj : Function.Surjective
      (fderiv ℝ (L.definingTupleAppend g) x)) :
    IsLocalMaxOn L.delta
      {y | ∀ i, L.definingTupleAppend g y i =
        L.definingTupleAppend g x i} x := by
  let H : Fin (q + p) → RealEuclideanFunction n :=
    fun i y ↦ L.definingTupleAppend g y i
  have hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x := by
    intro i
    exact (hsmooth n (H i) (L.definingTupleAppend_mem g hg i)).contDiffAt
      |>.hasStrictFDerivAt (by norm_num)
  have hmapDeriv :
      fderiv ℝ (L.definingTupleAppend g) x = constraintFDeriv H x := by
    have hdiff : ∀ i, DifferentiableAt ℝ (H i) x :=
      fun i ↦ (hH i).differentiableAt
    change fderiv ℝ (fun y i ↦ H i y) x = constraintFDeriv H x
    simpa only [constraintFDeriv] using fderiv_pi hdiff
  have hsurjRange : (constraintFDeriv H x).range = ⊤ := by
    rw [← hmapDeriv]
    exact LinearMap.range_eq_top.mpr hsurj
  have hlocalConstraint : ∃ V ∈ 𝓝 (x : RealEuclidean n),
      V ∩ {y | ∀ i, H i y = H i x} ⊆ L.fiber g t := by
    refine ⟨L.U, L.isOpen_U.mem_nhds ?_, ?_⟩
    · exact (L.mem_fiber_iff g t x).mp x.property |>.1
    · intro y hy
      have hxFiber := (L.mem_fiber_iff g t x).mp x.property
      have hfeq : L.equations y = L.equations x := by
        funext i
        simpa only [H, L.definingTupleAppend_castAdd] using
          hy.2 (Fin.castAdd p i)
      have hgeq : g y = g x := by
        funext j
        simpa only [H, L.definingTupleAppend_natAdd] using
          hy.2 (Fin.natAdd q j)
      exact (L.mem_fiber_iff g t y).mpr
        ⟨hy.1, hfeq.trans hxFiber.2.1, hgeq.trans hxFiber.2.2⟩
  simpa only [H] using
    componentMaximizer_isLocalMaxOn_of_surjectiveConstraint
      H L.delta x hmax hH hsurjRange hlocalConstraint

/-- Every maximal column coefficient of `theta_a` vanishes at a constrained
local maximum of `delta'_a`. -/
theorem criticalCoefficient_eq_zero_of_isLocalMaxOn
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (x : RealEuclidean n)
    (hlocal : IsLocalMaxOn (L.criticalCarpet g center height)
      {y | ∀ i, L.definingTupleAppend g y i =
        L.definingTupleAppend g x i} x)
    (cols : Fin ((q + p) + 1) ↪ Fin n) :
    L.criticalCoefficient g center height cols x = 0 := by
  let H : Fin (q + p) → RealEuclideanFunction n :=
    fun i y ↦ L.definingTupleAppend g y i
  let rho := L.criticalCarpet g center height
  have hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x := by
    intro i
    exact (hsmooth n (H i) (L.definingTupleAppend_mem g hg i)).contDiffAt
      |>.hasStrictFDerivAt (by norm_num)
  have hrho : HasStrictFDerivAt rho (fderiv ℝ rho x) x :=
    (hsmooth n rho
      (L.criticalCarpet_mem hG hderiv center hheight g hg)).contDiffAt
        |>.hasStrictFDerivAt (by norm_num)
  have hzero := criticalSystemDeterminant_eq_zero_of_isLocalExtrOn
    H rho x (fun j ↦ (Pi.basisFun ℝ (Fin n)) (cols j))
    (Or.inr hlocal) hH hrho
  change Matrix.det (fun i j ↦
    fderiv ℝ
      (fun y ↦ L.criticalAugmentedTuple g center height y i) x
      ((Pi.basisFun ℝ (Fin n)) (cols j))) = 0
  simpa only [criticalAugmentedTuple, H, rho] using hzero

/-- A constrained local maximum lies in the zero locus of `theta_a`. -/
theorem mem_criticalLocus_of_isLocalMaxOn
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (x : RealEuclidean n)
    (hlocal : IsLocalMaxOn (L.criticalCarpet g center height)
      {y | ∀ i, L.definingTupleAppend g y i =
        L.definingTupleAppend g x i} x) :
    x ∈ L.criticalLocus g center height := by
  exact (L.criticalMinorSum_eq_zero_iff g center height x).2
    (fun cols ↦ L.criticalCoefficient_eq_zero_of_isLocalMaxOn
      hG hsmooth hderiv g hg center hheight x hlocal cols)

/-- A component maximizer of `delta'_a` on a regular fiber belongs to
Lion's critical zero locus. -/
theorem componentMaximizer_mem_criticalLocus
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (t : RealEuclidean p)
    (x : (L.criticalLeaf hG hsmooth hderiv center hheight g hg).fiber g t)
    (hmax : x ∈ componentMaximizers
      (fun z : (L.criticalLeaf hG hsmooth hderiv center hheight g hg).fiber g t ↦
        (L.criticalLeaf hG hsmooth hderiv center hheight g hg).delta z)) :
    (x : RealEuclidean n) ∈ L.criticalLocus g center height := by
  let K := L.criticalLeaf hG hsmooth hderiv center hheight g hg
  have hxU : (x : RealEuclidean n) ∈ K.U :=
    (K.mem_fiber_iff g t x).mp x.property |>.1
  have hsurj : Function.Surjective
      (fderiv ℝ (K.definingTupleAppend g) x) := by
    exact hxU.2
  have hlocalK := K.carpet_isLocalMaxOn_definingTupleFiber_of_componentMaximizer
    hsmooth g hg t x hmax hsurj
  have htuple : K.definingTupleAppend g = L.definingTupleAppend g := by
    rfl
  have hlocal : IsLocalMaxOn (L.criticalCarpet g center height)
      {y | ∀ i, L.definingTupleAppend g y i =
        L.definingTupleAppend g x i} x := by
    rw [htuple] at hlocalK
    simpa only [K, criticalLeaf_delta] using hlocalK
  exact L.mem_criticalLocus_of_isLocalMaxOn
    hG hsmooth hderiv g hg center hheight x hlocal

/-- Source conclusion of the first half of Lemma 4: every connected
component of a regular fiber contains a point of `S_a`. -/
theorem exists_criticalTrace_point_in_connectedComponent
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (center : RealEuclidean n) {height : ℝ} (hheight : 0 < height)
    (t : RealEuclidean p)
    (x : (L.criticalLeaf hG hsmooth hderiv center hheight g hg).fiber g t) :
    ∃ y ∈ connectedComponent x,
      (y : RealEuclidean n) ∈ L.criticalTrace g center height := by
  let K := L.criticalLeaf hG hsmooth hderiv center hheight g hg
  obtain ⟨y, hycomponent, hymax⟩ :=
    K.exists_carpetMaximizer_in_connectedComponent hsmooth g hg t x
  refine ⟨y, hycomponent, ?_⟩
  have hycritical : (y : RealEuclidean n) ∈
      L.criticalLocus g center height :=
    L.componentMaximizer_mem_criticalLocus
      hG hsmooth hderiv g hg center hheight t y hymax
  have hycarrier : (y : RealEuclidean n) ∈ L.carrier ∩ L.regularLocus g := by
    have hyKcarrier := (K.mem_fiber_iff g t y).mp y.property
    exact (L.criticalLeaf_carrier hG hsmooth hderiv center hheight g hg) ▸
      ⟨hyKcarrier.1, hyKcarrier.2.1⟩
  exact ⟨hycarrier, hycritical⟩

end LionCarpetedLeaf

end AbelFormalization
