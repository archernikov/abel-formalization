import AbelFormalization.LionCarpetCompactification
import AbelFormalization.SmoothFamilyRectangularJacobianMinors
import AbelFormalization.SmoothGeometricFamily
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Carpeted leaves in Lion's sense

This file records the associated triplet `(U, delta, f)` used throughout
Lion's Lemmas 3--5.  The open set `U` is carpeted by `delta`, the coordinate
functions of `f` belong to the geometric family, and `f` is a submersion on
`U`.  The leaf itself is exactly `U ∩ f⁻¹(0)`.

When the codimension equals the ambient dimension, this carrier lies in the
smooth regular zero fiber of the square tuple.  Consequently the
`0`-regularity hypothesis makes every such terminal leaf finite, which is
the base case used in Lion's Theorem 7'.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- An associated carpeted-leaf triplet `(U, delta, f)` from Lion's paper.

The carrier has ambient dimension `n` and codimension `q`.  Smoothness is
not stored separately: for the applications here it follows from
`IsEverywhereSmoothFunctionFamily G` and the two family-membership fields. -/
structure LionCarpetedLeaf
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) (n q : ℕ) where
  U : Set (RealEuclidean n)
  isOpen_U : IsOpen U
  delta : RealEuclideanFunction n
  isCarpet : IsLionCarpetOn U delta
  delta_mem : delta ∈ G n
  equations : RealEuclidean n → RealEuclidean q
  equations_mem : FunctionTupleInFamily G equations
  fderiv_surjective : ∀ x ∈ U,
    Function.Surjective (fderiv ℝ equations x)

namespace LionCarpetedLeaf

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)} {n q : ℕ}

/-- The subset represented by an associated carpeted-leaf triplet. -/
def carrier (L : LionCarpetedLeaf G n q) : Set (RealEuclidean n) :=
  {x | x ∈ L.U ∧ L.equations x = 0}

@[simp]
theorem mem_carrier_iff (L : LionCarpetedLeaf G n q)
    (x : RealEuclidean n) :
    x ∈ L.carrier ↔ x ∈ L.U ∧ L.equations x = 0 :=
  Iff.rfl

/-- The carrier is literally the zero fiber restricted to the carpeted
open set. -/
theorem carrier_eq_inter_preimage_zero (L : LionCarpetedLeaf G n q) :
    L.carrier = L.U ∩ L.equations ⁻¹' {(0 : RealEuclidean q)} := by
  ext x
  simp only [carrier, mem_ofPred_eq, mem_inter_iff, mem_preimage,
    mem_singleton_iff]

theorem carrier_subset_U (L : LionCarpetedLeaf G n q) :
    L.carrier ⊆ L.U := by
  intro x hx
  exact hx.1

theorem equations_eq_zero_of_mem_carrier (L : LionCarpetedLeaf G n q)
    {x : RealEuclidean n} (hx : x ∈ L.carrier) :
    L.equations x = 0 :=
  hx.2

/-- Named family-membership statement for the tuple defining the leaf. -/
theorem equations_tuple_mem (L : LionCarpetedLeaf G n q) :
    FunctionTupleInFamily G L.equations :=
  L.equations_mem

/-- Every defining equation belongs to the same geometric family. -/
theorem equation_mem (L : LionCarpetedLeaf G n q) (i : Fin q) :
    (fun x ↦ L.equations x i) ∈ G n :=
  L.equations_mem i

/-- The carpet is itself a member of the geometric family. -/
theorem carpet_mem (L : LionCarpetedLeaf G n q) :
    L.delta ∈ G n :=
  L.delta_mem

/-- Family smoothness supplies the differentiability class of the defining
tuple required in the regular-fiber endpoint. -/
theorem equations_contDiff
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    ContDiff ℝ ∞ L.equations := by
  rw [contDiff_pi]
  intro i
  exact hsmooth n (fun x ↦ L.equations x i) (L.equation_mem i)

/-- Family smoothness also supplies the differentiability class of the
carpet appearing in Lion's associated triplet. -/
theorem carpet_contDiff
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    ContDiff ℝ ∞ L.delta :=
  hsmooth n L.delta L.carpet_mem

/-! ## The regular locus of a map on a carpeted leaf (Lion's Lemma 3) -/

/-- The tuple `(f,g)` used by Lion to detect regular points of `g|X`, where
`f` is the defining submersion of the leaf. -/
def definingTupleAppend (L : LionCarpetedLeaf G n q) {p : ℕ}
    (g : RealEuclidean n → RealEuclidean p) :
    RealEuclidean n → RealEuclidean (q + p) :=
  fun x ↦ Fin.addCases (L.equations x) (g x)

@[simp]
theorem definingTupleAppend_castAdd (L : LionCarpetedLeaf G n q)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (x : RealEuclidean n) (i : Fin q) :
    L.definingTupleAppend g x (Fin.castAdd p i) = L.equations x i := by
  simp [definingTupleAppend]

@[simp]
theorem definingTupleAppend_natAdd (L : LionCarpetedLeaf G n q)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (x : RealEuclidean n) (j : Fin p) :
    L.definingTupleAppend g x (Fin.natAdd q j) = g x j := by
  simp [definingTupleAppend]

/-- Appending a family-valued tuple to the equations of a leaf stays in the
same family, component by component. -/
theorem definingTupleAppend_mem (L : LionCarpetedLeaf G n q)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    FunctionTupleInFamily G (L.definingTupleAppend g) := by
  intro k
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
  · simpa [definingTupleAppend] using L.equation_mem i
  · simpa [definingTupleAppend] using hg j

/-- The squared norm of Lion's form
`df₁ ∧ ⋯ ∧ df_q ∧ dg₁ ∧ ⋯ ∧ dg_p`, written as the finite
sum of squares of all maximal coordinate Jacobian minors. -/
def regularityMinorSum (L : LionCarpetedLeaf G n q) {p : ℕ}
    (g : RealEuclidean n → RealEuclidean p) : RealEuclideanFunction n :=
  fun x ↦ ∑ cols : Fin (q + p) ↪ Fin n,
    standardJacobianColumnMinor (L.definingTupleAppend g) cols x ^ 2

theorem regularityMinorSum_nonneg (L : LionCarpetedLeaf G n q)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (x : RealEuclidean n) :
    0 ≤ L.regularityMinorSum g x := by
  exact Finset.sum_nonneg (fun cols _ ↦ sq_nonneg
    (standardJacobianColumnMinor (L.definingTupleAppend g) cols x))

theorem regularityMinorSum_eq_zero_iff
    (L : LionCarpetedLeaf G n q) {p : ℕ}
    (g : RealEuclidean n → RealEuclidean p) (x : RealEuclidean n) :
    L.regularityMinorSum g x = 0 ↔
      ∀ cols : Fin (q + p) ↪ Fin n,
        standardJacobianColumnMinor (L.definingTupleAppend g) cols x = 0 := by
  classical
  rw [regularityMinorSum]
  constructor
  · intro hzero cols
    exact ((Finset.sum_sq_eq_zero_iff Finset.univ
      (fun c : Fin (q + p) ↪ Fin n ↦
        standardJacobianColumnMinor (L.definingTupleAppend g) c x)).1
          hzero) cols (Finset.mem_univ cols)
  · intro hzero
    exact (Finset.sum_sq_eq_zero_iff Finset.univ
      (fun c : Fin (q + p) ↪ Fin n ↦
        standardJacobianColumnMinor (L.definingTupleAppend g) c x)).2
          (fun cols _ ↦ hzero cols)

/-- The squared maximal-minor sum is positive exactly at the regular points
of `(f,g)`.  On the leaf this is Lion's regular locus of `g|X`. -/
theorem regularityMinorSum_pos_iff_fderiv_surjective
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) (x : RealEuclidean n) :
    0 < L.regularityMinorSum g x ↔
      Function.Surjective (fderiv ℝ (L.definingTupleAppend g) x) := by
  rw [hsmooth.fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
    (L.definingTupleAppend g) (L.definingTupleAppend_mem g hg) x]
  have hnonneg := L.regularityMinorSum_nonneg g x
  constructor
  · intro hpos
    by_contra hnone
    simp only [not_exists, not_ne_iff] at hnone
    exact (ne_of_gt hpos) ((L.regularityMinorSum_eq_zero_iff g x).2 hnone)
  · rintro ⟨cols, hcols⟩
    exact lt_of_le_of_ne hnonneg (fun hzero ↦
      hcols ((L.regularityMinorSum_eq_zero_iff g x).1 hzero.symm cols))

/-- The regularity minor sum belongs to the original family. -/
theorem regularityMinorSum_mem
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    L.regularityMinorSum g ∈ G n := by
  classical
  have hsum := hG.finset_sum_mem
    (Finset.univ : Finset (Fin (q + p) ↪ Fin n))
    (fun cols ↦ fun x ↦
      standardJacobianColumnMinor (L.definingTupleAppend g) cols x ^ 2)
    (by
      intro cols _
      exact hG.sq_mem
        (hG.standardJacobianColumnMinor_mem hderiv
          (L.definingTupleAppend g) (L.definingTupleAppend_mem g hg) cols))
  change (fun x ↦ ∑ cols : Fin (q + p) ↪ Fin n,
    standardJacobianColumnMinor (L.definingTupleAppend g) cols x ^ 2) ∈ G n
  convert hsum using 1
  funext x
  simp only [Finset.sum_apply]

/-- Lion's open ambient regular locus `U'`: points of `U` where `(f,g)` is
a submersion. -/
def regularLocus (L : LionCarpetedLeaf G n q) {p : ℕ}
    (g : RealEuclidean n → RealEuclidean p) : Set (RealEuclidean n) :=
  {x | x ∈ L.U ∧ Function.Surjective
    (fderiv ℝ (L.definingTupleAppend g) x)}

theorem mem_regularLocus_iff_minorSum_pos
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) (x : RealEuclidean n) :
    x ∈ L.regularLocus g ↔
      x ∈ L.U ∧ 0 < L.regularityMinorSum g x := by
  rw [regularLocus, Set.mem_ofPred_eq,
    L.regularityMinorSum_pos_iff_fderiv_surjective hsmooth g hg x]

theorem regularLocus_isOpen
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    IsOpen (L.regularLocus g) := by
  have hcontinuous : Continuous (L.regularityMinorSum g) :=
    (hsmooth n (L.regularityMinorSum g)
      (L.regularityMinorSum_mem hG hderiv g hg)).continuous
  rw [show L.regularLocus g = L.U ∩ {x | 0 < L.regularityMinorSum g x} by
    ext x
    exact L.mem_regularLocus_iff_minorSum_pos hsmooth g hg x]
  exact L.isOpen_U.inter (isOpen_lt continuous_const hcontinuous)

/-- The bounded factor `|theta|/(1+|theta|)` used in Lion's carpet on the
regular locus. -/
def regularityCarpetFactor (L : LionCarpetedLeaf G n q) {p : ℕ}
    (g : RealEuclidean n → RealEuclidean p) : RealEuclideanFunction n :=
  fun x ↦ L.regularityMinorSum g x / (1 + L.regularityMinorSum g x)

theorem regularityCarpetFactor_mem
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    L.regularityCarpetFactor g ∈ G n := by
  have hM := L.regularityMinorSum_mem hG hderiv g hg
  have hdenom : (fun x ↦ 1 + L.regularityMinorSum g x) ∈ G n := by
    change (1 + L.regularityMinorSum g : RealEuclideanFunction n) ∈ G n
    exact hG.add hG.one_mem hM
  have hdenom_ne : ∀ x, 1 + L.regularityMinorSum g x ≠ 0 := by
    intro x
    linarith [L.regularityMinorSum_nonneg g x]
  have hinv := hG.inv hdenom hdenom_ne
  have hmul := hG.mul hM hinv
  convert hmul using 1
  funext x
  simp only [regularityCarpetFactor, Pi.mul_apply, Pi.inv_apply,
    div_eq_mul_inv]

theorem regularityCarpetFactor_pos_iff_fderiv_surjective
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) (x : RealEuclidean n) :
    0 < L.regularityCarpetFactor g x ↔
      Function.Surjective (fderiv ℝ (L.definingTupleAppend g) x) := by
  rw [regularityCarpetFactor, div_pos_iff]
  have hdenom : 0 < 1 + L.regularityMinorSum g x := by
    linarith [L.regularityMinorSum_nonneg g x]
  simp only [hdenom, and_true, not_lt_of_ge
    (L.regularityMinorSum_nonneg g x), false_and, or_false]
  exact L.regularityMinorSum_pos_iff_fderiv_surjective hsmooth g hg x

theorem regularityCarpetFactor_ne_zero_iff_fderiv_surjective
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) (x : RealEuclidean n) :
    L.regularityCarpetFactor g x ≠ 0 ↔
      Function.Surjective (fderiv ℝ (L.definingTupleAppend g) x) := by
  have hnonneg : 0 ≤ L.regularityCarpetFactor g x := by
    exact div_nonneg (L.regularityMinorSum_nonneg g x)
      (by linarith [L.regularityMinorSum_nonneg g x])
  rw [← L.regularityCarpetFactor_pos_iff_fderiv_surjective hsmooth g hg x]
  exact ne_iff_gt_iff_ge.mpr hnonneg

/-- Lion's actual carpet on the regular locus:
`δ' = δ · |theta|/(1+|theta|)`. -/
def regularCarpet (L : LionCarpetedLeaf G n q) {p : ℕ}
    (g : RealEuclidean n → RealEuclidean p) : RealEuclideanFunction n :=
  fun x ↦ L.delta x * L.regularityCarpetFactor g x

theorem regularCarpet_mem
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    L.regularCarpet g ∈ G n := by
  exact hG.mul L.delta_mem
    (L.regularityCarpetFactor_mem hG hderiv g hg)

theorem regularCarpet_pos_of_mem_regularLocus
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) {x : RealEuclidean n}
    (hx : x ∈ L.regularLocus g) :
    0 < L.regularCarpet g x := by
  exact mul_pos (L.isCarpet.pos x hx.1)
    ((L.regularityCarpetFactor_pos_iff_fderiv_surjective
      hsmooth g hg x).2 hx.2)

/-- The source-faithful properness step in Lemma 3: multiplying the old
carpet by the bounded regularity factor still gives a carpet on `U'`. -/
theorem regularCarpet_isLionCarpetOn
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    IsLionCarpetOn (L.regularLocus g) (L.regularCarpet g) := by
  refine ⟨fun x hx ↦ L.regularCarpet_pos_of_mem_regularLocus
    hsmooth g hg hx, ?_⟩
  intro eta heta
  have hcontinuous : Continuous (L.regularCarpet g) :=
    (hsmooth n (L.regularCarpet g)
      (L.regularCarpet_mem hG hderiv g hg)).continuous
  have hclosed : IsClosed {x | eta ≤ L.regularCarpet g x} :=
    isClosed_le continuous_const hcontinuous
  have hsubset :
      {x | x ∈ L.regularLocus g ∧ eta ≤ L.regularCarpet g x} ⊆
        {x | x ∈ L.U ∧ eta ≤ L.delta x} := by
    rintro x ⟨hxreg, heta'⟩
    refine ⟨hxreg.1, ?_⟩
    have hMnonneg := L.regularityMinorSum_nonneg g x
    have hfactor_le_one : L.regularityCarpetFactor g x ≤ 1 := by
      rw [regularityCarpetFactor]
      exact (div_le_one (by linarith)).2 (by linarith)
    have hdelta := L.isCarpet.pos x hxreg.1
    calc
      eta ≤ L.regularCarpet g x := heta'
      _ ≤ L.delta x := by
        rw [regularCarpet]
        nlinarith [show 0 ≤ L.regularityCarpetFactor g x by
          exact div_nonneg hMnonneg (by linarith)]
  have heq :
      {x | x ∈ L.regularLocus g ∧ eta ≤ L.regularCarpet g x} =
        {x | x ∈ L.U ∧ eta ≤ L.delta x} ∩
          {x | eta ≤ L.regularCarpet g x} := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hsubset hx, hx.2⟩
    · rintro x ⟨⟨hxU, _hdelta⟩, heta'⟩
      have hcarpetPos : 0 < L.regularCarpet g x := lt_of_lt_of_le heta heta'
      have hfactorPos : 0 < L.regularityCarpetFactor g x := by
        by_contra hnot
        have hfactorZero : L.regularityCarpetFactor g x = 0 := by
          have hfactorNonneg : 0 ≤ L.regularityCarpetFactor g x := by
            exact div_nonneg (L.regularityMinorSum_nonneg g x)
              (by linarith [L.regularityMinorSum_nonneg g x])
          exact le_antisymm (le_of_not_gt hnot) hfactorNonneg
        rw [regularCarpet, hfactorZero, mul_zero] at hcarpetPos
        exact (lt_irrefl 0 hcarpetPos)
      refine ⟨⟨hxU, ?_⟩, heta'⟩
      exact (L.regularityCarpetFactor_pos_iff_fderiv_surjective
        hsmooth g hg x).1 hfactorPos
  rw [heq]
  exact (L.isCarpet.isCompact_superlevel eta heta).inter_right hclosed

/-- Lemma 3 as an associated-triplet construction: the regular locus of
`g|X` is again a carpeted leaf, with the same defining equations and Lion's
minor-sum carpet. -/
def regularLeaf
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    LionCarpetedLeaf G n q where
  U := L.regularLocus g
  isOpen_U := L.regularLocus_isOpen hG hsmooth hderiv g hg
  delta := L.regularCarpet g
  isCarpet := L.regularCarpet_isLionCarpetOn hG hsmooth hderiv g hg
  delta_mem := L.regularCarpet_mem hG hderiv g hg
  equations := L.equations
  equations_mem := L.equations_mem
  fderiv_surjective := fun x hx ↦ L.fderiv_surjective x hx.1

/-- The carrier of the new leaf is exactly the regular part of the old leaf. -/
theorem regularLeaf_carrier
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    (L.regularLeaf hG hsmooth hderiv g hg).carrier =
      {x | x ∈ L.carrier ∧ Function.Surjective
        (fderiv ℝ (L.definingTupleAppend g) x)} := by
  ext x
  simp only [carrier, regularLeaf, regularLocus, Set.mem_ofPred_eq]
  aesop

/-- Literal source form of the preceding equality: `X' = X ∩ U'`. -/
theorem regularLeaf_carrier_eq_inter_regularLocus
    (L : LionCarpetedLeaf G n q)
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {p : ℕ} (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g) :
    (L.regularLeaf hG hsmooth hderiv g hg).carrier =
      L.carrier ∩ L.regularLocus g := by
  ext x
  simp only [carrier, regularLeaf, regularLocus, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  aesop

/-! ## The zero-dimensional terminal case -/

/-- A leaf whose codimension equals its ambient dimension. -/
abbrev ZeroDimensional
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) (n : ℕ) :=
  LionCarpetedLeaf G n n

/-- Every point of a zero-dimensional carpeted leaf is a regular point of
the square zero fiber defining it. -/
theorem carrier_subset_smoothRegularFiber_zero
    (L : ZeroDimensional G n)
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    L.carrier ⊆ smoothRegularFiber L.equations (0 : RealEuclidean n) := by
  intro x hx
  refine ⟨hx.2, L.U, L.isOpen_U, hx.1, ?_, L.fderiv_surjective⟩
  exact ((L.equations_contDiff hsmooth).of_le (by simp)).contDiffOn

/-- More precisely, the terminal leaf is the part of the regular zero fiber
lying in its associated carpeted open set. -/
theorem carrier_eq_inter_smoothRegularFiber_zero
    (L : ZeroDimensional G n)
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    L.carrier =
      L.U ∩ smoothRegularFiber L.equations (0 : RealEuclidean n) := by
  apply Subset.antisymm
  · intro x hx
    exact ⟨hx.1, L.carrier_subset_smoothRegularFiber_zero hsmooth hx⟩
  · rintro x ⟨hxU, hxregular⟩
    exact ⟨hxU, hxregular.1⟩

/-- The canonical inclusion of a terminal leaf into the smooth regular
zero fiber used by the base case of Theorem 7'. -/
def regularFiberEmbedding
    (L : ZeroDimensional G n)
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    L.carrier → smoothRegularFiber L.equations (0 : RealEuclidean n) :=
  fun x ↦ ⟨x, L.carrier_subset_smoothRegularFiber_zero hsmooth x.property⟩

theorem regularFiberEmbedding_injective
    (L : ZeroDimensional G n)
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    Function.Injective (L.regularFiberEmbedding hsmooth) := by
  intro x y hxy
  apply Subtype.ext
  exact congrArg
    (fun z : smoothRegularFiber L.equations (0 : RealEuclidean n) ↦
      (z : RealEuclidean n)) hxy

/-- The substantive zero-dimensional endpoint: `0`-regularity makes the
carrier of every square carpeted leaf finite. -/
theorem carrier_finite_of_zeroRegular
    (L : ZeroDimensional G n)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G) :
    L.carrier.Finite := by
  exact (hzero n L.equations L.equations_tuple_mem
      (0 : RealEuclidean n)).subset
    (L.carrier_subset_smoothRegularFiber_zero hsmooth)

/-- Natural-number form of terminal-leaf finiteness, ready for the finite
sum estimate in the induction for Theorem 7'. -/
theorem exists_enatCard_carrier_le_of_zeroRegular
    (L : ZeroDimensional G n)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G) :
    ∃ N : ℕ, ENat.card L.carrier ≤ N := by
  let _ : Finite L.carrier :=
    Set.finite_coe_iff.mpr (L.carrier_finite_of_zeroRegular hsmooth hzero)
  refine ⟨Nat.card L.carrier, ?_⟩
  exact (ENat.card_eq_coe_natCard L.carrier).le

end LionCarpetedLeaf

end AbelFormalization
