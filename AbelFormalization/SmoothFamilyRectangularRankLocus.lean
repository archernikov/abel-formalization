import AbelFormalization.SmoothFamilyRectangularJacobianMinors

/-!
# Rectangular regular and singular rank loci

For a globally smooth tuple from a geometric derivative-closed family, the
local-submersion definition of its regular fiber is detected pointwise by its
maximal Jacobian minors.  Consequently the regular rank locus is the union of
the nonzero loci of those minors, while the singular rank locus is their common
zero set.  Each defining minor is already a member of the original function
family by `IsGeometricFunctionFamily.standardJacobianColumnMinor_mem`.

This identifies the first rank decomposition needed in a higher-codimension
fiber argument.  It does not assert that either locus has finitely many
components, nor that any resulting bound is uniform in the fiber parameter.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The full-row-rank locus, expressed by nonvanishing of some maximal
coordinate minor. -/
def standardJacobianRegularLocus {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) : Set (RealEuclidean a) :=
  {x | ∃ cols : Fin b ↪ Fin a, standardJacobianColumnMinor g cols x ≠ 0}

/-- The rank-deficient locus, expressed as the common zero set of all maximal
coordinate minors. -/
def standardJacobianSingularLocus {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) : Set (RealEuclidean a) :=
  {x | ∀ cols : Fin b ↪ Fin a, standardJacobianColumnMinor g cols x = 0}

/-- The regular rank locus is literally the union of the nonzero maximal-minor
loci. -/
theorem standardJacobianRegularLocus_eq_iUnion {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) :
    standardJacobianRegularLocus g =
      ⋃ cols : Fin b ↪ Fin a,
        {x | standardJacobianColumnMinor g cols x ≠ 0} := by
  ext x
  simp only [standardJacobianRegularLocus, Set.mem_ofPred_eq,
    Set.mem_iUnion]

/-- The singular rank locus is literally the common zero set of the maximal
minors. -/
theorem standardJacobianSingularLocus_eq_iInter {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) :
    standardJacobianSingularLocus g =
      ⋂ cols : Fin b ↪ Fin a,
        {x | standardJacobianColumnMinor g cols x = 0} := by
  ext x
  simp only [standardJacobianSingularLocus, Set.mem_ofPred_eq,
    Set.mem_iInter]

/-- The singular and regular rank loci are complementary. -/
theorem standardJacobianSingularLocus_eq_compl_regularLocus {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) :
    standardJacobianSingularLocus g =
      (standardJacobianRegularLocus g)ᶜ := by
  classical
  ext x
  simp only [standardJacobianSingularLocus, standardJacobianRegularLocus,
    Set.mem_ofPred_eq, Set.mem_compl_iff]
  push Not
  rfl

/-- For an everywhere-smooth family tuple, membership in the manuscript's
local regular fiber is equivalent to the fiber equation together with the
nonvanishing of one maximal Jacobian minor. -/
theorem IsEverywhereSmoothFunctionFamily.mem_smoothRegularFiber_iff_exists_standardJacobianColumnMinor_ne_zero
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) (t : RealEuclidean b)
    (x : RealEuclidean a) :
    x ∈ smoothRegularFiber g t ↔
      g x = t ∧
        ∃ cols : Fin b ↪ Fin a,
          standardJacobianColumnMinor g cols x ≠ 0 := by
  have hgSmooth : ContDiff ℝ ∞ g := by
    rw [contDiff_pi]
    intro i
    exact hsmooth a (fun y ↦ g y i) (hg i)
  constructor
  · rintro ⟨hvalue, U, hUopen, hxU, hC1, hsurj⟩
    exact ⟨hvalue,
      (hsmooth.fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
        g hg x).mp (hsurj x hxU)⟩
  · rintro ⟨hvalue, cols, hcols⟩
    let minor : RealEuclideanFunction a :=
      standardJacobianColumnMinor g cols
    have hminorMem : minor ∈ G a := by
      exact hG.standardJacobianColumnMinor_mem hderiv g hg cols
    have hminorContinuous : Continuous minor :=
      (hsmooth a minor hminorMem).continuous
    let U : Set (RealEuclidean a) := {y | minor y ≠ 0}
    have hUopen : IsOpen U :=
      isOpen_ne_fun hminorContinuous continuous_const
    have hxU : x ∈ U := by
      simpa only [U, minor, Set.mem_ofPred_eq] using hcols
    refine ⟨hvalue, U, hUopen, hxU,
      (hgSmooth.of_le (by simp)).contDiffOn, ?_⟩
    intro y hyU
    apply
      (hsmooth.fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
        g hg y).mpr
    refine ⟨cols, ?_⟩
    simpa only [U, minor, Set.mem_ofPred_eq] using hyU

/-- The smooth regular fiber is the intersection of the literal fiber with
the open full-rank locus. -/
theorem IsEverywhereSmoothFunctionFamily.smoothRegularFiber_eq_fiber_inter_standardJacobianRegularLocus
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) (t : RealEuclidean b) :
    smoothRegularFiber g t =
      g ⁻¹' {t} ∩ standardJacobianRegularLocus g := by
  ext x
  rw [hsmooth.mem_smoothRegularFiber_iff_exists_standardJacobianColumnMinor_ne_zero
    hG hderiv g hg t x]
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    standardJacobianRegularLocus, Set.mem_ofPred_eq]

/-- The full-rank locus is open.  In the family setting this follows using
the family membership and smoothness of every maximal minor. -/
theorem IsEverywhereSmoothFunctionFamily.isOpen_standardJacobianRegularLocus
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) :
    IsOpen (standardJacobianRegularLocus g) := by
  rw [standardJacobianRegularLocus_eq_iUnion]
  apply isOpen_iUnion
  intro cols
  exact isOpen_ne_fun
    ((hsmooth a (standardJacobianColumnMinor g cols)
      (hG.standardJacobianColumnMinor_mem hderiv g hg cols)).continuous)
    continuous_const

/-- The common zero locus of the maximal minors is closed. -/
theorem IsEverywhereSmoothFunctionFamily.isClosed_standardJacobianSingularLocus
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) :
    IsClosed (standardJacobianSingularLocus g) := by
  rw [standardJacobianSingularLocus_eq_compl_regularLocus]
  exact (hsmooth.isOpen_standardJacobianRegularLocus hG hderiv g hg).isClosed_compl

/-- Inside a fiber, removing the smooth regular part leaves exactly the common
zero locus of all maximal minors. -/
theorem IsEverywhereSmoothFunctionFamily.fiber_diff_smoothRegularFiber_eq_inter_standardJacobianSingularLocus
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) (t : RealEuclidean b) :
    g ⁻¹' {t} \ smoothRegularFiber g t =
      g ⁻¹' {t} ∩ standardJacobianSingularLocus g := by
  classical
  ext x
  rw [Set.mem_sdiff,
    hsmooth.mem_smoothRegularFiber_iff_exists_standardJacobianColumnMinor_ne_zero
      hG hderiv g hg t x]
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
    standardJacobianSingularLocus, Set.mem_ofPred_eq]
  by_cases hfiber : g x = t
  · simp only [hfiber, true_and]
    push Not
    rfl
  · simp only [hfiber, false_and, not_false_eq_true]

end AbelFormalization
