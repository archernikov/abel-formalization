import AbelFormalization.CharbonnelSardianLiteralZeroRadialBase
import AbelFormalization.CharbonnelSardianRankConstructorReduction

/-!
# Algebra and topology of Wilkie's integer-affine slice

Wilkie 3.12 adds the positive level equation `ell(x)^2 + y^2 = epsilon`
for one integer-affine hyperplane. The radial compactifier used alongside
it is already supplied by `CharbonnelSardianLiteralZeroRadialBase`.

This module records only algebraic and topological facts. The nested
modulus, compact intersection estimate, shifted finite Sardian family,
and lower-rank replacement argument of Wilkie 3.13 remain separate.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- The displayed integer-affine linear polynomial on visible coordinates. -/
def integerAffineSliceLinearForm {n : ℕ}
    (coeff : Fin n → ℤ) (constant : ℤ)
    (x : RealEuclidean n) : ℝ :=
  (∑ j : Fin n, (coeff j : ℝ) * x j) + (constant : ℝ)

/-- One equation from a finite integer-affine system. Zero coefficients are
permitted, so this carrier may be all of space or empty. -/
def integerAffineSliceHyperplane {n : ℕ}
    (coeff : Fin n → ℤ) (constant : ℤ) : Set (RealEuclidean n) :=
  {x | integerAffineSliceLinearForm coeff constant x = 0}

/-- Every displayed one-equation carrier has the existing integer-affine
syntax. -/
theorem isIntegerAffineSet_integerAffineSliceHyperplane
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ) :
    IsIntegerAffineSet (integerAffineSliceHyperplane coeff constant) := by
  refine ⟨1, (fun _ j => coeff j), (fun _ => constant), ?_⟩
  ext x
  change (integerAffineSliceLinearForm coeff constant x = 0) ↔
    ∀ i : Fin 1, integerAffineSliceLinearForm coeff constant x = 0
  exact ⟨fun h _ => h, fun h => h 0⟩

/-- A finite integer-affine system is exactly the intersection of its
displayed one-equation carriers. -/
theorem IsIntegerAffineSet.exists_sliceHyperplane_presentation
    {n : ℕ} {L : Set (RealEuclidean n)} (hL : IsIntegerAffineSet L) :
    ∃ (r : ℕ) (coeff : Fin r → Fin n → ℤ)
      (constant : Fin r → ℤ),
      L = ⋂ i : Fin r,
        integerAffineSliceHyperplane (coeff i) (constant i) := by
  obtain ⟨r, coeff, constant, hL⟩ := hL
  refine ⟨r, coeff, constant, ?_⟩
  rw [hL]
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iInter,
    integerAffineSliceHyperplane, integerAffineSliceLinearForm]

/-- The polynomial used for the extra positive slice level in Wilkie 3.12.
Its last variable is one newly introduced hidden coordinate. -/
def integerAffineSliceLevelPolynomial {n : ℕ}
    (coeff : Fin n → ℤ) (constant : ℤ) :
    MvPolynomial (Fin (n + 1)) ℝ :=
  ((∑ j : Fin n,
      MvPolynomial.C (coeff j : ℝ) *
        MvPolynomial.X (Fin.castAdd 1 j)) +
      MvPolynomial.C (constant : ℝ)) ^ 2 +
    (MvPolynomial.X (Fin.natAdd n (0 : Fin 1))) ^ 2

/-- The slice level equation, represented directly by polynomial
evaluation. -/
def integerAffineSliceLevelEquation {n : ℕ}
    (coeff : Fin n → ℤ) (constant : ℤ) :
    RealEuclideanFunction (n + 1) :=
  fun v => MvPolynomial.eval v
    (integerAffineSliceLevelPolynomial coeff constant)

/-- The extra equation belongs to every geometric function family. -/
theorem integerAffineSliceLevelEquation_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ) :
    integerAffineSliceLevelEquation coeff constant ∈ G (n + 1) :=
  hG.polynomial (integerAffineSliceLevelPolynomial coeff constant)

/-- Appending the hidden variable produces precisely the two displayed
squares. -/
theorem integerAffineSliceLevelEquation_append
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (x : RealEuclidean n) (y : RealEuclidean 1) :
    integerAffineSliceLevelEquation coeff constant
        (realEuclideanAppend x y) =
      (integerAffineSliceLinearForm coeff constant x) ^ 2 + (y 0) ^ 2 := by
  classical
  simp only [integerAffineSliceLevelEquation,
    integerAffineSliceLevelPolynomial,
    map_add, map_sum, map_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X,
    realEuclideanAppend_castAdd, realEuclideanAppend_natAdd,
    integerAffineSliceLinearForm]

/-- Eliminating the extra hidden variable gives exactly a nonnegative
small-level condition. -/
theorem integerAffineSliceLevel_exists_iff
    {n : ℕ} (coeff : Fin n → ℤ) (constant : ℤ)
    (x : RealEuclidean n) (epsilon : ℝ) :
    (∃ y : RealEuclidean 1,
      integerAffineSliceLevelEquation coeff constant
        (realEuclideanAppend x y) = epsilon) ↔
      (integerAffineSliceLinearForm coeff constant x) ^ 2 ≤ epsilon := by
  constructor
  · rintro ⟨y, hy⟩
    rw [integerAffineSliceLevelEquation_append] at hy
    nlinarith [sq_nonneg (y 0)]
  · intro hlevel
    let y : RealEuclidean 1 := fun _ =>
      Real.sqrt (epsilon -
        (integerAffineSliceLinearForm coeff constant x) ^ 2)
    refine ⟨y, ?_⟩
    rw [integerAffineSliceLevelEquation_append]
    have hsqrt :
        (Real.sqrt (epsilon -
          (integerAffineSliceLinearForm coeff constant x) ^ 2)) ^ 2 =
            epsilon -
              (integerAffineSliceLinearForm coeff constant x) ^ 2 :=
      Real.sq_sqrt (sub_nonneg.mpr hlevel)
    dsimp only [y]
    linarith

/-- For a closed target, Wilkie 3.12's frontier-slice condition is exactly
avoidance of the target interior by that slice. -/
theorem closed_slice_frontier_condition_iff
    {X : Type*} [TopologicalSpace X]
    {A H : Set X} (hA : IsClosed A) :
    A ∩ H = frontier A ∩ H ↔ interior A ∩ H = ∅ := by
  constructor
  · intro heq
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxAH : x ∈ A ∩ H := ⟨interior_subset hx.1, hx.2⟩
    rw [heq] at hxAH
    have hxFront : x ∈ A \ interior A := by
      simpa only [hA.frontier_eq] using hxAH.1
    exact hxFront.2 hx.1
  · intro havoid
    ext x
    constructor
    · rintro ⟨hxA, hxH⟩
      have hxNot : x ∉ interior A := by
        intro hxInt
        have hxEmpty : x ∈ interior A ∩ H := ⟨hxInt, hxH⟩
        simpa [havoid] using hxEmpty
      exact ⟨by rw [hA.frontier_eq]; exact ⟨hxA, hxNot⟩, hxH⟩
    · rintro ⟨hxFront, hxH⟩
      exact ⟨hA.frontier_subset hxFront, hxH⟩

end AbelFormalization
