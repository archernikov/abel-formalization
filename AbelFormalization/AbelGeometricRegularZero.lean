import AbelFormalization.AbelGeometricFamily
import AbelFormalization.SmoothRegularZeroBridge
import AbelFormalization.RegularZeroEquationScaling
import AbelFormalization.RegularConstraintFiber

/-!
# Clearing denominators in regular fibers of the Abel geometric family

This file packages the exact reduction from a square tuple of localized Abel
expressions to one square tuple of numerator expressions.  Each denominator
is nonzero everywhere, so coordinatewise equation scaling preserves both the
zero set and surjectivity of the derivative at every zero.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The remaining numerator-level regular-zero assertion needed to prove that
the concrete localized Abel family is 0-regular. -/
def AbelNumeratorRegularZeroFinite (A : ℝ → ℝ) : Prop :=
  ∀ n (F : Fin n → RealEuclideanFunction n),
    (∀ i, AbelNumerator A n (F i)) →
      (regularZeroSet Set.univ (constraintMap F)).Finite

/-- Coordinatewise numerator/denominator witnesses for a square map whose
components lie in the localized Abel family. -/
structure AbelGeometricTuplePresentation (A : ℝ → ℝ) {n : ℕ}
    (g : RealEuclidean n → RealEuclidean n) where
  numerator : Fin n → RealEuclideanFunction n
  denominator : Fin n → RealEuclideanFunction n
  numerator_mem : ∀ i, AbelNumerator A n (numerator i)
  denominator_mem : ∀ i, AbelNumerator A n (denominator i)
  denominator_ne : ∀ i x, denominator i x ≠ 0
  quotient_eq : ∀ i, (fun x ↦ g x i) = numerator i / denominator i

/-- Every componentwise member of the localized family admits a simultaneous
finite tuple presentation. -/
theorem exists_abelGeometricTuplePresentation
    {A : ℝ → ℝ} {n : ℕ} {g : RealEuclidean n → RealEuclidean n}
    (hg : FunctionTupleInFamily (abelGeometricFamily A) g) :
    Nonempty (AbelGeometricTuplePresentation A g) := by
  classical
  choose P Q hP hQ hQ0 hPQ using fun i ↦ hg i
  exact ⟨{
    numerator := P
    denominator := Q
    numerator_mem := hP
    denominator_mem := hQ
    denominator_ne := hQ0
    quotient_eq := hPQ
  }⟩

/-- The numerator system obtained after clearing the target equation
`g(x)=t` coordinate by coordinate. -/
def AbelGeometricTuplePresentation.clearedFiberSystem
    {A : ℝ → ℝ} {n : ℕ} {g : RealEuclidean n → RealEuclidean n}
    (P : AbelGeometricTuplePresentation A g) (t : RealEuclidean n) :
    RealEuclidean n → RealEuclidean n :=
  fun x i ↦ P.numerator i x - t i * P.denominator i x

/-- The tuple of denominators, used as the nonzero diagonal equation scale. -/
def AbelGeometricTuplePresentation.denominatorSystem
    {A : ℝ → ℝ} {n : ℕ} {g : RealEuclidean n → RealEuclidean n}
    (P : AbelGeometricTuplePresentation A g) :
    RealEuclidean n → RealEuclidean n :=
  fun x i ↦ P.denominator i x

/-- Every cleared equation is again a numerator expression. -/
theorem AbelGeometricTuplePresentation.clearedFiberSystem_mem
    {A : ℝ → ℝ} {n : ℕ} {g : RealEuclidean n → RealEuclidean n}
    (P : AbelGeometricTuplePresentation A g) (t : RealEuclidean n) (i : Fin n) :
    AbelNumerator A n (fun x ↦ P.clearedFiberSystem t x i) := by
  have ht : AbelNumerator A n (fun _ : RealEuclidean n ↦ t i) :=
    AbelNumerator.const (t i)
  have hprod := AbelNumerator.mul ht (P.denominator_mem i)
  exact (AbelNumerator.sub (P.numerator_mem i) hprod).congr_of_eq (by rfl)

/-- Clearing denominators is literally coordinatewise multiplication of the
original target equations by the denominator tuple. -/
theorem AbelGeometricTuplePresentation.denominator_mul_sub_eq_cleared
    {A : ℝ → ℝ} {n : ℕ} {g : RealEuclidean n → RealEuclidean n}
    (P : AbelGeometricTuplePresentation A g) (t : RealEuclidean n)
    (x : RealEuclidean n) (i : Fin n) :
    P.denominatorSystem x i * (g x i - t i) =
      P.clearedFiberSystem t x i := by
  have hq := congrFun (P.quotient_eq i) x
  dsimp [AbelGeometricTuplePresentation.denominatorSystem,
    AbelGeometricTuplePresentation.clearedFiberSystem]
  change P.denominator i x * (g x i - t i) = _
  change g x i = P.numerator i x / P.denominator i x at hq
  rw [hq]
  rw [mul_sub, mul_div_cancel₀ _ (P.denominator_ne i x)]
  ring

/-- For an Abel function, the cleared numerator system and the original
fiber equation have exactly the same regular zeros. -/
theorem IsAbel.regularZeroSet_clearedFiberSystem_eq
    {A : ℝ → ℝ} (hA : IsAbel A) {n : ℕ}
    {g : RealEuclidean n → RealEuclidean n}
    (hg : FunctionTupleInFamily (abelGeometricFamily A) g)
    (P : AbelGeometricTuplePresentation A g) (t : RealEuclidean n) :
    regularZeroSet Set.univ (P.clearedFiberSystem t) =
      regularZeroSet Set.univ (fun x ↦ g x - t) := by
  have hgSmooth : ContDiff ℝ ∞ g := by
    rw [contDiff_pi]
    intro i
    exact hA.isEverywhereSmooth_abelGeometricFamily n
      (fun x ↦ g x i) (hg i)
  have hsubDiff : Differentiable ℝ (fun x ↦ g x - t) :=
    (hgSmooth.sub contDiff_const).differentiable (by simp)
  have hdenSmooth : ContDiff ℝ ∞ P.denominatorSystem := by
    rw [contDiff_pi]
    intro i
    exact (P.denominator_mem i).contDiff hA
  have hfun : P.clearedFiberSystem t =
      (fun y i ↦ P.denominatorSystem y i * (g y - t) i) := by
    funext y i
    exact (P.denominator_mul_sub_eq_cleared t y i).symm
  rw [hfun]
  ext x
  exact mem_regularZeroSet_coordinatewise_mul_iff
    (Omega := Set.univ) (x := x)
    hsubDiff.differentiableAt
    (hdenSmooth.differentiable (by simp)).differentiableAt
    (P.denominator_ne · x)

/-- Numerator-level regular-zero finiteness implies 0-regularity of the
concrete localized Abel family.  This is the denominator-clearing half of the
manuscript's final application of its regular-zero theorem. -/
theorem IsAbel.isZeroRegular_abelGeometricFamily_of_numerator
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hfinite : AbelNumeratorRegularZeroFinite A) :
    IsZeroRegularFunctionFamily (abelGeometricFamily A) := by
  apply IsZeroRegularFunctionFamily.of_regularZeroSet_finite
    hA.isEverywhereSmooth_abelGeometricFamily
  intro n g hg t
  let P := Classical.choice (exists_abelGeometricTuplePresentation hg)
  rw [← hA.regularZeroSet_clearedFiberSystem_eq hg P t]
  apply hfinite n (fun i x ↦ P.clearedFiberSystem t x i)
  exact fun i ↦ P.clearedFiberSystem_mem t i

end AbelFormalization
