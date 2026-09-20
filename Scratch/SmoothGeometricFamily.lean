import AbelFormalization.RegularZeroBasics
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Smooth geometric function families

This file gives the exact finite-dimensional function-family interfaces used
by the Lion--Ambrozy stage of the manuscript.  It also proves the local-rank
form of a regular fiber agrees, for a globally `C¹` square map, with the
pointwise surjective-derivative condition used by `regularZeroSet`.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The real coordinate space of dimension `n`. -/
abbrev RealEuclidean (n : ℕ) := Fin n → ℝ

/-- Real-valued functions on `ℝⁿ`. -/
abbrev RealEuclideanFunction (n : ℕ) := RealEuclidean n → ℝ

/-- A family satisfying the four algebraic and affine-pullback axioms of a
geometric function family.  Dimension zero is included harmlessly. -/
structure IsGeometricFunctionFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop where
  add : ∀ {n} {f g : RealEuclideanFunction n},
    f ∈ G n → g ∈ G n → f + g ∈ G n
  mul : ∀ {n} {f g : RealEuclideanFunction n},
    f ∈ G n → g ∈ G n → f * g ∈ G n
  inv : ∀ {n} {f : RealEuclideanFunction n},
    f ∈ G n → (∀ x, f x ≠ 0) → f⁻¹ ∈ G n
  polynomial : ∀ {n} (P : MvPolynomial (Fin n) ℝ),
    (fun x ↦ MvPolynomial.eval x P) ∈ G n
  affine_comp : ∀ {m n} {f : RealEuclideanFunction n},
    f ∈ G n → ∀ ℓ : RealEuclidean m →ᵃ[ℝ] RealEuclidean n,
      f ∘ ℓ ∈ G m

theorem IsGeometricFunctionFamily.const_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ} (c : ℝ) :
    (fun _ : RealEuclidean n ↦ c) ∈ G n := by
  simpa using hG.polynomial (n := n) (MvPolynomial.C c)

theorem IsGeometricFunctionFamily.zero_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ} :
    (0 : RealEuclideanFunction n) ∈ G n := by
  change (fun _ : RealEuclidean n ↦ 0) ∈ G n
  exact hG.const_mem (n := n) 0

theorem IsGeometricFunctionFamily.one_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ} :
    (1 : RealEuclideanFunction n) ∈ G n := by
  change (fun _ : RealEuclidean n ↦ 1) ∈ G n
  exact hG.const_mem (n := n) 1

theorem IsGeometricFunctionFamily.neg_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    {f : RealEuclideanFunction n} (hf : f ∈ G n) :
    -f ∈ G n := by
  have hm := hG.mul (hG.const_mem (n := n) (-1)) hf
  change (fun x ↦ (-1) * f x) ∈ G n at hm
  change (fun x ↦ -f x) ∈ G n
  simpa using hm

theorem IsGeometricFunctionFamily.sub_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    {f g : RealEuclideanFunction n} (hf : f ∈ G n) (hg : g ∈ G n) :
    f - g ∈ G n := by
  simpa [sub_eq_add_neg] using hG.add hf (hG.neg_mem hg)

theorem IsGeometricFunctionFamily.sq_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    {f : RealEuclideanFunction n} (hf : f ∈ G n) :
    (fun x ↦ f x ^ 2) ∈ G n := by
  have hm := hG.mul hf hf
  change (fun x ↦ f x * f x) ∈ G n at hm
  simpa only [pow_two] using hm

/-- Every member is globally smooth. -/
def IsEverywhereSmoothFunctionFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ n f, f ∈ G n → ContDiff ℝ ∞ f

/-- Coordinate differentiation stays in the family. -/
def IsCoordinateDerivativeClosedFunctionFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ n (f : RealEuclideanFunction n), f ∈ G n → ∀ i : Fin n,
    (fun x ↦ fderiv ℝ f x (Pi.single i 1)) ∈ G n

/-- A finite tuple belongs componentwise to a function family. -/
def FunctionTupleInFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n))
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b) : Prop :=
  ∀ j, (fun x ↦ g x j) ∈ G a

/-- The manuscript's regular part of a fiber: the map is a `C¹` submersion
on one neighborhood of the point. -/
def smoothRegularFiber {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b)
    (t : RealEuclidean b) : Set (RealEuclidean a) :=
  {x | g x = t ∧ ∃ U : Set (RealEuclidean a),
    IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 1 g U ∧
      ∀ y ∈ U, Function.Surjective (fderiv ℝ g y)}

/-- The 0-regular condition from the smooth-family criterion. -/
def IsZeroRegularFunctionFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ n (g : RealEuclidean n → RealEuclidean n),
    FunctionTupleInFamily G g → ∀ t, (smoothRegularFiber g t).Finite

/-- Uniform connected-component finiteness of every fiber. -/
def HasUniformFiberFiniteness
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ a b (g : RealEuclidean a → RealEuclidean b),
    FunctionTupleInFamily G g → ∃ N : ℕ, ∀ t,
      ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ N

theorem smoothRegularFiber_subset_fiber {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (t : RealEuclidean b) :
    smoothRegularFiber g t ⊆ g ⁻¹' {t} := by
  intro x hx
  exact hx.1

/-- For a globally `C¹` square map, pointwise surjectivity of the derivative
persists on a neighborhood.  Hence the local-submersion definition of the
regular fiber is exactly the usual pointwise one. -/
theorem mem_smoothRegularFiber_iff_of_contDiff_square
    {n : ℕ} (g : RealEuclidean n → RealEuclidean n)
    (hg : ContDiff ℝ 1 g) (t : RealEuclidean n) (x : RealEuclidean n) :
    x ∈ smoothRegularFiber g t ↔
      g x = t ∧ Function.Surjective (fderiv ℝ g x) := by
  constructor
  · rintro ⟨hvalue, U, hUopen, hxU, hC1, hsurj⟩
    exact ⟨hvalue, hsurj x hxU⟩
  · rintro ⟨hvalue, hsurj⟩
    let D := fderiv ℝ g x
    have hinj : Function.Injective D :=
      continuousLinearMap_injective_of_surjective_of_finrank_eq D rfl hsurj
    have hunit : IsUnit D := by
      rw [ContinuousLinearMap.isUnit_iff_bijective]
      exact ⟨hinj, hsurj⟩
    let U : Set (RealEuclidean n) :=
      (fderiv ℝ g) ⁻¹' {T : RealEuclidean n →L[ℝ] RealEuclidean n | IsUnit T}
    have hUopen : IsOpen U :=
      Units.isOpen.preimage (hg.continuous_fderiv (by norm_num))
    have hxU : x ∈ U := hunit
    refine ⟨hvalue, U, hUopen, hxU, hg.contDiffOn, ?_⟩
    intro y hy
    exact (ContinuousLinearMap.isUnit_iff_bijective.mp hy).2

end AbelFormalization
