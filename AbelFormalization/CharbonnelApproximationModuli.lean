import AbelFormalization.CharbonnelWeakStructure

/-!
# Nested moduli and two-sided approximation

This file formalizes Definition 3.2 of Wilkie's complement theorem.  A
`k`-modulus controls `k + 1` positive parameters in order: the bound for the
last parameter may depend on all earlier parameters.  An approximating set in
`ℝ^(n+k)` stores the final `k` parameters; the first parameter controls both
the approximation error and the bounded part of the target set.

Only the definitions and their elementary order theory are proved here.  No
existence of approximants, boundary theorem, or complement closure is claimed.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Wilkie's recursively nested `k`-modulus.  A value of type
`CharbonnelModulus k` controls a vector indexed by `Fin (k + 1)`.

At a successor step the new bound is a positive function of the already
chosen positive prefix. -/
inductive CharbonnelModulus : ℕ → Type
  | base (bound : ℝ) (bound_pos : 0 < bound) : CharbonnelModulus 0
  | step {k : ℕ} (initial : CharbonnelModulus k)
      (lastBound : RealEuclidean (k + 1) → ℝ)
      (lastBound_pos : ∀ ε : RealEuclidean (k + 1),
        (∀ i, 0 < ε i) → 0 < lastBound ε) :
      CharbonnelModulus (k + 1)

namespace CharbonnelModulus

/-- A positive parameter vector satisfies all bounds in their nested order. -/
def IsBounded : {k : ℕ} → CharbonnelModulus k →
    RealEuclidean (k + 1) → Prop
  | 0, .base bound _, ε => 0 < ε 0 ∧ ε 0 < bound
  | k + 1, .step initial lastBound _, ε =>
      initial.IsBounded (Fin.init ε) ∧
        0 < ε (Fin.last (k + 1)) ∧
        ε (Fin.last (k + 1)) < lastBound (Fin.init ε)

/-- Semantic refinement: every vector bounded by `tighter` is also bounded by
`looser`.  This is the direction used when an argument shrinks a modulus. -/
def Refines {k : ℕ}
    (tighter looser : CharbonnelModulus k) : Prop :=
  ∀ ε, tighter.IsBounded ε → looser.IsBounded ε

theorem refines_refl {k : ℕ} (μ : CharbonnelModulus k) : μ.Refines μ :=
  fun _ hε => hε

theorem Refines.trans {k : ℕ} {μ₁ μ₂ μ₃ : CharbonnelModulus k}
    (h₁₂ : μ₁.Refines μ₂) (h₂₃ : μ₂.Refines μ₃) : μ₁.Refines μ₃ :=
  fun ε hε => h₂₃ ε (h₁₂ ε hε)

/-- Pointwise minimum of two nested moduli. -/
def infimum : {k : ℕ} →
    CharbonnelModulus k → CharbonnelModulus k → CharbonnelModulus k
  | 0, .base left hleft, .base right hright =>
      .base (min left right) (lt_min hleft hright)
  | k + 1, .step left leftLast hleft,
      .step right rightLast hright =>
      .step (infimum left right)
        (fun ε => min (leftLast ε) (rightLast ε))
        (fun ε hε => lt_min (hleft ε hε) (hright ε hε))

theorem isBounded_infimum_iff : ∀ {k : ℕ}
    (μ ν : CharbonnelModulus k) (ε : RealEuclidean (k + 1)),
    (infimum μ ν).IsBounded ε ↔ μ.IsBounded ε ∧ ν.IsBounded ε := by
  intro k
  induction k with
  | zero =>
      intro μ ν ε
      cases μ with
      | base left hleft =>
          cases ν with
          | base right hright =>
              simp only [infimum, IsBounded, lt_min_iff]
              tauto
  | succ k ih =>
      intro μ ν ε
      cases μ with
      | step left leftLast hleft =>
          cases ν with
          | step right rightLast hright =>
              simp only [infimum, IsBounded, ih, lt_min_iff]
              tauto

theorem infimum_refines_left {k : ℕ}
    (μ ν : CharbonnelModulus k) : (infimum μ ν).Refines μ := by
  intro ε hε
  exact (isBounded_infimum_iff μ ν ε).mp hε |>.1

theorem infimum_refines_right {k : ℕ}
    (μ ν : CharbonnelModulus k) : (infimum μ ν).Refines ν := by
  intro ε hε
  exact (isBounded_infimum_iff μ ν ε).mp hε |>.2

theorem exists_common_refinement {k : ℕ}
    (μ ν : CharbonnelModulus k) :
    ∃ ξ : CharbonnelModulus k, ξ.Refines μ ∧ ξ.Refines ν :=
  ⟨infimum μ ν, infimum_refines_left μ ν,
    infimum_refines_right μ ν⟩

/-- The `k` stored parameters `ε₁, ..., ε_k`, obtained by dropping `ε₀`. -/
def parameterTail {k : ℕ} (ε : RealEuclidean (k + 1)) :
    RealEuclidean k :=
  fun i => ε i.succ

/-- Approximation from below: each point of a sufficiently small parameter
section of `T` lies within `ε₀` of `A`. -/
def ApproximatesFromBelow {n k : ℕ} (μ : CharbonnelModulus k)
    (T : Set (RealEuclidean (n + k))) (A : Set (RealEuclidean n)) : Prop :=
  ∀ ε : RealEuclidean (k + 1), μ.IsBounded ε →
    ∀ x : RealEuclidean n,
      realEuclideanAppend x (parameterTail ε) ∈ T →
        ∃ y ∈ A, dist x y < ε 0

/-- Approximation from above on bounded sets: every point of `A` in the
`ε₀⁻¹` ball lies within `ε₀` of the corresponding parameter section of `T`.
The norm on a finite function space is the maximum norm used in the source. -/
def ApproximatesFromAboveOnBoundedSets {n k : ℕ}
    (μ : CharbonnelModulus k)
    (A : Set (RealEuclidean n)) (T : Set (RealEuclidean (n + k))) : Prop :=
  ∀ ε : RealEuclidean (k + 1), μ.IsBounded ε →
    ∀ x ∈ A, ‖x‖ < (ε 0)⁻¹ →
      ∃ y : RealEuclidean n,
        dist x y < ε 0 ∧
          realEuclideanAppend y (parameterTail ε) ∈ T

theorem ApproximatesFromBelow.mono_modulus {n k : ℕ}
    {μ ν : CharbonnelModulus k}
    {T : Set (RealEuclidean (n + k))} {A : Set (RealEuclidean n)}
    (h : ApproximatesFromBelow μ T A) (hrefine : ν.Refines μ) :
    ApproximatesFromBelow ν T A := by
  intro ε hε x hx
  exact h ε (hrefine ε hε) x hx

theorem ApproximatesFromAboveOnBoundedSets.mono_modulus {n k : ℕ}
    {μ ν : CharbonnelModulus k}
    {A : Set (RealEuclidean n)} {T : Set (RealEuclidean (n + k))}
    (h : ApproximatesFromAboveOnBoundedSets μ A T)
    (hrefine : ν.Refines μ) :
    ApproximatesFromAboveOnBoundedSets ν A T := by
  intro ε hε x hxA hxnorm
  exact h ε (hrefine ε hε) x hxA hxnorm

/-- The two approximation directions used together in Wilkie's `3.6`. -/
def IsTwoSidedApproximation {n k : ℕ} (μ : CharbonnelModulus k)
    (T : Set (RealEuclidean (n + k))) (A : Set (RealEuclidean n)) : Prop :=
  ApproximatesFromBelow μ T A ∧
    ApproximatesFromAboveOnBoundedSets μ A T

theorem IsTwoSidedApproximation.mono_modulus {n k : ℕ}
    {μ ν : CharbonnelModulus k}
    {T : Set (RealEuclidean (n + k))} {A : Set (RealEuclidean n)}
    (h : IsTwoSidedApproximation μ T A) (hrefine : ν.Refines μ) :
    IsTwoSidedApproximation ν T A :=
  ⟨h.1.mono_modulus hrefine, h.2.mono_modulus hrefine⟩

/-- Two approximation statements of the same complexity can be made with one
common, tighter modulus. -/
theorem exists_common_modulus_for_two_approximations
    {n m k : ℕ} {μ ν : CharbonnelModulus k}
    {T : Set (RealEuclidean (n + k))} {A : Set (RealEuclidean n)}
    {U : Set (RealEuclidean (m + k))} {B : Set (RealEuclidean m)}
    (hT : IsTwoSidedApproximation μ T A)
    (hU : IsTwoSidedApproximation ν U B) :
    ∃ ξ : CharbonnelModulus k,
      IsTwoSidedApproximation ξ T A ∧
        IsTwoSidedApproximation ξ U B := by
  refine ⟨infimum μ ν,
    hT.mono_modulus (infimum_refines_left μ ν),
    hU.mono_modulus (infimum_refines_right μ ν)⟩

theorem ApproximatesFromBelow.union {n k : ℕ}
    {μ : CharbonnelModulus k}
    {T U : Set (RealEuclidean (n + k))} {A B : Set (RealEuclidean n)}
    (hT : ApproximatesFromBelow μ T A)
    (hU : ApproximatesFromBelow μ U B) :
    ApproximatesFromBelow μ (T ∪ U) (A ∪ B) := by
  intro ε hε x hx
  rcases hx with hxT | hxU
  · obtain ⟨y, hyA, hxy⟩ := hT ε hε x hxT
    exact ⟨y, Or.inl hyA, hxy⟩
  · obtain ⟨y, hyB, hxy⟩ := hU ε hε x hxU
    exact ⟨y, Or.inr hyB, hxy⟩

theorem ApproximatesFromAboveOnBoundedSets.union {n k : ℕ}
    {μ : CharbonnelModulus k}
    {A B : Set (RealEuclidean n)} {T U : Set (RealEuclidean (n + k))}
    (hT : ApproximatesFromAboveOnBoundedSets μ A T)
    (hU : ApproximatesFromAboveOnBoundedSets μ B U) :
    ApproximatesFromAboveOnBoundedSets μ (A ∪ B) (T ∪ U) := by
  intro ε hε x hx hxnorm
  rcases hx with hxA | hxB
  · obtain ⟨y, hxy, hyT⟩ := hT ε hε x hxA hxnorm
    exact ⟨y, hxy, Or.inl hyT⟩
  · obtain ⟨y, hxy, hyU⟩ := hU ε hε x hxB hxnorm
    exact ⟨y, hxy, Or.inr hyU⟩

/-- Two-sided approximations with a common modulus are closed under finite
union, the elementary content of Wilkie's Lemma 3.7. -/
theorem IsTwoSidedApproximation.union {n k : ℕ}
    {μ : CharbonnelModulus k}
    {T U : Set (RealEuclidean (n + k))} {A B : Set (RealEuclidean n)}
    (hT : IsTwoSidedApproximation μ T A)
    (hU : IsTwoSidedApproximation μ U B) :
    IsTwoSidedApproximation μ (T ∪ U) (A ∪ B) :=
  ⟨hT.1.union hU.1, hT.2.union hU.2⟩

end CharbonnelModulus

end AbelFormalization
