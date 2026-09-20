import AbelFormalization.CharbonnelApproximationTrace

/-!
# The boundary approximation used in Wilkie's induction

Wilkie's condition 3.6 uses two different target sets.  An approximant `T`
lies close to `closure A`, while only `frontier (closure A)` is required to
lie close to the corresponding small-parameter sections of `T`.

The older same-target predicate `CharbonnelModulus.IsTwoSidedApproximation`
is useful when that stronger property happens to hold, but it is not the
literal pair of approximation clauses in 3.6 for a set with interior.  This
file records the asymmetric predicate and connects its boundary half to the
already formalized trace descent of Wilkie's Lemma 3.3.  The remaining parts
of 3.6--positive parameter depth and a finite union of smooth constituents--
are packaged separately by `CharbonnelSardianApproximationCertificate`.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

namespace CharbonnelModulus

/-- The two asymmetric approximation clauses in Wilkie's condition 3.6 for
a set `A`: the approximation is close to `closure A` from below, and
approximates the boundary of `closure A` from above on bounded sets.

This semantic predicate also makes sense at parameter depth zero.  The full
condition 3.6 additionally asks for positive depth and a finite union of
smooth constituents. -/
def IsClosureBoundaryApproximation {n k : ℕ}
    (modulus : CharbonnelModulus k)
    (T : Set (RealEuclidean (n + k)))
    (A : Set (RealEuclidean n)) : Prop :=
  ApproximatesFromBelow modulus T (closure A) ∧
    ApproximatesFromAboveOnBoundedSets modulus
      (frontier (closure A)) T

theorem IsClosureBoundaryApproximation.approximatesFromBelow
    {n k : ℕ} {modulus : CharbonnelModulus k}
    {T : Set (RealEuclidean (n + k))}
    {A : Set (RealEuclidean n)}
    (h : IsClosureBoundaryApproximation modulus T A) :
    ApproximatesFromBelow modulus T (closure A) :=
  h.1

theorem IsClosureBoundaryApproximation.approximatesBoundaryFromAbove
    {n k : ℕ} {modulus : CharbonnelModulus k}
    {T : Set (RealEuclidean (n + k))}
    {A : Set (RealEuclidean n)}
    (h : IsClosureBoundaryApproximation modulus T A) :
    ApproximatesFromAboveOnBoundedSets modulus
      (frontier (closure A)) T :=
  h.2

theorem IsClosureBoundaryApproximation.mono_modulus
    {n k : ℕ} {modulus tighter : CharbonnelModulus k}
    {T : Set (RealEuclidean (n + k))}
    {A : Set (RealEuclidean n)}
    (h : IsClosureBoundaryApproximation modulus T A)
    (hrefine : tighter.Refines modulus) :
    IsClosureBoundaryApproximation tighter T A :=
  ⟨h.1.mono_modulus hrefine, h.2.mono_modulus hrefine⟩

/-- Approximation from above is contravariant in its target set. -/
theorem ApproximatesFromAboveOnBoundedSets.mono_target
    {n k : ℕ} {modulus : CharbonnelModulus k}
    {A B : Set (RealEuclidean n)}
    {T : Set (RealEuclidean (n + k))}
    (h : ApproximatesFromAboveOnBoundedSets modulus B T)
    (hAB : A ⊆ B) :
    ApproximatesFromAboveOnBoundedSets modulus A T := by
  intro ε hε x hx hnorm
  exact h ε hε x (hAB hx) hnorm

/-- A same-target approximation of `closure A` implies the asymmetric
clauses for `A`.  This is the bridge from the older, stronger predicate:
the boundary of a set is contained in its closure. -/
theorem IsTwoSidedApproximation.toClosureBoundaryApproximation
    {n k : ℕ} {modulus : CharbonnelModulus k}
    {T : Set (RealEuclidean (n + k))}
    {A : Set (RealEuclidean n)}
    (h : IsTwoSidedApproximation modulus T (closure A)) :
    IsClosureBoundaryApproximation modulus T A :=
  ⟨h.1, h.2.mono_target isClosed_closure.frontier_subset⟩

/-- Wilkie's asymmetric approximation clauses are preserved by binary union
when the two inputs already have one common parameter depth and modulus.
This is the topological core of Lemma 3.7; the source also pads unequal
depths before applying it and then iterates over a finite family. -/
theorem IsClosureBoundaryApproximation.union
    {n k : ℕ} {modulus : CharbonnelModulus k}
    {T U : Set (RealEuclidean (n + k))}
    {A B : Set (RealEuclidean n)}
    (hT : IsClosureBoundaryApproximation modulus T A)
    (hU : IsClosureBoundaryApproximation modulus U B) :
    IsClosureBoundaryApproximation modulus (T ∪ U) (A ∪ B) := by
  constructor
  · rw [closure_union]
    exact hT.1.union hU.1
  · have hfrontier :
        frontier (closure (A ∪ B)) ⊆
          frontier (closure A) ∪ frontier (closure B) := by
      rw [closure_union]
      apply (frontier_union_subset (closure A) (closure B)).trans
      exact union_subset
        (inter_subset_left.trans subset_union_left)
        (inter_subset_right.trans subset_union_right)
    exact (hT.2.union hU.2).mono_target hfrontier

/-- Two same-depth approximation statements can first be tightened to the
pointwise infimum of their moduli and then united. -/
theorem exists_common_modulus_union
    {n k : ℕ} {leftModulus rightModulus : CharbonnelModulus k}
    {T U : Set (RealEuclidean (n + k))}
    {A B : Set (RealEuclidean n)}
    (hT : IsClosureBoundaryApproximation leftModulus T A)
    (hU : IsClosureBoundaryApproximation rightModulus U B) :
    ∃ common : CharbonnelModulus k,
      IsClosureBoundaryApproximation common (T ∪ U) (A ∪ B) := by
  refine ⟨infimum leftModulus rightModulus, ?_⟩
  exact
    (hT.mono_modulus (infimum_refines_left leftModulus rightModulus)).union
      (hU.mono_modulus (infimum_refines_right leftModulus rightModulus))

/-- For a closed target, the asymmetric condition simplifies to approximation
of the target and its ordinary frontier. -/
theorem isClosureBoundaryApproximation_iff_of_isClosed
    {n k : ℕ} {modulus : CharbonnelModulus k}
    {T : Set (RealEuclidean (n + k))}
    {A : Set (RealEuclidean n)} (hA : IsClosed A) :
    IsClosureBoundaryApproximation modulus T A ↔
      ApproximatesFromBelow modulus T A ∧
        ApproximatesFromAboveOnBoundedSets modulus (frontier A) T := by
  simp only [IsClosureBoundaryApproximation, hA.closure_eq]

end CharbonnelModulus

/-! ## Connection to trace descent -/

/-- The boundary half of condition 3.6 supplies the approximation hypothesis
of Wilkie's Lemma 3.3 for the closed target `closure A`. -/
theorem CharbonnelModulus.IsClosureBoundaryApproximation.exists_boundaryCarrier
    {C : EuclideanSetFamily}
    (hC : CharbonnelApproximationTraceTameness C)
    {n k : ℕ} (hn : 0 < n)
    {A : Set (RealEuclidean n)}
    {T : Set (RealEuclidean (n + k))}
    (hTmem : T ∈ C (n + k))
    (hTempty : interior T = ∅)
    {modulus : CharbonnelModulus k}
    (happrox : CharbonnelModulus.IsClosureBoundaryApproximation
      modulus T A) :
    ∃ B : Set (RealEuclidean n),
      IsClosed B ∧ B ∈ C n ∧ interior B = ∅ ∧
        frontier (closure A) ⊆ B := by
  exact exists_closed_emptyInterior_boundaryCarrier_of_approximatesFromAbove
    hC hn (closure A) hTmem hTempty modulus happrox.2

end AbelFormalization
