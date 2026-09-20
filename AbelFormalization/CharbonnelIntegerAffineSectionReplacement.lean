import AbelFormalization.CharbonnelSardianRankConstructorReduction
import AbelFormalization.CharbonnelIntegerAffineSliceMetric

/-!
# The three-piece replacement for a closed affine section

Wilkie 3.13 splits the first closed hyperplane section into the closure of
the exact section and the traces of two one-sided closures. The latter are
the targets of the frontier-hyperplane argument of 3.12. This module proves
the carrier identity and the resulting conditional finite-certificate glue.
It does not assert that the one-sided certificates exist, or turn weak-
structure stage descent into numeric description-rank descent.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Finite-partition form of Wilkie 3.13's first-hyperplane replacement.
No disjointness of the three cells is required. Closedness of `H` removes
the redundant intersection from the closure of the exact section. -/
theorem closure_inter_closed_three_piece
    {X : Type*} [TopologicalSpace X]
    (B H P N : Set X) (hH : IsClosed H)
    (hcover : ∀ x : X, x ∈ H ∨ x ∈ P ∨ x ∈ N) :
    closure B ∩ H =
      (closure (B ∩ H) ∪ (closure (B ∩ P) ∩ H)) ∪
        (closure (B ∩ N) ∩ H) := by
  have hpartition : B = (B ∩ H ∪ B ∩ P) ∪ B ∩ N := by
    ext x
    constructor
    · intro hxB
      rcases hcover x with hxH | hxP | hxN
      · exact Or.inl (Or.inl ⟨hxB, hxH⟩)
      · exact Or.inl (Or.inr ⟨hxB, hxP⟩)
      · exact Or.inr ⟨hxB, hxN⟩
    · intro hx
      rcases hx with (hxFirst | hxLast)
      · rcases hxFirst with hxExact | hxPositive
        · exact hxExact.1
        · exact hxPositive.1
      · exact hxLast.1
  have hclosedSection : closure (B ∩ H) ⊆ H := by
    have hsubset : closure (B ∩ H) ⊆ closure H :=
      closure_mono Set.inter_subset_right
    simpa only [hH.closure_eq] using hsubset
  have hclosure : closure B =
      (closure (B ∩ H) ∪ closure (B ∩ P)) ∪ closure (B ∩ N) := by
    calc
      closure B = closure ((B ∩ H ∪ B ∩ P) ∪ B ∩ N) :=
        congrArg closure hpartition
      _ = (closure (B ∩ H) ∪ closure (B ∩ P)) ∪
          closure (B ∩ N) := by rw [closure_union, closure_union]
  rw [hclosure]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union]
  constructor
  · intro hx
    rcases hx with ⟨hxUnion, hxH⟩
    rcases hxUnion with hxFirst | hxNegative
    · rcases hxFirst with hxExact | hxPositive
      · exact Or.inl (Or.inl hxExact)
      · exact Or.inl (Or.inr ⟨hxPositive, hxH⟩)
    · exact Or.inr ⟨hxNegative, hxH⟩
  · intro hx
    rcases hx with hxFirst | hxNegative
    · rcases hxFirst with hxExact | hxPositive
      · exact ⟨Or.inl (Or.inl hxExact), hclosedSection hxExact⟩
      · exact ⟨Or.inl (Or.inr hxPositive.1), hxPositive.2⟩
    · exact ⟨Or.inr hxNegative.1, hxNegative.2⟩

/-- The two open sign cells in the displayed integer-affine form. -/
def integerAffineSlicePositiveSide {n : ℕ}
    (coeff : Fin n → ℤ) (constant : ℤ) : Set (RealEuclidean n) :=
  {x | 0 < integerAffineSliceLinearForm coeff constant x}

def integerAffineSliceNegativeSide {n : ℕ}
    (coeff : Fin n → ℤ) (constant : ℤ) : Set (RealEuclidean n) :=
  {x | integerAffineSliceLinearForm coeff constant x < 0}

/-- The exact first-cut identity, including zero-row degenerate cases. -/
theorem closure_inter_integerAffineSliceHyperplane_three_piece
    {n : ℕ} (B : Set (RealEuclidean n))
    (coeff : Fin n → ℤ) (constant : ℤ) :
    closure B ∩ integerAffineSliceHyperplane coeff constant =
      (closure (B ∩ integerAffineSliceHyperplane coeff constant) ∪
        (closure (B ∩ integerAffineSlicePositiveSide coeff constant) ∩
          integerAffineSliceHyperplane coeff constant)) ∪
        (closure (B ∩ integerAffineSliceNegativeSide coeff constant) ∩
          integerAffineSliceHyperplane coeff constant) := by
  apply closure_inter_closed_three_piece B
    (integerAffineSliceHyperplane coeff constant)
    (integerAffineSlicePositiveSide coeff constant)
    (integerAffineSliceNegativeSide coeff constant)
    (isClosed_integerAffineSliceHyperplane coeff constant)
  intro x
  rcases lt_trichotomy (integerAffineSliceLinearForm coeff constant x) 0 with
    hnegative | hzero | hpositive
  · exact Or.inr (Or.inr hnegative)
  · exact Or.inl hzero
  · exact Or.inr (Or.inl hpositive)

/-- The topological side condition behind the 3.12 application: if the
slice avoids the interior of the closure of a sign cell, it also avoids
the interior of every smaller one-sided closure. The nonzero-affine-row
instance of the premise is separate geometry, not a certificate theorem. -/
theorem oneSidedClosure_frontier_trace_of_avoid
    {X : Type*} [TopologicalSpace X]
    (B H P : Set X)
    (havoid : interior (closure P) ∩ H = ∅) :
    closure (B ∩ P) ∩ H =
      frontier (closure (B ∩ P)) ∩ H := by
  have hclosed : IsClosed (closure (B ∩ P)) := isClosed_closure
  apply (closed_slice_frontier_condition_iff hclosed).mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hsubset : closure (B ∩ P) ⊆ closure P :=
    closure_mono Set.inter_subset_right
  have hxP : x ∈ interior (closure P) ∩ H :=
    ⟨interior_mono hsubset hx.1, hx.2⟩
  simpa [havoid] using hxP

/-- Three independently supplied condition-3.6 certificates combine for
the closed section. The first certificate targets the exact `B ∩ H`; its
closure is free because condition 3.6 depends only on target closure. The
two trace certificates are exactly the output required from Wilkie 3.12. -/
def closedSectionSardianCertificate_of_threeInputs
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {n order : ℕ} (B H P N : Set (RealEuclidean n))
    (hH : IsClosed H)
    (hcover : ∀ x : RealEuclidean n, x ∈ H ∨ x ∈ P ∨ x ∈ N)
    (hexact : CharbonnelSardianApproximationCertificate
      G order n (B ∩ H))
    (hpositive : CharbonnelSardianApproximationCertificate
      G order n (closure (B ∩ P) ∩ H))
    (hnegative : CharbonnelSardianApproximationCertificate
      G order n (closure (B ∩ N) ∩ H)) :
    CharbonnelSardianApproximationCertificate
      G order n (closure B ∩ H) := by
  let first := hexact.topologicalClosure.unionOfAnyHiddenArity hpositive
  let combined := first.unionOfAnyHiddenArity hnegative
  have htarget := closure_inter_closed_three_piece B H P N hH hcover
  rw [htarget]
  exact combined

end AbelFormalization
