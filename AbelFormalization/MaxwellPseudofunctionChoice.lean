import AbelFormalization.MaxwellPseudofunction

/-!
# Choosing representatives of Maxwell pseudofunctions

The representative used in Maxwell's regularity argument need not itself be
chosen definably: its graph is already the family member relation.  Ordinary
classical choice therefore gives a total ambient function, and the null
multivalued locus is precisely the set that must be removed for the relation
to represent that function exactly.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Choose one value from a nonempty relation fiber, using zero when the fiber
is empty. -/
noncomputable def maxwellChosenValue {p q : ℕ}
    (R : MaxwellRelation p q) (x : RealEuclidean p) :
    RealEuclidean q := by
  classical
  exact if h : (maxwellRelationFiber R x).Nonempty then Classical.choose h else 0

/-- The chosen value lies in every nonempty fiber. -/
theorem maxwellChosenValue_mem_of_fiber_nonempty {p q : ℕ}
    (R : MaxwellRelation p q) (x : RealEuclidean p)
    (h : (maxwellRelationFiber R x).Nonempty) :
    maxwellChosenValue R x ∈ maxwellRelationFiber R x := by
  rw [maxwellChosenValue, dif_pos h]
  exact Classical.choose_spec h

/-- Full fibers over `U` make the chosen value a relation value on `U`. -/
theorem MaxwellHasFullFibersOver.maxwellChosenValue_mem {p q : ℕ}
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p q}
    (h : MaxwellHasFullFibersOver U R) {x : RealEuclidean p}
    (hx : x ∈ U) :
    realEuclideanAppend x (maxwellChosenValue R x) ∈ R := by
  exact maxwellChosenValue_mem_of_fiber_nonempty R x (h x hx)

/-- Away from the multivalued locus every relation value equals the chosen
one. -/
theorem eq_maxwellChosenValue_of_not_mem_multivaluedLocus {p q : ℕ}
    {R : MaxwellRelation p q} {x : RealEuclidean p}
    (hx : x ∉ maxwellMultivaluedLocus R)
    {y : RealEuclidean q} (hy : realEuclideanAppend x y ∈ R) :
    y = maxwellChosenValue R x := by
  have hchosen :
      realEuclideanAppend x (maxwellChosenValue R x) ∈ R :=
    maxwellChosenValue_mem_of_fiber_nonempty R x ⟨y, hy⟩
  by_contra hne
  exact hx ⟨y, maxwellChosenValue R x, hy, hchosen, hne⟩

/-- A full relation is represented exactly by its chosen function after its
multivalued locus is removed. -/
theorem MaxwellHasFullFibersOver.representsOn_maxwellChosenValue {p q : ℕ}
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p q}
    (h : MaxwellHasFullFibersOver U R) :
    MaxwellRelation.RepresentsOn R
      (U \ maxwellMultivaluedLocus R) (maxwellChosenValue R) := by
  intro x hx y
  constructor
  · exact eq_maxwellChosenValue_of_not_mem_multivaluedLocus hx.2
  · rintro rfl
    exact h.maxwellChosenValue_mem hx.1

/-- The canonical representative supplied by a pseudofunction on `U`. -/
theorem IsMaxwellPseudofunctionOn.representsOn_maxwellChosenValue {p q : ℕ}
    {U : Set (RealEuclidean p)} {R : MaxwellRelation p q}
    (h : IsMaxwellPseudofunctionOn U R) :
    MaxwellRelation.RepresentsOn R
      (U \ maxwellMultivaluedLocus R) (maxwellChosenValue R) :=
  h.full_fibers.representsOn_maxwellChosenValue

/-- The same representation on the complement of any larger exceptional
set. -/
theorem IsMaxwellPseudofunctionOn.representsOn_maxwellChosenValue_of_subset
    {p q : ℕ} {U A : Set (RealEuclidean p)}
    {R : MaxwellRelation p q}
    (h : IsMaxwellPseudofunctionOn U R)
    (hbad : maxwellMultivaluedLocus R ⊆ A) :
    MaxwellRelation.RepresentsOn R (U \ A) (maxwellChosenValue R) := by
  apply h.representsOn_maxwellChosenValue.mono
  intro x hx
  exact ⟨hx.1, fun hmulti ↦ hx.2 (hbad hmulti)⟩

/-- Read the unique coordinate of the chosen value of a scalar relation. -/
noncomputable def maxwellChosenScalarValue {p : ℕ}
    (R : MaxwellRelation p 1) (x : RealEuclidean p) : ℝ :=
  maxwellChosenValue R x 0

theorem maxwellChosenValue_eq_scalar {p : ℕ}
    (R : MaxwellRelation p 1) (x : RealEuclidean p) :
    maxwellChosenValue R x =
      (fun _ : Fin 1 ↦ maxwellChosenScalarValue R x) := by
  funext j
  rw [show j = 0 from Fin.eq_zero j]
  rfl

/-- Scalar form of the canonical representation, matching the function type
used by the differentiability-order induction. -/
theorem IsMaxwellPseudofunctionOn.representsOn_maxwellChosenScalarValue_of_subset
    {p : ℕ} {U A : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1}
    (h : IsMaxwellPseudofunctionOn U R)
    (hbad : maxwellMultivaluedLocus R ⊆ A) :
    MaxwellRelation.RepresentsOn R (U \ A)
      (fun x _ ↦ maxwellChosenScalarValue R x) := by
  intro x hx y
  change realEuclideanAppend x y ∈ R ↔
    y = (fun _ : Fin 1 ↦ maxwellChosenScalarValue R x)
  rw [← maxwellChosenValue_eq_scalar R x]
  exact h.representsOn_maxwellChosenValue_of_subset hbad x hx y

end AbelFormalization
