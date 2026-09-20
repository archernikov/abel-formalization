import AbelFormalization.CharbonnelOrderedSelectorCells
import AbelFormalization.WilkieBoundedCompactification

/-!
# Relative compatible covers and set difference

A finite relative cell cover of `D` compatible with `A` writes `D \ A` as
the union of exactly those cover cells which are disjoint from `A`.  Since
the selected index type is finite, empty-set membership and binary-union
closure put this difference in the ambient family.  No complement closure is
used.

The final statements specialize the result to a Charbonnel closure and to
Wilkie's open cube.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A union over an arbitrary finite type belongs to a family closed under
the empty set and binary unions. -/
theorem finite_iUnion_mem_of_finite
    {X ι : Type*} [Finite ι] {C : Set (Set X)}
    (hempty : (∅ : Set X) ∈ C)
    (hunion : ∀ {A B : Set X}, A ∈ C → B ∈ C → A ∪ B ∈ C)
    (s : ι → Set X) (hs : ∀ i, s i ∈ C) :
    (⋃ i, s i) ∈ C := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι :=
    (Fintype.equivFin ι).symm
  have hfinite :
      (⋃ j : Fin (Fintype.card ι), s (e j)) ∈ C :=
    finite_iUnion_mem hempty hunion
      (fun j ↦ s (e j)) (fun j ↦ hs (e j))
  have hreindex :
      (⋃ j : Fin (Fintype.card ι), s (e j)) = ⋃ i, s i := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨e j, hj⟩
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, by simpa⟩
  rwa [hreindex] at hfinite

namespace CharbonnelFiniteCompatibleRelativeCellCover

/-- The union of the cells in a relative compatible cover which are
disjoint from its target. -/
def outside
    {C : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleRelativeCellCover C D A) :
    Set (RealEuclidean n) :=
  ⋃ i : {i : cover.Index // Disjoint (cover.cell i).carrier A},
    (cover.cell i.1).carrier

/-- The disjoint cells in a relative compatible cover cover exactly the
part of the carrier outside the target. -/
theorem outside_eq_sdiff
    {C : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleRelativeCellCover C D A) :
    cover.outside = D \ A := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact ⟨cover.contained i.1 hxi,
      fun hxA ↦ Set.disjoint_left.mp i.2 hxi hxA⟩
  · rintro ⟨hxD, hxnotA⟩
    obtain ⟨i, hxi⟩ := cover.covers x hxD
    rcases cover.compatible i with hsubset | hdisjoint
    · exact (hxnotA (hsubset hxi)).elim
    · exact Set.mem_iUnion.mpr ⟨⟨i, hdisjoint⟩, hxi⟩

/-- A relative compatible cover exhibits the set difference as a finite
union of family-member cells disjoint from the target. -/
theorem sdiff_eq_iUnion_disjoint_cells
    {C : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleRelativeCellCover C D A) :
    D \ A =
      ⋃ i : {i : cover.Index // Disjoint (cover.cell i).carrier A},
        (cover.cell i.1).carrier := by
  simpa only [outside] using cover.outside_eq_sdiff.symm

/-- Empty-set membership and binary-union closure turn a relative compatible
cover into family membership of the covered carrier minus the target. -/
theorem sdiff_mem
    {C : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleRelativeCellCover C D A)
    (hempty : (∅ : Set (RealEuclidean n)) ∈ C n)
    (hunion : ∀ {left right : Set (RealEuclidean n)},
      left ∈ C n → right ∈ C n → left ∪ right ∈ C n) :
    D \ A ∈ C n := by
  classical
  let _ : Finite cover.Index := cover.indexFinite
  have houtside : cover.outside ∈ C n := by
    apply finite_iUnion_mem_of_finite hempty hunion
    intro i
    exact (cover.cell i.1).carrier_mem
  rwa [cover.outside_eq_sdiff] at houtside

/-- Intersection-with-the-complement spelling of `sdiff_mem`.  The proof
still uses only finite unions and the empty set. -/
theorem inter_compl_mem
    {C : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleRelativeCellCover C D A)
    (hempty : (∅ : Set (RealEuclidean n)) ∈ C n)
    (hunion : ∀ {left right : Set (RealEuclidean n)},
      left ∈ C n → right ∈ C n → left ∪ right ∈ C n) :
    D ∩ Aᶜ ∈ C n := by
  simpa only [Set.sdiff_eq] using cover.sdiff_mem hempty hunion

/-- In a Charbonnel closure, binary-union closure is built in, so only
empty-set membership in the relevant arity is needed. -/
theorem sdiff_mem_charbonnelClosure
    {S : EuclideanSetFamily} {n : ℕ}
    {D A : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleRelativeCellCover
      (charbonnelClosure S) D A)
    (hempty : (∅ : Set (RealEuclidean n)) ∈ charbonnelClosure S n) :
    D \ A ∈ charbonnelClosure S n :=
  cover.sdiff_mem hempty
    (fun hleft hright ↦ charbonnelClosure_union hleft hright)

/-- A positive-arity weak-set structure supplies the empty set needed by
`sdiff_mem_charbonnelClosure`. -/
theorem sdiff_mem_charbonnelClosure_of_weakSetStructure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {D A : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleRelativeCellCover
      (charbonnelClosure S) D A) :
    D \ A ∈ charbonnelClosure S n :=
  cover.sdiff_mem_charbonnelClosure
    (hC.ws2_polynomialSign hn (polynomialSignConstructible_empty n))

end CharbonnelFiniteCompatibleRelativeCellCover

/-! ## Bounded-coordinate endpoint -/

/-- A relative compatible cell cover of Wilkie's open cube puts the part of
the cube outside `T` in any family with the empty-set and finite-union
operations. -/
theorem wilkieOpenCube_sdiff_mem_of_relativeCellCover
    {C : EuclideanSetFamily} {n : ℕ}
    {T : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleRelativeCellCover C
      (wilkieOpenCube n) T)
    (hempty : (∅ : Set (RealEuclidean n)) ∈ C n)
    (hunion : ∀ {left right : Set (RealEuclidean n)},
      left ∈ C n → right ∈ C n → left ∪ right ∈ C n) :
    wilkieOpenCube n \ T ∈ C n :=
  cover.sdiff_mem hempty hunion

/-- Charbonnel-closure specialization of the bounded-coordinate endpoint. -/
theorem wilkieOpenCube_sdiff_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    {T : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleRelativeCellCover
      (charbonnelClosure S) (wilkieOpenCube n) T) :
    wilkieOpenCube n \ T ∈ charbonnelClosure S n :=
  cover.sdiff_mem_charbonnelClosure_of_weakSetStructure hC hn

end AbelFormalization
