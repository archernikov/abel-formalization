import AbelFormalization.CharbonnelClosedBoundaryCellAssembly

/-!
# Ordered selector cells over a Charbonnel base cell

This module formalizes the elementary full-dimensional part of Wilkie's
section 4 cell construction.  Over one recursive base cell, a finite strictly
ordered family of continuous selector graphs cuts the whole cylinder into
the graphs themselves, the intervening open bands, and the two outer rays.

The family-membership obligation for every resulting graph, band, and ray is
kept explicit.  Thus the construction does not use complement closure.  An
exact fibre description makes the graph cells lie in the target set and all
open cells disjoint from it.  The final flattening theorem composes these
relative covers over any finite base-cell cover.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Relative finite cell covers -/

/-- A finite family of recursive cells covering a specified carrier `D` and
compatible with `A`.  The index is allowed to be any finite type; this makes
dependent flattening over a finite base cover transparent. -/
structure CharbonnelFiniteCompatibleRelativeCellCover
    (C : EuclideanSetFamily) {n : ℕ}
    (D A : Set (RealEuclidean n)) where
  Index : Type
  indexFinite : Finite Index
  cell : Index → CharbonnelCell C n
  contained : ∀ i, (cell i).carrier ⊆ D
  covers : ∀ x ∈ D, ∃ i, x ∈ (cell i).carrier
  compatible : ∀ i, (cell i).carrier ⊆ A ∨
    Disjoint (cell i).carrier A

namespace CharbonnelFiniteCompatibleRelativeCellCover

/-- A relative cover of the whole space is an ordinary finite compatible
cell cover. -/
noncomputable def toGlobal
    {C : EuclideanSetFamily} {n : ℕ} {A : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleRelativeCellCover C Set.univ A) :
    CharbonnelFiniteCompatibleCellCover C A := by
  classical
  letI : Finite cover.Index := cover.indexFinite
  letI : Fintype cover.Index := Fintype.ofFinite cover.Index
  let e : Fin (Fintype.card cover.Index) ≃ cover.Index :=
    (Fintype.equivFin cover.Index).symm
  exact
    { count := Fintype.card cover.Index
      cell := fun i ↦ cover.cell (e i)
      covers := by
        intro x
        obtain ⟨i, hi⟩ := cover.covers x (by simp)
        exact ⟨e.symm i, by simpa⟩
      compatible := fun i ↦ cover.compatible (e i) }

end CharbonnelFiniteCompatibleRelativeCellCover

/-! ## The finite ordered-selector partition -/

/-- The cells cut out by `r > 0` ordered selectors: a lower ray, every
selector graph, every consecutive open band, and an upper ray. -/
inductive CharbonnelOrderedSelectorRegion (r : ℕ) where
  | lower
  | graph (i : Fin r)
  | band (i : Fin (r - 1))
  | upper
  deriving DecidableEq, Fintype

def charbonnelFirstSelectorIndex {r : ℕ} (hr : 0 < r) : Fin r :=
  ⟨0, hr⟩

def charbonnelLastSelectorIndex {r : ℕ} (hr : 0 < r) : Fin r :=
  ⟨r - 1, by omega⟩

def charbonnelBandLeftIndex {r : ℕ} (i : Fin (r - 1)) : Fin r :=
  ⟨i.1, lt_of_lt_of_le i.2 (Nat.sub_le r 1)⟩

def charbonnelBandRightIndex {r : ℕ} (i : Fin (r - 1)) : Fin r :=
  ⟨i.1 + 1, by omega⟩

theorem charbonnelBandLeftIndex_lt_rightIndex {r : ℕ}
    (i : Fin (r - 1)) :
    charbonnelBandLeftIndex i < charbonnelBandRightIndex i := by
  simp [charbonnelBandLeftIndex, charbonnelBandRightIndex]

/-- The scalar interval represented by one selector region. -/
def CharbonnelOrderedSelectorRegion.Contains {r : ℕ}
    (hr : 0 < r) (a : Fin r → ℝ) (y : ℝ) :
    CharbonnelOrderedSelectorRegion r → Prop
  | .lower => y < a (charbonnelFirstSelectorIndex hr)
  | .graph i => y = a i
  | .band i =>
      a (charbonnelBandLeftIndex i) < y ∧
        y < a (charbonnelBandRightIndex i)
  | .upper => a (charbonnelLastSelectorIndex hr) < y

/-- A nonempty finite list of scalar levels, in its given order, cuts the
line into the two outer rays, its levels, and consecutive gaps.  Strict
ordering is deliberately not needed for exhaustiveness; it enters below to
make the regions cells and make the open regions avoid the selector fibre. -/
theorem exists_charbonnelOrderedSelectorRegion_contains
    {r : ℕ} (hr : 0 < r) (a : Fin r → ℝ) (y : ℝ) :
    ∃ k : CharbonnelOrderedSelectorRegion r, k.Contains hr a y := by
  classical
  let last : Fin r := charbonnelLastSelectorIndex hr
  by_cases hu : a last < y
  · exact ⟨CharbonnelOrderedSelectorRegion.upper, hu⟩
  · have hlast : y ≤ a last := le_of_not_gt hu
    let s : Finset (Fin r) := Finset.univ.filter (fun i ↦ y ≤ a i)
    have hs : s.Nonempty := by
      refine ⟨last, ?_⟩
      simp [s, hlast]
    let i : Fin r := s.min' hs
    have his : i ∈ s := Finset.min'_mem s hs
    have hyi : y ≤ a i := by
      simpa [s] using his
    by_cases heq : y = a i
    · exact ⟨CharbonnelOrderedSelectorRegion.graph i, heq⟩
    · have hyilt : y < a i := lt_of_le_of_ne hyi heq
      by_cases hi0 : i.1 = 0
      · have hi : i = charbonnelFirstSelectorIndex hr := by
          apply Fin.ext
          simpa [charbonnelFirstSelectorIndex] using hi0
        exact ⟨CharbonnelOrderedSelectorRegion.lower, by
          simpa [CharbonnelOrderedSelectorRegion.Contains, hi] using hyilt⟩
      · let j : Fin (r - 1) := ⟨i.1 - 1, by omega⟩
        have hright : charbonnelBandRightIndex j = i := by
          apply Fin.ext
          simp [charbonnelBandRightIndex, j]
          omega
        have hleftlt : charbonnelBandLeftIndex j < i := by
          show (charbonnelBandLeftIndex j).1 < i.1
          simp [charbonnelBandLeftIndex, j]
          omega
        have hnotle : ¬ y ≤ a (charbonnelBandLeftIndex j) := by
          intro hle
          have hleftmem : charbonnelBandLeftIndex j ∈ s := by
            simp [s, hle]
          have hmin : i ≤ charbonnelBandLeftIndex j :=
            Finset.min'_le s _ hleftmem
          exact (not_lt_of_ge hmin) hleftlt
        exact ⟨CharbonnelOrderedSelectorRegion.band j,
          lt_of_not_ge hnotle, by simpa [hright] using hyilt⟩

/-- The ambient subset represented by a selector region over `base`. -/
def charbonnelOrderedSelectorRegionCarrier {n r : ℕ}
    (base : Set (RealEuclidean n))
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r) :
    CharbonnelOrderedSelectorRegion r → Set (RealEuclidean (n + 1))
  | .lower =>
      charbonnelLowerRayCell base (f (charbonnelFirstSelectorIndex hr))
  | .graph i => charbonnelRestrictedGraph base (f i)
  | .band i => charbonnelOpenBand base
      (f (charbonnelBandLeftIndex i))
      (f (charbonnelBandRightIndex i))
  | .upper =>
      charbonnelUpperRayCell base (f (charbonnelLastSelectorIndex hr))

/-- Each ordered-selector region has the recursive graph/band cell shape. -/
theorem charbonnelOrderedSelectorRegionCarrier_shape
    {n r : ℕ} (hn : 0 < n)
    {base : Set (RealEuclidean n)}
    (hbase : CharbonnelCellShape n base)
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hcontinuous : ∀ i, ContinuousOn (f i) base)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    (k : CharbonnelOrderedSelectorRegion r) :
    CharbonnelCellShape (n + 1)
      (charbonnelOrderedSelectorRegionCarrier base f hr k) := by
  cases k with
  | lower =>
      exact .lowerRay hn hbase _
        (hcontinuous (charbonnelFirstSelectorIndex hr))
  | graph i =>
      exact .graph hn hbase _ (hcontinuous i)
  | band i =>
      exact .band hn hbase _ _
        (hcontinuous (charbonnelBandLeftIndex i))
        (hcontinuous (charbonnelBandRightIndex i))
        (fun x hx ↦ hordered x hx
          (charbonnelBandLeftIndex_lt_rightIndex i))
  | upper =>
      exact .upperRay hn hbase _
        (hcontinuous (charbonnelLastSelectorIndex hr))

/-- Package a selector region as a family-member Charbonnel cell.  Membership
is an explicit hypothesis and uses no complement closure. -/
def charbonnelOrderedSelectorCell
    {C : EuclideanSetFamily} {n r : ℕ} (hn : 0 < n)
    {base : Set (RealEuclidean n)}
    (hbase : CharbonnelCellShape n base)
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hcontinuous : ∀ i, ContinuousOn (f i) base)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    (hmem : ∀ k, charbonnelOrderedSelectorRegionCarrier base f hr k ∈ C (n + 1))
    (k : CharbonnelOrderedSelectorRegion r) : CharbonnelCell C (n + 1) :=
  { carrier := charbonnelOrderedSelectorRegionCarrier base f hr k
    shape := charbonnelOrderedSelectorRegionCarrier_shape hn hbase f hr
      hcontinuous hordered k
    carrier_mem := hmem k }

/-! ## Compatibility with an exact selector fibre -/

/-- Under an exact-fibre description, graph regions lie in `A` and every
open region is disjoint from `A`. -/
theorem charbonnelOrderedSelectorRegionCarrier_compatible
    {n r : ℕ} {base : Set (RealEuclidean n)}
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    {A : Set (RealEuclidean (n + 1))}
    (hfiber : ∀ z, realEuclideanTakeLeft z ∈ base →
      (z ∈ A ↔ ∃ i, realEuclideanTakeRight z 0 =
        f i (realEuclideanTakeLeft z)))
    (k : CharbonnelOrderedSelectorRegion r) :
    charbonnelOrderedSelectorRegionCarrier base f hr k ⊆ A ∨
      Disjoint (charbonnelOrderedSelectorRegionCarrier base f hr k) A := by
  cases k with
  | graph i =>
      left
      intro z hz
      exact (hfiber z hz.1).2 ⟨i, hz.2⟩
  | lower =>
      right
      rw [Set.disjoint_left]
      intro z hz hzA
      obtain ⟨i, hi⟩ := (hfiber z hz.1).1 hzA
      have hindex : charbonnelFirstSelectorIndex hr ≤ i := by
        show (charbonnelFirstSelectorIndex hr).1 ≤ i.1
        simp [charbonnelFirstSelectorIndex]
      have hmono := (hordered _ hz.1).monotone hindex
      linarith [hz.2, hmono, hi]
  | upper =>
      right
      rw [Set.disjoint_left]
      intro z hz hzA
      obtain ⟨i, hi⟩ := (hfiber z hz.1).1 hzA
      have hindex : i ≤ charbonnelLastSelectorIndex hr := by
        show i.1 ≤ (charbonnelLastSelectorIndex hr).1
        simp [charbonnelLastSelectorIndex]
        omega
      have hmono := (hordered _ hz.1).monotone hindex
      linarith [hz.2, hmono, hi]
  | band j =>
      right
      rw [Set.disjoint_left]
      intro z hz hzA
      obtain ⟨i, hi⟩ := (hfiber z hz.1).1 hzA
      by_cases hile : i ≤ charbonnelBandLeftIndex j
      · have hmono := (hordered _ hz.1).monotone hile
        linarith [hz.2.1, hmono, hi]
      · have hrightle : charbonnelBandRightIndex j ≤ i := by
          show (charbonnelBandRightIndex j).1 ≤ i.1
          simp [charbonnelBandLeftIndex, charbonnelBandRightIndex] at hile ⊢
          omega
        have hmono := (hordered _ hz.1).monotone hrightle
        linarith [hz.2.2, hmono, hi]

/-- The graph, gap, and ray cells of a strictly ordered continuous selector
family form a finite compatible cover of the cylinder over one base cell. -/
def charbonnelOrderedSelectorRelativeCellCover
    {C : EuclideanSetFamily} {n r : ℕ} (hn : 0 < n)
    {base : Set (RealEuclidean n)}
    (hbase : CharbonnelCellShape n base)
    (f : Fin r → RealEuclidean n → ℝ) (hr : 0 < r)
    (hcontinuous : ∀ i, ContinuousOn (f i) base)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    {A : Set (RealEuclidean (n + 1))}
    (hfiber : ∀ z, realEuclideanTakeLeft z ∈ base →
      (z ∈ A ↔ ∃ i, realEuclideanTakeRight z 0 =
        f i (realEuclideanTakeLeft z)))
    (hmem : ∀ k, charbonnelOrderedSelectorRegionCarrier base f hr k ∈ C (n + 1)) :
    CharbonnelFiniteCompatibleRelativeCellCover C
      (charbonnelCylinderCell base) A := by
  let cell : CharbonnelOrderedSelectorRegion r → CharbonnelCell C (n + 1) :=
    charbonnelOrderedSelectorCell hn hbase f hr hcontinuous hordered hmem
  exact
    { Index := CharbonnelOrderedSelectorRegion r
      indexFinite := inferInstance
      cell := cell
      contained := by
        intro k z hz
        cases k <;>
          exact hz.1
      covers := by
        intro z hz
        obtain ⟨k, hk⟩ :=
          exists_charbonnelOrderedSelectorRegion_contains hr
            (fun i ↦ f i (realEuclideanTakeLeft z))
            (realEuclideanTakeRight z 0)
        refine ⟨k, ?_⟩
        cases k <;> exact ⟨hz, hk⟩
      compatible := fun k ↦
        charbonnelOrderedSelectorRegionCarrier_compatible
          f hr hordered hfiber k }

/-- If the exact fibre over a base cell is empty, the whole cylinder is a
single recursive cell disjoint from the target.  Cylinder membership in the
family is explicit. -/
def charbonnelEmptySelectorRelativeCellCover
    {C : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    {base : Set (RealEuclidean n)}
    (hbase : CharbonnelCellShape n base)
    {A : Set (RealEuclidean (n + 1))}
    (hfiberEmpty : ∀ z, realEuclideanTakeLeft z ∈ base → z ∉ A)
    (hmem : charbonnelCylinderCell base ∈ C (n + 1)) :
    CharbonnelFiniteCompatibleRelativeCellCover C
      (charbonnelCylinderCell base) A := by
  let cell : CharbonnelCell C (n + 1) :=
    { carrier := charbonnelCylinderCell base
      shape := .cylinder hn hbase
      carrier_mem := hmem }
  exact
    { Index := Unit
      indexFinite := inferInstance
      cell := fun _ ↦ cell
      contained := fun _ ↦ Subset.rfl
      covers := fun z hz ↦ ⟨(), hz⟩
      compatible := by
        intro _
        right
        rw [Set.disjoint_left]
        exact fun z hz hzA ↦ hfiberEmpty z hz hzA }

/-- Uniform single-base combinator for an arbitrary finite exact fibre.  The
zero-cardinality branch is one cylinder; a positive fibre is partitioned by
its ordered selectors. -/
noncomputable def charbonnelFiniteSelectorRelativeCellCover
    {C : EuclideanSetFamily} {n r : ℕ} (hn : 0 < n)
    {base : Set (RealEuclidean n)}
    (hbase : CharbonnelCellShape n base)
    (f : Fin r → RealEuclidean n → ℝ)
    (hcontinuous : ∀ i, ContinuousOn (f i) base)
    (hordered : ∀ x ∈ base, StrictMono (fun i ↦ f i x))
    {A : Set (RealEuclidean (n + 1))}
    (hfiber : ∀ z, realEuclideanTakeLeft z ∈ base →
      (z ∈ A ↔ ∃ i, realEuclideanTakeRight z 0 =
        f i (realEuclideanTakeLeft z)))
    (hzeroMem : r = 0 → charbonnelCylinderCell base ∈ C (n + 1))
    (hpositiveMem : ∀ (hr : 0 < r) k,
      charbonnelOrderedSelectorRegionCarrier base f hr k ∈ C (n + 1)) :
    CharbonnelFiniteCompatibleRelativeCellCover C
      (charbonnelCylinderCell base) A := by
  by_cases hr : 0 < r
  · exact charbonnelOrderedSelectorRelativeCellCover hn hbase f hr
      hcontinuous hordered hfiber (hpositiveMem hr)
  · have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
    subst r
    apply charbonnelEmptySelectorRelativeCellCover hn hbase
    · intro z hz hzA
      obtain ⟨i, _⟩ := (hfiber z hz).1 hzA
      exact Fin.elim0 i
    · exact hzeroMem rfl

/-! ## Flattening over a finite base cover -/

/-- Flatten relative cylinder covers over the cells of a finite base cover.
The base cover's own compatibility target is irrelevant here; its cells are
used only because they cover the entire base coordinate space. -/
def CharbonnelFiniteCompatibleCellCover.flattenRelativeCylinders
    {C : EuclideanSetFamily} {n : ℕ}
    {B : Set (RealEuclidean n)}
    (baseCover : CharbonnelFiniteCompatibleCellCover C B)
    {A : Set (RealEuclidean (n + 1))}
    (lift : ∀ i, CharbonnelFiniteCompatibleRelativeCellCover C
      (charbonnelCylinderCell (baseCover.cell i).carrier) A) :
    CharbonnelFiniteCompatibleRelativeCellCover C Set.univ A := by
  classical
  letI : ∀ i, Finite (lift i).Index := fun i ↦ (lift i).indexFinite
  exact
    { Index := Σ i, (lift i).Index
      indexFinite := inferInstance
      cell := fun ij ↦ (lift ij.1).cell ij.2
      contained := by
        intro ij z hz
        simp
      covers := by
        intro z hz
        obtain ⟨i, hi⟩ := baseCover.covers (realEuclideanTakeLeft z)
        have hzCylinder : z ∈
            charbonnelCylinderCell (baseCover.cell i).carrier := hi
        obtain ⟨j, hj⟩ := (lift i).covers z hzCylinder
        exact ⟨⟨i, j⟩, hj⟩
      compatible := fun ij ↦ (lift ij.1).compatible ij.2 }

/-- Ordinary finite compatible cover obtained after flattening relative
ordered-selector constructions over a finite base cover. -/
noncomputable def CharbonnelFiniteCompatibleCellCover.flattenRelativeCylindersGlobal
    {C : EuclideanSetFamily} {n : ℕ}
    {B : Set (RealEuclidean n)}
    (baseCover : CharbonnelFiniteCompatibleCellCover C B)
    {A : Set (RealEuclidean (n + 1))}
    (lift : ∀ i, CharbonnelFiniteCompatibleRelativeCellCover C
      (charbonnelCylinderCell (baseCover.cell i).carrier) A) :
    CharbonnelFiniteCompatibleCellCover C A :=
  (baseCover.flattenRelativeCylinders lift).toGlobal

/-- End-to-end open-cylinder combinator: exact finite ordered fibres on each
cell of a finite base cover produce a finite compatible cover one dimension
higher.  All graph/band/ray family-membership facts remain explicit. -/
noncomputable def CharbonnelFiniteCompatibleCellCover.orderedSelectorCylinderCover
    {C : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    {B : Set (RealEuclidean n)}
    (baseCover : CharbonnelFiniteCompatibleCellCover C B)
    {A : Set (RealEuclidean (n + 1))}
    (r : Fin baseCover.count → ℕ)
    (hr : ∀ i, 0 < r i)
    (f : ∀ i, Fin (r i) → RealEuclidean n → ℝ)
    (hcontinuous : ∀ i j, ContinuousOn (f i j) (baseCover.cell i).carrier)
    (hordered : ∀ i x, x ∈ (baseCover.cell i).carrier →
      StrictMono (fun j ↦ f i j x))
    (hfiber : ∀ i z, realEuclideanTakeLeft z ∈
        (baseCover.cell i).carrier →
      (z ∈ A ↔ ∃ j, realEuclideanTakeRight z 0 =
        f i j (realEuclideanTakeLeft z)))
    (hmem : ∀ i k,
      charbonnelOrderedSelectorRegionCarrier
        (baseCover.cell i).carrier (f i) (hr i) k ∈ C (n + 1)) :
    CharbonnelFiniteCompatibleCellCover C A := by
  apply baseCover.flattenRelativeCylindersGlobal
  intro i
  exact charbonnelOrderedSelectorRelativeCellCover hn
    (baseCover.cell i).shape (f i) (hr i)
    (hcontinuous i) (hordered i) (hfiber i) (hmem i)

/-- Mixed-cardinality version of `orderedSelectorCylinderCover`.  It permits
empty fibres on some base cells and positive ordered selector fibres on the
others, exactly as required after refining by fibre cardinality. -/
noncomputable def CharbonnelFiniteCompatibleCellCover.finiteSelectorCylinderCover
    {C : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    {B : Set (RealEuclidean n)}
    (baseCover : CharbonnelFiniteCompatibleCellCover C B)
    {A : Set (RealEuclidean (n + 1))}
    (r : Fin baseCover.count → ℕ)
    (f : ∀ i, Fin (r i) → RealEuclidean n → ℝ)
    (hcontinuous : ∀ i j, ContinuousOn (f i j) (baseCover.cell i).carrier)
    (hordered : ∀ i x, x ∈ (baseCover.cell i).carrier →
      StrictMono (fun j ↦ f i j x))
    (hfiber : ∀ i z, realEuclideanTakeLeft z ∈
        (baseCover.cell i).carrier →
      (z ∈ A ↔ ∃ j, realEuclideanTakeRight z 0 =
        f i j (realEuclideanTakeLeft z)))
    (hzeroMem : ∀ i, r i = 0 →
      charbonnelCylinderCell (baseCover.cell i).carrier ∈ C (n + 1))
    (hpositiveMem : ∀ i (hr : 0 < r i) k,
      charbonnelOrderedSelectorRegionCarrier
        (baseCover.cell i).carrier (f i) hr k ∈ C (n + 1)) :
    CharbonnelFiniteCompatibleCellCover C A := by
  apply baseCover.flattenRelativeCylindersGlobal
  intro i
  exact charbonnelFiniteSelectorRelativeCellCover hn
    (baseCover.cell i).shape (f i)
    (hcontinuous i) (hordered i) (hfiber i)
    (hzeroMem i) (hpositiveMem i)

end AbelFormalization
