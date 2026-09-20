import AbelFormalization.WilkieSection4SimultaneousRefinement

/-!
# Constructive fragments of Wilkie's common-refinement induction

Wilkie proves `(II)ₙ` by induction on the ambient dimension.  The unary base
case cuts the line at finitely many endpoints.  In the successor step he first
refines all projected base cells, then refines equality loci of the finitely
many graph and band boundary functions, and finally orders those functions on
each refined base cell.

This file proves the complete unary common-refinement theorem from WS2 and
WS5.  It also proves that any simultaneous base refinement lifts through the
cylinder constructor.  These are the parts of `(II)ₙ` supported by the current
cell API without an additional theorem decomposing equality and sign loci of
arbitrary cell-boundary functions.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Finite Boolean atoms on the line -/

/-- A chosen finite unary-piece presentation of a scalar set. -/
structure UnaryPieceDecompositionData (s : Set ℝ) where
  count : ℕ
  piece : Fin count → UnaryPiece
  union_eq : s = ⋃ i, (piece i).carrier

/-- Package a propositional unary-piece decomposition as data. -/
noncomputable def UnaryPieceDecomposable.chooseData
    {s : Set ℝ} (hs : UnaryPieceDecomposable s) :
    UnaryPieceDecompositionData s :=
  Classical.choice (show Nonempty (UnaryPieceDecompositionData s) from by
    obtain ⟨count, piece, union_eq⟩ := hs
    exact ⟨⟨count, piece, union_eq⟩⟩)

/-- Finite intersections preserve unary-piece decomposability. -/
theorem unaryPieceDecomposable_iInter_fin
    {r : ℕ} (s : Fin r → Set ℝ)
    (hs : ∀ i, UnaryPieceDecomposable (s i)) :
    UnaryPieceDecomposable (⋂ i, s i) := by
  rw [show (⋂ i, s i) = (⋃ i, (s i)ᶜ)ᶜ by
    ext x
    simp]
  exact (unaryPieceDecomposable_iUnion_fin (fun i ↦ (s i)ᶜ)
    (fun i ↦ (hs i).compl)).compl

/-- The Boolean atom specified by one membership pattern in a finite family
of scalar sets. -/
def wilkieUnaryBooleanAtom {r : ℕ}
    (target : Fin r → Set ℝ) (pattern : Fin r → Bool) : Set ℝ :=
  ⋂ j, if pattern j = true then target j else (target j)ᶜ

theorem unaryPieceDecomposable_wilkieUnaryBooleanAtom
    {r : ℕ} {target : Fin r → Set ℝ}
    (htarget : ∀ j, UnaryPieceDecomposable (target j))
    (pattern : Fin r → Bool) :
    UnaryPieceDecomposable (wilkieUnaryBooleanAtom target pattern) := by
  apply unaryPieceDecomposable_iInter_fin
  intro j
  by_cases hpattern : pattern j = true
  · simpa [hpattern] using htarget j
  · simpa [hpattern] using (htarget j).compl

theorem exists_wilkieUnaryBooleanAtom_membershipPattern
    {r : ℕ} (target : Fin r → Set ℝ) (x : ℝ) :
    ∃ pattern : Fin r → Bool,
      x ∈ wilkieUnaryBooleanAtom target pattern := by
  classical
  refine ⟨fun j ↦ decide (x ∈ target j), ?_⟩
  simp only [wilkieUnaryBooleanAtom, Set.mem_iInter]
  intro j
  by_cases hx : x ∈ target j <;> simp [hx]

/-- Every Boolean atom is compatible with every set used to define it. -/
theorem wilkieUnaryBooleanAtom_compatible
    {r : ℕ} (target : Fin r → Set ℝ)
    (pattern : Fin r → Bool) (j : Fin r) :
    wilkieUnaryBooleanAtom target pattern ⊆ target j ∨
      Disjoint (wilkieUnaryBooleanAtom target pattern) (target j) := by
  by_cases hpattern : pattern j = true
  · left
    intro x hx
    have hj := Set.mem_iInter.mp hx j
    simpa [hpattern] using hj
  · right
    rw [Set.disjoint_left]
    intro x hx hxTarget
    have hj := Set.mem_iInter.mp hx j
    have hxNotTarget : x ∉ target j := by
      simpa [hpattern] using hj
    exact hxNotTarget hxTarget

/-! ## A simultaneous unary Charbonnel cover -/

/-- Package any elementary unary piece as a Charbonnel cell. -/
def charbonnelUnaryCell
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C) (piece : UnaryPiece) :
    CharbonnelCell C 1 :=
  { carrier := realEuclideanUnaryPiece piece
    shape := .unary piece
    carrier_mem := hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_realEuclideanUnaryPiece piece) }

@[simp]
theorem charbonnelUnaryCell_carrier
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C) (piece : UnaryPiece) :
    (charbonnelUnaryCell hC piece).carrier =
      realEuclideanUnaryPiece piece :=
  rfl

/-- A target in `ℝ¹` is exactly the lift of its unique-coordinate image. -/
theorem realEuclideanUnaryLift_coordinateImage
    (s : Set (RealEuclidean 1)) :
    realEuclideanUnaryLift (realEuclideanOneCoordinateImage s) = s := by
  ext x
  simp only [realEuclideanUnaryLift, mem_ofPred_eq,
    mem_realEuclideanOneCoordinateImage_iff]

/-- Finite unary-piece decompositions of finitely many targets give a single
finite recursive-cell cover compatible with all of them.  The construction
takes every Boolean membership atom and flattens chosen unary-piece
decompositions of those atoms. -/
theorem exists_unary_simultaneouslyCompatibleCellCover
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {r : ℕ} (target : Fin r → Set (RealEuclidean 1))
    (htarget : ∀ j,
      UnaryPieceDecomposable
        (realEuclideanOneCoordinateImage (target j))) :
    Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleCellCover C target) := by
  classical
  let scalarTarget : Fin r → Set ℝ :=
    fun j ↦ realEuclideanOneCoordinateImage (target j)
  let atomData : (pattern : Fin r → Bool) →
      UnaryPieceDecompositionData
        (wilkieUnaryBooleanAtom scalarTarget pattern) :=
    fun pattern ↦
      (unaryPieceDecomposable_wilkieUnaryBooleanAtom htarget pattern).chooseData
  let Index := Σ pattern : Fin r → Bool, Fin (atomData pattern).count
  let e : Fin (Fintype.card Index) ≃ Index :=
    (Fintype.equivFin Index).symm
  refine ⟨
    { count := Fintype.card Index
      cell := fun i ↦
        charbonnelUnaryCell hC ((atomData (e i).1).piece (e i).2)
      covers := ?_
      compatible := ?_ }⟩
  · intro x
    obtain ⟨pattern, hxAtom⟩ :=
      exists_wilkieUnaryBooleanAtom_membershipPattern scalarTarget (x 0)
    have hxUnion : x 0 ∈
        ⋃ k, ((atomData pattern).piece k).carrier := by
      rw [← (atomData pattern).union_eq]
      exact hxAtom
    simp only [Set.mem_iUnion] at hxUnion
    obtain ⟨k, hk⟩ := hxUnion
    refine ⟨e.symm ⟨pattern, k⟩, ?_⟩
    rw [e.apply_symm_apply]
    simpa [charbonnelUnaryCell, realEuclideanUnaryPiece,
      realEuclideanUnaryLift] using hk
  · intro i j
    let q : Index := e i
    have hpieceAtom : ((atomData q.1).piece q.2).carrier ⊆
        wilkieUnaryBooleanAtom scalarTarget q.1 := by
      intro y hy
      rw [(atomData q.1).union_eq]
      exact Set.mem_iUnion.mpr ⟨q.2, hy⟩
    have htargetEq : realEuclideanUnaryLift (scalarTarget j) = target j :=
      realEuclideanUnaryLift_coordinateImage (target j)
    rcases wilkieUnaryBooleanAtom_compatible scalarTarget q.1 j with
      hsubset | hdisjoint
    · left
      intro x hx
      rw [← htargetEq]
      exact hsubset (hpieceAtom (by
        simpa [q, charbonnelUnaryCell, realEuclideanUnaryPiece,
          realEuclideanUnaryLift] using hx))
    · right
      rw [← htargetEq, Set.disjoint_left]
      intro x hxPiece hxTarget
      exact Set.disjoint_left.mp hdisjoint
        (hpieceAtom (by
          simpa [q, charbonnelUnaryCell, realEuclideanUnaryPiece,
            realEuclideanUnaryLift] using hxPiece)) hxTarget

/-- The complete unary base case of Wilkie's `(II)ₙ`: under WS2 and WS5,
every finite family of unary Charbonnel cells has a common finite compatible
cell cover. -/
theorem charbonnelFiniteCellFamilyCommonRefinement_one
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {ι : Type} [Fintype ι] (cells : ι → CharbonnelCell C 1) :
    Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleCellCover C
        (fun i ↦ (cells i).carrier)) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let target : Fin (Fintype.card ι) → Set (RealEuclidean 1) :=
    fun j ↦ (cells (e j)).carrier
  have htarget : ∀ j,
      UnaryPieceDecomposable
        (realEuclideanOneCoordinateImage (target j)) := by
    intro j
    exact hC.coordinateImage_unaryPieceDecomposable
      (cells (e j)).carrier_mem
  obtain ⟨cover⟩ :=
    exists_unary_simultaneouslyCompatibleCellCover
      hC.toPositiveArityWeakSetStructure target htarget
  refine ⟨
    { count := cover.count
      cell := cover.cell
      covers := cover.covers
      compatible := ?_ }⟩
  intro i j
  simpa [target] using cover.compatible i (e.symm j)

/-- Cover-indexed form of the unary `(II)₁` result, matching
`CharbonnelFiniteCompatibleCoverCommonRefinementProperty` at dimension one. -/
theorem charbonnelFiniteCompatibleCoverCommonRefinement_one
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {r : ℕ} {target : Fin r → Set (RealEuclidean 1)}
    (cover : (j : Fin r) →
      CharbonnelFiniteCompatibleCellCover C (target j)) :
    Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleCellCover C
        (fun q : Σ j : Fin r, Fin (cover j).count ↦
          ((cover q.1).cell q.2).carrier)) :=
  charbonnelFiniteCellFamilyCommonRefinement_one hC
    (fun q : Σ j : Fin r, Fin (cover j).count ↦
      (cover q.1).cell q.2)

/-! ## Lifting a common refinement through cylinders -/

/-- WS2 and WS3 put the cylinder over any positive-dimensional family member
back in the family. -/
theorem charbonnelCylinderCell_mem_of_weakStructure
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n : ℕ} (hn : 0 < n) {base : Set (RealEuclidean n)}
    (hbase : base ∈ C n) :
    charbonnelCylinderCell base ∈ C (n + 1) := by
  have huniv : (Set.univ : Set (RealEuclidean 1)) ∈ C 1 :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_univ 1)
  have hproduct : realEuclideanSetProduct base
      (Set.univ : Set (RealEuclidean 1)) ∈ C (n + 1) :=
    hC.ws3_prod hn (by omega) hbase huniv
  simpa [charbonnelCylinderCell, realEuclideanSetProduct] using hproduct

/-- A simultaneous refinement of base cells lifts to a simultaneous
refinement of their cylinders. -/
def CharbonnelFiniteSimultaneouslyCompatibleCellCover.cylinder
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n : ℕ} (hn : 0 < n) {ι : Type}
    {base : ι → CharbonnelCell C n}
    (cover : CharbonnelFiniteSimultaneouslyCompatibleCellCover C
      (fun i ↦ (base i).carrier)) :
    CharbonnelFiniteSimultaneouslyCompatibleCellCover C
      (fun i ↦ charbonnelCylinderCell (base i).carrier) :=
  { count := cover.count
    cell := fun k ↦
      { carrier := charbonnelCylinderCell (cover.cell k).carrier
        shape := .cylinder hn (cover.cell k).shape
        carrier_mem := charbonnelCylinderCell_mem_of_weakStructure
          hC hn (cover.cell k).carrier_mem }
    covers := by
      intro z
      obtain ⟨k, hk⟩ := cover.covers (realEuclideanTakeLeft z)
      exact ⟨k, hk⟩
    compatible := by
      intro k i
      rcases cover.compatible k i with hsubset | hdisjoint
      · left
        intro z hz
        exact hsubset hz
      · right
        rw [Set.disjoint_left]
        intro z hzBase hzTarget
        exact Set.disjoint_left.mp hdisjoint hzBase hzTarget }

/-- Source-shaped cylinder fragment of the successor step in `(II)ₙ`.
Whenever the projected bases have a simultaneous refinement, the associated
cylinder cells have one in the next dimension. -/
theorem exists_commonRefinement_cylinders
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n : ℕ} (hn : 0 < n) {ι : Type}
    (base : ι → CharbonnelCell C n)
    (hrefine : Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleCellCover C
        (fun i ↦ (base i).carrier))) :
    Nonempty
      (CharbonnelFiniteSimultaneouslyCompatibleCellCover C
        (fun i ↦ charbonnelCylinderCell (base i).carrier)) := by
  obtain ⟨cover⟩ := hrefine
  exact ⟨cover.cylinder hC hn⟩

end AbelFormalization
