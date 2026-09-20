import AbelFormalization.WilkieSection4DeepSimultaneousInduction
import AbelFormalization.WilkieSection4PartitionedEnrichedSelectorOutput

/-!
# The partitioned unary base of Wilkie's simultaneous induction

The earlier unary simultaneous cover decomposes Boolean atoms, but an
arbitrary decomposition of one atom can contain overlapping intervals.  Here
we instead start with the whole line and successively cut every current piece
at every endpoint occurring in the given finite family.  Each cut is a true
partition, so the final cells are pairwise disjoint and are compatible with
all of the original targets.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Disjoint scalar partitions and endpoint cuts -/

/-- A finite, genuinely disjoint partition of a scalar set into unary pieces. -/
private structure UnaryPieceDisjointPartition (s : Set ℝ) where
  Index : Type
  indexFinite : Finite Index
  piece : Index → UnaryPiece
  contained : ∀ i, (piece i).carrier ⊆ s
  covers : ∀ x ∈ s, ∃ i, x ∈ (piece i).carrier
  pairwise_disjoint : ∀ i j, i ≠ j →
    Disjoint (piece i).carrier (piece j).carrier

namespace UnaryPieceDisjointPartition

/-- The one-piece partition of an elementary unary piece. -/
def single (piece : UnaryPiece) :
    UnaryPieceDisjointPartition piece.carrier where
  Index := Unit
  indexFinite := inferInstance
  piece _ := piece
  contained _ := Subset.rfl
  covers x hx := ⟨(), hx⟩
  pairwise_disjoint i j hij := False.elim (hij (Subsingleton.elim _ _))

/-- Refine every piece of a disjoint partition by another disjoint partition. -/
def refine
    {s : Set ℝ} (coarse : UnaryPieceDisjointPartition s)
    (fine : ∀ i, UnaryPieceDisjointPartition (coarse.piece i).carrier) :
    UnaryPieceDisjointPartition s := by
  letI : Finite coarse.Index := coarse.indexFinite
  letI (i : coarse.Index) : Finite (fine i).Index := (fine i).indexFinite
  exact
    { Index := Σ i, (fine i).Index
      indexFinite := inferInstance
      piece q := (fine q.1).piece q.2
      contained q := ((fine q.1).contained q.2).trans (coarse.contained q.1)
      covers x hx := by
        obtain ⟨i, hi⟩ := coarse.covers x hx
        obtain ⟨k, hk⟩ := (fine i).covers x hi
        exact ⟨⟨i, k⟩, hk⟩
      pairwise_disjoint := by
        rintro ⟨i, k⟩ ⟨j, l⟩ hne
        by_cases hij : i = j
        · subst j
          have hkl : k ≠ l := by
            intro hkl
            subst l
            exact hne rfl
          exact (fine i).pairwise_disjoint k l hkl
        · exact (coarse.pairwise_disjoint i j hij).mono
            ((fine i).contained k) ((fine j).contained l) }

/-- An endpoint cut, together with the compatibility it creates. -/
private structure PointCut (piece : UnaryPiece) (c : ℝ)
    extends UnaryPieceDisjointPartition piece.carrier where
  compatible : ∀ i, (toUnaryPieceDisjointPartition.piece i).carrier ⊆
      ({c} : Set ℝ) ∨
    Disjoint (toUnaryPieceDisjointPartition.piece i).carrier ({c} : Set ℝ)

private def pointCutOutside (piece : UnaryPiece) (c : ℝ)
    (hc : c ∉ piece.carrier) : PointCut piece c where
  toUnaryPieceDisjointPartition := single piece
  compatible := by
    intro i
    right
    rw [Set.disjoint_left]
    intro x hx hxc
    have hxc' : x = c := hxc
    subst x
    exact hc hx

private inductive Three
  | left
  | middle
  | right
  deriving DecidableEq

private instance : Fintype Three where
  elems := {.left, .middle, .right}
  complete x := by cases x <;> simp

private def threePieces (left middle right : UnaryPiece) : Three → UnaryPiece
  | .left => left
  | .middle => middle
  | .right => right

/- A three-piece cut of an interval or ray at an interior point. -/
private def threePieceCut (left middle right : UnaryPiece)
    (s : Set ℝ)
    (hcontained : ∀ i : Three,
      (threePieces left middle right i).carrier ⊆ s)
    (hcovers : ∀ x ∈ s, ∃ i : Three,
      x ∈ (threePieces left middle right i).carrier)
    (hdisjoint : ∀ i j : Three, i ≠ j →
      Disjoint (threePieces left middle right i).carrier
        (threePieces left middle right j).carrier) :
    UnaryPieceDisjointPartition s where
  Index := Three
  indexFinite := inferInstance
  piece i := threePieces left middle right i
  contained := hcontained
  covers := hcovers
  pairwise_disjoint := hdisjoint

/-- Cut one elementary unary piece at a point.  If the point is outside the
piece, this is the unchanged one-piece partition. -/
def atPoint (piece : UnaryPiece) (c : ℝ) :
    PointCut piece c := by
  cases piece with
  | point a =>
      by_cases hac : a = c
      · subst a
        exact
          { toUnaryPieceDisjointPartition := single (.point c)
            compatible := by
              intro i
              left
              simpa [single, UnaryPiece.carrier] }
      · exact pointCutOutside (.point a) c (by
          simpa [UnaryPiece.carrier] using fun h ↦ hac h.symm)
  | bounded a b =>
      by_cases hc : c ∈ Ioo a b
      · refine
          { toUnaryPieceDisjointPartition :=
              threePieceCut (.bounded a c) (.point c) (.bounded c b)
                (Ioo a b) (by
                  intro i
                  cases i <;> simp only [threePieces, UnaryPiece.carrier]
                  · exact fun x hx ↦ ⟨hx.1, hx.2.trans hc.2⟩
                  · rintro x rfl
                    exact hc
                  · exact fun x hx ↦ ⟨hc.1.trans hx.1, hx.2⟩)
                (by
                  intro x hx
                  rcases lt_trichotomy x c with hxc | rfl | hcx
                  · exact ⟨.left, hx.1, hxc⟩
                  · exact ⟨.middle, rfl⟩
                  · exact ⟨.right, hcx, hx.2⟩)
                (by
                  intro i j hij
                  cases i <;> cases j
                  all_goals simp at hij
                  all_goals
                    rw [Set.disjoint_left]
                    intro x hx hy
                    simp only [threePieces, UnaryPiece.carrier, mem_Ioo,
                      mem_singleton_iff] at hx hy
                    linarith)
            compatible := ?_ }
        change ∀ i : Three, _
        intro i
        cases i
        · right
          rw [Set.disjoint_left]
          intro x hx hxc
          have hxlt : x < c := by
            have hx' : x ∈ Ioo a c := by
              simpa [threePieceCut, threePieces, UnaryPiece.carrier] using hx
            exact hx'.2
          have hxeq : x = c := hxc
          exact (ne_of_lt hxlt) hxeq
        · left
          simp [threePieceCut, threePieces, UnaryPiece.carrier]
        · right
          rw [Set.disjoint_left]
          intro x hx hxc
          have hxgt : c < x := by
            have hx' : x ∈ Ioo c b := by
              simpa [threePieceCut, threePieces, UnaryPiece.carrier] using hx
            exact hx'.1
          have hxeq : x = c := hxc
          exact (ne_of_gt hxgt) hxeq
      · exact pointCutOutside (.bounded a b) c (by
          simpa [UnaryPiece.carrier] using hc)
  | leftRay b =>
      by_cases hc : c < b
      · refine
          { toUnaryPieceDisjointPartition :=
              threePieceCut (.leftRay c) (.point c) (.bounded c b)
                (Iio b) (by
                  intro i
                  cases i <;> simp only [threePieces, UnaryPiece.carrier]
                  · exact fun _ hx ↦ hx.trans hc
                  · rintro _ rfl
                    exact hc
                  · exact fun _ hx ↦ hx.2)
                (by
                  intro x hx
                  rcases lt_trichotomy x c with hxc | rfl | hcx
                  · exact ⟨.left, hxc⟩
                  · exact ⟨.middle, rfl⟩
                  · exact ⟨.right, hcx, hx⟩)
                (by
                  intro i j hij
                  cases i <;> cases j
                  all_goals simp at hij
                  all_goals
                    rw [Set.disjoint_left]
                    intro x hx hy
                    simp only [threePieces, UnaryPiece.carrier, mem_Iio,
                      mem_Ioo, mem_singleton_iff] at hx hy
                    linarith)
            compatible := ?_ }
        change ∀ i : Three, _
        intro i
        cases i
        · right
          rw [Set.disjoint_left]
          intro x hx hxc
          have hxlt : x < c := by
            simpa [threePieceCut, threePieces, UnaryPiece.carrier] using hx
          have hxeq : x = c := hxc
          exact (ne_of_lt hxlt) hxeq
        · left
          simp [threePieceCut, threePieces, UnaryPiece.carrier]
        · right
          rw [Set.disjoint_left]
          intro x hx hxc
          have hxgt : c < x := by
            have hx' : x ∈ Ioo c b := by
              simpa [threePieceCut, threePieces, UnaryPiece.carrier] using hx
            exact hx'.1
          have hxeq : x = c := hxc
          exact (ne_of_gt hxgt) hxeq
      · exact pointCutOutside (.leftRay b) c (by
          simpa [UnaryPiece.carrier] using hc)
  | rightRay a =>
      by_cases hc : a < c
      · refine
          { toUnaryPieceDisjointPartition :=
              threePieceCut (.bounded a c) (.point c) (.rightRay c)
                (Ioi a) (by
                  intro i
                  cases i <;> simp only [threePieces, UnaryPiece.carrier]
                  · exact fun _ hx ↦ hx.1
                  · rintro _ rfl
                    exact hc
                  · exact fun _ hx ↦ hc.trans hx)
                (by
                  intro x hx
                  rcases lt_trichotomy x c with hxc | rfl | hcx
                  · exact ⟨.left, hx, hxc⟩
                  · exact ⟨.middle, rfl⟩
                  · exact ⟨.right, hcx⟩)
                (by
                  intro i j hij
                  cases i <;> cases j
                  all_goals simp at hij
                  all_goals
                    rw [Set.disjoint_left]
                    intro x hx hy
                    simp only [threePieces, UnaryPiece.carrier, mem_Ioo,
                      mem_Ioi, mem_singleton_iff] at hx hy
                    linarith)
            compatible := ?_ }
        change ∀ i : Three, _
        intro i
        cases i
        · right
          rw [Set.disjoint_left]
          intro x hx hxc
          have hxlt : x < c := by
            have hx' : x ∈ Ioo a c := by
              simpa [threePieceCut, threePieces, UnaryPiece.carrier] using hx
            exact hx'.2
          have hxeq : x = c := hxc
          exact (ne_of_lt hxlt) hxeq
        · left
          simp [threePieceCut, threePieces, UnaryPiece.carrier]
        · right
          rw [Set.disjoint_left]
          intro x hx hxc
          have hxgt : c < x := by
            simpa [threePieceCut, threePieces, UnaryPiece.carrier] using hx
          have hxeq : x = c := hxc
          exact (ne_of_gt hxgt) hxeq
      · exact pointCutOutside (.rightRay a) c (by
          simpa [UnaryPiece.carrier] using hc)
  | whole =>
      refine
        { toUnaryPieceDisjointPartition :=
            threePieceCut (.leftRay c) (.point c) (.rightRay c)
              Set.univ (by simp [UnaryPiece.carrier])
              (by
                intro x _
                rcases lt_trichotomy x c with hxc | rfl | hcx
                · exact ⟨.left, hxc⟩
                · exact ⟨.middle, rfl⟩
                · exact ⟨.right, hcx⟩)
              (by
                intro i j hij
                cases i <;> cases j
                all_goals simp at hij
                all_goals
                  rw [Set.disjoint_left]
                  intro x hx hy
                  simp only [threePieces, UnaryPiece.carrier, mem_Iio,
                    mem_Ioi, mem_singleton_iff] at hx hy
                  linarith)
          compatible := ?_ }
      change ∀ i : Three, _
      intro i
      cases i
      · right
        rw [Set.disjoint_left]
        intro x hx hxc
        have hxlt : x < c := by
          simpa [threePieceCut, threePieces, UnaryPiece.carrier] using hx
        have hxeq : x = c := hxc
        exact (ne_of_lt hxlt) hxeq
      · left
        simp [threePieceCut, threePieces, UnaryPiece.carrier]
      · right
        rw [Set.disjoint_left]
        intro x hx hxc
        have hxgt : c < x := by
          simpa [threePieceCut, threePieces, UnaryPiece.carrier] using hx
        have hxeq : x = c := hxc
        exact (ne_of_gt hxgt) hxeq

/-- Every cell produced by an endpoint cut is compatible with that endpoint. -/
theorem atPoint_compatible (piece : UnaryPiece) (c : ℝ) :
    ∀ i, ((atPoint piece c).piece i).carrier ⊆ ({c} : Set ℝ) ∨
      Disjoint ((atPoint piece c).piece i).carrier ({c} : Set ℝ) :=
  (atPoint piece c).compatible

/-- Refining a partition at one point preserves genuine disjointness. -/
def refineAtPoint {s : Set ℝ}
    (partition : UnaryPieceDisjointPartition s) (c : ℝ) :
    UnaryPieceDisjointPartition s :=
  partition.refine (fun i ↦
    (atPoint (partition.piece i) c).toUnaryPieceDisjointPartition)

theorem refineAtPoint_compatible {s : Set ℝ}
    (partition : UnaryPieceDisjointPartition s) (c : ℝ) :
    ∀ i, ((partition.refineAtPoint c).piece i).carrier ⊆ ({c} : Set ℝ) ∨
      Disjoint ((partition.refineAtPoint c).piece i).carrier ({c} : Set ℝ) := by
  intro i
  exact atPoint_compatible (partition.piece i.1) c i.2

theorem refineAtPoint_inherits_compatible {s target : Set ℝ}
    (partition : UnaryPieceDisjointPartition s)
    (hcompat : ∀ i, (partition.piece i).carrier ⊆ target ∨
      Disjoint (partition.piece i).carrier target)
    (c : ℝ) :
    ∀ i, ((partition.refineAtPoint c).piece i).carrier ⊆ target ∨
      Disjoint ((partition.refineAtPoint c).piece i).carrier target := by
  intro i
  rcases hcompat i.1 with hsub | hdisjoint
  · exact Or.inl (((atPoint (partition.piece i.1) c).contained i.2).trans hsub)
  · exact Or.inr (hdisjoint.mono_left
      ((atPoint (partition.piece i.1) c).contained i.2))

private theorem unaryPiece_scalar_isPreconnected (piece : UnaryPiece) :
    IsPreconnected piece.carrier := by
  cases piece with
  | point a => simpa [UnaryPiece.carrier] using isPreconnected_singleton (x := a)
  | bounded a b => simpa [UnaryPiece.carrier] using isPreconnected_Ioo (a := a) (b := b)
  | leftRay b => simpa [UnaryPiece.carrier] using isPreconnected_Iio (a := b)
  | rightRay a => simpa [UnaryPiece.carrier] using isPreconnected_Ioi (a := a)
  | whole => simpa [UnaryPiece.carrier] using
      (isPreconnected_univ : IsPreconnected (Set.univ : Set ℝ))

private theorem compatible_Ioo_of_endpoints
    (piece : UnaryPiece) (a b : ℝ)
    (ha : piece.carrier ⊆ ({a} : Set ℝ) ∨
      Disjoint piece.carrier ({a} : Set ℝ))
    (hb : piece.carrier ⊆ ({b} : Set ℝ) ∨
      Disjoint piece.carrier ({b} : Set ℝ)) :
    piece.carrier ⊆ Ioo a b ∨ Disjoint piece.carrier (Ioo a b) := by
  by_cases hab : a < b
  · rcases ha with ha | ha
    · right
      exact Set.disjoint_left.mpr fun x hx hxab ↦ by
        have hxa : x = a := ha hx
        linarith [hxab.1]
    · rcases hb with hb | hb
      · right
        exact Set.disjoint_left.mpr fun x hx hxab ↦ by
          have hxb : x = b := hb hx
          linarith [hxab.2]
      · apply IsPreconnected.subset_or_disjoint_of_disjoint_frontier
          (unaryPiece_scalar_isPreconnected piece)
        rw [frontier_Ioo hab]
        exact Set.disjoint_left.mpr fun x hx hxpair ↦ by
          rcases hxpair with (rfl | rfl)
          · exact Set.disjoint_left.mp ha hx rfl
          · exact Set.disjoint_left.mp hb hx rfl
  · right
    exact Set.disjoint_left.mpr fun _ _ hx ↦ hab (hx.1.trans hx.2)

private theorem compatible_Iio_of_endpoint
    (piece : UnaryPiece) (b : ℝ)
    (hb : piece.carrier ⊆ ({b} : Set ℝ) ∨
      Disjoint piece.carrier ({b} : Set ℝ)) :
    piece.carrier ⊆ Iio b ∨ Disjoint piece.carrier (Iio b) := by
  rcases hb with hb | hb
  · right
    exact Set.disjoint_left.mpr fun x hx hxb ↦ by
      have : x = b := hb hx
      subst x
      exact (lt_irrefl b) hxb
  · apply IsPreconnected.subset_or_disjoint_of_disjoint_frontier
      (unaryPiece_scalar_isPreconnected piece)
    rw [frontier_Iio]
    exact hb

private theorem compatible_Ioi_of_endpoint
    (piece : UnaryPiece) (a : ℝ)
    (ha : piece.carrier ⊆ ({a} : Set ℝ) ∨
      Disjoint piece.carrier ({a} : Set ℝ)) :
    piece.carrier ⊆ Ioi a ∨ Disjoint piece.carrier (Ioi a) := by
  rcases ha with ha | ha
  · right
    exact Set.disjoint_left.mpr fun x hx hxa ↦ by
      have : x = a := ha hx
      subst x
      exact (lt_irrefl a) hxa
  · apply IsPreconnected.subset_or_disjoint_of_disjoint_frontier
      (unaryPiece_scalar_isPreconnected piece)
    rw [frontier_Ioi]
    exact ha

/-- Refine a scalar partition at every frontier point of one unary piece. -/
def refineByPiece {s : Set ℝ}
    (partition : UnaryPieceDisjointPartition s) (target : UnaryPiece) :
    UnaryPieceDisjointPartition s := by
  cases target with
  | point c => exact partition.refineAtPoint c
  | bounded a b => exact (partition.refineAtPoint a).refineAtPoint b
  | leftRay b => exact partition.refineAtPoint b
  | rightRay a => exact partition.refineAtPoint a
  | whole => exact partition

theorem refineByPiece_compatible {s : Set ℝ}
    (partition : UnaryPieceDisjointPartition s) (target : UnaryPiece) :
    ∀ i, ((partition.refineByPiece target).piece i).carrier ⊆ target.carrier ∨
      Disjoint ((partition.refineByPiece target).piece i).carrier target.carrier := by
  cases target with
  | point c =>
      exact partition.refineAtPoint_compatible c
  | bounded a b =>
      intro i
      apply compatible_Ioo_of_endpoints
      · exact refineAtPoint_inherits_compatible
          (partition.refineAtPoint a)
          (partition.refineAtPoint_compatible a) b i
      · exact (partition.refineAtPoint a).refineAtPoint_compatible b i
  | leftRay b =>
      intro i
      exact compatible_Iio_of_endpoint _ _
        (partition.refineAtPoint_compatible b i)
  | rightRay a =>
      intro i
      exact compatible_Ioi_of_endpoint _ _
        (partition.refineAtPoint_compatible a i)
  | whole =>
      intro i
      exact Or.inl (by simp [UnaryPiece.carrier])

theorem refineByPiece_inherits_compatible {s : Set ℝ}
    (partition : UnaryPieceDisjointPartition s) (newTarget : UnaryPiece)
    {target : Set ℝ}
    (hcompat : ∀ i, (partition.piece i).carrier ⊆ target ∨
      Disjoint (partition.piece i).carrier target) :
    ∀ i, ((partition.refineByPiece newTarget).piece i).carrier ⊆ target ∨
      Disjoint ((partition.refineByPiece newTarget).piece i).carrier target := by
  cases newTarget with
  | point c => exact partition.refineAtPoint_inherits_compatible hcompat c
  | bounded a b =>
      exact (partition.refineAtPoint a).refineAtPoint_inherits_compatible
        (partition.refineAtPoint_inherits_compatible hcompat a) b
  | leftRay b => exact partition.refineAtPoint_inherits_compatible hcompat b
  | rightRay a => exact partition.refineAtPoint_inherits_compatible hcompat a
  | whole => exact hcompat

end UnaryPieceDisjointPartition

/-! ## A genuine simultaneous partition on the line -/

/-- Successively split the whole line at all endpoints occurring in a finite
family of unary pieces. -/
private noncomputable def unaryPieceFamilyPartition :
    ∀ r : ℕ, (Fin r → UnaryPiece) → UnaryPieceDisjointPartition Set.univ
  | 0, _ => UnaryPieceDisjointPartition.single .whole
  | r + 1, piece =>
      (unaryPieceFamilyPartition r (fun j ↦ piece j.succ)).refineByPiece (piece 0)

private theorem unaryPieceFamilyPartition_compatible :
    ∀ {r : ℕ} (piece : Fin r → UnaryPiece) i j,
      ((unaryPieceFamilyPartition r piece).piece i).carrier ⊆
          (piece j).carrier ∨
        Disjoint ((unaryPieceFamilyPartition r piece).piece i).carrier
          (piece j).carrier := by
  intro r
  induction r with
  | zero =>
      intro piece i j
      exact Fin.elim0 j
  | succ r ih =>
      intro piece i j
      refine Fin.cases ?_ (fun k ↦ ?_) j
      · exact UnaryPieceDisjointPartition.refineByPiece_compatible
          (unaryPieceFamilyPartition r (fun k ↦ piece k.succ)) (piece 0) i
      · exact UnaryPieceDisjointPartition.refineByPiece_inherits_compatible
          (unaryPieceFamilyPartition r (fun k ↦ piece k.succ)) (piece 0)
          (fun q ↦ ih (fun k ↦ piece k.succ) q k) i

/-- A finite family of unary targets with unary-piece decomposable coordinate
images admits a simultaneous Charbonnel cover whose output carriers are
pairwise equal or disjoint. -/
theorem exists_unary_partitionedSimultaneouslyCompatibleCellCover
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {J : Type} [Fintype J]
    (target : J → Set (RealEuclidean 1))
    (htarget : ∀ j,
      UnaryPieceDecomposable
        (realEuclideanOneCoordinateImage (target j))) :
    Nonempty
      (CharbonnelFinitePartitionedSimultaneouslyCompatibleCellCover C target) := by
  classical
  let data : (j : J) → UnaryPieceDecompositionData
      (realEuclideanOneCoordinateImage (target j)) :=
    fun j ↦ (htarget j).chooseData
  let PieceIndex := Σ j : J, Fin (data j).count
  let e : Fin (Fintype.card PieceIndex) ≃ PieceIndex :=
    (Fintype.equivFin PieceIndex).symm
  let input : Fin (Fintype.card PieceIndex) → UnaryPiece :=
    fun k ↦ (data (e k).1).piece (e k).2
  let partition := unaryPieceFamilyPartition (Fintype.card PieceIndex) input
  letI : Finite partition.Index := partition.indexFinite
  letI : Fintype partition.Index := Fintype.ofFinite partition.Index
  let ep : Fin (Fintype.card partition.Index) ≃ partition.Index :=
    (Fintype.equivFin partition.Index).symm
  let cover : CharbonnelFiniteSimultaneouslyCompatibleCellCover C target :=
    { count := Fintype.card partition.Index
      cell := fun i ↦ charbonnelUnaryCell hC (partition.piece (ep i))
      covers := by
        intro x
        obtain ⟨i, hi⟩ := partition.covers (x 0) (Set.mem_univ _)
        exact ⟨ep.symm i, by
          rw [ep.apply_symm_apply]
          simpa [charbonnelUnaryCell, realEuclideanUnaryPiece,
            realEuclideanUnaryLift] using hi⟩
      compatible := by
        intro i j
        let scalarCell : Set ℝ := (partition.piece (ep i)).carrier
        have hscalar : scalarCell ⊆
              realEuclideanOneCoordinateImage (target j) ∨
            Disjoint scalarCell
              (realEuclideanOneCoordinateImage (target j)) := by
          by_cases hnonempty : scalarCell.Nonempty
          · obtain ⟨x, hx⟩ := hnonempty
            by_cases hxtarget : x ∈
                realEuclideanOneCoordinateImage (target j)
            · have hxunion := hxtarget
              rw [(data j).union_eq] at hxunion
              obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hxunion
              have hcompat := unaryPieceFamilyPartition_compatible input
                (ep i) (e.symm ⟨j, k⟩)
              dsimp only [input] at hcompat
              rw [e.apply_symm_apply] at hcompat
              have hcompat' : scalarCell ⊆ ((data j).piece k).carrier ∨
                  Disjoint scalarCell ((data j).piece k).carrier := by
                simpa only [scalarCell, partition] using hcompat
              rcases hcompat' with hsub | hdisjoint
              · left
                intro y hy
                rw [(data j).union_eq]
                exact Set.mem_iUnion.mpr ⟨k, hsub hy⟩
              · exact False.elim (Set.disjoint_left.mp hdisjoint hx hxk)
            · right
              rw [Set.disjoint_left]
              intro y hy hytarget
              have hyunion := hytarget
              rw [(data j).union_eq] at hyunion
              obtain ⟨k, hyk⟩ := Set.mem_iUnion.mp hyunion
              have hcompat := unaryPieceFamilyPartition_compatible input
                (ep i) (e.symm ⟨j, k⟩)
              dsimp only [input] at hcompat
              rw [e.apply_symm_apply] at hcompat
              have hcompat' : scalarCell ⊆ ((data j).piece k).carrier ∨
                  Disjoint scalarCell ((data j).piece k).carrier := by
                simpa only [scalarCell, partition] using hcompat
              rcases hcompat' with hsub | hdisjoint
              · exact hxtarget (by
                  rw [(data j).union_eq]
                  exact Set.mem_iUnion.mpr ⟨k, hsub hx⟩)
              · exact Set.disjoint_left.mp hdisjoint hy hyk
          · left
            exact fun x hx ↦ False.elim (hnonempty ⟨x, hx⟩)
        have hlift : realEuclideanUnaryLift
              (realEuclideanOneCoordinateImage (target j)) = target j :=
          realEuclideanUnaryLift_coordinateImage (target j)
        rcases hscalar with hsub | hdisjoint
        · left
          intro x hx
          rw [← hlift]
          exact hsub (by
            simpa [scalarCell, charbonnelUnaryCell,
              realEuclideanUnaryPiece, realEuclideanUnaryLift] using hx)
        · right
          rw [← hlift, Set.disjoint_left]
          intro x hxCell hxTarget
          exact Set.disjoint_left.mp hdisjoint (by
            simpa [scalarCell, charbonnelUnaryCell,
              realEuclideanUnaryPiece, realEuclideanUnaryLift] using hxCell) hxTarget }
  refine ⟨
    { cover := cover
      cells_eq_or_disjoint := ?_ }⟩
  intro i k
  by_cases hik : i = k
  · exact Or.inl (congrArg (fun q ↦ (cover.cell q).carrier) hik)
  · right
    have hne : ep i ≠ ep k := fun h ↦ hik (ep.injective h)
    have hdisjoint := partition.pairwise_disjoint (ep i) (ep k) hne
    rw [Set.disjoint_left]
    intro x hxi hxk
    exact Set.disjoint_left.mp hdisjoint (by
      simpa [cover, charbonnelUnaryCell, realEuclideanUnaryPiece,
        realEuclideanUnaryLift] using hxi) (by
      simpa [cover, charbonnelUnaryCell, realEuclideanUnaryPiece,
        realEuclideanUnaryLift] using hxk)

/-! ## Restriction to a unary deep domain -/

/-- Every ordinary unary cell admits a retained unary shape.  This is stated
propositionally first because ordinary cell shapes are proof-valued. -/
private theorem exists_deepUnaryOfCell
    {S : EuclideanSetFamily}
    (cell : CharbonnelCell (charbonnelClosure S) 1) :
    ∃ deep : CharbonnelDeepEnrichedCell S 1,
      deep.carrier = cell.carrier := by
  rcases cell with ⟨cellCarrier, shape, hcarrier⟩
  cases shape with
  | unary piece =>
      exact ⟨⟨realEuclideanUnaryPiece piece, .unary piece⟩, rfl⟩
  | graph hn => omega
  | band hn => omega
  | lowerRay hn => omega
  | upperRay hn => omega
  | cylinder hn => omega

private noncomputable def deepUnaryOfCell
    {S : EuclideanSetFamily}
    (cell : CharbonnelCell (charbonnelClosure S) 1) :
    CharbonnelDeepEnrichedCell S 1 :=
  Classical.choose (exists_deepUnaryOfCell cell)

@[simp]
private theorem deepUnaryOfCell_carrier
    {S : EuclideanSetFamily}
    (cell : CharbonnelCell (charbonnelClosure S) 1) :
    (deepUnaryOfCell cell).carrier = cell.carrier :=
  Classical.choose_spec (exists_deepUnaryOfCell cell)

/-- The coordinate image of a retained unary cell is its elementary scalar
piece, and therefore is unary-piece decomposable. -/
private theorem deepUnary_coordinateImage_decomposable
    {S : EuclideanSetFamily}
    (D : CharbonnelDeepEnrichedCell S 1) :
    UnaryPieceDecomposable
      (realEuclideanOneCoordinateImage D.carrier) := by
  rcases D with ⟨carrier, shape⟩
  cases shape with
  | unary piece =>
      have himage :
          realEuclideanOneCoordinateImage
              (realEuclideanUnaryPiece piece) = piece.carrier := by
        ext x
        constructor
        · rintro ⟨v, hv, rfl⟩
          simpa [realEuclideanUnaryPiece, realEuclideanUnaryLift] using hv
        · intro hx
          refine ⟨fun _ ↦ x, ?_, rfl⟩
          simpa [realEuclideanUnaryPiece, realEuclideanUnaryLift] using hx
      rw [himage]
      exact unaryPieceDecomposable_carrier piece
  | graph hn => omega
  | band hn => omega
  | lowerRay hn => omega
  | upperRay hn => omega
  | cylinder hn => omega

/-- Restrict a global unary partition to the cells lying in one designated
domain target, and retain the canonical deep unary enrichment. -/
private def unaryDeepRelativeCoverOfPartition
    {S : EuclideanSetFamily} {J : Type}
    {target : J → Set (RealEuclidean 1)}
    (fine : CharbonnelFinitePartitionedSimultaneouslyCompatibleCellCover
      (charbonnelClosure S) target)
    (domainIndex : J)
    (D : CharbonnelDeepEnrichedCell S 1)
    (hdomain : target domainIndex = D.carrier) :
    CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
      S D.carrier target := by
  classical
  let Index := {i : Fin fine.cover.count //
    (fine.cover.cell i).carrier ⊆ D.carrier}
  exact
    { Index := Index
      indexFinite := inferInstance
      cell := fun i ↦ deepUnaryOfCell (fine.cover.cell i.1)
      contained := by
        intro i
        simpa only [deepUnaryOfCell_carrier] using i.2
      covers := by
        intro x hxD
        obtain ⟨i, hxi⟩ := fine.cover.covers x
        have hiD : (fine.cover.cell i).carrier ⊆ D.carrier := by
          have hcompat := fine.cover.compatible i domainIndex
          rw [hdomain] at hcompat
          rcases hcompat with hsub | hdisjoint
          · exact hsub
          · exact False.elim (Set.disjoint_left.mp hdisjoint hxi hxD)
        exact ⟨⟨i, hiD⟩, by
          simpa only [deepUnaryOfCell_carrier] using hxi⟩
      compatible := by
        intro i j
        simpa only [deepUnaryOfCell_carrier] using
          fine.cover.compatible i.1 j
      cells_eq_or_disjoint := by
        intro i k
        simpa only [deepUnaryOfCell_carrier] using
          fine.cells_eq_or_disjoint i.1 k.1
      hereditary_projection_coherent := trivial }

/-- The genuine partitioned unary construction proves both halves of the
retained simultaneous Section 4 induction in dimension one. -/
theorem PositiveArityOMinimalWeakSetStructure.charbonnelDeepSection4InductionAt_zero
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S)) :
    CharbonnelDeepSection4InductionAt S 0 := by
  constructor
  · intro D A hAD hAmem _hAclosed
    let target : Bool → Set (RealEuclidean 1)
      | false => D.carrier
      | true => A
    have htarget : ∀ j,
        UnaryPieceDecomposable
          (realEuclideanOneCoordinateImage (target j)) := by
      intro j
      cases j with
      | false =>
          simpa [target] using deepUnary_coordinateImage_decomposable D
      | true =>
          exact hC.coordinateImage_unaryPieceDecomposable hAmem
    obtain ⟨fine⟩ := exists_unary_partitionedSimultaneouslyCompatibleCellCover
      hC.toPositiveArityWeakSetStructure target htarget
    let relative := unaryDeepRelativeCoverOfPartition fine false D rfl
    exact ⟨
      { Index := relative.Index
        indexFinite := relative.indexFinite
        cell := relative.cell
        contained := relative.contained
        covers := relative.covers
        compatible := fun i _ ↦ relative.compatible i true
        cells_eq_or_disjoint := relative.cells_eq_or_disjoint
        hereditary_projection_coherent :=
          relative.hereditary_projection_coherent }⟩
  · intro D J _ targetCells
    let target : Option J → Set (RealEuclidean 1)
      | none => D.carrier
      | some j => (targetCells j).carrier
    have htarget : ∀ j,
        UnaryPieceDecomposable
          (realEuclideanOneCoordinateImage (target j)) := by
      intro j
      cases j with
      | none =>
          simpa [target] using deepUnary_coordinateImage_decomposable D
      | some j =>
          simpa [target] using
            deepUnary_coordinateImage_decomposable (targetCells j)
    obtain ⟨fine⟩ := exists_unary_partitionedSimultaneouslyCompatibleCellCover
      hC.toPositiveArityWeakSetStructure target htarget
    let relative := unaryDeepRelativeCoverOfPartition fine none D rfl
    exact ⟨
      { Index := relative.Index
        indexFinite := relative.indexFinite
        cell := relative.cell
        contained := relative.contained
        covers := relative.covers
        compatible := fun i j ↦ relative.compatible i (some j)
        cells_eq_or_disjoint := relative.cells_eq_or_disjoint
        hereditary_projection_coherent :=
          relative.hereditary_projection_coherent }⟩

/-- Source-faithful bounded unary base case. -/
theorem PositiveArityOMinimalWeakSetStructure.charbonnelBoundedDeepSection4InductionAt_zero
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S)) :
    CharbonnelBoundedDeepSection4InductionAt S 0 :=
  charbonnelBoundedDeepSection4InductionAt_of_deep
    hC.charbonnelDeepSection4InductionAt_zero

end AbelFormalization
