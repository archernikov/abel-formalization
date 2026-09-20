import AbelFormalization.CharbonnelClosedBoundaryCellAssembly
import AbelFormalization.CharbonnelBoundarySelectorAssembly

/-!
# Unary compatible cell covers

Wilkie's simultaneous cell induction starts from the one-dimensional case.
WS5 gives a finite point/interval decomposition of a unary member.  Applying
the elementary Boolean closure of unary-piece decompositions to its complement
and concatenating the two lists gives an actual finite recursive-cell cover of
the line compatible with the member.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Every unary member of a positive-arity o-minimal weak family admits the
finite compatible recursive-cell cover used as Wilkie's `(I)₁` base case. -/
noncomputable def
    PositiveArityOMinimalWeakSetStructure.unaryCompatibleCellCover
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {A : Set (RealEuclidean 1)} (hA : A ∈ C 1) :
    CharbonnelFiniteCompatibleCellCover C A := by
  classical
  let scalarA : Set ℝ := realEuclideanOneCoordinateImage A
  have hscalar : UnaryPieceDecomposable scalarA :=
    hC.coordinateImage_unaryPieceDecomposable hA
  let r : ℕ := Classical.choose hscalar
  let inside : Fin r → UnaryPiece :=
    Classical.choose (Classical.choose_spec hscalar)
  have hins : scalarA = ⋃ i, (inside i).carrier :=
    Classical.choose_spec (Classical.choose_spec hscalar)
  have hscalarCompl : UnaryPieceDecomposable scalarAᶜ := hscalar.compl
  let s : ℕ := Classical.choose hscalarCompl
  let outside : Fin s → UnaryPiece :=
    Classical.choose (Classical.choose_spec hscalarCompl)
  have hout : scalarAᶜ = ⋃ i, (outside i).carrier :=
    Classical.choose_spec (Classical.choose_spec hscalarCompl)
  let piece : Fin (r + s) → UnaryPiece := Fin.addCases inside outside
  let cell : Fin (r + s) → CharbonnelCell C 1 := fun i ↦
    { carrier := realEuclideanUnaryPiece (piece i)
      shape := CharbonnelCellShape.unary (piece i)
      carrier_mem := hC.ws2_polynomialSign (by omega)
        (polynomialSignConstructible_realEuclideanUnaryPiece (piece i)) }
  refine
    { count := r + s
      cell := cell
      covers := ?_
      compatible := ?_ }
  · intro x
    by_cases hx : x ∈ A
    · have hxscalar : x 0 ∈ scalarA :=
        (mem_realEuclideanOneCoordinateImage_iff A x).mpr hx
      rw [hins] at hxscalar
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxscalar
      refine ⟨Fin.castAdd s i, ?_⟩
      simpa [cell, piece, realEuclideanUnaryPiece,
        realEuclideanUnaryLift] using hi
    · have hxscalar : x 0 ∈ scalarAᶜ := by
        change x 0 ∉ scalarA
        intro hxscalar
        apply hx
        apply (mem_realEuclideanOneCoordinateImage_iff A x).mp
        simpa [scalarA] using hxscalar
      rw [hout] at hxscalar
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxscalar
      refine ⟨Fin.natAdd r i, ?_⟩
      simpa [cell, piece, realEuclideanUnaryPiece,
        realEuclideanUnaryLift] using hi
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      left
      intro x hx
      apply (mem_realEuclideanOneCoordinateImage_iff A x).mp
      change x 0 ∈ scalarA
      rw [hins]
      exact Set.mem_iUnion.mpr ⟨j, by
        simpa [cell, piece, realEuclideanUnaryPiece,
          realEuclideanUnaryLift] using hx⟩
    · intro j
      right
      apply Set.disjoint_left.mpr
      intro x hx hxA
      have hxout : x 0 ∈ scalarAᶜ := by
        rw [hout]
        exact Set.mem_iUnion.mpr ⟨j, by
          simpa [cell, piece, realEuclideanUnaryPiece,
            realEuclideanUnaryLift] using hx⟩
      exact hxout ((mem_realEuclideanOneCoordinateImage_iff A x).mpr hxA)

/-- Uniform statement of the unary `(I)₁` base case. -/
theorem PositiveArityOMinimalWeakSetStructure.nonempty_unaryCompatibleCellCover
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {A : Set (RealEuclidean 1)} (hA : A ∈ C 1) :
    Nonempty (CharbonnelFiniteCompatibleCellCover C A) :=
  ⟨hC.unaryCompatibleCellCover hA⟩

/-- Wilkie's individual compatible-cover property in every positive
dimension.  Keeping this predicate separate from the closed-lift endpoint
makes the dimension induction usable on the auxiliary Section 4 loci. -/
def CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n : ℕ}, 0 < n →
    ∀ {A : Set (RealEuclidean n)}, IsClosed A → A ∈ C n →
      Nonempty (CharbonnelFiniteCompatibleCellCover C A)

/-- The explicit WS5 unary base and the existing higher-dimensional property
combine into the all-positive-dimensional form of Wilkie's `(I)`. -/
theorem positiveDimensionalClosedMemberCellCovers_of_unary_and_higher
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hhigher : CharbonnelHigherDimensionalClosedMemberCellCoverProperty C) :
    CharbonnelPositiveDimensionalClosedMemberCellCoverProperty C := by
  intro n hn A hAclosed hAmem
  by_cases hone : n = 1
  · subst n
    exact hC.nonempty_unaryCompatibleCellCover hAmem
  · exact hhigher (by omega) hAclosed hAmem

end AbelFormalization
