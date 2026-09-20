import AbelFormalization.WilkieSection4DeepCoverCore
import AbelFormalization.WilkieBoundedCompactification

/-!
# The retained simultaneous induction for Wilkie Section 4

Wilkie proves relative closed-set decomposition and finite common refinement
simultaneously.  The induction must retain the projected base and every
boundary-graph membership certificate; ordinary `CharbonnelCell`s deliberately
forget those data.  This file records the exact deep-cell invariant used by
the remaining geometric induction.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A finite partition of a deep cell, compatible with finitely many targets,
whose cells retain their complete projection history.  Equality is allowed in
the partition clause because flattening local constructions can repeat a cell. -/
structure CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
    (S : EuclideanSetFamily) {n : ℕ} {J : Type}
    (D : Set (RealEuclidean (n + 1)))
    (target : J → Set (RealEuclidean (n + 1))) where
  Index : Type
  indexFinite : Finite Index
  cell : Index → CharbonnelDeepEnrichedCell S (n + 1)
  contained : ∀ i, (cell i).carrier ⊆ D
  covers : ∀ x ∈ D, ∃ i, x ∈ (cell i).carrier
  compatible : ∀ i j,
    (cell i).carrier ⊆ target j ∨
      Disjoint (cell i).carrier (target j)
  cells_eq_or_disjoint : ∀ i k,
    (cell i).carrier = (cell k).carrier ∨
      Disjoint (cell i).carrier (cell k).carrier
  hereditary_projection_coherent :
    CharbonnelDeepCellFamilyProjectionCoherent n cell

namespace CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover

/-- Select one target from a simultaneous deep partition. -/
def targetCover
    {S : EuclideanSetFamily} {n : ℕ} {J : Type}
    {D : Set (RealEuclidean (n + 1))}
    {target : J → Set (RealEuclidean (n + 1))}
    (cover :
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D target)
    (j : J) (htarget : target j ⊆ D) :
    CharbonnelFiniteDeepProjectionCoherentCellCover S D (target j) where
  Index := cover.Index
  indexFinite := cover.indexFinite
  cell := cover.cell
  target_subset_domain := htarget
  contained := cover.contained
  covers := cover.covers
  compatible := fun i ↦ cover.compatible i j
  hereditary_projection_coherent := cover.hereditary_projection_coherent

/-- Forget the retained projection data and obtain an ordinary relative cell
cover for one selected target. -/
def targetRelativeCellCover
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {J : Type}
    {D : Set (RealEuclidean (n + 1))}
    {target : J → Set (RealEuclidean (n + 1))}
    (cover :
      CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D target)
    (j : J) :
    CharbonnelFiniteCompatibleRelativeCellCover
      (charbonnelClosure S) D (target j) where
  Index := cover.Index
  indexFinite := cover.indexFinite
  cell i := (cover.cell i).toCell hC
  contained := by
    intro i
    simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using
      cover.contained i
  covers := by
    intro x hx
    obtain ⟨i, hi⟩ := cover.covers x hx
    exact ⟨i, by
      simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using hi⟩
  compatible := by
    intro i
    simpa only [CharbonnelDeepEnrichedCell.toCell_carrier] using
      cover.compatible i j

end CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover

/-- Wilkie's relative closed-set decomposition assertion at one positive
ambient dimension, with all source data and all projection stages retained. -/
def CharbonnelDeepRelativeClosedDecompositionAt
    (S : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ (D : CharbonnelDeepEnrichedCell S (n + 1))
    {A : Set (RealEuclidean (n + 1))},
    A ⊆ D.carrier →
    A ∈ charbonnelClosure S (n + 1) →
    IsClosed (Subtype.val ⁻¹' A : Set D.carrier) →
    Nonempty
      (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D.carrier (fun _ : Unit ↦ A))

/-- Wilkie's finite common-refinement assertion at one positive ambient
dimension, restricted to a specified deep domain cell. -/
def CharbonnelDeepRelativeCommonRefinementAt
    (S : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ (D : CharbonnelDeepEnrichedCell S (n + 1))
    {J : Type} [Fintype J]
    (target : J → CharbonnelDeepEnrichedCell S (n + 1)),
    Nonempty
      (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
        S D.carrier (fun j ↦ (target j).carrier))

/-- The exact mutually inductive Section 4 datum at one dimension. -/
def CharbonnelDeepSection4InductionAt
    (S : EuclideanSetFamily) (n : ℕ) : Prop :=
  CharbonnelDeepRelativeClosedDecompositionAt S n ∧
    CharbonnelDeepRelativeCommonRefinementAt S n

/-! ## The source-faithful bounded induction assertions

Wilkie explicitly works with bounded cells after conjugating the ambient
space to the open cube.  The induction hypotheses therefore include
boundedness of the domain cell.  Keeping these predicates separate from the
earlier unrestricted interface makes the source restriction visible at every
recursive call. -/

/-- Wilkie's relative closed-set decomposition assertion for a bounded deep
domain cell. -/
def CharbonnelBoundedDeepRelativeClosedDecompositionAt
    (S : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ (D : CharbonnelDeepEnrichedCell S (n + 1)),
    Bornology.IsBounded D.carrier →
    ∀ {A : Set (RealEuclidean (n + 1))},
      A ⊆ D.carrier →
      A ∈ charbonnelClosure S (n + 1) →
      IsClosed (Subtype.val ⁻¹' A : Set D.carrier) →
      Nonempty
        (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
          S D.carrier (fun _ : Unit ↦ A))

/-- Wilkie's finite common-refinement assertion for a bounded deep domain
cell. -/
def CharbonnelBoundedDeepRelativeCommonRefinementAt
    (S : EuclideanSetFamily) (n : ℕ) : Prop :=
  ∀ (D : CharbonnelDeepEnrichedCell S (n + 1)),
    Bornology.IsBounded D.carrier →
    ∀ {J : Type} [Fintype J]
      (target : J → CharbonnelDeepEnrichedCell S (n + 1)),
      Nonempty
        (CharbonnelFinitePartitionedDeepSimultaneouslyCompatibleRelativeCellCover
          S D.carrier (fun j ↦ (target j).carrier))

/-- The exact bounded mutually inductive Section 4 datum at one dimension. -/
def CharbonnelBoundedDeepSection4InductionAt
    (S : EuclideanSetFamily) (n : ℕ) : Prop :=
  CharbonnelBoundedDeepRelativeClosedDecompositionAt S n ∧
    CharbonnelBoundedDeepRelativeCommonRefinementAt S n

/-- An unrestricted retained decomposition immediately supplies the bounded
source assertion. -/
theorem charbonnelBoundedDeepSection4InductionAt_of_deep
    {S : EuclideanSetFamily} {n : ℕ}
    (h : CharbonnelDeepSection4InductionAt S n) :
    CharbonnelBoundedDeepSection4InductionAt S n := by
  constructor
  · intro D _hD A hAD hAmem hAclosed
    exact h.1 D hAD hAmem hAclosed
  · intro D _hD J _ target
    exact h.2 D target

/-! ## The deep open cube and the full-closed-cover endpoint -/

private def deepOpenCubeLastCoordinatePolynomial (n : ℕ) (c : ℝ) :
    MvPolynomial (Fin (n + 1)) ℝ :=
  MvPolynomial.X (Fin.last n) - MvPolynomial.C c

@[simp]
private theorem deepOpenCubeLastCoordinatePolynomial_eval
    (n : ℕ) (c : ℝ) (z : RealEuclidean (n + 1)) :
    MvPolynomial.eval z (deepOpenCubeLastCoordinatePolynomial n c) =
      realEuclideanTakeRight z 0 - c := by
  have hlast : Fin.last n = Fin.natAdd n (0 : Fin 1) := by
    apply Fin.ext
    rfl
  simp only [deepOpenCubeLastCoordinatePolynomial, map_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_C]
  rw [hlast]
  rfl

private theorem deepOpenCubeRestrictedConstantGraph_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {base : Set (RealEuclidean n)}
    (hbase : base ∈ charbonnelClosure S n) (c : ℝ) :
    charbonnelRestrictedGraph base (fun _ ↦ c) ∈
      charbonnelClosure S (n + 1) := by
  have hbasePull : realEuclideanTakeLeftLinearMap n 1 ⁻¹' base ∈
      charbonnelClosure S (n + 1) :=
    hC.linear_preimage_mem (by omega) hn hbase
      (realEuclideanTakeLeftLinearMap n 1)
  have hlevel : {z : RealEuclidean (n + 1) |
        MvPolynomial.eval z (deepOpenCubeLastCoordinatePolynomial n c) = 0} ∈
      charbonnelClosure S (n + 1) :=
    hC.ws2_polynomialSign (by omega) (.zero _)
  rw [show charbonnelRestrictedGraph base (fun _ ↦ c) =
      realEuclideanTakeLeftLinearMap n 1 ⁻¹' base ∩
        {z : RealEuclidean (n + 1) |
          MvPolynomial.eval z (deepOpenCubeLastCoordinatePolynomial n c) = 0} by
    ext z
    simp [charbonnelRestrictedGraph, sub_eq_zero]]
  exact hC.ws1_inter (by omega) hbasePull hlevel

/-- The bounded open cube with every recursive base and both constant
boundary-graph certificates retained. -/
noncomputable def charbonnelDeepOpenCubeCell
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S)) :
    ∀ n : ℕ, 0 < n → CharbonnelDeepEnrichedCell S n
  | 0, hn => False.elim (by omega)
  | n + 1, _hn => by
      by_cases hn : n = 0
      · subst n
        exact
          { carrier := realEuclideanUnaryPiece (.bounded (-1) 1)
            shape := .unary (.bounded (-1) 1) }
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        let base := charbonnelDeepOpenCubeCell hC n hnpos
        let lower : RealEuclidean n → ℝ := fun _ ↦ -1
        let upper : RealEuclidean n → ℝ := fun _ ↦ 1
        have hlower : charbonnelRestrictedGraph base.carrier lower ∈
            charbonnelClosure S (n + 1) :=
          deepOpenCubeRestrictedConstantGraph_mem_charbonnelClosure
            hC hnpos (base.toCell hC).carrier_mem (-1)
        have hupper : charbonnelRestrictedGraph base.carrier upper ∈
            charbonnelClosure S (n + 1) :=
          deepOpenCubeRestrictedConstantGraph_mem_charbonnelClosure
            hC hnpos (base.toCell hC).carrier_mem 1
        exact
          { carrier := charbonnelOpenBand base.carrier lower upper
            shape := .band hnpos base.shape lower upper
              continuousOn_const continuousOn_const (by norm_num)
              hlower hupper }
termination_by n => n

@[simp]
theorem charbonnelDeepOpenCubeCell_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) :
    (charbonnelDeepOpenCubeCell hC n hn).carrier = wilkieOpenCube n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      by_cases hm : m = 0
      · subst m
        ext x
        simp [charbonnelDeepOpenCubeCell, realEuclideanUnaryPiece,
          realEuclideanUnaryLift, UnaryPiece.carrier, wilkieOpenCube]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        rw [show
          (charbonnelDeepOpenCubeCell hC (m + 1) (by omega)).carrier =
              charbonnelOpenBand
                (charbonnelDeepOpenCubeCell hC m hmpos).carrier
                (fun _ ↦ -1) (fun _ ↦ 1) by
          simp [charbonnelDeepOpenCubeCell, hm]]
        rw [ih m (by omega) hmpos]
        ext z
        simp only [charbonnelOpenBand, wilkieOpenCube, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hx, hlower, hupper⟩ i
          refine Fin.addCases (m := m) (n := 1)
            (fun j ↦ ?_) (fun j ↦ ?_) i
          · simpa [realEuclideanTakeLeft] using hx j
          · fin_cases j
            simpa [realEuclideanTakeRight] using And.intro hlower hupper
        · intro hz
          refine ⟨?_, ?_, ?_⟩
          · intro j
            simpa [realEuclideanTakeLeft] using hz (Fin.castAdd 1 j)
          · simpa [realEuclideanTakeRight] using
              (hz (Fin.natAdd m (0 : Fin 1))).1
          · simpa [realEuclideanTakeRight] using
              (hz (Fin.natAdd m (0 : Fin 1))).2

/-- The retained open-cube cell is a bounded domain, as required by the
source-faithful Section 4 induction. -/
theorem charbonnelDeepOpenCubeCell_isBounded
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) :
    Bornology.IsBounded (charbonnelDeepOpenCubeCell hC n hn).carrier := by
  rw [charbonnelDeepOpenCubeCell_carrier hC hn]
  refine
    (Bornology.IsBounded.pi
      (fun _ : Fin n ↦ Metric.isBounded_Ioo (-1 : ℝ) 1)).subset ?_
  intro x hx i _hi
  exact hx i

/-- Relative closed decomposition inside the retained open cube gives the
full-dimensional hereditary cover needed before any hidden coordinate is
projected away. -/
theorem
    fullClosedDeepCovers_of_deepRelativeClosedDecomposition
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : ∀ n : ℕ, CharbonnelDeepRelativeClosedDecompositionAt S n) :
    ∀ {m : ℕ} {B : Set (RealEuclidean (m + 1))},
      IsClosed B → B ∈ charbonnelClosure S (m + 1) →
      Nonempty
        (CharbonnelFiniteDeepProjectionCoherentCellCover S
          (wilkieOpenCube (m + 1)) (wilkieBoundedImage B)) := by
  intro m B hBclosed hBmem
  let D := charbonnelDeepOpenCubeCell hC (m + 1) (by omega)
  have hAD : wilkieBoundedImage B ⊆ D.carrier := by
    rw [charbonnelDeepOpenCubeCell_carrier]
    rintro _ ⟨x, _hx, rfl⟩
    exact wilkieBoundedMap_mem_openCube (m + 1) x
  have hAmem : wilkieBoundedImage B ∈ charbonnelClosure S (m + 1) :=
    wilkieBoundedImage_mem_charbonnelClosure hC (by omega) hBmem
  have hAclosed : IsClosed
      (Subtype.val ⁻¹' wilkieBoundedImage B : Set D.carrier) := by
    rw [show D.carrier = wilkieOpenCube (m + 1) by
      exact charbonnelDeepOpenCubeCell_carrier hC (by omega)]
    exact isClosed_preimage_val_wilkieBoundedImage hBclosed
  obtain ⟨cover⟩ := hI m D hAD hAmem hAclosed
  refine ⟨?_⟩
  rw [← show D.carrier = wilkieOpenCube (m + 1) by
    simpa only [D] using
      charbonnelDeepOpenCubeCell_carrier hC (show 0 < m + 1 by omega)]
  exact cover.targetCover () hAD

/-- The bounded Section 4 closed-decomposition assertion suffices at the
endpoint because the retained compactification cube is bounded. -/
theorem
    fullClosedDeepCovers_of_boundedDeepRelativeClosedDecomposition
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : ∀ n : ℕ,
      CharbonnelBoundedDeepRelativeClosedDecompositionAt S n) :
    ∀ {m : ℕ} {B : Set (RealEuclidean (m + 1))},
      IsClosed B → B ∈ charbonnelClosure S (m + 1) →
      Nonempty
        (CharbonnelFiniteDeepProjectionCoherentCellCover S
          (wilkieOpenCube (m + 1)) (wilkieBoundedImage B)) := by
  intro m B hBclosed hBmem
  let D := charbonnelDeepOpenCubeCell hC (m + 1) (by omega)
  have hDbounded : Bornology.IsBounded D.carrier := by
    exact charbonnelDeepOpenCubeCell_isBounded hC (by omega)
  have hAD : wilkieBoundedImage B ⊆ D.carrier := by
    rw [charbonnelDeepOpenCubeCell_carrier]
    rintro _ ⟨x, _hx, rfl⟩
    exact wilkieBoundedMap_mem_openCube (m + 1) x
  have hAmem : wilkieBoundedImage B ∈ charbonnelClosure S (m + 1) :=
    wilkieBoundedImage_mem_charbonnelClosure hC (by omega) hBmem
  have hAclosed : IsClosed
      (Subtype.val ⁻¹' wilkieBoundedImage B : Set D.carrier) := by
    rw [show D.carrier = wilkieOpenCube (m + 1) by
      exact charbonnelDeepOpenCubeCell_carrier hC (by omega)]
    exact isClosed_preimage_val_wilkieBoundedImage hBclosed
  obtain ⟨cover⟩ := hI m D hDbounded hAD hAmem hAclosed
  refine ⟨?_⟩
  rw [← show D.carrier = wilkieOpenCube (m + 1) by
    simpa only [D] using
      charbonnelDeepOpenCubeCell_carrier hC (show 0 < m + 1 by omega)]
  exact cover.targetCover () hAD

end AbelFormalization
