import AbelFormalization.WilkieSection4ProjectionTowerAssembly

/-!
# Bounded enriched covers from one pointwise Section 4 decomposition

This file reduces the bounded enriched-cover interface to the source-shaped
statement that projections of closed lifts are finite unions of enriched
successor cells.  The construction first realizes bounded coordinates by a
new closed lift.  It then uses the retained selector refinement, including an
explicit enriched cell for the open cube, to turn the resulting finite union
into a relative compatible cover of that cube.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Constant graphs and the recursive open-cube cell -/

def charbonnelLastCoordinatePolynomial (n : ℕ) (c : ℝ) :
    MvPolynomial (Fin (n + 1)) ℝ :=
  MvPolynomial.X (Fin.last n) - MvPolynomial.C c

@[simp]
theorem charbonnelLastCoordinatePolynomial_eval
    (n : ℕ) (c : ℝ) (z : RealEuclidean (n + 1)) :
    MvPolynomial.eval z (charbonnelLastCoordinatePolynomial n c) =
      realEuclideanTakeRight z 0 - c := by
  have hlast : Fin.last n = Fin.natAdd n (0 : Fin 1) := by
    apply Fin.ext
    rfl
  simp only [charbonnelLastCoordinatePolynomial, map_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_C]
  rw [hlast]
  rfl

theorem charbonnelRestrictedConstantGraph_mem_charbonnelClosure
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
        MvPolynomial.eval z (charbonnelLastCoordinatePolynomial n c) = 0} ∈
      charbonnelClosure S (n + 1) :=
    hC.ws2_polynomialSign (by omega) (.zero _)
  rw [show charbonnelRestrictedGraph base (fun _ ↦ c) =
      realEuclideanTakeLeftLinearMap n 1 ⁻¹' base ∩
        {z : RealEuclidean (n + 1) |
          MvPolynomial.eval z (charbonnelLastCoordinatePolynomial n c) = 0} by
    ext z
    simp [charbonnelRestrictedGraph, sub_eq_zero]]
  exact hC.ws1_inter (by omega) hbasePull hlevel

/-- The open cube in each positive dimension, packaged as a recursive cell. -/
noncomputable def charbonnelOpenCubeCell
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S)) :
    ∀ n : ℕ, 0 < n → CharbonnelCell (charbonnelClosure S) n
  | 0, hn => False.elim (Nat.lt_asymm hn hn)
  | n + 1, _hn => by
      by_cases hn : n = 0
      · subst n
        exact charbonnelUnaryCell hC (.bounded (-1) 1)
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        let base := charbonnelOpenCubeCell hC n hnpos
        let lower : RealEuclidean n → ℝ := fun _ ↦ -1
        let upper : RealEuclidean n → ℝ := fun _ ↦ 1
        have hlower : charbonnelRestrictedGraph base.carrier lower ∈
            charbonnelClosure S (n + 1) :=
          charbonnelRestrictedConstantGraph_mem_charbonnelClosure
            hC hnpos base.carrier_mem (-1)
        have hupper : charbonnelRestrictedGraph base.carrier upper ∈
            charbonnelClosure S (n + 1) :=
          charbonnelRestrictedConstantGraph_mem_charbonnelClosure
            hC hnpos base.carrier_mem 1
        exact
          { carrier := charbonnelOpenBand base.carrier lower upper
            shape := .band hnpos base.shape lower upper
              continuousOn_const continuousOn_const (by norm_num)
            carrier_mem :=
              charbonnelOpenBand_mem_charbonnelClosure_of_graph_mem
                hC hlower hupper }
termination_by n => n

theorem charbonnelOpenCubeCell_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) :
    (charbonnelOpenCubeCell hC n hn).carrier = wilkieOpenCube n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      by_cases hm : m = 0
      · subst m
        ext x
        simp [charbonnelOpenCubeCell, charbonnelUnaryCell,
          realEuclideanUnaryPiece, realEuclideanUnaryLift,
          UnaryPiece.carrier, wilkieOpenCube]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        rw [show (charbonnelOpenCubeCell hC (m + 1) (by omega)).carrier =
            charbonnelOpenBand
              (charbonnelOpenCubeCell hC m hmpos).carrier
              (fun _ ↦ -1) (fun _ ↦ 1) by
          simp [charbonnelOpenCubeCell, hm]]
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

/-- The open cube in successor dimension, with the two constant boundary
graphs retained. -/
noncomputable def charbonnelOpenCubeEnrichedCell
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) : CharbonnelEnrichedSuccessorCell S n := by
  let base := charbonnelOpenCubeCell hC n hn
  let lower : RealEuclidean n → ℝ := fun _ ↦ -1
  let upper : RealEuclidean n → ℝ := fun _ ↦ 1
  exact ⟨base, .band lower upper continuousOn_const continuousOn_const
    (by norm_num)
    (charbonnelRestrictedConstantGraph_mem_charbonnelClosure
      hC hn base.carrier_mem (-1))
    (charbonnelRestrictedConstantGraph_mem_charbonnelClosure
      hC hn base.carrier_mem 1)⟩

@[simp]
theorem charbonnelOpenCubeEnrichedCell_carrier
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) :
    (charbonnelOpenCubeEnrichedCell hC hn).carrier =
      wilkieOpenCube (n + 1) := by
  change charbonnelOpenBand
      (charbonnelOpenCubeCell hC n hn).carrier
      (fun _ ↦ -1) (fun _ ↦ 1) = wilkieOpenCube (n + 1)
  rw [charbonnelOpenCubeCell_carrier hC hn]
  ext z
  simp only [charbonnelOpenBand, wilkieOpenCube, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hlower, hupper⟩ i
    refine Fin.addCases (m := n) (n := 1)
      (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa [realEuclideanTakeLeft] using hx j
    · fin_cases j
      simpa [realEuclideanTakeRight] using And.intro hlower hupper
  · intro hz
    refine ⟨?_, ?_, ?_⟩
    · intro j
      simpa [realEuclideanTakeLeft] using hz (Fin.castAdd 1 j)
    · simpa [realEuclideanTakeRight] using
        (hz (Fin.natAdd n (0 : Fin 1))).1
    · simpa [realEuclideanTakeRight] using
        (hz (Fin.natAdd n (0 : Fin 1))).2

/-! ## What partitioned refinement already supplies -/

/-- Forget the partition clause at one fixed dimension. -/
theorem charbonnelFiniteCellFamilyCommonRefinementAt_of_partitionedAt
    {C : EuclideanSetFamily} {n : ℕ}
    (hII : CharbonnelFinitePartitionedCellFamilyCommonRefinementAt C n) :
    CharbonnelFiniteCellFamilyCommonRefinementAt C n := by
  intro I _ cells
  obtain ⟨fine⟩ := hII cells
  exact ⟨fine.cover⟩

/-- A finite enriched decomposition of each projected closed lift, together
with partitioned common refinement in the same ambient dimension, already
constructs all closed-member covers.  No separate boundary-selector premise
is needed for this consequence. -/
theorem
    charbonnelPositiveDimensionalClosedMemberCellCoverProperty_of_enrichedDecompositions
    {S : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure (charbonnelClosure S))
    (hII :
      CharbonnelPositiveDimensionalFinitePartitionedCellFamilyCommonRefinementProperty
        (charbonnelClosure S))
    (hdecomposition :
      CharbonnelEnrichedProjectedClosedLiftDecompositionProperty S) :
    CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S) := by
  intro d hd A hAclosed hAmem
  by_cases hd1 : d = 1
  · subst d
    exact hC.nonempty_unaryCompatibleCellCover hAmem
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    have hn : 0 < n := by omega
    obtain ⟨decomposition⟩ :
        Nonempty (CharbonnelFiniteEnrichedSuccessorDecomposition S n A) := by
      simpa using
        (hdecomposition (n := n) (q := 0) hn hAclosed hAmem)
    obtain ⟨fine⟩ :=
      hII (by omega : 0 < n + 1)
        (fun i ↦ (decomposition.cell i).toCell
          hC.toPositiveArityWeakSetStructure hn)
    refine ⟨
      { count := fine.cover.count
        cell := fine.cover.cell
        covers := fine.cover.covers
        compatible := ?_ }⟩
    intro i
    have hcompat : ∀ j,
        (fine.cover.cell i).carrier ⊆ (decomposition.cell j).carrier ∨
          Disjoint (fine.cover.cell i).carrier
            (decomposition.cell j).carrier := by
      intro j
      simpa using fine.cover.compatible i j
    rcases subset_iUnion_or_disjoint_iUnion_of_compatible hcompat with
      hsubset | hdisjoint
    · left
      exact hsubset.trans decomposition.union_eq.symm.subset
    · right
      exact hdisjoint.mono Subset.rfl decomposition.union_eq.subset

/-- Dimension-local version of the retained successor refinement.  This is
the same selector construction as the global theorem, but it asks for common
refinement only in the one base dimension actually used. -/
theorem charbonnelFiniteEnrichedCellFamilyCommonRefinement_succ_retained_at
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (hI : CharbonnelPositiveDimensionalClosedMemberCellCoverProperty
      (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (hII : CharbonnelFiniteCellFamilyCommonRefinementAt
      (charbonnelClosure S) n)
    {I : Type} [Fintype I]
    (input : I → CharbonnelEnrichedSuccessorCell S n) :
    Nonempty
      (CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
        S Set.univ (fun i ↦ (input i).carrier)) := by
  classical
  obtain ⟨refinement⟩ :=
    exists_charbonnelEnrichedEqualityBaseRefinement_at
      hC hI hn hII input
  let lift : ∀ k,
      CharbonnelFiniteEnrichedSimultaneouslyCompatibleRelativeCellCover
        S (charbonnelCylinderCell (refinement.cell k).carrier)
        (fun i ↦ (input i).carrier) :=
    fun k ↦ Classical.choice
      (exists_charbonnelEnrichedLocalSelectorCoverRetained hC hn refinement k)
  let _ : ∀ k, Finite (lift k).Index :=
    fun k ↦ (lift k).indexFinite
  let Index := Σ k, (lift k).Index
  let _ : Fintype Index := Fintype.ofFinite Index
  refine ⟨
    { Index := Index
      indexFinite := inferInstance
      cell := fun q ↦ (lift q.1).cell q.2
      contained := fun _ _ _ ↦ Set.mem_univ _
      covers := ?_
      compatible := ?_ }⟩
  · intro z _hz
    obtain ⟨k, hk⟩ := refinement.covers (realEuclideanTakeLeft z)
    have hzCylinder : z ∈
        charbonnelCylinderCell (refinement.cell k).carrier := hk
    obtain ⟨j, hj⟩ := (lift k).covers z hzCylinder
    exact ⟨⟨k, j⟩, hj⟩
  · intro q i
    exact (lift q.1).compatible q.2 i

end AbelFormalization
