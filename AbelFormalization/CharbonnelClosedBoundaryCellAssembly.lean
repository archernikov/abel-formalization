import AbelFormalization.CharbonnelComplementPipeline
import AbelFormalization.UnaryPieceDecomposition

/-!
# Cell-cover reduction for the closed-boundary complement assembly

This module isolates the set-theoretic endpoint of Wilkie's section 4 cell
argument and proves its one-dimensional base.

* WS5 decomposes every unary member into finitely many points and intervals.
  Those pieces, and their complements, are polynomial-sign constructible, so
  every unary member of an o-minimal weak family has a complement in the same
  family.
* In higher dimension, a finite cover by family-member cells compatible with
  a set immediately puts its complement in the family.
* WS6 therefore reduces all remaining positive-arity complements to finite
  compatible cell covers of the visible projections of closed lifts.

The last property is exactly the output supplied by Wilkie's simultaneous
cell-decomposition induction.  No complement theorem is used in proving the
reduction.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Unary sign cells -/

/-- Lift a scalar set to the unique coordinate of `RealEuclidean 1`. -/
def realEuclideanUnaryLift (s : Set ℝ) : Set (RealEuclidean 1) :=
  {x | x 0 ∈ s}

/-- Lift one unary decomposition piece to `RealEuclidean 1`. -/
def realEuclideanUnaryPiece (piece : UnaryPiece) : Set (RealEuclidean 1) :=
  realEuclideanUnaryLift piece.carrier

def unaryLowerSignPolynomial (a : ℝ) : MvPolynomial (Fin 1) ℝ :=
  MvPolynomial.X 0 - MvPolynomial.C a

def unaryUpperSignPolynomial (b : ℝ) : MvPolynomial (Fin 1) ℝ :=
  MvPolynomial.C b - MvPolynomial.X 0

@[simp]
theorem unaryLowerSignPolynomial_eval (a : ℝ) (x : RealEuclidean 1) :
    MvPolynomial.eval x (unaryLowerSignPolynomial a) = x 0 - a := by
  simp [unaryLowerSignPolynomial]

@[simp]
theorem unaryUpperSignPolynomial_eval (b : ℝ) (x : RealEuclidean 1) :
    MvPolynomial.eval x (unaryUpperSignPolynomial b) = b - x 0 := by
  simp [unaryUpperSignPolynomial]

/-- Every lifted point, interval, or ray used by a unary cell decomposition
is polynomial-sign constructible. -/
theorem polynomialSignConstructible_realEuclideanUnaryPiece
    (piece : UnaryPiece) :
    PolynomialSignConstructible 1 (realEuclideanUnaryPiece piece) := by
  cases piece with
  | point a =>
      simpa [realEuclideanUnaryPiece, realEuclideanUnaryLift,
        UnaryPiece.carrier, sub_eq_zero] using
        (PolynomialSignConstructible.zero (unaryLowerSignPolynomial a))
  | bounded a b =>
      rw [show realEuclideanUnaryPiece (.bounded a b) =
          {x : RealEuclidean 1 | a < x 0} ∩
            {x : RealEuclidean 1 | x 0 < b} by
        ext x
        simp [realEuclideanUnaryPiece, realEuclideanUnaryLift,
          UnaryPiece.carrier]]
      simpa using
        (PolynomialSignConstructible.inter
          (PolynomialSignConstructible.pos (unaryLowerSignPolynomial a))
          (PolynomialSignConstructible.pos (unaryUpperSignPolynomial b)))
  | leftRay b =>
      simpa [realEuclideanUnaryPiece, realEuclideanUnaryLift,
        UnaryPiece.carrier] using
        (PolynomialSignConstructible.pos (unaryUpperSignPolynomial b))
  | rightRay a =>
      simpa [realEuclideanUnaryPiece, realEuclideanUnaryLift,
        UnaryPiece.carrier] using
        (PolynomialSignConstructible.pos (unaryLowerSignPolynomial a))
  | whole =>
      simpa [realEuclideanUnaryPiece, realEuclideanUnaryLift,
        UnaryPiece.carrier] using polynomialSignConstructible_univ 1

/-- Polynomial-sign constructible sets are closed under unions indexed by a
finite ordinal. -/
theorem polynomialSignConstructible_iUnion_fin
    {d r : ℕ} (s : Fin r → Set (RealEuclidean d))
    (hs : ∀ i, PolynomialSignConstructible d (s i)) :
    PolynomialSignConstructible d (⋃ i, s i) := by
  induction r with
  | zero =>
      simpa using polynomialSignConstructible_empty d
  | succ r ih =>
      rw [show (⋃ i : Fin (r + 1), s i) =
          s 0 ∪ ⋃ j : Fin r, s j.succ by
        ext x
        simp only [mem_iUnion, mem_union]
        constructor
        · rintro ⟨i, hi⟩
          exact Fin.cases
            (motive := fun i ↦ x ∈ s i →
              x ∈ s 0 ∨ ∃ j : Fin r, x ∈ s j.succ)
            (fun h ↦ Or.inl h)
            (fun j h ↦ Or.inr ⟨j, h⟩) i hi
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨0, hx⟩
          · exact ⟨j.succ, hj⟩]
      exact .union (hs 0)
        (ih (fun j ↦ s j.succ) (fun j ↦ hs j.succ))

/-- A finite unary-piece decomposition becomes a polynomial-sign
construction after lifting to `RealEuclidean 1`. -/
theorem UnaryPieceDecomposable.polynomialSignConstructible_unaryLift
    {s : Set ℝ} (hs : UnaryPieceDecomposable s) :
    PolynomialSignConstructible 1 (realEuclideanUnaryLift s) := by
  obtain ⟨r, pieces, hpieces⟩ := hs
  have hlift : realEuclideanUnaryLift s =
      ⋃ i, realEuclideanUnaryPiece (pieces i) := by
    rw [hpieces]
    ext x
    simp [realEuclideanUnaryLift, realEuclideanUnaryPiece]
  rw [hlift]
  exact polynomialSignConstructible_iUnion_fin _
    (fun i ↦ polynomialSignConstructible_realEuclideanUnaryPiece
      (pieces i))

@[simp]
theorem mem_realEuclideanOneCoordinateImage_iff
    (A : Set (RealEuclidean 1)) (x : RealEuclidean 1) :
    x 0 ∈ realEuclideanOneCoordinateImage A ↔ x ∈ A := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hxy : y = x := by
      funext i
      rw [show i = 0 from Fin.eq_zero i]
      exact hyx
    simpa [hxy] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The unary case of the complement theorem follows already from WS2 and
WS5.  It does not use the closed-boundary-carrier property. -/
theorem PositiveArityOMinimalWeakSetStructure.compl_mem_one
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {A : Set (RealEuclidean 1)} (hA : A ∈ C 1) :
    Aᶜ ∈ C 1 := by
  have hpieces :
      UnaryPieceDecomposable (realEuclideanOneCoordinateImage A) :=
    hC.coordinateImage_unaryPieceDecomposable hA
  have hsign : PolynomialSignConstructible 1
      (realEuclideanUnaryLift
        (realEuclideanOneCoordinateImage A)ᶜ) :=
    hpieces.compl.polynomialSignConstructible_unaryLift
  have hlift : realEuclideanUnaryLift
      (realEuclideanOneCoordinateImage A)ᶜ = Aᶜ := by
    ext x
    simp only [realEuclideanUnaryLift, mem_ofPred_eq, mem_compl_iff,
      mem_realEuclideanOneCoordinateImage_iff]
  rw [← hlift]
  exact hC.ws2_polynomialSign (by omega) hsign

/-! ## Charbonnel graph and band cells -/

def charbonnelRestrictedGraph {n : ℕ}
    (base : Set (RealEuclidean n)) (f : RealEuclidean n → ℝ) :
    Set (RealEuclidean (n + 1)) :=
  {z | realEuclideanTakeLeft z ∈ base ∧
    realEuclideanTakeRight z 0 = f (realEuclideanTakeLeft z)}

def charbonnelOpenBand {n : ℕ}
    (base : Set (RealEuclidean n)) (f g : RealEuclidean n → ℝ) :
    Set (RealEuclidean (n + 1)) :=
  {z | realEuclideanTakeLeft z ∈ base ∧
    f (realEuclideanTakeLeft z) < realEuclideanTakeRight z 0 ∧
    realEuclideanTakeRight z 0 < g (realEuclideanTakeLeft z)}

def charbonnelLowerRayCell {n : ℕ}
    (base : Set (RealEuclidean n)) (g : RealEuclidean n → ℝ) :
    Set (RealEuclidean (n + 1)) :=
  {z | realEuclideanTakeLeft z ∈ base ∧
    realEuclideanTakeRight z 0 < g (realEuclideanTakeLeft z)}

def charbonnelUpperRayCell {n : ℕ}
    (base : Set (RealEuclidean n)) (f : RealEuclidean n → ℝ) :
    Set (RealEuclidean (n + 1)) :=
  {z | realEuclideanTakeLeft z ∈ base ∧
    f (realEuclideanTakeLeft z) < realEuclideanTakeRight z 0}

def charbonnelCylinderCell {n : ℕ}
    (base : Set (RealEuclidean n)) : Set (RealEuclidean (n + 1)) :=
  {z | realEuclideanTakeLeft z ∈ base}

/-- Recursive geometric shape of a graph/band cell. -/
inductive CharbonnelCellShape :
    ∀ n : ℕ, Set (RealEuclidean n) → Prop
  | unary (piece : UnaryPiece) :
      CharbonnelCellShape 1 (realEuclideanUnaryPiece piece)
  | graph {n : ℕ} {base : Set (RealEuclidean n)}
      (hn : 0 < n) (hbase : CharbonnelCellShape n base)
      (f : RealEuclidean n → ℝ) (hcontinuous : ContinuousOn f base) :
      CharbonnelCellShape (n + 1) (charbonnelRestrictedGraph base f)
  | band {n : ℕ} {base : Set (RealEuclidean n)}
      (hn : 0 < n) (hbase : CharbonnelCellShape n base)
      (f g : RealEuclidean n → ℝ)
      (hf : ContinuousOn f base) (hg : ContinuousOn g base)
      (hfg : ∀ x ∈ base, f x < g x) :
      CharbonnelCellShape (n + 1) (charbonnelOpenBand base f g)
  | lowerRay {n : ℕ} {base : Set (RealEuclidean n)}
      (hn : 0 < n) (hbase : CharbonnelCellShape n base)
      (g : RealEuclidean n → ℝ) (hg : ContinuousOn g base) :
      CharbonnelCellShape (n + 1) (charbonnelLowerRayCell base g)
  | upperRay {n : ℕ} {base : Set (RealEuclidean n)}
      (hn : 0 < n) (hbase : CharbonnelCellShape n base)
      (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base) :
      CharbonnelCellShape (n + 1) (charbonnelUpperRayCell base f)
  | cylinder {n : ℕ} {base : Set (RealEuclidean n)}
      (hn : 0 < n) (hbase : CharbonnelCellShape n base) :
      CharbonnelCellShape (n + 1) (charbonnelCylinderCell base)

/-- A recursive cell together with its already-established membership in the
ambient family.  The membership field is the algebraic obligation discharged
when Wilkie's graph and band cells are constructed. -/
structure CharbonnelCell (C : EuclideanSetFamily) (n : ℕ) where
  carrier : Set (RealEuclidean n)
  shape : CharbonnelCellShape n carrier
  carrier_mem : carrier ∈ C n

/-! ## Finite compatible cell covers -/

/-- A finite cover of the whole coordinate space by family-member cells,
compatible with `A`.  Pairwise disjointness is part of a traditional cell
decomposition but is not needed for the complement-membership endpoint, so
the reduction asks only for the strictly weaker cover data. -/
structure CharbonnelFiniteCompatibleCellCover
    (C : EuclideanSetFamily) {n : ℕ}
    (A : Set (RealEuclidean n)) where
  count : ℕ
  cell : Fin count → CharbonnelCell C n
  covers : ∀ x : RealEuclidean n, ∃ i, x ∈ (cell i).carrier
  compatible : ∀ i, (cell i).carrier ⊆ A ∨
    Disjoint (cell i).carrier A

theorem finite_iUnion_mem
    {X : Type*} {C : Set (Set X)}
    (hempty : (∅ : Set X) ∈ C)
    (hunion : ∀ {A B : Set X}, A ∈ C → B ∈ C → A ∪ B ∈ C)
    {r : ℕ} (s : Fin r → Set X) (hs : ∀ i, s i ∈ C) :
    (⋃ i, s i) ∈ C := by
  induction r with
  | zero => simpa using hempty
  | succ r ih =>
      rw [show (⋃ i : Fin (r + 1), s i) =
          s 0 ∪ ⋃ j : Fin r, s j.succ by
        ext x
        simp only [mem_iUnion, mem_union]
        constructor
        · rintro ⟨i, hi⟩
          exact Fin.cases
            (motive := fun i ↦ x ∈ s i →
              x ∈ s 0 ∨ ∃ j : Fin r, x ∈ s j.succ)
            (fun h ↦ Or.inl h)
            (fun j h ↦ Or.inr ⟨j, h⟩) i hi
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨0, hx⟩
          · exact ⟨j.succ, hj⟩]
      exact hunion (hs 0)
        (ih (fun j ↦ s j.succ) (fun j ↦ hs j.succ))

namespace CharbonnelFiniteCompatibleCellCover

noncomputable def outside {C : EuclideanSetFamily} {n : ℕ}
    {A : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleCellCover C A) :
    Set (RealEuclidean n) := by
  classical
  exact ⋃ i, if Disjoint (cover.cell i).carrier A then
    (cover.cell i).carrier else ∅

theorem outside_eq_compl
    {C : EuclideanSetFamily} {n : ℕ}
    {A : Set (RealEuclidean n)}
    (cover : CharbonnelFiniteCompatibleCellCover C A) :
    cover.outside = Aᶜ := by
  classical
  ext x
  constructor
  · intro hx
    simp only [outside, mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    by_cases hdisjoint : Disjoint (cover.cell i).carrier A
    · have hxcell : x ∈ (cover.cell i).carrier := by
        simpa [hdisjoint] using hi
      exact fun hxA ↦ Set.disjoint_left.mp hdisjoint hxcell hxA
    · simp [hdisjoint] at hi
  · intro hx
    have hxnot : x ∉ A := hx
    obtain ⟨i, hxcell⟩ := cover.covers x
    rcases cover.compatible i with hsubset | hdisjoint
    · exact (hxnot (hsubset hxcell)).elim
    · simp only [outside, mem_iUnion]
      exact ⟨i, by simp [hdisjoint, hxcell]⟩

/-- A finite compatible cell cover puts the complement in the family using
only the empty-set and binary-union clauses. -/
theorem complement_mem
    {C : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure C)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hunion : ∀ {left right : Set (RealEuclidean n)},
      left ∈ C n → right ∈ C n → left ∪ right ∈ C n)
    (cover : CharbonnelFiniteCompatibleCellCover C A) :
    Aᶜ ∈ C n := by
  classical
  have hempty : (∅ : Set (RealEuclidean n)) ∈ C n :=
    hC.ws2_polynomialSign hn (polynomialSignConstructible_empty n)
  have houtside : cover.outside ∈ C n := by
    apply finite_iUnion_mem hempty hunion
    intro i
    by_cases hdisjoint : Disjoint (cover.cell i).carrier A
    · simpa [outside, hdisjoint] using (cover.cell i).carrier_mem
    · simpa [outside, hdisjoint] using hempty
  rwa [cover.outside_eq_compl] at houtside

end CharbonnelFiniteCompatibleCellCover

/-! ## Exact higher-dimensional residual -/

/-- The output of the still-unformalized higher-dimensional part of Wilkie's
simultaneous cell induction.  A closed WS6 lift must induce, after projecting
to any visible arity greater than one, a finite compatible cover by recursive
Charbonnel cells. -/
def CharbonnelHigherDimensionalClosedLiftCellCoverProperty
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n q : ℕ}, 1 < n →
    ∀ {B : Set (RealEuclidean (n + q))}, IsClosed B → B ∈ C (n + q) →
      Nonempty (CharbonnelFiniteCompatibleCellCover C
        (realEuclideanExistentialProjection B))

/-- Unary complement closure and higher-dimensional compatible covers finish
positive-arity complement closure after applying WS6. -/
theorem positiveArity_compl_mem_of_closedLiftCellCovers
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hunion : ∀ {n : ℕ} {A B : Set (RealEuclidean n)},
      A ∈ C n → B ∈ C n → A ∪ B ∈ C n)
    (hcovers : CharbonnelHigherDimensionalClosedLiftCellCoverProperty C)
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)} (hA : A ∈ C n) :
    Aᶜ ∈ C n := by
  by_cases hone : n = 1
  · subst n
    exact hC.compl_mem_one hA
  · have htwo : 1 < n := by omega
    obtain ⟨q, B, hBclosed, hBmem, hprojection⟩ :=
      hC.ws6_closedLift hn hA
    obtain ⟨cover⟩ := hcovers htwo hBclosed hBmem
    rw [hprojection]
    exact CharbonnelFiniteCompatibleCellCover.complement_mem
      hC.toPositiveArityWeakSetStructure hn
      (fun hleft hright ↦ hunion hleft hright) cover

/-- The remaining source cell step, now stripped of the completed unary base
and of the formal finite-cover/WS6 assembly. -/
def CharbonnelClosedBoundaryCellCoverAssembly
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  CharbonnelClosedBoundaryCarrierProperty G →
    CharbonnelHigherDimensionalClosedLiftCellCoverProperty
      (charbonnelClosure (literalZeroSetFamily G))

/-- The narrowed higher-dimensional cell-cover premise discharges the older
unproved closed-boundary complement-assembly premise. -/
theorem charbonnelClosedBoundaryComplementAssembly_of_cellCovers
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hcells : CharbonnelClosedBoundaryCellCoverAssembly G) :
    CharbonnelClosedBoundaryComplementAssembly G := by
  intro hboundary n hn A hA
  exact positiveArity_compl_mem_of_closedLiftCellCovers
    (literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure
      hG hsmooth hUFF)
    (fun hleft hright ↦ charbonnelClosure_union hleft hright)
    (hcells hboundary) hn hA

end AbelFormalization
