import AbelFormalization.CharbonnelClosureNullityWitnesses
import Mathlib.Algebra.BigOperators.Fin

/-!
# The finite locally closed reduction in Charbonnel's closure

This file isolates exactly what can be proved by finite topology and the
description algebra about locally closed pieces.

Charbonnel 5.1 starts with one set already assumed locally closed.  Section
5.5 proves that one particular exceptional base set is locally closed.  Those
arguments do not give a finite locally closed decomposition of every member
of the Charbonnel closure.  For the inductive description language, base and
closure nodes have a one-piece decomposition, unions concatenate finite
decompositions, and integer-affine cuts restrict every piece.  The only
remaining constructor is existential projection.  The proposition
`CharbonnelLocallyClosedProjectionDecomposition` below records precisely that
missing geometric projection step.

The final section also records the weaker statement actually used in
Maxwell--Servi's formulation of the closure-smallness result: empty interior
is preserved by closure.  It suffices in place of the stronger finite-piece
premise in the section 5 assembly.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators MeasureTheory Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Per-set finite decompositions -/

/-- A finite locally closed decomposition of one set, with every piece still
belonging to the same Euclidean set family. -/
def HasCharbonnelFiniteLocallyClosedDecomposition
    (C : EuclideanSetFamily) {d : ℕ}
    (S : Set (RealEuclidean d)) : Prop :=
  ∃ (k : ℕ) (piece : Fin k → Set (RealEuclidean d)),
    (∀ i, piece i ∈ C d) ∧
    (∀ i, IsLocallyClosed (piece i)) ∧
    S = ⋃ i, piece i

theorem charbonnelFiniteLocallyClosedDecomposition_iff
    {C : EuclideanSetFamily} {d : ℕ} :
    CharbonnelFiniteLocallyClosedDecomposition C d ↔
      ∀ S : Set (RealEuclidean d), S ∈ C d →
        HasCharbonnelFiniteLocallyClosedDecomposition C S :=
  Iff.rfl

/-- A locally closed family member is its own one-piece decomposition. -/
theorem hasCharbonnelFiniteLocallyClosedDecomposition_of_isLocallyClosed
    {C : EuclideanSetFamily} {d : ℕ}
    {S : Set (RealEuclidean d)} (hS : S ∈ C d)
    (hSLocallyClosed : IsLocallyClosed S) :
    HasCharbonnelFiniteLocallyClosedDecomposition C S := by
  refine ⟨1, (fun _ ↦ S), (fun _ ↦ hS),
    (fun _ ↦ hSLocallyClosed), ?_⟩
  ext x
  simp only [mem_iUnion]
  constructor
  · intro hx
    exact ⟨0, hx⟩
  · rintro ⟨_, hx⟩
    exact hx

/-- Finite locally closed decompositions concatenate across a binary union. -/
theorem HasCharbonnelFiniteLocallyClosedDecomposition.union
    {C : EuclideanSetFamily} {d : ℕ}
    {S T : Set (RealEuclidean d)}
    (hS : HasCharbonnelFiniteLocallyClosedDecomposition C S)
    (hT : HasCharbonnelFiniteLocallyClosedDecomposition C T) :
    HasCharbonnelFiniteLocallyClosedDecomposition C (S ∪ T) := by
  obtain ⟨k, left, hleftMem, hleftLocallyClosed, hSUnion⟩ := hS
  obtain ⟨l, right, hrightMem, hrightLocallyClosed, hTUnion⟩ := hT
  refine ⟨k + l, Fin.addCases left right, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa using hleftMem j
    · simpa using hrightMem j
  · intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa using hleftLocallyClosed j
    · simpa using hrightLocallyClosed j
  · rw [hSUnion, hTUnion]
    ext x
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
      · exact ⟨Fin.castAdd l i, by simpa⟩
      · exact ⟨Fin.natAdd k j, by simpa⟩
    · rintro ⟨i, hi⟩
      exact Fin.addCases
        (fun j hj ↦ Or.inl ⟨j, by simpa using hj⟩)
        (fun j hj ↦ Or.inr ⟨j, by simpa using hj⟩) i hi

/-- Restrict every piece of a decomposition by an integer-affine set. -/
theorem HasCharbonnelFiniteLocallyClosedDecomposition.integerAffineInter
    {B : EuclideanSetFamily} {d : ℕ}
    {S L : Set (RealEuclidean d)}
    (hS : HasCharbonnelFiniteLocallyClosedDecomposition
      (charbonnelClosure B) S)
    (hL : IsIntegerAffineSet L) :
    HasCharbonnelFiniteLocallyClosedDecomposition
      (charbonnelClosure B) (S ∩ L) := by
  obtain ⟨k, piece, hpieceMem, hpieceLocallyClosed, hSUnion⟩ := hS
  refine ⟨k, (fun i ↦ piece i ∩ L), ?_, ?_, ?_⟩
  · intro i
    exact charbonnelClosure_integerAffineInter (hpieceMem i) hL
  · intro i
    exact (hpieceLocallyClosed i).inter hL.isClosed.isLocallyClosed
  · rw [hSUnion]
    ext x
    simp only [mem_inter_iff, mem_iUnion]
    constructor
    · rintro ⟨⟨i, hi⟩, hxL⟩
      exact ⟨i, hi, hxL⟩
    · rintro ⟨i, hi, hxL⟩
      exact ⟨⟨i, hi⟩, hxL⟩

/-- Existential projection commutes with an arbitrary indexed union. -/
theorem realEuclideanExistentialProjection_iUnion
    {I : Type*} {n q : ℕ}
    (piece : I → Set (RealEuclidean (n + q))) :
    realEuclideanExistentialProjection (⋃ i, piece i) =
      ⋃ i, realEuclideanExistentialProjection (piece i) := by
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_ofPred_eq,
    Set.mem_iUnion]
  constructor
  · rintro ⟨y, i, hxy⟩
    exact ⟨i, y, hxy⟩
  · rintro ⟨i, y, hxy⟩
    exact ⟨y, i, hxy⟩

/-! ## The unique missing description constructor -/

/-- The projection-stratification input left after the elementary
description induction: the projection of one locally closed family member
is a finite union of locally closed family members. -/
def CharbonnelLocallyClosedProjectionDecomposition
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n q : ℕ}, 0 < n →
    ∀ {S : Set (RealEuclidean (n + q))}, S ∈ C (n + q) →
      IsLocallyClosed S →
        HasCharbonnelFiniteLocallyClosedDecomposition C
          (realEuclideanExistentialProjection S)

/-- Once projections of individual locally closed pieces can be decomposed,
projection preserves every finite locally closed decomposition. -/
theorem HasCharbonnelFiniteLocallyClosedDecomposition.projection
    {C : EuclideanSetFamily} {n q : ℕ} (hn : 0 < n)
    {S : Set (RealEuclidean (n + q))}
    (hS : HasCharbonnelFiniteLocallyClosedDecomposition C S)
    (hprojection : CharbonnelLocallyClosedProjectionDecomposition C) :
    HasCharbonnelFiniteLocallyClosedDecomposition C
      (realEuclideanExistentialProjection S) := by
  classical
  obtain ⟨k, piece, hpieceMem, hpieceLocallyClosed, hSUnion⟩ := hS
  choose count projected hprojected using fun i ↦
    hprojection hn (hpieceMem i) (hpieceLocallyClosed i)
  let e : Fin (∑ i, count i) ≃ Σ i, Fin (count i) :=
    finSigmaFinEquiv.symm
  let flat : Fin (∑ i, count i) → Set (RealEuclidean n) :=
    fun j ↦ projected (e j).1 (e j).2
  refine ⟨∑ i, count i, flat, ?_, ?_, ?_⟩
  · intro j
    exact (hprojected (e j).1).1 (e j).2
  · intro j
    exact (hprojected (e j).1).2.1 (e j).2
  · rw [hSUnion, realEuclideanExistentialProjection_iUnion]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      rw [(hprojected i).2.2] at hi
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
      refine ⟨e.symm ⟨i, j⟩, ?_⟩
      change x ∈ projected (e (e.symm ⟨i, j⟩)).1
        (e (e.symm ⟨i, j⟩)).2
      rw [Equiv.apply_symm_apply]
      exact hj
    · rintro ⟨j, hj⟩
      have hj' : x ∈ projected (e j).1 (e j).2 := by
        simpa only [flat] using hj
      refine ⟨(e j).1, ?_⟩
      rw [(hprojected (e j).1).2.2]
      exact Set.mem_iUnion.mpr ⟨(e j).2, hj'⟩

/-- Every Charbonnel description has a finite locally closed decomposition
once the projection constructor has the preceding geometric property.  All
other cases use only the description semantics and finite topology. -/
theorem CharbonnelDescription.hasFiniteLocallyClosedDecomposition
    {B : EuclideanSetFamily}
    (hbaseClosed : IsClosedPositiveAritySetFamily B)
    (hprojection : CharbonnelLocallyClosedProjectionDecomposition
      (charbonnelClosure B))
    {d : ℕ} (description : CharbonnelDescription B d) :
    HasCharbonnelFiniteLocallyClosedDecomposition
      (charbonnelClosure B) description.carrier := by
  induction description with
  | @base d hd S hS =>
      exact hasCharbonnelFiniteLocallyClosedDecomposition_of_isLocallyClosed
        (mem_charbonnelClosure_of_mem hd hS)
        (hbaseClosed hd hS).isLocallyClosed
  | @union d left right hleft hright =>
      exact hleft.union hright
  | @integerAffineInter d inner L hL hinner =>
      exact hinner.integerAffineInter hL
  | @projection d q hd inner hinner =>
      exact hinner.projection hd hprojection
  | @topologicalClosure d inner _hinner =>
      exact hasCharbonnelFiniteLocallyClosedDecomposition_of_isLocallyClosed
        (⟨CharbonnelDescription.topologicalClosure inner, rfl⟩)
        isClosed_closure.isLocallyClosed

/-- Family-level constructor induction. -/
theorem charbonnelClosure_finiteLocallyClosedDecomposition_of_projection
    {B : EuclideanSetFamily}
    (hbaseClosed : IsClosedPositiveAritySetFamily B)
    (hprojection : CharbonnelLocallyClosedProjectionDecomposition
      (charbonnelClosure B)) :
    ∀ d : ℕ,
      CharbonnelFiniteLocallyClosedDecomposition (charbonnelClosure B) d := by
  intro d S hS
  obtain ⟨description, rfl⟩ := hS
  exact CharbonnelDescription.hasFiniteLocallyClosedDecomposition
    hbaseClosed hprojection description

/-- Literal zero-set specialization of the constructor reduction. -/
theorem literalZeroSet_charbonnelClosure_finiteLocallyClosedDecomposition_of_projection
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hprojection : CharbonnelLocallyClosedProjectionDecomposition
      (charbonnelClosure (literalZeroSetFamily G))) :
    ∀ d : ℕ, CharbonnelFiniteLocallyClosedDecomposition
      (charbonnelClosure (literalZeroSetFamily G)) d :=
  charbonnelClosure_finiteLocallyClosedDecomposition_of_projection
    (literalZeroSetFamily_isClosed hsmooth) hprojection

/-! ## Equivalent narrowing through the closed-lift theorem -/

/-- A narrower projection input adapted to the closed lifts from Servi
3.3.9 and Charbonnel 2.2(v). -/
def CharbonnelClosedProjectionDecomposition
    (C : EuclideanSetFamily) : Prop :=
  ∀ {n q : ℕ}, 0 < n →
    ∀ {T : Set (RealEuclidean (n + q))}, T ∈ C (n + q) →
      IsClosed T →
        HasCharbonnelFiniteLocallyClosedDecomposition C
          (realEuclideanExistentialProjection T)

theorem CharbonnelLocallyClosedProjectionDecomposition.toClosed
    {C : EuclideanSetFamily}
    (hprojection : CharbonnelLocallyClosedProjectionDecomposition C) :
    CharbonnelClosedProjectionDecomposition C := by
  intro n q hn T hT hTClosed
  exact hprojection hn hT hTClosed.isLocallyClosed

/-- The proved closed-lift theorem reduces the desired literal-zero result
to decomposition of projections of closed family members. -/
theorem literalZeroSet_charbonnelClosure_finiteLocallyClosedDecomposition_of_closedProjection
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hprojection : CharbonnelClosedProjectionDecomposition
      (charbonnelClosure (literalZeroSetFamily G))) :
    ∀ {d : ℕ}, 0 < d →
      CharbonnelFiniteLocallyClosedDecomposition
        (charbonnelClosure (literalZeroSetFamily G)) d := by
  intro d hd S hS
  obtain ⟨q, T, hTClosed, hT, hST⟩ :=
    literalZeroSet_charbonnelClosure_semiClosed hG hsmooth hS
  rw [hST]
  exact hprojection hd hT hTClosed

/-! ## The weaker source-shaped closure statement -/

/-- The closure regularity stated by Maxwell and Servi: within the family,
closure preserves empty interior in positive arity. -/
def CharbonnelClosureInteriorRegularity
    (C : EuclideanSetFamily) : Prop :=
  ∀ {d : ℕ}, 0 < d →
    ∀ {S : Set (RealEuclidean d)}, S ∈ C d →
      interior S = ∅ → interior (closure S) = ∅

/-- A finite locally closed decomposition implies closure-interior
regularity by finite union of nowhere-dense pieces. -/
theorem HasCharbonnelFiniteLocallyClosedDecomposition.closureInterior_eq_empty
    {C : EuclideanSetFamily} {d : ℕ}
    {S : Set (RealEuclidean d)}
    (hS : HasCharbonnelFiniteLocallyClosedDecomposition C S)
    (hSInterior : interior S = ∅) :
    interior (closure S) = ∅ := by
  obtain ⟨k, piece, _hpieceMem, hpieceLocallyClosed, hSUnion⟩ := hS
  rw [hSUnion]
  exact IsNowhereDense.iUnion fun i ↦ by
    have hpieceSubset : piece i ⊆ S := by
      rw [hSUnion]
      exact subset_iUnion piece i
    have hpieceInterior : interior (piece i) = ∅ :=
      interior_eq_empty_of_subset hpieceSubset hSInterior
    exact IsLocallyClosed.interior_closure_eq_empty
      (hpieceLocallyClosed i) hpieceInterior

/-- Family-level finite decomposition is therefore stronger than the exact
closure-interior regularity used later in section 5. -/
theorem charbonnelClosureInteriorRegularity_of_finiteLocallyClosedDecomposition
    {C : EuclideanSetFamily}
    (hdecomposition : ∀ {d : ℕ}, 0 < d →
      CharbonnelFiniteLocallyClosedDecomposition C d) :
    CharbonnelClosureInteriorRegularity C := by
  intro d hd S hS hSInterior
  exact HasCharbonnelFiniteLocallyClosedDecomposition.closureInterior_eq_empty
    (hdecomposition hd S hS) hSInterior

/-- The source-shaped closure regularity and `P'_n` already give the
nullity/empty-interior equivalence for arbitrary family members. -/
theorem charbonnelInteriorNullity_of_pPrime_and_closureInteriorRegularity
    {C : EuclideanSetFamily} {d : ℕ} (hd : 0 < d)
    (hmem : CharbonnelSection5TraceMembership C)
    (hregularity : CharbonnelClosureInteriorRegularity C)
    (hPPrime : CharbonnelPPrime C d) :
    CharbonnelInteriorNullity C d := by
  intro S hS
  constructor
  · intro hSNull
    exact (volume : Measure (RealEuclidean d)).interior_eq_empty_of_null hSNull
  · intro hSInterior
    have hclosureInterior : interior (closure S) = ∅ :=
      hregularity hd hS hSInterior
    have hclosureMem : closure S ∈ C d :=
      hmem.closure_mem hd hS
    exact measure_mono_null subset_closure
      ((hPPrime (closure S) isClosed_closure hclosureMem).mpr
        hclosureInterior)

/-- Section 5 can be assembled using the exact closure-interior statement,
without asking for the stronger finite locally closed decomposition. -/
theorem charbonnelApproximationTraceSmallness_of_section5Induction_and_closureInteriorRegularity
    {C : EuclideanSetFamily}
    (hmem : CharbonnelSection5TraceMembership C)
    (htrunc : CharbonnelCompactTruncationMembership C)
    (hbase : CharbonnelPPrime C 1)
    (hanalytic : CharbonnelSection5AnalyticStep C)
    (hregularity : CharbonnelClosureInteriorRegularity C)
    (hwitness : HasCharbonnelClosureNullityWitnesses C) :
    CharbonnelApproximationTraceSmallness C := by
  have hPPrime : ∀ {d : ℕ}, 0 < d → CharbonnelPPrime C d :=
    charbonnelPPrime_all_of_one_and_analyticStep htrunc hbase hanalytic
  have hQ : ∀ {d : ℕ}, 0 < d → CharbonnelQ C d := by
    intro d hd
    exact charbonnelQ_of_pPrime_and_analyticStep hd htrunc hanalytic
      (hPPrime hd)
  have hP : ∀ {d : ℕ}, 0 < d → CharbonnelP C d := by
    intro d hd
    exact charbonnelP_of_pPrime_Q_and_closureWitness
      hd hmem (hPPrime hd) (hQ hd) hwitness
  have hnull : ∀ {d : ℕ}, 0 < d → CharbonnelInteriorNullity C d := by
    intro d hd
    exact charbonnelInteriorNullity_of_pPrime_and_closureInteriorRegularity
      hd hmem hregularity (hPPrime hd)
  exact charbonnelApproximationTraceSmallness_of_section5
    hmem hnull hP hQ

/-- Literal-zero assembly with the proved elementary inputs and section 5.8
witnesses.  The remaining regularity premise is the exact Maxwell--Servi
closure statement rather than a finite-piece strengthening. -/
theorem literalZeroSet_charbonnelClosure_approximationTraceSmallness_of_section5ClosureRegularity
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)))
    (hanalytic : CharbonnelSection5AnalyticStep
      (charbonnelClosure (literalZeroSetFamily G)))
    (hregularity : CharbonnelClosureInteriorRegularity
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelApproximationTraceSmallness
      (charbonnelClosure (literalZeroSetFamily G)) :=
  charbonnelApproximationTraceSmallness_of_section5Induction_and_closureInteriorRegularity
    (literalZeroSet_charbonnelClosure_section5TraceMembership hG hsmooth)
    (literalZeroSet_charbonnelClosure_compactTruncationMembership hG hsmooth)
    hC.charbonnelPPrime_one hanalytic hregularity
    (literalZeroSet_charbonnelClosure_hasClosureNullityWitnesses hG hsmooth)

end AbelFormalization
