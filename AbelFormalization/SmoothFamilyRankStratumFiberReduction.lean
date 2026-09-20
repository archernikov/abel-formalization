import AbelFormalization.SmoothFamilyRankStratumLocalFiber

/-!
# Reducing fiber-component finiteness to exact-rank pieces

Every fiber is covered by the finitely many loci on which the derivative has
one fixed rank.  Connected components of the rank pieces therefore map
surjectively onto the connected components of the whole fiber.

This module records two deliberately different reductions.  Finiteness of
every rank piece for every fixed target gives only targetwise finiteness of the
fiber components.  A uniform-in-target bound for the entire finite rank-piece
cover gives uniform fiber finiteness.  The second conclusion is not inferred
from the first one.

The missing geometric input is now local to the exact-rank pieces: a
constant-rank fiber lemma can be combined with the selected-minor charts in
`SmoothFamilyRankStratumLocalFiber` to study each such piece.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Connected components of a finite cover -/

/-- Send a connected component of one member of a cover to the connected
component of the ambient space containing it. -/
def connectedComponentsCoverMap
    {X ι : Type*} [TopologicalSpace X] (S : ι → Set X) :
    (Σ i, ConnectedComponents (S i)) → ConnectedComponents X
  | ⟨i, c⟩ =>
      Continuous.connectedComponentsMap
        (continuous_subtype_val : Continuous (Subtype.val : S i → X)) c

/-- If a family of sets covers the ambient space, its component-to-ambient
component map is surjective.  No local finiteness or disjointness of the cover
is needed. -/
theorem connectedComponentsCoverMap_surjective
    {X ι : Type*} [TopologicalSpace X] (S : ι → Set X)
    (hcover : ⋃ i, S i = Set.univ) :
    Function.Surjective (connectedComponentsCoverMap S) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hx : x ∈ ⋃ i, S i := by
    rw [hcover]
    exact Set.mem_univ x
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  refine ⟨⟨i, ConnectedComponents.mk ⟨x, hi⟩⟩, ?_⟩
  simpa only [connectedComponentsCoverMap] using
    (Continuous.connectedComponentsMap_mk
      (continuous_subtype_val : Continuous (Subtype.val : S i → X))
      ⟨x, hi⟩)

/-- A finite cover by sets with finitely many connected components gives
finitely many connected components in the ambient space. -/
theorem finite_connectedComponents_of_finite_iUnion_cover
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (S : ι → Set X) (hcover : ⋃ i, S i = Set.univ)
    (hfinite : ∀ i, Finite (ConnectedComponents (S i))) :
    Finite (ConnectedComponents X) := by
  let _ (i : ι) : Finite (ConnectedComponents (S i)) := hfinite i
  exact Finite.of_surjective (connectedComponentsCoverMap S)
    (connectedComponentsCoverMap_surjective S hcover)

/-- The extended-natural component count of a covered space is bounded by
the count of the dependent family of components of the covering sets. -/
theorem enatCard_connectedComponents_le_coverSigma
    {X ι : Type*} [TopologicalSpace X] (S : ι → Set X)
    (hcover : ⋃ i, S i = Set.univ) :
    ENat.card (ConnectedComponents X) ≤
      ENat.card (Σ i, ConnectedComponents (S i)) := by
  let hsurj := connectedComponentsCoverMap_surjective S hcover
  exact ENat.card_le_card_of_injective (Function.injective_surjInv hsurj)

/-! ## The exact-rank cover of one fiber -/

/-- The part of a fiber on which the derivative has exact rank `k`, viewed as
a subset of the fiber subtype. -/
def standardJacobianRankFiberPiece {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (t : RealEuclidean b)
    (k : ℕ) : Set (g ⁻¹' {t}) :=
  {x | (x : RealEuclidean a) ∈ standardJacobianRankLocus g k}

/-- The ranks `0, ..., a` cover the fiber.  We index by the source dimension;
this remains valid when the target dimension is smaller. -/
theorem iUnion_standardJacobianRankFiberPiece_eq_univ
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (t : RealEuclidean b) :
    ⋃ k : Fin (a + 1), standardJacobianRankFiberPiece g t k = Set.univ := by
  ext x
  simp only [standardJacobianRankFiberPiece,
    standardJacobianRankLocus, Set.mem_iUnion, Set.mem_ofPred_eq,
    Set.mem_univ, iff_true]
  let r := Module.finrank ℝ
    (LinearMap.range (fderiv ℝ g (x : RealEuclidean a)).toLinearMap)
  have hr : r ≤ a := by
    have hr' := LinearMap.finrank_range_le
      (fderiv ℝ g (x : RealEuclidean a)).toLinearMap
    simpa only [r, Module.finrank_fin_fun] using hr'
  exact ⟨⟨r, Nat.lt_succ_of_le hr⟩, rfl⟩

/-- For one fixed target, finiteness of the connected components of every
exact-rank piece implies finiteness of the connected components of the whole
fiber. -/
theorem finite_connectedComponents_fiber_of_finite_rank_pieces
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (t : RealEuclidean b)
    (hpieces : ∀ k : Fin (a + 1),
      Finite (ConnectedComponents
        (standardJacobianRankFiberPiece g t k))) :
    Finite (ConnectedComponents (g ⁻¹' {t})) := by
  apply finite_connectedComponents_of_finite_iUnion_cover
    (fun k : Fin (a + 1) => standardJacobianRankFiberPiece g t k)
  · exact iUnion_standardJacobianRankFiberPiece_eq_univ g t
  · exact hpieces

/-- Pointwise-in-target finiteness of all exact-rank fiber pieces.  This
property contains no common bound as the target varies. -/
def HasTargetwiseFiniteRankFiberPieces {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) : Prop :=
  ∀ t (k : Fin (a + 1)),
    Finite (ConnectedComponents (standardJacobianRankFiberPiece g t k))

/-- Targetwise rank-piece finiteness yields targetwise fiber-component
finiteness.  The quantifiers are intentionally `∀ t, Finite`; this theorem
does not produce one natural-number bound valid for every `t`. -/
theorem forall_target_finite_connectedComponents_fiber_of_targetwise_rank_pieces
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hpieces : HasTargetwiseFiniteRankFiberPieces g) :
    ∀ t, Finite (ConnectedComponents (g ⁻¹' {t})) := by
  intro t
  exact finite_connectedComponents_fiber_of_finite_rank_pieces g t
    (hpieces t)

/-! ## The genuinely uniform reduction -/

/-- A uniform-in-target bound for the dependent finite cover by exact-rank
components.  The bound is placed on the whole cover sigma type so no cardinal
addition formula is needed and no finiteness is hidden in `Nat.card`.

This property is strictly stronger data than
`HasTargetwiseFiniteRankFiberPieces`: a collection of finite types can have
unbounded cardinalities as the target varies. -/
def HasUniformRankFiberPieceCoverBound {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) : Prop :=
  ∃ N : ℕ, ∀ t,
    ENat.card
      (Σ k : Fin (a + 1),
        ConnectedComponents (standardJacobianRankFiberPiece g t k)) ≤ N

/-- A uniform bound for the exact-rank component cover gives a uniform bound
for the connected components of the whole fiber. -/
theorem exists_uniform_fiber_component_bound_of_uniform_rank_piece_cover_bound
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hpieces : HasUniformRankFiberPieceCoverBound g) :
    ∃ N : ℕ, ∀ t,
      ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ N := by
  obtain ⟨N, hN⟩ := hpieces
  refine ⟨N, fun t => ?_⟩
  exact (enatCard_connectedComponents_le_coverSigma
    (fun k : Fin (a + 1) => standardJacobianRankFiberPiece g t k)
    (iUnion_standardJacobianRankFiberPiece_eq_univ g t)).trans (hN t)

/-- Family-level targetwise exact-rank-piece finiteness.  It implies
pointwise fiber-component finiteness, but by itself does not imply
`HasUniformFiberFiniteness`. -/
def HasTargetwiseFiniteRankFiberPiecesForFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ a b (g : RealEuclidean a → RealEuclidean b),
    FunctionTupleInFamily G g → HasTargetwiseFiniteRankFiberPieces g

/-- The family-level conclusion available from targetwise rank-piece
finiteness. -/
theorem forall_target_finite_connectedComponents_fiber_of_family_rank_pieces
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hpieces : HasTargetwiseFiniteRankFiberPiecesForFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g) :
    ∀ t, Finite (ConnectedComponents (g ⁻¹' {t})) :=
  forall_target_finite_connectedComponents_fiber_of_targetwise_rank_pieces
    g (hpieces a b g hg)

/-- Family-level uniform exact-rank-cover bounds. -/
def HasUniformRankFiberPieceCoverBoundsForFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ a b (g : RealEuclidean a → RealEuclidean b),
    FunctionTupleInFamily G g → HasUniformRankFiberPieceCoverBound g

/-- The uniform rank-piece-cover property is sufficient for the manuscript's
uniform fiber-finiteness conclusion. -/
theorem HasUniformRankFiberPieceCoverBoundsForFamily.hasUniformFiberFiniteness
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hpieces : HasUniformRankFiberPieceCoverBoundsForFamily G) :
    HasUniformFiberFiniteness G := by
  intro a b g hg
  exact
    exists_uniform_fiber_component_bound_of_uniform_rank_piece_cover_bound
      g (hpieces a b g hg)

end AbelFormalization
