import AbelFormalization.CharbonnelClosedBoundaryCellAssembly

/-!
# Boundary compatibility for connected cells

Wilkie's full-dimensional cell step first replaces a closed set by an
empty-interior closed carrier containing its frontier.  The topological reason
this is enough is independent of the later fiber-cardinality construction: a
connected cell which misses the frontier lies entirely on one side of the
set.  This file records that argument and its finite-cover consequence.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A preconnected set which avoids the frontier of `A` lies in `A` or is
disjoint from `A`. -/
theorem IsPreconnected.subset_or_disjoint_of_disjoint_frontier
    {X : Type*} [TopologicalSpace X] {E A : Set X}
    (hE : IsPreconnected E) (hfrontier : Disjoint E (frontier A)) :
    E ⊆ A ∨ Disjoint E A := by
  have hcover : E ⊆ interior A ∪ interior Aᶜ := by
    rw [← compl_frontier_eq_union_interior]
    intro x hxE hxfrontier
    exact Set.disjoint_left.mp hfrontier hxE hxfrontier
  have hdisjoint : Disjoint (interior A) (interior Aᶜ) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxA hxAc
    exact (interior_subset hxAc) (interior_subset hxA)
  rcases hE.subset_or_subset isOpen_interior isOpen_interior
      hdisjoint hcover with hin | hout
  · exact Or.inl (hin.trans interior_subset)
  · exact Or.inr <| Set.disjoint_left.mpr fun x hxE hxA =>
      (interior_subset (hout hxE)) hxA

/-- If `A` is closed and `B` contains its frontier, connected cells compatible
with `A ∩ B` are already compatible with `A`.  This is the precise topological
reduction used in Wilkie's open-cell case after producing the empty-interior
boundary carrier. -/
theorem connected_cell_compatible_of_boundary_intersection
    {X : Type*} [TopologicalSpace X]
    {E A B : Set X} (hE : IsPreconnected E)
    (hAclosed : IsClosed A) (hfrontier : frontier A ⊆ B)
    (hcompat : E ⊆ A ∩ B ∨ Disjoint E (A ∩ B)) :
    E ⊆ A ∨ Disjoint E A := by
  rcases hcompat with hinside | houtside
  · exact Or.inl (hinside.trans inter_subset_left)
  · have hfrontierAB : frontier A ⊆ A ∩ B := fun x hx =>
      ⟨(hAclosed.frontier_subset hx), hfrontier hx⟩
    have hmisses : Disjoint E (frontier A) :=
      houtside.mono_right hfrontierAB
    exact IsPreconnected.subset_or_disjoint_of_disjoint_frontier hE hmisses

/-! ## Connectedness of the recursive cells -/

/-- The canonical scalar parametrization of `RealEuclidean 1`. -/
def realEuclideanSingletonVector (y : ℝ) : RealEuclidean 1 :=
  fun _ ↦ y

theorem continuous_realEuclideanSingletonVector :
    Continuous realEuclideanSingletonVector := by
  rw [continuous_pi_iff]
  intro i
  change Continuous fun y : ℝ ↦ y
  fun_prop

theorem realEuclideanSingletonVector_image_eq_unaryLift (s : Set ℝ) :
    realEuclideanSingletonVector '' s = realEuclideanUnaryLift s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [realEuclideanUnaryLift, realEuclideanSingletonVector] using hy
  · intro hx
    refine ⟨x 0, ?_, ?_⟩
    · simpa [realEuclideanUnaryLift] using hx
    · funext i
      rw [Fin.eq_zero i]
      rfl

theorem unaryPiece_isPreconnected (piece : UnaryPiece) :
    IsPreconnected (realEuclideanUnaryPiece piece) := by
  have hscalar : IsPreconnected piece.carrier := by
    cases piece with
    | point a => simpa [UnaryPiece.carrier] using isPreconnected_singleton (x := a)
    | bounded a b => simpa [UnaryPiece.carrier] using isPreconnected_Ioo (a := a) (b := b)
    | leftRay b => simpa [UnaryPiece.carrier] using isPreconnected_Iio (a := b)
    | rightRay a => simpa [UnaryPiece.carrier] using isPreconnected_Ioi (a := a)
    | whole =>
        simpa [UnaryPiece.carrier] using
          (isPreconnected_univ : IsPreconnected (Set.univ : Set ℝ))
  rw [realEuclideanUnaryPiece, ← realEuclideanSingletonVector_image_eq_unaryLift]
  exact hscalar.image realEuclideanSingletonVector
    continuous_realEuclideanSingletonVector.continuousOn

/-- Parametrization of a restricted graph. -/
def charbonnelGraphParam {n : ℕ} (f : RealEuclidean n → ℝ)
    (x : RealEuclidean n) : RealEuclidean (n + 1) :=
  realEuclideanAppend x (realEuclideanSingletonVector (f x))

theorem continuousOn_charbonnelGraphParam {n : ℕ}
    {base : Set (RealEuclidean n)} {f : RealEuclidean n → ℝ}
    (hf : ContinuousOn f base) :
    ContinuousOn (charbonnelGraphParam f) base := by
  rw [continuousOn_pi]
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa [charbonnelGraphParam, realEuclideanAppend] using
      (continuous_apply j).continuousOn
  · simpa [charbonnelGraphParam, realEuclideanAppend,
      realEuclideanSingletonVector] using hf

theorem charbonnelGraphParam_image_eq {n : ℕ}
    (base : Set (RealEuclidean n)) (f : RealEuclidean n → ℝ) :
    charbonnelGraphParam f '' base = charbonnelRestrictedGraph base f := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp [charbonnelRestrictedGraph, charbonnelGraphParam,
      realEuclideanSingletonVector, hx]
  · rintro ⟨hx, hvalue⟩
    refine ⟨realEuclideanTakeLeft z, hx, ?_⟩
    have hright :
        realEuclideanSingletonVector (f (realEuclideanTakeLeft z)) =
          realEuclideanTakeRight z := by
      funext j
      rw [Fin.eq_zero j]
      simpa [realEuclideanSingletonVector] using hvalue.symm
    rw [charbonnelGraphParam, hright]
    exact realEuclideanAppend_takeLeft_takeRight z

theorem isPreconnected_charbonnelRestrictedGraph {n : ℕ}
    {base : Set (RealEuclidean n)} (hbase : IsPreconnected base)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base) :
    IsPreconnected (charbonnelRestrictedGraph base f) := by
  rw [← charbonnelGraphParam_image_eq]
  exact hbase.image (charbonnelGraphParam f)
    (continuousOn_charbonnelGraphParam hf)

/-- Flatten a base point and one scalar coordinate. -/
def charbonnelScalarAppend {n : ℕ}
    (p : RealEuclidean n × ℝ) : RealEuclidean (n + 1) :=
  realEuclideanAppend p.1 (realEuclideanSingletonVector p.2)

theorem continuous_charbonnelScalarAppend {n : ℕ} :
    Continuous (charbonnelScalarAppend (n := n)) := by
  rw [continuous_pi_iff]
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp only [charbonnelScalarAppend, realEuclideanAppend_castAdd]
    fun_prop
  · simpa [charbonnelScalarAppend, realEuclideanAppend,
      realEuclideanSingletonVector] using continuous_snd

/-- Linear interpolation between two graph functions. -/
def charbonnelBandParam {n : ℕ}
    (f g : RealEuclidean n → ℝ) (p : RealEuclidean n × ℝ) :
    RealEuclidean (n + 1) :=
  charbonnelScalarAppend
    (p.1, (1 - p.2) * f p.1 + p.2 * g p.1)

theorem continuousOn_charbonnelBandParam {n : ℕ}
    {base : Set (RealEuclidean n)} {f g : RealEuclidean n → ℝ}
    (hf : ContinuousOn f base) (hg : ContinuousOn g base) :
    ContinuousOn (charbonnelBandParam f g) (base ×ˢ Set.Ioo (0 : ℝ) 1) := by
  let domain := base ×ˢ Set.Ioo (0 : ℝ) 1
  have hfst : ContinuousOn (fun p : RealEuclidean n × ℝ ↦ p.1) domain :=
    continuous_fst.continuousOn
  have hfstMaps : Set.MapsTo (fun p : RealEuclidean n × ℝ ↦ p.1)
      domain base := fun _ hp ↦ hp.1
  have hf' : ContinuousOn (fun p : RealEuclidean n × ℝ ↦ f p.1) domain :=
    hf.comp hfst hfstMaps
  have hg' : ContinuousOn (fun p : RealEuclidean n × ℝ ↦ g p.1) domain :=
    hg.comp hfst hfstMaps
  have ht : ContinuousOn (fun p : RealEuclidean n × ℝ ↦ p.2) domain :=
    continuous_snd.continuousOn
  have hvalue : ContinuousOn
      (fun p : RealEuclidean n × ℝ ↦
        (1 - p.2) * f p.1 + p.2 * g p.1) domain :=
    (continuousOn_const.sub ht).mul hf' |>.add (ht.mul hg')
  exact continuous_charbonnelScalarAppend.continuousOn.comp
    (hfst.prodMk hvalue) (fun _ _ ↦ Set.mem_univ _)

theorem charbonnelBandParam_image_eq {n : ℕ}
    (base : Set (RealEuclidean n)) (f g : RealEuclidean n → ℝ)
    (hfg : ∀ x ∈ base, f x < g x) :
    charbonnelBandParam f g '' (base ×ˢ Set.Ioo (0 : ℝ) 1) =
      charbonnelOpenBand base f g := by
  ext z
  constructor
  · rintro ⟨⟨x, t⟩, ⟨hx, ht0, ht1⟩, rfl⟩
    have hlt := hfg x hx
    simp only [charbonnelOpenBand, charbonnelBandParam,
      charbonnelScalarAppend, mem_ofPred_eq,
      realEuclideanTakeLeft_append, realEuclideanTakeRight_append]
    constructor
    · exact hx
    constructor <;>
      simp only [realEuclideanSingletonVector] <;> nlinarith
  · rintro ⟨hx, hfy, hyg⟩
    let x := realEuclideanTakeLeft z
    let y := realEuclideanTakeRight z 0
    let d := g x - f x
    let t := (y - f x) / d
    have hd : 0 < d := sub_pos.mpr (hfg x hx)
    have ht0 : 0 < t := div_pos (sub_pos.mpr hfy) hd
    have ht1 : t < 1 := by
      apply (div_lt_one hd).2
      linarith
    have htmul : t * d = y - f x := by
      exact div_mul_cancel₀ _ hd.ne'
    have hvalue : (1 - t) * f x + t * g x = y := by
      dsimp only [d] at htmul
      nlinarith
    refine ⟨(x, t), ⟨hx, ht0, ht1⟩, ?_⟩
    have hright :
        realEuclideanSingletonVector
            ((1 - t) * f x + t * g x) = realEuclideanTakeRight z := by
      funext j
      rw [Fin.eq_zero j]
      simpa [realEuclideanSingletonVector, y] using hvalue
    rw [charbonnelBandParam, charbonnelScalarAppend, hright]
    exact realEuclideanAppend_takeLeft_takeRight z

theorem isPreconnected_charbonnelOpenBand {n : ℕ}
    {base : Set (RealEuclidean n)} (hbase : IsPreconnected base)
    (f g : RealEuclidean n → ℝ)
    (hf : ContinuousOn f base) (hg : ContinuousOn g base)
    (hfg : ∀ x ∈ base, f x < g x) :
    IsPreconnected (charbonnelOpenBand base f g) := by
  rw [← charbonnelBandParam_image_eq base f g hfg]
  exact (hbase.prod isPreconnected_Ioo).image (charbonnelBandParam f g)
    (continuousOn_charbonnelBandParam hf hg)

/-- Positive-distance parametrization of the lower ray below a graph. -/
def charbonnelLowerRayParam {n : ℕ}
    (g : RealEuclidean n → ℝ) (p : RealEuclidean n × ℝ) :
    RealEuclidean (n + 1) :=
  charbonnelScalarAppend (p.1, g p.1 - p.2)

theorem continuousOn_charbonnelLowerRayParam {n : ℕ}
    {base : Set (RealEuclidean n)} {g : RealEuclidean n → ℝ}
    (hg : ContinuousOn g base) :
    ContinuousOn (charbonnelLowerRayParam g)
      (base ×ˢ Set.Ioi (0 : ℝ)) := by
  let domain := base ×ˢ Set.Ioi (0 : ℝ)
  have hg' : ContinuousOn (fun p : RealEuclidean n × ℝ ↦ g p.1) domain :=
    hg.comp continuous_fst.continuousOn (fun _ hp ↦ hp.1)
  have hvalue : ContinuousOn
      (fun p : RealEuclidean n × ℝ ↦ g p.1 - p.2) domain :=
    hg'.sub continuous_snd.continuousOn
  exact continuous_charbonnelScalarAppend.continuousOn.comp
    (continuous_fst.continuousOn.prodMk hvalue) (fun _ _ ↦ Set.mem_univ _)

theorem charbonnelLowerRayParam_image_eq {n : ℕ}
    (base : Set (RealEuclidean n)) (g : RealEuclidean n → ℝ) :
    charbonnelLowerRayParam g '' (base ×ˢ Set.Ioi (0 : ℝ)) =
      charbonnelLowerRayCell base g := by
  ext z
  constructor
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    simpa [charbonnelLowerRayCell, charbonnelLowerRayParam,
      charbonnelScalarAppend, realEuclideanSingletonVector, hx] using ht
  · rintro ⟨hx, hy⟩
    let x := realEuclideanTakeLeft z
    let y := realEuclideanTakeRight z 0
    let t := g x - y
    have ht : 0 < t := sub_pos.mpr hy
    refine ⟨(x, t), ⟨hx, ht⟩, ?_⟩
    have hright : realEuclideanSingletonVector (g x - t) =
        realEuclideanTakeRight z := by
      funext j
      rw [Fin.eq_zero j]
      simp [realEuclideanSingletonVector, t, y]
    rw [charbonnelLowerRayParam, charbonnelScalarAppend, hright]
    exact realEuclideanAppend_takeLeft_takeRight z

theorem isPreconnected_charbonnelLowerRayCell {n : ℕ}
    {base : Set (RealEuclidean n)} (hbase : IsPreconnected base)
    (g : RealEuclidean n → ℝ) (hg : ContinuousOn g base) :
    IsPreconnected (charbonnelLowerRayCell base g) := by
  rw [← charbonnelLowerRayParam_image_eq]
  exact (hbase.prod isPreconnected_Ioi).image (charbonnelLowerRayParam g)
    (continuousOn_charbonnelLowerRayParam hg)

/-- Positive-distance parametrization of the upper ray above a graph. -/
def charbonnelUpperRayParam {n : ℕ}
    (f : RealEuclidean n → ℝ) (p : RealEuclidean n × ℝ) :
    RealEuclidean (n + 1) :=
  charbonnelScalarAppend (p.1, f p.1 + p.2)

theorem continuousOn_charbonnelUpperRayParam {n : ℕ}
    {base : Set (RealEuclidean n)} {f : RealEuclidean n → ℝ}
    (hf : ContinuousOn f base) :
    ContinuousOn (charbonnelUpperRayParam f)
      (base ×ˢ Set.Ioi (0 : ℝ)) := by
  let domain := base ×ˢ Set.Ioi (0 : ℝ)
  have hf' : ContinuousOn (fun p : RealEuclidean n × ℝ ↦ f p.1) domain :=
    hf.comp continuous_fst.continuousOn (fun _ hp ↦ hp.1)
  have hvalue : ContinuousOn
      (fun p : RealEuclidean n × ℝ ↦ f p.1 + p.2) domain :=
    hf'.add continuous_snd.continuousOn
  exact continuous_charbonnelScalarAppend.continuousOn.comp
    (continuous_fst.continuousOn.prodMk hvalue) (fun _ _ ↦ Set.mem_univ _)

theorem charbonnelUpperRayParam_image_eq {n : ℕ}
    (base : Set (RealEuclidean n)) (f : RealEuclidean n → ℝ) :
    charbonnelUpperRayParam f '' (base ×ˢ Set.Ioi (0 : ℝ)) =
      charbonnelUpperRayCell base f := by
  ext z
  constructor
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    simpa [charbonnelUpperRayCell, charbonnelUpperRayParam,
      charbonnelScalarAppend, realEuclideanSingletonVector, hx] using ht
  · rintro ⟨hx, hy⟩
    let x := realEuclideanTakeLeft z
    let y := realEuclideanTakeRight z 0
    let t := y - f x
    have ht : 0 < t := sub_pos.mpr hy
    refine ⟨(x, t), ⟨hx, ht⟩, ?_⟩
    have hright : realEuclideanSingletonVector (f x + t) =
        realEuclideanTakeRight z := by
      funext j
      rw [Fin.eq_zero j]
      simp [realEuclideanSingletonVector, t, y]
    rw [charbonnelUpperRayParam, charbonnelScalarAppend, hright]
    exact realEuclideanAppend_takeLeft_takeRight z

theorem isPreconnected_charbonnelUpperRayCell {n : ℕ}
    {base : Set (RealEuclidean n)} (hbase : IsPreconnected base)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base) :
    IsPreconnected (charbonnelUpperRayCell base f) := by
  rw [← charbonnelUpperRayParam_image_eq]
  exact (hbase.prod isPreconnected_Ioi).image (charbonnelUpperRayParam f)
    (continuousOn_charbonnelUpperRayParam hf)

theorem charbonnelScalarAppend_image_product_eq_cylinder {n : ℕ}
    (base : Set (RealEuclidean n)) :
    charbonnelScalarAppend '' (base ×ˢ (Set.univ : Set ℝ)) =
      charbonnelCylinderCell base := by
  ext z
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, _⟩, rfl⟩
    simpa [charbonnelCylinderCell, charbonnelScalarAppend] using hx
  · intro hz
    let x := realEuclideanTakeLeft z
    let y := realEuclideanTakeRight z 0
    refine ⟨(x, y), ⟨hz, Set.mem_univ _⟩, ?_⟩
    have hright : realEuclideanSingletonVector y = realEuclideanTakeRight z := by
      funext j
      rw [Fin.eq_zero j]
      rfl
    rw [charbonnelScalarAppend, hright]
    exact realEuclideanAppend_takeLeft_takeRight z

theorem isPreconnected_charbonnelCylinderCell {n : ℕ}
    {base : Set (RealEuclidean n)} (hbase : IsPreconnected base) :
    IsPreconnected (charbonnelCylinderCell base) := by
  rw [← charbonnelScalarAppend_image_product_eq_cylinder]
  exact (hbase.prod isPreconnected_univ).image charbonnelScalarAppend
    continuous_charbonnelScalarAppend.continuousOn

/-- Every recursive Charbonnel cell shape is preconnected. -/
theorem CharbonnelCellShape.isPreconnected
    {n : ℕ} {carrier : Set (RealEuclidean n)}
    (shape : CharbonnelCellShape n carrier) : IsPreconnected carrier := by
  induction shape with
  | unary piece => exact unaryPiece_isPreconnected piece
  | graph _ _ f hf ih =>
      exact isPreconnected_charbonnelRestrictedGraph ih f hf
  | band _ _ f g hf hg hfg ih =>
      exact isPreconnected_charbonnelOpenBand ih f g hf hg hfg
  | lowerRay _ _ g hg ih =>
      exact isPreconnected_charbonnelLowerRayCell ih g hg
  | upperRay _ _ f hf ih =>
      exact isPreconnected_charbonnelUpperRayCell ih f hf
  | cylinder _ _ ih =>
      exact isPreconnected_charbonnelCylinderCell ih

namespace CharbonnelFiniteCompatibleCellCover

/-- Reuse a finite connected-cell cover compatible with the intersection of a
closed set and one of its boundary carriers as a cover compatible with the
closed set itself.  No family operation is used: the cells and all membership
certificates are retained verbatim. -/
noncomputable def of_boundaryIntersection
    {C : EuclideanSetFamily} {n : ℕ}
    {A B : Set (RealEuclidean n)}
    (hAclosed : IsClosed A) (hfrontier : frontier A ⊆ B)
    (cover : CharbonnelFiniteCompatibleCellCover C (A ∩ B))
    (hconnected : ∀ i, IsPreconnected (cover.cell i).carrier) :
    CharbonnelFiniteCompatibleCellCover C A where
  count := cover.count
  cell := cover.cell
  covers := cover.covers
  compatible i :=
    connected_cell_compatible_of_boundary_intersection
      (hconnected i) hAclosed hfrontier (cover.compatible i)

/-- Boundary-intersection transfer specialized to recursive Charbonnel cells.
Their connectedness is automatic from `CharbonnelCellShape`. -/
noncomputable def of_boundaryIntersection_auto
    {C : EuclideanSetFamily} {n : ℕ}
    {A B : Set (RealEuclidean n)}
    (hAclosed : IsClosed A) (hfrontier : frontier A ⊆ B)
    (cover : CharbonnelFiniteCompatibleCellCover C (A ∩ B)) :
    CharbonnelFiniteCompatibleCellCover C A :=
  of_boundaryIntersection hAclosed hfrontier cover
    (fun i ↦ (cover.cell i).shape.isPreconnected)

end CharbonnelFiniteCompatibleCellCover

end AbelFormalization
