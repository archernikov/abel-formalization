import AbelFormalization.WilkieSection4DeepArbitraryGraphInsertion

/-!
# Presenting a bounded non-open deep cell by deleting its first singular coordinate

A nonempty bounded deep cell which is not open has a first singular coordinate.
It is either a graph over a positive-dimensional deep base, or a unary point.
This file deletes that coordinate while retaining all later band layers and records
the exact carrier and projection identities used by the lower-dimensional
induction in Wilkie's Section 4 argument.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

open CharbonnelDeepEnrichedCell

/-- Data obtained by deleting the first singular coordinate of a bounded,
non-open deep cell of dimension at least two. -/
inductive CharbonnelDeepNonOpenPresentation
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S)) :
    {d : ℕ} → CharbonnelDeepEnrichedCell S d → Type 1
  | graph {n q : ℕ} (hn : 0 < n)
      (D : CharbonnelDeepEnrichedCell S ((n + 1) + q))
      (base : CharbonnelDeepEnrichedCell S n)
      (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
      (hgraph : charbonnelRestrictedGraph base.carrier f ∈
        charbonnelClosure S (n + 1))
      (deleted : CharbonnelDeepEnrichedCell S (n + q))
      (hroot : (deleted.projectedBaseN hn q).carrier ⊆ base.carrier)
      (carrier_eq : D.carrier =
        (insertGraphAtDepth hC hn base f hf hgraph q deleted hroot).carrier)
      (projection_image :
        charbonnelBuriedGraphProjectionLinearMap n q '' D.carrier =
          deleted.carrier)
      (deleted_isBounded : Bornology.IsBounded deleted.carrier) :
      CharbonnelDeepNonOpenPresentation hC D
  | point {q : ℕ}
      (D : CharbonnelDeepEnrichedCell S ((1 + q) + 1))
      (a : ℝ)
      (deleted : CharbonnelDeepEnrichedCell S (q + 1))
      (carrier_eq : D.carrier =
        (insertUnaryPointAtDepth hC a q deleted).carrier)
      (projection_image :
        charbonnelUnaryPointProjectionLinearMap (q + 1) '' D.carrier =
          deleted.carrier)
      (deleted_isBounded : Bornology.IsBounded deleted.carrier) :
      CharbonnelDeepNonOpenPresentation hC D

/-! The implementation first allows the bare one-dimensional point.  One
further band layer turns this private root case into the public `point`
presentation above. -/

private inductive CharbonnelDeepSingularRootPresentation
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S)) :
    {d : ℕ} → CharbonnelDeepEnrichedCell S d → Type 1
  | unaryPoint (D : CharbonnelDeepEnrichedCell S 1) (a : ℝ)
      (carrier_eq : D.carrier = realEuclideanUnaryPiece (.point a))
      (cell_isBounded : Bornology.IsBounded D.carrier) :
      CharbonnelDeepSingularRootPresentation hC D
  | transport {d : ℕ} (D : CharbonnelDeepEnrichedCell S d)
      (presentation : CharbonnelDeepNonOpenPresentation hC D) :
      CharbonnelDeepSingularRootPresentation hC D

/-- Restricting a projection to a common constraint and then reinserting is
an exact inverse-image identity. -/
private theorem inter_preimage_image_eq_of_subset_of_injOn
    {α β : Type*} {P : α → β} {constraint A : Set α}
    (hA : A ⊆ constraint) (hinj : Set.InjOn P constraint) :
    constraint ∩ P ⁻¹' (P '' A) = A := by
  ext x
  constructor
  · rintro ⟨hxConstraint, y, hyA, hyx⟩
    have hxy : x = y := hinj hxConstraint (hA hyA) hyx.symm
    simpa [hxy] using hyA
  · intro hxA
    exact ⟨hA hxA, ⟨x, hxA, rfl⟩⟩

/-- An open base and continuous strict boundaries give an open band. -/
theorem isOpen_charbonnelOpenBand_of_isOpen
    {n : ℕ} {base : Set (RealEuclidean n)}
    {f g : RealEuclidean n → ℝ}
    (hbase : IsOpen base) (hf : ContinuousOn f base)
    (hg : ContinuousOn g base) :
    IsOpen (charbonnelOpenBand base f g) := by
  let B : Set (RealEuclidean (n + 1)) := charbonnelCylinderCell base
  have hB : IsOpen B := by
    exact hbase.preimage
      (realEuclideanTakeLeftContinuousLinearMap n 1).continuous
  have hleft : ContinuousOn (fun z : RealEuclidean (n + 1) ↦
      f (realEuclideanTakeLeft z)) B := by
    exact hf.comp
      (realEuclideanTakeLeftContinuousLinearMap n 1).continuous.continuousOn
      (by intro z hz; exact hz)
  have hright : ContinuousOn (fun z : RealEuclidean (n + 1) ↦
      g (realEuclideanTakeLeft z)) B := by
    exact hg.comp
      (realEuclideanTakeLeftContinuousLinearMap n 1).continuous.continuousOn
      (by intro z hz; exact hz)
  have hlast : Continuous (fun z : RealEuclidean (n + 1) ↦
      realEuclideanTakeRight z 0) := by
    exact (continuous_apply (0 : Fin 1)).comp
      (realEuclideanTakeRightLinearMap n 1).toContinuousLinearMap.continuous
  have hlow : IsOpen (B ∩ {z | f (realEuclideanTakeLeft z) <
      realEuclideanTakeRight z 0}) := by
    exact (hleft.prodMk hlast.continuousOn).isOpen_inter_preimage
      hB isOpen_lt_prod
  have hopen := ContinuousOn.isOpen_inter_preimage
    (hlast.continuousOn.prodMk (hright.mono inter_subset_left))
    hlow isOpen_lt_prod
  convert hopen using 1 <;>
    ext z <;>
    simp [B, charbonnelOpenBand, charbonnelCylinderCell, and_assoc]

/-- A bounded lower ray has empty base. -/
private theorem lowerRay_base_eq_empty_of_isBounded
    {n : ℕ} {base : Set (RealEuclidean n)}
    (g : RealEuclidean n → ℝ)
    (hbounded : Bornology.IsBounded (charbonnelLowerRayCell base g)) :
    base = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hbounded
  let u : RealEuclidean 1 := fun _ ↦ g x - 1
  let v : RealEuclidean 1 := fun _ ↦ g x - (|C| + 2)
  let z := realEuclideanAppend x u
  let w := realEuclideanAppend x v
  have hpos : 0 < |C| + 2 := by linarith [abs_nonneg C]
  have hz : z ∈ charbonnelLowerRayCell base g := by
    simp [charbonnelLowerRayCell, z, u, hx]
  have hw : w ∈ charbonnelLowerRayCell base g := by
    simp [charbonnelLowerRayCell, w, v, hx, hpos]
  have hcoord : dist (z (Fin.last n)) (w (Fin.last n)) ≤ dist z w :=
    (dist_pi_le_iff dist_nonneg).mp le_rfl (Fin.last n)
  have hzw : dist z w ≤ C := hC hz hw
  have hlast : Fin.last n = Fin.natAdd n (0 : Fin 1) := by
    apply Fin.ext
    rfl
  have hlarge : C < dist (z (Fin.last n)) (w (Fin.last n)) := by
    rw [hlast]
    simp only [z, w, realEuclideanAppend_natAdd, u, v, Real.dist_eq]
    rw [show g x - 1 - (g x - (|C| + 2)) = |C| + 1 by ring]
    rw [abs_of_nonneg (by positivity : 0 ≤ |C| + 1)]
    linarith [le_abs_self C]
  linarith

/-- A bounded upper ray has empty base. -/
private theorem upperRay_base_eq_empty_of_isBounded
    {n : ℕ} {base : Set (RealEuclidean n)}
    (f : RealEuclidean n → ℝ)
    (hbounded : Bornology.IsBounded (charbonnelUpperRayCell base f)) :
    base = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hbounded
  let u : RealEuclidean 1 := fun _ ↦ f x + 1
  let v : RealEuclidean 1 := fun _ ↦ f x + (|C| + 2)
  let z := realEuclideanAppend x u
  let w := realEuclideanAppend x v
  have hpos : 0 < |C| + 2 := by linarith [abs_nonneg C]
  have hz : z ∈ charbonnelUpperRayCell base f := by
    simp [charbonnelUpperRayCell, z, u, hx]
  have hw : w ∈ charbonnelUpperRayCell base f := by
    simp [charbonnelUpperRayCell, w, v, hx, hpos]
  have hcoord : dist (z (Fin.last n)) (w (Fin.last n)) ≤ dist z w :=
    (dist_pi_le_iff dist_nonneg).mp le_rfl (Fin.last n)
  have hzw : dist z w ≤ C := hC hz hw
  have hlast : Fin.last n = Fin.natAdd n (0 : Fin 1) := by
    apply Fin.ext
    rfl
  have hlarge : C < dist (z (Fin.last n)) (w (Fin.last n)) := by
    rw [hlast]
    simp only [z, w, realEuclideanAppend_natAdd, u, v, Real.dist_eq]
    rw [show f x + 1 - (f x + (|C| + 2)) = -(|C| + 1) by ring]
    rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ |C| + 1)]
    linarith [le_abs_self C]
  linarith

/-- A bounded full cylinder has empty base. -/
private theorem cylinder_base_eq_empty_of_isBounded
    {n : ℕ} {base : Set (RealEuclidean n)}
    (hbounded : Bornology.IsBounded (charbonnelCylinderCell base)) :
    base = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hbounded
  let u : RealEuclidean 1 := fun _ ↦ 0
  let v : RealEuclidean 1 := fun _ ↦ |C| + 1
  let z := realEuclideanAppend x u
  let w := realEuclideanAppend x v
  have hz : z ∈ charbonnelCylinderCell base := by
    simpa [charbonnelCylinderCell, z] using hx
  have hw : w ∈ charbonnelCylinderCell base := by
    simpa [charbonnelCylinderCell, w] using hx
  have hcoord : dist (z (Fin.last n)) (w (Fin.last n)) ≤ dist z w :=
    (dist_pi_le_iff dist_nonneg).mp le_rfl (Fin.last n)
  have hzw : dist z w ≤ C := hC hz hw
  have hlast : Fin.last n = Fin.natAdd n (0 : Fin 1) := by
    apply Fin.ext
    rfl
  have hlarge : C < dist (z (Fin.last n)) (w (Fin.last n)) := by
    rw [hlast]
    simp only [z, w, realEuclideanAppend_natAdd, u, v, Real.dist_eq,
      zero_sub, abs_neg]
    rw [abs_of_nonneg (by positivity : 0 ≤ |C| + 1)]
    linarith [le_abs_self C]
  linarith

/-! ## Projecting one trailing band -/

/-- The coordinatewise extension of a section of a base projection is
continuous on the corresponding cylinder. -/
private theorem continuousOn_append_section_last
    {a b : ℕ} {small : Set (RealEuclidean b)}
    {I : RealEuclidean b → RealEuclidean a}
    (hI : ContinuousOn I small) :
    ContinuousOn
      (fun z : RealEuclidean (b + 1) ↦
        realEuclideanAppend (I (realEuclideanTakeLeft z))
          (realEuclideanTakeRight z))
      (charbonnelCylinderCell small) := by
  have hleft : ContinuousOn
      (fun z : RealEuclidean (b + 1) ↦ I (realEuclideanTakeLeft z))
      (charbonnelCylinderCell small) := by
    exact hI.comp
      (realEuclideanTakeLeftContinuousLinearMap b 1).continuous.continuousOn
      (by intro z hz; exact hz)
  rw [continuousOn_pi]
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · rw [show
        (fun y : RealEuclidean (b + 1) ↦
          realEuclideanAppend (I (realEuclideanTakeLeft y))
            (realEuclideanTakeRight y) (Fin.castAdd 1 j)) =
        ((fun p : RealEuclidean a ↦ p j) ∘
          (fun z : RealEuclidean (b + 1) ↦ I (realEuclideanTakeLeft z))) by
          funext z
          simp]
    exact (((continuous_apply j).continuousOn :
      ContinuousOn (fun x : RealEuclidean a ↦ x j) Set.univ).comp
        hleft (Set.mapsTo_univ _ _))
  · rw [show
        (fun y : RealEuclidean (b + 1) ↦
          realEuclideanAppend (I (realEuclideanTakeLeft y))
            (realEuclideanTakeRight y) (Fin.natAdd a j)) =
        ((fun p : RealEuclidean 1 ↦ p j) ∘
          (realEuclideanTakeRightLinearMap b 1)) by
          funext z
          simp]
    exact ((continuous_apply j).comp
      (realEuclideanTakeRightLinearMap b 1).toContinuousLinearMap.continuous).continuousOn

/-- Projecting a boundary graph through a base projection with a continuous
section produces the boundary graph obtained by composing with that section. -/
private theorem extendLinearMap_image_restrictedGraph
    {a b : ℕ} (P : RealEuclidean a →ₗ[ℝ] RealEuclidean b)
    (I : RealEuclidean b → RealEuclidean a)
    {constraint : Set (RealEuclidean a)}
    {large : Set (RealEuclidean a)} {small : Set (RealEuclidean b)}
    (hlarge : large = constraint ∩ P ⁻¹' small)
    (hPI : ∀ y, P (I y) = y)
    (hIC : Set.MapsTo I small constraint)
    (hIP : ∀ x ∈ constraint, I (P x) = x)
    (f : RealEuclidean a → ℝ) :
    charbonnelExtendLinearMapLast P '' charbonnelRestrictedGraph large f =
      charbonnelRestrictedGraph small (fun y ↦ f (I y)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    let x : RealEuclidean a := realEuclideanTakeLeft z
    let u : RealEuclidean 1 := realEuclideanTakeRight z
    have hzdecomp : z = realEuclideanAppend x u :=
      (realEuclideanAppend_takeLeft_takeRight z).symm
    have hxLarge : x ∈ large := hz.1
    have hxConstraint : x ∈ constraint := by
      rw [hlarge] at hxLarge
      exact hxLarge.1
    have hxSmall : P x ∈ small := by
      rw [hlarge] at hxLarge
      exact hxLarge.2
    rw [hzdecomp]
    simp only [charbonnelExtendLinearMapLast_append,
      charbonnelRestrictedGraph, Set.mem_ofPred_eq,
      realEuclideanTakeLeft_append, realEuclideanTakeRight_append]
    exact ⟨hxSmall, by simpa [hIP x hxConstraint] using hz.2⟩
  · intro hy
    let v : RealEuclidean b := realEuclideanTakeLeft y
    let u : RealEuclidean 1 := realEuclideanTakeRight y
    have hydecomp : y = realEuclideanAppend v u :=
      (realEuclideanAppend_takeLeft_takeRight y).symm
    have hvSmall : v ∈ small := hy.1
    let z : RealEuclidean (a + 1) := realEuclideanAppend (I v) u
    have hzLarge : I v ∈ large := by
      rw [hlarge]
      exact ⟨hIC hvSmall, by simpa [hPI v] using hvSmall⟩
    refine ⟨z, ?_, ?_⟩
    · simpa [z, charbonnelRestrictedGraph] using
        (And.intro hzLarge (by simpa [hydecomp] using hy.2))
    · simp [z, hPI v, hydecomp]

/-- The same base projection sends an open band exactly to the band whose
boundary functions are composed with the section. -/
private theorem extendLinearMap_image_openBand
    {a b : ℕ} (P : RealEuclidean a →ₗ[ℝ] RealEuclidean b)
    (I : RealEuclidean b → RealEuclidean a)
    {constraint : Set (RealEuclidean a)}
    {large : Set (RealEuclidean a)} {small : Set (RealEuclidean b)}
    (hlarge : large = constraint ∩ P ⁻¹' small)
    (hPI : ∀ y, P (I y) = y)
    (hIC : Set.MapsTo I small constraint)
    (hIP : ∀ x ∈ constraint, I (P x) = x)
    (f g : RealEuclidean a → ℝ) :
    charbonnelExtendLinearMapLast P '' charbonnelOpenBand large f g =
      charbonnelOpenBand small (fun y ↦ f (I y)) (fun y ↦ g (I y)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    let x : RealEuclidean a := realEuclideanTakeLeft z
    let u : RealEuclidean 1 := realEuclideanTakeRight z
    have hzdecomp : z = realEuclideanAppend x u :=
      (realEuclideanAppend_takeLeft_takeRight z).symm
    have hxLarge : x ∈ large := hz.1
    have hxConstraint : x ∈ constraint := by
      rw [hlarge] at hxLarge
      exact hxLarge.1
    have hxSmall : P x ∈ small := by
      rw [hlarge] at hxLarge
      exact hxLarge.2
    rw [hzdecomp]
    simp only [charbonnelExtendLinearMapLast_append,
      charbonnelOpenBand, Set.mem_ofPred_eq,
      realEuclideanTakeLeft_append, realEuclideanTakeRight_append]
    exact ⟨hxSmall, by simpa [hIP x hxConstraint] using hz.2⟩
  · intro hy
    let v : RealEuclidean b := realEuclideanTakeLeft y
    let u : RealEuclidean 1 := realEuclideanTakeRight y
    have hydecomp : y = realEuclideanAppend v u :=
      (realEuclideanAppend_takeLeft_takeRight y).symm
    have hvSmall : v ∈ small := hy.1
    let z : RealEuclidean (a + 1) := realEuclideanAppend (I v) u
    have hzLarge : I v ∈ large := by
      rw [hlarge]
      exact ⟨hIC hvSmall, by simpa [hPI v] using hvSmall⟩
    refine ⟨z, ?_, ?_⟩
    · simpa [z, charbonnelOpenBand] using
        (And.intro hzLarge (by simpa [hydecomp] using hy.2))
    · simp [z, hPI v, hydecomp]

/-- Insertion of a buried graph is continuous on a source whose retained
root lies in the graph base. -/
private theorem continuousOn_charbonnelBuriedGraphInsertion
    {S : EuclideanSetFamily} {n q : ℕ} (hn : 0 < n)
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (source : CharbonnelDeepEnrichedCell S (n + q))
    (hroot : (source.projectedBaseN hn q).carrier ⊆ base.carrier) :
    ContinuousOn (charbonnelBuriedGraphInsertion f) source.carrier := by
  rw [continuousOn_pi]
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
    · have hc : ContinuousOn
          ((fun p : RealEuclidean n ↦ p k) ∘
            (realEuclideanTakeLeftContinuousLinearMap n q)) source.carrier :=
        ((continuous_apply k).comp
          (realEuclideanTakeLeftContinuousLinearMap n q).continuous).continuousOn
      convert hc using 1
      funext z
      simp [charbonnelBuriedGraphInsertion]
    · fin_cases k
      have htake : Set.MapsTo
          (realEuclideanTakeLeftLinearMap n q) source.carrier base.carrier := by
        intro z hz
        exact hroot (source.mem_projectedBaseN_of_mem hn q hz)
      have hc := hf.comp
        (realEuclideanTakeLeftContinuousLinearMap n q).continuous.continuousOn
        htake
      convert hc using 1
      funext z
      simp [charbonnelBuriedGraphInsertion]
  · have hc : ContinuousOn
        ((fun p : RealEuclidean q ↦ p j) ∘
          (realEuclideanTakeRightLinearMap n q)) source.carrier :=
      ((continuous_apply j).comp
        (realEuclideanTakeRightLinearMap n q).toContinuousLinearMap.continuous).continuousOn
    convert hc using 1
    funext z
    simp [charbonnelBuriedGraphInsertion]

/-- Inserting a fixed unary coordinate is continuous. -/
private theorem continuous_charbonnelUnaryPointInsertion
    {q : ℕ} (a : ℝ) :
    Continuous (charbonnelUnaryPointInsertion (q := q) a) := by
  rw [continuous_pi_iff]
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa [charbonnelUnaryPointInsertion, realEuclideanAppend] using
      (continuous_const : Continuous (fun _ : RealEuclidean q ↦ a))
  · simpa [charbonnelUnaryPointInsertion, realEuclideanAppend] using
      (continuous_apply j : Continuous (fun z : RealEuclidean q ↦ z j))

/-- Extend a positive-dimensional graph presentation through one trailing
bounded band. -/
private def CharbonnelDeepNonOpenPresentation.graph_band
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n q : ℕ} (hn : 0 < n)
    (large : CharbonnelDeepEnrichedCell S ((n + 1) + q))
    (base : CharbonnelDeepEnrichedCell S n)
    (root : RealEuclidean n → ℝ)
    (hrootContinuous : ContinuousOn root base.carrier)
    (hrootGraph : charbonnelRestrictedGraph base.carrier root ∈
      charbonnelClosure S (n + 1))
    (small : CharbonnelDeepEnrichedCell S (n + q))
    (hroot : (small.projectedBaseN hn q).carrier ⊆ base.carrier)
    (hlarge : large.carrier =
      (insertGraphAtDepth hC hn base root hrootContinuous hrootGraph
        q small hroot).carrier)
    (hprojection : charbonnelBuriedGraphProjectionLinearMap n q ''
      large.carrier = small.carrier)
    (hsmallBounded : Bornology.IsBounded small.carrier)
    (F G : RealEuclidean ((n + 1) + q) → ℝ)
    (hF : ContinuousOn F large.carrier)
    (hG : ContinuousOn G large.carrier)
    (hFG : ∀ x ∈ large.carrier, F x < G x)
    (hFgraph : charbonnelRestrictedGraph large.carrier F ∈
      charbonnelClosure S (((n + 1) + q) + 1))
    (hGgraph : charbonnelRestrictedGraph large.carrier G ∈
      charbonnelClosure S (((n + 1) + q) + 1))
    (D : CharbonnelDeepEnrichedCell S (((n + 1) + q) + 1))
    (hD : D.carrier = charbonnelOpenBand large.carrier F G)
    (hDBounded : Bornology.IsBounded D.carrier) :
    CharbonnelDeepNonOpenPresentation hC D := by
  let P := charbonnelBuriedGraphProjectionLinearMap n q
  let I : RealEuclidean (n + q) → RealEuclidean ((n + 1) + q) :=
    charbonnelBuriedGraphInsertion (q := q) root
  let constraint := charbonnelBuriedGraphConstraint q base.carrier root
  have hlargeFormula : large.carrier =
      constraint ∩ P ⁻¹' small.carrier := by
    rw [hlarge, CharbonnelDeepEnrichedCell.insertGraphAtDepth_carrier]
  have hPI : ∀ y, P (I y) = y := by
    intro y
    exact charbonnelBuriedGraphProjection_insertion root y
  have hIC : Set.MapsTo I small.carrier constraint := by
    intro y hy
    let x : RealEuclidean n := realEuclideanTakeLeft y
    let t : RealEuclidean q := realEuclideanTakeRight y
    have hydecomp : y = realEuclideanAppend x t :=
      (realEuclideanAppend_takeLeft_takeRight y).symm
    rw [hydecomp]
    rw [show I (realEuclideanAppend x t) =
        realEuclideanAppend (realEuclideanAppend x (fun _ ↦ root x)) t by
      simp [I]]
    exact (mem_charbonnelBuriedGraphConstraint_append_iff
      x (fun _ ↦ root x) t).2
        ⟨hroot (small.mem_projectedBaseN_of_mem hn q hy), rfl⟩
  have hIP : ∀ x ∈ constraint, I (P x) = x := by
    intro x hx
    exact charbonnelBuriedGraphInsertion_projection hx
  have hILarge : Set.MapsTo I small.carrier large.carrier := by
    intro y hy
    rw [hlargeFormula]
    exact ⟨hIC hy, by simpa [hPI y] using hy⟩
  have hIContinuous : ContinuousOn I small.carrier :=
    continuousOn_charbonnelBuriedGraphInsertion hn base root
      hrootContinuous small hroot
  let lower : RealEuclidean (n + q) → ℝ := fun y ↦ F (I y)
  let upper : RealEuclidean (n + q) → ℝ := fun y ↦ G (I y)
  have hlowerContinuous : ContinuousOn lower small.carrier :=
    hF.comp hIContinuous hILarge
  have hupperContinuous : ContinuousOn upper small.carrier :=
    hG.comp hIContinuous hILarge
  have hlowerImage := extendLinearMap_image_restrictedGraph
    P I hlargeFormula hPI hIC hIP F
  have hupperImage := extendLinearMap_image_restrictedGraph
    P I hlargeFormula hPI hIC hIP G
  have hlowerGraph : charbonnelRestrictedGraph small.carrier lower ∈
      charbonnelClosure S ((n + q) + 1) := by
    rw [← hlowerImage]
    rw [← charbonnelBuriedGraphProjectionLinearMap_succ n q]
    exact charbonnelBuriedGraphProjection_image_mem_charbonnelClosure
      hC (n := n) (q := q + 1) (by omega) hFgraph
  have hupperGraph : charbonnelRestrictedGraph small.carrier upper ∈
      charbonnelClosure S ((n + q) + 1) := by
    rw [← hupperImage]
    rw [← charbonnelBuriedGraphProjectionLinearMap_succ n q]
    exact charbonnelBuriedGraphProjection_image_mem_charbonnelClosure
      hC (n := n) (q := q + 1) (by omega) hGgraph
  have hlowerUpper : ∀ y ∈ small.carrier, lower y < upper y := by
    intro y hy
    exact hFG (I y) (hILarge hy)
  let deleted : CharbonnelDeepEnrichedCell S ((n + q) + 1) :=
    { carrier := charbonnelOpenBand small.carrier lower upper
      shape := .band (by omega) small.shape lower upper
        hlowerContinuous hupperContinuous hlowerUpper hlowerGraph hupperGraph }
  have hprojectionBand :
      charbonnelBuriedGraphProjectionLinearMap n (q + 1) '' D.carrier =
        deleted.carrier := by
    rw [hD, charbonnelBuriedGraphProjectionLinearMap_succ]
    exact extendLinearMap_image_openBand P I hlargeFormula hPI hIC hIP F G
  have hdeletedBounded : Bornology.IsBounded deleted.carrier := by
    rw [← hprojectionBand]
    exact ((charbonnelBuriedGraphProjectionLinearMap n (q + 1)).toContinuousLinearMap.lipschitzWith).isBounded_image hDBounded
  have hnewRoot :
      (deleted.projectedBaseN hn (q + 1)).carrier ⊆ base.carrier := by
    change (small.projectedBaseN hn q).carrier ⊆ base.carrier
    exact hroot
  have hDConstraint : D.carrier ⊆
      charbonnelBuriedGraphConstraint (q + 1) base.carrier root := by
    intro z hz
    rw [hD] at hz
    have hxLarge := hz.1
    have hxConstraint : realEuclideanTakeLeft z ∈ constraint := by
      rw [hlargeFormula] at hxLarge
      exact hxLarge.1
    exact hxConstraint
  have hcarrier : D.carrier =
      (insertGraphAtDepth hC hn base root hrootContinuous hrootGraph
        (q + 1) deleted hnewRoot).carrier := by
    rw [CharbonnelDeepEnrichedCell.insertGraphAtDepth_carrier]
    rw [← hprojectionBand]
    exact (inter_preimage_image_eq_of_subset_of_injOn hDConstraint
      charbonnelBuriedGraphProjection_injectiveOn).symm
  exact @CharbonnelDeepNonOpenPresentation.graph S hC n (q + 1) hn D
    base root hrootContinuous hrootGraph deleted hnewRoot hcarrier
    hprojectionBand hdeletedBounded

/-- Extend a unary-point presentation through one more trailing bounded band. -/
private def CharbonnelDeepNonOpenPresentation.point_band
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {q : ℕ}
    (large : CharbonnelDeepEnrichedCell S ((1 + q) + 1))
    (a : ℝ) (small : CharbonnelDeepEnrichedCell S (q + 1))
    (hlarge : large.carrier =
      (insertUnaryPointAtDepth hC a q small).carrier)
    (hprojection : charbonnelUnaryPointProjectionLinearMap (q + 1) ''
      large.carrier = small.carrier)
    (hsmallBounded : Bornology.IsBounded small.carrier)
    (F G : RealEuclidean ((1 + q) + 1) → ℝ)
    (hF : ContinuousOn F large.carrier)
    (hG : ContinuousOn G large.carrier)
    (hFG : ∀ x ∈ large.carrier, F x < G x)
    (hFgraph : charbonnelRestrictedGraph large.carrier F ∈
      charbonnelClosure S (((1 + q) + 1) + 1))
    (hGgraph : charbonnelRestrictedGraph large.carrier G ∈
      charbonnelClosure S (((1 + q) + 1) + 1))
    (D : CharbonnelDeepEnrichedCell S (((1 + q) + 1) + 1))
    (hD : D.carrier = charbonnelOpenBand large.carrier F G)
    (hDBounded : Bornology.IsBounded D.carrier) :
    CharbonnelDeepNonOpenPresentation hC D := by
  let P := charbonnelUnaryPointProjectionLinearMap (q + 1)
  let I : RealEuclidean (q + 1) → RealEuclidean (1 + (q + 1)) :=
    charbonnelUnaryPointInsertion (q := q + 1) a
  let constraint := charbonnelBuriedUnaryPointConstraint (q + 1) a
  have hlargeFormula : large.carrier =
      constraint ∩ P ⁻¹' small.carrier := by
    rw [hlarge, CharbonnelDeepEnrichedCell.insertUnaryPointAtDepth_carrier]
  have hPI : ∀ y, P (I y) = y := by
    intro y
    exact charbonnelUnaryPointProjection_insertion a y
  have hIC : Set.MapsTo I small.carrier constraint := by
    intro y hy
    simp [I, constraint, charbonnelUnaryPointInsertion,
      charbonnelBuriedUnaryPointConstraint]
  have hIP : ∀ x ∈ constraint, I (P x) = x := by
    intro x hx
    exact charbonnelUnaryPointInsertion_projection hx
  have hILarge : Set.MapsTo I small.carrier large.carrier := by
    intro y hy
    rw [hlargeFormula]
    exact ⟨hIC hy, by simpa [hPI y] using hy⟩
  have hIContinuous : ContinuousOn I small.carrier :=
    (continuous_charbonnelUnaryPointInsertion a).continuousOn
  let lower : RealEuclidean (q + 1) → ℝ := fun y ↦ F (I y)
  let upper : RealEuclidean (q + 1) → ℝ := fun y ↦ G (I y)
  have hlowerContinuous : ContinuousOn lower small.carrier :=
    hF.comp hIContinuous hILarge
  have hupperContinuous : ContinuousOn upper small.carrier :=
    hG.comp hIContinuous hILarge
  have hlowerImage := extendLinearMap_image_restrictedGraph
    P I hlargeFormula hPI hIC hIP F
  have hupperImage := extendLinearMap_image_restrictedGraph
    P I hlargeFormula hPI hIC hIP G
  have hlowerGraph : charbonnelRestrictedGraph small.carrier lower ∈
      charbonnelClosure S ((q + 1) + 1) := by
    rw [← hlowerImage]
    rw [← charbonnelUnaryPointProjectionLinearMap_succ (q + 1)]
    exact CharbonnelDeepEnrichedCell.charbonnelUnaryPointProjection_image_mem_charbonnelClosure
      hC (q := (q + 1) + 1) (by omega) hFgraph
  have hupperGraph : charbonnelRestrictedGraph small.carrier upper ∈
      charbonnelClosure S ((q + 1) + 1) := by
    rw [← hupperImage]
    rw [← charbonnelUnaryPointProjectionLinearMap_succ (q + 1)]
    exact CharbonnelDeepEnrichedCell.charbonnelUnaryPointProjection_image_mem_charbonnelClosure
      hC (q := (q + 1) + 1) (by omega) hGgraph
  have hlowerUpper : ∀ y ∈ small.carrier, lower y < upper y := by
    intro y hy
    exact hFG (I y) (hILarge hy)
  let deleted : CharbonnelDeepEnrichedCell S ((q + 1) + 1) :=
    { carrier := charbonnelOpenBand small.carrier lower upper
      shape := .band (by omega) small.shape lower upper
        hlowerContinuous hupperContinuous hlowerUpper hlowerGraph hupperGraph }
  have hprojectionBand :
      charbonnelUnaryPointProjectionLinearMap ((q + 1) + 1) '' D.carrier =
        deleted.carrier := by
    rw [hD, charbonnelUnaryPointProjectionLinearMap_succ]
    exact extendLinearMap_image_openBand P I hlargeFormula hPI hIC hIP F G
  have hdeletedBounded : Bornology.IsBounded deleted.carrier := by
    rw [← hprojectionBand]
    exact ((charbonnelUnaryPointProjectionLinearMap ((q + 1) + 1)).toContinuousLinearMap.lipschitzWith).isBounded_image hDBounded
  have hDConstraint : D.carrier ⊆
      charbonnelBuriedUnaryPointConstraint ((q + 1) + 1) a := by
    intro z hz
    rw [hD] at hz
    have hxLarge := hz.1
    have hxConstraint : realEuclideanTakeLeft z ∈ constraint := by
      rw [hlargeFormula] at hxLarge
      exact hxLarge.1
    exact hxConstraint
  have hcarrier : D.carrier =
      (insertUnaryPointAtDepth hC a (q + 1) deleted).carrier := by
    rw [CharbonnelDeepEnrichedCell.insertUnaryPointAtDepth_carrier]
    rw [← hprojectionBand]
    exact (inter_preimage_image_eq_of_subset_of_injOn hDConstraint
      charbonnelUnaryPointProjection_injectiveOn).symm
  exact @CharbonnelDeepNonOpenPresentation.point S hC (q + 1) D a deleted
    hcarrier hprojectionBand hdeletedBounded

/-- The first band above a unary point becomes the unary source piece for
point insertion. -/
private def unaryPoint_band
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (large : CharbonnelDeepEnrichedCell S 1) (a : ℝ)
    (hlarge : large.carrier = realEuclideanUnaryPiece (.point a))
    (F G : RealEuclidean 1 → ℝ)
    (hF : ContinuousOn F large.carrier)
    (hG : ContinuousOn G large.carrier)
    (hFG : ∀ x ∈ large.carrier, F x < G x)
    (hFgraph : charbonnelRestrictedGraph large.carrier F ∈
      charbonnelClosure S 2)
    (hGgraph : charbonnelRestrictedGraph large.carrier G ∈
      charbonnelClosure S 2)
    (D : CharbonnelDeepEnrichedCell S 2)
    (hD : D.carrier = charbonnelOpenBand large.carrier F G)
    (hDBounded : Bornology.IsBounded D.carrier) :
    CharbonnelDeepNonOpenPresentation hC D := by
  let u : RealEuclidean 1 := fun _ ↦ a
  have huLarge : u ∈ large.carrier := by
    rw [hlarge]
    simp [u, realEuclideanUnaryPiece, realEuclideanUnaryLift,
      UnaryPiece.carrier]
  have hbounds : F u < G u := hFG u huLarge
  let deleted : CharbonnelDeepEnrichedCell S 1 :=
    { carrier := realEuclideanUnaryPiece (.bounded (F u) (G u))
      shape := .unary (.bounded (F u) (G u)) }
  have hprojection :
      charbonnelUnaryPointProjectionLinearMap 1 '' D.carrier =
        deleted.carrier := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hD] at hz
      have hzBase := hz.1
      have htake : realEuclideanTakeLeft z = u := by
        funext i
        rw [Fin.eq_zero i]
        rw [hlarge] at hzBase
        simpa [realEuclideanUnaryPiece, realEuclideanUnaryLift,
          UnaryPiece.carrier, u] using hzBase
      change F u < realEuclideanTakeRight z 0 ∧
        realEuclideanTakeRight z 0 < G u
      simpa [htake] using hz.2
    · intro hy
      let z : RealEuclidean 2 := realEuclideanAppend u y
      refine ⟨z, ?_, ?_⟩
      · rw [hD]
        simp only [charbonnelOpenBand, Set.mem_ofPred_eq, z,
          realEuclideanTakeLeft_append, realEuclideanTakeRight_append]
        simpa [deleted, realEuclideanUnaryPiece, realEuclideanUnaryLift,
          UnaryPiece.carrier] using And.intro huLarge hy
      · exact charbonnelUnaryPointProjectionLinearMap_append u y
  have hdeletedBounded : Bornology.IsBounded deleted.carrier := by
    rw [← hprojection]
    exact ((charbonnelUnaryPointProjectionLinearMap 1).toContinuousLinearMap.lipschitzWith).isBounded_image hDBounded
  have hDConstraint : D.carrier ⊆
      charbonnelBuriedUnaryPointConstraint 1 a := by
    intro z hz
    rw [hD] at hz
    have hzBase := hz.1
    rw [hlarge] at hzBase
    simpa [charbonnelBuriedUnaryPointConstraint,
      realEuclideanUnaryPiece, realEuclideanUnaryLift,
      UnaryPiece.carrier] using hzBase
  have hcarrier : D.carrier =
      (insertUnaryPointAtDepth hC a 0 deleted).carrier := by
    rw [CharbonnelDeepEnrichedCell.insertUnaryPointAtDepth_carrier]
    rw [← hprojection]
    exact (inter_preimage_image_eq_of_subset_of_injOn hDConstraint
      charbonnelUnaryPointProjection_injectiveOn).symm
  exact @CharbonnelDeepNonOpenPresentation.point S hC 0 D a deleted
    hcarrier hprojection hdeletedBounded

/-! ## Projection homeomorphisms and projected targets -/

/-- On a graph presentation, coordinate deletion is a homeomorphism onto the
deleted carrier. -/
def charbonnelDeepGraphPresentationHomeomorph
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n q : ℕ} (hn : 0 < n)
    (D : CharbonnelDeepEnrichedCell S ((n + 1) + q))
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    (deleted : CharbonnelDeepEnrichedCell S (n + q))
    (hroot : (deleted.projectedBaseN hn q).carrier ⊆ base.carrier)
    (carrier_eq : D.carrier =
      (insertGraphAtDepth hC hn base f hf hgraph q deleted hroot).carrier)
    (projection_image :
      charbonnelBuriedGraphProjectionLinearMap n q '' D.carrier =
        deleted.carrier) :
    D.carrier ≃ₜ deleted.carrier where
  toFun z :=
    ⟨charbonnelBuriedGraphProjectionLinearMap n q z,
      by rw [← projection_image]; exact ⟨z, z.property, rfl⟩⟩
  invFun y :=
    ⟨charbonnelBuriedGraphInsertion (q := q) f
        (y : RealEuclidean (n + q)), by
      rw [carrier_eq,
        CharbonnelDeepEnrichedCell.insertGraphAtDepth_carrier]
      constructor
      · let yy : RealEuclidean (n + q) := y
        let x : RealEuclidean n := realEuclideanTakeLeft yy
        let t : RealEuclidean q := realEuclideanTakeRight yy
        have hydecomp : yy = realEuclideanAppend x t :=
          (realEuclideanAppend_takeLeft_takeRight yy).symm
        change charbonnelBuriedGraphInsertion (q := q) f yy ∈
          charbonnelBuriedGraphConstraint q base.carrier f
        rw [hydecomp]
        rw [charbonnelBuriedGraphInsertion_append]
        exact (mem_charbonnelBuriedGraphConstraint_append_iff
          x (fun _ ↦ f x) t).2
            ⟨hroot (deleted.mem_projectedBaseN_of_mem hn q y.property), rfl⟩
      · change charbonnelBuriedGraphProjectionLinearMap n q
          (charbonnelBuriedGraphInsertion (q := q) f y) ∈ deleted.carrier
        rw [charbonnelBuriedGraphProjection_insertion]
        exact y.property⟩
  left_inv z := by
    apply Subtype.ext
    apply charbonnelBuriedGraphInsertion_projection
    let x : RealEuclidean ((n + 1) + q) := z
    have hx : x ∈ D.carrier := z.property
    rw [carrier_eq,
      CharbonnelDeepEnrichedCell.insertGraphAtDepth_carrier] at hx
    exact hx.1
  right_inv y := by
    apply Subtype.ext
    exact charbonnelBuriedGraphProjection_insertion f (y : RealEuclidean (n + q))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((charbonnelBuriedGraphProjectionLinearMap n q).toContinuousLinearMap.continuous).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuousOn_charbonnelBuriedGraphInsertion hn base f hf deleted
      hroot).restrict

/-- On a unary-point presentation, first-coordinate deletion is a
homeomorphism onto the deleted carrier. -/
def charbonnelDeepPointPresentationHomeomorph
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {q : ℕ}
    (D : CharbonnelDeepEnrichedCell S ((1 + q) + 1))
    (a : ℝ) (deleted : CharbonnelDeepEnrichedCell S (q + 1))
    (carrier_eq : D.carrier =
      (insertUnaryPointAtDepth hC a q deleted).carrier)
    (projection_image :
      charbonnelUnaryPointProjectionLinearMap (q + 1) '' D.carrier =
        deleted.carrier) :
    D.carrier ≃ₜ deleted.carrier where
  toFun z :=
    ⟨charbonnelUnaryPointProjectionLinearMap (q + 1) z,
      by rw [← projection_image]; exact ⟨z, z.property, rfl⟩⟩
  invFun y :=
    ⟨charbonnelUnaryPointInsertion (q := q + 1) a
        (y : RealEuclidean (q + 1)), by
      rw [carrier_eq,
        CharbonnelDeepEnrichedCell.insertUnaryPointAtDepth_carrier]
      exact ⟨by
        simp [charbonnelUnaryPointInsertion,
          charbonnelBuriedUnaryPointConstraint], by
        change charbonnelUnaryPointProjectionLinearMap (q + 1)
          (charbonnelUnaryPointInsertion (q := q + 1) a y) ∈ deleted.carrier
        rw [charbonnelUnaryPointProjection_insertion]
        exact y.property⟩⟩
  left_inv z := by
    apply Subtype.ext
    change charbonnelUnaryPointInsertion (q := q + 1) a
      (charbonnelUnaryPointProjectionLinearMap (q + 1) z) = z
    apply charbonnelUnaryPointInsertion_projection
    let x : RealEuclidean ((1 + q) + 1) := z
    have hx : x ∈ D.carrier := z.property
    rw [carrier_eq,
      CharbonnelDeepEnrichedCell.insertUnaryPointAtDepth_carrier] at hx
    exact hx.1
  right_inv y := by
    apply Subtype.ext
    exact charbonnelUnaryPointProjection_insertion a
      (y : RealEuclidean (q + 1))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((charbonnelUnaryPointProjectionLinearMap (q + 1)).toContinuousLinearMap.continuous).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_charbonnelUnaryPointInsertion a).comp
      continuous_subtype_val

/-- A target remains in the Charbonnel closure after deleting a buried graph
coordinate. -/
theorem charbonnelDeepGraphPresentation_projectedTarget_mem
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n q : ℕ} (hn : 0 < n)
    {A : Set (RealEuclidean ((n + 1) + q))}
    (hA : A ∈ charbonnelClosure S ((n + 1) + q)) :
    charbonnelBuriedGraphProjectionLinearMap n q '' A ∈
      charbonnelClosure S (n + q) :=
  charbonnelBuriedGraphProjection_image_mem_charbonnelClosure
    hC (by omega) hA

/-- A target remains in the Charbonnel closure after deleting a unary point. -/
theorem charbonnelDeepPointPresentation_projectedTarget_mem
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {q : ℕ} {A : Set (RealEuclidean ((1 + q) + 1))}
    (hA : A ∈ charbonnelClosure S ((1 + q) + 1)) :
    charbonnelUnaryPointProjectionLinearMap (q + 1) '' A ∈
      charbonnelClosure S (q + 1) := by
  exact CharbonnelDeepEnrichedCell.charbonnelUnaryPointProjection_image_mem_charbonnelClosure
    hC (q := q + 1) (by omega) hA

/-- Relative closedness is preserved by the graph-presentation projection. -/
theorem charbonnelDeepGraphPresentation_projectedTarget_isClosed
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n q : ℕ} (hn : 0 < n)
    (D : CharbonnelDeepEnrichedCell S ((n + 1) + q))
    (base : CharbonnelDeepEnrichedCell S n)
    (f : RealEuclidean n → ℝ) (hf : ContinuousOn f base.carrier)
    (hgraph : charbonnelRestrictedGraph base.carrier f ∈
      charbonnelClosure S (n + 1))
    (deleted : CharbonnelDeepEnrichedCell S (n + q))
    (hroot : (deleted.projectedBaseN hn q).carrier ⊆ base.carrier)
    (carrier_eq : D.carrier =
      (insertGraphAtDepth hC hn base f hf hgraph q deleted hroot).carrier)
    (projection_image :
      charbonnelBuriedGraphProjectionLinearMap n q '' D.carrier =
        deleted.carrier)
    {A : Set (RealEuclidean ((n + 1) + q))} (hAD : A ⊆ D.carrier)
    (hclosed : IsClosed (Subtype.val ⁻¹' A : Set D.carrier)) :
    IsClosed (Subtype.val ⁻¹'
      (charbonnelBuriedGraphProjectionLinearMap n q '' A) :
        Set deleted.carrier) := by
  let H := charbonnelDeepGraphPresentationHomeomorph hC hn D base f hf
    hgraph deleted hroot carrier_eq projection_image
  rw [show (Subtype.val ⁻¹'
      (charbonnelBuriedGraphProjectionLinearMap n q '' A) :
        Set deleted.carrier) =
      H '' (Subtype.val ⁻¹' A : Set D.carrier) by
    ext y
    constructor
    · rintro ⟨x, hxA, hxy⟩
      let xs : D.carrier := ⟨x, hAD hxA⟩
      refine ⟨xs, hxA, ?_⟩
      apply Subtype.ext
      change charbonnelBuriedGraphProjectionLinearMap n q x = y
      exact hxy
    · rintro ⟨x, hxA, rfl⟩
      refine ⟨x, hxA, ?_⟩
      rfl]
  exact H.isClosed_image.mpr hclosed

/-- Relative closedness is preserved by the point-presentation projection. -/
theorem charbonnelDeepPointPresentation_projectedTarget_isClosed
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {q : ℕ}
    (D : CharbonnelDeepEnrichedCell S ((1 + q) + 1))
    (a : ℝ) (deleted : CharbonnelDeepEnrichedCell S (q + 1))
    (carrier_eq : D.carrier =
      (insertUnaryPointAtDepth hC a q deleted).carrier)
    (projection_image :
      charbonnelUnaryPointProjectionLinearMap (q + 1) '' D.carrier =
        deleted.carrier)
    {A : Set (RealEuclidean ((1 + q) + 1))} (hAD : A ⊆ D.carrier)
    (hclosed : IsClosed (Subtype.val ⁻¹' A : Set D.carrier)) :
    IsClosed (Subtype.val ⁻¹'
      (charbonnelUnaryPointProjectionLinearMap (q + 1) '' A) :
        Set deleted.carrier) := by
  let H := charbonnelDeepPointPresentationHomeomorph hC D a deleted
    carrier_eq projection_image
  rw [show (Subtype.val ⁻¹'
      (charbonnelUnaryPointProjectionLinearMap (q + 1) '' A) :
        Set deleted.carrier) =
      H '' (Subtype.val ⁻¹' A : Set D.carrier) by
    ext y
    constructor
    · rintro ⟨x, hxA, hxy⟩
      let xs : D.carrier := ⟨x, hAD hxA⟩
      refine ⟨xs, hxA, ?_⟩
      apply Subtype.ext
      change charbonnelUnaryPointProjectionLinearMap (q + 1) x = y
      exact hxy
    · rintro ⟨x, hxA, rfl⟩
      refine ⟨x, hxA, ?_⟩
      rfl]
  exact H.isClosed_image.mpr hclosed

/-! The band-deletion constructors and the structural classifier follow.
They are kept separate so the transport module can consume only the public
indexed result above. -/

private def singularRootPresentation_of_isBounded_nonempty_not_isOpen
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {d : ℕ} (D : CharbonnelDeepEnrichedCell S d)
    (hbounded : Bornology.IsBounded D.carrier)
    (hne : D.carrier.Nonempty) (hnotopen : ¬ IsOpen D.carrier) :
    CharbonnelDeepSingularRootPresentation hC D := by
  rcases D with ⟨carrier, shape⟩
  induction shape with
  | unary piece =>
      cases piece with
      | point a =>
          exact .unaryPoint _ a rfl hbounded
      | bounded a b =>
          exfalso
          apply hnotopen
          have hopen : IsOpen ((fun x : RealEuclidean 1 ↦ x 0) ⁻¹'
              Set.Ioo a b) :=
            isOpen_Ioo.preimage
              (continuous_apply (0 : Fin 1) :
                Continuous (fun x : RealEuclidean 1 ↦ x 0))
          convert hopen using 1 <;>
            ext x <;>
            simp [realEuclideanUnaryPiece, realEuclideanUnaryLift,
              UnaryPiece.carrier]
      | leftRay b =>
          exfalso
          apply hnotopen
          have hopen : IsOpen ((fun x : RealEuclidean 1 ↦ x 0) ⁻¹'
              Set.Iio b) :=
            isOpen_Iio.preimage
              (continuous_apply (0 : Fin 1) :
                Continuous (fun x : RealEuclidean 1 ↦ x 0))
          convert hopen using 1 <;>
            ext x <;>
            simp [realEuclideanUnaryPiece, realEuclideanUnaryLift,
              UnaryPiece.carrier]
      | rightRay a =>
          exfalso
          apply hnotopen
          have hopen : IsOpen ((fun x : RealEuclidean 1 ↦ x 0) ⁻¹'
              Set.Ioi a) :=
            isOpen_Ioi.preimage
              (continuous_apply (0 : Fin 1) :
                Continuous (fun x : RealEuclidean 1 ↦ x 0))
          convert hopen using 1 <;>
            ext x <;>
            simp [realEuclideanUnaryPiece, realEuclideanUnaryLift,
              UnaryPiece.carrier]
      | whole =>
          exfalso
          apply hnotopen
          simpa [realEuclideanUnaryPiece, realEuclideanUnaryLift,
            UnaryPiece.carrier] using
            (isOpen_univ : IsOpen (Set.univ : Set (RealEuclidean 1)))
  | @graph n baseCarrier hn baseShape root hrootContinuous hrootGraph =>
      let base : CharbonnelDeepEnrichedCell S _ :=
        ⟨_, baseShape⟩
      let graphCell : CharbonnelDeepEnrichedCell S _ :=
        ⟨_, .graph hn baseShape root hrootContinuous hrootGraph⟩
      have hroot : (base.projectedBaseN hn 0).carrier ⊆ base.carrier := by
        simpa using (Set.Subset.rfl : base.carrier ⊆ base.carrier)
      have hcarrier : graphCell.carrier =
          (insertGraphAtDepth hC hn base root hrootContinuous
            hrootGraph 0 base hroot).carrier := by
        rw [CharbonnelDeepEnrichedCell.insertGraphAtDepth_carrier]
        dsimp only [graphCell, base]
        ext z
        simp [charbonnelBuriedGraphConstraint, charbonnelRestrictedGraph]
        aesop
      have hprojection :
          charbonnelBuriedGraphProjectionLinearMap _ 0 '' graphCell.carrier =
            base.carrier := by
        ext x
        constructor
        · rintro ⟨z, hz, hzx⟩
          rw [charbonnelBuriedGraphProjectionLinearMap_zero] at hzx
          rw [← hzx]
          exact hz.1
        · intro hx
          let u : RealEuclidean 1 := fun _ ↦ root x
          refine ⟨@realEuclideanAppend n 1 x u, ?_, ?_⟩
          · change @realEuclideanAppend n 1 x u ∈
              charbonnelRestrictedGraph base.carrier root
            exact ⟨by simpa using hx, by simp [u]⟩
          · simp
      have hbaseBounded : Bornology.IsBounded base.carrier := by
        rw [← hprojection]
        exact (charbonnelBuriedGraphProjectionLinearMap _ 0).toContinuousLinearMap.lipschitzWith.isBounded_image hbounded
      exact .transport graphCell
        (@CharbonnelDeepNonOpenPresentation.graph S hC _ 0 hn graphCell
          base root hrootContinuous hrootGraph base hroot hcarrier hprojection
          hbaseBounded)
  | band hn baseShape F G hF hG hFG hFgraph hGgraph ih =>
      let base : CharbonnelDeepEnrichedCell S _ := ⟨_, baseShape⟩
      let bandCell : CharbonnelDeepEnrichedCell S _ :=
        ⟨_, .band hn baseShape F G hF hG hFG hFgraph hGgraph⟩
      have hbaseBounded : Bornology.IsBounded base.carrier := by
        refine Bornology.IsBounded.subset
          ((realEuclideanTakeLeftContinuousLinearMap _ 1).lipschitzWith.isBounded_image hbounded) ?_
        intro x hx
        let u : RealEuclidean 1 := fun _ ↦ (F x + G x) / 2
        refine ⟨realEuclideanAppend x u, ?_, ?_⟩
        · exact ⟨by simpa using hx, by
            have hlt := hFG x hx
            constructor <;> simp [u] <;> linarith⟩
        · simp
      have hbaseNonempty : base.carrier.Nonempty := by
        obtain ⟨z, hz⟩ := hne
        exact ⟨realEuclideanTakeLeft z, hz.1⟩
      have hbaseNotOpen : ¬ IsOpen base.carrier := by
        intro hbaseOpen
        apply hnotopen
        exact isOpen_charbonnelOpenBand_of_isOpen hbaseOpen hF hG
      have hpresentation := ih hbaseBounded hbaseNonempty hbaseNotOpen
      cases hpresentation with
      | unaryPoint _ a hpoint hpointBounded =>
          exact .transport bandCell
            (unaryPoint_band hC base a hpoint F G hF hG hFG
              hFgraph hGgraph bandCell rfl hbounded)
      | transport _ presentation =>
          cases presentation with
          | @graph n q hn' _ rootBase root hrootContinuous hrootGraph small
              hroot hlarge hprojection hsmallBounded =>
              exact .transport bandCell
                (CharbonnelDeepNonOpenPresentation.graph_band hC hn' base
                  rootBase root hrootContinuous hrootGraph small hroot hlarge
                  hprojection hsmallBounded F G hF hG hFG hFgraph hGgraph
                  bandCell rfl hbounded)
          | point _ a small hlarge hprojection hsmallBounded =>
              exact .transport bandCell
                (CharbonnelDeepNonOpenPresentation.point_band hC base a small
                  hlarge hprojection hsmallBounded F G hF hG hFG hFgraph
                  hGgraph bandCell rfl hbounded)
  | lowerRay hn baseShape G hG hGgraph ih =>
      have hempty := lowerRay_base_eq_empty_of_isBounded G hbounded
      exfalso
      obtain ⟨z, hz⟩ := hne
      have hzBase := hz.1
      rw [hempty] at hzBase
      exact hzBase
  | upperRay hn baseShape F hF hFgraph ih =>
      have hempty := upperRay_base_eq_empty_of_isBounded F hbounded
      exfalso
      obtain ⟨z, hz⟩ := hne
      have hzBase := hz.1
      rw [hempty] at hzBase
      exact hzBase
  | cylinder hn baseShape ih =>
      have hempty := cylinder_base_eq_empty_of_isBounded hbounded
      exfalso
      obtain ⟨z, hz⟩ := hne
      have hzBase : realEuclideanTakeLeft z ∈ (∅ : Set _) := by
        rw [← hempty]
        exact hz
      exact hzBase

/-- Every nonempty bounded non-open deep cell of dimension at least two is
the exact insertion of either a positive-dimensional buried graph or a unary
point, over a bounded deleted deep cell. -/
def charbonnelDeepNonOpenPresentation_of_isBounded_nonempty_not_isOpen
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {d : ℕ} (hd : 0 < d)
    (D : CharbonnelDeepEnrichedCell S (d + 1))
    (hbounded : Bornology.IsBounded D.carrier)
    (hne : D.carrier.Nonempty) (hnotopen : ¬ IsOpen D.carrier) :
    CharbonnelDeepNonOpenPresentation hC D := by
  have h := singularRootPresentation_of_isBounded_nonempty_not_isOpen
    hC D hbounded hne hnotopen
  cases h with
  | unaryPoint _ _ _ _ => omega
  | transport _ presentation => exact presentation

end AbelFormalization
