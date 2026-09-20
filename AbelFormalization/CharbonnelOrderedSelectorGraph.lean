import AbelFormalization.CharbonnelOrderedSelectorContinuity

/-!
# Family membership of every canonical ordered-selector graph

The original Maxwell ordered incidence exposes only the first entry of an
increasing tuple.  This file exposes an arbitrary entry.  Its incidence still
contains the whole increasing tuple, so WS1--WS4 and existential projection
put the visible graph in the Charbonnel closure.  On an exact finite-fibre
locus, the increasing tuple is the canonical enumeration.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## Incidence for an arbitrary ordered entry -/

/-- An increasing `(k + 1)`-tuple of fibre points whose `i`th entry is the
displayed scalar value. -/
def MaxwellOrderedScalarIthFiberWitness {p k : ℕ}
    (R : MaxwellRelation p 1) (i : Fin (k + 1))
    (x : RealEuclidean p) (y : ℝ) : Prop :=
  ∃ values : RealEuclidean (k + 1),
    values i = y ∧
    (∀ j : Fin k, values j.castSucc < values j.succ) ∧
    ∀ j : Fin (k + 1), values j ∈ maxwellScalarFiber R x

/-- Polynomial imposing that the displayed output equals entry `i` of the
full ordered tuple. -/
def maxwellOrderedScalarIthWitnessPolynomial
    (p k : ℕ) (i : Fin (k + 1)) :
    MvPolynomial (Fin ((p + 1) + (k + 1))) ℝ :=
  MvPolynomial.X (maxwellOrderedWitnessValueIndex p k i) -
    MvPolynomial.X (maxwellOrderedWitnessOutputIndex p k)

/-- Equality to entry `i`, together with all adjacent strict inequalities. -/
def maxwellOrderedScalarIthWitnessConstraint
    (p k : ℕ) (i : Fin (k + 1)) :
    Set (RealEuclidean ((p + 1) + (k + 1))) :=
  {w | MvPolynomial.eval w
      (maxwellOrderedScalarIthWitnessPolynomial p k i) = 0} ∩
    ⋂ j : Fin k,
      {w | 0 < MvPolynomial.eval w
        (maxwellOrderedWitnessIncrementPolynomial p k j)}

theorem polynomialSignConstructible_maxwellOrderedScalarIthWitnessConstraint
    (p k : ℕ) (i : Fin (k + 1)) :
    PolynomialSignConstructible ((p + 1) + (k + 1))
      (maxwellOrderedScalarIthWitnessConstraint p k i) := by
  exact .inter
    (.zero (maxwellOrderedScalarIthWitnessPolynomial p k i))
    (polynomialSignConstructible_iInter_fin _ fun j ↦
      .pos (maxwellOrderedWitnessIncrementPolynomial p k j))

/-- The full ordered-tuple incidence with entry `i` exposed as the visible
scalar coordinate. -/
def maxwellOrderedScalarIthWitnessIncidence {p : ℕ}
    (B : Set (RealEuclidean p)) (R : MaxwellRelation p 1) (k : ℕ)
    (i : Fin (k + 1)) :
    Set (RealEuclidean ((p + 1) + (k + 1))) :=
  (maxwellOrderedWitnessBaseLinearMap p k ⁻¹' B ∩
    ⋂ j : Fin (k + 1),
      maxwellOrderedWitnessRelationLinearMap p k j ⁻¹' R) ∩
    maxwellOrderedScalarIthWitnessConstraint p k i

@[simp]
theorem realEuclideanAppend_append_mem_maxwellOrderedScalarIthWitnessIncidence_iff
    {p k : ℕ} (B : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) (i : Fin (k + 1))
    (x : RealEuclidean p) (y : ℝ)
    (values : RealEuclidean (k + 1)) :
    realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) values ∈
        maxwellOrderedScalarIthWitnessIncidence B R k i ↔
      x ∈ B ∧ values i = y ∧
        (∀ j : Fin k, values j.castSucc < values j.succ) ∧
        ∀ j : Fin (k + 1),
          values j ∈ maxwellScalarFiber R x := by
  simp [maxwellOrderedScalarIthWitnessIncidence,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter,
    maxwellOrderedScalarIthWitnessConstraint,
    maxwellOrderedWitnessBaseLinearMap_apply_append,
    maxwellOrderedWitnessRelationLinearMap_apply_append,
    maxwellScalarFiber, maxwellOrderedScalarIthWitnessPolynomial,
    maxwellOrderedWitnessIncrementPolynomial, map_sub,
    MvPolynomial.eval_X, maxwellOrderedWitnessOutputIndex,
    maxwellOrderedWitnessValueIndex, realEuclideanAppend_castAdd,
    realEuclideanAppend_natAdd, sub_eq_zero, sub_pos,
    and_assoc, and_left_comm, and_comm]

/-- The visible graph obtained by projecting away the full ordered tuple. -/
def maxwellOrderedScalarIthWitnessGraph {p : ℕ}
    (B : Set (RealEuclidean p)) (R : MaxwellRelation p 1) (k : ℕ)
    (i : Fin (k + 1)) : Set (RealEuclidean (p + 1)) :=
  realEuclideanExistentialProjection
    (maxwellOrderedScalarIthWitnessIncidence B R k i)

@[simp]
theorem realEuclideanAppend_mem_maxwellOrderedScalarIthWitnessGraph_iff
    {p k : ℕ} (B : Set (RealEuclidean p))
    (R : MaxwellRelation p 1) (i : Fin (k + 1))
    (x : RealEuclidean p) (y : ℝ) :
    realEuclideanAppend x (fun _ : Fin 1 ↦ y) ∈
        maxwellOrderedScalarIthWitnessGraph B R k i ↔
      x ∈ B ∧ MaxwellOrderedScalarIthFiberWitness R i x y := by
  change (∃ values : RealEuclidean (k + 1),
    realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y)) values ∈
        maxwellOrderedScalarIthWitnessIncidence B R k i) ↔ _
  simp only [
    realEuclideanAppend_append_mem_maxwellOrderedScalarIthWitnessIncidence_iff,
    MaxwellOrderedScalarIthFiberWitness]
  aesop

/-- Every arbitrary-entry ordered-witness graph belongs to the Charbonnel
closure when its base and scalar relation do. -/
theorem maxwellOrderedScalarIthWitnessGraph_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p k : ℕ} (hp : 0 < p)
    {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hB : B ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (i : Fin (k + 1)) :
    maxwellOrderedScalarIthWitnessGraph B R k i ∈
      charbonnelClosure S (p + 1) := by
  have hambient : 0 < (p + 1) + (k + 1) := by omega
  have hbase : maxwellOrderedWitnessBaseLinearMap p k ⁻¹' B ∈
      charbonnelClosure S ((p + 1) + (k + 1)) :=
    hC.linear_preimage_mem hambient hp hB
      (maxwellOrderedWitnessBaseLinearMap p k)
  have hrelations :
      (⋂ j : Fin (k + 1),
        maxwellOrderedWitnessRelationLinearMap p k j ⁻¹' R) ∈
          charbonnelClosure S ((p + 1) + (k + 1)) := by
    apply maxwell_charbonnelClosure_iInter_fin_mem hC hambient
    intro j
    exact hC.linear_preimage_mem hambient (by omega) hR
      (maxwellOrderedWitnessRelationLinearMap p k j)
  have hconstraint : maxwellOrderedScalarIthWitnessConstraint p k i ∈
      charbonnelClosure S ((p + 1) + (k + 1)) :=
    hC.ws2_polynomialSign hambient
      (polynomialSignConstructible_maxwellOrderedScalarIthWitnessConstraint
        p k i)
  have hincidence : maxwellOrderedScalarIthWitnessIncidence B R k i ∈
      charbonnelClosure S ((p + 1) + (k + 1)) :=
    hC.ws1_inter hambient
      (hC.ws1_inter hambient hbase hrelations) hconstraint
  exact charbonnelClosure_projection (by omega) hincidence

/-! ## Identification with the canonical enumeration -/

/-- There is only one increasing `r`-tuple of points in a finite set of
cardinality `r`. -/
theorem strictMono_tuple_eq_of_mem_of_ncard_eq
    {r : ℕ} {s : Set ℝ} (hfinite : s.Finite) (hcard : s.ncard = r)
    {values other : Fin r → ℝ}
    (hvaluesMono : StrictMono values) (hotherMono : StrictMono other)
    (hvaluesMem : ∀ j, values j ∈ s)
    (hotherMem : ∀ j, other j ∈ s) :
    values = other := by
  classical
  let t : Finset ℝ := hfinite.toFinset
  have htCard : t.card = r := by
    change hfinite.toFinset.card = r
    rw [← Set.ncard_eq_toFinset_card s hfinite]
    exact hcard
  let valuesEmbedding : Fin r ↪o ℝ :=
    OrderEmbedding.ofStrictMono values hvaluesMono
  let otherEmbedding : Fin r ↪o ℝ :=
    OrderEmbedding.ofStrictMono other hotherMono
  have hvaluesEmbedding :
      valuesEmbedding = t.orderEmbOfFin htCard := by
    exact Finset.orderEmbOfFin_unique' htCard fun j ↦
      (Set.Finite.mem_toFinset hfinite).mpr (hvaluesMem j)
  have hotherEmbedding :
      otherEmbedding = t.orderEmbOfFin htCard := by
    exact Finset.orderEmbOfFin_unique' htCard fun j ↦
      (Set.Finite.mem_toFinset hfinite).mpr (hotherMem j)
  funext j
  exact DFunLike.congr_fun
    (hvaluesEmbedding.trans hotherEmbedding.symm) j

/-- Under exact cardinality, an arbitrary-entry full-tuple witness displays
the corresponding entry of the canonical increasing enumeration. -/
theorem maxwellOrderedScalarIthFiberWitness_iff_eq_enumeration
    {p k : ℕ} {R : MaxwellRelation p 1} {x : RealEuclidean p}
    (hfinite : (maxwellScalarFiber R x).Finite)
    (hcard : (maxwellScalarFiber R x).ncard = k + 1)
    (i : Fin (k + 1)) (y : ℝ) :
    MaxwellOrderedScalarIthFiberWitness R i x y ↔
      y = maxwellOrderedScalarFiberEnumeration R x i := by
  constructor
  · rintro ⟨values, hiy, hstep, hvalues⟩
    have hvaluesMono : StrictMono values :=
      Fin.strictMono_iff_lt_succ.mpr hstep
    have hcanonicalMono : StrictMono
        (maxwellOrderedScalarFiberEnumeration R x) :=
      maxwellOrderedScalarFiberEnumeration_strictMono hfinite hcard
    have hcanonicalMem : ∀ j : Fin (k + 1),
        maxwellOrderedScalarFiberEnumeration R x j ∈
          maxwellScalarFiber R x :=
      fun j ↦ maxwellOrderedScalarFiberEnumeration_mem hfinite hcard j
    have htuple : values = maxwellOrderedScalarFiberEnumeration R x :=
      strictMono_tuple_eq_of_mem_of_ncard_eq hfinite hcard
        hvaluesMono hcanonicalMono hvalues hcanonicalMem
    rw [htuple] at hiy
    exact hiy.symm
  · intro hy
    let values : Fin (k + 1) → ℝ :=
      maxwellOrderedScalarFiberEnumeration R x
    refine ⟨values, ?_, ?_, ?_⟩
    · exact hy.symm
    · exact Fin.strictMono_iff_lt_succ.mp
        (maxwellOrderedScalarFiberEnumeration_strictMono hfinite hcard)
    · intro j
      exact maxwellOrderedScalarFiberEnumeration_mem hfinite hcard j

/-- On an exact finite-fibre base, the incidence graph exposing entry `i`
is exactly the restricted graph of the canonical `i`th selector. -/
theorem maxwellOrderedScalarIthWitnessGraph_eq_charbonnelRestrictedGraph
    {p k : ℕ} {B : Set (RealEuclidean p)}
    {R : MaxwellRelation p 1}
    (hfiber : ∀ x ∈ B,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = k + 1)
    (i : Fin (k + 1)) :
    maxwellOrderedScalarIthWitnessGraph B R k i =
      charbonnelRestrictedGraph B
        (fun x ↦ maxwellOrderedScalarFiberEnumeration R x i) := by
  ext z
  have hright : realEuclideanTakeRight z =
      (fun _ : Fin 1 ↦ realEuclideanTakeRight z 0) := by
    funext j
    rw [show j = 0 from Fin.eq_zero j]
  rw [← realEuclideanAppend_takeLeft_takeRight (n := p) (m := 1) z,
    hright,
    realEuclideanAppend_mem_maxwellOrderedScalarIthWitnessGraph_iff]
  simp only [charbonnelRestrictedGraph, Set.mem_ofPred_eq,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append]
  constructor
  · rintro ⟨hx, hwitness⟩
    exact ⟨hx,
      (maxwellOrderedScalarIthFiberWitness_iff_eq_enumeration
        (hfiber _ hx).1 (hfiber _ hx).2 i _).mp hwitness⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx,
      (maxwellOrderedScalarIthFiberWitness_iff_eq_enumeration
        (hfiber _ hx).1 (hfiber _ hx).2 i _).mpr hy⟩

/-- Every canonical ordered-selector graph over an exact finite-fibre base is
a member of the Charbonnel closure. -/
theorem charbonnelRestrictedGraph_maxwellOrderedScalarFiberEnumeration_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p r : ℕ} (hp : 0 < p)
    {B : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hB : B ∈ charbonnelClosure S p)
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hfiber : ∀ x ∈ B,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = r)
    (i : Fin r) :
    charbonnelRestrictedGraph B
        (fun x ↦ maxwellOrderedScalarFiberEnumeration R x i) ∈
      charbonnelClosure S (p + 1) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ k =>
      rw [← maxwellOrderedScalarIthWitnessGraph_eq_charbonnelRestrictedGraph
        hfiber i]
      exact maxwellOrderedScalarIthWitnessGraph_mem_charbonnelClosure
        hC hp hB hR i

/-! ## Membership-complete cell-cover wrappers -/

/-- The local exact-fibre cylinder cover, with canonical graph membership
discharged by the ordered-tuple incidence above. -/
noncomputable def
    charbonnelFiniteSelectorRelativeCellCover_of_noEscape_noCollision
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p r : ℕ} (hp : 0 < p)
    {base : Set (RealEuclidean p)}
    (hbaseShape : CharbonnelCellShape p base)
    (hbaseMem : base ∈ charbonnelClosure S p)
    {R : MaxwellRelation p 1}
    (hR : R ∈ charbonnelClosure S (p + 1))
    (hfiber : ∀ x ∈ base,
      (maxwellScalarFiber R x).Finite ∧
      (maxwellScalarFiber R x).ncard = r)
    (hescape : MaxwellScalarFiberNoEscape base R)
    (hcollision : MaxwellScalarFiberNoCollision base R) :
    CharbonnelFiniteCompatibleRelativeCellCover (charbonnelClosure S)
      (charbonnelCylinderCell base) R := by
  apply
    charbonnelFiniteSelectorRelativeCellCover_of_noEscape_noCollision_graph_mem
      hC hp hbaseShape hbaseMem hfiber hescape hcollision
  intro i
  exact
    charbonnelRestrictedGraph_maxwellOrderedScalarFiberEnumeration_mem_charbonnelClosure
      hC hp hbaseMem hR hfiber i

/-- Global mixed-cardinality cylinder cover over a finite recursive base-cell
cover, with every canonical graph-membership premise discharged internally. -/
noncomputable def
    CharbonnelFiniteCompatibleCellCover.finiteFiberRelationCylinderCover_of_relation_mem
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {p : ℕ} (hp : 0 < p)
    {B : Set (RealEuclidean p)}
    (baseCover : CharbonnelFiniteCompatibleCellCover
      (charbonnelClosure S) B)
    (A : MaxwellRelation p 1)
    (hA : A ∈ charbonnelClosure S (p + 1))
    (r : Fin baseCover.count → ℕ)
    (hfiber : ∀ i x, x ∈ (baseCover.cell i).carrier →
      (maxwellScalarFiber A x).Finite ∧
      (maxwellScalarFiber A x).ncard = r i)
    (hescape : ∀ i, MaxwellScalarFiberNoEscape
      (baseCover.cell i).carrier A)
    (hcollision : ∀ i, MaxwellScalarFiberNoCollision
      (baseCover.cell i).carrier A) :
    CharbonnelFiniteCompatibleCellCover (charbonnelClosure S) A := by
  apply baseCover.finiteFiberRelationCylinderCover hC hp A r
    hfiber hescape hcollision
  intro i j
  exact
    charbonnelRestrictedGraph_maxwellOrderedScalarFiberEnumeration_mem_charbonnelClosure
      hC hp (baseCover.cell i).carrier_mem hA (hfiber i) j

end AbelFormalization
