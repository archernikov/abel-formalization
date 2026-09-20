import AbelFormalization.MaxwellPseudofunction
import AbelFormalization.CharbonnelClosureNullityWitnesses
import AbelFormalization.CharbonnelDescriptionAlgebra
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Empty interior of Maxwell directional quotient relations

The positive-zero-trace argument for a directional difference quotient needs
the quotient relation to have empty interior.  No continuity, openness of the
source domain, or family-membership hypothesis is needed for this fact.

If two different quotient slopes occur over the same `(x, epsilon)`, then at
least one of the source fibers over `x` and `x + epsilon e_i` is multivalued.
The exceptional quotient bases therefore lie in the union of two cylinders
over the source multivalued locus.  The second cylinder is the inverse image
of the first under an invertible linear shear, so both are Lebesgue null.
Thus a scalar pseudofunction has a scalar pseudofunction as its directional
quotient relation.

The final elementary topological lemma says that a scalar relation with null
multivalued locus has empty interior.  Indeed, a product box contained in the
relation supplies two distinct output values over an open set of bases,
contradicting nullity of the multivalued locus.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

/-! ## The endpoint shear and its null exceptional locus -/

/-- On quotient bases `(x, epsilon)`, replace `x` by `x + epsilon e_i` and
retain `epsilon`.  Its inverse subtracts the same displacement. -/
def maxwellDifferenceQuotientBaseShearLinearEquiv
    {p : ℕ} (i : Fin p) :
    RealEuclidean (p + 1) ≃ₗ[ℝ] RealEuclidean (p + 1) where
  toFun xepsilon :=
    realEuclideanAppend
      (realEuclideanTakeLeft xepsilon +
        (realEuclideanTakeRight xepsilon 0) •
          (Pi.single i 1 : RealEuclidean p))
      (realEuclideanTakeRight xepsilon)
  invFun xepsilon :=
    realEuclideanAppend
      (realEuclideanTakeLeft xepsilon -
        (realEuclideanTakeRight xepsilon 0) •
          (Pi.single i 1 : RealEuclidean p))
      (realEuclideanTakeRight xepsilon)
  left_inv xepsilon := by
    simp only [realEuclideanTakeLeft_append,
      realEuclideanTakeRight_append, add_sub_cancel_right]
    exact realEuclideanAppend_takeLeft_takeRight xepsilon
  right_inv xepsilon := by
    simp only [realEuclideanTakeLeft_append,
      realEuclideanTakeRight_append, sub_add_cancel]
    exact realEuclideanAppend_takeLeft_takeRight xepsilon
  map_add' v w := by
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
    · simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight, add_smul, add_assoc, add_left_comm,
        add_comm]
    · simp [realEuclideanAppend, realEuclideanTakeRight]
  map_smul' c v := by
    funext j
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) j
    · simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight, mul_smul]
      ring
    · simp [realEuclideanAppend, realEuclideanTakeRight]

@[simp]
theorem maxwellDifferenceQuotientBaseShearLinearEquiv_takeLeft
    {p : ℕ} (i : Fin p) (xepsilon : RealEuclidean (p + 1)) :
    realEuclideanTakeLeft
        (maxwellDifferenceQuotientBaseShearLinearEquiv i xepsilon) =
      realEuclideanTakeLeft xepsilon +
        (realEuclideanTakeRight xepsilon 0) •
          (Pi.single i 1 : RealEuclidean p) := by
  simp [maxwellDifferenceQuotientBaseShearLinearEquiv]

@[simp]
theorem maxwellDifferenceQuotientBaseShearLinearEquiv_takeRight
    {p : ℕ} (i : Fin p) (xepsilon : RealEuclidean (p + 1)) :
    realEuclideanTakeRight
        (maxwellDifferenceQuotientBaseShearLinearEquiv i xepsilon) =
      realEuclideanTakeRight xepsilon := by
  simp [maxwellDifferenceQuotientBaseShearLinearEquiv]

/-- The quotient bases for which at least one of the two endpoint fibers of
the source relation is multivalued. -/
def maxwellDifferenceQuotientEndpointBadLocus {p : ℕ}
    (R : MaxwellRelation p 1) (i : Fin p) :
    Set (RealEuclidean (p + 1)) :=
  {xepsilon |
    realEuclideanTakeLeft xepsilon ∈ maxwellMultivaluedLocus R ∨
      realEuclideanTakeLeft xepsilon +
          (realEuclideanTakeRight xepsilon 0) •
            (Pi.single i 1 : RealEuclidean p) ∈
        maxwellMultivaluedLocus R}

@[simp]
theorem mem_maxwellDifferenceQuotientEndpointBadLocus_iff
    {p : ℕ} (R : MaxwellRelation p 1) (i : Fin p)
    (xepsilon : RealEuclidean (p + 1)) :
    xepsilon ∈ maxwellDifferenceQuotientEndpointBadLocus R i ↔
      realEuclideanTakeLeft xepsilon ∈ maxwellMultivaluedLocus R ∨
        realEuclideanTakeLeft xepsilon +
            (realEuclideanTakeRight xepsilon 0) •
              (Pi.single i 1 : RealEuclidean p) ∈
          maxwellMultivaluedLocus R :=
  Iff.rfl

/-- The endpoint-bad locus is null whenever the source multivalued locus is
null.  The first endpoint gives a cylinder; the second is its pullback by the
invertible endpoint shear. -/
theorem maxwellDifferenceQuotientEndpointBadLocus_volume_eq_zero
    {p : ℕ} {R : MaxwellRelation p 1}
    (i : Fin p) (hR : IsMaxwellPseudofunction R) :
    (volume : Measure (RealEuclidean (p + 1)))
        (maxwellDifferenceQuotientEndpointBadLocus R i) = 0 := by
  let M := maxwellMultivaluedLocus R
  let C : Set (RealEuclidean (p + 1)) :=
    (realEuclideanDropLastLinearMap p) ⁻¹' M
  let E := maxwellDifferenceQuotientBaseShearLinearEquiv i
  have hC : (volume : Measure (RealEuclidean (p + 1))) C = 0 := by
    exact volume_dropLast_preimage_eq_zero hR
  have hEC : (volume : Measure (RealEuclidean (p + 1))) (E ⁻¹' C) = 0 := by
    calc
      (volume : Measure (RealEuclidean (p + 1))) (E ⁻¹' C) =
          ENNReal.ofReal
              |LinearMap.det
                (E.symm : RealEuclidean (p + 1) →ₗ[ℝ]
                  RealEuclidean (p + 1))| *
            (volume : Measure (RealEuclidean (p + 1))) C :=
        (volume : Measure (RealEuclidean (p + 1))).addHaar_preimage_linearEquiv
          E C
      _ = 0 := by rw [hC, mul_zero]
  have hbadEq : maxwellDifferenceQuotientEndpointBadLocus R i =
      C ∪ E ⁻¹' C := by
    ext xepsilon
    simp only [mem_maxwellDifferenceQuotientEndpointBadLocus_iff,
      Set.mem_union, Set.mem_preimage]
    change
      realEuclideanTakeLeft xepsilon ∈ M ∨
          realEuclideanTakeLeft xepsilon +
              (realEuclideanTakeRight xepsilon 0) •
                (Pi.single i 1 : RealEuclidean p) ∈ M ↔
        realEuclideanDropLastLinearMap p xepsilon ∈ M ∨
          realEuclideanDropLastLinearMap p (E xepsilon) ∈ M
    have hdrop (z : RealEuclidean (p + 1)) :
        realEuclideanDropLastLinearMap p z =
          realEuclideanTakeLeft z := by
      funext j
      rfl
    rw [hdrop xepsilon, hdrop (E xepsilon)]
    dsimp only [E]
    rw [maxwellDifferenceQuotientBaseShearLinearEquiv_takeLeft]
  rw [hbadEq]
  exact measure_union_null hC hEC

/-! ## Multivalued quotient fibers come from multivalued endpoints -/

/-- A one-coordinate real vector is determined by its zeroth coordinate. -/
theorem maxwellDifferenceQuotient_realEuclideanOne_eq_const
    (y : RealEuclidean 1) :
    y = (fun _ : Fin 1 ↦ y 0) := by
  funext j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  rfl

/-- If a directional quotient fiber has two values, then one of the two
source endpoint fibers is multivalued. -/
theorem maxwellDifferenceQuotient_multivaluedLocus_subset_endpointBadLocus
    {p : ℕ} (U : Set (RealEuclidean p)) (R : MaxwellRelation p 1)
    (i : Fin p) :
    maxwellMultivaluedLocus
        (maxwellDifferenceQuotientRelation U R i) ⊆
      maxwellDifferenceQuotientEndpointBadLocus R i := by
  rintro xepsilon ⟨y₁, y₂, hy₁, hy₂, hyne⟩
  let x : RealEuclidean p := realEuclideanTakeLeft xepsilon
  let epsilon : ℝ := realEuclideanTakeRight xepsilon 0
  have hxepsilon : xepsilon =
      realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon) := by
    calc
      xepsilon = realEuclideanAppend
          (realEuclideanTakeLeft xepsilon)
          (realEuclideanTakeRight xepsilon) :=
        (realEuclideanAppend_takeLeft_takeRight xepsilon).symm
      _ = realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon) := by
        congr 1
        exact maxwellDifferenceQuotient_realEuclideanOne_eq_const
          (realEuclideanTakeRight xepsilon)
  have hy₁' :
      realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
          (fun _ : Fin 1 ↦ y₁ 0) ∈
        maxwellDifferenceQuotientRelation U R i := by
    rw [← hxepsilon,
      ← maxwellDifferenceQuotient_realEuclideanOne_eq_const y₁]
    exact hy₁
  have hy₂' :
      realEuclideanAppend
          (realEuclideanAppend x (fun _ : Fin 1 ↦ epsilon))
          (fun _ : Fin 1 ↦ y₂ 0) ∈
        maxwellDifferenceQuotientRelation U R i := by
    rw [← hxepsilon,
      ← maxwellDifferenceQuotient_realEuclideanOne_eq_const y₂]
    exact hy₂
  obtain ⟨hxU, hxshiftU, hepsilon, z₁, z₂,
      hz₁, hz₂, heq₁⟩ :=
    (realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff
      U R i x epsilon (y₁ 0)).mp hy₁'
  obtain ⟨_hxU', _hxshiftU', _hepsilon', w₁, w₂,
      hw₁, hw₂, heq₂⟩ :=
    (realEuclideanAppend_append_mem_maxwellDifferenceQuotientRelation_iff
      U R i x epsilon (y₂ 0)).mp hy₂'
  by_contra hbad
  simp only [mem_maxwellDifferenceQuotientEndpointBadLocus_iff,
    not_or] at hbad
  have hz₁w₁ : z₁ = w₁ := by
    by_contra hne
    apply hbad.1
    exact ⟨(fun _ : Fin 1 ↦ z₁), (fun _ : Fin 1 ↦ w₁),
      hz₁, hw₁, fun h ↦ hne (congrFun h 0)⟩
  have hz₂w₂ : z₂ = w₂ := by
    by_contra hne
    apply hbad.2
    exact ⟨(fun _ : Fin 1 ↦ z₂), (fun _ : Fin 1 ↦ w₂),
      hz₂, hw₂, fun h ↦ hne (congrFun h 0)⟩
  have hscalar : y₁ 0 = y₂ 0 := by
    apply mul_left_cancel₀ hepsilon
    calc
      epsilon * y₁ 0 = z₂ - z₁ := heq₁
      _ = w₂ - w₁ := by rw [hz₁w₁, hz₂w₂]
      _ = epsilon * y₂ 0 := heq₂.symm
  apply hyne
  calc
    y₁ = (fun _ : Fin 1 ↦ y₁ 0) :=
      maxwellDifferenceQuotient_realEuclideanOne_eq_const y₁
    _ = (fun _ : Fin 1 ↦ y₂ 0) := by rw [hscalar]
    _ = y₂ :=
      (maxwellDifferenceQuotient_realEuclideanOne_eq_const y₂).symm

/-- A scalar Maxwell pseudofunction has a Maxwell-pseudofunction directional
quotient relation.  Its precise domain is irrelevant for this conclusion. -/
theorem isMaxwellPseudofunction_maxwellDifferenceQuotientRelation
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hR : IsMaxwellPseudofunction R) :
    IsMaxwellPseudofunction
      (maxwellDifferenceQuotientRelation U R i) := by
  unfold IsMaxwellPseudofunction
  exact measure_mono_null
    (maxwellDifferenceQuotient_multivaluedLocus_subset_endpointBadLocus
      U R i)
    (maxwellDifferenceQuotientEndpointBadLocus_volume_eq_zero i hR)

/-! ## Scalar pseudofunctions have empty interior -/

/-- A scalar relation whose multivalued locus is null has empty interior.
This uses no measurability assumption on the relation itself. -/
theorem interior_eq_empty_of_isMaxwellPseudofunction_scalar
    {p : ℕ} {G : MaxwellRelation p 1}
    (hG : IsMaxwellPseudofunction G) :
    interior G = ∅ := by
  have hmultivaluedInterior :
      interior (maxwellMultivaluedLocus G) = ∅ :=
    (volume : Measure (RealEuclidean p)).interior_eq_empty_of_null hG
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro w hw
  let E := (realEuclideanAppendLinearEquiv p 1).toContinuousLinearEquiv
  let xy : RealEuclidean p × RealEuclidean 1 := E.symm w
  have hEpre : E ⁻¹' interior G ∈ nhds xy := by
    apply E.continuous.continuousAt
    have hE : E xy = w := by simp [xy]
    rw [hE]
    exact isOpen_interior.mem_nhds hw
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hEpre
  let y : RealEuclidean 1 := xy.2
  let curve : ℝ → RealEuclidean 1 :=
    fun t _ ↦ y 0 + t
  have hcurveContinuous : Continuous curve := by
    apply continuous_pi
    intro j
    exact continuous_const.add continuous_id
  have hcurveZero : curve 0 = y := by
    funext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simp [curve, y]
  have hcurvePre : curve ⁻¹' B ∈ nhds 0 := by
    have hB' : B ∈ nhds (curve 0) := by rwa [hcurveZero]
    exact hcurveContinuous.continuousAt hB'
  obtain ⟨a, b, hab, hIoo⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp hcurvePre
  let t : ℝ := b / 2
  have htpos : 0 < t := by
    exact half_pos hab.2
  have htlt : t < b := by
    exact half_lt_self hab.2
  have hcurveZeroMem : curve 0 ∈ B := by
    exact hIoo ⟨hab.1, hab.2⟩
  have hcurveTMem : curve t ∈ B := by
    exact hIoo ⟨lt_trans hab.1 htpos, htlt⟩
  have hcurveNe : curve 0 ≠ curve t := by
    intro heq
    have hcoordinate := congrFun heq 0
    simp only [curve, add_zero] at hcoordinate
    have : t = 0 := by linarith
    exact ne_of_gt htpos this
  have hA_subset : A ⊆ maxwellMultivaluedLocus G := by
    intro x hx
    have hfirstInterior : E (x, curve 0) ∈ interior G :=
      hAB ⟨hx, hcurveZeroMem⟩
    have hsecondInterior : E (x, curve t) ∈ interior G :=
      hAB ⟨hx, hcurveTMem⟩
    refine ⟨curve 0, curve t, ?_, ?_, hcurveNe⟩
    · change realEuclideanAppend x (curve 0) ∈ G
      exact interior_subset hfirstInterior
    · change realEuclideanAppend x (curve t) ∈ G
      exact interior_subset hsecondInterior
  have hxyMultivalued : xy.1 ∈
      interior (maxwellMultivaluedLocus G) := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset hA hA_subset
  rw [hmultivaluedInterior] at hxyMultivalued
  exact hxyMultivalued

/-- The exact empty-interior premise required by the positive-zero-trace
argument follows from source pseudofunctionality alone. -/
theorem maxwellDifferenceQuotientRelation_interior_eq_empty
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (i : Fin p) (hR : IsMaxwellPseudofunction R) :
    interior (maxwellDifferenceQuotientRelation U R i) = ∅ :=
  interior_eq_empty_of_isMaxwellPseudofunction_scalar
    (isMaxwellPseudofunction_maxwellDifferenceQuotientRelation i hR)

/-- Convenient source-shaped specialization: a pseudofunction on `U`
supplies the quotient empty-interior premise through its null multivalued
locus.  Openness of `U` is not needed. -/
theorem IsMaxwellPseudofunctionOn.differenceQuotientRelation_interior_eq_empty
    {p : ℕ} {U : Set (RealEuclidean p)} {R : MaxwellRelation p 1}
    (hR : IsMaxwellPseudofunctionOn U R) (i : Fin p) :
    interior (maxwellDifferenceQuotientRelation U R i) = ∅ :=
  maxwellDifferenceQuotientRelation_interior_eq_empty i
    hR.multivalued_null

end AbelFormalization
