import AbelFormalization.LionRankPatchFixedSquareEncoding
import AbelFormalization.ReciprocalConstraintGraph

/-!
# Canonical Lagrange reduction for rank/minor patches

The canonical rank/minor patch of a fiber is cut out by three kinds of
conditions: the original fiber equations, the vanishing of every successor
minor, and one reciprocal equation for the selected nonzero minor.  This file
packages those equations as one fixed tuple, proves that its varying fibers
are homeomorphic to the rank/minor patches, and proves closure of the tuple in
every derivative-closed geometric family.

The remaining input is stated at the precise point where the existing smooth
constant-rank and reciprocal-graph arguments stop.  It asks for a regular
Lagrange lift of a squared-distance minimizer on every connected component of
the canonical closed fiber.  From that input the fixed square encoder is
constructed explicitly.  Thus the residual is a singular constrained-Morse
statement for a concrete tuple of fiber, successor-minor, and reciprocal
equations; it is not another name for the desired encoder.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## A generic regular-Lagrange-lift constructor -/

/-- A fiberwise constrained-Morse property for a fixed constraint tuple.

For every target one may choose a squared-distance center.  Every minimizer
of that distance on a connected component of the fiber must have a
multiplier which solves the Lagrange system and is a regular point of that
square system.  The center may depend on the target, while the constraint
tuple and the parameter-recording square map remain fixed. -/
def HasRegularLagrangeLiftsAtComponentMinima
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a) : Prop :=
  ∀ t : RealEuclidean k,
    ∃ center : RealEuclidean a,
      ∀ x : constraintMap H ⁻¹' {t},
        x ∈ componentMinimizers
            (fun y : constraintMap H ⁻¹' {t} ↦
              standardSquaredDistance center (y : RealEuclidean a)) →
          ∃ lambda : RealEuclidean k,
            let z : RealEuclidean (a + k) :=
              realEuclideanAppend (x : RealEuclidean a) lambda
            lagrangeCriticalSystemMap H
                (standardSquaredDistance center) z =
              realEuclideanAppend (0 : RealEuclidean a) t ∧
            (fderiv ℝ (lagrangeCriticalSystemMap H
              (standardSquaredDistance center)) z).range = ⊤

/-- Regular Lagrange lifts at componentwise distance minima produce the
fixed-square component encoder used by Lion's uniform argument. -/
noncomputable def
    fixedSquareRegularFiberComponentEncoding_of_regularLagrangeLifts
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a k : ℕ} (H : Fin k → RealEuclideanFunction a)
    (hHmem : ∀ i, H i ∈ G a)
    (hlifts : HasRegularLagrangeLiftsAtComponentMinima H) :
    FixedSquareRegularFiberComponentEncoding G (constraintMap H) := by
  classical
  have hHinf : ∀ i, ContDiff ℝ ∞ (H i) :=
    fun i ↦ hsmooth a (H i) (hHmem i)
  have hH2 : ∀ i, ContDiff ℝ 2 (H i) :=
    fun i ↦ (hHinf i).of_le (by norm_num)
  have hconstraintC1 : ContDiff ℝ 1 (constraintMap H) := by
    rw [contDiff_pi]
    intro i
    exact (hHinf i).of_le (by norm_num)
  let squareMap : RealEuclidean ((a + k) + a) →
      RealEuclidean ((a + k) + a) :=
    lagrangeParameterRecordingSquareMap H
  have hsquareMem : FunctionTupleInFamily G squareMap :=
    hG.lagrangeParameterRecordingSquareMap_mem hderiv H hHmem
  have hfamilyC1 : ContDiff ℝ 1
      (lagrangeSquaredDistanceCriticalFamily H) :=
    contDiff_lagrangeSquaredDistanceCriticalFamily H hH2
  have hsquareC1 : ContDiff ℝ 1 squareMap :=
    contDiff_flatParameterRecordingMap hfamilyC1
  let center : RealEuclidean k → RealEuclidean a :=
    fun t ↦ Classical.choose (hlifts t)
  have hcenter : ∀ t : RealEuclidean k,
      ∀ x : constraintMap H ⁻¹' {t},
        x ∈ componentMinimizers
            (fun y : constraintMap H ⁻¹' {t} ↦
              standardSquaredDistance (center t) (y : RealEuclidean a)) →
          ∃ lambda : RealEuclidean k,
            let z : RealEuclidean (a + k) :=
              realEuclideanAppend (x : RealEuclidean a) lambda
            lagrangeCriticalSystemMap H
                (standardSquaredDistance (center t)) z =
              realEuclideanAppend (0 : RealEuclidean a) t ∧
            (fderiv ℝ (lagrangeCriticalSystemMap H
              (standardSquaredDistance (center t))) z).range = ⊤ := by
    intro t
    exact Classical.choose_spec (hlifts t)
  let fiberTarget : RealEuclidean k → RealEuclidean ((a + k) + a) :=
    fun t ↦ realEuclideanAppend
      (realEuclideanAppend (0 : RealEuclidean a) t) (center t)
  have hpick : ∀ t : RealEuclidean k,
      ∃ pick : ConnectedComponents (constraintMap H ⁻¹' {t}) →
          smoothRegularFiber squareMap (fiberTarget t),
        Function.Injective pick := by
    intro t
    let M : Set (RealEuclidean a) := constraintMap H ⁻¹' {t}
    let rho : RealEuclideanFunction a :=
      standardSquaredDistance (center t)
    have hMclosed : IsClosed M :=
      isClosed_singleton.preimage hconstraintC1.continuous
    have hrhoMem : rho ∈ G a := by
      simpa only [rho, standardSquaredDistance] using
        hG.standardSquaredDistance_mem (center t)
    have hrhoInf : ContDiff ℝ ∞ rho :=
      hsmooth a rho hrhoMem
    have hcompact : ∀ R : ℝ,
        IsCompact {x : M | rho (x : RealEuclidean a) ≤ R} := by
      intro R
      apply isCompact_subtype_sublevel_of_isClosed hMclosed rho
      intro c
      simpa only [rho, standardSquaredDistance] using
        isCompact_algebraicSquaredDistance_basis_sublevel
          (Pi.basisFun ℝ (Fin a)) (center t) c
    let base : smoothRegularFiber squareMap (fiberTarget t) → M :=
      fun v ↦ ⟨lagrangePrimalProjection a k
          (realEuclideanTakeLeft (v : RealEuclidean ((a + k) + a))), by
        have hv : squareMap
            (v : RealEuclidean ((a + k) + a)) = fiberTarget t :=
          v.property.1
        change constraintMap H (lagrangePrimalProjection a k
          (realEuclideanTakeLeft (v : RealEuclidean ((a + k) + a)))) = t
        funext i
        have hcoordinate := congrFun hv
          (Fin.castAdd a (Fin.natAdd a i))
        simpa only [squareMap, fiberTarget,
          lagrangeParameterRecordingSquareMap_constraint,
          realEuclideanAppend_castAdd, realEuclideanAppend_natAdd,
          constraintMap] using hcoordinate⟩
    have hlift : ∀ x : M,
        x ∈ componentMinimizers
          (fun y : M ↦ rho (y : RealEuclidean a)) →
        ∃ v : smoothRegularFiber squareMap (fiberTarget t),
          base v = x := by
      intro x hmin
      obtain ⟨lambda, hsystem, hregular⟩ := hcenter t x (by
        simpa only [M, rho] using hmin)
      let z : RealEuclidean (a + k) :=
        realEuclideanAppend (x : RealEuclidean a) lambda
      let v : RealEuclidean ((a + k) + a) :=
        realEuclideanAppend z (center t)
      have hvvalue : squareMap v = fiberTarget t := by
        simpa only [squareMap, fiberTarget, v, z,
          lagrangeParameterRecordingSquareMap_append] using
            congrArg (fun w ↦ realEuclideanAppend w (center t)) hsystem
      have hfamilyAt : DifferentiableAt ℝ
          (lagrangeSquaredDistanceCriticalFamily H) (z, center t) :=
        (hfamilyC1.differentiable (by norm_num)).differentiableAt
      have hpartial : Function.Surjective
          (fstPartial (fderiv ℝ
            (lagrangeSquaredDistanceCriticalFamily H) (z, center t))) := by
        rw [← fderiv_lagrangeSquaredDistanceCriticalFamily_fixed_center
          H z (center t) hfamilyAt]
        exact LinearMap.range_eq_top.mp (by
          simpa only [z] using hregular)
      have hvderiv : Function.Surjective (fderiv ℝ squareMap v) := by
        simpa only [squareMap, lagrangeParameterRecordingSquareMap, v] using
          surjective_fderiv_flatParameterRecordingMap hfamilyAt hpartial
      have hvregular : v ∈ smoothRegularFiber squareMap
          (fiberTarget t) :=
        (mem_smoothRegularFiber_iff_of_contDiff_square
          squareMap hsquareC1 (fiberTarget t) v).mpr
          ⟨hvvalue, hvderiv⟩
      refine ⟨⟨v, hvregular⟩, ?_⟩
      apply Subtype.ext
      change lagrangePrimalProjection a k
          (realEuclideanTakeLeft v) = (x : RealEuclidean a)
      rw [show realEuclideanTakeLeft v = z by
        exact realEuclideanTakeLeft_append z (center t)]
      exact lagrangePrimalProjection_append (x : RealEuclidean a) lambda
    have hmeet : ∀ x : M,
        ∃ v : smoothRegularFiber squareMap (fiberTarget t),
          base v ∈ connectedComponent x := by
      intro x
      obtain ⟨y, hycomponent, hymin⟩ :=
        exists_componentMinimizer_of_compact_sublevel
          (fun y : M ↦ rho (y : RealEuclidean a))
          (hrhoInf.continuous.comp continuous_subtype_val)
          hcompact x
      obtain ⟨v, hvbase⟩ := hlift y hymin
      exact ⟨v, by simpa only [hvbase] using hycomponent⟩
    exact exists_injective_connectedComponents_to_lifts base hmeet
  exact
    { dimension := (a + k) + a
      squareMap := squareMap
      fiberTarget := fiberTarget
      squareMap_mem := hsquareMem
      encode := fun t ↦ Classical.choose (hpick t)
      encode_injective := fun t ↦ Classical.choose_spec (hpick t) }

/-! ## The canonical closed reciprocal/minor system -/

/-- Indices of the successor minors imposing derivative rank at most `k`. -/
abbrev SuccessorMinorIndex (a b k : ℕ) :=
  (Fin (k + 1) ↪ Fin b) × (Fin (k + 1) ↪ Fin a)

/-- Number of successor-minor equations. -/
abbrev successorMinorCount (a b k : ℕ) :=
  Fintype.card (SuccessorMinorIndex a b k)

/-- A fixed enumeration of all successor minors. -/
noncomputable def successorMinorEquiv (a b k : ℕ) :
    Fin (successorMinorCount a b k) ≃ SuccessorMinorIndex a b k :=
  (Fintype.equivFin (SuccessorMinorIndex a b k)).symm

/-- The fixed closed constraint tuple attached to a rank/minor patch.

Its first block is the original map, its second block lists all successor
minors, and its final coordinate is `u * q(x)` for the selected minor `q`.
The target will be `(t, 0, 1)`. -/
def rankMinorPatchConstraintTuple {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b)
    (i : RankMinorPatchIndex a b) :
    Fin ((b + successorMinorCount a b (i.1 : ℕ)) + 1) →
      RealEuclideanFunction (a + 1) :=
  functionTupleSnoc
    (Fin.addCases
      (fun j z ↦ g (lagrangePrimalProjection a 1 z) j)
      (fun r z ↦
        let rc := successorMinorEquiv a b (i.1 : ℕ) r
        standardJacobianMinor g rc.1 rc.2
          (lagrangePrimalProjection a 1 z)))
    (fun z ↦ z (Fin.natAdd a (0 : Fin 1)) *
      standardJacobianMinor g i.2.1 i.2.2
        (lagrangePrimalProjection a 1 z))

/-- The target `(t, 0, 1)` of the canonical closed constraint tuple. -/
def rankMinorPatchConstraintTarget {a b : ℕ}
    (i : RankMinorPatchIndex a b) (t : RealEuclidean b) :
    RealEuclidean ((b + successorMinorCount a b (i.1 : ℕ)) + 1) :=
  Fin.lastCases 1
    (Fin.addCases (fun j ↦ t j)
      (fun _ : Fin (successorMinorCount a b (i.1 : ℕ)) ↦ 0))

@[simp]
theorem rankMinorPatchConstraintTuple_original {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b)
    (i : RankMinorPatchIndex a b) (z : RealEuclidean (a + 1))
    (j : Fin b) :
    rankMinorPatchConstraintTuple g i
        (Fin.castSucc (Fin.castAdd (successorMinorCount a b (i.1 : ℕ)) j)) z =
      g (lagrangePrimalProjection a 1 z) j := by
  simp [rankMinorPatchConstraintTuple]

@[simp]
theorem rankMinorPatchConstraintTuple_successor {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b)
    (i : RankMinorPatchIndex a b) (z : RealEuclidean (a + 1))
    (r : Fin (successorMinorCount a b (i.1 : ℕ))) :
    rankMinorPatchConstraintTuple g i
        (Fin.castSucc (Fin.natAdd b r)) z =
      let rc := successorMinorEquiv a b (i.1 : ℕ) r
      standardJacobianMinor g rc.1 rc.2
        (lagrangePrimalProjection a 1 z) := by
  let q : Fin (b + successorMinorCount a b (i.1 : ℕ)) :=
    Fin.natAdd b r
  change rankMinorPatchConstraintTuple g i q.castSucc z = _
  rw [rankMinorPatchConstraintTuple, functionTupleSnoc_castSucc]
  simp only [q, Fin.addCases_right]

@[simp]
theorem rankMinorPatchConstraintTuple_reciprocal {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b)
    (i : RankMinorPatchIndex a b) (z : RealEuclidean (a + 1)) :
    rankMinorPatchConstraintTuple g i
        (Fin.last (b + successorMinorCount a b (i.1 : ℕ))) z =
      z (Fin.natAdd a (0 : Fin 1)) *
        standardJacobianMinor g i.2.1 i.2.2
          (lagrangePrimalProjection a 1 z) := by
  simp [rankMinorPatchConstraintTuple]

@[simp]
theorem rankMinorPatchConstraintTarget_original {a b : ℕ}
    (i : RankMinorPatchIndex a b) (t : RealEuclidean b) (j : Fin b) :
    rankMinorPatchConstraintTarget i t
        (Fin.castSucc (Fin.castAdd (successorMinorCount a b (i.1 : ℕ)) j)) =
      t j := by
  simp [rankMinorPatchConstraintTarget]

@[simp]
theorem rankMinorPatchConstraintTarget_successor {a b : ℕ}
    (i : RankMinorPatchIndex a b) (t : RealEuclidean b)
    (r : Fin (successorMinorCount a b (i.1 : ℕ))) :
    rankMinorPatchConstraintTarget i t (Fin.castSucc (Fin.natAdd b r)) = 0 := by
  let q : Fin (b + successorMinorCount a b (i.1 : ℕ)) :=
    Fin.natAdd b r
  change (@Fin.lastCases (b + successorMinorCount a b (i.1 : ℕ))
    (fun _ ↦ ℝ) (1 : ℝ)
    (@Fin.addCases b (successorMinorCount a b (i.1 : ℕ))
      (fun _ ↦ ℝ) (fun j ↦ t j) (fun _ ↦ (0 : ℝ)))
      q.castSucc) = (0 : ℝ)
  rw [Fin.lastCases_castSucc]
  simp [q]

@[simp]
theorem rankMinorPatchConstraintTarget_reciprocal {a b : ℕ}
    (i : RankMinorPatchIndex a b) (t : RealEuclidean b) :
    rankMinorPatchConstraintTarget i t
        (Fin.last (b + successorMinorCount a b (i.1 : ℕ))) = 1 := by
  simp [rankMinorPatchConstraintTarget]

/-- Coordinatewise characterization of a canonical constraint fiber. -/
theorem rankMinorPatchConstraintTuple_eq_target_iff {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b)
    (i : RankMinorPatchIndex a b) (t : RealEuclidean b)
    (z : RealEuclidean (a + 1)) :
    constraintMap (rankMinorPatchConstraintTuple g i) z =
        rankMinorPatchConstraintTarget i t ↔
      g (lagrangePrimalProjection a 1 z) = t ∧
      (∀ rows : Fin ((i.1 : ℕ) + 1) ↪ Fin b,
        ∀ cols : Fin ((i.1 : ℕ) + 1) ↪ Fin a,
          standardJacobianMinor g rows cols
            (lagrangePrimalProjection a 1 z) = 0) ∧
      z (Fin.natAdd a (0 : Fin 1)) *
        standardJacobianMinor g i.2.1 i.2.2
          (lagrangePrimalProjection a 1 z) = 1 := by
  constructor
  · intro hz
    have horiginal : g (lagrangePrimalProjection a 1 z) = t := by
      funext j
      have hj := congrFun hz
        (Fin.castSucc (Fin.castAdd
          (successorMinorCount a b (i.1 : ℕ)) j))
      simpa only [constraintMap,
        rankMinorPatchConstraintTuple_original,
        rankMinorPatchConstraintTarget_original] using hj
    have hsuccessor : ∀ rows : Fin ((i.1 : ℕ) + 1) ↪ Fin b,
        ∀ cols : Fin ((i.1 : ℕ) + 1) ↪ Fin a,
          standardJacobianMinor g rows cols
            (lagrangePrimalProjection a 1 z) = 0 := by
      intro rows cols
      let rc : SuccessorMinorIndex a b (i.1 : ℕ) := (rows, cols)
      let r : Fin (successorMinorCount a b (i.1 : ℕ)) :=
        (successorMinorEquiv a b (i.1 : ℕ)).symm rc
      have hr := congrFun hz (Fin.castSucc (Fin.natAdd b r))
      simpa only [constraintMap,
        rankMinorPatchConstraintTuple_successor,
        rankMinorPatchConstraintTarget_successor,
        r, rc, Equiv.apply_symm_apply] using hr
    have hreciprocal := congrFun hz
      (Fin.last (b + successorMinorCount a b (i.1 : ℕ)))
    exact ⟨horiginal, hsuccessor, by
      simpa only [constraintMap,
        rankMinorPatchConstraintTuple_reciprocal,
        rankMinorPatchConstraintTarget_reciprocal] using hreciprocal⟩
  · rintro ⟨horiginal, hsuccessor, hreciprocal⟩
    funext r
    refine Fin.lastCases ?_ (fun q ↦ ?_) r
    · simpa only [constraintMap,
        rankMinorPatchConstraintTuple_reciprocal,
        rankMinorPatchConstraintTarget_reciprocal] using hreciprocal
    · refine Fin.addCases (fun j ↦ ?_) (fun s ↦ ?_) q
      · simpa only [constraintMap,
          rankMinorPatchConstraintTuple_original,
          rankMinorPatchConstraintTarget_original] using congrFun horiginal j
      · let rc := successorMinorEquiv a b (i.1 : ℕ) s
        simpa only [constraintMap,
          rankMinorPatchConstraintTuple_successor,
          rankMinorPatchConstraintTarget_successor, rc] using
            hsuccessor rc.1 rc.2

/-- The canonical rank/minor patch is homeomorphic to the corresponding
fiber of the fixed closed reciprocal/minor constraint tuple. -/
def rankMinorFiberPatchHomeomorph {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b)
    (hg : ContDiff ℝ 1 g) (t : RealEuclidean b)
    (i : RankMinorPatchIndex a b) :
    rankMinorFiberPatch g t i ≃ₜ
      constraintMap (rankMinorPatchConstraintTuple g i) ⁻¹'
        {rankMinorPatchConstraintTarget i t} where
  toFun x := ⟨realEuclideanAppendScalar (x : RealEuclidean a)
      (standardJacobianMinor g i.2.1 i.2.2 x)⁻¹, by
    rw [Set.mem_preimage, Set.mem_singleton_iff,
      rankMinorPatchConstraintTuple_eq_target_iff]
    have hx := (mem_rankMinorFiberPatch_iff_successorMinors
      g hg t i x).mp x.property
    refine ⟨?_, ?_, ?_⟩
    · simpa only [realEuclideanAppendScalar,
        lagrangePrimalProjection_append] using
          Set.mem_singleton_iff.mp x.1.property
    · simpa only [realEuclideanAppendScalar,
        lagrangePrimalProjection_append] using hx.2
    · simp only [realEuclideanAppendScalar,
        lagrangePrimalProjection_append, realEuclideanAppend_natAdd]
      exact inv_mul_cancel₀ hx.1⟩
  invFun z := by
    let x : g ⁻¹' {t} := ⟨lagrangePrimalProjection a 1 z, by
      have hz := (rankMinorPatchConstraintTuple_eq_target_iff
        g i t z).mp (Set.mem_singleton_iff.mp z.property)
      exact Set.mem_singleton_iff.mpr hz.1⟩
    refine ⟨x, ?_⟩
    apply (mem_rankMinorFiberPatch_iff_successorMinors g hg t i x).mpr
    have hz := (rankMinorPatchConstraintTuple_eq_target_iff
      g i t z).mp (Set.mem_singleton_iff.mp z.property)
    refine ⟨?_, hz.2.1⟩
    intro hzero
    have hproduct := hz.2.2
    rw [hzero, mul_zero] at hproduct
    exact zero_ne_one hproduct
  left_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact lagrangePrimalProjection_append (x : RealEuclidean a)
      (fun _ : Fin 1 ↦
        (standardJacobianMinor g i.2.1 i.2.2 x)⁻¹)
  right_inv := by
    intro z
    apply Subtype.ext
    have hz := (rankMinorPatchConstraintTuple_eq_target_iff
      g i t z).mp (Set.mem_singleton_iff.mp z.property)
    have hlast : z.1 (Fin.natAdd a (0 : Fin 1)) =
        (standardJacobianMinor g i.2.1 i.2.2
          (lagrangePrimalProjection a 1 z))⁻¹ :=
      eq_inv_of_mul_eq_one_left hz.2.2
    funext r
    refine Fin.addCases (fun j ↦ ?_) (fun q ↦ ?_) r
    · simp [realEuclideanAppendScalar]
    · have hq : q = (0 : Fin 1) := Subsingleton.elim _ _
      subst q
      simpa [realEuclideanAppendScalar] using hlast.symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hval : Continuous
        (fun x : rankMinorFiberPatch g t i ↦ (x : RealEuclidean a)) :=
      (continuous_subtype_val : Continuous
        (Subtype.val : g ⁻¹' {t} → RealEuclidean a)).comp
        (continuous_subtype_val : Continuous
          (Subtype.val : rankMinorFiberPatch g t i → g ⁻¹' {t}))
    have hminorContinuous : Continuous
        (standardJacobianMinor g i.2.1 i.2.2) :=
      continuous_standardJacobianMinor_of_contDiff_one hg i.2.1 i.2.2
    have hinv : Continuous
        (fun x : rankMinorFiberPatch g t i ↦
          (standardJacobianMinor g i.2.1 i.2.2 x)⁻¹) := by
      apply Continuous.inv₀
      · exact hminorContinuous.comp hval
      · intro x
        exact x.property.2
    change Continuous
      (realEuclideanAppendScalarContinuousLinearEquiv a ∘
        (fun x : rankMinorFiberPatch g t i ↦
          ((x : RealEuclidean a),
            (standardJacobianMinor g i.2.1 i.2.2 x)⁻¹)))
    exact (realEuclideanAppendScalarContinuousLinearEquiv a).continuous.comp
      (hval.prodMk hinv)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (lagrangePrimalProjectionCLM a 1).continuous.comp
      continuous_subtype_val

/-- Every coordinate of the canonical closed reciprocal/minor tuple remains
in a geometric family closed under coordinate differentiation. -/
theorem IsGeometricFunctionFamily.rankMinorPatchConstraintTuple_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g)
    (i : RankMinorPatchIndex a b) :
    ∀ r, rankMinorPatchConstraintTuple g i r ∈ G (a + 1) := by
  intro r
  refine Fin.lastCases ?_ (fun q ↦ ?_) r
  · have hcoordinate :
        (fun z : RealEuclidean (a + 1) ↦
          z (Fin.natAdd a (0 : Fin 1))) ∈ G (a + 1) := by
      simpa using hG.polynomial
        (MvPolynomial.X (Fin.natAdd a (0 : Fin 1)))
    have hminor : standardJacobianMinor g i.2.1 i.2.2 ∈ G a :=
      hG.standardJacobianMinor_mem hderiv g hg i.2.1 i.2.2
    have hpull :
        (fun z : RealEuclidean (a + 1) ↦
          standardJacobianMinor g i.2.1 i.2.2
            (lagrangePrimalProjection a 1 z)) ∈ G (a + 1) := by
      change (standardJacobianMinor g i.2.1 i.2.2 ∘
        (lagrangePrimalProjection a 1).toAffineMap) ∈ G (a + 1)
      exact hG.affine_comp hminor (lagrangePrimalProjection a 1).toAffineMap
    rw [show rankMinorPatchConstraintTuple g i
        (Fin.last (b + successorMinorCount a b (i.1 : ℕ))) =
        (fun z ↦ z (Fin.natAdd a (0 : Fin 1)) *
          standardJacobianMinor g i.2.1 i.2.2
            (lagrangePrimalProjection a 1 z)) by
      funext z
      exact rankMinorPatchConstraintTuple_reciprocal g i z]
    exact hG.mul hcoordinate hpull
  · refine Fin.addCases (fun j ↦ ?_) (fun s ↦ ?_) q
    · rw [show rankMinorPatchConstraintTuple g i
          (Fin.castSucc
            (Fin.castAdd (successorMinorCount a b (i.1 : ℕ)) j)) =
          (fun z : RealEuclidean (a + 1) ↦
            g (lagrangePrimalProjection a 1 z) j) by
        funext z
        exact rankMinorPatchConstraintTuple_original g i z j]
      change ((fun x ↦ g x j) ∘
        (lagrangePrimalProjection a 1).toAffineMap) ∈ G (a + 1)
      exact hG.affine_comp (hg j) (lagrangePrimalProjection a 1).toAffineMap
    · let rc := successorMinorEquiv a b (i.1 : ℕ) s
      have hminor : standardJacobianMinor g rc.1 rc.2 ∈ G a :=
        hG.standardJacobianMinor_mem hderiv g hg rc.1 rc.2
      rw [show rankMinorPatchConstraintTuple g i
          (Fin.castSucc (Fin.natAdd b s)) =
          (fun z : RealEuclidean (a + 1) ↦
            standardJacobianMinor g rc.1 rc.2
              (lagrangePrimalProjection a 1 z)) by
        funext z
        simpa only [rc] using
          rankMinorPatchConstraintTuple_successor g i z s]
      change (standardJacobianMinor g rc.1 rc.2 ∘
        (lagrangePrimalProjection a 1).toAffineMap) ∈ G (a + 1)
      exact hG.affine_comp hminor (lagrangePrimalProjection a 1).toAffineMap

/-- A homeomorphism induces an injective map on connected components. -/
theorem Homeomorph.connectedComponentsMap_injective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) :
    Function.Injective e.continuous.connectedComponentsMap := by
  have hfib : ∀ y : Y, IsConnected (e ⁻¹' {y}) := by
    intro y
    have hset : e ⁻¹' {y} = {e.symm y} := by
      ext x
      change e x = y ↔ x = e.symm y
      constructor
      · intro hxy
        rw [← e.symm_apply_apply x]
        exact congrArg e.symm hxy
      · rintro rfl
        exact e.apply_symm_apply y
    rw [hset]
    exact isConnected_singleton
  exact (e.isQuotientMap.isCoinducing.connectedComponentsMap_bijective
    hfib).1

/-! ## Finite subtuple Lagrange charts -/

/-- Candidate constraint subtuples for a canonical rank/minor system.

The lifted canonical source has dimension `a + 1`.  A regular constraint
subtuple can therefore have at most `a + 1` equations.  We enumerate every
such size and every embedding into the full canonical equation tuple. -/
abbrev RankMinorLagrangeChartIndex (a b : ℕ)
    (i : RankMinorPatchIndex a b) :=
  Σ r : Fin ((a + 1) + 1),
    Fin (r : ℕ) ↪
      Fin ((b + successorMinorCount a b (i.1 : ℕ)) + 1)

/-- The constraint subtuple selected by one finite Lagrange chart. -/
def rankMinorPatchLagrangeSubtuple {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b)
    (i : RankMinorPatchIndex a b)
    (chart : RankMinorLagrangeChartIndex a b i) :
    Fin (chart.1 : ℕ) → RealEuclideanFunction (a + 1) :=
  fun j ↦ rankMinorPatchConstraintTuple g i (chart.2 j)

/-- The corresponding coordinates of the canonical target `(t, 0, 1)`. -/
def rankMinorPatchLagrangeSubtarget {a b : ℕ}
    (i : RankMinorPatchIndex a b) (t : RealEuclidean b)
    (chart : RankMinorLagrangeChartIndex a b i) :
    RealEuclidean (chart.1 : ℕ) :=
  fun j ↦ rankMinorPatchConstraintTarget i t (chart.2 j)

/-- The fixed parameter-recording Lagrange square map for one candidate
subtuple. -/
def rankMinorPatchLagrangeSquareMap {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b)
    (i : RankMinorPatchIndex a b)
    (chart : RankMinorLagrangeChartIndex a b i) :
    RealEuclidean (((a + 1) + (chart.1 : ℕ)) + (a + 1)) →
      RealEuclidean (((a + 1) + (chart.1 : ℕ)) + (a + 1)) :=
  lagrangeParameterRecordingSquareMap
    (rankMinorPatchLagrangeSubtuple g i chart)

/-- The regular-fiber target determined by a canonical target and a chosen
squared-distance center. -/
def rankMinorPatchLagrangeSquareTarget {a b : ℕ}
    (i : RankMinorPatchIndex a b) (t : RealEuclidean b)
    (chart : RankMinorLagrangeChartIndex a b i)
    (center : RealEuclidean (a + 1)) :
    RealEuclidean (((a + 1) + (chart.1 : ℕ)) + (a + 1)) :=
  realEuclideanAppend
    (realEuclideanAppend (0 : RealEuclidean (a + 1))
      (rankMinorPatchLagrangeSubtarget i t chart)) center

/-- The exact stratified constrained-Morse input left by the canonical
reduction.

For each chart and target a center is fixed before components are considered.
Every component of the full canonical closed fiber must contain a point
which has a regular Lagrange lift for one source-sized subtuple.  The point
still lies in the full fiber; the selected subtuple is used only as its local
critical certificate.  This permits different rank strata to use different
independent equations while keeping a finite collection of fixed square
maps. -/
structure CanonicalRankMinorFiniteRegularLagrangeCover
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b) where
  center : ∀ i : RankMinorPatchIndex a b,
    RankMinorLagrangeChartIndex a b i →
      RealEuclidean b → RealEuclidean (a + 1)
  component_lift :
    ∀ (i : RankMinorPatchIndex a b) (t : RealEuclidean b)
      (x : constraintMap (rankMinorPatchConstraintTuple g i) ⁻¹'
        {rankMinorPatchConstraintTarget i t}),
      ∃ (chart : RankMinorLagrangeChartIndex a b i)
        (y : constraintMap (rankMinorPatchConstraintTuple g i) ⁻¹'
          {rankMinorPatchConstraintTarget i t})
        (lambda : RealEuclidean (chart.1 : ℕ)),
        y ∈ connectedComponent x ∧
        let H := rankMinorPatchLagrangeSubtuple g i chart
        let z : RealEuclidean ((a + 1) + (chart.1 : ℕ)) :=
          realEuclideanAppend (y : RealEuclidean (a + 1)) lambda
        lagrangeCriticalSystemMap H
            (standardSquaredDistance (center i chart t)) z =
          realEuclideanAppend (0 : RealEuclidean (a + 1))
            (rankMinorPatchLagrangeSubtarget i t chart) ∧
        (fderiv ℝ (lagrangeCriticalSystemMap H
          (standardSquaredDistance (center i chart t))) z).range = ⊤

/-- Family-level form of the finite-subtuple regular-Lagrange cover. -/
def HasCanonicalRankMinorFiniteRegularLagrangeCoversForFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ a b (g : RealEuclidean a → RealEuclidean b),
    FunctionTupleInFamily G g →
      Nonempty (CanonicalRankMinorFiniteRegularLagrangeCover g)

/-- Every chart square map remains in the same geometric,
coordinate-derivative-closed family. -/
theorem IsGeometricFunctionFamily.rankMinorPatchLagrangeSquareMap_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g)
    (i : RankMinorPatchIndex a b)
    (chart : RankMinorLagrangeChartIndex a b i) :
    FunctionTupleInFamily G
      (rankMinorPatchLagrangeSquareMap g i chart) := by
  exact hG.lagrangeParameterRecordingSquareMap_mem hderiv
    (rankMinorPatchLagrangeSubtuple g i chart)
    (fun j ↦ hG.rankMinorPatchConstraintTuple_mem hderiv g hg i (chart.2 j))

/-- A finite regular-Lagrange cover gives an injection from the components
of one canonical rank/minor patch into the dependent sum of its chartwise
regular fibers. -/
theorem exists_injective_rankMinorPatch_components_to_lagrangeCharts
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g)
    (cover : CanonicalRankMinorFiniteRegularLagrangeCover g)
    (i : RankMinorPatchIndex a b) (t : RealEuclidean b) :
    ∃ encode : ConnectedComponents (rankMinorFiberPatch g t i) →
        Σ chart : RankMinorLagrangeChartIndex a b i,
          smoothRegularFiber
            (rankMinorPatchLagrangeSquareMap g i chart)
            (rankMinorPatchLagrangeSquareTarget i t chart
              (cover.center i chart t)),
      Function.Injective encode := by
  classical
  let M : Set (RealEuclidean (a + 1)) :=
    constraintMap (rankMinorPatchConstraintTuple g i) ⁻¹'
      {rankMinorPatchConstraintTarget i t}
  let Lift := Σ chart : RankMinorLagrangeChartIndex a b i,
    smoothRegularFiber
      (rankMinorPatchLagrangeSquareMap g i chart)
      (rankMinorPatchLagrangeSquareTarget i t chart
        (cover.center i chart t))
  have hpickM : ∃ pick : ConnectedComponents M → Lift,
      Function.Injective pick := by
    by_cases hM : M.Nonempty
    · let x0 : M := ⟨Classical.choose hM, Classical.choose_spec hM⟩
      let primal : Lift → RealEuclidean (a + 1) := fun p ↦
        lagrangePrimalProjection (a + 1) (p.1.1 : ℕ)
          (realEuclideanTakeLeft
            (p.2 : RealEuclidean
              (((a + 1) + (p.1.1 : ℕ)) + (a + 1))))
      let base : Lift → M := fun p ↦
        if hp : primal p ∈ M then ⟨primal p, hp⟩ else x0
      have hmeet : ∀ x : M, ∃ v : Lift,
          base v ∈ connectedComponent x := by
        intro x
        obtain ⟨chart, y, lambda, hycomponent, hsystem, hregular⟩ :=
          cover.component_lift i t x
        let H := rankMinorPatchLagrangeSubtuple g i chart
        let squareMap := rankMinorPatchLagrangeSquareMap g i chart
        let center := cover.center i chart t
        let target := rankMinorPatchLagrangeSquareTarget i t chart center
        let z : RealEuclidean ((a + 1) + (chart.1 : ℕ)) :=
          realEuclideanAppend (y : RealEuclidean (a + 1)) lambda
        let v : RealEuclidean
            (((a + 1) + (chart.1 : ℕ)) + (a + 1)) :=
          realEuclideanAppend z center
        have hHmem : ∀ j, H j ∈ G (a + 1) := by
          intro j
          exact hG.rankMinorPatchConstraintTuple_mem hderiv g hg i
            (chart.2 j)
        have hH2 : ∀ j, ContDiff ℝ 2 (H j) := by
          intro j
          exact (hsmooth (a + 1) (H j) (hHmem j)).of_le (by norm_num)
        have hfamilyC1 : ContDiff ℝ 1
            (lagrangeSquaredDistanceCriticalFamily H) :=
          contDiff_lagrangeSquaredDistanceCriticalFamily H hH2
        have hsquareC1 : ContDiff ℝ 1 squareMap := by
          simpa [squareMap, rankMinorPatchLagrangeSquareMap,
            lagrangeParameterRecordingSquareMap, H] using
            contDiff_flatParameterRecordingMap hfamilyC1
        have hvvalue : squareMap v = target := by
          simpa only [squareMap, target, v, z, H,
            rankMinorPatchLagrangeSquareMap,
            rankMinorPatchLagrangeSquareTarget,
            lagrangeParameterRecordingSquareMap_append] using
              congrArg (fun w ↦ realEuclideanAppend w center) hsystem
        have hfamilyAt : DifferentiableAt ℝ
            (lagrangeSquaredDistanceCriticalFamily H) (z, center) :=
          (hfamilyC1.differentiable (by norm_num)).differentiableAt
        have hpartial : Function.Surjective
            (fstPartial (fderiv ℝ
              (lagrangeSquaredDistanceCriticalFamily H) (z, center))) := by
          rw [← fderiv_lagrangeSquaredDistanceCriticalFamily_fixed_center
            H z center hfamilyAt]
          exact LinearMap.range_eq_top.mp (by
            simpa only [H, z, center] using hregular)
        have hvderiv : Function.Surjective (fderiv ℝ squareMap v) := by
          simpa only [squareMap, rankMinorPatchLagrangeSquareMap,
            lagrangeParameterRecordingSquareMap, v, H] using
              surjective_fderiv_flatParameterRecordingMap hfamilyAt hpartial
        have hvregular : v ∈ smoothRegularFiber squareMap target :=
          (mem_smoothRegularFiber_iff_of_contDiff_square
            squareMap hsquareC1 target v).mpr ⟨hvvalue, hvderiv⟩
        let vv : smoothRegularFiber squareMap target := ⟨v, hvregular⟩
        let lifted : Lift := ⟨chart, vv⟩
        have hprimal : primal lifted = (y : RealEuclidean (a + 1)) := by
          change lagrangePrimalProjection (a + 1) (chart.1 : ℕ)
              (realEuclideanTakeLeft v) = (y : RealEuclidean (a + 1))
          rw [show realEuclideanTakeLeft v = z by
            exact realEuclideanTakeLeft_append z center]
          exact lagrangePrimalProjection_append
            (y : RealEuclidean (a + 1)) lambda
        have hprimalM : primal lifted ∈ M := by
          rw [hprimal]
          exact y.property
        refine ⟨lifted, ?_⟩
        have hbase : base lifted = y := by
          simp only [base, dite_eq_left hprimalM]
          exact Subtype.ext hprimal
        simpa only [hbase] using hycomponent
      exact exists_injective_connectedComponents_to_lifts base hmeet
    · have hfalse : ∀ x : M, False := by
        intro x
        exact hM ⟨x, x.property⟩
      let pick : ConnectedComponents M → Lift := fun c ↦ by
        let x : M := Classical.choose (ConnectedComponents.surjective_coe c)
        exact (hfalse x).elim
      refine ⟨pick, ?_⟩
      intro c
      let x : M := Classical.choose (ConnectedComponents.surjective_coe c)
      exact (hfalse x).elim
  obtain ⟨pickM, hpickM_injective⟩ := hpickM
  have hgC1 : ContDiff ℝ 1 g := by
    rw [contDiff_pi]
    intro j
    exact (hsmooth a (fun x ↦ g x j) (hg j)).of_le (by norm_num)
  let e := rankMinorFiberPatchHomeomorph g hgC1 t i
  refine ⟨pickM ∘ e.continuous.connectedComponentsMap, ?_⟩
  exact hpickM_injective.comp
    (Homeomorph.connectedComponentsMap_injective e)

/-- The finite subtuple cover assembles directly into a finite fixed-square
atlas for the full fibers of `g`.  This bypasses the unnecessarily rigid
requirement that all components of one rank/minor patch use one square map. -/
noncomputable def
    finiteFixedSquareRegularFiberComponentEncoding_of_canonicalFiniteLagrangeCover
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g)
    (cover : CanonicalRankMinorFiniteRegularLagrangeCover g) :
    FiniteFixedSquareRegularFiberComponentEncoding G g := by
  classical
  let Patch := Σ i : RankMinorPatchIndex a b,
    RankMinorLagrangeChartIndex a b i
  let dimension : Patch → ℕ := fun p ↦
    ((a + 1) + (p.2.1 : ℕ)) + (a + 1)
  let squareMap : ∀ p : Patch,
      RealEuclidean (dimension p) → RealEuclidean (dimension p) :=
    fun p ↦ rankMinorPatchLagrangeSquareMap g p.1 p.2
  let fiberTarget : ∀ p : Patch,
      RealEuclidean b → RealEuclidean (dimension p) :=
    fun p t ↦ rankMinorPatchLagrangeSquareTarget p.1 t p.2
      (cover.center p.1 p.2 t)
  have hsquareMapMem : ∀ p : Patch,
      FunctionTupleInFamily G (squareMap p) := by
    intro p
    exact hG.rankMinorPatchLagrangeSquareMap_mem hderiv g hg p.1 p.2
  have hgC1 : ContDiff ℝ 1 g := by
    rw [contDiff_pi]
    intro j
    exact (hsmooth a (fun x ↦ g x j) (hg j)).of_le (by norm_num)
  let patchEncode : ∀ (i : RankMinorPatchIndex a b) (t : RealEuclidean b),
      ConnectedComponents (rankMinorFiberPatch g t i) →
        Σ chart : RankMinorLagrangeChartIndex a b i,
          smoothRegularFiber
            (rankMinorPatchLagrangeSquareMap g i chart)
            (rankMinorPatchLagrangeSquareTarget i t chart
              (cover.center i chart t)) :=
    fun i t ↦ Classical.choose
      (exists_injective_rankMinorPatch_components_to_lagrangeCharts
        hG hsmooth hderiv g hg cover i t)
  have hpatchEncode : ∀ (i : RankMinorPatchIndex a b)
      (t : RealEuclidean b), Function.Injective (patchEncode i t) := by
    intro i t
    exact Classical.choose_spec
      (exists_injective_rankMinorPatch_components_to_lagrangeCharts
        hG hsmooth hderiv g hg cover i t)
  let rankCover (t : RealEuclidean b) :
      RankMinorPatchIndex a b → Set (g ⁻¹' {t}) :=
    fun i ↦ rankMinorFiberPatch g t i
  have hcoverSurj : ∀ t, Function.Surjective
      (connectedComponentsCoverMap (rankCover t)) := by
    intro t
    exact connectedComponentsCoverMap_surjective (rankCover t)
      (iUnion_rankMinorFiberPatch_eq_univ g hgC1 t)
  let chooseRankPatch (t : RealEuclidean b) :
      ConnectedComponents (g ⁻¹' {t}) →
        Σ i, ConnectedComponents (rankMinorFiberPatch g t i) :=
    Function.surjInv (hcoverSurj t)
  have hchooseRankPatch : ∀ t,
      Function.Injective (chooseRankPatch t) := by
    intro t
    exact Function.injective_surjInv (hcoverSurj t)
  let ChartFiber (t : RealEuclidean b)
      (i : RankMinorPatchIndex a b)
      (chart : RankMinorLagrangeChartIndex a b i) :=
    smoothRegularFiber
      (rankMinorPatchLagrangeSquareMap g i chart)
      (rankMinorPatchLagrangeSquareTarget i t chart
        (cover.center i chart t))
  let encodeNested (t : RealEuclidean b) :
      (Σ i, ConnectedComponents (rankMinorFiberPatch g t i)) →
        Σ i, Σ chart : RankMinorLagrangeChartIndex a b i,
          ChartFiber t i chart :=
    Sigma.map id (fun i ↦ patchEncode i t)
  have hencodeNested : ∀ t,
      Function.Injective (encodeNested t) := by
    intro t
    exact Function.injective_id.sigma_map (fun i ↦ hpatchEncode i t)
  let reassoc (t : RealEuclidean b) :
      (Σ i, Σ chart : RankMinorLagrangeChartIndex a b i,
          ChartFiber t i chart) ≃
        (Σ p : Patch,
          smoothRegularFiber (squareMap p) (fiberTarget p t)) := by
    simpa only [Patch, dimension, squareMap, fiberTarget, ChartFiber] using
      (Equiv.sigmaAssoc (fun i chart ↦ ↥(ChartFiber t i chart))).symm
  let encodeRankSigma (t : RealEuclidean b) :
      (Σ i, ConnectedComponents (rankMinorFiberPatch g t i)) →
        Σ p : Patch, smoothRegularFiber (squareMap p) (fiberTarget p t) :=
    reassoc t ∘ encodeNested t
  have hencodeRankSigma : ∀ t,
      Function.Injective (encodeRankSigma t) := by
    intro t
    exact (reassoc t).injective.comp (hencodeNested t)
  exact
    { Patch := Patch
      patchFintype := inferInstance
      dimension := dimension
      squareMap := squareMap
      fiberTarget := fiberTarget
      squareMap_mem := hsquareMapMem
      encode := fun t ↦ encodeRankSigma t ∘ chooseRankPatch t
      encode_injective := fun t ↦
        (hencodeRankSigma t).comp (hchooseRankPatch t) }

/-- Family-level finite-atlas consequence of the honest finite-subtuple
regular-Lagrange residual. -/
theorem hasFiniteFixedSquareRegularFiberComponentEncodingsForFamily_of_canonicalFiniteLagrangeCovers
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hcovers : HasCanonicalRankMinorFiniteRegularLagrangeCoversForFamily G) :
    HasFiniteFixedSquareRegularFiberComponentEncodingsForFamily G := by
  intro a b g hg
  obtain ⟨cover⟩ := hcovers a b g hg
  exact ⟨finiteFixedSquareRegularFiberComponentEncoding_of_canonicalFiniteLagrangeCover
    hG hsmooth hderiv g hg cover⟩

/-- The finite-subtuple residual and uniform regular-fiber bounds imply
uniform fiber finiteness without first merging the chart maps. -/
theorem hasUniformFiberFiniteness_of_canonicalFiniteLagrangeCovers
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hregular : HasUniformSquareRegularFiberBound G)
    (hcovers : HasCanonicalRankMinorFiniteRegularLagrangeCoversForFamily G) :
    HasUniformFiberFiniteness G :=
  (hasFiniteFixedSquareRegularFiberComponentEncodingsForFamily_of_canonicalFiniteLagrangeCovers
    hG hsmooth hderiv hcovers).hasUniformFiberFiniteness hregular

/-- Concrete Abel-family finite atlas from the finite-subtuple
regular-Lagrange cover. -/
theorem IsAbel.hasFiniteFixedSquareRegularFiberComponentEncodingsForFamily_of_canonicalFiniteLagrangeCovers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hcovers : HasCanonicalRankMinorFiniteRegularLagrangeCoversForFamily
      (abelGeometricFamily A)) :
    HasFiniteFixedSquareRegularFiberComponentEncodingsForFamily
      (abelGeometricFamily A) := by
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact
    AbelFormalization.hasFiniteFixedSquareRegularFiberComponentEncodingsForFamily_of_canonicalFiniteLagrangeCovers
      hG hsmooth hderiv hcovers

/-- Concrete Abel-family uniform fiber theorem from the finite-subtuple
regular-Lagrange residual and the separate Gabrielov bound. -/
theorem IsAbel.hasUniformFiberFiniteness_of_canonicalFiniteLagrangeCovers
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hregular : HasUniformSquareRegularFiberBound (abelGeometricFamily A))
    (hcovers : HasCanonicalRankMinorFiniteRegularLagrangeCoversForFamily
      (abelGeometricFamily A)) :
    HasUniformFiberFiniteness (abelGeometricFamily A) := by
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact AbelFormalization.hasUniformFiberFiniteness_of_canonicalFiniteLagrangeCovers
    hG hsmooth hderiv hregular hcovers

/-! ## Strong one-tuple special case -/

/-- A stronger special case asking the entire canonical tuple to have regular
Lagrange lifts.  This directly recovers one square map per rank/minor patch.
It is intentionally not used as the final residual above: an overdetermined
canonical tuple cannot have surjective constraint derivative, whereas the
finite-subtuple cover permits the independent equations to vary by stratum. -/
def HasCanonicalRankMinorRegularLagrangeLiftsForFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ a b (g : RealEuclidean a → RealEuclidean b),
    FunctionTupleInFamily G g →
      ∀ i : RankMinorPatchIndex a b,
        HasRegularLagrangeLiftsAtComponentMinima
          (rankMinorPatchConstraintTuple g i)

/-- The canonical regular-Lagrange residual supplies every rank/minor patch
encoder.  The square map is the parameter-recording Lagrange map of the fixed
closed reciprocal/minor tuple. -/
noncomputable def rankMinorPatchFixedSquareEncoding_of_canonicalLagrangeLifts
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : FunctionTupleInFamily G g)
    (hlifts : ∀ i : RankMinorPatchIndex a b,
      HasRegularLagrangeLiftsAtComponentMinima
        (rankMinorPatchConstraintTuple g i)) :
    RankMinorPatchFixedSquareEncoding G g := by
  classical
  have hgC1 : ContDiff ℝ 1 g := by
    rw [contDiff_pi]
    intro j
    exact (hsmooth a (fun x ↦ g x j) (hg j)).of_le (by norm_num)
  let encoding : ∀ i : RankMinorPatchIndex a b,
      FixedSquareRegularFiberComponentEncoding G
        (constraintMap (rankMinorPatchConstraintTuple g i)) :=
    fun i ↦ fixedSquareRegularFiberComponentEncoding_of_regularLagrangeLifts
      hG hsmooth hderiv (rankMinorPatchConstraintTuple g i)
        (hG.rankMinorPatchConstraintTuple_mem hderiv g hg i) (hlifts i)
  exact
    { dimension := fun i ↦ (encoding i).dimension
      squareMap := fun i ↦ (encoding i).squareMap
      fiberTarget := fun i t ↦
        (encoding i).fiberTarget (rankMinorPatchConstraintTarget i t)
      squareMap_mem := fun i ↦ (encoding i).squareMap_mem
      encodePatch := fun i t ↦
        (encoding i).encode (rankMinorPatchConstraintTarget i t) ∘
          (rankMinorFiberPatchHomeomorph g hgC1 t i).continuous.connectedComponentsMap
      encodePatch_injective := fun i t ↦
        ((encoding i).encode_injective
          (rankMinorPatchConstraintTarget i t)).comp
            (Homeomorph.connectedComponentsMap_injective
              (rankMinorFiberPatchHomeomorph g hgC1 t i)) }

/-- Family-level form of the canonical reduction. -/
theorem hasRankMinorPatchFixedSquareEncodingsForFamily_of_canonicalLagrangeLifts
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hlifts : HasCanonicalRankMinorRegularLagrangeLiftsForFamily G) :
    HasRankMinorPatchFixedSquareEncodingsForFamily G := by
  intro a b g hg
  exact ⟨rankMinorPatchFixedSquareEncoding_of_canonicalLagrangeLifts
    hG hsmooth hderiv g hg (hlifts a b g hg)⟩

/-- Concrete Abel-family endpoint: the old patch-encoding premise follows
from regular Lagrange lifts for the explicit reciprocal/successor-minor
systems. -/
theorem IsAbel.hasRankMinorPatchFixedSquareEncodingsForFamily_of_canonicalLagrangeLifts
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hlifts : HasCanonicalRankMinorRegularLagrangeLiftsForFamily
      (abelGeometricFamily A)) :
    HasRankMinorPatchFixedSquareEncodingsForFamily
      (abelGeometricFamily A) := by
  obtain ⟨hG, hsmooth, hderiv⟩ :=
    hA.geometric_smooth_derivativeClosed_abelGeometricFamily
  exact
    AbelFormalization.hasRankMinorPatchFixedSquareEncodingsForFamily_of_canonicalLagrangeLifts
      hG hsmooth hderiv hlifts

/-- Combining the canonical constrained-Morse residual with a uniform bound
for fixed square regular fibers yields Lion's uniform fiber conclusion for
the concrete Abel family. -/
theorem IsAbel.hasUniformFiberFiniteness_of_canonicalRankMinorLagrangeLifts
    {A : ℝ → ℝ} (hA : IsAbel A)
    (hregular : HasUniformSquareRegularFiberBound (abelGeometricFamily A))
    (hlifts : HasCanonicalRankMinorRegularLagrangeLiftsForFamily
      (abelGeometricFamily A)) :
    HasUniformFiberFiniteness (abelGeometricFamily A) := by
  exact hasUniformFiberFiniteness_of_rankMinorPatchEncodings
    hA.isEverywhereSmooth_abelGeometricFamily hregular
    (hA.hasRankMinorPatchFixedSquareEncodingsForFamily_of_canonicalLagrangeLifts
      hlifts)

end AbelFormalization
