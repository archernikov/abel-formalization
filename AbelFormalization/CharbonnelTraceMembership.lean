import AbelFormalization.CharbonnelApproximationTrace
import AbelFormalization.ClosedZeroSetCharbonnelBridge
import AbelFormalization.ProjectedZeroPolynomialSigns

/-!
# Membership of Charbonnel approximation traces

This file proves the algebraic membership half of
`CharbonnelApproximationTraceTameness` for the Charbonnel closure generated
by literal zero sets.  Topological closure is already a constructor of a
Charbonnel description.  For the positive zero trace, the construction is:

1. encode positivity of the final coordinate as a projected zero set and
   hence as a rank-one literal-zero description;
2. intersect this locus with the input description;
3. take its topological closure;
4. cut by the integer-affine hyperplane where the final coordinate is zero;
5. existentially project away that final coordinate.

The remaining analytic content is isolated in
`CharbonnelApproximationTraceSmallness`, whose two fields state precisely
the empty-interior preservation facts imported from Charbonnel's theorems.
No complement closure is assumed or proved here.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## The two elementary loci used by the trace construction -/

/-- The strict positive locus of the final coordinate. -/
def charbonnelPositiveLastCoordinateLocus (d : ℕ) :
    Set (RealEuclidean (d + 1)) :=
  {v | 0 < v (Fin.last d)}

@[simp]
theorem charbonnelPositiveLastPart_eq_inter_locus
    {d : ℕ} (S : Set (RealEuclidean (d + 1))) :
    charbonnelPositiveLastPart S =
      S ∩ charbonnelPositiveLastCoordinateLocus d :=
  rfl

/-- Positivity of the final coordinate has the standard polynomial witness
equation and is therefore projected-zero. -/
theorem charbonnelPositiveLastCoordinateLocus_isProjectedZeroSet
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) (d : ℕ) :
    IsProjectedZeroSet G (charbonnelPositiveLastCoordinateLocus d) := by
  simpa [charbonnelPositiveLastCoordinateLocus] using
    (isProjectedZeroSet_polynomial_pos hG
      (MvPolynomial.X (Fin.last d)))

/-- The positive-final-coordinate locus has a rank-one description over the
literal zero-set base. -/
theorem exists_rank_one_description_positiveLastCoordinateLocus
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) (d : ℕ) :
    ∃ description :
        CharbonnelDescription (literalZeroSetFamily G) (d + 1),
      description.carrier = charbonnelPositiveLastCoordinateLocus d ∧
        description.rank = 1 :=
  (charbonnelPositiveLastCoordinateLocus_isProjectedZeroSet hG d).exists_rank_one_literalZero_description
    (by omega)

/-- The integer-affine hyperplane on which the final coordinate vanishes. -/
def charbonnelLastCoordinateZeroHyperplane (d : ℕ) :
    Set (RealEuclidean (d + 1)) :=
  {v | v (Fin.last d) = 0}

/-- One integer coefficient row cuts out the final-coordinate zero
hyperplane. -/
theorem isIntegerAffineSet_charbonnelLastCoordinateZeroHyperplane
    (d : ℕ) :
    IsIntegerAffineSet (charbonnelLastCoordinateZeroHyperplane d) := by
  refine ⟨1,
    (fun _ j ↦ if j = Fin.last d then 1 else 0),
    (fun _ ↦ 0), ?_⟩
  ext v
  simp [charbonnelLastCoordinateZeroHyperplane]

/-! ## The carrier identity -/

/-- Cutting the closure of the positive part by `last = 0` and projecting
away the final coordinate is exactly the positive zero trace. -/
theorem realEuclideanExistentialProjection_closure_positiveLastPart_inter_lastZero
    {d : ℕ} (S : Set (RealEuclidean (d + 1))) :
    realEuclideanExistentialProjection
        (closure (charbonnelPositiveLastPart S) ∩
          charbonnelLastCoordinateZeroHyperplane d) =
      charbonnelPositiveZeroTrace S := by
  ext x
  change
    (∃ y : RealEuclidean 1,
      realEuclideanAppend x y ∈ closure (charbonnelPositiveLastPart S) ∩
        charbonnelLastCoordinateZeroHyperplane d) ↔
      charbonnelAppendLastCoordinate x 0 ∈
        closure (charbonnelPositiveLastPart S)
  constructor
  · rintro ⟨y, hyclosure, hyzero⟩
    have hy0 : y 0 = 0 := by
      simpa [charbonnelLastCoordinateZeroHyperplane,
        realEuclideanAppend_last_one] using hyzero
    have hy : y = fun _ ↦ 0 := by
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact hy0
    subst y
    simpa [charbonnelAppendLastCoordinate] using hyclosure
  · intro hx
    refine ⟨fun _ ↦ 0, ?_, ?_⟩
    · simpa [charbonnelAppendLastCoordinate] using hx
    · simp [charbonnelLastCoordinateZeroHyperplane,
        realEuclideanAppend_last_one]

/-! ## Membership in the literal-zero Charbonnel closure -/

/-- Closure membership is one of the defining Charbonnel-description
constructors. -/
theorem literalZeroSet_charbonnelClosure_closure_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {d : ℕ} {S : Set (RealEuclidean d)}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) d) :
    closure S ∈ charbonnelClosure (literalZeroSetFamily G) d :=
  charbonnelClosure_topologicalClosure hS

/-- The positive zero trace of a member of the literal-zero Charbonnel
closure is again a member.  This is only the algebraic membership statement;
empty-interior preservation is supplied separately below. -/
theorem literalZeroSet_charbonnelClosure_positiveZeroTrace_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {d : ℕ} (hd : 0 < d)
    {S : Set (RealEuclidean (d + 1))}
    (hS : S ∈ charbonnelClosure (literalZeroSetFamily G) (d + 1)) :
    charbonnelPositiveZeroTrace S ∈
      charbonnelClosure (literalZeroSetFamily G) d := by
  obtain ⟨positiveDescription, hpositiveCarrier, _hpositiveRank⟩ :=
    exists_rank_one_description_positiveLastCoordinateLocus hG d
  have hpositive : charbonnelPositiveLastCoordinateLocus d ∈
      charbonnelClosure (literalZeroSetFamily G) (d + 1) :=
    ⟨positiveDescription, hpositiveCarrier⟩
  let hbase : ClosedPositiveArityDescriptionBase (literalZeroSetFamily G) :=
    literalZeroSetFamily_closedDescriptionBase hG hsmooth
  have hpositivePart : charbonnelPositiveLastPart S ∈
      charbonnelClosure (literalZeroSetFamily G) (d + 1) := by
    rw [charbonnelPositiveLastPart_eq_inter_locus]
    exact hbase.charbonnelClosure_inter hS hpositive
  have hclosedPositivePart : closure (charbonnelPositiveLastPart S) ∈
      charbonnelClosure (literalZeroSetFamily G) (d + 1) :=
    charbonnelClosure_topologicalClosure hpositivePart
  have hzeroCut :
      closure (charbonnelPositiveLastPart S) ∩
          charbonnelLastCoordinateZeroHyperplane d ∈
        charbonnelClosure (literalZeroSetFamily G) (d + 1) :=
    charbonnelClosure_integerAffineInter hclosedPositivePart
      (isIntegerAffineSet_charbonnelLastCoordinateZeroHyperplane d)
  have hprojection :
      realEuclideanExistentialProjection
          (closure (charbonnelPositiveLastPart S) ∩
            charbonnelLastCoordinateZeroHyperplane d) ∈
        charbonnelClosure (literalZeroSetFamily G) d :=
    charbonnelClosure_projection hd hzeroCut
  rw [realEuclideanExistentialProjection_closure_positiveLastPart_inter_lastZero
    S] at hprojection
  exact hprojection

/-! ## Separating the remaining Charbonnel smallness input -/

/-- The exact analytic remainder of approximation-trace tameness after the
two membership clauses have been proved above. -/
structure CharbonnelApproximationTraceSmallness
    (C : EuclideanSetFamily) : Prop where
  closure_interior_eq_empty : ∀ {d : ℕ}, 0 < d →
    ∀ {S : Set (RealEuclidean d)}, S ∈ C d →
      interior S = ∅ → interior (closure S) = ∅
  positiveZeroTrace_interior_eq_empty : ∀ {d : ℕ}, 0 < d →
    ∀ {S : Set (RealEuclidean (d + 1))}, S ∈ C (d + 1) →
      interior S = ∅ → interior (charbonnelPositiveZeroTrace S) = ∅

/-- The proved membership clauses and the two explicit smallness hypotheses
assemble the full trace-tameness interface used by the descent recursion. -/
theorem literalZeroSet_charbonnelClosure_traceTameness
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hsmall : CharbonnelApproximationTraceSmallness
      (charbonnelClosure (literalZeroSetFamily G))) :
    CharbonnelApproximationTraceTameness
      (charbonnelClosure (literalZeroSetFamily G)) where
  closure_mem := by
    intro d _hd S hS
    exact literalZeroSet_charbonnelClosure_closure_mem hS
  closure_interior_eq_empty := by
    intro d hd S hS hSempty
    exact hsmall.closure_interior_eq_empty hd hS hSempty
  positiveZeroTrace_mem := by
    intro d hd S hS
    exact literalZeroSet_charbonnelClosure_positiveZeroTrace_mem
      hG hsmooth hd hS
  positiveZeroTrace_interior_eq_empty := by
    intro d hd S hS hSempty
    exact hsmall.positiveZeroTrace_interior_eq_empty hd hS hSempty

end AbelFormalization
