import AbelFormalization.CharbonnelSardianProjectionTopology
import AbelFormalization.SmoothFamilyRectangularJacobianMinors

/-!
# Algebraic Sardian choices for Wilkie 3.10

For one-coordinate existential projection, Wilkie appends one equation to
each old constituent tuple.  The equation is either a radial escape level
or the square of a maximal Jacobian minor.  This file constructs those
choices as a finite Sardian family when `G` is geometric, everywhere smooth,
and closed under coordinate derivatives.

The source prints a reciprocal square-root radial equation.  A reciprocal
of the positive polynomial `1 + sum of hidden-coordinate squares` has the
same small-level escape role and belongs to any geometric function family.
No approximation modulus, radial-range dichotomy, or boundary reach is
claimed here.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

private theorem projectionOneCoordinateArity_eq (n q : ℕ) :
    (n + 1) + q = n + (q + 1) := by
  omega

/-- The old ambient coordinates and the new constituent input coordinates
have the same finite order: the erased visible coordinate becomes the first
coordinate of the enlarged hidden block. -/
def sardianProjectionOldInputReindex (n q : ℕ) :
    RealEuclidean (n + (q + 1)) ≃ₗ[ℝ]
      RealEuclidean ((n + 1) + q) :=
  realEuclideanCoordinateReindex
    (finCongr (projectionOneCoordinateArity_eq n q))

/-- The old `q + 1` constituent equations, read in the new ambient
coordinates. -/
def sardianProjectionOldTuple
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q) :
    RealEuclidean (n + (q + 1)) → RealEuclidean (q + 1) :=
  fun v i ↦ old.equation i (sardianProjectionOldInputReindex n q v)

/-- Geometric-family affine closure transports each old equation to the
new ambient coordinate type. -/
theorem sardianProjectionOldTuple_inFamily
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q) :
    FunctionTupleInFamily G (sardianProjectionOldTuple old) := by
  intro i
  have hpull := hG.affine_comp (old.equation_mem i)
    (sardianProjectionOldInputReindex n q).toLinearMap.toAffineMap
  change (fun v : RealEuclidean (n + (q + 1)) ↦
    old.equation i (sardianProjectionOldInputReindex n q v)) ∈
      G (n + (q + 1)) at hpull
  exact hpull

/-- A positive radial denominator involving precisely the new hidden
coordinate block. -/
def sardianProjectionRadialDenominator (n q : ℕ) :
    RealEuclideanFunction (n + (q + 1)) :=
  fun v ↦ 1 + ∑ j : Fin (q + 1), (realEuclideanTakeRight v j) ^ 2

def sardianProjectionRadialReciprocal (n q : ℕ) :
    RealEuclideanFunction (n + (q + 1)) :=
  fun v ↦ (sardianProjectionRadialDenominator n q v)⁻¹

theorem sardianProjectionRadialDenominator_pos (n q : ℕ)
    (v : RealEuclidean (n + (q + 1))) :
    0 < sardianProjectionRadialDenominator n q v := by
  have hsum : 0 ≤ ∑ j : Fin (q + 1),
      (realEuclideanTakeRight v j) ^ 2 :=
    Finset.sum_nonneg (fun j _ ↦ sq_nonneg _)
  dsimp [sardianProjectionRadialDenominator]
  linarith

theorem sardianProjectionRadialDenominator_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G) (n q : ℕ) :
    sardianProjectionRadialDenominator n q ∈ G (n + (q + 1)) := by
  let square : Fin (q + 1) → RealEuclideanFunction (n + (q + 1)) :=
    fun j v ↦ v (Fin.natAdd n j) ^ 2
  have hsquare : ∀ j ∈ (Finset.univ : Finset (Fin (q + 1))),
      square j ∈ G (n + (q + 1)) := by
    intro j _
    apply hG.sq_mem
    simpa [square] using
      (hG.polynomial (MvPolynomial.X (Fin.natAdd n j)))
  have hsum := hG.finset_sum_mem Finset.univ square hsquare
  have htotal := hG.add
    (hG.const_mem (n := n + (q + 1)) 1) hsum
  convert htotal using 1
  funext v
  simp [sardianProjectionRadialDenominator, square,
    realEuclideanTakeRight, Finset.sum_apply, Pi.add_apply]

theorem sardianProjectionRadialReciprocal_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G) (n q : ℕ) :
    sardianProjectionRadialReciprocal n q ∈ G (n + (q + 1)) := by
  exact hG.inv (sardianProjectionRadialDenominator_mem hG n q)
    (fun v ↦ ne_of_gt (sardianProjectionRadialDenominator_pos n q v))

/-- The finite choice index: radial escape or one maximal critical minor.
The squared minor avoids sign restrictions on the final positive level. -/
abbrev SardianProjectionLastEquationChoice (n q : ℕ) :=
  Option (Fin (q + 1) ↪ Fin (n + (q + 1)))

def sardianProjectionLastEquation
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (choice : SardianProjectionLastEquationChoice n q) :
    RealEuclideanFunction (n + (q + 1)) :=
  match choice with
  | none => sardianProjectionRadialReciprocal n q
  | some cols =>
      fun v ↦ (standardJacobianColumnMinor
        (sardianProjectionOldTuple old) cols v) ^ 2

/-- Both kinds of final equation belong to the function family. -/
theorem sardianProjectionLastEquation_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (choice : SardianProjectionLastEquationChoice n q) :
    sardianProjectionLastEquation old choice ∈ G (n + (q + 1)) := by
  cases choice with
  | none =>
      exact sardianProjectionRadialReciprocal_mem hG n q
  | some cols =>
      exact hG.sq_mem
        (hG.standardJacobianColumnMinor_mem hderiv
          (sardianProjectionOldTuple old)
          (sardianProjectionOldTuple_inFamily hG old) cols)

/-- Append the selected equation to the old tuple.  This is an actual
`order`-Sardian constituent, with the source's hidden arity increased by one.
It does not assert either direction of condition 3.6. -/
def sardianProjectionAlgebraicConstituent
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (choice : SardianProjectionLastEquationChoice n q) :
    CharbonnelSardianConstituent G order n (q + 1) := by
  let equations : Fin ((q + 1) + 1) →
      RealEuclideanFunction (n + (q + 1)) :=
    Fin.lastCases (sardianProjectionLastEquation old choice)
      (fun i v ↦ sardianProjectionOldTuple old v i)
  have hequations : ∀ i, equations i ∈ G (n + (q + 1)) := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [equations, Fin.lastCases_last] using
        (sardianProjectionLastEquation_mem hG hderiv old choice)
    · simpa only [equations, Fin.lastCases_castSucc] using
        (sardianProjectionOldTuple_inFamily hG old j)
  exact {
    visible_pos := hn
    equation := equations
    equation_mem := hequations
    equation_contDiff := fun i ↦
      (hsmooth (n + (q + 1)) (equations i) (hequations i)).of_le
        (by simp)
  }

/-- The first `q + 1` equations remain the old constituent tuple after
the ambient coordinate reindexing. -/
theorem sardianProjectionAlgebraicConstituent_equation_castSucc
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (choice : SardianProjectionLastEquationChoice n q)
    (i : Fin (q + 1)) (v : RealEuclidean (n + (q + 1))) :
    (sardianProjectionAlgebraicConstituent
      hG hsmooth hderiv hn old choice).equation i.castSucc v =
        sardianProjectionOldTuple old v i := by
  simp only [sardianProjectionAlgebraicConstituent,
    Fin.lastCases_castSucc]

/-- The final equation is exactly the selected radial or squared-minor
level. -/
theorem sardianProjectionAlgebraicConstituent_equation_last
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (choice : SardianProjectionLastEquationChoice n q)
    (v : RealEuclidean (n + (q + 1))) :
    (sardianProjectionAlgebraicConstituent
      hG hsmooth hderiv hn old choice).equation (Fin.last (q + 1)) v =
        sardianProjectionLastEquation old choice v := by
  simp only [sardianProjectionAlgebraicConstituent,
    Fin.lastCases_last]

/-- Exact carrier equations after moving one visible coordinate into the
hidden block and appending one positive parameter.  This is syntax and
coordinate algebra only; it gives no approximation inequality. -/
theorem mem_sardianProjectionAlgebraicConstituent_carrier_iff
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (choice : SardianProjectionLastEquationChoice n q)
    (x : RealEuclidean n) (ε : RealEuclidean ((q + 1) + 1)) :
    realEuclideanAppend x ε ∈
        (sardianProjectionAlgebraicConstituent
          hG hsmooth hderiv hn old choice).carrier ↔
      (∀ i, 0 < ε i) ∧
        ∃ y : RealEuclidean (q + 1),
          (∀ i : Fin (q + 1),
            sardianProjectionOldTuple old (realEuclideanAppend x y) i =
              ε i.castSucc) ∧
          sardianProjectionLastEquation old choice
            (realEuclideanAppend x y) = ε (Fin.last (q + 1)) := by
  let c := sardianProjectionAlgebraicConstituent
    hG hsmooth hderiv hn old choice
  change realEuclideanAppend x ε ∈ c.carrier ↔ _
  rw [c.mem_carrier_iff]
  simp only [realEuclideanTakeLeft_append,
    realEuclideanTakeRight_append]
  constructor
  · rintro ⟨⟨y, hy⟩, hpositive⟩
    refine ⟨hpositive, y, ?_, ?_⟩
    · intro i
      have hi := hy i.castSucc
      rw [sardianProjectionAlgebraicConstituent_equation_castSucc
        hG hsmooth hderiv hn old choice i] at hi
      exact hi
    · have hlast := hy (Fin.last (q + 1))
      rw [sardianProjectionAlgebraicConstituent_equation_last
        hG hsmooth hderiv hn old choice] at hlast
      exact hlast
  · rintro ⟨hpositive, y, hprefix, hlast⟩
    refine ⟨⟨y, ?_⟩, hpositive⟩
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [sardianProjectionAlgebraicConstituent_equation_last
        hG hsmooth hderiv hn old choice]
      exact hlast
    · rw [sardianProjectionAlgebraicConstituent_equation_castSucc
        hG hsmooth hderiv hn old choice j]
      exact hprefix j

/-- All the radial/minor choices for one old constituent form one finite
Sardian family at the enlarged hidden depth. -/
def sardianProjectionAlgebraicFamily
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q) :
    CharbonnelFiniteSardianFamily G order n (q + 1) := by
  classical
  exact {
    visible_pos := hn
    constituents :=
      (Finset.univ : Finset (SardianProjectionLastEquationChoice n q)).toList.map
        (fun choice ↦
          CharbonnelPaddedSardianConstituent.ofConstituent
            (Nat.le_refl (q + 1))
            (sardianProjectionAlgebraicConstituent
              hG hsmooth hderiv hn old choice))
  }

/-- The constructed finite carrier lies in the projected-zero algebra.
This is a consequence of the constituent syntax, independent of the
projection approximation theorem. -/
theorem sardianProjectionAlgebraicFamily_isProjectedZeroSet
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q) :
    IsProjectedZeroSet G
      (sardianProjectionAlgebraicFamily
        hG hsmooth hderiv hn old).carrier :=
  (sardianProjectionAlgebraicFamily
    hG hsmooth hderiv hn old).carrier_isProjectedZeroSet hG

end AbelFormalization
