import AbelFormalization.CharbonnelSardianProjectionFiniteChoicePrefixLift
import AbelFormalization.CharbonnelSardianProjectionRadialBranch
import Mathlib.Topology.Order.IntermediateValue

/-!
# Conditional small-level alternative for Sardian projection

Wilkie 3.10 needs new radial or squared-minor levels at every sufficiently
small positive final parameter.  The radial image of a connected fiber has
this property when it takes arbitrarily small positive values.  The minor
range alternative in Wilkie 2.9 is recorded here as an explicit premise:
proving it requires the regular-value and differential-topology argument.
These level statements are then converted into membership in the finite
projected constituent family by its exact carrier equations.

Arbitrary small radial values on a disconnected fiber do not yield an
interval by topology alone.  The source uses the weak structure's finite
one-dimensional behavior for that step.  This file does not infer either
the connected radial subfiber or the minor range from definability.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A continuous real function on a preconnected set assumes every small
positive level if it has one positive value and arbitrarily small values. -/
theorem isPreconnected_all_small_positive_levels
    {X : Type*} [TopologicalSpace X]
    {S : Set X} {f : X → ℝ}
    (hS : IsPreconnected S) (hf : ContinuousOn f S)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ x ∈ S, f x < δ)
    (hanchor : ∃ x ∈ S, 0 < f x) :
    ∃ η : ℝ, 0 < η ∧
      ∀ t : ℝ, 0 < t → t < η → ∃ x ∈ S, f x = t := by
  obtain ⟨a, ha, hapos⟩ := hanchor
  refine ⟨f a, hapos, ?_⟩
  intro t htpos hteta
  obtain ⟨b, hb, hblt⟩ := hsmall t htpos
  obtain ⟨x, hx, hfx⟩ :=
    hS.intermediate_value hb ha hf
      (show t ∈ Icc (f b) (f a) from
        ⟨le_of_lt hblt, le_of_lt hteta⟩)
  exact ⟨x, hx, hfx⟩

/-- The old regular fiber over a visible ball and a fixed old positive
parameter block.  Its hidden dimension and equation count are both `q+1`,
as in Wilkie 2.9 after one-coordinate projection. -/
def sardianProjectionOldTupleFiber
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q : ℕ}
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n)) (e : RealEuclidean (q + 1)) :
    Set (RealEuclidean (n + (q + 1))) :=
  {v | realEuclideanTakeLeft v ∈ U ∧
    ∀ i : Fin (q + 1), sardianProjectionOldTuple old v i = e i}

/-- A point on the old tuple fiber whose chosen appended equation has
level `t` gives a point in the finite projected family at parameter block
`(e,t)`.  No approximation estimate enters this carrier equivalence. -/
theorem mem_sardianProjectionAlgebraicFamily_of_oldTupleFiber_level
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (e : RealEuclidean (q + 1)) (hepos : ∀ i, 0 < e i)
    (t : ℝ) (htpos : 0 < t)
    (choice : SardianProjectionLastEquationChoice n q)
    (v : RealEuclidean (n + (q + 1)))
    (hprefix : ∀ i : Fin (q + 1),
      sardianProjectionOldTuple old v i = e i)
    (hlevel : sardianProjectionLastEquation old choice v = t) :
    realEuclideanAppend (realEuclideanTakeLeft v)
        (charbonnelAppendLastParameter e t) ∈
      (sardianProjectionAlgebraicFamily
        hG hsmooth hderiv hn old).carrier := by
  let ε : RealEuclidean ((q + 1) + 1) :=
    charbonnelAppendLastParameter e t
  have hprefixParameter : ∀ i : Fin (q + 1), ε i.castSucc = e i := by
    intro i
    have hi : i.castSucc = Fin.castAdd 1 i := Fin.ext rfl
    simp [ε, charbonnelAppendLastParameter, hi]
  have hlastParameter : ε (Fin.last (q + 1)) = t := by
    simpa only [ε] using charbonnelAppendLastParameter_last e t
  have hpositiveParameter : ∀ j : Fin ((q + 1) + 1), 0 < ε j := by
    intro j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simpa only [hlastParameter] using htpos
    · simpa only [hprefixParameter] using hepos i
  have hvsplit :
      realEuclideanAppend (realEuclideanTakeLeft v)
        (realEuclideanTakeRight v) = v :=
    realEuclideanAppend_takeLeft_takeRight v
  have hchoiceCarrier :
      realEuclideanAppend (realEuclideanTakeLeft v) ε ∈
        (sardianProjectionAlgebraicConstituent
          hG hsmooth hderiv hn old choice).carrier := by
    apply (mem_sardianProjectionAlgebraicConstituent_carrier_iff
      hG hsmooth hderiv hn old choice
      (realEuclideanTakeLeft v) ε).mpr
    refine ⟨hpositiveParameter, realEuclideanTakeRight v, ?_, ?_⟩
    · intro i
      rw [hvsplit, hprefix i, hprefixParameter i]
    · rw [hvsplit, hlevel, hlastParameter]
  exact (mem_sardianProjectionAlgebraicFamily_carrier_iff_exists_choice
    hG hsmooth hderiv hn old).mpr ⟨choice, hchoiceCarrier⟩

/-- A conditional form of the exact level alternative used in Wilkie 3.10.
The radial premise names a preconnected part of the old tuple fiber that
takes arbitrarily small radial values.  The minor premise is exactly the
positive-level consequence of Wilkie 2.9, with the maximal minor index and
its uniform interval given explicitly. -/
theorem exists_small_levels_in_sardianProjectionAlgebraicFamily
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (U : Set (RealEuclidean n))
    (e : RealEuclidean (q + 1)) (hepos : ∀ i, 0 < e i)
    (hbranch :
      (∃ S : Set (RealEuclidean (n + (q + 1))),
        IsPreconnected S ∧
        S ⊆ sardianProjectionOldTupleFiber old U e ∧
        ∀ δ : ℝ, 0 < δ →
          ∃ v ∈ S, sardianProjectionRadialReciprocal n q v < δ) ∨
      (∃ columns : Fin (q + 1) ↪ Fin (n + (q + 1)),
        ∃ η : ℝ, 0 < η ∧
          ∀ t : ℝ, t ∈ Icc (0 : ℝ) η →
            ∃ v ∈ sardianProjectionOldTupleFiber old U e,
              sardianProjectionLastEquation old (some columns) v = t)) :
    ∃ η : ℝ, 0 < η ∧
      ∀ t : ℝ, 0 < t → t < η →
        ∃ x ∈ U,
          realEuclideanAppend x (charbonnelAppendLastParameter e t) ∈
            (sardianProjectionAlgebraicFamily
              hG hsmooth hderiv hn old).carrier := by
  rcases hbranch with ⟨S, hS, hsubset, hsmall⟩ |
      ⟨columns, η, hηpos, hminorRange⟩
  · have hradialContinuous :
        Continuous (sardianProjectionRadialReciprocal n q) :=
      (hsmooth (n + (q + 1))
        (sardianProjectionRadialReciprocal n q)
        (sardianProjectionRadialReciprocal_mem hG n q)).continuous
    obtain ⟨anchor, hanchor, _⟩ := hsmall 1 (by norm_num)
    have hradialPositive :
        0 < sardianProjectionRadialReciprocal n q anchor := by
      change 0 < (sardianProjectionRadialDenominator n q anchor)⁻¹
      exact inv_pos.mpr
        (sardianProjectionRadialDenominator_pos n q anchor)
    obtain ⟨η, hηpos, hlevels⟩ :=
      isPreconnected_all_small_positive_levels hS
        hradialContinuous.continuousOn hsmall
        ⟨anchor, hanchor, hradialPositive⟩
    refine ⟨η, hηpos, ?_⟩
    intro t htpos hteta
    obtain ⟨v, hvS, hradialLevel⟩ := hlevels t htpos hteta
    have hvFiber := hsubset hvS
    refine ⟨realEuclideanTakeLeft v, hvFiber.1, ?_⟩
    exact mem_sardianProjectionAlgebraicFamily_of_oldTupleFiber_level
      hG hsmooth hderiv hn old e hepos t htpos none v
      hvFiber.2 hradialLevel
  · refine ⟨η, hηpos, ?_⟩
    intro t htpos hteta
    obtain ⟨v, hvFiber, hminorLevel⟩ :=
      hminorRange t ⟨le_of_lt htpos, le_of_lt hteta⟩
    refine ⟨realEuclideanTakeLeft v, hvFiber.1, ?_⟩
    exact mem_sardianProjectionAlgebraicFamily_of_oldTupleFiber_level
      hG hsmooth hderiv hn old e hepos t htpos (some columns) v
      hvFiber.2 hminorLevel

end AbelFormalization
