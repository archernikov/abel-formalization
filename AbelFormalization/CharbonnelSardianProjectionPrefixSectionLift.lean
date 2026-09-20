import AbelFormalization.CharbonnelSardianProjectionFromBelowReduction

/-!
# Old-section lift for one projected Sardian constituent

The coordinate reindex in Wilkie 3.10 keeps `x : ℝⁿ` visible, makes the
erased visible coordinate `y 0` the last old visible coordinate, and leaves
`Fin.tail y` as the old hidden block. Dropping the new last positive level
therefore turns any member of one radial-or-minor projected constituent
into a member of its old constituent. The conclusion is exactly the
`hsection` premise of `approximatesFromBelow_projection_of_prefixSection`
for one exact-depth choice; it does not assert modulus compatibility or
boundary approximation from above.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The explicit reassociation underlying Wilkie's one-coordinate
projection: the first new hidden coordinate was the erased old visible
coordinate. The `finCongr` in the project reindex preserves every natural
coordinate index. -/
theorem sardianProjectionOldInputReindex_append_eq
    (n q : ℕ) (x : RealEuclidean n)
    (y : RealEuclidean (q + 1)) :
    sardianProjectionOldInputReindex n q
        (realEuclideanAppend x y) =
      realEuclideanAppend
        (realEuclideanAppend x (fun _ : Fin 1 ↦ y 0))
        (Fin.tail y) := by
  let h : (n + 1) + q = n + (q + 1) := by omega
  change realEuclideanCoordinateReindex (finCongr h)
      (realEuclideanAppend x y) =
    realEuclideanAppend
      (realEuclideanAppend x (fun _ : Fin 1 ↦ y 0))
      (Fin.tail y)
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun k ↦ ?_) i
  · refine Fin.lastCases ?_ (fun a ↦ ?_) j
    · have hindex :
          (finCongr h) (Fin.castAdd q
            (Fin.natAdd n (0 : Fin 1))) =
            Fin.natAdd n (0 : Fin (q + 1)) := by
        apply Fin.ext
        rfl
      have hlast : (Fin.last n) =
          Fin.natAdd n (0 : Fin 1) := by
        apply Fin.ext
        rfl
      simp only [realEuclideanCoordinateReindex_apply, hlast]
      rw [hindex]
      simp only [realEuclideanAppend_castAdd, realEuclideanAppend_natAdd]
    · have hindex :
          (finCongr h) (Fin.castAdd q (Fin.castAdd 1 a)) =
            Fin.castAdd (q + 1) a := by
        apply Fin.ext
        rfl
      have hcast : a.castSucc = Fin.castAdd 1 a := by
        apply Fin.ext
        rfl
      simp only [realEuclideanCoordinateReindex_apply, hcast]
      rw [hindex]
      simp only [realEuclideanAppend_castAdd]
  · have hindex :
        (finCongr h) (Fin.natAdd (n + 1) k) =
          Fin.natAdd n k.succ := by
      apply Fin.ext
      dsimp
      omega
    simp only [realEuclideanCoordinateReindex_apply,
      realEuclideanAppend_natAdd, hindex]
    rfl

/-- Old constituent parameters are the prefix of the new positive
parameter block, omitting the appended radial-or-minor level. -/
def sardianProjectionOldParameterBlock {q : ℕ}
    (newParameters : RealEuclidean ((q + 1) + 1)) :
    RealEuclidean (q + 1) :=
  fun i ↦ newParameters i.castSucc

/-- Exact new-to-old section lift for any last-equation choice, radial or
squared maximal minor. The old visible vector is literally
`realEuclideanAppend x (fun _ ↦ y 0)` for the hidden witness `y` supplied
by the new carrier. -/
theorem sardianProjectionAlgebraicConstituent_section_lifts_old
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (choice : SardianProjectionLastEquationChoice n q)
    (x : RealEuclidean n)
    (newParameters : RealEuclidean ((q + 1) + 1))
    (hnew : realEuclideanAppend x newParameters ∈
      (sardianProjectionAlgebraicConstituent
        hG hsmooth hderiv hn old choice).carrier) :
    ∃ erased : RealEuclidean 1,
      realEuclideanAppend (realEuclideanAppend x erased)
        (sardianProjectionOldParameterBlock newParameters) ∈
          old.carrier := by
  obtain ⟨hpositive, y, hprefix, _hlast⟩ :=
    (mem_sardianProjectionAlgebraicConstituent_carrier_iff
      hG hsmooth hderiv hn old choice x newParameters).mp hnew
  let erased : RealEuclidean 1 := fun _ ↦ y 0
  let oldHidden : RealEuclidean q := Fin.tail y
  have holdEquations : ∀ i : Fin (q + 1),
      old.equation i
          (realEuclideanAppend
            (realEuclideanAppend x erased) oldHidden) =
        sardianProjectionOldParameterBlock newParameters i := by
    intro i
    have hi := hprefix i
    change old.equation i
        (sardianProjectionOldInputReindex n q
          (realEuclideanAppend x y)) =
      newParameters i.castSucc at hi
    rw [sardianProjectionOldInputReindex_append_eq] at hi
    exact hi
  refine ⟨erased, ?_⟩
  rw [old.mem_carrier_iff]
  simp only [realEuclideanTakeLeft_append,
    realEuclideanTakeRight_append]
  constructor
  · exact ⟨oldHidden, holdEquations⟩
  · intro i
    exact hpositive i.castSucc

/-- The full modulus parameter tail has the same old-level prefix as the
new constituent's positive parameter block. -/
theorem sardianProjectionParameterTail_prefix
    {k : ℕ} (ε : RealEuclidean ((k + 1) + 1)) :
    CharbonnelModulus.parameterTail
        (sardianProjectionParameterPrefix ε) =
      (fun i : Fin k ↦
        (CharbonnelModulus.parameterTail ε) i.castSucc) := by
  funext i
  change ε (i.succ.castSucc) = ε (i.castSucc.succ)
  congr 1

/-- The precise `hsection` shape consumed by the generic from-below
reduction, for one old constituent and one chosen last equation. -/
theorem sardianProjectionAlgebraicConstituent_prefixSectionLift
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {order n q : ℕ} (hn : 0 < n)
    (old : CharbonnelSardianConstituent G (order + 1) (n + 1) q)
    (choice : SardianProjectionLastEquationChoice n q)
    (ε : RealEuclidean (((q + 1) + 1) + 1))
    (x : RealEuclidean n)
    (hnew : realEuclideanAppend x
        (CharbonnelModulus.parameterTail ε) ∈
      (sardianProjectionAlgebraicConstituent
        hG hsmooth hderiv hn old choice).carrier) :
    ∃ erased : RealEuclidean 1,
      realEuclideanAppend (realEuclideanAppend x erased)
        (CharbonnelModulus.parameterTail
          (sardianProjectionParameterPrefix ε)) ∈ old.carrier := by
  obtain ⟨erased, hold⟩ :=
    sardianProjectionAlgebraicConstituent_section_lifts_old
      hG hsmooth hderiv hn old choice x
        (CharbonnelModulus.parameterTail ε) hnew
  refine ⟨erased, ?_⟩
  rw [sardianProjectionParameterTail_prefix]
  exact hold

end AbelFormalization
