import AbelFormalization.WilkieFiniteVisibleProjectionFork
import AbelFormalization.WilkieVerticalMinorDerivativeBridge
import Mathlib.Logic.Equiv.Fintype

/-!
# An arbitrary maximal column minor supplies a square chart

A permutation sends the standard last `k` source columns to the chosen
embedding.  Reindexing the source turns the chosen minor into the vertical
minor of a conjugated map, so the existing vertical derivative bridge gives
the square chart for the complementary coordinate projection.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Extend the chosen `k` columns to a permutation of all source columns. -/
private noncomputable def wilkieColumnPermutation {n k : ℕ}
    (cols : Fin k ↪ Fin (n + k)) : Equiv.Perm (Fin (n + k)) :=
  Classical.choose <|
    Equiv.Perm.exists_extending_pair
      (Fin.natAdd n) cols (Fin.natAddEmb n).injective cols.injective

private theorem wilkieColumnPermutation_natAdd {n k : ℕ}
    (cols : Fin k ↪ Fin (n + k)) (j : Fin k) :
    wilkieColumnPermutation cols (Fin.natAdd n j) = cols j :=
  Classical.choose_spec
    (Equiv.Perm.exists_extending_pair
      (Fin.natAdd n) cols (Fin.natAddEmb n).injective cols.injective) j

/-- New source coordinate `t` records the old coordinate in column
`wilkieColumnPermutation cols t`. -/
private noncomputable def wilkieColumnReorder {n k : ℕ}
    (cols : Fin k ↪ Fin (n + k)) :
    RealEuclidean (n + k) ≃L[ℝ] RealEuclidean (n + k) :=
  (LinearEquiv.piCongrLeft' ℝ (fun _ : Fin (n + k) ↦ ℝ)
    (wilkieColumnPermutation cols).symm).toContinuousLinearEquiv

private theorem wilkieColumnReorder_apply {n k : ℕ}
    (cols : Fin k ↪ Fin (n + k)) (v : RealEuclidean (n + k))
    (t : Fin (n + k)) :
    wilkieColumnReorder cols v t =
      v (wilkieColumnPermutation cols t) := rfl

private theorem wilkieColumnReorder_symm_apply {n k : ℕ}
    (cols : Fin k ↪ Fin (n + k)) (v : RealEuclidean (n + k))
    (t : Fin (n + k)) :
    (wilkieColumnReorder cols).symm v t =
      v ((wilkieColumnPermutation cols).symm t) := by
  simp [wilkieColumnReorder, LinearEquiv.piCongrLeft',
    Equiv.piCongrLeft'_symm]

/-- Projection onto the `n` coordinates complementary to `cols`, in the
order chosen by `wilkieColumnPermutation`. -/
noncomputable def wilkieColumnComplementaryProjection {n k : ℕ}
    (cols : Fin k ↪ Fin (n + k)) :
    RealEuclidean (n + k) →L[ℝ] RealEuclidean n :=
  (realEuclideanTakeLeftContinuousLinearMap n k).comp
    (wilkieColumnReorder cols : RealEuclidean (n + k) →L[ℝ]
      RealEuclidean (n + k))

/-- A nonzero minor in arbitrary source columns gives a strictly
differentiable square map with an invertible derivative. -/
theorem wilkieColumnComplementarySquareMap_hasStrictFDerivAt_of_minor
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (cols : Fin k ↪ Fin (n + k))
    {y : RealEuclidean (n + k)}
    (hminor : standardJacobianColumnMinor F cols y ≠ 0) :
    ∃ L : RealEuclidean (n + k) ≃L[ℝ]
        (RealEuclidean n × RealEuclidean k),
      HasStrictFDerivAt
        (fun z ↦ (wilkieColumnComplementaryProjection cols z, F z))
        (L : RealEuclidean (n + k) →L[ℝ]
          (RealEuclidean n × RealEuclidean k)) y := by
  let σ : Equiv.Perm (Fin (n + k)) := wilkieColumnPermutation cols
  let R : RealEuclidean (n + k) ≃L[ℝ] RealEuclidean (n + k) :=
    wilkieColumnReorder cols
  let G : RealEuclidean (n + k) → RealEuclidean k := F ∘ R.symm
  have hG : ContDiff ℝ 1 G := hF.comp R.symm.contDiff
  have hbasis (j : Fin k) :
      R.symm ((Pi.basisFun ℝ (Fin (n + k))) (Fin.natAdd n j)) =
        ((Pi.basisFun ℝ (Fin (n + k))) (cols j)) := by
    funext t
    change (wilkieColumnReorder cols).symm
      ((Pi.basisFun ℝ (Fin (n + k))) (Fin.natAdd n j)) t =
        ((Pi.basisFun ℝ (Fin (n + k))) (cols j)) t
    rw [wilkieColumnReorder_symm_apply]
    simp only [Pi.basisFun_apply]
    by_cases ht : t = cols j
    · subst t
      have hs : (wilkieColumnPermutation cols).symm (cols j) =
          Fin.natAdd n j := by
        rw [← wilkieColumnPermutation_natAdd cols j,
          Equiv.symm_apply_apply]
      simp [hs]
    · have hs : (wilkieColumnPermutation cols).symm t ≠
          Fin.natAdd n j := by
        intro heq
        have heq' : t = cols j := by
          calc
            t = σ (σ.symm t) := (σ.apply_symm_apply t).symm
            _ = σ (Fin.natAdd n j) := by rw [heq]
            _ = cols j := wilkieColumnPermutation_natAdd cols j
        exact ht heq'
      simp [ht, hs]
  have hJac :
      (standardRectangularJacobian G (R y)).submatrix id
          (Fin.natAddEmb n) =
        (standardRectangularJacobian F y).submatrix id cols := by
    ext i j
    change fderiv ℝ
        ((fun z : RealEuclidean (n + k) ↦ F z i) ∘ R.symm)
        (R y) ((Pi.basisFun ℝ (Fin (n + k))) (Fin.natAdd n j)) =
      fderiv ℝ (fun z : RealEuclidean (n + k) ↦ F z i) y
        ((Pi.basisFun ℝ (Fin (n + k))) (cols j))
    rw [R.symm.comp_right_fderiv, R.symm_apply_apply]
    change fderiv ℝ (fun z : RealEuclidean (n + k) ↦ F z i) y
        (R.symm ((Pi.basisFun ℝ (Fin (n + k))) (Fin.natAdd n j))) = _
    rw [hbasis]
  have hminorG : standardJacobianColumnMinor G (Fin.natAddEmb n) (R y) ≠ 0 := by
    have hEq : standardJacobianColumnMinor G (Fin.natAddEmb n) (R y) =
        standardJacobianColumnMinor F cols y := by
      change ((standardRectangularJacobian G (R y)).submatrix id
        (Fin.natAddEmb n)).det =
        ((standardRectangularJacobian F y).submatrix id cols).det
      exact congrArg Matrix.det hJac
    rw [hEq]
    exact hminor
  obtain ⟨L₀, hL₀⟩ :=
    wilkieVisibleFiberSquareMap_hasStrictFDerivAt_of_verticalMinor hG hminorG
  let L : RealEuclidean (n + k) ≃L[ℝ]
      (RealEuclidean n × RealEuclidean k) := R.trans L₀
  refine ⟨L, ?_⟩
  have hcomp := hL₀.comp y R.hasStrictFDerivAt
  have hMapEq :
      (fun z ↦ wilkieVisibleFiberSquareMap G (R z)) =
        (fun z ↦ (wilkieColumnComplementaryProjection cols z, F z)) := by
    funext z
    apply Prod.ext
    · rfl
    · change F (R.symm (R z)) = F z
      exact congrArg F (R.symm_apply_apply z)
  rw [hMapEq] at hcomp
  have hderiv :
      (L : RealEuclidean (n + k) →L[ℝ]
        (RealEuclidean n × RealEuclidean k)) =
      (L₀ : RealEuclidean (n + k) →L[ℝ]
        (RealEuclidean n × RealEuclidean k)).comp
        (R : RealEuclidean (n + k) →L[ℝ]
          RealEuclidean (n + k)) := rfl
  simpa only [hderiv] using hcomp

/-- The fixed complementary projection supplies the `hSquare` premise on
the entire full fiber component. -/
theorem wilkieColumnComplementaryProjection_fullComponent_squareChart
    {n k : ℕ} {F : RealEuclidean (n + k) → RealEuclidean k}
    (hF : ContDiff ℝ 1 F) (a : RealEuclidean k)
    {x : RealEuclidean (n + k)} (cols : Fin k ↪ Fin (n + k)) :
    ∀ y ∈ wilkieFullFiberComponent F a x,
      standardJacobianColumnMinor F cols y ≠ 0 →
      ∃ L : RealEuclidean (n + k) ≃L[ℝ]
          (RealEuclidean n × RealEuclidean k),
        HasStrictFDerivAt
          (fun z ↦ (wilkieColumnComplementaryProjection cols z, F z))
          (L : RealEuclidean (n + k) →L[ℝ]
            (RealEuclidean n × RealEuclidean k)) y := by
  intro y _ hyMinor
  exact wilkieColumnComplementarySquareMap_hasStrictFDerivAt_of_minor
    hF cols hyMinor

end AbelFormalization
