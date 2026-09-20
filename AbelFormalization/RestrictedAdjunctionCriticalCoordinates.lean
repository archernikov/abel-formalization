import AbelFormalization.SquaredDistanceProper

/-!
# Canonical coordinates for the adjunction critical system

After the graph variable and reciprocal variable are adjoined, the source
dimension is two greater than the original one.  The definitions below put
its canonical basis and coordinate functions in exactly the index shape used
by the square critical system.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Arithmetic reindexing between the flattened enlarged source and the
`(original dimension)+2` critical-system indexing. -/
def restrictedAdjunctionCriticalIndexEquiv (m p a : ℕ) :
    Fin ((m + p) + ((a + 1) + 1)) ≃
      Fin ((((m + p) + a) + 1) + 1) :=
  finCongr (by omega)

/-- The canonical basis of the twice-enlarged restricted source, indexed as
the critical system expects. -/
def restrictedAdjunctionCriticalBasis (m p a : ℕ) :
    Module.Basis (Fin ((((m + p) + a) + 1) + 1)) ℝ
      (RestrictedSource m p ((a + 1) + 1)) :=
  (restrictedSourceBasis m p ((a + 1) + 1)).reindex
    (restrictedAdjunctionCriticalIndexEquiv m p a)

/-- Scalar coordinates dual to `restrictedAdjunctionCriticalBasis`. -/
def restrictedAdjunctionCriticalCoordinates (m p a : ℕ) :
    Fin ((((m + p) + a) + 1) + 1) →
      RestrictedSource m p ((a + 1) + 1) → ℝ :=
  fun i x ↦ (restrictedAdjunctionCriticalBasis m p a).equivFun x i

theorem restrictedAdjunctionCriticalCoordinates_apply
    (m p a : ℕ) (i : Fin ((((m + p) + a) + 1) + 1))
    (x : RestrictedSource m p ((a + 1) + 1)) :
    restrictedAdjunctionCriticalCoordinates m p a i x =
      restrictedSourceCoordinates m p ((a + 1) + 1)
        ((restrictedAdjunctionCriticalIndexEquiv m p a).symm i) x := by
  change ((restrictedSourceBasis m p ((a + 1) + 1)).reindex
      (restrictedAdjunctionCriticalIndexEquiv m p a)).equivFun x i = _
  rw [Module.Basis.equivFun_apply, Module.Basis.repr_reindex_apply]
  simpa only [Module.Basis.equivFun_apply] using
    (restrictedSourceBasis_equivFun_apply m p ((a + 1) + 1) x
      ((restrictedAdjunctionCriticalIndexEquiv m p a).symm i))

/-- Every canonical critical-system coordinate is available at every tower
level. -/
theorem restrictedAdjunctionCriticalCoordinates_mem_level
    {A : ℝ → ℝ} {ι : Type*} {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := (a + 1) + 1)
        A representative offset) (ell := ell))
    (level : ℕ) :
    ∀ i, restrictedAdjunctionCriticalCoordinates m p a i ∈ T.level level := by
  intro i
  rw [show restrictedAdjunctionCriticalCoordinates m p a i =
      restrictedSourceCoordinates m p ((a + 1) + 1)
        ((restrictedAdjunctionCriticalIndexEquiv m p a).symm i) by
    funext x
    exact restrictedAdjunctionCriticalCoordinates_apply m p a i x]
  exact restrictedSourceCoordinates_mem_level T level _

/-- The canonical squared-distance function on the twice-enlarged source has
compact sublevels. -/
theorem isCompact_restrictedAdjunctionCriticalSquaredDistance_sublevel
    (m p a : ℕ)
    (center : Fin ((((m + p) + a) + 1) + 1) → ℝ) (R : ℝ) :
    IsCompact {x : RestrictedSource m p ((a + 1) + 1) |
      algebraicSquaredDistance
        (restrictedAdjunctionCriticalCoordinates m p a) center x ≤ R} := by
  exact isCompact_algebraicSquaredDistance_basis_sublevel
    (restrictedAdjunctionCriticalBasis m p a) center R

end AbelFormalization
