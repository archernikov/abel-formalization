import AbelFormalization.RestrictedBoundedReclassificationTower
import AbelFormalization.RegularZeroLinearEquiv

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Reindex square equations after moving one source coordinate into the
bounded box. -/
def restrictedReclassificationEquationIndexEquiv (m p a : ℕ) :
    Fin (((m + 1) + p) + a) ≃ Fin ((m + (p + 1)) + a) :=
  finCongr (by omega)

/-- The corresponding coordinate permutation on equation-value spaces. -/
def restrictedReclassificationTargetEquiv (m p a : ℕ) :
    (Fin (((m + 1) + p) + a) → ℝ) ≃L[ℝ]
      (Fin ((m + (p + 1)) + a) → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ
    (fun _ : Fin ((m + (p + 1)) + a) ↦ ℝ)
    (restrictedReclassificationEquationIndexEquiv m p a)

/-- Reindex and pull back a square family along source reclassification. -/
def restrictedReclassifiedEquationFamily {m p a : ℕ}
    (i : Fin (m + 1))
    (F : Fin (((m + 1) + p) + a) →
      RestrictedSource (m + 1) p a → ℝ) :
    Fin ((m + (p + 1)) + a) → RestrictedSource m (p + 1) a → ℝ :=
  fun k x ↦ F ((restrictedReclassificationEquationIndexEquiv m p a).symm k)
    (restrictedSourceReclassifyAt i x)

theorem restrictedReclassificationTargetEquiv_apply
    {m p a : ℕ} (v : Fin (((m + 1) + p) + a) → ℝ)
    (k : Fin ((m + (p + 1)) + a)) :
    restrictedReclassificationTargetEquiv m p a v k =
      v ((restrictedReclassificationEquationIndexEquiv m p a).symm k) := by
  rfl

theorem constraintMap_restrictedReclassifiedEquationFamily
    {m p a : ℕ} (i : Fin (m + 1))
    (F : Fin (((m + 1) + p) + a) →
      RestrictedSource (m + 1) p a → ℝ) :
    constraintMap (restrictedReclassifiedEquationFamily i F) =
      restrictedReclassificationTargetEquiv m p a ∘
        constraintMap F ∘ restrictedSourceReclassifyAt i := by
  funext x k
  rfl

theorem regularZeroSet_restrictedReclassifiedEquationFamily
    {m p a : ℕ} (i : Fin (m + 1))
    (Omega : Set (RestrictedSource (m + 1) p a))
    (F : Fin (((m + 1) + p) + a) →
      RestrictedSource (m + 1) p a → ℝ) :
    regularZeroSet (restrictedSourceReclassifyAt i ⁻¹' Omega)
        (constraintMap (restrictedReclassifiedEquationFamily i F)) =
      restrictedSourceReclassifyAt i ⁻¹'
        regularZeroSet Omega (constraintMap F) := by
  rw [constraintMap_restrictedReclassifiedEquationFamily]
  exact regularZeroSet_preimage_continuousLinearEquiv
    (restrictedSourceReclassifyAt i)
    (restrictedReclassificationTargetEquiv m p a) Omega (constraintMap F)

/-- Finiteness of a square regular-zero set is unchanged by the simultaneous
source reclassification and equation-coordinate permutation. -/
theorem finite_regularZeroSet_restrictedReclassifiedEquationFamily_iff
    {m p a : ℕ} (i : Fin (m + 1))
    (Omega : Set (RestrictedSource (m + 1) p a))
    (F : Fin (((m + 1) + p) + a) →
      RestrictedSource (m + 1) p a → ℝ) :
    (regularZeroSet (restrictedSourceReclassifyAt i ⁻¹' Omega)
      (constraintMap (restrictedReclassifiedEquationFamily i F))).Finite ↔
      (regularZeroSet Omega (constraintMap F)).Finite := by
  rw [constraintMap_restrictedReclassifiedEquationFamily]
  exact finite_regularZeroSet_comp_continuousLinearEquiv_iff
    (restrictedSourceReclassifyAt i)
    (restrictedReclassificationTargetEquiv m p a) Omega (constraintMap F)

/-- The exact bounded-slice form used by the outer induction: the new open
domain is the preimage of the old open domain cut by `s_i < M`. -/
theorem finite_regularZeroSet_reclassifyAt_slice_iff
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (i : Fin (m + 1))
    (F : Fin (((m + 1) + p) + a) →
      RestrictedSource (m + 1) p a → ℝ) :
    (regularZeroSet (restrictedBaseOpenDomain (D.snoc R M hRM) R)
      (constraintMap (restrictedReclassifiedEquationFamily i F))).Finite ↔
      (regularZeroSet
        (restrictedBaseOpenDomain D R ∩ {x | x.1.1 i < M})
        (constraintMap F)).Finite := by
  rw [← preimage_restrictedBaseOpenDomain_slice_reclassifyAt
    D R M hRM i]
  exact finite_regularZeroSet_restrictedReclassifiedEquationFamily_iff
    i _ F

end AbelFormalization
