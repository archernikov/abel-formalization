import AbelFormalization.RestrictedAdjunctionCriticalExpressions

/-!
# Scalar coordinates of a restricted source

These coordinate functions use the same `s,w,y` order as
`restrictedSourceBasis`.  Every coordinate belongs to the restricted base
algebra and hence to every level of every restricted expression tower.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- All scalar coordinates of a restricted source, in the paper's order. -/
def restrictedSourceCoordinates (m p a : ℕ) :
    Fin ((m + p) + a) → RestrictedSource m p a → ℝ :=
  Fin.addCases
    (Fin.addCases
      (fun i x ↦ restrictedSCoordinate (p := p) (a := a) i x)
      (fun j x ↦ restrictedWCoordinate (m := m) (a := a) j x))
    (fun k x ↦ restrictedAuxCoordinate (m := m) (p := p) k x)

theorem restrictedSourceCoordinates_mem_base
    {m p a : ℕ} (D : RestrictedBox p)
    (S : Set (RestrictedSource m p a → ℝ)) :
    ∀ i, restrictedSourceCoordinates m p a i ∈
      restrictedExpressionBase D S := by
  intro i
  refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) i
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa [restrictedSourceCoordinates] using
        restrictedSCoordinate_mem_base D S j
    · simpa [restrictedSourceCoordinates] using
        restrictedWCoordinate_mem_base D S j
  · simpa [restrictedSourceCoordinates] using
      restrictedAuxCoordinate_mem_base D S k

theorem restrictedSourceCoordinates_mem_level
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (level : ℕ) :
    ∀ i, restrictedSourceCoordinates m p a i ∈ T.level level := by
  intro i
  exact T.base_mem_level (restrictedSourceCoordinates_mem_base D S i) level

/-- The explicit scalar coordinates are exactly the coefficient map of the
canonical restricted-source basis. -/
theorem restrictedSourceBasis_equivFun_apply
    (m p a : ℕ) (x : RestrictedSource m p a) (i : Fin ((m + p) + a)) :
    (restrictedSourceBasis m p a).equivFun x i =
      restrictedSourceCoordinates m p a i x := by
  refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) i
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [restrictedSourceBasis, restrictedSourceCoordinates,
        Module.Basis.equivFun_apply, restrictedSCoordinate]
    · simp [restrictedSourceBasis, restrictedSourceCoordinates,
        Module.Basis.equivFun_apply, restrictedWCoordinate]
  · simp [restrictedSourceBasis, restrictedSourceCoordinates,
      Module.Basis.equivFun_apply, restrictedAuxCoordinate]

end AbelFormalization
