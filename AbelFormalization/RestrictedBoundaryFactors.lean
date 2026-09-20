import AbelFormalization.CanonicalDenominatorLift

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- The paper's boundary factors `sᵢ-R`, `wⱼ-αⱼ`, `βⱼ-wⱼ`, and `Y`,
in that order. -/
def restrictedBoundaryFactors {m p a : ℕ} (D : RestrictedBox p) (R : ℝ) :
    Fin (m + (p + (p + 1))) → RestrictedSource m p (a + 1) → ℝ :=
  Fin.addCases
    (fun i x ↦ restrictedSCoordinate (p := p) (a := a + 1) i x - R)
    (Fin.addCases
      (fun j x ↦ restrictedWCoordinate (m := m) (a := a + 1) j x - D.lower j)
      (Fin.addCases
        (fun j x ↦ D.upper j -
          restrictedWCoordinate (m := m) (a := a + 1) j x)
        (fun _ x ↦ restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) x)))

theorem restrictedBoundaryFactors_pos_iff {m p a : ℕ}
    (D : RestrictedBox p) (R : ℝ) (x : RestrictedSource m p (a + 1)) :
    (∀ i, 0 < restrictedBoundaryFactors D R i x) ↔
      (∀ i, R < x.1.1 i) ∧ x.1.2 ∈ D.openBox ∧ 0 < x.2 (Fin.last a) := by
  simp only [restrictedBoundaryFactors, Fin.forall_fin_add,
    Fin.addCases_left, Fin.addCases_right, sub_pos, D.mem_openBox,
    restrictedSCoordinate, restrictedWCoordinate, restrictedAuxCoordinate]
  constructor
  · rintro ⟨hs, hl, hu, hY⟩
    exact ⟨hs, fun i ↦ ⟨hl i, hu i⟩, hY 0⟩
  · rintro ⟨hs, hw, hY⟩
    exact ⟨hs, fun i ↦ (hw i).1, fun i ↦ (hw i).2, fun _ ↦ hY⟩

theorem restrictedBoundaryFactors_nonneg_iff {m p a : ℕ}
    (D : RestrictedBox p) (R : ℝ) (x : RestrictedSource m p (a + 1)) :
    (∀ i, 0 ≤ restrictedBoundaryFactors D R i x) ↔
      (∀ i, R ≤ x.1.1 i) ∧ x.1.2 ∈ D.closedBox ∧ 0 ≤ x.2 (Fin.last a) := by
  simp only [restrictedBoundaryFactors, Fin.forall_fin_add,
    Fin.addCases_left, Fin.addCases_right, sub_nonneg, D.mem_closedBox,
    restrictedSCoordinate, restrictedWCoordinate, restrictedAuxCoordinate]
  constructor
  · rintro ⟨hs, hl, hu, hY⟩
    exact ⟨hs, fun i ↦ ⟨hl i, hu i⟩, hY 0⟩
  · rintro ⟨hs, hw, hY⟩
    exact ⟨hs, fun i ↦ (hw i).1, fun i ↦ (hw i).2, fun _ ↦ hY⟩

theorem continuous_restrictedBoundaryFactors {m p a : ℕ}
    (D : RestrictedBox p) (R : ℝ) :
    ∀ i, Continuous
      (restrictedBoundaryFactors (m := m) (a := a) D R i) := by
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) i
  · simp only [restrictedBoundaryFactors, Fin.addCases_left]
    unfold restrictedSCoordinate
    fun_prop
  · refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) i
    · simp only [restrictedBoundaryFactors, Fin.addCases_right,
        Fin.addCases_left]
      unfold restrictedWCoordinate
      fun_prop
    · refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) i
      · simp only [restrictedBoundaryFactors, Fin.addCases_right,
          Fin.addCases_left]
        unfold restrictedWCoordinate
        fun_prop
      · simp only [restrictedBoundaryFactors, Fin.addCases_right]
        unfold restrictedAuxCoordinate
        fun_prop

theorem restrictedBoundaryFactors_mem_base
    {m p a : ℕ} (D : RestrictedBox p) (R : ℝ)
    (S : Set (RestrictedSource m p (a + 1) → ℝ)) :
    ∀ i, restrictedBoundaryFactors D R i ∈ restrictedExpressionBase D S := by
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) i
  · simp only [restrictedBoundaryFactors, Fin.addCases_left]
    exact (restrictedExpressionBase D S).sub_mem
      (restrictedSCoordinate_mem_base D S j)
      ((restrictedExpressionBase D S).algebraMap_mem R)
  · refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) i
    · simp only [restrictedBoundaryFactors, Fin.addCases_right,
        Fin.addCases_left]
      exact (restrictedExpressionBase D S).sub_mem
        (restrictedWCoordinate_mem_base D S j)
        ((restrictedExpressionBase D S).algebraMap_mem (D.lower j))
    · refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) i
      · simp only [restrictedBoundaryFactors, Fin.addCases_right,
          Fin.addCases_left]
        exact (restrictedExpressionBase D S).sub_mem
          ((restrictedExpressionBase D S).algebraMap_mem (D.upper j))
          (restrictedWCoordinate_mem_base D S j)
      · simp only [restrictedBoundaryFactors, Fin.addCases_right]
        exact restrictedAuxCoordinate_mem_base D S (Fin.last a)

theorem RestrictedExpressionTower.restrictedBoundaryFactors_mem_level
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p (a + 1) → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell))
    (R : ℝ) (level : ℕ) :
    ∀ i, restrictedBoundaryFactors D R i ∈ T.level level := by
  intro i
  exact T.base_mem_level (restrictedBoundaryFactors_mem_base D R S i) level

end AbelFormalization
