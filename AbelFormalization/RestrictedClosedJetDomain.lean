import AbelFormalization.RestrictedAdjunctionCanonicalCriticalSystem

/-!
# Closed restricted domains inside the Abel-jet domain

The reciprocal construction is closed using weak boundary inequalities.
For a finite offset family, the threshold can be chosen with one unit of
slack, so these weak inequalities still keep every shifted Abel argument
strictly positive.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- Closed weak-inequality version of the restricted base domain. -/
def restrictedBaseClosedDomain {m p a : ℕ} (D : RestrictedBox p) (R : ℝ) :
    Set (RestrictedSource m p a) :=
  {x | (∀ i, R ≤ x.1.1 i) ∧ x.1.2 ∈ D.closedBox}

theorem isClosed_restrictedBaseClosedDomain {m p a : ℕ}
    (D : RestrictedBox p) (R : ℝ) :
    IsClosed (restrictedBaseClosedDomain (m := m) (a := a) D R) := by
  have hs : IsClosed {x : RestrictedSource m p a | ∀ i, R ≤ x.1.1 i} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const
      ((continuous_apply i).comp (continuous_fst.comp continuous_fst))
  have hw : IsClosed {x : RestrictedSource m p a | x.1.2 ∈ D.closedBox} :=
    D.isClosed_closedBox.preimage (continuous_snd.comp continuous_fst)
  exact hs.inter hw

theorem restrictedBaseOpenDomain_subset_closedDomain {m p a : ℕ}
    (D : RestrictedBox p) (R : ℝ) :
    restrictedBaseOpenDomain (m := m) (a := a) D R ⊆
      restrictedBaseClosedDomain D R := by
  rintro x ⟨hs, hw⟩
  exact ⟨fun i ↦ (hs i).le, D.openBox_subset_closedBox hw⟩

/-- The admissible closed-domain condition is independent of the number of
unrestricted auxiliary coordinates.  Thus it persists after adjoining any
finite auxiliary block. -/
theorem restrictedBaseClosedDomain_subset_AbelJetDomain_addAux
    {m p a k : ℕ} {D : RestrictedBox p}
    (R : ℝ) (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset) :
    restrictedBaseClosedDomain (m := m) (a := a + k) D R ⊆
      restrictedAbelJetDomain (a := a + k) D representative offset := by
  intro x hx
  have hdrop : restrictedSourceDropAux k x ∈
      restrictedBaseClosedDomain (m := m) (a := a) D R := by
    exact ⟨hx.1, hx.2⟩
  have hjet := hDomain hdrop
  exact ⟨hjet.1, hjet.2⟩

/-- A finite analytic offset family admits a threshold whose entire closed
weak-inequality cylinder lies in the positive Abel-jet domain. -/
theorem exists_restrictedBaseClosedDomain_subset_AbelJetDomain
    [Finite ι] {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    ∃ R : ℝ, restrictedBaseClosedDomain (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset := by
  classical
  letI := Fintype.ofFinite ι
  have hbound : ∀ t : ι, ∃ C : ℝ, ∀ w ∈ D.closedBox,
      -(offset t : RestrictedBoxSpace p → ℝ) w ≤ C := by
    intro t
    have hcont : ContinuousOn
        (fun w ↦ -(offset t : RestrictedBoxSpace p → ℝ) w) D.closedBox :=
      (D.analyticNearClosedBox_iff.mp (offset t).property).continuousOn.neg
    obtain ⟨C, hC⟩ := D.isCompact_closedBox.bddAbove_image hcont
    refine ⟨C, ?_⟩
    intro w hw
    exact hC ⟨w, hw, rfl⟩
  choose C hC using hbound
  let R : ℝ := 1 + ∑ t : ι, max (C t) 0
  refine ⟨R, ?_⟩
  intro x hx
  constructor
  · exact hx.2
  · intro t
    change 0 < x.1.1 (representative t) +
      (offset t : RestrictedBoxSpace p → ℝ) x.1.2
    have hoff := hC t x.1.2 hx.2
    have hterm : C t ≤ ∑ u : ι, max (C u) 0 := by
      calc
        C t ≤ max (C t) 0 := le_max_left _ _
        _ ≤ ∑ u : ι, max (C u) 0 :=
          Finset.single_le_sum (fun u _ ↦ le_max_right (C u) 0)
            (Finset.mem_univ t)
    have hs := hx.1 (representative t)
    dsimp [R] at hs
    linarith

end AbelFormalization
