import AbelFormalization.RestrictedLastGeneratorAdjunction

/-!
# A common positivity threshold for finitely many offsets

The restricted argument list is finite in the manuscript.  Compactness of
the closed coefficient box therefore supplies one threshold above which all
shifted Abel arguments are positive at once.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- A finite family of analytic offsets admits a common lower threshold for
all shifted Abel arguments. -/
theorem exists_restrictedBaseOpenDomain_subset_AbelJetDomain
    [Finite ι] {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    ∃ R : ℝ, restrictedBaseOpenDomain (a := a) D R ⊆
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
  · exact D.openBox_subset_closedBox hx.2
  · intro t
    change 0 < x.1.1 (representative t) +
      (offset t : RestrictedBoxSpace p → ℝ) x.1.2
    have hoff := hC t x.1.2 (D.openBox_subset_closedBox hx.2)
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
