import AbelFormalization.RestrictedBoundedReclassification
import AbelFormalization.RestrictedClosedJetDomain

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Reclassifying one representative as a bounded coordinate identifies the
new base domain with the old base domain cut by an upper bound on that
representative. -/
theorem preimage_restrictedBaseOpenDomain_slice_reclassifyAt
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (i : Fin (m + 1)) :
    restrictedSourceReclassifyAt (p := p) (a := a) i ⁻¹'
        (restrictedBaseOpenDomain D R ∩
          {x | x.1.1 i < M}) =
      restrictedBaseOpenDomain (D.snoc R M hRM) R := by
  ext x
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hs, hw⟩, hM⟩
    refine ⟨?_, ?_⟩
    · intro j
      simpa using hs (i.succAbove j)
    · rw [D.mem_openBox_snoc]
      refine ⟨?_, ?_, ?_⟩
      · simpa using hw
      · simpa using hs i
      · simpa using hM
  · rintro ⟨hs, hw⟩
    rw [D.mem_openBox_snoc] at hw
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro j
      refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j
      · simpa using hw.2.1
      · simpa using hs k
    · simpa using hw.1
    · simpa using hw.2.2

/-- The analogous exact identity for the weak closed domains. -/
theorem preimage_restrictedBaseClosedDomain_slice_reclassifyAt
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (i : Fin (m + 1)) :
    restrictedSourceReclassifyAt (p := p) (a := a) i ⁻¹'
        (restrictedBaseClosedDomain D R ∩
          {x | x.1.1 i ≤ M}) =
      restrictedBaseClosedDomain (D.snoc R M hRM) R := by
  ext x
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hs, hw⟩, hM⟩
    refine ⟨?_, ?_⟩
    · intro j
      simpa using hs (i.succAbove j)
    · rw [D.mem_closedBox_snoc]
      refine ⟨?_, ?_, ?_⟩
      · simpa using hw
      · simpa using hs i
      · simpa using hM
  · rintro ⟨hs, hw⟩
    rw [D.mem_closedBox_snoc] at hw
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro j
      refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j
      · simpa using hw.2.1
      · simpa using hs k
    · simpa using hw.1
    · simpa using hw.2.2

/-- In particular, the reclassified closed domain maps into the original
closed domain. -/
theorem mapsTo_restrictedBaseClosedDomain_reclassifyAt
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (i : Fin (m + 1)) :
    MapsTo (restrictedSourceReclassifyAt (p := p) (a := a) i)
      (restrictedBaseClosedDomain (D.snoc R M hRM) R)
      (restrictedBaseClosedDomain D R) := by
  intro x hx
  have hx' : x ∈ restrictedSourceReclassifyAt (p := p) (a := a) i ⁻¹'
      (restrictedBaseClosedDomain D R ∩ {y | y.1.1 i ≤ M}) := by
    rw [preimage_restrictedBaseClosedDomain_slice_reclassifyAt]
    exact hx
  exact hx'.1

end AbelFormalization
