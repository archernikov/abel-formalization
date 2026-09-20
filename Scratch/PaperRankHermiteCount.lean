import AbelFormalization.PaperRankFlatHermiteReindexing
import AbelFormalization.RestrictedHermiteJetBlockification

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

variable {ι : Type*}

/-- The derivative bound used by ordered-cluster descent after retaining the
complete Hermite coefficient family. -/
abbrev paperRankHermiteHigherCount (S : Finset (ι × ℕ)) : ℕ :=
  paperRankHermiteCoefficientCount S - 2

theorem two_le_paperRankHermiteCoefficientCount
    (S : Finset (ι × ℕ)) :
    2 ≤ paperRankHermiteCoefficientCount S := by
  classical
  unfold paperRankHermiteCoefficientCount totalMultiplicity
  have hle : paperRankHermiteNodeMultiplicity S none ≤
      ∑ i : Option (Fin S.card), paperRankHermiteNodeMultiplicity S i := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (none : Option (Fin S.card)))
  simpa [paperRankHermiteNodeMultiplicity] using hle

@[simp]
theorem paperRankHermiteHigherCount_add_two
    (S : Finset (ι × ℕ)) :
    paperRankHermiteHigherCount S + 2 =
      paperRankHermiteCoefficientCount S := by
  exact Nat.sub_add_cancel (two_le_paperRankHermiteCoefficientCount S)

@[simp]
theorem paperRankHermiteHigherCount_add_one
    (S : Finset (ι × ℕ)) :
    paperRankHermiteHigherCount S + 1 =
      paperRankHermitePositiveDerivativeCount S := by
  change (paperRankHermiteCoefficientCount S - 2) + 1 =
    paperRankHermiteCoefficientCount S - 1
  have htwo := two_le_paperRankHermiteCoefficientCount S
  omega

end AbelFormalization
