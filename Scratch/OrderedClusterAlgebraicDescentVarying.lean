import AbelFormalization.OrderedClusterAlgebraicDescent

noncomputable section
set_option autoImplicit false

namespace AbelFormalization
namespace RepresentativeClusterSubsequence

universe u

theorem test_exists_orderedClusterPrefixAlgebraicDescent_varying
    (R : Type u) [CommRing R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    (higher : ℕ)
    (initialIdeal : Ideal
      (data.OrderedClusterPrefixRing R higher data.orderedClusterCount))
    (krullDim : ℕ → ℕ)
    [∀ k, Algebra ℚ (data.OrderedClusterPrefixRing R higher k)]
    [∀ k, IsNoetherianRing
      (data.OrderedClusterPrefixRing R higher k)]
    [∀ k, Ring.KrullDimLE (krullDim k)
      (data.OrderedClusterPrefixRing R higher k)] :
    ∃ finalIdeal : Ideal (data.OrderedClusterPrefixRing R higher 0),
      Nonempty (OrderedClusterPrefixAlgebraicDescent R data higher
        initialIdeal 0 (Nat.zero_le _) finalIdeal) := by
  let motive := fun (k : ℕ) (hk : k ≤ data.orderedClusterCount) ↦
    ∃ stageIdeal : Ideal (data.OrderedClusterPrefixRing R higher k),
      Nonempty (OrderedClusterPrefixAlgebraicDescent R data higher
        initialIdeal k hk stageIdeal)
  exact Nat.decreasingInduction (n := data.orderedClusterCount)
    (motive := motive)
    (fun k hk ih ↦ by
      obtain ⟨nextIdeal, ⟨tail⟩⟩ := ih
      let c : Fin data.orderedClusterCount := ⟨k, hk⟩
      let certificate := Classical.choice
        (data.nonempty_orderedClusterPrefixAlgebraicReductionCertificate
          R higher c nextIdeal (krullDim := krullDim k))
      exact ⟨certificate.terminalized.coefficientIdeal,
        ⟨OrderedClusterPrefixAlgebraicDescent.step k hk tail certificate⟩⟩)
    ⟨initialIdeal, ⟨OrderedClusterPrefixAlgebraicDescent.top⟩⟩
    (Nat.zero_le _)

end RepresentativeClusterSubsequence
end AbelFormalization
