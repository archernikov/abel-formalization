import AbelFormalization.RestrictedOrderedClusterPartition

namespace AbelFormalization

namespace RepresentativeClusterSubsequence

set_option autoImplicit false

theorem test_orderedClusterCount_pos_of_nonempty
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time)
    [Nonempty (Fin m)] :
    0 < data.orderedClusterCount := by
  let i : Fin m := Classical.choice (inferInstance : Nonempty (Fin m))
  obtain ⟨c, _hc⟩ := data.exists_mem_orderedCluster i
  exact lt_of_le_of_lt (Nat.zero_le c) c.isLt

end RepresentativeClusterSubsequence
end AbelFormalization
