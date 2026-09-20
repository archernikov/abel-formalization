import AbelFormalization.WilkieArbitraryMinorDerivativeBridge

open AbelFormalization

example (n : ℕ) (hn : 0 < n) : Nontrivial (RealEuclidean n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  infer_instance

example (n : ℕ) (hn : 0 < n) : NoncompactSpace (RealEuclidean n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  infer_instance

example (n : ℕ) : ConnectedSpace (RealEuclidean n) := by
  infer_instance
