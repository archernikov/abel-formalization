import AbelFormalization.OrderedClusterPrefixAlgebraicStep

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

/-- The non-`q` variables in a flat constant-order Hermite operation ring
have cardinality `m * (D + 1)`: `m * D` derivative variables and `m` time
variables. -/
theorem card_flatHermiteCentralIndex (m D : ℕ) :
    Fintype.card
      (CentralPolynomialIndex (Fin m) (fun _ ↦ D) (Fin m)) =
      m * (D + 1) := by
  classical
  simp [CentralPolynomialIndex, Nat.mul_add]

/-- Canonically enumerate all derivative and time variables of a flat
constant-order Hermite operation ring by one `Fin` type. -/
def flatHermiteCentralIndexEquiv (m D : ℕ) :
    Fin (m * (D + 1)) ≃
      CentralPolynomialIndex (Fin m) (fun _ ↦ D) (Fin m) :=
  (finCongr (card_flatHermiteCentralIndex m D).symm).trans
    (Fintype.equivFin
      (CentralPolynomialIndex (Fin m) (fun _ ↦ D) (Fin m))).symm

/-- With exactly `m * (D + 1)` retained jet slots, the paper-rank symbols
are a relabeling of the flat Hermite operation symbols. The original `Fin m`
variables are preserved as the auxiliary `q` variables. -/
def paperRankRetainedFlatHermiteEquiv (m D : ℕ) :
    PaperRankRetainedSymbols m (m * (D + 1)) ≃
      ClusterOperationSymbol (Fin m) (fun _ ↦ D) :=
  Equiv.sumCongr (Equiv.refl (Fin m)) (flatHermiteCentralIndexEquiv m D)

@[simp]
theorem paperRankRetainedFlatHermiteEquiv_free
    (m D : ℕ) (i : Fin m) :
    paperRankRetainedFlatHermiteEquiv m D (Sum.inl i) = Sum.inl i :=
  rfl

@[simp]
theorem paperRankRetainedFlatHermiteEquiv_jet
    (m D : ℕ) (j : Fin (m * (D + 1))) :
    paperRankRetainedFlatHermiteEquiv m D (Sum.inr j) =
      Sum.inr (flatHermiteCentralIndexEquiv m D j) :=
  rfl

/-- Polynomial reindexing from the retained rank ring with the exact flat
Hermite variable count to the flat Hermite operation ring. -/
def paperRankRetainedFlatHermiteAlgEquiv
    (R : Type*) [CommSemiring R] (m D : ℕ) :
    MvPolynomial (PaperRankRetainedSymbols m (m * (D + 1))) R ≃ₐ[R]
      MvPolynomial (ClusterOperationSymbol (Fin m) (fun _ ↦ D)) R :=
  MvPolynomial.renameEquiv R (paperRankRetainedFlatHermiteEquiv m D)

@[simp]
theorem paperRankRetainedFlatHermiteAlgEquiv_X_free
    (R : Type*) [CommSemiring R] (m D : ℕ) (i : Fin m) :
    paperRankRetainedFlatHermiteAlgEquiv R m D
        (MvPolynomial.X (Sum.inl i)) =
      MvPolynomial.X (Sum.inl i) := by
  simp [paperRankRetainedFlatHermiteAlgEquiv]

@[simp]
theorem paperRankRetainedFlatHermiteAlgEquiv_X_jet
    (R : Type*) [CommSemiring R] (m D : ℕ)
    (j : Fin (m * (D + 1))) :
    paperRankRetainedFlatHermiteAlgEquiv R m D
        (MvPolynomial.X (Sum.inr j)) =
      MvPolynomial.X
        (Sum.inr (flatHermiteCentralIndexEquiv m D j)) := by
  simp [paperRankRetainedFlatHermiteAlgEquiv]

namespace RepresentativeClusterSubsequence

/-- At the full ordered-cluster prefix, the retained rank ring with one slot
for every positive derivative and time variable is algebra-equivalent to the
canonical ordered-prefix ring. -/
def paperRankRetainedTopPrefixAlgEquiv
    (R : Type*) [CommSemiring R]
    {m : ℕ} {time : ℕ → Fin m → ℝ}
    (data : RepresentativeClusterSubsequence time) (higher : ℕ) :
    MvPolynomial
        (PaperRankRetainedSymbols m (m * (higher + 2))) R ≃ₐ[R]
      data.OrderedClusterPrefixRing R higher data.orderedClusterCount := by
  let flat := paperRankRetainedFlatHermiteAlgEquiv R m (higher + 1)
  let topRename := clusterOperationRenameAlgEquiv R
    data.orderedClusterPrefixTopEquiv
    (fun _ : Fin m ↦ higher + 1)
    (data.orderedClusterPrefixConstantDerivativeCount
      (higher + 1) data.orderedClusterCount)
    (fun _ ↦ rfl)
  simpa only [Nat.add_assoc, Nat.reduceAdd] using flat.trans topRename

end RepresentativeClusterSubsequence
end AbelFormalization
