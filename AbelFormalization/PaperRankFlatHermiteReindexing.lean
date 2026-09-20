import AbelFormalization.OrderedClusterPrefixAlgebraicStep

/-!
# Reindexing retained paper-rank variables as flat Hermite variables

This file records the finite variable equivalence needed when rank elimination
is run with a complete family of flat Hermite coordinates.  The original
`Fin m` paper-rank variables become the auxiliary `q` variables.  The retained
variables enumerate all positive derivatives and retained time variables.

The construction is only a polynomial-variable relabeling.  It does not turn
the existing substitution of a selected family of Abel jets by Hermite
polynomials into an equivalence.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

/-- The non-`q` variables in a flat constant-order Hermite operation ring
have cardinality `m * (D + 1)`: `m * D` derivative variables and `m` time
variables. -/
theorem flatHermiteCentralIndex_card (m D : ℕ) :
    Fintype.card
      (CentralPolynomialIndex (Fin m) (fun _ ↦ D) (Fin m)) =
      m * (D + 1) := by
  classical
  simp [CentralPolynomialIndex, Nat.mul_add]

/-- Enumerate all derivative and time variables of a flat constant-order
Hermite operation ring by one `Fin` type. -/
def flatHermiteCentralIndexEquiv (m D : ℕ) :
    Fin (m * (D + 1)) ≃
      CentralPolynomialIndex (Fin m) (fun _ ↦ D) (Fin m) :=
  (finCongr (flatHermiteCentralIndex_card m D).symm).trans
    (Fintype.equivFin
      (CentralPolynomialIndex (Fin m) (fun _ ↦ D) (Fin m))).symm

/-- With exactly `m * (D + 1)` retained slots, the paper-rank symbols are a
relabeling of the flat Hermite operation symbols.  The original `Fin m`
variables are preserved as the auxiliary `q` variables. -/
def paperRankRetainedFlatHermiteEquiv (m D : ℕ) :
    PaperRankRetainedSymbols m (m * (D + 1)) ≃
      ClusterOperationSymbol (Fin m) (fun _ ↦ D) :=
  Equiv.sumCongr (Equiv.refl (Fin m)) (flatHermiteCentralIndexEquiv m D)

@[simp]
theorem paperRankRetainedFlatHermiteEquiv_apply_free
    (m D : ℕ) (i : Fin m) :
    paperRankRetainedFlatHermiteEquiv m D (Sum.inl i) = Sum.inl i :=
  rfl

@[simp]
theorem paperRankRetainedFlatHermiteEquiv_apply_retained
    (m D : ℕ) (j : Fin (m * (D + 1))) :
    paperRankRetainedFlatHermiteEquiv m D (Sum.inr j) =
      Sum.inr (flatHermiteCentralIndexEquiv m D j) :=
  rfl

/-- Reindex the retained paper-rank polynomial ring, with the complete flat
Hermite variable count, as the corresponding operation polynomial ring. -/
def paperRankRetainedFlatHermiteAlgEquiv
    (R : Type*) [CommSemiring R] (m D : ℕ) :
    MvPolynomial (PaperRankRetainedSymbols m (m * (D + 1))) R ≃ₐ[R]
      MvPolynomial (ClusterOperationSymbol (Fin m) (fun _ ↦ D)) R :=
  MvPolynomial.renameEquiv R (paperRankRetainedFlatHermiteEquiv m D)

@[simp]
theorem paperRankRetainedFlatHermiteAlgEquiv_apply_X_free
    (R : Type*) [CommSemiring R] (m D : ℕ) (i : Fin m) :
    paperRankRetainedFlatHermiteAlgEquiv R m D
        (MvPolynomial.X (Sum.inl i)) =
      MvPolynomial.X (Sum.inl i) := by
  simp [paperRankRetainedFlatHermiteAlgEquiv]

@[simp]
theorem paperRankRetainedFlatHermiteAlgEquiv_apply_X_retained
    (R : Type*) [CommSemiring R] (m D : ℕ)
    (j : Fin (m * (D + 1))) :
    paperRankRetainedFlatHermiteAlgEquiv R m D
        (MvPolynomial.X (Sum.inr j)) =
      MvPolynomial.X
        (Sum.inr (flatHermiteCentralIndexEquiv m D j)) := by
  simp [paperRankRetainedFlatHermiteAlgEquiv]

namespace RepresentativeClusterSubsequence

/-- At the full ordered-cluster prefix, the retained paper-rank ring with one
slot for every positive derivative and time variable is algebra-equivalent to
the canonical ordered-prefix ring. -/
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
