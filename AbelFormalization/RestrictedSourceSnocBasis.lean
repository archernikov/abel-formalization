import AbelFormalization.RestrictedComparisonTransversality

noncomputable section


namespace AbelFormalization

set_option autoImplicit false

/-- Extend any basis of a restricted source by its final auxiliary
coordinate, using the canonical splitting of that coordinate. -/
def restrictedSourceAuxOneBasis {m p a n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a)) :
    Module.Basis (Fin (n + 1)) ℝ (RestrictedSource m p (a + 1)) :=
  (graphProductBasis basis).map
    restrictedSourceAuxOneContinuousLinearEquiv.symm.toLinearEquiv

@[simp]
theorem restrictedSourceAuxOneBasis_apply {m p a n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (i : Fin (n + 1)) :
    restrictedSourceAuxOneBasis basis i =
      restrictedSourceAuxOneContinuousLinearEquiv.symm
        (graphProductBasis basis i) :=
  rfl

/-- Extend a restricted-source basis by two successive auxiliary
coordinates, as required by the closed adjunction curve. -/
def restrictedSourceAuxTwoBasis {m p a n : ℕ}
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a)) :
    Module.Basis (Fin ((n + 1) + 1)) ℝ
      (RestrictedSource m p ((a + 1) + 1)) :=
  restrictedSourceAuxOneBasis
    (restrictedSourceAuxOneBasis basis)

end AbelFormalization
