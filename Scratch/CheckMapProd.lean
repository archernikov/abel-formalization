import AbelFormalization.TerminalTimeQuantitativeBridge
import AbelFormalization.PolynomialGermSymbolMaps

open Filter
open scoped BigOperators Topology

namespace AbelFormalization

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (h : ℕ) (higher : Fin h → ℕ) :
    analyticPolynomialGermHom x
        (terminalFirstDerivativeProduct (AnalyticGermAt x) (Fin h) h higher) =
      ((fun _ : E ↦ terminalFirstDerivativeProduct ℝ (Fin h) h higher) :
        Germ (𝓝 x)
          (TerminalMultiblockSourceRing ℝ h higher (Fin h))) := by
  rw [terminalFirstDerivativeProduct_eq_prod,
    terminalFirstDerivativeProduct_eq_prod, map_prod]
  have hfun :
      (fun _ : E => ∏ b : Fin h,
        (MvPolynomial.X (Sum.inl ⟨b, (0 : Fin (higher b + 1))⟩) :
          TerminalMultiblockSourceRing ℝ h higher (Fin h))) =
        ∏ b : Fin h, fun _ : E =>
          (MvPolynomial.X (Sum.inl ⟨b, (0 : Fin (higher b + 1))⟩) :
            TerminalMultiblockSourceRing ℝ h higher (Fin h)) := by
    funext y
    simp only [Finset.prod_apply]
  rw [hfun]
  change (∏ b : Fin h, analyticPolynomialGermHom x
      (MvPolynomial.X (Sum.inl ⟨b, (0 : Fin (higher b + 1))⟩))) =
    Germ.coeRingHom (𝓝 x)
      (∏ b : Fin h, fun _ : E =>
        (MvPolynomial.X (Sum.inl ⟨b, (0 : Fin (higher b + 1))⟩) :
          TerminalMultiblockSourceRing ℝ h higher (Fin h)))
  rw [map_prod]
  simp only [analyticPolynomialGermHom_X]
  apply Finset.prod_congr rfl
  intro b hb
  rfl

end AbelFormalization
