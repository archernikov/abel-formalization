import AbelFormalization.TerminalGlobalMultiblockBridge
import AbelFormalization.TerminalLocalizedMultigradingBridge

set_option autoImplicit false

/-!
# Terminal algebraic elimination from the global symmetries

The global multigrading and signed-Stirling invariance supply both inputs to
the simultaneous terminal localization argument: preservation by every
blockwise triangular field and closure under every localized total-degree
component.  The localized ideal is therefore extended from the retained
coefficient ring.
-/

noncomputable section

namespace AbelFormalization

/-- End-to-end terminal algebraic elimination.  A globally multigraded ideal
which is invariant under the global signed-Stirling action becomes, after
simultaneous localization of the first variable in every block, the extension
of its contraction to the retained-variable coefficient ring. -/
theorem terminalGlobalStirlingInvariant_multiblockElimination
    (R Keep : Type*) [CommRing R] [Algebra ℚ R]
    (h : ℕ) (d : Fin h → ℕ)
    (I : Ideal (TerminalMultiblockSourceRing R h d Keep))
    (hgraded : IsTerminalMultigradedIdeal R (Fin h)
      (fun b ↦ d b + 1) Keep I)
    (hJ : IsTerminalGlobalStirlingInvariant R (Fin h)
      (fun b ↦ d b + 1) Keep I) :
    I.map (terminalMultiblockLocalizationHom R Keep h d) =
      (terminalMultiblockRetainedContraction R Keep h d
        (I.map (terminalMultiblockLocalizationHom R Keep h d))).map
          (terminalMultiblockRetainedCoefficientHom R Keep h d) := by
  apply terminalMultiblockElimination R Keep h d
  · exact terminalMultiblockTriangularFields_preserve_mappedIdeal_of_global
      R Keep h d I hgraded hJ
  · exact terminalMultiblockLocalizationHom_map_isMultigraded I hgraded

end AbelFormalization
