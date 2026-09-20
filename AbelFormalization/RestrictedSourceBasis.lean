import AbelFormalization.RestrictedOffsetThreshold
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Coordinate basis of a restricted source

The basis follows the manuscript's variable order: unbounded `s`
coordinates, bounded `w` coordinates, then unrestricted auxiliaries.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Coordinate basis of a restricted source, ordered as `s`, then `w`, then
the unrestricted auxiliary coordinates. -/
def restrictedSourceBasis (m p a : ℕ) :
    Module.Basis (Fin ((m + p) + a)) ℝ (RestrictedSource m p a) :=
  (((Pi.basisFun ℝ (Fin m)).prod (Pi.basisFun ℝ (Fin p))).prod
      (Pi.basisFun ℝ (Fin a))).reindex
    ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin a))).trans
      finSumFinEquiv)

end AbelFormalization
