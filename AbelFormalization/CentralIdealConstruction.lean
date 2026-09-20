import AbelFormalization.CentralLaurentContraction
import AbelFormalization.CentralPolynomialEquiv

set_option autoImplicit false

/-!
# The composed central ideal

This module composes the actual shifted Laurent contraction with the final
signed-Stirling/time-translation polynomial equivalence.  Thus the output is
the literal ideal after all algebraic changes of coordinates in the central
construction, and its height is still at least the height of the input ideal.
-/

noncomputable section

namespace AbelFormalization

universe u v w

variable {R : Type u} [CommRing R]
variable {Block : Type v} {d : Block → ℕ} {Time : Type w} {h : ℕ}

/-- The full central ideal: first translate the independent `q` variables,
take the original least lexicographic initial ideal, invert and rescale the
`q` variables, contract to weight zero, and finally apply `Φ`. -/
def centralIdealConstruction
    (ω : CentralPolynomialIndex Block d Time → Fin h → ℤ)
    (I : Ideal
      (MvPolynomial (Fin h ⊕ CentralPolynomialIndex Block d Time) R)) :
    Ideal (CentralPolynomial R Block d Time) :=
  (centralShiftedLaurentContraction ω I).map
    (centralPolynomialPhi R Block d Time).toRingHom

/-- The full construction is exactly the image under `Φ` of the literal
shifted Laurent contraction. -/
theorem centralIdealConstruction_eq
    (ω : CentralPolynomialIndex Block d Time → Fin h → ℤ)
    (I : Ideal
      (MvPolynomial (Fin h ⊕ CentralPolynomialIndex Block d Time) R)) :
    centralIdealConstruction ω I =
      (centralShiftedLaurentContraction ω I).map
        (centralPolynomialPhi R Block d Time).toRingHom := rfl

/-- None of the successive central changes of coordinates lowers height. -/
theorem centralIdealConstruction_height_le
    [IsNoetherianRing R] [Finite Block] [Finite Time]
    (ω : CentralPolynomialIndex Block d Time → Fin h → ℤ)
    (I : Ideal
      (MvPolynomial (Fin h ⊕ CentralPolynomialIndex Block d Time) R)) :
    I.height ≤ (centralIdealConstruction ω I).height := by
  let J : Ideal (CentralPolynomial R Block d Time) :=
    centralShiftedLaurentContraction ω I
  calc
    I.height ≤ J.height := centralShiftedLaurentContraction_height_le ω I
    _ = (J.map (centralPolynomialPhi R Block d Time).toRingHom).height :=
      (centralPolynomialPhi_height_map R Block d Time J).symm
    _ = (centralIdealConstruction ω I).height := rfl

/-- Applying the inverse polynomial equivalence recovers the contracted ideal
exactly. -/
theorem centralIdealConstruction_comap_phi
    (ω : CentralPolynomialIndex Block d Time → Fin h → ℤ)
    (I : Ideal
      (MvPolynomial (Fin h ⊕ CentralPolynomialIndex Block d Time) R)) :
    (centralIdealConstruction ω I).comap
        (centralPolynomialPhi R Block d Time).toRingHom =
      centralShiftedLaurentContraction ω I := by
  rw [centralIdealConstruction]
  exact Ideal.comap_map_of_bijective
    (centralPolynomialPhi R Block d Time).toRingHom
    (centralPolynomialPhi R Block d Time).bijective

end AbelFormalization
