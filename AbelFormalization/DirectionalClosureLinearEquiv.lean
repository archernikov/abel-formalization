import AbelFormalization.RestrictedSourceLinearEquiv
import AbelFormalization.DifferentiallyClosedTower

/-!
# Transporting directional closure through a linear equivalence

Directional derivative representatives remain in the mapped function
algebra after a continuous linear change of source coordinates.  This is
the coordinate-change step needed to split the last unrestricted variable
from a restricted source.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Map a directionally closed function algebra through a continuous linear
equivalence.  The domain is transported by the inverse equivalence. -/
theorem DirectionallyClosedOn.map_continuousLinearEquiv
    (B : Subalgebra ℝ (X → ℝ)) (Omega : Set X)
    (e : X ≃L[ℝ] Y) (v : Y)
    (hclosed : DirectionallyClosedOn B Omega (e.symm v)) :
    DirectionallyClosedOn
      (B.map (functionPrecompAlgHom e.symm))
      (e.symm ⁻¹' Omega) v := by
  intro f hf
  rw [Subalgebra.mem_map] at hf
  obtain ⟨f0, hf0, rfl⟩ := hf
  obtain ⟨df0, hdf0, hderiv⟩ := hclosed f0 hf0
  refine ⟨functionPrecompAlgHom e.symm df0, ?_, ?_⟩
  · rw [Subalgebra.mem_map]
    exact ⟨df0, hdf0, rfl⟩
  · intro y hy
    have hxy := hderiv (e.symm y) hy
    have hcomp := hxy.1.hasFDerivAt.comp y e.symm.hasFDerivAt
    constructor
    · exact hcomp.differentiableAt
    · have happ := congrArg (fun L : Y →L[ℝ] ℝ ↦ L v) hcomp.fderiv
      change fderiv ℝ (f0 ∘ e.symm) y v = df0 (e.symm y)
      simpa [hxy.2] using happ

end AbelFormalization
