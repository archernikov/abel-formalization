import AbelFormalization.CentralJet
import AbelFormalization.HermiteInterpolation
import AbelFormalization.NormalizedPolynomial

/-! # The zero-scale value of the central Hermite coefficients

The interpolation center, scale, and nodes are separate parameters.
At scale zero, the combined multiplicity at zero is the total degree,
so every normalized coefficient is the corresponding central jet.
-/

noncomputable section

namespace AbelFormalization

open Set Metric Filter
open scoped Topology

variable {ι : Type*} [Fintype ι]

theorem nodeMultiplicity_zero_nodes (m : ι → ℕ) :
    nodeMultiplicity (fun _ : ι => (0 : ℂ)) m 0 = totalMultiplicity m := by
  simp [nodeMultiplicity, totalMultiplicity]

theorem hermiteContour_zero_nodes_normalizedCoeff {f : ℂ → ℂ} (m : ι → ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (hf : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) ρ))
    {r : ℕ} (hr : r < totalMultiplicity m) :
    normalizedCoeff (hermiteContourPolynomial f
      (nodePolynomial (fun _ : ι => (0 : ℂ)) m) ρ) r = iteratedDeriv r f 0 := by
  rw [normalizedCoeff_eq_iteratedDeriv]
  symm
  apply hermiteContour_interpolates_combined _ m hρ hf
    (fun _ => mem_ball_self hρ) (lt_of_le_of_lt (Nat.zero_le r) hr)
  simpa only [nodeMultiplicity_zero_nodes] using hr

/-- Factorial-normalized coefficients of the central interpolation problem,
with independent complex center, scale, and node parameters. -/
def centralCoefficient (F : ℂ → ℂ) (m : ι → ℕ) (ρ : ℝ)
    (u q : ℂ) (δ : ι → ℂ) (r : ℕ) : ℂ :=
  normalizedCoeff (hermiteContourPolynomial (centralComplexFunction F u)
    (nodePolynomial (fun i => q * δ i) m) ρ) r

theorem centralCoefficient_zero_scale {F : ℂ → ℂ} (m : ι → ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) {u : ℂ}
    (hF : AnalyticOnNhd ℂ (centralComplexFunction F u) (closedBall (0 : ℂ) ρ))
    (δ : ι → ℂ) {r : ℕ} (hr : r < totalMultiplicity m) :
    centralCoefficient F m ρ u 0 δ r = iteratedDeriv r (centralComplexFunction F u) 0 := by
  simpa only [centralCoefficient, zero_mul] using
    hermiteContour_zero_nodes_normalizedCoeff m hρ hF hr

namespace IsAbel

variable {A : ℝ → ℝ} (hA : IsAbel A)
include hA

/-- The zero-scale coefficient is exactly the signed-Stirling combination
of real Abel derivatives at the center. -/
theorem centralCoefficient_zero_scale_stirling {F : ℂ → ℂ} (m : ι → ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) {u : ℝ} (hu : 0 < u)
    (hF : AnalyticAt ℂ F (u : ℂ))
    (he : (fun y : ℝ => F (y : ℂ)) =ᶠ[𝓝 u] fun y => (A y : ℂ))
    (hH : AnalyticOnNhd ℂ (centralComplexFunction F (u : ℂ)) (closedBall (0 : ℂ) ρ))
    (δ : ι → ℂ) {r : ℕ} (hr : 1 ≤ r) (hrd : r < totalMultiplicity m) :
    centralCoefficient F m ρ (u : ℂ) 0 δ r =
      ∑ j ∈ Finset.range (r + 1), (signedStirling r j : ℂ) *
        ((iteratedDeriv j A u : ℝ) : ℂ) := by
  rw [centralCoefficient_zero_scale m hρ hH δ hrd]
  exact hA.centralComplexFunction_iteratedDeriv hu hF he r hr

end IsAbel
end AbelFormalization
