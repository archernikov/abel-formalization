import AbelFormalization.NormalizedCofactorFlow
import AbelFormalization.RolleComponentUniqueness

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A curve that stays in `M` and is regular on a neighborhood of a closed
interval gives a `RegularArcIn` between its endpoint values.  The larger set
`S` is useful when the endpoint derivatives come from an ODE theorem stated on
an open time interval. -/
theorem regularArcIn_of_hasDerivAt_on_superset
    {M : Set E} {S : Set ℝ} {a b : ℝ} {γ v : ℝ → E}
    (hab : a < b)
    (hIcc : Icc a b ⊆ S)
    (hγM : ∀ t ∈ S, γ t ∈ M)
    (hγderiv : ∀ t ∈ S, HasDerivAt γ (v t) t)
    (hv : ∀ t ∈ Ioo a b, v t ≠ 0) :
    RegularArcIn M (γ a) (γ b) := by
  refine ⟨a, b, γ, v, hab, rfl, rfl, ?_, ?_, ?_⟩
  · intro t ht
    exact (hγderiv t (hIcc ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact hγM t (hIcc ht)
  · intro t ht
    exact ⟨hγderiv t (hIcc (Ioo_subset_Icc_self ht)), hv t ht⟩

/-- A positive-time segment of a local normalized cofactor integral curve is
a regular arc from its initial point to its value at that time. -/
theorem regularArcIn_zero_to_of_local_normalizedCofactorIntegralCurve
    {r : ℕ} {M : Set E} (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : M)
    {ε : ℝ} (hε : 0 < ε) {γ : ℝ → E}
    (hγzero : γ 0 = x)
    (hdet : ∀ y ∈ M, criticalDeterminant H h basis y ≠ 0)
    (hγlocal : ∀ s ∈ Ioo (-ε) ε,
      γ s ∈ M ∧
        HasDerivAt γ
          (normalizedCofactorVectorField H h basis (γ s)) s ∧
        h (γ s) = h x + s)
    {t : ℝ} (ht : t ∈ Ioo 0 ε) :
    RegularArcIn M x (γ t) := by
  have hIcc : Icc (0 : ℝ) t ⊆ Ioo (-ε) ε := by
    intro s hs
    exact ⟨lt_of_lt_of_le (neg_lt_zero.mpr hε) hs.1,
      lt_of_le_of_lt hs.2 ht.2⟩
  have harc : RegularArcIn M (γ 0) (γ t) := by
    refine regularArcIn_of_hasDerivAt_on_superset
      (M := M) (S := Ioo (-ε) ε) (a := 0) (b := t)
      (γ := γ)
      (v := fun s ↦ normalizedCofactorVectorField H h basis (γ s))
      ht.1 hIcc ?_ ?_ ?_
    · intro s hs
      exact (hγlocal s hs).1
    · intro s hs
      exact (hγlocal s hs).2.1
    · intro s hs
      have hs' : s ∈ Ioo (-ε) ε :=
        hIcc (Ioo_subset_Icc_self hs)
      exact normalizedCofactorVectorField_ne_zero H h basis (γ s)
        (hdet (γ s) (hγlocal s hs').1)
  simpa only [hγzero] using harc

/-- A negative-time segment of a local normalized cofactor integral curve is
a regular arc from that value back to its initial point. -/
theorem regularArcIn_to_zero_of_local_normalizedCofactorIntegralCurve
    {r : ℕ} {M : Set E} (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : M)
    {ε : ℝ} (hε : 0 < ε) {γ : ℝ → E}
    (hγzero : γ 0 = x)
    (hdet : ∀ y ∈ M, criticalDeterminant H h basis y ≠ 0)
    (hγlocal : ∀ s ∈ Ioo (-ε) ε,
      γ s ∈ M ∧
        HasDerivAt γ
          (normalizedCofactorVectorField H h basis (γ s)) s ∧
        h (γ s) = h x + s)
    {t : ℝ} (ht : t ∈ Ioo (-ε) 0) :
    RegularArcIn M (γ t) x := by
  have hIcc : Icc t (0 : ℝ) ⊆ Ioo (-ε) ε := by
    intro s hs
    exact ⟨lt_of_lt_of_le ht.1 hs.1,
      lt_of_le_of_lt hs.2 hε⟩
  have harc : RegularArcIn M (γ t) (γ 0) := by
    refine regularArcIn_of_hasDerivAt_on_superset
      (M := M) (S := Ioo (-ε) ε) (a := t) (b := 0)
      (γ := γ)
      (v := fun s ↦ normalizedCofactorVectorField H h basis (γ s))
      ht.2 hIcc ?_ ?_ ?_
    · intro s hs
      exact (hγlocal s hs).1
    · intro s hs
      exact (hγlocal s hs).2.1
    · intro s hs
      have hs' : s ∈ Ioo (-ε) ε :=
        hIcc (Ioo_subset_Icc_self hs)
      exact normalizedCofactorVectorField_ne_zero H h basis (γ s)
        (hdet (γ s) (hγlocal s hs').1)
  simpa only [hγzero] using harc

/-- Local normalized cofactor ODE existence, strengthened with the regular
arcs furnished by all positive- and negative-time subsegments. -/
theorem exists_local_normalizedCofactorIntegralCurve_with_regularArcs
    {r : ℕ} {M Ω : Set E} (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : M)
    (hΩ : Ω ∈ 𝓝 (x : E))
    (hH : ∀ y ∈ Ω, ∀ i, ContDiffAt ℝ 2 (H i) y)
    (hh : ∀ y ∈ Ω, ContDiffAt ℝ 2 h y)
    (hdet : ∀ y ∈ M, criticalDeterminant H h basis y ≠ 0)
    (hlocalConstraint : ∃ U ∈ 𝓝 (x : E),
      U ∩ {y | ∀ i, H i y = H i x} ⊆ M) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E,
      γ 0 = x ∧
        (∀ t ∈ Ioo (-ε) ε,
          γ t ∈ M ∧
            HasDerivAt γ
              (normalizedCofactorVectorField H h basis (γ t)) t ∧
            h (γ t) = h x + t) ∧
        (∀ t ∈ Ioo 0 ε, RegularArcIn M x (γ t)) ∧
        ∀ t ∈ Ioo (-ε) 0, RegularArcIn M (γ t) x := by
  obtain ⟨ε, hε, γ, hγzero, hγlocal⟩ :=
    exists_local_normalizedCofactorIntegralCurve
      H h basis x hΩ hH hh hdet hlocalConstraint
  refine ⟨ε, hε, γ, hγzero, hγlocal, ?_, ?_⟩
  · intro t ht
    exact regularArcIn_zero_to_of_local_normalizedCofactorIntegralCurve
      H h basis x hε hγzero hdet hγlocal ht
  · intro t ht
    exact regularArcIn_to_zero_of_local_normalizedCofactorIntegralCurve
      H h basis x hε hγzero hdet hγlocal ht

end AbelFormalization
