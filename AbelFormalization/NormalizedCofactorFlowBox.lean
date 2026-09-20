import AbelFormalization.NormalizedCofactorFlow
import AbelFormalization.RegularZeroBasics

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Nonvanishing of the cofactor determinant makes the square coordinate map
`(H, h)` locally injective. -/
theorem exists_nhds_constraintMap_functionTupleSnoc_injOn
    {r : ℕ} (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : E)
    (hH : ∀ i, ContDiffAt ℝ 2 (H i) x)
    (hh : ContDiffAt ℝ 2 h x)
    (hdet : criticalDeterminant H h basis x ≠ 0) :
    ∃ U ∈ 𝓝 x,
      Set.InjOn (constraintMap (functionTupleSnoc H h)) U := by
  let G : E → (Fin (r + 1) → ℝ) :=
    constraintMap (functionTupleSnoc H h)
  let D : E →L[ℝ] (Fin (r + 1) → ℝ) :=
    constraintFDeriv (functionTupleSnoc H h) x
  have htupleStrict : ∀ i, HasStrictFDerivAt
      (functionTupleSnoc H h i)
      (fderiv ℝ (functionTupleSnoc H h i) x) x := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [functionTupleSnoc_last] using
        hh.hasStrictFDerivAt (by norm_num)
    · simpa only [functionTupleSnoc_castSucc] using
        (hH j).hasStrictFDerivAt (by norm_num)
  have hGstrict : HasStrictFDerivAt G D x := by
    dsimp only [G, D]
    exact hasStrictFDerivAt_constraintMap
      (functionTupleSnoc H h) x htupleStrict
  have hDrange : D.range = ⊤ := by
    dsimp only [D]
    exact (constraintJacobianInBasis_det_ne_zero_iff_surjective
      (functionTupleSnoc H h) basis x).mp hdet
  have hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ) := by
    rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis basis]
    simp
  have hDsurj : Function.Surjective D :=
    LinearMap.range_eq_top.mp hDrange
  have hDinj : Function.Injective D :=
    continuousLinearMap_injective_of_surjective_of_finrank_eq
      D hdim hDsurj
  have hDker : D.ker = ⊥ := LinearMap.ker_eq_bot.mpr hDinj
  let e : E ≃L[ℝ] (Fin (r + 1) → ℝ) :=
    ContinuousLinearEquiv.ofBijective D hDker hDrange
  have heD : (e : E →L[ℝ] (Fin (r + 1) → ℝ)) = D :=
    ContinuousLinearEquiv.coe_ofBijective D hDker hDrange
  have hGstrictEquiv : HasStrictFDerivAt G
      (e : E →L[ℝ] (Fin (r + 1) → ℝ)) x := by
    rw [heD]
    exact hGstrict
  let invchart := hGstrictEquiv.toOpenPartialHomeomorph G
  have hxsource : x ∈ invchart.source :=
    hGstrictEquiv.mem_toOpenPartialHomeomorph_source
  exact ⟨invchart.source, invchart.open_source.mem_nhds hxsource,
    invchart.toPartialEquiv.injOn⟩

/-!
This is the local orbit-neighborhood statement needed after constructing the
normalized cofactor integral curve.  The only extra fiber hypothesis says
that `M` is contained in the constraint level through `x`; in the application
it follows immediately from the assumption that every `H i` vanishes on
`M`.

The proof applies the inverse function theorem to the square map

  `y ↦ (H 0 y, ..., H (r - 1) y, h y)`.

Its Jacobian determinant in `basis` is exactly `criticalDeterminant H h basis`.
Thus the square map is locally injective.  The normalized flow preserves all
the `H i` and changes `h` by elapsed time, so local injectivity identifies a
nearby point `y : M` with the flow point at time `h y - h x`.
-/

/-- A normalized cofactor trajectory through `x` parametrizes an ambient
neighborhood of `x` inside the constraint fiber `M`.

The returned neighborhood is ambient (`U ∈ 𝓝 (x : E)`), while the conclusion
only concerns points of `U ∩ M`.  The time interval is shrunk from the one
returned by `exists_local_normalizedCofactorIntegralCurve` so that the whole
trajectory segment lies in an inverse-function chart for `(H, h)`. -/
theorem exists_local_normalizedCofactorIntegralCurve_flowBox
    {r : ℕ} {M Ω : Set E} (H : Fin r → E → ℝ) (h : E → ℝ)
    (basis : Module.Basis (Fin (r + 1)) ℝ E) (x : M)
    (hΩ : Ω ∈ 𝓝 (x : E))
    (hH : ∀ y ∈ Ω, ∀ i, ContDiffAt ℝ 2 (H i) y)
    (hh : ∀ y ∈ Ω, ContDiffAt ℝ 2 h y)
    (hdet : ∀ y ∈ M, criticalDeterminant H h basis y ≠ 0)
    (hMlevel : ∀ y ∈ M, ∀ i, H i y = H i x)
    (hlocalConstraint : ∃ V ∈ 𝓝 (x : E),
      V ∩ {y | ∀ i, H i y = H i x} ⊆ M) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → E,
      γ 0 = x ∧
        (∀ t ∈ Ioo (-ε) ε,
          γ t ∈ M ∧
            HasDerivAt γ
              (normalizedCofactorVectorField H h basis (γ t)) t ∧
            h (γ t) = h x + t) ∧
        ∃ U ∈ 𝓝 (x : E), ∀ y ∈ U, y ∈ M →
          h y - h x ∈ Ioo (-ε) ε ∧ γ (h y - h x) = y := by
  have hxΩ : (x : E) ∈ Ω := mem_of_mem_nhds hΩ

  -- The square map `(H, h)` and its product derivative at `x`.
  let G : E → (Fin (r + 1) → ℝ) :=
    constraintMap (functionTupleSnoc H h)
  let D : E →L[ℝ] (Fin (r + 1) → ℝ) :=
    constraintFDeriv (functionTupleSnoc H h) (x : E)
  have htupleStrict : ∀ i, HasStrictFDerivAt
      (functionTupleSnoc H h i)
      (fderiv ℝ (functionTupleSnoc H h i) (x : E)) (x : E) := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [functionTupleSnoc_last] using
        (hh (x : E) hxΩ).hasStrictFDerivAt (by norm_num)
    · simpa only [functionTupleSnoc_castSucc] using
        (hH (x : E) hxΩ j).hasStrictFDerivAt (by norm_num)
  have hGstrict : HasStrictFDerivAt G D (x : E) := by
    dsimp only [G, D]
    exact hasStrictFDerivAt_constraintMap
      (functionTupleSnoc H h) (x : E) htupleStrict

  -- Nonvanishing of the critical determinant makes the derivative of `G`
  -- bijective.  The source dimension calculation uses the supplied basis.
  have hdetx :
      (constraintJacobianInBasis (functionTupleSnoc H h) basis (x : E)).det ≠ 0 := by
    exact hdet (x : E) x.property
  have hDrange : D.range = ⊤ := by
    dsimp only [D]
    exact (constraintJacobianInBasis_det_ne_zero_iff_surjective
      (functionTupleSnoc H h) basis (x : E)).mp hdetx
  have hdim : Module.finrank ℝ E =
      Module.finrank ℝ (Fin (r + 1) → ℝ) := by
    rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis basis]
    simp
  have hDsurj : Function.Surjective D :=
    LinearMap.range_eq_top.mp hDrange
  have hDinj : Function.Injective D :=
    continuousLinearMap_injective_of_surjective_of_finrank_eq
      D hdim hDsurj
  have hDker : D.ker = ⊥ := LinearMap.ker_eq_bot.mpr hDinj
  let e : E ≃L[ℝ] (Fin (r + 1) → ℝ) :=
    ContinuousLinearEquiv.ofBijective D hDker hDrange
  have heD : (e : E →L[ℝ] (Fin (r + 1) → ℝ)) = D :=
    ContinuousLinearEquiv.coe_ofBijective D hDker hDrange
  have hGstrictEquiv : HasStrictFDerivAt G
      (e : E →L[ℝ] (Fin (r + 1) → ℝ)) (x : E) := by
    rw [heD]
    exact hGstrict
  let invchart := hGstrictEquiv.toOpenPartialHomeomorph G
  have hxsource : (x : E) ∈ invchart.source :=
    hGstrictEquiv.mem_toOpenPartialHomeomorph_source
  have hsourceNhds : invchart.source ∈ 𝓝 (x : E) :=
    invchart.open_source.mem_nhds hxsource

  obtain ⟨ε₀, hε₀, γ, hγzero, hγlocal₀⟩ :=
    exists_local_normalizedCofactorIntegralCurve
      H h basis x hΩ hH hh hdet hlocalConstraint
  have hzeroOld : (0 : ℝ) ∈ Ioo (-ε₀) ε₀ := by
    constructor <;> linarith
  have hγcont : ContinuousAt γ 0 :=
    (hγlocal₀ 0 hzeroOld).2.1.continuousAt
  have hsourceTime : γ ⁻¹' invchart.source ∈ 𝓝 (0 : ℝ) := by
    apply hγcont.preimage_mem_nhds
    rw [hγzero]
    exact hsourceNhds
  have htimeWindow : Ioo (-ε₀) ε₀ ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have htimeEventually : ∀ᶠ t in 𝓝 (0 : ℝ),
      t ∈ Ioo (-ε₀) ε₀ ∧ γ t ∈ invchart.source := by
    filter_upwards [htimeWindow, hsourceTime] with t ht htsource
    exact ⟨ht, htsource⟩
  rw [Metric.eventually_nhds_iff_ball] at htimeEventually
  obtain ⟨ε, hε, htimeStay⟩ := htimeEventually
  have htimeLocal : ∀ t ∈ Ioo (-ε) ε,
      t ∈ Ioo (-ε₀) ε₀ ∧ γ t ∈ invchart.source := by
    intro t ht
    apply htimeStay t
    simpa [Real.dist_eq, abs_lt] using ht
  have hγlocal : ∀ t ∈ Ioo (-ε) ε,
      γ t ∈ M ∧
        HasDerivAt γ
          (normalizedCofactorVectorField H h basis (γ t)) t ∧
        h (γ t) = h x + t := by
    intro t ht
    exact hγlocal₀ t (htimeLocal t ht).1

  -- Restrict nearby points by their `h`-coordinate.  For each such point the
  -- prescribed time lies in the shrunken flow interval.
  let U : Set E := invchart.source ∩
    h ⁻¹' Ioo (h x - ε) (h x + ε)
  have hhWindow : h ⁻¹' Ioo (h x - ε) (h x + ε) ∈ 𝓝 (x : E) := by
    apply (hh (x : E) hxΩ).continuousAt.preimage_mem_nhds
    exact Ioo_mem_nhds (by linarith) (by linarith)
  have hU : U ∈ 𝓝 (x : E) := by
    exact inter_mem hsourceNhds hhWindow
  refine ⟨ε, hε, γ, hγzero, hγlocal, U, hU, ?_⟩
  intro y hyU hyM
  change y ∈ invchart.source ∩
    h ⁻¹' Ioo (h x - ε) (h x + ε) at hyU
  let t : ℝ := h y - h x
  have ht : t ∈ Ioo (-ε) ε := by
    dsimp only [t]
    constructor <;> linarith [hyU.2.1, hyU.2.2]
  have hγt := hγlocal t ht
  have hGeq : G (γ t) = G y := by
    funext i
    change functionTupleSnoc H h i (γ t) =
      functionTupleSnoc H h i y
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp only [functionTupleSnoc_last]
      calc
        h (γ t) = h x + t := hγt.2.2
        _ = h y := by dsimp only [t]; ring
    · simp only [functionTupleSnoc_castSucc]
      exact (hMlevel (γ t) hγt.1 j).trans
        (hMlevel y hyM j).symm
  have hγty : γ t = y :=
    invchart.toPartialEquiv.injOn
      (htimeLocal t ht).2 hyU.1 hGeq
  exact ⟨ht, by simpa only [t] using hγty⟩

end AbelFormalization
