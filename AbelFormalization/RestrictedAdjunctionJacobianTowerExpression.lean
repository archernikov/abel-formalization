import AbelFormalization.ExponentialAdjunctionJacobianExpression
import AbelFormalization.DirectionalClosureLinearEquiv
import AbelFormalization.RestrictedAbelAuxExtension
import AbelFormalization.RestrictedExponentialGraph

/-!
# The adjunction Jacobian in the lower restricted tower level

After the last exponential generator is replaced by a free auxiliary
coordinate, the manuscript's global determinant `J(x,Y)` is represented at
the preceding exponential level.  The proof transports the enlarged Abel
tower to product coordinates, applies the general directional-Jacobian
construction, and transports the resulting representative back.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- Dropping fresh auxiliary coordinates preserves the common positivity
and closed-box domain of the shifted Abel jets. -/
theorem restrictedSourceDropAux_mem_restrictedAbelJetDomain
    {m p a k : ℕ} {D : RestrictedBox p}
    {representative : ι → Fin m}
    {offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D}
    {x : RestrictedSource m p (a + k)}
    (hx : x ∈ restrictedAbelJetDomain D representative offset) :
    restrictedSourceDropAux k x ∈
      restrictedAbelJetDomain (a := a) D representative offset := by
  constructor
  · exact hx.1
  · intro t
    exact hx.2 t

/-- The manuscript's global adjunction determinant has a representative at
the lower tower level on the enlarged restricted source. -/
theorem IsAbel.exists_restrictedExponentialAdjunctionJacobianExpression
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell n : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (i : Fin ell)
    (H : Fin n → RestrictedSource m p (a + 1) → ℝ)
    (basis : Module.Basis (Fin n) ℝ (RestrictedSource m p a))
    (hH : ∀ k, H k ∈
      (T.extendAuxAbel A representative offset 1).level i.val) :
    ∃ J : RestrictedSource m p (a + 1) → ℝ,
      J ∈ (T.extendAuxAbel A representative offset 1).level i.val ∧
      ∀ y ∈ restrictedAbelJetDomain (a := a + 1) D representative offset,
        J y = restrictedExponentialAdjunctionJacobian H (T.exponent i) basis y := by
  let TE := T.extendAuxAbel A representative offset 1
  let e : RestrictedSource m p (a + 1) ≃L[ℝ]
      RestrictedSource m p a × ℝ := restrictedSourceAuxOneContinuousLinearEquiv
  let B := TE.level i.val
  let Omega := restrictedAbelJetDomain (a := a + 1) D representative offset
  let Bprod : Subalgebra ℝ ((RestrictedSource m p a × ℝ) → ℝ) :=
    B.map (functionPrecompAlgHom e.symm)
  have hFprod : ∀ k,
      (fun q ↦ restrictedSystemProductForm H q k) ∈ Bprod := by
    intro k
    rw [Subalgebra.mem_map]
    refine ⟨H k, hH k, ?_⟩
    rfl
  have hgsource : functionPrecompAlgHom (restrictedSourceDropAux 1)
      (T.exponent i) ∈ B := by
    change functionPrecompAlgHom (restrictedSourceDropAux 1)
        (T.exponent i) ∈ TE.level i.val
    rw [T.extendAuxAbel_level_eq_extendAux A representative offset]
    exact T.precomp_mem_extendAux_level 1 (T.exponent_mem i)
  have hgprod : (fun q : RestrictedSource m p a × ℝ ↦
      T.exponent i q.1) ∈ Bprod := by
    rw [Subalgebra.mem_map]
    refine ⟨functionPrecompAlgHom (restrictedSourceDropAux 1)
      (T.exponent i), hgsource, ?_⟩
    funext q
    simp [e]
  have hYsource : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) ∈ B := by
    change restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) ∈
      TE.level i.val
    exact TE.base_mem_level
      (restrictedAuxCoordinate_mem_base D _ (Fin.last a)) i.val
  have hYprod : (fun q : RestrictedSource m p a × ℝ ↦ q.2) ∈ Bprod := by
    rw [Subalgebra.mem_map]
    refine ⟨restrictedAuxCoordinate (m := m) (p := p) (Fin.last a),
      hYsource, ?_⟩
    funext q
    simpa [restrictedAuxCoordinate, e] using
      (restrictedSourceAppendAuxOne_last q.1 q.2)
  have hclosed : ∀ j, DirectionallyClosedOn Bprod
      (e.symm ⁻¹' Omega) (graphProductBasis basis j) := by
    intro j
    apply DirectionallyClosedOn.map_continuousLinearEquiv B Omega e
    exact hA.extendAuxAbel_directionallyClosedOn_level
      representative offset T 1 (e.symm (graphProductBasis basis j)) i.val
  have hgdiff : ∀ q ∈ e.symm ⁻¹' Omega,
      DifferentiableAt ℝ (T.exponent i) q.1 := by
    intro q hq
    have hqbase : q.1 ∈
        restrictedAbelJetDomain (a := a) D representative offset := by
      have hdrop := restrictedSourceDropAux_mem_restrictedAbelJetDomain
        (a := a) (k := 1) hq
      simpa [e] using hdrop
    obtain ⟨dg, hdgmem, hdg⟩ :=
      hA.restrictedAbelTower_directionallyClosedOn_level
        representative offset T (0 : RestrictedSource m p a) i.val
        (T.exponent i) (T.exponent_mem i)
    exact (hdg q.1 hqbase).1
  obtain ⟨Jprod, hJprod, hJeq⟩ :=
    exists_exponentialAdjunctionJacobianExpression Bprod
      (e.symm ⁻¹' Omega) (restrictedSystemProductForm H) (T.exponent i)
      basis hFprod hgprod hYprod hclosed hgdiff
  rw [Subalgebra.mem_map] at hJprod
  obtain ⟨J, hJ, hJmap⟩ := hJprod
  refine ⟨J, hJ, ?_⟩
  intro y hy
  have hpoint : e.symm (e y) ∈ Omega := by
    simpa
  have hvalue := congrFun hJmap (e y)
  calc
    J y = Jprod (e y) := by simpa using hvalue
    _ = exponentialAdjunctionJacobian (restrictedSystemProductForm H)
        (T.exponent i) basis (e y) := hJeq (e y) hpoint
    _ = restrictedExponentialAdjunctionJacobian H (T.exponent i) basis y := by
      rfl

end AbelFormalization
