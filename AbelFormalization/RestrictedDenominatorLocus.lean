import AbelFormalization.DenominatorEquationExpressions

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Forget the final auxiliary coordinate while retaining it as a separate
real coordinate. -/
def restrictedDenominatorProjection {m p a : ℕ} :
    RestrictedSource m p (a + 1) → RestrictedSource m p a × ℝ :=
  fun x ↦
    (restrictedSourceDropAux 1 x,
      restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) x)

@[fun_prop]
theorem continuous_restrictedDenominatorProjection {m p a : ℕ} :
    Continuous (restrictedDenominatorProjection (m := m) (p := p) (a := a)) := by
  unfold restrictedDenominatorProjection
  have hdrop : Continuous (restrictedSourceDropAux (m := m) (p := p) (a := a) 1) := by
    unfold restrictedSourceDropAux
    fun_prop
  have hlast : Continuous
      (restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) :
        RestrictedSource m p (a + 1) → ℝ) := by
    unfold restrictedAuxCoordinate
    fun_prop
  exact hdrop.prodMk hlast

@[simp]
theorem restrictedDenominatorProjection_appendAuxOne {m p a : ℕ}
    (x : RestrictedSource m p a) (z : ℝ) :
    restrictedDenominatorProjection (restrictedSourceAppendAuxOne x z) = (x, z) := by
  apply Prod.ext
  · exact restrictedSourceDropAux_appendAuxOne x z
  · exact restrictedSourceAppendAuxOne_last x z

@[simp]
theorem restrictedSourceAppendAuxOne_projection {m p a : ℕ}
    (x : RestrictedSource m p (a + 1)) :
    restrictedSourceAppendAuxOne (restrictedSourceDropAux 1 x)
        (restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) x) = x := by
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · exact restrictedSourceAppendAuxOne_last _ _
    · have hidx : j.castSucc = Fin.castAdd 1 j := rfl
      rw [hidx, restrictedSourceAppendAuxOne_oldAux]
      rfl

theorem restrictedDenominatorProjection_injective {m p a : ℕ} :
    Function.Injective
      (restrictedDenominatorProjection (m := m) (p := p) (a := a)) := by
  intro x y hxy
  have := congrArg
    (fun p : RestrictedSource m p a × ℝ ↦
      restrictedSourceAppendAuxOne p.1 p.2) hxy
  simpa [restrictedDenominatorProjection] using this

theorem restrictedDenominatorProjection_surjective {m p a : ℕ} :
    Function.Surjective
      (restrictedDenominatorProjection (m := m) (p := p) (a := a)) := by
  rintro ⟨x, z⟩
  exact ⟨restrictedSourceAppendAuxOne x z,
    restrictedDenominatorProjection_appendAuxOne x z⟩

/-- The closed denominator locus realized directly in the restricted source
with one fresh auxiliary coordinate. -/
def restrictedClosedDenominatorLocus {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (q : RestrictedSource m p a → ℝ) :
    Set (RestrictedSource m p (a + 1)) :=
  restrictedDenominatorProjection ⁻¹' closedDenominatorLocus H u q

theorem isClosed_restrictedClosedDenominatorLocus
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (q : RestrictedSource m p a → ℝ)
    (hH : ∀ i, Continuous (H i))
    (hu : ∀ i, Continuous (u i)) (hq : Continuous q) :
    IsClosed (restrictedClosedDenominatorLocus H u q) := by
  exact (isClosed_closedDenominatorLocus H u q hH hu hq).preimage
    continuous_restrictedDenominatorProjection

@[simp]
theorem appendAuxOne_mem_restrictedClosedDenominatorLocus_iff
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (q : RestrictedSource m p a → ℝ)
    (x : RestrictedSource m p a) (z : ℝ) :
    restrictedSourceAppendAuxOne x z ∈
        restrictedClosedDenominatorLocus H u q ↔
      (∀ i, H i x = 0) ∧ (∀ i, 0 ≤ u i x) ∧ z * q x = 1 := by
  simp [restrictedClosedDenominatorLocus, closedDenominatorLocus]

theorem restrictedClosedDenominatorLocus_boundary_strictPos
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J : RestrictedSource m p a → ℝ)
    {x : RestrictedSource m p (a + 1)}
    (hx : x ∈ restrictedClosedDenominatorLocus H u
      (boundaryDenominator J u)) :
    (∀ i, 0 < u i (restrictedSourceDropAux 1 x)) ∧
      J (restrictedSourceDropAux 1 x) ≠ 0 := by
  exact closedDenominatorLocus_boundary_strictPos H u J hx

/-- Pull back the old equations and append the reciprocal equation as the
last component of a square-system-ready tuple. -/
def restrictedDenominatorSystem {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (q : RestrictedSource m p a → ℝ) :
    Fin (r + 1) → RestrictedSource m p (a + 1) → ℝ :=
  functionTupleSnoc
    (fun i ↦ functionPrecompAlgHom (restrictedSourceDropAux 1) (H i))
    (restrictedDenominatorEquation q)

@[simp]
theorem restrictedDenominatorSystem_castSucc_appendAuxOne
    {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (q : RestrictedSource m p a → ℝ)
    (i : Fin r) (x : RestrictedSource m p a) (z : ℝ) :
    restrictedDenominatorSystem H q i.castSucc
        (restrictedSourceAppendAuxOne x z) = H i x := by
  simp [restrictedDenominatorSystem]

@[simp]
theorem restrictedDenominatorSystem_last_appendAuxOne
    {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (q : RestrictedSource m p a → ℝ)
    (x : RestrictedSource m p a) (z : ℝ) :
    restrictedDenominatorSystem H q (Fin.last r)
        (restrictedSourceAppendAuxOne x z) = z * q x - 1 := by
  simp [restrictedDenominatorSystem]

theorem RestrictedExpressionTower.restrictedDenominatorSystem_mem_extendAux_level
    {m p a ell r : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) {j : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (q : RestrictedSource m p a → ℝ)
    (hH : ∀ i, H i ∈ T.level j) (hq : q ∈ T.level j) :
    ∀ i, restrictedDenominatorSystem H q i ∈ (T.extendAux 1).level j := by
  apply functionTupleSnoc_mem_subalgebra
  · intro i
    exact T.precomp_mem_extendAux_level 1 (hH i)
  · exact T.restrictedDenominatorEquation_mem_extendAux_level q hq

end AbelFormalization
