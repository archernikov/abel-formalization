import AbelFormalization.ClosedDenominatorGraph
import AbelFormalization.RestrictedAuxExtension
import AbelFormalization.RestrictedLastGeneratorLift

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {X : Type*}

/-- The product of a Jacobian factor and finitely many boundary factors
stays in any function subalgebra containing those factors. -/
theorem boundaryDenominator_mem_subalgebra
    {b : ℕ} (B : Subalgebra ℝ (X → ℝ))
    (J : X → ℝ) (u : Fin b → X → ℝ)
    (hJ : J ∈ B) (hu : ∀ i, u i ∈ B) :
    boundaryDenominator J u ∈ B := by
  apply B.mul_mem hJ
  have hprod : (∏ i, u i) ∈ B := B.prod_mem fun i _ ↦ hu i
  have heq : (fun x ↦ ∏ i, u i x) = ∏ i, u i := by
    funext x
    simp
  rw [heq]
  exact hprod

/-- The equation in the fresh auxiliary coordinate cutting out the
reciprocal graph of `q`. -/
def restrictedDenominatorEquation {m p a : ℕ}
    (q : RestrictedSource m p a → ℝ) :
    RestrictedSource m p (a + 1) → ℝ :=
  restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) *
    functionPrecompAlgHom (restrictedSourceDropAux 1) q - 1

@[simp]
theorem restrictedDenominatorEquation_appendAuxOne
    {m p a : ℕ} (q : RestrictedSource m p a → ℝ)
    (x : RestrictedSource m p a) (z : ℝ) :
    restrictedDenominatorEquation q (restrictedSourceAppendAuxOne x z) =
      z * q x - 1 := by
  unfold restrictedDenominatorEquation
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.one_apply]
  have hz : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a)
      (restrictedSourceAppendAuxOne x z) = z := by
    exact restrictedSourceAppendAuxOne_last x z
  have hq : functionPrecompAlgHom (restrictedSourceDropAux 1) q
      (restrictedSourceAppendAuxOne x z) = q x := by
    change q (restrictedSourceDropAux 1
      (restrictedSourceAppendAuxOne x z)) = q x
    rw [restrictedSourceDropAux_appendAuxOne]
  rw [hz, hq]

/-- Adjoining the reciprocal equation costs only one unrestricted auxiliary
coordinate and does not increase the exponential level. -/
theorem RestrictedExpressionTower.restrictedDenominatorEquation_mem_extendAux_level
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell))
    {j : ℕ} (q : RestrictedSource m p a → ℝ)
    (hq : q ∈ T.level j) :
    restrictedDenominatorEquation q ∈ (T.extendAux 1).level j := by
  have hzBase : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) ∈
      restrictedExpressionBase D (restrictedSpecialGeneratorsExtendAux 1 S) :=
    restrictedAuxCoordinate_mem_base D _ (Fin.last a)
  have hz : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) ∈
      (T.extendAux 1).level j :=
    (T.extendAux 1).base_mem_level hzBase j
  have hq' : functionPrecompAlgHom (restrictedSourceDropAux 1) q ∈
      (T.extendAux 1).level j := T.precomp_mem_extendAux_level 1 hq
  exact ((T.extendAux 1).level j).sub_mem
    (((T.extendAux 1).level j).mul_mem hz hq')
    ((T.extendAux 1).level j).one_mem

/-- The full denominator and its reciprocal equation both remain in the
same tower level after adjoining the reciprocal coordinate. -/
theorem RestrictedExpressionTower.boundaryDenominator_and_equation_mem
    {m p a ell b : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) {j : ℕ}
    (J : RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (hJ : J ∈ T.level j) (hu : ∀ i, u i ∈ T.level j) :
    boundaryDenominator J u ∈ T.level j ∧
      restrictedDenominatorEquation (boundaryDenominator J u) ∈
        (T.extendAux 1).level j := by
  have hq : boundaryDenominator J u ∈ T.level j :=
    boundaryDenominator_mem_subalgebra (T.level j) J u hJ hu
  exact ⟨hq, T.restrictedDenominatorEquation_mem_extendAux_level _ hq⟩

end AbelFormalization
