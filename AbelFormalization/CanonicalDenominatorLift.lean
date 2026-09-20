import AbelFormalization.RestrictedDenominatorLocus

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

@[fun_prop]
theorem continuous_restrictedSourceAppendAuxOne {m p a : ℕ} :
    Continuous (fun x : RestrictedSource m p a × ℝ =>
      restrictedSourceAppendAuxOne x.1 x.2) := by
  unfold restrictedSourceAppendAuxOne
  fun_prop

/-- Splitting off the final unrestricted auxiliary coordinate is a
homeomorphism. -/
def restrictedSourceAuxOneHomeomorph {m p a : ℕ} :
    RestrictedSource m p (a + 1) ≃ₜ RestrictedSource m p a × ℝ where
  toFun := restrictedDenominatorProjection
  invFun := fun x ↦ restrictedSourceAppendAuxOne x.1 x.2
  left_inv := restrictedSourceAppendAuxOne_projection
  right_inv := fun x ↦ restrictedDenominatorProjection_appendAuxOne x.1 x.2
  continuous_toFun := continuous_restrictedDenominatorProjection
  continuous_invFun := continuous_restrictedSourceAppendAuxOne

/-- The original locus before adjoining the reciprocal denominator. -/
def restrictedOpenDenominatorLocus {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J : RestrictedSource m p a → ℝ) :
    Set (RestrictedSource m p a) :=
  {x | (∀ i, H i x = 0) ∧ (∀ i, 0 < u i x) ∧ J x ≠ 0}

theorem boundaryDenominator_ne_zero_of_mem_restrictedOpenDenominatorLocus
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J : RestrictedSource m p a → ℝ)
    {x : RestrictedSource m p a}
    (hx : x ∈ restrictedOpenDenominatorLocus H u J) :
    boundaryDenominator J u x ≠ 0 := by
  apply mul_ne_zero hx.2.2
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ ne_of_gt (hx.2.1 i)

theorem continuous_boundaryDenominator {m p a b : ℕ}
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J : RestrictedSource m p a → ℝ)
    (hu : ∀ i, Continuous (u i)) (hJ : Continuous J) :
    Continuous (boundaryDenominator J u) := by
  apply hJ.mul
  simpa using (continuous_finsetProd Finset.univ fun i _ ↦ hu i)

/-- The canonical lift into the closed reciprocal locus. -/
def restrictedCanonicalDenominatorLift
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J : RestrictedSource m p a → ℝ) :
    restrictedOpenDenominatorLocus H u J →
      restrictedClosedDenominatorLocus H u (boundaryDenominator J u) :=
  fun x ↦ ⟨restrictedSourceAppendAuxOne x
      ((boundaryDenominator J u x)⁻¹), by
    rw [appendAuxOne_mem_restrictedClosedDenominatorLocus_iff]
    exact ⟨x.property.1, fun i ↦ (x.property.2.1 i).le,
      inv_mul_cancel₀
        (boundaryDenominator_ne_zero_of_mem_restrictedOpenDenominatorLocus
          H u J x.property)⟩⟩

/-- Forget the reciprocal coordinate of a point in the closed locus. -/
def restrictedCanonicalDenominatorDrop
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J : RestrictedSource m p a → ℝ) :
    restrictedClosedDenominatorLocus H u (boundaryDenominator J u) →
      restrictedOpenDenominatorLocus H u J :=
  fun y ↦ ⟨restrictedSourceDropAux 1 y, by
    have hstrict := restrictedClosedDenominatorLocus_boundary_strictPos
      H u J y.property
    exact ⟨y.property.1, hstrict.1, hstrict.2⟩⟩

theorem restrictedCanonicalDenominatorDrop_lift
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J : RestrictedSource m p a → ℝ)
    (x : restrictedOpenDenominatorLocus H u J) :
    restrictedCanonicalDenominatorDrop H u J
        (restrictedCanonicalDenominatorLift H u J x) = x := by
  apply Subtype.ext
  exact restrictedSourceDropAux_appendAuxOne (x : RestrictedSource m p a)
    ((boundaryDenominator J u x)⁻¹)

theorem restrictedCanonicalDenominatorLift_drop
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J : RestrictedSource m p a → ℝ)
    (y : restrictedClosedDenominatorLocus H u (boundaryDenominator J u)) :
    restrictedCanonicalDenominatorLift H u J
        (restrictedCanonicalDenominatorDrop H u J y) = y := by
  apply Subtype.ext
  change restrictedSourceAppendAuxOne
      (restrictedSourceDropAux 1 (y : RestrictedSource m p (a + 1)))
      ((boundaryDenominator J u
        (restrictedSourceDropAux 1 (y : RestrictedSource m p (a + 1))))⁻¹) =
        (y : RestrictedSource m p (a + 1))
  have hygraph : restrictedDenominatorProjection
      (y : RestrictedSource m p (a + 1)) ∈
      denominatorGraph (boundaryDenominator J u) :=
    y.property.2.2
  have hlast : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a)
      (y : RestrictedSource m p (a + 1)) =
      (boundaryDenominator J u
        (restrictedSourceDropAux 1 (y : RestrictedSource m p (a + 1))))⁻¹ :=
    denominatorGraph_snd_eq_inv (boundaryDenominator J u) hygraph
  rw [← hlast]
  exact restrictedSourceAppendAuxOne_projection
    (y : RestrictedSource m p (a + 1))

theorem continuous_restrictedCanonicalDenominatorLift
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J : RestrictedSource m p a → ℝ)
    (hu : ∀ i, Continuous (u i)) (hJ : Continuous J) :
    Continuous (restrictedCanonicalDenominatorLift H u J) := by
  apply Continuous.subtype_mk
  have hinv : Continuous (fun x : restrictedOpenDenominatorLocus H u J ↦
      (boundaryDenominator J u (x : RestrictedSource m p a))⁻¹) := by
    apply Continuous.inv₀
    · exact (continuous_boundaryDenominator u J hu hJ).comp continuous_subtype_val
    · intro x
      exact boundaryDenominator_ne_zero_of_mem_restrictedOpenDenominatorLocus
        H u J x.property
  change Continuous ((fun x : RestrictedSource m p a × ℝ ↦
    restrictedSourceAppendAuxOne x.1 x.2) ∘
      (fun x : restrictedOpenDenominatorLocus H u J ↦
        ((x : RestrictedSource m p a),
          (boundaryDenominator J u (x : RestrictedSource m p a))⁻¹)))
  exact continuous_restrictedSourceAppendAuxOne.comp
    (continuous_subtype_val.prodMk hinv)

theorem continuous_restrictedCanonicalDenominatorDrop
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J : RestrictedSource m p a → ℝ) :
    Continuous (restrictedCanonicalDenominatorDrop H u J) := by
  apply Continuous.subtype_mk
  exact continuous_fst.comp
    (continuous_restrictedDenominatorProjection.comp continuous_subtype_val)

/-- The canonical reciprocal graph lift is a homeomorphism from the open
constraint locus onto its closed realization with one fresh coordinate. -/
def restrictedOpenClosedDenominatorHomeomorph
    {m p a r b : ℕ}
    (H : Fin r → RestrictedSource m p a → ℝ)
    (u : Fin b → RestrictedSource m p a → ℝ)
    (J : RestrictedSource m p a → ℝ)
    (hu : ∀ i, Continuous (u i)) (hJ : Continuous J) :
    restrictedOpenDenominatorLocus H u J ≃ₜ
      restrictedClosedDenominatorLocus H u (boundaryDenominator J u) where
  toFun := restrictedCanonicalDenominatorLift H u J
  invFun := restrictedCanonicalDenominatorDrop H u J
  left_inv := restrictedCanonicalDenominatorDrop_lift H u J
  right_inv := restrictedCanonicalDenominatorLift_drop H u J
  continuous_toFun := continuous_restrictedCanonicalDenominatorLift H u J hu hJ
  continuous_invFun := continuous_restrictedCanonicalDenominatorDrop H u J

end AbelFormalization
