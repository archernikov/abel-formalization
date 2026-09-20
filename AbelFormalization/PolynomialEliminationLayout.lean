import AbelFormalization.PolynomialEliminationHeight
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap

set_option autoImplicit false

/-!
# Actual polynomial ring layout for elimination

The flat ring has one distinguished inverse symbol `none`, auxiliary symbols
`some (inl y)`, and retained symbols `some (inr k)`. It is explicitly identified
with the nested ring R[retained][auxiliary][inverse]. The retained contraction
is preserved as an ideal of the same actual retained coefficient ring.
-/

noncomputable section

namespace AbelFormalization

private theorem ringHom_height_map_of_bijective {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Bijective f) (I : Ideal R) :
    (I.map f).height = I.height := (RingEquiv.ofBijective f hf).height_map I

private theorem ringHom_height_comap_of_bijective {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Bijective f) (I : Ideal S) :
    (I.comap f).height = I.height := (RingEquiv.ofBijective f hf).height_comap I

private theorem algEquiv_height_map_toRingHom {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) (I : Ideal S) :
    (I.map e.toRingHom).height = I.height :=
  ringHom_height_map_of_bijective e.toRingHom e.bijective I

private theorem algEquiv_height_comap_toRingHom {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (e : S ≃ₐ[R] T) (I : Ideal T) :
    (I.comap e.toRingHom).height = I.height :=
  ringHom_height_comap_of_bijective e.toRingHom e.bijective I

variable (B Keep Aux : Type*) [CommRing B]

/-- The flat ring and the ring with retained variables in the coefficients
are genuinely isomorphic as B-algebras. -/
def polynomialEliminationLayout :
    MvPolynomial (Option (Aux ⊕ Keep)) B ≃ₐ[B]
      Polynomial (MvPolynomial Aux (MvPolynomial Keep B)) :=
  (MvPolynomial.optionEquivLeft B (Aux ⊕ Keep)).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.sumAlgEquiv B Aux Keep))

/-- The actual retained-ring inclusion in the flat ring. -/
def polynomialEliminationRetainedFlat :
    MvPolynomial Keep B →+* MvPolynomial (Option (Aux ⊕ Keep)) B :=
  (MvPolynomial.rename (fun k : Keep => some (Sum.inr k))).toRingHom

/-- The actual retained-ring inclusion in the nested ring. -/
def polynomialEliminationRetainedNested :
    MvPolynomial Keep B →+* Polynomial (MvPolynomial Aux (MvPolynomial Keep B)) :=
  Polynomial.C.comp MvPolynomial.C

/-- Embed the entire pre-inverse ring in the flat ring. -/
def polynomialEliminationOldFlat :
    MvPolynomial (Aux ⊕ Keep) B →+* MvPolynomial (Option (Aux ⊕ Keep)) B :=
  (MvPolynomial.rename Option.some).toRingHom

/-- The pre-inverse ring, regrouped with the retained symbols as coefficients. -/
def polynomialEliminationOldNested :
    MvPolynomial (Aux ⊕ Keep) B →+*
      Polynomial (MvPolynomial Aux (MvPolynomial Keep B)) :=
  Polynomial.C.comp (MvPolynomial.sumAlgEquiv B Aux Keep).toRingHom

variable {B Keep Aux}

@[simp] theorem polynomialEliminationLayout_C (b : B) :
    polynomialEliminationLayout B Keep Aux (MvPolynomial.C b) =
      Polynomial.C (MvPolynomial.C (MvPolynomial.C b)) := by
  simp [polynomialEliminationLayout]

@[simp] theorem polynomialEliminationLayout_X_none :
    polynomialEliminationLayout B Keep Aux (MvPolynomial.X none) = Polynomial.X := by
  simp [polynomialEliminationLayout]

@[simp] theorem polynomialEliminationLayout_X_aux (y : Aux) :
    polynomialEliminationLayout B Keep Aux (MvPolynomial.X (some (Sum.inl y))) =
      Polynomial.C (MvPolynomial.X y) := by
  simp [polynomialEliminationLayout]

@[simp] theorem polynomialEliminationLayout_X_retained (k : Keep) :
    polynomialEliminationLayout B Keep Aux (MvPolynomial.X (some (Sum.inr k))) =
      Polynomial.C (MvPolynomial.C (MvPolynomial.X k)) := by
  simp [polynomialEliminationLayout]

@[simp] theorem polynomialEliminationLayout_symm_C_C_C (b : B) :
    (polynomialEliminationLayout B Keep Aux).symm
      (Polynomial.C (MvPolynomial.C (MvPolynomial.C b))) = MvPolynomial.C b := by
  apply (polynomialEliminationLayout B Keep Aux).injective
  simp

@[simp] theorem polynomialEliminationLayout_symm_X :
    (polynomialEliminationLayout B Keep Aux).symm Polynomial.X = MvPolynomial.X none := by
  apply (polynomialEliminationLayout B Keep Aux).injective
  simp

@[simp] theorem polynomialEliminationLayout_symm_C_X (y : Aux) :
    (polynomialEliminationLayout B Keep Aux).symm (Polynomial.C (MvPolynomial.X y)) =
      MvPolynomial.X (some (Sum.inl y)) := by
  apply (polynomialEliminationLayout B Keep Aux).injective
  simp

@[simp] theorem polynomialEliminationLayout_symm_C_C_X (k : Keep) :
    (polynomialEliminationLayout B Keep Aux).symm
      (Polynomial.C (MvPolynomial.C (MvPolynomial.X k))) =
      MvPolynomial.X (some (Sum.inr k)) := by
  apply (polynomialEliminationLayout B Keep Aux).injective
  simp

@[simp] theorem polynomialEliminationRetainedFlat_C (b : B) :
    polynomialEliminationRetainedFlat B Keep Aux (MvPolynomial.C b) = MvPolynomial.C b := by
  simp [polynomialEliminationRetainedFlat]

@[simp] theorem polynomialEliminationRetainedFlat_X (k : Keep) :
    polynomialEliminationRetainedFlat B Keep Aux (MvPolynomial.X k) =
      MvPolynomial.X (some (Sum.inr k)) := by
  simp [polynomialEliminationRetainedFlat]

@[simp] theorem polynomialEliminationRetainedNested_apply (r : MvPolynomial Keep B) :
    polynomialEliminationRetainedNested B Keep Aux r = Polynomial.C (MvPolynomial.C r) := rfl

/-- Regrouping commutes with the exact retained-ring inclusion. -/
theorem polynomialEliminationLayout_comp_retained :
    (polynomialEliminationLayout B Keep Aux).toRingHom.comp
      (polynomialEliminationRetainedFlat B Keep Aux) =
      polynomialEliminationRetainedNested B Keep Aux := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp
  · intro k
    simp

@[simp] theorem polynomialEliminationLayout_retained (r : MvPolynomial Keep B) :
    polynomialEliminationLayout B Keep Aux (polynomialEliminationRetainedFlat B Keep Aux r) =
      Polynomial.C (MvPolynomial.C r) :=
  RingHom.congr_fun polynomialEliminationLayout_comp_retained r

/-- The pre-inverse inclusion also commutes with regrouping. -/
theorem polynomialEliminationLayout_comp_old :
    (polynomialEliminationLayout B Keep Aux).toRingHom.comp
      (polynomialEliminationOldFlat B Keep Aux) =
      polynomialEliminationOldNested B Keep Aux := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp [polynomialEliminationOldFlat, polynomialEliminationOldNested]
  · rintro (y | k)
    · simp [polynomialEliminationOldFlat, polynomialEliminationOldNested]
    · simp [polynomialEliminationOldFlat, polynomialEliminationOldNested]

@[simp] theorem polynomialEliminationLayout_old (P : MvPolynomial (Aux ⊕ Keep) B) :
    polynomialEliminationLayout B Keep Aux (polynomialEliminationOldFlat B Keep Aux P) =
      Polynomial.C (MvPolynomial.sumAlgEquiv B Aux Keep P) :=
  RingHom.congr_fun polynomialEliminationLayout_comp_old P

/-- Mapping the ambient ideal along the actual ring equivalence preserves
its contraction to the retained ring, as an equality of ideals of that ring. -/
theorem polynomialEliminationLayout_contraction_map
    (Q : Ideal (MvPolynomial (Option (Aux ⊕ Keep)) B)) :
    (Q.map (polynomialEliminationLayout B Keep Aux).toRingHom).comap
      (polynomialEliminationRetainedNested B Keep Aux) =
      Q.comap (polynomialEliminationRetainedFlat B Keep Aux) := by
  rw [← polynomialEliminationLayout_comp_retained, ← Ideal.comap_comap]
  rw [Ideal.comap_map_of_bijective
    (I := Q) (polynomialEliminationLayout B Keep Aux).toRingHom
    (polynomialEliminationLayout B Keep Aux).bijective]

/-- The reverse ideal transport has the same exact retained contraction. -/
theorem polynomialEliminationLayout_contraction_comap
    (Q : Ideal (Polynomial (MvPolynomial Aux (MvPolynomial Keep B)))) :
    (Q.comap (polynomialEliminationLayout B Keep Aux).toRingHom).comap
      (polynomialEliminationRetainedFlat B Keep Aux) =
      Q.comap (polynomialEliminationRetainedNested B Keep Aux) := by
  rw [Ideal.comap_comap, polynomialEliminationLayout_comp_retained]

attribute [local irreducible] polynomialEliminationLayout

/-- The ambient ideal height is unchanged by the flat/nested identification. -/
theorem polynomialEliminationLayout_height_map
    (Q : Ideal (MvPolynomial (Option (Aux ⊕ Keep)) B)) :
    Ideal.height (R := Polynomial (MvPolynomial Aux (MvPolynomial Keep B)))
        (Q.map (polynomialEliminationLayout B Keep Aux).toRingHom) =
      Ideal.height (R := MvPolynomial (Option (Aux ⊕ Keep)) B) Q := by
  have h := algEquiv_height_map_toRingHom (R := B)
    (S := MvPolynomial (Option (Aux ⊕ Keep)) B)
    (T := Polynomial (MvPolynomial Aux (MvPolynomial Keep B)))
    (polynomialEliminationLayout B Keep Aux) Q
  exact h

theorem polynomialEliminationLayout_height_comap
    (Q : Ideal (Polynomial (MvPolynomial Aux (MvPolynomial Keep B)))) :
    Ideal.height (R := MvPolynomial (Option (Aux ⊕ Keep)) B)
        (Q.comap (polynomialEliminationLayout B Keep Aux).toRingHom) =
      Ideal.height (R := Polynomial (MvPolynomial Aux (MvPolynomial Keep B))) Q := by
  have h := algEquiv_height_comap_toRingHom (R := B)
    (S := MvPolynomial (Option (Aux ⊕ Keep)) B)
    (T := Polynomial (MvPolynomial Aux (MvPolynomial Keep B)))
    (polynomialEliminationLayout B Keep Aux) Q
  exact h

section FiniteAuxiliary

/-- The flat retained contraction is precisely the previous literal
elimination contraction after regrouping; no substitute coefficient ring is used. -/
theorem polynomialEliminationLayout_eliminationContraction (a : ℕ)
    (Q : Ideal (MvPolynomial (Option (Fin a ⊕ Keep)) B)) :
    polynomialEliminationContraction a
      (Q.map (polynomialEliminationLayout B Keep (Fin a)).toRingHom) =
      Q.comap (polynomialEliminationRetainedFlat B Keep (Fin a)) := by
  unfold polynomialEliminationContraction
  rw [Ideal.comap_comap]
  exact polynomialEliminationLayout_contraction_map Q

variable [IsNoetherianRing B] [Finite Keep]

/-- The exact height cost for eliminating y,z in the flat polynomial layout. -/
theorem polynomialEliminationLayout_height_le_retained_add (a : ℕ)
    (Q : Ideal (MvPolynomial (Option (Fin a ⊕ Keep)) B)) :
    Q.height ≤ (Q.comap (polynomialEliminationRetainedFlat B Keep (Fin a))).height +
      (a + 1 : ℕ) := by
  have h := polynomial_height_le_eliminationContraction_add a
    (Q.map (polynomialEliminationLayout B Keep (Fin a)).toRingHom)
  rwa [polynomialEliminationLayout_height_map,
    polynomialEliminationLayout_eliminationContraction] at h

/-- The retained height bound is unchanged when the rank argument uses the
flat ring and the elimination argument uses the nested ring. -/
theorem polynomialEliminationLayout_retained_height_ge (a r : ℕ)
    (Q : Ideal (MvPolynomial (Option (Fin a ⊕ Keep)) B))
    (hQ : ((r + a + 1 : ℕ) : ℕ∞) ≤ Q.height) :
    (r : ℕ∞) ≤ (Q.comap (polynomialEliminationRetainedFlat B Keep (Fin a))).height := by
  rw [← polynomialEliminationLayout_eliminationContraction]
  apply polynomialEliminationContraction_height_ge a r
  simpa only [polynomialEliminationLayout_height_map] using hQ

end FiniteAuxiliary

end AbelFormalization
