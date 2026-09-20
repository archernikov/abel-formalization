import AbelFormalization.RankOneIdealArtinianDescent

set_option autoImplicit false

/-!
# Rank-one transport under polynomial algebra equivalences

This file identifies the coefficient-linear action of a polynomial algebra
equivalence on the rank-one free polynomial module with ideal mapping.  It
also packages restriction of that action to a bounded polynomial window.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n r h : ℕ}

/-- Apply a polynomial algebra equivalence in each coordinate of a finite
free polynomial module. -/
def polynomialAlgEquivModuleEquiv
    (J : MvPolynomial (Fin n) B ≃ₐ[B] MvPolynomial (Fin n) B) :
    artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r :=
  LinearEquiv.piCongrRight (fun _ : Fin r ↦ J.toLinearEquiv)

@[simp]
theorem polynomialAlgEquivModuleEquiv_apply
    (J : MvPolynomial (Fin n) B ≃ₐ[B] MvPolynomial (Fin n) B)
    (P : artinianFreePolynomialModule B n r) (k : Fin r) :
    polynomialAlgEquivModuleEquiv J P k = J (P k) :=
  rfl

@[simp]
theorem polynomialAlgEquivModuleEquiv_symm_apply
    (J : MvPolynomial (Fin n) B ≃ₐ[B] MvPolynomial (Fin n) B)
    (P : artinianFreePolynomialModule B n r) (k : Fin r) :
    (polynomialAlgEquivModuleEquiv J).symm P k = J.symm (P k) :=
  rfl

/-- Ideal mapping by an algebra equivalence is exactly coefficient-linear
mapping of the associated rank-one polynomial submodule. -/
theorem rankOnePolynomialIdealSubmodule_map_algEquiv
    (J : MvPolynomial (Fin n) B ≃ₐ[B] MvPolynomial (Fin n) B)
    (I : Ideal (MvPolynomial (Fin n) B)) :
    (rankOnePolynomialIdealSubmodule
        (I.map J.toRingHom)).restrictScalars B =
      ((rankOnePolynomialIdealSubmodule I).restrictScalars B).map
        (polynomialAlgEquivModuleEquiv (r := 1) J).toLinearMap := by
  ext P
  rw [Submodule.mem_map_equiv]
  change P ∈ rankOnePolynomialIdealSubmodule (I.map J.toRingHom) ↔
    (polynomialAlgEquivModuleEquiv (r := 1) J).symm P ∈
      rankOnePolynomialIdealSubmodule I
  rw [mem_rankOnePolynomialIdealSubmodule_iff,
    mem_rankOnePolynomialIdealSubmodule_iff]
  change P 0 ∈ I.map J.toRingHom ↔ J.symm (P 0) ∈ I
  rw [Ideal.mem_map_iff_of_surjective J.toRingHom J.surjective]
  constructor
  · rintro ⟨Q, hQ, hQP⟩
    change J Q = P 0 at hQP
    have hEq : J.symm (P 0) = Q := by
      rw [← hQP, J.symm_apply_apply]
    rw [hEq]
    exact hQ
  · intro hP
    exact ⟨J.symm (P 0), hP, J.apply_symm_apply (P 0)⟩

variable (G : PolynomialGradedLexData n r h)

/-- The inverse of the restricted window equivalence has the expected
ambient value. -/
theorem PolynomialGradedLexData.windowRestriction_symm_coe
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r)
    (hJ : (G.windowModule B hpositive D).map J.toLinearMap =
      G.windowModule B hpositive D)
    (P : G.windowModule B hpositive D) :
    (G.windowRestriction hpositive D J hJ).symm P =
      ⟨J.symm P, by
        have himage : (P : artinianFreePolynomialModule B n r) ∈
            (G.windowModule B hpositive D).map J.toLinearMap := by
          rw [hJ]
          exact P.property
        rw [Submodule.mem_map_equiv] at himage
        exact himage⟩ := by
  apply (G.windowRestriction hpositive D J hJ).injective
  apply Subtype.ext
  simp [G.windowRestriction_coe]

/-- If an ambient coefficient-linear equivalence maps one polynomial
submodule to another and preserves the window, its restriction maps their
bounded parts exactly. -/
theorem PolynomialGradedLexData.polynomialWindowPart_map_equiv
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r)
    (hJ : (G.windowModule B hpositive D).map J.toLinearMap =
      G.windowModule B hpositive D)
    (N N' : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (hmap : N'.restrictScalars B =
      (N.restrictScalars B).map J.toLinearMap) :
    G.polynomialWindowPart hpositive D N' =
      (G.polynomialWindowPart hpositive D N).map
        (G.windowRestriction hpositive D J hJ).toLinearMap := by
  ext P
  rw [Submodule.mem_map_equiv]
  change (P : artinianFreePolynomialModule B n r) ∈ N' ↔
    (((G.windowRestriction hpositive D J hJ).symm P :
      G.windowModule B hpositive D) :
        artinianFreePolynomialModule B n r) ∈ N
  change (P : artinianFreePolynomialModule B n r) ∈
      N'.restrictScalars B ↔
    (((G.windowRestriction hpositive D J hJ).symm P :
      G.windowModule B hpositive D) :
        artinianFreePolynomialModule B n r) ∈ N.restrictScalars B
  rw [hmap, Submodule.mem_map_equiv]
  change J.symm (P : artinianFreePolynomialModule B n r) ∈
      N.restrictScalars B ↔ _
  rw [G.windowRestriction_symm_coe]

/-- Transporting both bounded parts to the ordered product turns the
restricted action into the window conjugate used by finite descent. -/
theorem PolynomialGradedLexData.polynomialWindowOrderedWeightPart_map_equiv
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r)
    (hJ : (G.windowModule B hpositive D).map J.toLinearMap =
      G.windowModule B hpositive D)
    (N N' : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (hmap : N'.restrictScalars B =
      (N.restrictScalars B).map J.toLinearMap) :
    G.polynomialWindowOrderedWeightPart hpositive D N' =
      (G.polynomialWindowOrderedWeightPart hpositive D N).map
        (G.windowOrderedWeightConjugate hpositive D J hJ).toLinearMap := by
  unfold PolynomialGradedLexData.polynomialWindowOrderedWeightPart
  rw [G.polynomialWindowPart_map_equiv hpositive D J hJ N N' hmap]
  ext x
  simp only [Submodule.mem_map_equiv]
  simp only [PolynomialGradedLexData.windowOrderedWeightConjugate,
    LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  simp only [LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply]

end AbelFormalization
