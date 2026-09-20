import AbelFormalization.RankOneIdealGlobalArtinianDescent
import AbelFormalization.LexicographicInitialIdealLocalization
import Mathlib.Algebra.Notation.Pi.Basic

set_option autoImplicit false

/-!
# Product base change for full lexicographic initial ideals

A coefficient quotient can kill the lowest nonzero weight component of a
polynomial, so full initial formation does not commute with an arbitrary
surjective coefficient map.  A product projection has an additional central
idempotent: multiplying by the coordinate idempotent removes every other
coordinate without changing the selected one.  This supplies a lift whose
support is exactly the support after projection and restores equality.

For example, under `ℤ → ZMod 2` with the ordinary positive weight and
`I = (2 + X)`, the global initial ideal is `(2)` and maps to zero, whereas the
image of `I` is `(X)` and has initial ideal `(X)`.  Thus surjectivity alone is
insufficient.

The abstract hypothesis below records precisely the part of that argument
which is needed.  For `f : R →+* S`, a coefficient selector `e : R` satisfies

* `f e = 1`, and
* `e * a = 0 ↔ f a = 0` for every coefficient `a`.

The theorem is then specialized first to an arbitrary product coordinate and
finally to the canonical local factors of a commutative Artinian ring.
-/

noncomputable section

namespace AbelFormalization

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Support control -/

/-- The lexicographic minimum depends only on the monomial support. -/
theorem lexicographicMinimumWeight_eq_of_support_eq
    {R S σ : Type*} [CommSemiring R] [CommSemiring S] {h : ℕ}
    (weight : σ → Fin h → ℤ)
    {p : MvPolynomial σ R} {q : MvPolynomial σ S}
    (hsupport : p.support = q.support) :
    lexicographicMinimumWeight weight p =
      lexicographicMinimumWeight weight q := by
  classical
  simp only [lexicographicMinimumWeight, hsupport]

/-! ## The coefficient-selector criterion -/

/-- A surjective coefficient map commutes with full lexicographic initial
formation when it admits an element which isolates exactly the coefficients
surviving the map. -/
theorem lexicographicInitialIdeal_map_eq_of_coefficientSelector
    {R S σ : Type*} [CommRing R] [CommRing S] {h : ℕ}
    (f : R →+* S) (hf : Function.Surjective f)
    (selector : R) (hselector_one : f selector = 1)
    (hselector_kernel : ∀ a : R, selector * a = 0 ↔ f a = 0)
    (weight : σ → Fin h → ℤ)
    (I : Ideal (MvPolynomial σ R)) :
    (lexicographicInitialIdeal weight I).map (MvPolynomial.map f) =
      lexicographicInitialIdeal weight
        (I.map (MvPolynomial.map f)) := by
  classical
  let φ : MvPolynomial σ R →+* MvPolynomial σ S :=
    MvPolynomial.map f
  have hφ : Function.Surjective φ :=
    MvPolynomial.map_surjective f hf
  apply le_antisymm
  · exact lexicographicInitialIdeal_map_le f weight I
  · refine Ideal.span_le.mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hpq⟩ :=
      (Ideal.mem_map_iff_of_surjective φ hφ).mp hq
    let isolated : MvPolynomial σ R := MvPolynomial.C selector * p
    have hisolated_mem : isolated ∈ I := by
      exact I.mul_mem_left (MvPolynomial.C selector) hp
    have hisolated_map : φ isolated = q := by
      change MvPolynomial.map f (MvPolynomial.C selector * p) = q
      rw [map_mul, MvPolynomial.map_C, hselector_one,
        MvPolynomial.C_1, one_mul, hpq]
    have hcoeff (d : σ →₀ ℕ) : f (p.coeff d) = q.coeff d := by
      have hd := congrArg (fun P : MvPolynomial σ S => P.coeff d) hpq
      simpa only [φ, MvPolynomial.coeff_map] using hd
    have hsupport : isolated.support = q.support := by
      ext d
      simp only [MvPolynomial.mem_support_iff]
      change isolated.coeff d ≠ 0 ↔ q.coeff d ≠ 0
      rw [show isolated.coeff d = selector * p.coeff d by
        simp only [isolated, MvPolynomial.coeff_C_mul]]
      simpa only [hcoeff d] using
        not_congr (hselector_kernel (p.coeff d))
    have hminimum :
        lexicographicMinimumWeight weight isolated =
          lexicographicMinimumWeight weight q :=
      lexicographicMinimumWeight_eq_of_support_eq weight hsupport
    have hform :
        φ (lexicographicInitialForm weight isolated) =
          lexicographicInitialForm weight q := by
      calc
        φ (lexicographicInitialForm weight isolated) =
            MvPolynomial.weightedHomogeneousComponent
              (fun i => toLex (weight i))
              (lexicographicMinimumWeight weight isolated)
              (φ isolated) := by
                simpa only [φ, lexicographicInitialForm] using
                  mvPolynomial_map_weightedHomogeneousComponent f
                    (fun i => toLex (weight i))
                    (lexicographicMinimumWeight weight isolated) isolated
        _ = MvPolynomial.weightedHomogeneousComponent
              (fun i => toLex (weight i))
              (lexicographicMinimumWeight weight q) q := by
                rw [hminimum, hisolated_map]
        _ = lexicographicInitialForm weight q := rfl
    have hmapmem : φ (lexicographicInitialForm weight isolated) ∈
        (lexicographicInitialIdeal weight I).map φ :=
      Ideal.mem_map_of_mem φ
        (lexicographicInitialForm_mem_initialIdeal
          weight I hisolated_mem)
    rwa [hform] at hmapmem

/-! ## Coordinate projections of product rings -/

/-- Multiplication by a coordinate idempotent is zero exactly when the
selected coordinate is zero. -/
theorem pi_single_one_mul_eq_zero_iff
    {κ : Type*} [DecidableEq κ] (A : κ → Type*) [∀ k, Semiring (A k)]
    (k : κ) (a : ∀ k, A k) :
    Pi.single k (1 : A k) * a = 0 ↔ a k = 0 := by
  classical
  constructor
  · intro h
    have hk := congrFun h k
    simpa using hk
  · intro hk
    funext j
    by_cases hj : j = k
    · subst j
      simp [hk]
    · simp [Pi.single_apply, hj]

/-- Full lexicographic initial ideals commute with every coordinate
projection from a product coefficient ring.  Finiteness of the index type is
not needed for this elementwise statement. -/
theorem lexicographicInitialIdeal_map_piEval
    {κ σ : Type*} (A : κ → Type*) [∀ k, CommRing (A k)]
    {h : ℕ} (k : κ) (weight : σ → Fin h → ℤ)
    (I : Ideal (MvPolynomial σ (∀ k, A k))) :
    (lexicographicInitialIdeal weight I).map
        (MvPolynomial.map (Pi.evalRingHom A k)) =
      lexicographicInitialIdeal weight
        (I.map (MvPolynomial.map (Pi.evalRingHom A k))) := by
  classical
  apply lexicographicInitialIdeal_map_eq_of_coefficientSelector
    (Pi.evalRingHom A k) (Function.surjective_eval k)
    (Pi.single k (1 : A k))
  · simp
  · intro a
    simpa only [Pi.evalRingHom_apply] using
      pi_single_one_mul_eq_zero_iff A k a

/-! ## Canonical Artinian local factors -/

variable (B : Type*) [CommRing B] [IsArtinianRing B]

/-- The coefficient projection to one canonical Artinian local factor,
expressed through the product decomposition. -/
noncomputable def artinianLocalFactorProjection
    (m : MaximalSpectrum B) : B →+* artinianLocalFactor B m :=
  (Pi.evalRingHom
      (fun m : MaximalSpectrum B => artinianLocalFactor B m) m).comp
    (artinianLocalFactorEquiv B).toRingHom

/-- The central idempotent selecting one canonical local factor, transported
back to the Artinian ring. -/
noncomputable def artinianLocalFactorSelector
    (m : MaximalSpectrum B) : B := by
  classical
  exact (artinianLocalFactorEquiv B).symm
    (Pi.single m (1 : artinianLocalFactor B m))

theorem artinianLocalFactorProjection_surjective
    (m : MaximalSpectrum B) :
    Function.Surjective (artinianLocalFactorProjection B m) :=
  (Function.surjective_eval m).comp
    (artinianLocalFactorEquiv B).surjective

@[simp]
theorem artinianLocalFactorProjection_selector
    (m : MaximalSpectrum B) :
    artinianLocalFactorProjection B m
        (artinianLocalFactorSelector B m) = 1 := by
  classical
  simp [artinianLocalFactorProjection, artinianLocalFactorSelector]

theorem artinianLocalFactorSelector_mul_eq_zero_iff
    (m : MaximalSpectrum B) (a : B) :
    artinianLocalFactorSelector B m * a = 0 ↔
      artinianLocalFactorProjection B m a = 0 := by
  classical
  let E := artinianLocalFactorEquiv B
  change artinianLocalFactorSelector B m * a = 0 ↔ E a m = 0
  have hmul :
      E (artinianLocalFactorSelector B m * a) =
        Pi.single m (1 : artinianLocalFactor B m) * E a := by
    simp only [map_mul, artinianLocalFactorSelector, E,
      RingEquiv.apply_symm_apply]
  constructor
  · intro h
    apply (pi_single_one_mul_eq_zero_iff
      (fun m : MaximalSpectrum B => artinianLocalFactor B m) m (E a)).mp
    rw [← hmul, h, map_zero]
  · intro h
    apply E.injective
    rw [map_zero, hmul]
    exact (pi_single_one_mul_eq_zero_iff
      (fun m : MaximalSpectrum B => artinianLocalFactor B m) m (E a)).mpr h

/-- Evaluating the polynomial product equivalence at one factor is exactly
coefficient base change along `artinianLocalFactorProjection`. -/
theorem artinianLocalFactorPolynomialEquiv_comp_eval
    (σ : Type*) (m : MaximalSpectrum B) :
    (Pi.evalRingHom
      (fun m : MaximalSpectrum B =>
        MvPolynomial σ (artinianLocalFactor B m)) m).comp
        (artinianLocalFactorPolynomialEquiv B σ).toRingHom =
      MvPolynomial.map (artinianLocalFactorProjection B m) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp [artinianLocalFactorPolynomialEquiv,
      artinianLocalFactorProjection, mvPolynomialPiRingEquiv_apply]
  · intro i
    simp [artinianLocalFactorPolynomialEquiv,
      artinianLocalFactorProjection, mvPolynomialPiRingEquiv_apply]

/-- The ideal equivalence used for Artinian decomposition is coordinatewise
ideal mapping along the displayed coefficient projection. -/
theorem artinianLocalFactorPolynomialIdealEquiv_apply_eq_map_projection
    (σ : Type*) (I : Ideal (MvPolynomial σ B))
    (m : MaximalSpectrum B) :
    artinianLocalFactorPolynomialIdealEquiv B σ I m =
      I.map (MvPolynomial.map (artinianLocalFactorProjection B m)) := by
  change
    ((I.map (artinianLocalFactorPolynomialEquiv B σ).toRingHom).map
      (Pi.evalRingHom
        (fun m : MaximalSpectrum B =>
          MvPolynomial σ (artinianLocalFactor B m)) m)) = _
  rw [Ideal.map_map, artinianLocalFactorPolynomialEquiv_comp_eval]

/-- Full lexicographic initial formation commutes with the canonical
Artinian local-factor projection.  This discharges the `initial_factor`
field of `RankOneGlobalArtinianDescentData`; no extra base-change hypothesis
is required for that field. -/
theorem artinianLocalFactorPolynomialIdealEquiv_lexicographicInitialIdeal
    {σ : Type*} {h : ℕ} (weight : σ → Fin h → ℤ)
    (I : Ideal (MvPolynomial σ B)) (m : MaximalSpectrum B) :
    artinianLocalFactorPolynomialIdealEquiv B σ
        (lexicographicInitialIdeal weight I) m =
      lexicographicInitialIdeal weight
        (artinianLocalFactorPolynomialIdealEquiv B σ I m) := by
  rw [artinianLocalFactorPolynomialIdealEquiv_apply_eq_map_projection,
    artinianLocalFactorPolynomialIdealEquiv_apply_eq_map_projection]
  exact lexicographicInitialIdeal_map_eq_of_coefficientSelector
    (artinianLocalFactorProjection B m)
    (artinianLocalFactorProjection_surjective B m)
    (artinianLocalFactorSelector B m)
    (artinianLocalFactorProjection_selector B m)
    (artinianLocalFactorSelector_mul_eq_zero_iff B m)
    weight I

end AbelFormalization
