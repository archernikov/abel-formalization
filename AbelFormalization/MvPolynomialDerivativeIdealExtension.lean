import AbelFormalization.PolynomialDerivativeIdealExtension
import Mathlib.Algebra.MvPolynomial.PDeriv

set_option autoImplicit false

/-!
# Partial-derivative-stable ideals in finitely many variables

Over a commutative rational algebra, an ideal of a polynomial ring in
finitely many variables which is stable under every formal partial
derivative is extended from the coefficient ring.

The proof peels off variable `0` with `MvPolynomial.finSuccEquiv`.  The
partial derivative in that variable becomes the ordinary univariate
derivative, while the remaining partial derivatives preserve the
coefficient contraction.  The one-variable extension theorem then reduces
the result by induction to one fewer variable.
-/

noncomputable section

namespace AbelFormalization

variable {C : Type*} [CommRing C] [Algebra ℚ C]

/-- Constants from the original coefficient ring are carried to constants
in the iterated polynomial presentation. -/
@[simp]
theorem mvPolynomial_finSuccEquiv_C
    {n : ℕ} (c : C) :
    MvPolynomial.finSuccEquiv C n (MvPolynomial.C c) =
      Polynomial.C (MvPolynomial.C c) := by
  simpa only [MvPolynomial.C_eq_algebraMap, Polynomial.algebraMap_apply]
    using (MvPolynomial.finSuccEquiv C n).commutes c

/-! ## The distinguished variable under `finSuccEquiv` -/

/-- Under `finSuccEquiv`, differentiation in variable `0` is ordinary
univariate differentiation. -/
theorem mvPolynomial_finSuccEquiv_pderiv_zero
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) C) :
    MvPolynomial.finSuccEquiv C n (MvPolynomial.pderiv 0 P) =
      Polynomial.derivative (MvPolynomial.finSuccEquiv C n P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      simp [mvPolynomial_finSuccEquiv_C]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ, Polynomial.derivative_add]
  | mul_X P i hP =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [MvPolynomial.pderiv_mul, hP, Polynomial.derivative_mul,
          MvPolynomial.finSuccEquiv_X_zero, mul_comm]
      · simp [MvPolynomial.pderiv_mul, hP, Polynomial.derivative_mul,
          MvPolynomial.finSuccEquiv_X_succ, mul_comm]

/-! ## The retained coefficient variables -/

/-- The variables `1, ..., n` become constant coefficients under
`finSuccEquiv`. -/
@[simp]
theorem mvPolynomial_finSuccEquiv_rename_succ
    {n : ℕ} (P : MvPolynomial (Fin n) C) :
    MvPolynomial.finSuccEquiv C n (MvPolynomial.rename Fin.succ P) =
      Polynomial.C P := by
  have h :
      (MvPolynomial.finSuccEquiv C n).toRingHom.comp
          (MvPolynomial.rename Fin.succ).toRingHom =
        (Polynomial.C : MvPolynomial (Fin n) C →+*
          Polynomial (MvPolynomial (Fin n) C)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change
        MvPolynomial.finSuccEquiv C n
            (MvPolynomial.rename Fin.succ (MvPolynomial.C a)) =
          Polynomial.C (MvPolynomial.C a)
      rw [MvPolynomial.rename_C, mvPolynomial_finSuccEquiv_C]
    · intro i
      change
        MvPolynomial.finSuccEquiv C n
            (MvPolynomial.rename Fin.succ (MvPolynomial.X i)) =
          Polynomial.C (MvPolynomial.X i)
      rw [MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_succ]
  exact RingHom.congr_fun h P

/-- Equivalently, a constant polynomial over the retained polynomial ring
is sent back to the same polynomial with all variables shifted by one. -/
@[simp]
theorem mvPolynomial_finSuccEquiv_symm_C
    {n : ℕ} (P : MvPolynomial (Fin n) C) :
    (MvPolynomial.finSuccEquiv C n).symm (Polynomial.C P) =
      MvPolynomial.rename Fin.succ P := by
  apply (MvPolynomial.finSuccEquiv C n).injective
  rw [(MvPolynomial.finSuccEquiv C n).apply_symm_apply,
    mvPolynomial_finSuccEquiv_rename_succ]

/-- The inverse image of a constant coefficient intertwines a retained
partial derivative with the corresponding successor-indexed derivative. -/
theorem mvPolynomial_finSuccEquiv_pderiv_succ_symm_C
    {n : ℕ} (j : Fin n) (P : MvPolynomial (Fin n) C) :
    MvPolynomial.finSuccEquiv C n
        (MvPolynomial.pderiv j.succ
          ((MvPolynomial.finSuccEquiv C n).symm (Polynomial.C P))) =
      Polynomial.C (MvPolynomial.pderiv j P) := by
  rw [mvPolynomial_finSuccEquiv_symm_C,
    MvPolynomial.pderiv_rename (Fin.succ_injective n),
    mvPolynomial_finSuccEquiv_rename_succ]

/-! ## Transporting derivative stability through `finSuccEquiv` -/

/-- If an ideal is stable under all partial derivatives, its image under
`finSuccEquiv` is stable under the outer univariate derivative. -/
theorem mvPolynomial_finSuccEquiv_map_derivative_stable
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) C))
    (hderiv : ∀ i P, P ∈ I → MvPolynomial.pderiv i P ∈ I) :
    ∀ Q ∈ I.map (MvPolynomial.finSuccEquiv C n).toRingHom,
      Polynomial.derivative Q ∈
        I.map (MvPolynomial.finSuccEquiv C n).toRingHom := by
  intro Q hQ
  let e := MvPolynomial.finSuccEquiv C n
  have hpre : e.symm Q ∈ I := by
    exact (Ideal.symm_apply_mem_of_equiv_iff
      (I := I) (f := e.toRingEquiv) (y := Q)).2 hQ
  have hd : MvPolynomial.pderiv (0 : Fin (n + 1)) (e.symm Q) ∈ I :=
    hderiv 0 _ hpre
  have hmap :
      e (MvPolynomial.pderiv (0 : Fin (n + 1)) (e.symm Q)) ∈
        I.map e.toRingHom := by
    exact (Ideal.apply_mem_of_equiv_iff
      (I := I) (f := e.toRingEquiv)
      (x := MvPolynomial.pderiv (0 : Fin (n + 1)) (e.symm Q))).2 hd
  rw [mvPolynomial_finSuccEquiv_pderiv_zero, e.apply_symm_apply] at hmap
  exact hmap

/-- The coefficient contraction of the transported ideal remains stable
under every partial derivative in the retained variables. -/
theorem mvPolynomial_finSuccEquiv_coefficientContraction_pderiv_stable
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) C))
    (hderiv : ∀ i P, P ∈ I → MvPolynomial.pderiv i P ∈ I) :
    ∀ j P,
      P ∈ (I.map (MvPolynomial.finSuccEquiv C n).toRingHom).comap
          Polynomial.C →
        MvPolynomial.pderiv j P ∈
          (I.map (MvPolynomial.finSuccEquiv C n).toRingHom).comap
            Polynomial.C := by
  intro j P hP
  let e := MvPolynomial.finSuccEquiv C n
  change Polynomial.C P ∈ I.map e.toRingHom at hP
  change Polynomial.C (MvPolynomial.pderiv j P) ∈ I.map e.toRingHom
  have hpre : e.symm (Polynomial.C P) ∈ I := by
    exact (Ideal.symm_apply_mem_of_equiv_iff
      (I := I) (f := e.toRingEquiv) (y := Polynomial.C P)).2 hP
  have hd :
      MvPolynomial.pderiv j.succ (e.symm (Polynomial.C P)) ∈ I :=
    hderiv j.succ _ hpre
  have hmap :
      e (MvPolynomial.pderiv j.succ (e.symm (Polynomial.C P))) ∈
        I.map e.toRingHom := by
    exact (Ideal.apply_mem_of_equiv_iff
      (I := I) (f := e.toRingEquiv)
      (x := MvPolynomial.pderiv j.succ
        (e.symm (Polynomial.C P)))).2 hd
  rw [mvPolynomial_finSuccEquiv_pderiv_succ_symm_C] at hmap
  exact hmap

/-- Transport by `finSuccEquiv` does not change contraction all the way to
the original coefficient ring. -/
theorem mvPolynomial_finSuccEquiv_coefficientContraction_comap_C
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) C)) :
    ((I.map (MvPolynomial.finSuccEquiv C n).toRingHom).comap
        Polynomial.C).comap MvPolynomial.C =
      I.comap MvPolynomial.C := by
  ext c
  change
    Polynomial.C (MvPolynomial.C c) ∈
        I.map (MvPolynomial.finSuccEquiv C n).toRingHom ↔
      MvPolynomial.C c ∈ I
  rw [← mvPolynomial_finSuccEquiv_C]
  exact Ideal.apply_mem_of_equiv_iff
    (I := I) (f := (MvPolynomial.finSuccEquiv C n).toRingEquiv)
    (x := MvPolynomial.C c)

/-! ## Finite-variable extension from the coefficient contraction -/

/-- An ideal of a finite-variable polynomial ring over a rational algebra
which is stable under every formal partial derivative is extended from its
contraction to the coefficient ring. -/
theorem mvPolynomial_pderiv_stable_ideal_eq_map_comap :
    ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) C)),
      (∀ i P, P ∈ I → MvPolynomial.pderiv i P ∈ I) →
        I = (I.comap MvPolynomial.C).map MvPolynomial.C := by
  intro n
  induction n with
  | zero =>
      intro I hderiv
      rw [← MvPolynomial.isEmptyRingEquiv_symm_toRingHom
        (R := C) (σ := Fin 0)]
      exact (Ideal.map_comap_eq_self_of_equiv
        (MvPolynomial.isEmptyRingEquiv C (Fin 0)).symm I).symm
  | succ n ih =>
      intro I hderiv
      let e := MvPolynomial.finSuccEquiv C n
      let J : Ideal (Polynomial (MvPolynomial (Fin n) C)) :=
        I.map e.toRingHom
      let K : Ideal (MvPolynomial (Fin n) C) := J.comap Polynomial.C
      have hJderiv : ∀ Q ∈ J, Polynomial.derivative Q ∈ J := by
        exact mvPolynomial_finSuccEquiv_map_derivative_stable I hderiv
      have hJ : J = K.map Polynomial.C := by
        exact polynomial_derivative_stable_ideal_eq_map_comap J hJderiv
      have hKderiv :
          ∀ j P, P ∈ K → MvPolynomial.pderiv j P ∈ K := by
        exact
          mvPolynomial_finSuccEquiv_coefficientContraction_pderiv_stable
            I hderiv
      have hK : K = (K.comap MvPolynomial.C).map MvPolynomial.C :=
        ih K hKderiv
      have hcontraction :
          K.comap MvPolynomial.C = I.comap MvPolynomial.C := by
        exact mvPolynomial_finSuccEquiv_coefficientContraction_comap_C I
      calc
        I = J.map e.symm.toRingHom := by
          exact (Ideal.map_of_equiv e.toRingEquiv).symm
        _ = (K.map Polynomial.C).map e.symm.toRingHom := by
          rw [hJ]
        _ =
            (((K.comap MvPolynomial.C).map MvPolynomial.C).map
              Polynomial.C).map e.symm.toRingHom := by
          exact congrArg
            (fun L : Ideal (MvPolynomial (Fin n) C) =>
              (L.map Polynomial.C).map e.symm.toRingHom) hK
        _ = (K.comap MvPolynomial.C).map
              (e.symm.toRingHom.comp
                (Polynomial.C.comp MvPolynomial.C)) := by
          simp only [Ideal.map_map, RingHom.comp_assoc]
        _ = (K.comap MvPolynomial.C).map MvPolynomial.C := by
          have hcomp :
              e.symm.toRingHom.comp
                  (Polynomial.C.comp MvPolynomial.C) =
                (MvPolynomial.C : C →+* MvPolynomial (Fin (n + 1)) C) := by
            dsimp only [e]
            exact MvPolynomial.finSuccEquiv_comp_C_eq_C n
          rw [hcomp]
        _ = (I.comap MvPolynomial.C).map MvPolynomial.C := by
          rw [hcontraction]

end AbelFormalization
