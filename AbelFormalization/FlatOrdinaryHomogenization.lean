import AbelFormalization.OrdinaryHomogenization
import AbelFormalization.OrdinaryHomogeneousDehomogenizationHeight
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false

/-!
# Flat ordinary homogenization

This scratch module puts the outer homogenizing variable used by
`ordinaryHomogenize` into the same `MvPolynomial` variable type as the
original variables.  The distinguished homogenizing variable is the unique
element of `Fin 1` on the left of `Fin 1 ⊕ ι`.

The construction is transported through an explicit algebra equivalence,
so the existing height theorem for full ordinary homogenization applies
without any new commutative-algebra argument.  The remaining proofs record
that the transported generators are homogeneous and that evaluation at the
distinguished variable equal to one recovers the original ideal exactly.
-/

noncomputable section

namespace AbelFormalization

variable {R ι : Type*}

/-- `none` is the new homogenizing variable and `some i` is the old variable
`i`.  This is stated explicitly instead of hiding the variable convention in
an arbitrary cardinality equivalence. -/
def optionEquivFinOneSum (ι : Type*) : Option ι ≃ Fin 1 ⊕ ι where
  toFun
    | none => Sum.inl 0
    | some i => Sum.inr i
  invFun
    | Sum.inl _ => none
    | Sum.inr i => some i
  left_inv := by
    intro i
    cases i <;> rfl
  right_inv := by
    intro i
    rcases i with j | j
    · change Sum.inl (0 : Fin 1) = Sum.inl j
      exact congrArg Sum.inl (Subsingleton.elim _ _)
    · rfl

@[simp]
theorem optionEquivFinOneSum_none :
    optionEquivFinOneSum ι none = Sum.inl 0 :=
  rfl

@[simp]
theorem optionEquivFinOneSum_some (i : ι) :
    optionEquivFinOneSum ι (some i) = Sum.inr i :=
  rfl

@[simp]
theorem optionEquivFinOneSum_symm_inl (j : Fin 1) :
    (optionEquivFinOneSum ι).symm (Sum.inl j) = none :=
  rfl

@[simp]
theorem optionEquivFinOneSum_symm_inr (i : ι) :
    (optionEquivFinOneSum ι).symm (Sum.inr i) = some i :=
  rfl

section Semiring

variable [CommSemiring R]

/-- Regroup a flat polynomial in the variables `Fin 1 ⊕ ι` as a
univariate polynomial in the distinguished variable, with coefficients in
the old multivariate polynomial ring. -/
def flatPolynomialEquiv (R : Type*) [CommSemiring R] (ι : Type*) :
    MvPolynomial (Fin 1 ⊕ ι) R ≃ₐ[R]
      Polynomial (MvPolynomial ι R) :=
  (MvPolynomial.renameEquiv R (optionEquivFinOneSum ι).symm).trans
    (MvPolynomial.optionEquivLeft R ι)

@[simp]
theorem flatPolynomialEquiv_C (r : R) :
    flatPolynomialEquiv R ι (MvPolynomial.C r) =
      Polynomial.C (MvPolynomial.C r) := by
  simp [flatPolynomialEquiv]

@[simp]
theorem flatPolynomialEquiv_X_left (j : Fin 1) :
    flatPolynomialEquiv R ι (MvPolynomial.X (Sum.inl j)) =
      Polynomial.X := by
  simp [flatPolynomialEquiv]

@[simp]
theorem flatPolynomialEquiv_X_right (i : ι) :
    flatPolynomialEquiv R ι (MvPolynomial.X (Sum.inr i)) =
      Polynomial.C (MvPolynomial.X i) := by
  simp [flatPolynomialEquiv]

/-- The Option-indexed form of ordinary homogenization, before renaming
`none` and `some i` to the two summands of `Fin 1 ⊕ ι`. -/
def optionOrdinaryHomogenize (f : MvPolynomial ι R) :
    MvPolynomial (Option ι) R :=
  (MvPolynomial.optionEquivLeft R ι).symm (ordinaryHomogenize f)

/-- Ordinary homogenization as one flat multivariate polynomial. -/
def flatOrdinaryHomogenize (f : MvPolynomial ι R) :
    MvPolynomial (Fin 1 ⊕ ι) R :=
  (flatPolynomialEquiv R ι).symm (ordinaryHomogenize f)

theorem flatOrdinaryHomogenize_eq_rename (f : MvPolynomial ι R) :
    flatOrdinaryHomogenize f =
      MvPolynomial.rename (optionEquivFinOneSum ι)
        (optionOrdinaryHomogenize f) := by
  rfl

private theorem optionEquivLeft_symm_monomial
    (d : ι →₀ ℕ) (k : ℕ) (r : R) :
    (MvPolynomial.optionEquivLeft R ι).symm
        (Polynomial.monomial k (MvPolynomial.monomial d r)) =
      MvPolynomial.monomial (d.optionElim k) r := by
  apply (MvPolynomial.optionEquivLeft R ι).injective
  rw [AlgEquiv.apply_symm_apply]
  simpa using
    (MvPolynomial.optionEquivLeft_monomial
      (R := R) (S₁ := ι) (d.optionElim k) r).symm

private theorem degree_optionElim (d : ι →₀ ℕ) (k : ℕ) :
    (d.optionElim k).degree = k + d.degree := by
  classical
  have hsplit :
      d.optionElim k =
        Finsupp.single none k + d.embDomain Function.Embedding.some := by
    ext i
    rcases i with _ | i <;> simp
  rw [hsplit, map_add, Finsupp.degree_single,
    Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]

/-- The Option-indexed homogenization is homogeneous of the original total
degree.  This includes the zero polynomial, for which mathlib's total degree
is zero. -/
theorem optionOrdinaryHomogenize_isHomogeneous
    (f : MvPolynomial ι R) :
    (optionOrdinaryHomogenize f).IsHomogeneous f.totalDegree := by
  classical
  rw [optionOrdinaryHomogenize, ordinaryHomogenize, map_sum]
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  rw [optionEquivLeft_symm_monomial]
  apply MvPolynomial.isHomogeneous_monomial
  rw [degree_optionElim]
  change f.totalDegree - d.degree + d.degree = f.totalDegree
  apply Nat.sub_add_cancel
  exact MvPolynomial.le_totalDegree hd

/-- Every flat ordinary homogenization is homogeneous of its original total
degree for the ordinary grading in which all variables, including `H`, have
degree one. -/
theorem flatOrdinaryHomogenize_isHomogeneous
    (f : MvPolynomial ι R) :
    (flatOrdinaryHomogenize f).IsHomogeneous f.totalDegree := by
  rw [flatOrdinaryHomogenize_eq_rename]
  exact (optionOrdinaryHomogenize_isHomogeneous f).rename_isHomogeneous

/-- Full flat ordinary homogenization is the transport of the existing full
ordinary homogenization ideal across the polynomial regrouping equivalence. -/
def flatFullOrdinaryHomogenization (I : Ideal (MvPolynomial ι R)) :
    Ideal (MvPolynomial (Fin 1 ⊕ ι) R) :=
  (fullOrdinaryHomogenization I).map
    (flatPolynomialEquiv R ι).symm.toRingHom

/-- Generator presentation of the transported full ideal. -/
theorem flatFullOrdinaryHomogenization_eq_span
    (I : Ideal (MvPolynomial ι R)) :
    flatFullOrdinaryHomogenization I =
      Ideal.span
        (flatOrdinaryHomogenize '' (I : Set (MvPolynomial ι R))) := by
  rw [flatFullOrdinaryHomogenization, fullOrdinaryHomogenization,
    Ideal.map_span, Set.image_image]
  rfl

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The flat full ideal is homogeneous for ordinary total degree. -/
theorem flatFullOrdinaryHomogenization_isHomogeneous
    (I : Ideal (MvPolynomial ι R)) :
    (flatFullOrdinaryHomogenization I).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ : Fin 1 ⊕ ι => (1 : ℕ))) := by
  rw [flatFullOrdinaryHomogenization_eq_span]
  refine Ideal.homogeneous_span
    (MvPolynomial.weightedHomogeneousSubmodule R
      (fun _ : Fin 1 ⊕ ι => (1 : ℕ))) _ ?_
  rintro _ ⟨f, _, rfl⟩
  refine ⟨f.totalDegree, ?_⟩
  exact flatOrdinaryHomogenize_isHomogeneous f

end Semiring

section Ring

variable [CommRing R]

/-- Under the flat regrouping equivalence, setting the left variable equal
to one is exactly evaluation of the outer polynomial variable at one. -/
theorem ordinaryDehomogenizationHom_eq_eval_comp_flatPolynomialEquiv :
    ordinaryDehomogenizationHom (B := R) (ι := ι) =
      (Polynomial.evalRingHom (1 : MvPolynomial ι R)).comp
        (flatPolynomialEquiv R ι).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · rintro (j | i)
    · simp
    · simp

/-- Dehomogenizing a transported ordinary homogenization recovers its input
exactly. -/
@[simp]
theorem ordinaryDehomogenizationHom_flatOrdinaryHomogenize
    (f : MvPolynomial ι R) :
    ordinaryDehomogenizationHom (B := R) (ι := ι)
        (flatOrdinaryHomogenize f) = f := by
  rw [ordinaryDehomogenizationHom_eq_eval_comp_flatPolynomialEquiv]
  simp [flatOrdinaryHomogenize]

/-- Dehomogenization at `H = 1` of the full flat homogenization is the
original ideal, as an equality of ideals rather than only a generator-wise
containment. -/
theorem flatFullOrdinaryHomogenization_map_dehomogenization
    (I : Ideal (MvPolynomial ι R)) :
    (flatFullOrdinaryHomogenization I).map
        (ordinaryDehomogenizationHom (B := R) (ι := ι)) = I := by
  rw [flatFullOrdinaryHomogenization_eq_span, Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    simpa using hf
  · intro f hf
    apply Ideal.subset_span
    refine ⟨flatOrdinaryHomogenize f, ⟨f, hf, rfl⟩, ?_⟩
    exact ordinaryDehomogenizationHom_flatOrdinaryHomogenize f

/-- Transport through the explicit algebra equivalence preserves height, so
the existing height equality for full ordinary homogenization immediately
gives the flat version. -/
theorem flatFullOrdinaryHomogenization_height
    [IsNoetherianRing R] [Finite ι]
    (I : Ideal (MvPolynomial ι R)) :
    (flatFullOrdinaryHomogenization I).height = I.height := by
  calc
    (flatFullOrdinaryHomogenization I).height =
        (fullOrdinaryHomogenization I).height :=
      (flatPolynomialEquiv R ι).symm.toRingEquiv.height_map _
    _ = I.height := fullOrdinaryHomogenization_height I

end Ring

end AbelFormalization
