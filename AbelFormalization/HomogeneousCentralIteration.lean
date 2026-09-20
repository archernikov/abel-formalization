import AbelFormalization.FlatOrdinaryHomogenization
import AbelFormalization.CentralUnusedExtension
import AbelFormalization.LexicographicInitialIdealSecondaryHomogeneity
import AbelFormalization.TerminalGlobalParameterDeformation
import AbelFormalization.TerminalReindexedWindowStirling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Homogeneous central iteration

This module puts the central step into the ordinarily homogeneous polynomial
ring used before dehomogenization.  The new variable `H` is the unique member
of the left `Fin 1` summand among the retained variables.  The homogeneous
time shear fixes `H` and every derivative variable and sends every genuine
time variable `t` to `t + H`.

The shear preserves every terminal-weight component, hence commutes with the
full terminal lexicographic initial ideal.  It also commutes with the global
terminal Stirling automorphism.  These two commutation statements give the
exact homogeneous iterate identity.

The final section records the exact dehomogenized one-step identity.  The only
additional hypothesis needed to identify it with an iteration entirely in the
dehomogenized ring is the displayed initial/dehomogenization commutation
equality.  Keeping that equality explicit isolates the remaining bridge.
-/

noncomputable section

namespace AbelFormalization

universe u v w z

open scoped BigOperators

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Two generic graded-automorphism lemmas -/

/-- An algebra equivalence which preserves each weighted homogeneous degree
commutes with the corresponding homogeneous component. -/
theorem weightedHomogeneousComponent_algEquiv_of_preserves
    {R : Type u} {sigma : Type v} {M : Type w}
    [CommRing R] [AddCommMonoid M] [DecidableEq M]
    (weight : sigma → M)
    (E : MvPolynomial sigma R ≃ₐ[R] MvPolynomial sigma R)
    (hE : ∀ {P : MvPolynomial sigma R} {degree : M},
      P.IsWeightedHomogeneous weight degree →
        (E P).IsWeightedHomogeneous weight degree)
    (degree : M) (P : MvPolynomial sigma R) :
    E (MvPolynomial.weightedHomogeneousComponent weight degree P) =
      MvPolynomial.weightedHomogeneousComponent weight degree (E P) := by
  classical
  have hsum :
      (∑ other ∈ P.support.image (Finsupp.weight weight),
        MvPolynomial.weightedHomogeneousComponent weight other P) = P :=
    sum_weightedHomogeneousComponent_support weight P
  calc
    E (MvPolynomial.weightedHomogeneousComponent weight degree P) =
        E (MvPolynomial.weightedHomogeneousComponent weight degree
          (∑ other ∈ P.support.image (Finsupp.weight weight),
            MvPolynomial.weightedHomogeneousComponent weight other P)) := by
      rw [hsum]
    _ = MvPolynomial.weightedHomogeneousComponent weight degree
        (E (∑ other ∈ P.support.image (Finsupp.weight weight),
          MvPolynomial.weightedHomogeneousComponent weight other P)) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro other hother
      have hsource :
          (MvPolynomial.weightedHomogeneousComponent weight other P).IsWeightedHomogeneous
            weight other :=
        MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous other P
      have htarget := hE hsource
      by_cases hdegree : degree = other
      · subst other
        rw [hsource.weightedHomogeneousComponent_same,
          htarget.weightedHomogeneousComponent_same]
      · rw [hsource.weightedHomogeneousComponent_ne degree hdegree,
          map_zero, htarget.weightedHomogeneousComponent_ne degree hdegree]
    _ = MvPolynomial.weightedHomogeneousComponent weight degree (E P) := by
      rw [hsum]

/-- If an algebra automorphism preserves every homogeneous degree for a
lexicographic vector weight, it commutes with the least-weight form. -/
theorem lexicographicInitialForm_algEquiv_of_preserves
    {R : Type u} {sigma : Type v} [CommRing R] {n : ℕ}
    (weight : sigma → Fin n → ℤ)
    (E : MvPolynomial sigma R ≃ₐ[R] MvPolynomial sigma R)
    (hE : ∀ {P : MvPolynomial sigma R}
        {degree : Lex (Fin n → ℤ)},
      P.IsWeightedHomogeneous (fun i ↦ toLex (weight i)) degree →
        (E P).IsWeightedHomogeneous
          (fun i ↦ toLex (weight i)) degree)
    (P : MvPolynomial sigma R) :
    E (lexicographicInitialForm weight P) =
      lexicographicInitialForm weight (E P) := by
  classical
  by_cases hP : P = 0
  · subst P
    simp
  let lexWeight : sigma → Lex (Fin n → ℤ) :=
    fun i ↦ toLex (weight i)
  let beta : Lex (Fin n → ℤ) :=
    lexicographicMinimumWeight weight P
  have hcomponent :
      E (MvPolynomial.weightedHomogeneousComponent lexWeight beta P) =
        MvPolynomial.weightedHomogeneousComponent lexWeight beta (E P) :=
    weightedHomogeneousComponent_algEquiv_of_preserves
      lexWeight E hE beta P
  have hsourceComponent :
      MvPolynomial.weightedHomogeneousComponent lexWeight beta P ≠ 0 := by
    change lexicographicInitialForm weight P ≠ 0
    exact lexicographicInitialForm_ne_zero weight hP
  have htargetComponent :
      MvPolynomial.weightedHomogeneousComponent lexWeight beta (E P) ≠ 0 := by
    intro hzero
    apply hsourceComponent
    apply E.injective
    rw [map_zero, hcomponent, hzero]
  have hbound : ∀ d ∈ (E P).support,
      beta ≤ Finsupp.weight lexWeight d := by
    intro d hd
    by_contra hnot
    have hlt : Finsupp.weight lexWeight d < beta := lt_of_not_ge hnot
    let gamma : Lex (Fin n → ℤ) := Finsupp.weight lexWeight d
    have htargetGamma :
        MvPolynomial.weightedHomogeneousComponent
            lexWeight gamma (E P) ≠ 0 := by
      intro hzero
      have hcoeff := congrArg
        (fun Q : MvPolynomial sigma R ↦ Q.coeff d) hzero
      rw [MvPolynomial.coeff_weightedHomogeneousComponent,
        if_pos rfl, MvPolynomial.coeff_zero] at hcoeff
      exact (MvPolynomial.mem_support_iff.mp hd) hcoeff
    have hgammaComponent :
        E (MvPolynomial.weightedHomogeneousComponent lexWeight gamma P) =
          MvPolynomial.weightedHomogeneousComponent
            lexWeight gamma (E P) :=
      weightedHomogeneousComponent_algEquiv_of_preserves
        lexWeight E hE gamma P
    have hsourceGamma :
        MvPolynomial.weightedHomogeneousComponent lexWeight gamma P ≠ 0 := by
      intro hzero
      apply htargetGamma
      rw [← hgammaComponent, hzero, map_zero]
    obtain ⟨m, hm⟩ :=
      MvPolynomial.support_nonempty.mpr hsourceGamma
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hm
    have hmSupport : m ∈ P.support := (Finset.mem_filter.mp hm).1
    have hmWeight : Finsupp.weight lexWeight m = gamma :=
      (Finset.mem_filter.mp hm).2
    have hminimum := lexicographicMinimumWeight_le weight P hmSupport
    change beta ≤ Finsupp.weight lexWeight m at hminimum
    rw [hmWeight] at hminimum
    exact (not_lt_of_ge hminimum) hlt
  have hminimum : lexicographicMinimumWeight weight (E P) = beta :=
    lexicographicMinimumWeight_eq_of_component_ne_zero
      weight (E P) beta hbound htargetComponent
  change
    E (MvPolynomial.weightedHomogeneousComponent lexWeight beta P) =
      MvPolynomial.weightedHomogeneousComponent lexWeight
        (lexicographicMinimumWeight weight (E P)) (E P)
  rw [hcomponent, hminimum]

/-- The corresponding full initial ideals commute with such an algebra
automorphism. -/
theorem lexicographicInitialIdeal_map_algEquiv_of_preserves
    {R : Type u} {sigma : Type v} [CommRing R] {n : ℕ}
    (weight : sigma → Fin n → ℤ)
    (E : MvPolynomial sigma R ≃ₐ[R] MvPolynomial sigma R)
    (hE : ∀ {P : MvPolynomial sigma R}
        {degree : Lex (Fin n → ℤ)},
      P.IsWeightedHomogeneous (fun i ↦ toLex (weight i)) degree →
        (E P).IsWeightedHomogeneous
          (fun i ↦ toLex (weight i)) degree)
    (I : Ideal (MvPolynomial sigma R)) :
    lexicographicInitialIdeal weight (I.map E.toRingHom) =
      (lexicographicInitialIdeal weight I).map E.toRingHom := by
  apply le_antisymm
  · change Ideal.span
        (lexicographicInitialForm weight ''
          (I.map E.toRingHom : Set (MvPolynomial sigma R))) ≤ _
    apply Ideal.span_le.mpr
    rintro _ ⟨Q, hQ, rfl⟩
    have hpre : E.symm Q ∈ I :=
      (Ideal.symm_apply_mem_of_equiv_iff
        (I := I) (f := E.toRingEquiv) (y := Q)).2 hQ
    have hform :=
      lexicographicInitialForm_algEquiv_of_preserves
        weight E hE (E.symm Q)
    rw [E.apply_symm_apply] at hform
    rw [← hform]
    exact Ideal.mem_map_of_mem E.toRingHom
      (lexicographicInitialForm_mem_initialIdeal weight I hpre)
  · change
      (Ideal.span
        (lexicographicInitialForm weight ''
          (I : Set (MvPolynomial sigma R)))).map E.toRingHom ≤ _
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
    change E (lexicographicInitialForm weight P) ∈ _
    rw [lexicographicInitialForm_algEquiv_of_preserves weight E hE]
    exact lexicographicInitialForm_mem_initialIdeal weight _
      (Ideal.mem_map_of_mem E.toRingHom hP)

/-- Mapping an ideal through a degree-preserving algebra equivalence preserves
homogeneity for the same grading. -/
theorem ideal_map_algEquiv_isHomogeneous_of_preserves
    {R : Type u} {sigma : Type v} {M : Type w}
    [CommRing R] [AddCommMonoid M] [DecidableEq M]
    (weight : sigma → M)
    (E : MvPolynomial sigma R ≃ₐ[R] MvPolynomial sigma R)
    (hE : ∀ {P : MvPolynomial sigma R} {degree : M},
      P.IsWeightedHomogeneous weight degree →
        (E P).IsWeightedHomogeneous weight degree)
    (I : Ideal (MvPolynomial sigma R))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R weight)) :
    (I.map E.toRingHom).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R weight) := by
  let grade := MvPolynomial.weightedHomogeneousSubmodule R weight
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists grade I).mp hI
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
  obtain ⟨degree, hdegree⟩ := P.property
  exact ⟨degree, hE hdegree⟩

/-! ## Reassociation and the homogeneous dehomogenization map -/

variable (R : Type u) [CommRing R]
variable {h : ℕ} (totalD : Fin h → ℕ) (Time : Type v)

/-- Reassociate the homogeneous central index so that `H` is the outer left
summand expected by flat ordinary homogenization. -/
def homogeneousCentralIndexEquiv :
    CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) ≃
      Fin 1 ⊕ CentralPolynomialIndex (Fin h) totalD Time where
  toFun
    | Sum.inl derivative => Sum.inr (Sum.inl derivative)
    | Sum.inr (Sum.inl H) => Sum.inl H
    | Sum.inr (Sum.inr t) => Sum.inr (Sum.inr t)
  invFun
    | Sum.inl H => Sum.inr (Sum.inl H)
    | Sum.inr (Sum.inl derivative) => Sum.inl derivative
    | Sum.inr (Sum.inr t) => Sum.inr (Sum.inr t)
  left_inv := by
    intro x
    rcases x with derivative | (H | t) <;> rfl
  right_inv := by
    intro x
    rcases x with H | (derivative | t) <;> rfl

/-- Polynomial-ring reassociation induced by `homogeneousCentralIndexEquiv`. -/
def homogeneousCentralReassocEquiv :
    CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time) ≃ₐ[R]
      MvPolynomial
        (Fin 1 ⊕ CentralPolynomialIndex (Fin h) totalD Time) R :=
  MvPolynomial.renameEquiv R
    (homogeneousCentralIndexEquiv totalD Time)

/-- Full ordinary homogenization, transported into the central index layout
in which `H` belongs to the retained-variable summand. -/
def homogeneousCentralFullOrdinaryHomogenization
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    Ideal (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)) :=
  (flatFullOrdinaryHomogenization K).map
    (homogeneousCentralReassocEquiv R totalD Time).symm.toRingHom

/-- Set `H = 1`, retaining all derivative and genuine time variables. -/
def homogeneousCentralDehomogenization :
    CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time) →+*
      CentralPolynomial R (Fin h) totalD Time :=
  (ordinaryDehomogenizationHom
    (B := R) (ι := CentralPolynomialIndex (Fin h) totalD Time)).comp
      (homogeneousCentralReassocEquiv R totalD Time).toRingHom

@[simp]
theorem homogeneousCentralDehomogenization_C (r : R) :
    homogeneousCentralDehomogenization R totalD Time (MvPolynomial.C r) =
      MvPolynomial.C r := by
  simp [homogeneousCentralDehomogenization,
    homogeneousCentralReassocEquiv, MvPolynomial.renameEquiv_apply]

@[simp]
theorem homogeneousCentralDehomogenization_X_block
    (b : Fin h) (i : Fin (totalD b)) :
    homogeneousCentralDehomogenization R totalD Time
        (MvPolynomial.X
          (Sum.inl ⟨b, i⟩ :
            CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time))) =
      MvPolynomial.X
        (Sum.inl ⟨b, i⟩ : CentralPolynomialIndex (Fin h) totalD Time) := by
  simp [homogeneousCentralDehomogenization,
    homogeneousCentralReassocEquiv, homogeneousCentralIndexEquiv]

@[simp]
theorem homogeneousCentralDehomogenization_X_H (j : Fin 1) :
    homogeneousCentralDehomogenization R totalD Time
        (MvPolynomial.X
          (Sum.inr (Sum.inl j) :
            CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time))) = 1 := by
  simp [homogeneousCentralDehomogenization,
    homogeneousCentralReassocEquiv, homogeneousCentralIndexEquiv]

@[simp]
theorem homogeneousCentralDehomogenization_X_time (t : Time) :
    homogeneousCentralDehomogenization R totalD Time
        (MvPolynomial.X
          (Sum.inr (Sum.inr t) :
            CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time))) =
      MvPolynomial.X
        (Sum.inr t : CentralPolynomialIndex (Fin h) totalD Time) := by
  simp [homogeneousCentralDehomogenization,
    homogeneousCentralReassocEquiv, homogeneousCentralIndexEquiv]

/-- The transported full homogenization dehomogenizes exactly to its source
ideal. -/
theorem homogeneousCentralFullOrdinaryHomogenization_map_dehomogenization
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    (homogeneousCentralFullOrdinaryHomogenization R totalD Time K).map
        (homogeneousCentralDehomogenization R totalD Time) = K := by
  change
    ((flatFullOrdinaryHomogenization K).map
      (homogeneousCentralReassocEquiv R totalD Time).symm.toRingHom).map
        ((ordinaryDehomogenizationHom
          (B := R) (ι := CentralPolynomialIndex (Fin h) totalD Time)).comp
            (homogeneousCentralReassocEquiv R totalD Time).toRingHom) = K
  rw [Ideal.map_map]
  have hcomp :
      ((ordinaryDehomogenizationHom
        (B := R) (ι := CentralPolynomialIndex (Fin h) totalD Time)).comp
          (homogeneousCentralReassocEquiv R totalD Time).toRingHom).comp
            (homogeneousCentralReassocEquiv R totalD Time).symm.toRingHom =
        ordinaryDehomogenizationHom
          (B := R) (ι := CentralPolynomialIndex (Fin h) totalD Time) := by
    apply RingHom.ext
    intro P
    simp
  rw [hcomp,
    flatFullOrdinaryHomogenization_map_dehomogenization]

/-! ## The homogeneous time shear -/

/-- The distinguished homogenizing variable. -/
def homogeneousCentralH :
    CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time) :=
  MvPolynomial.X
    (Sum.inr (Sum.inl 0) :
      CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time))

/-- Images of variables under the forward homogeneous shear. -/
def homogeneousTimeShearVariable :
    CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) →
      CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)
  | Sum.inl derivative => MvPolynomial.X (Sum.inl derivative)
  | Sum.inr (Sum.inl H) => MvPolynomial.X (Sum.inr (Sum.inl H))
  | Sum.inr (Sum.inr t) =>
      MvPolynomial.X (Sum.inr (Sum.inr t)) +
        homogeneousCentralH R totalD Time

/-- Images of variables under the inverse homogeneous shear. -/
def homogeneousTimeShearInverseVariable :
    CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) →
      CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)
  | Sum.inl derivative => MvPolynomial.X (Sum.inl derivative)
  | Sum.inr (Sum.inl H) => MvPolynomial.X (Sum.inr (Sum.inl H))
  | Sum.inr (Sum.inr t) =>
      MvPolynomial.X (Sum.inr (Sum.inr t)) -
        homogeneousCentralH R totalD Time

def homogeneousTimeShearForwardHom :
    CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time) →ₐ[R]
      CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time) :=
  MvPolynomial.aeval (homogeneousTimeShearVariable R totalD Time)

def homogeneousTimeShearInverseHom :
    CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time) →ₐ[R]
      CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time) :=
  MvPolynomial.aeval (homogeneousTimeShearInverseVariable R totalD Time)

/-- The homogeneous shear fixes derivatives and `H` and sends `t` to
`t + H`. -/
def homogeneousTimeShear :
    CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time) ≃ₐ[R]
      CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time) :=
  AlgEquiv.ofAlgHom
    (homogeneousTimeShearForwardHom R totalD Time)
    (homogeneousTimeShearInverseHom R totalD Time)
    (by
      apply MvPolynomial.algHom_ext
      intro x
      rcases x with derivative | (H | t)
      · simp [homogeneousTimeShearForwardHom,
          homogeneousTimeShearInverseHom,
          homogeneousTimeShearVariable,
          homogeneousTimeShearInverseVariable]
      · simp [homogeneousTimeShearForwardHom,
          homogeneousTimeShearInverseHom,
          homogeneousTimeShearVariable,
          homogeneousTimeShearInverseVariable,
          homogeneousCentralH]
      · simp [homogeneousTimeShearForwardHom,
          homogeneousTimeShearInverseHom,
          homogeneousTimeShearVariable,
          homogeneousTimeShearInverseVariable,
          homogeneousCentralH])
    (by
      apply MvPolynomial.algHom_ext
      intro x
      rcases x with derivative | (H | t)
      · simp [homogeneousTimeShearForwardHom,
          homogeneousTimeShearInverseHom,
          homogeneousTimeShearVariable,
          homogeneousTimeShearInverseVariable]
      · simp [homogeneousTimeShearForwardHom,
          homogeneousTimeShearInverseHom,
          homogeneousTimeShearVariable,
          homogeneousTimeShearInverseVariable,
          homogeneousCentralH]
      · simp [homogeneousTimeShearForwardHom,
          homogeneousTimeShearInverseHom,
          homogeneousTimeShearVariable,
          homogeneousTimeShearInverseVariable,
          homogeneousCentralH])

@[simp]
theorem homogeneousTimeShear_C (r : R) :
    homogeneousTimeShear R totalD Time (MvPolynomial.C r) =
      MvPolynomial.C r := by
  simp [homogeneousTimeShear, homogeneousTimeShearForwardHom]

@[simp]
theorem homogeneousTimeShear_X_block
    (b : Fin h) (i : Fin (totalD b)) :
    homogeneousTimeShear R totalD Time
        (MvPolynomial.X
          (Sum.inl ⟨b, i⟩ :
            CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time))) =
      MvPolynomial.X
        (Sum.inl ⟨b, i⟩ :
          CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time)) := by
  exact MvPolynomial.aeval_X _ _

@[simp]
theorem homogeneousTimeShear_X_H (j : Fin 1) :
    homogeneousTimeShear R totalD Time
        (MvPolynomial.X
          (Sum.inr (Sum.inl j) :
            CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time))) =
      MvPolynomial.X
        (Sum.inr (Sum.inl j) :
          CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time)) := by
  exact MvPolynomial.aeval_X _ _

@[simp]
theorem homogeneousTimeShear_X_time (t : Time) :
    homogeneousTimeShear R totalD Time
        (MvPolynomial.X
          (Sum.inr (Sum.inr t) :
            CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time))) =
      MvPolynomial.X
          (Sum.inr (Sum.inr t) :
            CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time)) +
        homogeneousCentralH R totalD Time := by
  exact MvPolynomial.aeval_X _ _

/-! ## Homogeneity, components, and commutation -/

/-- The homogeneous shear preserves ordinary total degree. -/
theorem homogeneousTimeShear_preserves_ordinaryHomogeneous
    {P : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)}
    {degree : ℕ}
    (hP : P.IsWeightedHomogeneous (fun _ ↦ (1 : ℕ)) degree) :
    (homogeneousTimeShear R totalD Time P).IsWeightedHomogeneous
      (fun _ ↦ (1 : ℕ)) degree := by
  change
    (MvPolynomial.aeval
      (homogeneousTimeShearVariable R totalD Time) P).IsWeightedHomogeneous
        (fun _ ↦ (1 : ℕ)) degree
  apply weightedHomogeneous_aeval hP
  intro x
  rcases x with derivative | (H | t)
  · simpa [homogeneousTimeShearVariable] using
      (MvPolynomial.isWeightedHomogeneous_X R
        (fun _ : CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) ↦
          (1 : ℕ)) (Sum.inl derivative))
  · simpa [homogeneousTimeShearVariable] using
      (MvPolynomial.isWeightedHomogeneous_X R
        (fun _ : CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) ↦
          (1 : ℕ)) (Sum.inr (Sum.inl H)))
  · simpa [homogeneousTimeShearVariable, homogeneousCentralH] using
      (MvPolynomial.isWeightedHomogeneous_X R
        (fun _ : CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) ↦
          (1 : ℕ)) (Sum.inr (Sum.inr t))).add
        (MvPolynomial.isWeightedHomogeneous_X R
          (fun _ : CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) ↦
            (1 : ℕ)) (Sum.inr (Sum.inl (0 : Fin 1))))

/-- The homogeneous shear preserves the genuine terminal multidegree. -/
theorem homogeneousTimeShear_preserves_terminalHomogeneous
    {P : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)}
    {degree : TerminalMultidegree (Fin h)}
    (hP : P.IsWeightedHomogeneous
      (terminalGlobalWeight (Fin h) totalD (Fin 1 ⊕ Time)) degree) :
    (homogeneousTimeShear R totalD Time P).IsWeightedHomogeneous
      (terminalGlobalWeight (Fin h) totalD (Fin 1 ⊕ Time)) degree := by
  change
    (MvPolynomial.aeval
      (homogeneousTimeShearVariable R totalD Time) P).IsWeightedHomogeneous
          (terminalGlobalWeight (Fin h) totalD (Fin 1 ⊕ Time)) degree
  apply weightedHomogeneous_aeval hP
  intro x
  rcases x with derivative | (H | t)
  · simpa [homogeneousTimeShearVariable] using
      (MvPolynomial.isWeightedHomogeneous_X R
        (terminalGlobalWeight (Fin h) totalD (Fin 1 ⊕ Time))
        (Sum.inl derivative))
  · simpa [homogeneousTimeShearVariable] using
      (MvPolynomial.isWeightedHomogeneous_X R
        (terminalGlobalWeight (Fin h) totalD (Fin 1 ⊕ Time))
        (Sum.inr (Sum.inl H)))
  · simpa [homogeneousTimeShearVariable, homogeneousCentralH] using
      (MvPolynomial.isWeightedHomogeneous_X R
        (terminalGlobalWeight (Fin h) totalD (Fin 1 ⊕ Time))
        (Sum.inr (Sum.inr t))).add
        (MvPolynomial.isWeightedHomogeneous_X R
          (terminalGlobalWeight (Fin h) totalD (Fin 1 ⊕ Time))
          (Sum.inr (Sum.inl (0 : Fin 1))))

/-- The same preservation statement after casting terminal multidegrees to
the signed lexicographic grading used by `lexicographicInitialIdeal`. -/
theorem homogeneousTimeShear_preserves_signedTerminalHomogeneous
    {P : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)}
    {degree : Lex (Fin h → ℤ)}
    (hP : P.IsWeightedHomogeneous
      (fun x ↦ toLex
        (signedTerminalWeight totalD (Fin 1 ⊕ Time) x)) degree) :
    (homogeneousTimeShear R totalD Time P).IsWeightedHomogeneous
      (fun x ↦ toLex
        (signedTerminalWeight totalD (Fin 1 ⊕ Time) x)) degree := by
  change
    (MvPolynomial.aeval
      (homogeneousTimeShearVariable R totalD Time) P).IsWeightedHomogeneous
          (fun x ↦ toLex
            (signedTerminalWeight totalD (Fin 1 ⊕ Time) x)) degree
  apply weightedHomogeneous_aeval hP
  intro x
  rcases x with derivative | (H | t)
  · simpa [homogeneousTimeShearVariable] using
      (MvPolynomial.isWeightedHomogeneous_X R
        (fun x ↦ toLex
          (signedTerminalWeight totalD (Fin 1 ⊕ Time) x))
        (Sum.inl derivative))
  · simpa [homogeneousTimeShearVariable, signedTerminalWeight] using
      (MvPolynomial.isWeightedHomogeneous_X R
        (fun x ↦ toLex
          (signedTerminalWeight totalD (Fin 1 ⊕ Time) x))
        (Sum.inr (Sum.inl H)))
  · simpa [homogeneousTimeShearVariable, homogeneousCentralH,
        signedTerminalWeight] using
      (MvPolynomial.isWeightedHomogeneous_X R
        (fun x ↦ toLex
          (signedTerminalWeight totalD (Fin 1 ⊕ Time) x))
        (Sum.inr (Sum.inr t))).add
        (MvPolynomial.isWeightedHomogeneous_X R
          (fun x ↦ toLex
            (signedTerminalWeight totalD (Fin 1 ⊕ Time) x))
          (Sum.inr (Sum.inl (0 : Fin 1))))

/-- The shear commutes with every actual terminal component. -/
theorem homogeneousTimeShear_terminalGlobalComponent
    (degree : TerminalMultidegree (Fin h))
    (P : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)) :
    homogeneousTimeShear R totalD Time
        (terminalGlobalComponent R (Fin h) totalD (Fin 1 ⊕ Time)
          degree P) =
      terminalGlobalComponent R (Fin h) totalD (Fin 1 ⊕ Time)
        degree (homogeneousTimeShear R totalD Time P) := by
  exact weightedHomogeneousComponent_algEquiv_of_preserves
    (terminalGlobalWeight (Fin h) totalD (Fin 1 ⊕ Time))
    (homogeneousTimeShear R totalD Time)
    (fun hP ↦
      homogeneousTimeShear_preserves_terminalHomogeneous
        R totalD Time hP)
    degree P

/-- Consequently, the shear commutes with the full terminal initial ideal. -/
theorem lexicographicInitialIdeal_map_homogeneousTimeShear
    (I : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))) :
    lexicographicInitialIdeal
        (signedTerminalWeight totalD (Fin 1 ⊕ Time))
        (I.map (homogeneousTimeShear R totalD Time).toRingHom) =
      (lexicographicInitialIdeal
        (signedTerminalWeight totalD (Fin 1 ⊕ Time)) I).map
          (homogeneousTimeShear R totalD Time).toRingHom := by
  exact lexicographicInitialIdeal_map_algEquiv_of_preserves
    (signedTerminalWeight totalD (Fin 1 ⊕ Time))
    (homogeneousTimeShear R totalD Time)
    (fun hP ↦
      homogeneousTimeShear_preserves_signedTerminalHomogeneous
        R totalD Time hP) I

/-- The homogeneous shear and the terminal signed-Stirling automorphism
commute as ring homomorphisms. -/
theorem homogeneousTimeShear_commutes_terminalGlobalStirling :
    (homogeneousTimeShear R totalD Time).toRingHom.comp
        (terminalGlobalStirlingEquiv R (Fin h) totalD
          (Fin 1 ⊕ Time)).toRingHom =
      (terminalGlobalStirlingEquiv R (Fin h) totalD
        (Fin 1 ⊕ Time)).toRingHom.comp
          (homogeneousTimeShear R totalD Time).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro x
    rcases x with ⟨b, i⟩ | (H | t)
    · simp
    · simp
    · simp [homogeneousCentralH]

/-- Ideal-level form of commutation between the shear and terminal
Stirling. -/
theorem ideal_map_homogeneousTimeShear_terminalGlobalStirling_commute
    (I : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))) :
    (I.map (homogeneousTimeShear R totalD Time).toRingHom).map
        (terminalGlobalStirlingEquiv R (Fin h) totalD
          (Fin 1 ⊕ Time)).toRingHom =
      (I.map (terminalGlobalStirlingEquiv R (Fin h) totalD
        (Fin 1 ⊕ Time)).toRingHom).map
          (homogeneousTimeShear R totalD Time).toRingHom := by
  rw [Ideal.map_map, Ideal.map_map,
    homogeneousTimeShear_commutes_terminalGlobalStirling]

/-- The homogeneous shear preserves ordinary homogeneous ideals. -/
theorem homogeneousTimeShear_map_isOrdinaryHomogeneous
    (I : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ)))) :
    (I.map (homogeneousTimeShear R totalD Time).toRingHom).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ))) := by
  exact ideal_map_algEquiv_isHomogeneous_of_preserves
    (fun _ : CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) ↦
      (1 : ℕ))
    (homogeneousTimeShear R totalD Time)
    (fun hP ↦
      homogeneousTimeShear_preserves_ordinaryHomogeneous
        R totalD Time hP) I hI

/-- The global terminal Stirling map preserves ordinary homogeneous ideals. -/
theorem terminalGlobalStirlingEquiv_map_isOrdinaryHomogeneous
    (I : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ)))) :
    (I.map (terminalGlobalStirlingEquiv R (Fin h) totalD
      (Fin 1 ⊕ Time)).toRingHom).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ))) := by
  apply ideal_map_algEquiv_isHomogeneous_of_preserves
    (fun _ : CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) ↦
      (1 : ℕ))
    (terminalGlobalStirlingEquiv R (Fin h) totalD (Fin 1 ⊕ Time))
    _ I hI
  intro P degree hP
  change P.IsHomogeneous degree at hP
  change
    (terminalGlobalStirlingEquiv R (Fin h) totalD
      (Fin 1 ⊕ Time) P).IsHomogeneous degree
  exact terminalGlobalStirlingEquiv_isHomogeneous
    (R := R) totalD (Fin 1 ⊕ Time) hP

/-- The transported full ordinary homogenization is homogeneous in the
central variable layout. -/
theorem homogeneousCentralFullOrdinaryHomogenization_isHomogeneous
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    (homogeneousCentralFullOrdinaryHomogenization R totalD Time K).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule R
          (fun _ ↦ (1 : ℕ))) := by
  let sourceGrade := MvPolynomial.weightedHomogeneousSubmodule R
    (fun _ : Fin 1 ⊕ CentralPolynomialIndex (Fin h) totalD Time ↦
      (1 : ℕ))
  have hflat := flatFullOrdinaryHomogenization_isHomogeneous K
  obtain ⟨S, hS⟩ :=
    (Ideal.IsHomogeneous.iff_exists sourceGrade
      (flatFullOrdinaryHomogenization K)).mp hflat
  change
    ((flatFullOrdinaryHomogenization K).map
      (homogeneousCentralReassocEquiv R totalD Time).symm.toRingHom).IsHomogeneous _
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨_, ⟨P, hP, rfl⟩, rfl⟩
  obtain ⟨degree, hdegree⟩ := P.property
  refine ⟨degree, ?_⟩
  change
    (P : MvPolynomial
      (Fin 1 ⊕ CentralPolynomialIndex (Fin h) totalD Time) R).IsHomogeneous
        degree at hdegree
  change
    ((homogeneousCentralReassocEquiv R totalD Time).symm P).IsHomogeneous degree
  change
    (MvPolynomial.rename
      (homogeneousCentralIndexEquiv totalD Time).symm
      (P : MvPolynomial
        (Fin 1 ⊕ CentralPolynomialIndex (Fin h) totalD Time) R)).IsHomogeneous
          degree
  exact hdegree.rename_isHomogeneous

/-! ## Dehomogenization and the central automorphism -/

/-- Translation by one on every genuine time variable, fixing all derivative
variables. -/
def centralTimeTranslationByOne :
    CentralPolynomial R (Fin h) totalD Time ≃ₐ[R]
      CentralPolynomial R (Fin h) totalD Time :=
  polynomialCoordinateTranslation
    (Sum.elim
      (fun _ : (Σ b : Fin h, Fin (totalD b)) ↦ (0 : R))
      (fun _ : Time ↦ (1 : R)))

@[simp]
theorem centralTimeTranslationByOne_X_block
    (b : Fin h) (i : Fin (totalD b)) :
    centralTimeTranslationByOne R totalD Time
        (MvPolynomial.X
          (Sum.inl ⟨b, i⟩ : CentralPolynomialIndex (Fin h) totalD Time)) =
      MvPolynomial.X
        (Sum.inl ⟨b, i⟩ : CentralPolynomialIndex (Fin h) totalD Time) := by
  simp [centralTimeTranslationByOne]

@[simp]
theorem centralTimeTranslationByOne_X_time (t : Time) :
    centralTimeTranslationByOne R totalD Time
        (MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex (Fin h) totalD Time)) =
      MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex (Fin h) totalD Time) + 1 := by
  simp [centralTimeTranslationByOne]

/-- After `H = 1`, the homogeneous shear is ordinary translation by one. -/
theorem homogeneousCentralDehomogenization_comp_homogeneousTimeShear :
    (homogeneousCentralDehomogenization R totalD Time).comp
        (homogeneousTimeShear R totalD Time).toRingHom =
      (centralTimeTranslationByOne R totalD Time).toRingHom.comp
        (homogeneousCentralDehomogenization R totalD Time) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [centralTimeTranslationByOne,
      polynomialCoordinateTranslation_C]
  · intro x
    rcases x with ⟨b, i⟩ | (H | t)
    · simp
    · simp
    · simp [homogeneousCentralH]

/-- Dehomogenization commutes with the terminal Stirling automorphism, which
fixes `H` and all time variables. -/
theorem homogeneousCentralDehomogenization_comp_terminalGlobalStirling :
    (homogeneousCentralDehomogenization R totalD Time).comp
        (terminalGlobalStirlingEquiv R (Fin h) totalD
          (Fin 1 ⊕ Time)).toRingHom =
      (terminalGlobalStirlingEquiv R (Fin h) totalD Time).toRingHom.comp
        (homogeneousCentralDehomogenization R totalD Time) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro x
    rcases x with ⟨b, i⟩ | (H | t)
    · simp
    · simp
    · simp

/-- Translation by one after terminal Stirling is exactly `centralPolynomialPhi`. -/
theorem centralTimeTranslationByOne_comp_terminalGlobalStirling :
    (centralTimeTranslationByOne R totalD Time).toRingHom.comp
        (terminalGlobalStirlingEquiv R (Fin h) totalD Time).toRingHom =
      (centralPolynomialPhi R (Fin h) totalD Time).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [centralTimeTranslationByOne,
      polynomialCoordinateTranslation_C]
  · intro x
    rcases x with ⟨b, i⟩ | t
    · simp [centralTimeTranslationByOne,
        polynomialCoordinateTranslation_C]
    · simp

/-- Combined pointwise compatibility: dehomogenizing the homogeneous
`shear ∘ Stirling` action is the central automorphism `Phi`. -/
theorem homogeneousCentralDehomogenization_comp_shear_stirling :
    (homogeneousCentralDehomogenization R totalD Time).comp
        ((homogeneousTimeShear R totalD Time).toRingHom.comp
          (terminalGlobalStirlingEquiv R (Fin h) totalD
            (Fin 1 ⊕ Time)).toRingHom) =
      (centralPolynomialPhi R (Fin h) totalD Time).toRingHom.comp
        (homogeneousCentralDehomogenization R totalD Time) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro x
    rcases x with ⟨b, i⟩ | (H | t)
    · simp
    · simp
    · simp [homogeneousCentralH]

/-! ## One homogeneous step and its exact iteration -/

/-- The retained-ring version of one central step.  By
`centralIdealConstruction_unusedExtension`, this is exactly the full central
construction after adjoining the unused representative variables. -/
def retainedCentralStep
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    Ideal (CentralPolynomial R (Fin h) totalD Time) :=
  (lexicographicInitialIdeal (signedTerminalWeight totalD Time) K).map
    (centralPolynomialPhi R (Fin h) totalD Time).toRingHom

theorem retainedCentralStep_eq_centralIdealConstruction_unusedExtension
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    retainedCentralStep R totalD Time K =
      centralIdealConstruction
        (negativeTerminalWeight totalD Time)
        (unusedRepresentativeExtension R totalD Time K) := by
  simpa [retainedCentralStep] using
    (centralIdealConstruction_unusedExtension R totalD Time K).symm

/-- One homogeneous central step: take the terminal initial ideal, apply
terminal Stirling, then apply the homogeneous time shear. -/
def homogeneousCentralStep
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))) :
    Ideal (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)) :=
  ((lexicographicInitialIdeal
      (signedTerminalWeight totalD (Fin 1 ⊕ Time)) K).map
        (terminalGlobalStirlingEquiv R (Fin h) totalD
          (Fin 1 ⊕ Time)).toRingHom).map
    (homogeneousTimeShear R totalD Time).toRingHom

/-- One homogeneous step preserves ordinary homogeneity. -/
theorem homogeneousCentralStep_isOrdinaryHomogeneous
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ)))) :
    (homogeneousCentralStep R totalD Time K).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ))) := by
  apply homogeneousTimeShear_map_isOrdinaryHomogeneous R totalD Time
  apply terminalGlobalStirlingEquiv_map_isOrdinaryHomogeneous R totalD Time
  exact lexicographicInitialIdeal_isOrdinaryHomogeneous
    (fun _ : CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) ↦
      (1 : ℕ))
    (signedTerminalWeight totalD (Fin 1 ⊕ Time)) K hK

/-- Every iterate of the homogeneous central step remains ordinarily
homogeneous. -/
theorem homogeneousCentralStep_iterate_isOrdinaryHomogeneous
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ)))) :
    ∀ j : ℕ,
      ((homogeneousCentralStep R totalD Time)^[j] K).IsHomogeneous
        (MvPolynomial.weightedHomogeneousSubmodule R
          (fun _ ↦ (1 : ℕ))) := by
  intro j
  induction j with
  | zero => exact hK
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact homogeneousCentralStep_isOrdinaryHomogeneous
        R totalD Time _ ih

/-- Ideal map induced by the homogeneous shear. -/
def homogeneousTimeShearIdeal
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))) :
    Ideal (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)) :=
  K.map (homogeneousTimeShear R totalD Time).toRingHom

/-- The auxiliary initial-ideal sequence
`I_0 = in(K)`, `I_(j+1) = in(J(I_j))`.  This is the variable-type-generic
version of `lexicographicInitialIdealIteration`. -/
def homogeneousTerminalInitialIteration
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))) :
    ℕ → Ideal (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))
  | 0 => lexicographicInitialIdeal
      (signedTerminalWeight totalD (Fin 1 ⊕ Time)) K
  | j + 1 =>
      lexicographicInitialIdeal
        (signedTerminalWeight totalD (Fin 1 ⊕ Time))
        ((homogeneousTerminalInitialIteration K j).map
          (terminalGlobalStirlingEquiv R (Fin h) totalD
            (Fin 1 ⊕ Time)).toRingHom)

@[simp]
theorem homogeneousTerminalInitialIteration_zero
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))) :
    homogeneousTerminalInitialIteration R totalD Time K 0 =
      lexicographicInitialIdeal
        (signedTerminalWeight totalD (Fin 1 ⊕ Time)) K :=
  rfl

@[simp]
theorem homogeneousTerminalInitialIteration_succ
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))) (j : ℕ) :
    homogeneousTerminalInitialIteration R totalD Time K (j + 1) =
      lexicographicInitialIdeal
        (signedTerminalWeight totalD (Fin 1 ⊕ Time))
        ((homogeneousTerminalInitialIteration R totalD Time K j).map
          (terminalGlobalStirlingEquiv R (Fin h) totalD
            (Fin 1 ⊕ Time)).toRingHom) :=
  rfl

/-- A homogeneous central step commutes with a further homogeneous shear. -/
theorem homogeneousCentralStep_commutes_homogeneousTimeShearIdeal :
    Function.Commute
      (homogeneousCentralStep R totalD Time)
      (homogeneousTimeShearIdeal R totalD Time) := by
  intro I
  change
    (((lexicographicInitialIdeal
      (signedTerminalWeight totalD (Fin 1 ⊕ Time))
      (I.map (homogeneousTimeShear R totalD Time).toRingHom)).map
        (terminalGlobalStirlingEquiv R (Fin h) totalD
          (Fin 1 ⊕ Time)).toRingHom).map
      (homogeneousTimeShear R totalD Time).toRingHom) = _
  rw [lexicographicInitialIdeal_map_homogeneousTimeShear]
  rw [ideal_map_homogeneousTimeShear_terminalGlobalStirling_commute]
  rfl

/-- Exact homogeneous iterate identity.  After `j+1` central steps, the
auxiliary ideal `I_j` is mapped once by terminal Stirling and `j+1` times by
the homogeneous shear. -/
theorem homogeneousCentralStep_iterate_eq
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))) (j : ℕ) :
    (homogeneousCentralStep R totalD Time)^[j + 1] K =
      (homogeneousTimeShearIdeal R totalD Time)^[j + 1]
        ((homogeneousTerminalInitialIteration R totalD Time K j).map
          (terminalGlobalStirlingEquiv R (Fin h) totalD
            (Fin 1 ⊕ Time)).toRingHom) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      let F := homogeneousCentralStep R totalD Time
      let T := homogeneousTimeShearIdeal R totalD Time
      let J := terminalGlobalStirlingEquiv R (Fin h) totalD
        (Fin 1 ⊕ Time)
      have hcommute : Function.Commute F T :=
        homogeneousCentralStep_commutes_homogeneousTimeShearIdeal
          R totalD Time
      calc
        F^[Nat.succ j + 1] K = F (F^[j + 1] K) := by
          rw [show Nat.succ j + 1 = Nat.succ (j + 1) by omega]
          exact Function.iterate_succ_apply' F (j + 1) K
        _ = F
            (T^[j + 1]
              ((homogeneousTerminalInitialIteration
                R totalD Time K j).map J.toRingHom)) := by
          rw [ih]
        _ = T^[j + 1]
            (F ((homogeneousTerminalInitialIteration
              R totalD Time K j).map J.toRingHom)) :=
          (hcommute.iterate_right (j + 1)).eq _
        _ = T^[j + 1]
            (T ((homogeneousTerminalInitialIteration
              R totalD Time K (j + 1)).map J.toRingHom)) := by
          rfl
        _ = T^[Nat.succ j + 1]
            ((homogeneousTerminalInitialIteration
              R totalD Time K (Nat.succ j)).map J.toRingHom) := by
          exact (Function.iterate_succ_apply T (j + 1) _).symm

/-! ## Exact dehomogenized step and the remaining bridge -/

/-- Map an ideal through `H = 1`. -/
def homogeneousCentralDehomogenizeIdeal
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))) :
    Ideal (CentralPolynomial R (Fin h) totalD Time) :=
  K.map (homogeneousCentralDehomogenization R totalD Time)

/-- Exact one-step identity before commuting initial formation with
dehomogenization. -/
theorem homogeneousCentralStep_map_dehomogenization
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))) :
    homogeneousCentralDehomogenizeIdeal R totalD Time
        (homogeneousCentralStep R totalD Time K) =
      ((lexicographicInitialIdeal
        (signedTerminalWeight totalD (Fin 1 ⊕ Time)) K).map
          (homogeneousCentralDehomogenization R totalD Time)).map
        (centralPolynomialPhi R (Fin h) totalD Time).toRingHom := by
  change
    ((((lexicographicInitialIdeal
      (signedTerminalWeight totalD (Fin 1 ⊕ Time)) K).map
        (terminalGlobalStirlingEquiv R (Fin h) totalD
          (Fin 1 ⊕ Time)).toRingHom).map
      (homogeneousTimeShear R totalD Time).toRingHom).map
        (homogeneousCentralDehomogenization R totalD Time)) = _
  repeat' rw [Ideal.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro x
    rcases x with ⟨b, i⟩ | (H | t)
    · simp
    · simp
    · simp [homogeneousCentralH]

/-- The precise remaining algebraic bridge for an ideal: terminal initial
formation commutes with evaluation at `H = 1`. -/
def TerminalInitialDehomogenizationCompatible
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))) : Prop :=
  (lexicographicInitialIdeal
      (signedTerminalWeight totalD (Fin 1 ⊕ Time)) K).map
        (homogeneousCentralDehomogenization R totalD Time) =
    lexicographicInitialIdeal (signedTerminalWeight totalD Time)
      (homogeneousCentralDehomogenizeIdeal R totalD Time K)

/-- Under exactly that bridge, one homogeneous step dehomogenizes to the
retained central step. -/
theorem homogeneousCentralStep_dehomogenizes_to_retainedCentralStep
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hcompat : TerminalInitialDehomogenizationCompatible
      R totalD Time K) :
    homogeneousCentralDehomogenizeIdeal R totalD Time
        (homogeneousCentralStep R totalD Time K) =
      retainedCentralStep R totalD Time
        (homogeneousCentralDehomogenizeIdeal R totalD Time K) := by
  rw [homogeneousCentralStep_map_dehomogenization]
  rw [hcompat]
  rfl

/-- Thus the dehomogenized homogeneous step is literally the full central
construction on the corresponding unused representative extension. -/
theorem homogeneousCentralStep_dehomogenizes_to_centralIdealConstruction
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hcompat : TerminalInitialDehomogenizationCompatible
      R totalD Time K) :
    homogeneousCentralDehomogenizeIdeal R totalD Time
        (homogeneousCentralStep R totalD Time K) =
      centralIdealConstruction
        (negativeTerminalWeight totalD Time)
        (unusedRepresentativeExtension R totalD Time
          (homogeneousCentralDehomogenizeIdeal R totalD Time K)) := by
  rw [homogeneousCentralStep_dehomogenizes_to_retainedCentralStep
    R totalD Time K hcompat]
  exact retainedCentralStep_eq_centralIdealConstruction_unusedExtension
    R totalD Time _

/-- If the displayed initial/dehomogenization bridge holds for every ideal,
dehomogenization semiconjugates the homogeneous and retained central steps. -/
theorem homogeneousCentralDehomogenization_semiconj
    (hcompat : ∀ K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)),
      TerminalInitialDehomogenizationCompatible R totalD Time K) :
    Function.Semiconj
      (homogeneousCentralDehomogenizeIdeal R totalD Time)
      (homogeneousCentralStep R totalD Time)
      (retainedCentralStep R totalD Time) := by
  intro K
  exact homogeneousCentralStep_dehomogenizes_to_retainedCentralStep
    R totalD Time K (hcompat K)

/-- Exact iterated central-step identity under the same single, explicit
bridge. -/
theorem homogeneousCentralStep_iterate_map_dehomogenization
    (hcompat : ∀ K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)),
      TerminalInitialDehomogenizationCompatible R totalD Time K)
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))) (j : ℕ) :
    homogeneousCentralDehomogenizeIdeal R totalD Time
        ((homogeneousCentralStep R totalD Time)^[j] K) =
      (retainedCentralStep R totalD Time)^[j]
        (homogeneousCentralDehomogenizeIdeal R totalD Time K) := by
  exact Function.Semiconj.iterate_right
    (homogeneousCentralDehomogenization_semiconj
      R totalD Time hcompat) j K

end AbelFormalization
