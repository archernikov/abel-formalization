import AbelFormalization.HomogeneousCentralIteration
import AbelFormalization.LexicographicInitialIdealPrincipalQuotient
import AbelFormalization.WeightedGroupEvaluation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Terminal initial ideals and ordinary dehomogenization

This module proves the compatibility hypothesis isolated by
`HomogeneousCentralIteration`.  If an ideal in the homogeneous central ring
is homogeneous for ordinary total degree, then setting `H = 1` commutes with
the full terminal lexicographic initial ideal.

The essential point is that dehomogenization is injective on each fixed
ordinary degree.  We prove this through the existing Laurent rescaling.  A
homogeneous ideal then supplies a homogeneous preimage for every element of
its dehomogenized image: decompose any preimage by ordinary degree and raise
each component to one common degree by a power of `H`.
-/

noncomputable section

namespace AbelFormalization

universe u v w z

open scoped BigOperators

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## A component lemma for homomorphisms between different polynomial rings -/

/-- An additive ring homomorphism which preserves every weighted homogeneous
degree commutes with weighted homogeneous components. -/
theorem weightedHomogeneousComponent_ringHom_of_preserves
    {R : Type u} {S : Type v} {sigma : Type w} {tau : Type z}
    {M : Type*}
    [CommRing R] [CommRing S] [AddCommMonoid M] [DecidableEq M]
    (sourceWeight : sigma → M) (targetWeight : tau → M)
    (F : MvPolynomial sigma R →+* MvPolynomial tau S)
    (hF : ∀ {P : MvPolynomial sigma R} {degree : M},
      P.IsWeightedHomogeneous sourceWeight degree →
        (F P).IsWeightedHomogeneous targetWeight degree)
    (degree : M) (P : MvPolynomial sigma R) :
    F (MvPolynomial.weightedHomogeneousComponent sourceWeight degree P) =
      MvPolynomial.weightedHomogeneousComponent targetWeight degree (F P) := by
  classical
  have hsum :
      (∑ other ∈ P.support.image (Finsupp.weight sourceWeight),
        MvPolynomial.weightedHomogeneousComponent sourceWeight other P) = P :=
    sum_weightedHomogeneousComponent_support sourceWeight P
  calc
    F (MvPolynomial.weightedHomogeneousComponent sourceWeight degree P) =
        F (MvPolynomial.weightedHomogeneousComponent sourceWeight degree
          (∑ other ∈ P.support.image (Finsupp.weight sourceWeight),
            MvPolynomial.weightedHomogeneousComponent
              sourceWeight other P)) := by
      rw [hsum]
    _ = MvPolynomial.weightedHomogeneousComponent targetWeight degree
        (F (∑ other ∈ P.support.image (Finsupp.weight sourceWeight),
          MvPolynomial.weightedHomogeneousComponent
            sourceWeight other P)) := by
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro other hother
      have hsource :
          (MvPolynomial.weightedHomogeneousComponent sourceWeight other P).IsWeightedHomogeneous
            sourceWeight other :=
        MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous other P
      have htarget := hF hsource
      by_cases hdegree : degree = other
      · subst other
        rw [hsource.weightedHomogeneousComponent_same,
          htarget.weightedHomogeneousComponent_same]
      · rw [hsource.weightedHomogeneousComponent_ne degree hdegree,
          map_zero, htarget.weightedHomogeneousComponent_ne degree hdegree]
    _ = MvPolynomial.weightedHomogeneousComponent targetWeight degree (F P) := by
      rw [hsum]

/-! ## Fixed-degree injectivity of ordinary dehomogenization -/

variable {B ι : Type*} [CommRing B]

/-- The ordinary Laurent-rescaled inclusion is injective. -/
theorem ordinaryCentralLaurentRescaledMap_injective :
    Function.Injective
      (centralLaurentRescaledMap (R := B)
        (ordinaryLaurentRescalingWeight (ι := ι))) := by
  intro P Q hPQ
  change
    groupLaurentWeightRescaling
        (ordinaryLaurentRescalingWeight (ι := ι))
        (finiteLaurentPolynomialHom (MvPolynomial ι B) 1
          (MvPolynomial.sumAlgEquiv B (Fin 1) ι P)) =
      groupLaurentWeightRescaling
        (ordinaryLaurentRescalingWeight (ι := ι))
        (finiteLaurentPolynomialHom (MvPolynomial ι B) 1
          (MvPolynomial.sumAlgEquiv B (Fin 1) ι Q)) at hPQ
  apply (MvPolynomial.sumAlgEquiv B (Fin 1) ι).injective
  apply finiteLaurentPolynomialHom_injective (MvPolynomial ι B) 1
  exact (groupLaurentWeightRescaling
    (R := B) (ordinaryLaurentRescalingWeight (ι := ι))).injective hPQ

/-- Evaluation at `H = 1` is injective on polynomials of one fixed ordinary
homogeneous degree. -/
theorem ordinaryDehomogenizationHom_injective_on_homogeneous_degree
    {P Q : MvPolynomial (Fin 1 ⊕ ι) B} {degree : ℕ}
    (hP : P.IsWeightedHomogeneous (fun _ ↦ (1 : ℕ)) degree)
    (hQ : Q.IsWeightedHomogeneous (fun _ ↦ (1 : ℕ)) degree)
    (hPQ : ordinaryDehomogenizationHom (B := B) (ι := ι) P =
      ordinaryDehomogenizationHom (B := B) (ι := ι) Q) :
    P = Q := by
  let D := ordinaryDehomogenizationHom (B := B) (ι := ι)
  let L := centralLaurentRescaledMap (R := B)
    (ordinaryLaurentRescalingWeight (ι := ι))
  have hsub : (P - Q).IsWeightedHomogeneous
      (fun _ ↦ (1 : ℕ)) degree := hP.sub hQ
  have hsubLaurent :=
    isWeightedHomogeneous_ordinaryLaurentTotalWeight hsub
  have hformula :
      L (P - Q) =
        AddMonoidAlgebra.single (fun _ : Fin 1 ↦ (degree : ℤ))
          (D (P - Q)) := by
    change
      centralLaurentRescaledMap
          (ordinaryLaurentRescalingWeight (ι := ι)) (P - Q) = _
    rw [centralLaurentRescaledMap_eq_evaluation,
      centralLaurentWeight_one_neg]
    simpa [D, ordinaryDehomogenizationHom] using
      (weightedGroupEvaluation_of_homogeneous
        (MvPolynomial.C : B →+* MvPolynomial ι B)
        (Sum.elim
          (fun _ : Fin 1 ↦ (1 : MvPolynomial ι B)) MvPolynomial.X)
        (ordinaryLaurentTotalWeight (ι := ι)) hsubLaurent)
  have hDzero : D (P - Q) = 0 := by
    change
      ordinaryDehomogenizationHom (B := B) (ι := ι) (P - Q) = 0
    rw [map_sub, hPQ, sub_self]
  have hLzero : L (P - Q) = 0 := by
    rw [hformula, hDzero, AddMonoidAlgebra.single_zero]
  have hsubzero : P - Q = 0 := by
    apply ordinaryCentralLaurentRescaledMap_injective
      (B := B) (ι := ι)
    simpa [L] using hLzero
  exact sub_eq_zero.mp hsubzero

/-! ## Direct central dehomogenization and its terminal components -/

variable (R : Type u) [CommRing R]
variable {h : ℕ} (totalD : Fin h → ℕ) (Time : Type v)

/-- Direct variable images for setting `H = 1` in the central index layout. -/
def homogeneousCentralDehomogenizationVariable :
    CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) →
      CentralPolynomial R (Fin h) totalD Time
  | Sum.inl derivative => MvPolynomial.X (Sum.inl derivative)
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr t) => MvPolynomial.X (Sum.inr t)

/-- Algebra-homomorphism packaging of direct central dehomogenization. -/
def homogeneousCentralDehomogenizationAlgHom :
    CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time) →ₐ[R]
      CentralPolynomial R (Fin h) totalD Time :=
  MvPolynomial.aeval
    (homogeneousCentralDehomogenizationVariable R totalD Time)

theorem homogeneousCentralDehomogenizationAlgHom_toRingHom :
    (homogeneousCentralDehomogenizationAlgHom R totalD Time).toRingHom =
      homogeneousCentralDehomogenization R totalD Time := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [homogeneousCentralDehomogenizationAlgHom]
  · intro x
    rcases x with ⟨b, i⟩ | (H | t)
    · simp [homogeneousCentralDehomogenizationAlgHom,
        homogeneousCentralDehomogenizationVariable]
    · simp [homogeneousCentralDehomogenizationAlgHom,
        homogeneousCentralDehomogenizationVariable]
    · simp [homogeneousCentralDehomogenizationAlgHom,
        homogeneousCentralDehomogenizationVariable]

/-- Dehomogenization preserves the signed terminal homogeneous degree. -/
theorem homogeneousCentralDehomogenization_preserves_signedTerminalHomogeneous
    {P : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)}
    {degree : Lex (Fin h → ℤ)}
    (hP : P.IsWeightedHomogeneous
      (fun x ↦ toLex
        (signedTerminalWeight totalD (Fin 1 ⊕ Time) x)) degree) :
    (homogeneousCentralDehomogenization R totalD Time P).IsWeightedHomogeneous
        (fun x ↦ toLex (signedTerminalWeight totalD Time x)) degree := by
  rw [← homogeneousCentralDehomogenizationAlgHom_toRingHom
    R totalD Time]
  change
    (MvPolynomial.aeval
      (homogeneousCentralDehomogenizationVariable R totalD Time) P).IsWeightedHomogeneous
          (fun x ↦ toLex (signedTerminalWeight totalD Time x)) degree
  apply weightedHomogeneous_aeval hP
  intro x
  rcases x with derivative | (H | t)
  · change
      (MvPolynomial.X (Sum.inl derivative) :
        CentralPolynomial R (Fin h) totalD Time).IsWeightedHomogeneous
          (fun x ↦ toLex (signedTerminalWeight totalD Time x))
          (toLex (signedTerminalWeight totalD Time (Sum.inl derivative)))
    simpa [homogeneousCentralDehomogenizationVariable] using
      (MvPolynomial.isWeightedHomogeneous_X R
        (fun x ↦ toLex (signedTerminalWeight totalD Time x))
        (Sum.inl derivative))
  · have hzero :
        signedTerminalWeight totalD (Fin 1 ⊕ Time)
            (Sum.inr (Sum.inl H)) = 0 := by
      funext b
      simp [signedTerminalWeight, terminalGlobalWeight]
    rw [hzero]
    simpa [homogeneousCentralDehomogenizationVariable] using
      (MvPolynomial.isWeightedHomogeneous_one R
        (fun x ↦ toLex (signedTerminalWeight totalD Time x)))
  · change
      (MvPolynomial.X (Sum.inr t) :
        CentralPolynomial R (Fin h) totalD Time).IsWeightedHomogeneous
          (fun x ↦ toLex (signedTerminalWeight totalD Time x))
          (toLex (signedTerminalWeight totalD Time (Sum.inr t)))
    simpa [homogeneousCentralDehomogenizationVariable] using
      (MvPolynomial.isWeightedHomogeneous_X R
        (fun x ↦ toLex (signedTerminalWeight totalD Time x))
        (Sum.inr t))

/-- Dehomogenization commutes with each signed terminal component. -/
theorem homogeneousCentralDehomogenization_weightedComponent
    (degree : Lex (Fin h → ℤ))
    (P : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)) :
    homogeneousCentralDehomogenization R totalD Time
        (MvPolynomial.weightedHomogeneousComponent
          (fun x ↦ toLex
            (signedTerminalWeight totalD (Fin 1 ⊕ Time) x)) degree P) =
      MvPolynomial.weightedHomogeneousComponent
        (fun x ↦ toLex (signedTerminalWeight totalD Time x)) degree
        (homogeneousCentralDehomogenization R totalD Time P) := by
  exact weightedHomogeneousComponent_ringHom_of_preserves
    (fun x ↦ toLex
      (signedTerminalWeight totalD (Fin 1 ⊕ Time) x))
    (fun x ↦ toLex (signedTerminalWeight totalD Time x))
    (homogeneousCentralDehomogenization R totalD Time)
    (fun hP ↦
      homogeneousCentralDehomogenization_preserves_signedTerminalHomogeneous
        R totalD Time hP) degree P

/-- Fixed-degree injectivity transported from the flat layout to the central
layout. -/
theorem homogeneousCentralDehomogenization_injective_on_homogeneous_degree
    {P Q : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)}
    {degree : ℕ}
    (hP : P.IsWeightedHomogeneous (fun _ ↦ (1 : ℕ)) degree)
    (hQ : Q.IsWeightedHomogeneous (fun _ ↦ (1 : ℕ)) degree)
    (hPQ : homogeneousCentralDehomogenization R totalD Time P =
      homogeneousCentralDehomogenization R totalD Time Q) :
    P = Q := by
  let E := homogeneousCentralReassocEquiv R totalD Time
  apply E.injective
  apply ordinaryDehomogenizationHom_injective_on_homogeneous_degree
    (B := R) (ι := CentralPolynomialIndex (Fin h) totalD Time)
  · change P.IsHomogeneous degree at hP
    change (E P).IsHomogeneous degree
    change
      (MvPolynomial.rename
        (homogeneousCentralIndexEquiv totalD Time) P).IsHomogeneous degree
    exact hP.rename_isHomogeneous
  · change Q.IsHomogeneous degree at hQ
    change (E Q).IsHomogeneous degree
    change
      (MvPolynomial.rename
        (homogeneousCentralIndexEquiv totalD Time) Q).IsHomogeneous degree
    exact hQ.rename_isHomogeneous
  · exact hPQ

/-! ## Compatibility for one homogeneous polynomial -/

/-- On an ordinarily homogeneous polynomial, dehomogenization commutes with
the least signed-terminal-weight form. -/
theorem homogeneousCentralDehomogenization_lexicographicInitialForm
    {P : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)}
    {ordinaryDegree : ℕ}
    (hP : P.IsWeightedHomogeneous (fun _ ↦ (1 : ℕ)) ordinaryDegree) :
    homogeneousCentralDehomogenization R totalD Time
        (lexicographicInitialForm
          (signedTerminalWeight totalD (Fin 1 ⊕ Time)) P) =
      lexicographicInitialForm (signedTerminalWeight totalD Time)
        (homogeneousCentralDehomogenization R totalD Time P) := by
  classical
  by_cases hPzero : P = 0
  · subst P
    simp
  let sourceWeight :
      CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) →
        Lex (Fin h → ℤ) :=
    fun x ↦ toLex (signedTerminalWeight totalD (Fin 1 ⊕ Time) x)
  let targetWeight :
      CentralPolynomialIndex (Fin h) totalD Time → Lex (Fin h → ℤ) :=
    fun x ↦ toLex (signedTerminalWeight totalD Time x)
  let ordinaryWeight :
      CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) → ℕ :=
    fun _ ↦ 1
  let beta : Lex (Fin h → ℤ) :=
    lexicographicMinimumWeight
      (signedTerminalWeight totalD (Fin 1 ⊕ Time)) P
  have hcomponent :
      homogeneousCentralDehomogenization R totalD Time
          (MvPolynomial.weightedHomogeneousComponent sourceWeight beta P) =
        MvPolynomial.weightedHomogeneousComponent targetWeight beta
          (homogeneousCentralDehomogenization R totalD Time P) :=
    homogeneousCentralDehomogenization_weightedComponent
      R totalD Time beta P
  have hsourceComponent :
      MvPolynomial.weightedHomogeneousComponent sourceWeight beta P ≠ 0 := by
    change
      lexicographicInitialForm
        (signedTerminalWeight totalD (Fin 1 ⊕ Time)) P ≠ 0
    exact lexicographicInitialForm_ne_zero _ hPzero
  have hsourceOrdinary :
      (MvPolynomial.weightedHomogeneousComponent sourceWeight beta P).IsWeightedHomogeneous
        ordinaryWeight ordinaryDegree := by
    exact weightedHomogeneousComponent_preserves_homogeneity
      sourceWeight ordinaryWeight beta hP
  have himageComponent :
      homogeneousCentralDehomogenization R totalD Time
        (MvPolynomial.weightedHomogeneousComponent sourceWeight beta P) ≠ 0 := by
    intro hzero
    apply hsourceComponent
    apply homogeneousCentralDehomogenization_injective_on_homogeneous_degree
      R totalD Time hsourceOrdinary
      (MvPolynomial.isWeightedHomogeneous_zero R ordinaryWeight ordinaryDegree)
    simpa using hzero
  have htargetComponent :
      MvPolynomial.weightedHomogeneousComponent targetWeight beta
        (homogeneousCentralDehomogenization R totalD Time P) ≠ 0 := by
    rwa [← hcomponent]
  have hbound : ∀ d ∈
      (homogeneousCentralDehomogenization R totalD Time P).support,
      beta ≤ Finsupp.weight targetWeight d := by
    intro d hd
    by_contra hnot
    have hlt : Finsupp.weight targetWeight d < beta := lt_of_not_ge hnot
    let gamma : Lex (Fin h → ℤ) := Finsupp.weight targetWeight d
    have htargetGamma :
        MvPolynomial.weightedHomogeneousComponent targetWeight gamma
          (homogeneousCentralDehomogenization R totalD Time P) ≠ 0 := by
      intro hzero
      have hcoeff := congrArg
        (fun Q : CentralPolynomial R (Fin h) totalD Time ↦ Q.coeff d) hzero
      rw [MvPolynomial.coeff_weightedHomogeneousComponent,
        if_pos rfl, MvPolynomial.coeff_zero] at hcoeff
      exact (MvPolynomial.mem_support_iff.mp hd) hcoeff
    have hgammaComponent :=
      homogeneousCentralDehomogenization_weightedComponent
        R totalD Time gamma P
    have hsourceGamma :
        MvPolynomial.weightedHomogeneousComponent sourceWeight gamma P ≠ 0 := by
      intro hzero
      apply htargetGamma
      rw [← hgammaComponent, hzero, map_zero]
    obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hsourceGamma
    rw [MvPolynomial.support_weightedHomogeneousComponent] at hm
    have hmSupport : m ∈ P.support := (Finset.mem_filter.mp hm).1
    have hmWeight : Finsupp.weight sourceWeight m = gamma :=
      (Finset.mem_filter.mp hm).2
    have hminimum := lexicographicMinimumWeight_le
      (signedTerminalWeight totalD (Fin 1 ⊕ Time)) P hmSupport
    change beta ≤ Finsupp.weight sourceWeight m at hminimum
    rw [hmWeight] at hminimum
    exact (not_lt_of_ge hminimum) hlt
  have hminimum :
      lexicographicMinimumWeight (signedTerminalWeight totalD Time)
          (homogeneousCentralDehomogenization R totalD Time P) = beta :=
    lexicographicMinimumWeight_eq_of_component_ne_zero
      (signedTerminalWeight totalD Time)
      (homogeneousCentralDehomogenization R totalD Time P)
      beta hbound htargetComponent
  change
    homogeneousCentralDehomogenization R totalD Time
        (MvPolynomial.weightedHomogeneousComponent sourceWeight beta P) =
      MvPolynomial.weightedHomogeneousComponent targetWeight
        (lexicographicMinimumWeight (signedTerminalWeight totalD Time)
          (homogeneousCentralDehomogenization R totalD Time P))
        (homogeneousCentralDehomogenization R totalD Time P)
  rw [hcomponent, hminimum]

/-! ## Homogeneous lifting inside a homogeneous ideal -/

/-- Raise all ordinary homogeneous components to the total degree of `P` by
powers of `H`. -/
def homogeneousCentralHomogeneousLift
    (P : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)) :
    CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time) :=
  ∑ degree ∈ P.support.image
      (Finsupp.weight (fun _ ↦ (1 : ℕ))),
    homogeneousCentralH R totalD Time ^ (P.totalDegree - degree) *
      MvPolynomial.weightedHomogeneousComponent
        (fun _ ↦ (1 : ℕ)) degree P

private theorem homogeneousCentral_supportDegree_le_totalDegree
    (P : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))
    {degree : ℕ}
    (hdegree : degree ∈ P.support.image
      (Finsupp.weight (fun _ ↦ (1 : ℕ)))) :
    degree ≤ P.totalDegree := by
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hdegree
  simpa [Finsupp.weight_apply] using
    MvPolynomial.le_totalDegree hm

/-- The lift remains inside every ordinarily homogeneous ideal containing
the original polynomial. -/
theorem homogeneousCentralHomogeneousLift_mem
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ))))
    {P : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)}
    (hP : P ∈ K) :
    homogeneousCentralHomogeneousLift R totalD Time P ∈ K := by
  classical
  unfold homogeneousCentralHomogeneousLift
  apply Ideal.sum_mem
  intro degree hdegree
  exact K.mul_mem_left _
    (MvPolynomial.weightedHomogeneousComponent_mem_of_mem R
      (fun _ ↦ (1 : ℕ)) hK hP degree)

/-- The lift is homogeneous of degree `P.totalDegree`. -/
theorem homogeneousCentralHomogeneousLift_isHomogeneous
    (P : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)) :
    (homogeneousCentralHomogeneousLift R totalD Time P).IsWeightedHomogeneous
      (fun _ ↦ (1 : ℕ)) P.totalDegree := by
  classical
  unfold homogeneousCentralHomogeneousLift
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro degree hdegree
  have hdegreeLe : degree ≤ P.totalDegree :=
    homogeneousCentral_supportDegree_le_totalDegree
      R totalD Time P hdegree
  have hH : (homogeneousCentralH R totalD Time).IsWeightedHomogeneous
      (fun _ ↦ (1 : ℕ)) 1 := by
    exact MvPolynomial.isWeightedHomogeneous_X R
      (fun _ : CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) ↦
        (1 : ℕ))
      (Sum.inr (Sum.inl (0 : Fin 1)))
  have hHpow := hH.pow (P.totalDegree - degree)
  have hcomponent :
      (MvPolynomial.weightedHomogeneousComponent
        (fun _ : CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) ↦
          (1 : ℕ)) degree P).IsWeightedHomogeneous
        (fun _ ↦ (1 : ℕ)) degree :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous degree P
  simpa [Nat.sub_add_cancel hdegreeLe] using hHpow.mul hcomponent

/-- Dehomogenizing the homogeneous lift gives the same polynomial as
dehomogenizing its input. -/
theorem homogeneousCentralDehomogenization_homogeneousLift
    (P : CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)) :
    homogeneousCentralDehomogenization R totalD Time
        (homogeneousCentralHomogeneousLift R totalD Time P) =
      homogeneousCentralDehomogenization R totalD Time P := by
  classical
  let ordinaryWeight :
      CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) → ℕ :=
    fun _ ↦ 1
  let degrees := P.support.image (Finsupp.weight ordinaryWeight)
  calc
    homogeneousCentralDehomogenization R totalD Time
        (homogeneousCentralHomogeneousLift R totalD Time P) =
      ∑ degree ∈ degrees,
        homogeneousCentralDehomogenization R totalD Time
          (MvPolynomial.weightedHomogeneousComponent
            ordinaryWeight degree P) := by
      simp [homogeneousCentralHomogeneousLift, ordinaryWeight, degrees,
        homogeneousCentralH]
    _ = homogeneousCentralDehomogenization R totalD Time
        (∑ degree ∈ degrees,
          MvPolynomial.weightedHomogeneousComponent
            ordinaryWeight degree P) := by
      simp only [map_sum]
    _ = homogeneousCentralDehomogenization R totalD Time P := by
      rw [sum_weightedHomogeneousComponent_support ordinaryWeight P]

/-! ## Surjectivity and homogeneous preimages -/

/-- Include the dehomogenized central variables while omitting `H`. -/
def homogeneousCentralRetainedInclusion :
    CentralPolynomial R (Fin h) totalD Time →+*
      CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time) :=
  (MvPolynomial.rename
    (fun x : CentralPolynomialIndex (Fin h) totalD Time ↦
      match x with
      | Sum.inl derivative => Sum.inl derivative
      | Sum.inr t => Sum.inr (Sum.inr t))).toRingHom

theorem homogeneousCentralDehomogenization_comp_retainedInclusion :
    (homogeneousCentralDehomogenization R totalD Time).comp
        (homogeneousCentralRetainedInclusion R totalD Time) =
      RingHom.id (CentralPolynomial R (Fin h) totalD Time) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [homogeneousCentralRetainedInclusion]
  · intro x
    rcases x with ⟨b, i⟩ | t
    · simp [homogeneousCentralRetainedInclusion]
    · simp [homogeneousCentralRetainedInclusion]

/-- Direct central dehomogenization is surjective. -/
theorem homogeneousCentralDehomogenization_surjective :
    Function.Surjective
      (homogeneousCentralDehomogenization R totalD Time) := by
  intro P
  refine ⟨homogeneousCentralRetainedInclusion R totalD Time P, ?_⟩
  exact RingHom.congr_fun
    (homogeneousCentralDehomogenization_comp_retainedInclusion
      R totalD Time) P

/-- Every member of the dehomogenized image of an ordinarily homogeneous
ideal has a homogeneous preimage in that ideal. -/
theorem exists_homogeneous_mem_of_mem_dehomogenizedIdeal
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ))))
    {P : CentralPolynomial R (Fin h) totalD Time}
    (hP : P ∈ K.map
      (homogeneousCentralDehomogenization R totalD Time)) :
    ∃ Q ∈ K, ∃ degree : ℕ,
      Q.IsWeightedHomogeneous (fun _ ↦ (1 : ℕ)) degree ∧
      homogeneousCentralDehomogenization R totalD Time Q = P := by
  obtain ⟨Q, hQK, hQP⟩ :=
    (Ideal.mem_map_iff_of_surjective
      (homogeneousCentralDehomogenization R totalD Time)
      (homogeneousCentralDehomogenization_surjective R totalD Time)).mp hP
  let Qhom := homogeneousCentralHomogeneousLift R totalD Time Q
  refine ⟨Qhom,
    homogeneousCentralHomogeneousLift_mem R totalD Time K hK hQK,
    Q.totalDegree,
    homogeneousCentralHomogeneousLift_isHomogeneous R totalD Time Q, ?_⟩
  exact (homogeneousCentralDehomogenization_homogeneousLift
    R totalD Time Q).trans hQP

/-! ## Ideal-level compatibility -/

/-- Terminal full initial formation commutes with `H = 1` for every
ordinarily homogeneous ideal. -/
theorem lexicographicInitialIdeal_map_homogeneousCentralDehomogenization
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ)))) :
    (lexicographicInitialIdeal
      (signedTerminalWeight totalD (Fin 1 ⊕ Time)) K).map
        (homogeneousCentralDehomogenization R totalD Time) =
      lexicographicInitialIdeal (signedTerminalWeight totalD Time)
        (K.map (homogeneousCentralDehomogenization R totalD Time)) := by
  classical
  let sourceOrdinaryWeight :
      CentralPolynomialIndex (Fin h) totalD (Fin 1 ⊕ Time) → ℕ :=
    fun _ ↦ 1
  apply le_antisymm
  · change
      (Ideal.span
        (lexicographicInitialForm
          (signedTerminalWeight totalD (Fin 1 ⊕ Time)) ''
          (K : Set
            (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time))))).map
        (homogeneousCentralDehomogenization R totalD Time) ≤ _
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨_, ⟨P, hPK, rfl⟩, rfl⟩
    rw [← sum_weightedHomogeneousComponent_support
      sourceOrdinaryWeight
      (lexicographicInitialForm
        (signedTerminalWeight totalD (Fin 1 ⊕ Time)) P), map_sum]
    apply Ideal.sum_mem
    intro degree hdegree
    by_cases hzero :
        MvPolynomial.weightedHomogeneousComponent sourceOrdinaryWeight degree
          (lexicographicInitialForm
            (signedTerminalWeight totalD (Fin 1 ⊕ Time)) P) = 0
    · rw [hzero, map_zero]
      exact Ideal.zero_mem _
    · rw [← lexicographicInitialForm_of_weightedComponent
        sourceOrdinaryWeight
        (signedTerminalWeight totalD (Fin 1 ⊕ Time)) degree P hzero]
      rw [homogeneousCentralDehomogenization_lexicographicInitialForm
        R totalD Time
        (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
          degree P)]
      exact lexicographicInitialForm_mem_initialIdeal
        (signedTerminalWeight totalD Time) _
        (Ideal.mem_map_of_mem
          (homogeneousCentralDehomogenization R totalD Time)
          (MvPolynomial.weightedHomogeneousComponent_mem_of_mem R
            sourceOrdinaryWeight hK hPK degree))
  · change Ideal.span
      (lexicographicInitialForm (signedTerminalWeight totalD Time) ''
        (K.map (homogeneousCentralDehomogenization R totalD Time) :
          Set (CentralPolynomial R (Fin h) totalD Time))) ≤ _
    apply Ideal.span_le.mpr
    rintro _ ⟨P, hP, rfl⟩
    obtain ⟨Q, hQK, degree, hQhom, hQP⟩ :=
      exists_homogeneous_mem_of_mem_dehomogenizedIdeal
        R totalD Time K hK hP
    have hform :=
      homogeneousCentralDehomogenization_lexicographicInitialForm
        R totalD Time hQhom
    rw [← hQP, ← hform]
    exact Ideal.mem_map_of_mem
      (homogeneousCentralDehomogenization R totalD Time)
      (lexicographicInitialForm_mem_initialIdeal
        (signedTerminalWeight totalD (Fin 1 ⊕ Time)) K hQK)

/-- The compatibility predicate from `HomogeneousCentralIteration` follows
from ordinary homogeneity, with no Noetherianity, finiteness, domain, or
characteristic hypothesis. -/
theorem terminalInitialDehomogenizationCompatible_of_isOrdinaryHomogeneous
    (K : Ideal
      (CentralPolynomial R (Fin h) totalD (Fin 1 ⊕ Time)))
    (hK : K.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R
        (fun _ ↦ (1 : ℕ)))) :
    TerminalInitialDehomogenizationCompatible R totalD Time K := by
  exact lexicographicInitialIdeal_map_homogeneousCentralDehomogenization
    R totalD Time K hK

end AbelFormalization
