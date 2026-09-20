import AbelFormalization.RankOneIdealHomogeneity

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Rank-one lexicographic initial ideals in a bounded polynomial window

For an ordinary homogeneous ideal, taking the full lexicographic initial
ideal and then restricting to a bounded ordinary-degree window agrees with
the literal finite-coordinate initial submodule of that window.  The proof
uses all elements of the ideal.  A lift of a prescribed lexicographic
component is truncated by ordinary degree; ordinary homogeneity keeps that
truncation in the ideal.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n h : ℕ}

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## Ordinary-degree truncation -/

/-- Discard the terms whose weighted ordinary degree is greater than `D`.
The integer cutoff is convenient because the shifted polynomial-window API
uses integer degrees, although the rank-one ideal has zero shift. -/
def rankOneOrdinaryWindowProjection
    (ordinaryDegree : Fin n → ℕ) (D : ℤ) :
    MvPolynomial (Fin n) B →ₗ[B] MvPolynomial (Fin n) B where
  toFun f := AddMonoidAlgebra.ofCoeff <|
    Finsupp.filter
      (fun d => (Finsupp.weight ordinaryDegree d : ℤ) ≤ D)
      f.coeff
  map_add' f g := by
    apply AddMonoidAlgebra.ext
    rw [AddMonoidAlgebra.coeff_add]
    exact Finsupp.filter_add
  map_smul' c f := by
    apply AddMonoidAlgebra.ext
    simp only [AddMonoidAlgebra.coeff_smul, RingHom.id_apply]
    exact Finsupp.filter_smul

@[simp]
theorem rankOneOrdinaryWindowProjection_coeff
    (ordinaryDegree : Fin n → ℕ) (D : ℤ)
    (f : MvPolynomial (Fin n) B) (d : Fin n →₀ ℕ) :
    (rankOneOrdinaryWindowProjection ordinaryDegree D f).coeff d =
      if (Finsupp.weight ordinaryDegree d : ℤ) ≤ D
      then f.coeff d else 0 :=
  rfl

/-- The cutoff is the finite sum of the ordinary homogeneous components
that it retains. -/
theorem rankOneOrdinaryWindowProjection_eq_sum
    (ordinaryDegree : Fin n → ℕ) (D : ℤ)
    (f : MvPolynomial (Fin n) B) :
    rankOneOrdinaryWindowProjection ordinaryDegree D f =
      ∑ degree ∈
          ((f.support.image (Finsupp.weight ordinaryDegree) : Finset ℕ).filter
            (fun degree : ℕ => (degree : ℤ) ≤ D)),
        MvPolynomial.weightedHomogeneousComponent
          ordinaryDegree degree f := by
  classical
  ext d
  rw [rankOneOrdinaryWindowProjection_coeff]
  simp only [MvPolynomial.coeff_sum,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  by_cases hcoeff : f.coeff d = 0
  · simp [hcoeff]
  · have hdegree : Finsupp.weight ordinaryDegree d ∈
        f.support.image (Finsupp.weight ordinaryDegree) := by
      exact Finset.mem_image.mpr
        ⟨d, MvPolynomial.mem_support_iff.mpr hcoeff, rfl⟩
    by_cases hD : (Finsupp.weight ordinaryDegree d : ℤ) ≤ D
    · rw [if_pos hD]
      have hmem : Finsupp.weight ordinaryDegree d ∈
          ((f.support.image (Finsupp.weight ordinaryDegree) : Finset ℕ).filter
            (fun degree : ℕ => (degree : ℤ) ≤ D)) :=
        Finset.mem_filter.mpr ⟨hdegree, hD⟩
      rw [Finset.sum_eq_single_of_mem
        (Finsupp.weight ordinaryDegree d) hmem]
      · simp
      · intro degree _ hne
        rw [if_neg (Ne.symm hne)]
    · rw [if_neg hD]
      symm
      apply Finset.sum_eq_zero
      intro degree hdegree'
      by_cases heq : Finsupp.weight ordinaryDegree d = degree
      · subst degree
        exact (hD (Finset.mem_filter.mp hdegree').2).elim
      · exact if_neg heq

/-- A natural ordinary-degree component is the corresponding component for
the integral casts of the variable degrees. -/
theorem weightedHomogeneousComponent_nat_eq_intCast
    (ordinaryDegree : Fin n → ℕ) (degree : ℕ)
    (f : MvPolynomial (Fin n) B) :
    MvPolynomial.weightedHomogeneousComponent ordinaryDegree degree f =
      MvPolynomial.weightedHomogeneousComponent
        (fun i => (ordinaryDegree i : ℤ)) (degree : ℤ) f := by
  classical
  ext d
  simp only [MvPolynomial.coeff_weightedHomogeneousComponent,
    finsupp_weight_natCast, Int.ofNat_inj]

/-- Ordinary homogeneity ensures that ordinary-degree truncation stays in
the ideal. -/
theorem rankOneOrdinaryWindowProjection_mem_of_isHomogeneous
    (ordinaryDegree : Fin n → ℕ) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun i => (ordinaryDegree i : ℤ))))
    {f : MvPolynomial (Fin n) B} (hf : f ∈ I) :
    rankOneOrdinaryWindowProjection ordinaryDegree D f ∈ I := by
  rw [rankOneOrdinaryWindowProjection_eq_sum]
  apply Ideal.sum_mem
  intro degree hdegree
  rw [weightedHomogeneousComponent_nat_eq_intCast]
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem B
    (fun i => (ordinaryDegree i : ℤ)) hI hf (degree : ℤ)

/-- Truncation cannot introduce a monomial below an existing lower bound
for a second weight. -/
theorem rankOneOrdinaryWindowProjection_support_bound
    (ordinaryDegree : Fin n → ℕ) (D : ℤ)
    (multiDegree : Fin n → Fin h → ℤ)
    (beta : PolynomialLexWeight h)
    {f : MvPolynomial (Fin n) B}
    (hbound : ∀ d ∈ f.support,
      beta ≤ Finsupp.weight (fun i => toLex (multiDegree i)) d) :
    ∀ d ∈ (rankOneOrdinaryWindowProjection ordinaryDegree D f).support,
      beta ≤ Finsupp.weight (fun i => toLex (multiDegree i)) d := by
  intro d hd
  apply hbound d
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  rw [rankOneOrdinaryWindowProjection_coeff] at hcoeff
  by_cases hD : (Finsupp.weight ordinaryDegree d : ℤ) ≤ D
  · exact MvPolynomial.mem_support_iff.mpr (by simpa [hD] using hcoeff)
  · simp [hD] at hcoeff

/-- Ordinary truncation and a lexicographic-weight component are commuting
coefficient filters. -/
theorem weightedHomogeneousComponent_rankOneOrdinaryWindowProjection
    (ordinaryDegree : Fin n → ℕ) (D : ℤ)
    (multiDegree : Fin n → Fin h → ℤ)
    (beta : PolynomialLexWeight h)
    (f : MvPolynomial (Fin n) B) :
    MvPolynomial.weightedHomogeneousComponent
        (fun i => toLex (multiDegree i)) beta
        (rankOneOrdinaryWindowProjection ordinaryDegree D f) =
      rankOneOrdinaryWindowProjection ordinaryDegree D
        (MvPolynomial.weightedHomogeneousComponent
          (fun i => toLex (multiDegree i)) beta f) := by
  classical
  ext d
  simp only [rankOneOrdinaryWindowProjection_coeff,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs <;> rfl

section CanonicalRankOneGrading

variable (ordinaryDegree : Fin n → ℕ)
variable (multiDegree : Fin n → Fin h → ℤ)

local notation "G₁" =>
  rankOnePolynomialGradedLexData ordinaryDegree multiDegree

/-- The cutoff lands in the canonical rank-one polynomial window. -/
theorem rankOneOrdinaryWindowProjection_mem_window
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (f : MvPolynomial (Fin n) B) :
    rankOneOrdinaryWindowProjection ordinaryDegree D f ∈
      (G₁).rankOnePolynomialWindowPreimage hpositive D := by
  rw [(G₁).mem_rankOnePolynomialWindowPreimage_iff_coeff]
  intro d hd
  have hD : (Finsupp.weight ordinaryDegree d : ℤ) ≤ D := by
    rw [rankOneOrdinaryWindowProjection_coeff] at hd
    by_cases hle : (Finsupp.weight ordinaryDegree d : ℤ) ≤ D
    · exact hle
    · simp [hle] at hd
  apply ((G₁).mem_windowTermFinset_iff_le hpositive D
    ((0 : Fin 1), d)).mpr
  simpa only [rankOnePolynomialGradedLexData_termOrdinaryDegree] using hD

/-- The cutoff fixes a polynomial already in the canonical rank-one
window. -/
theorem rankOneOrdinaryWindowProjection_eq_self_of_mem_window
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    {f : MvPolynomial (Fin n) B}
    (hf : f ∈ (G₁).rankOnePolynomialWindowPreimage hpositive D) :
    rankOneOrdinaryWindowProjection ordinaryDegree D f = f := by
  classical
  ext d
  rw [rankOneOrdinaryWindowProjection_coeff]
  by_cases hcoeff : f.coeff d = 0
  · simp [hcoeff]
  · have ht :=
      ((G₁).mem_rankOnePolynomialWindowPreimage_iff_coeff
        hpositive D f).mp hf d hcoeff
    have hD :=
      ((G₁).mem_windowTermFinset_iff_le hpositive D
        ((0 : Fin 1), d)).mp ht
    have hD' : (Finsupp.weight ordinaryDegree d : ℤ) ≤ D := by
      simpa only [rankOnePolynomialGradedLexData_termOrdinaryDegree] using hD
    exact if_pos hD'

/-! ## Rank-one coordinates and prefix vanishing -/

/-- The unique coordinate of a rank-one module weight component is the
corresponding polynomial weight component. -/
theorem rankOnePolynomial_weightFiberComponent_zero_module
    (weight : PolynomialLexWeight h)
    (P : artinianFreePolynomialModule B n 1) :
    (artinianPolynomialModuleFiberComponent (G₁).termWeight weight P 0) =
      MvPolynomial.weightedHomogeneousComponent
        (fun i => toLex (multiDegree i)) weight (P 0) := by
  classical
  ext d
  rw [artinianPolynomialModuleFiberComponent_coeff,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  simp only [rankOnePolynomialGradedLexData_termWeight]

/-- Ordered-window evaluation is literally polynomial weight projection in
the unique rank-one coordinate. -/
theorem rankOne_windowOrderedWeightLinearEquiv_apply_zero
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (P : (G₁).windowModule B hpositive D)
    (i : Fin ((G₁).weightCount hpositive D)) :
    ((((G₁).windowOrderedWeightLinearEquiv (B := B) hpositive D P i :
          (G₁).orderedWeightPiece B hpositive D i) :
        artinianFreePolynomialModule B n 1) 0) =
      MvPolynomial.weightedHomogeneousComponent
        (fun j => toLex (multiDegree j))
        ((G₁).weightAt hpositive D i)
        ((P : artinianFreePolynomialModule B n 1) 0) := by
  change
    (artinianPolynomialModuleFiberComponent (G₁).termWeight
      ((G₁).weightAt hpositive D i)
      (P : artinianFreePolynomialModule B n 1) 0) = _
  classical
  apply MvPolynomial.ext
  intro d
  rw [artinianPolynomialModuleFiberComponent_coeff,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  simp only [rankOnePolynomialGradedLexData_termWeight]

/-- A grouped rank-one weight piece is homogeneous of that polynomial
weight. -/
theorem rankOne_windowWeightPiece_isWeightedHomogeneous
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (weight : PolynomialLexWeight h)
    (v : (G₁).windowWeightPiece B hpositive D weight) :
    ((v : artinianFreePolynomialModule B n 1) 0).IsWeightedHomogeneous
      (fun i => toLex (multiDegree i)) weight := by
  intro d hd
  have ht := (mem_artinianPolynomialModuleSupported _ _).mp v.property
    0 d hd
  simpa only [rankOnePolynomialGradedLexData_termWeight] using ht.2

/-- The polynomial in a grouped rank-one weight piece belongs to the
pulled-back ordinary-degree window. -/
theorem rankOne_windowWeightPiece_mem_window
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (weight : PolynomialLexWeight h)
    (v : (G₁).windowWeightPiece B hpositive D weight) :
    ((v : artinianFreePolynomialModule B n 1) 0) ∈
      (G₁).rankOnePolynomialWindowPreimage hpositive D := by
  rw [(G₁).mem_rankOnePolynomialWindowPreimage_iff_coeff]
  intro d hd
  exact ((mem_artinianPolynomialModuleSupported _ _).mp v.property
    0 d hd).1

/-- Earlier ordered-window coordinates vanish exactly when every supported
monomial has weight at least the selected coordinate weight. -/
theorem rankOne_finiteWeightPrefixProjection_eq_zero_iff_support_bound
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (P : (G₁).windowModule B hpositive D)
    (i : Fin ((G₁).weightCount hpositive D)) :
    finiteWeightPrefixProjection B
        (fun j : Fin ((G₁).weightCount hpositive D) =>
          (G₁).orderedWeightPiece B hpositive D j) i.val
        ((G₁).windowOrderedWeightLinearEquiv hpositive D P) = 0 ↔
      ∀ d ∈ ((P : artinianFreePolynomialModule B n 1) 0).support,
        (G₁).weightAt hpositive D i ≤
          Finsupp.weight (fun j => toLex (multiDegree j)) d := by
  classical
  constructor
  · intro hprefix d hd
    have hcoeff :
        ((P : artinianFreePolynomialModule B n 1) 0).coeff d ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hd
    have ht : ((0 : Fin 1), d) ∈ (G₁).windowTermSet hpositive D :=
      (mem_artinianPolynomialModuleSupported _ _).mp P.property 0 d hcoeff
    have hweight :
        Finsupp.weight (fun j => toLex (multiDegree j)) d ∈
          (G₁).weightWindow hpositive D := by
      apply ((G₁).mem_weightWindow hpositive D _).mpr
      refine ⟨((0 : Fin 1), d),
        ((G₁).mem_windowTermFinset_iff_le hpositive D _).mp ht, ?_⟩
      simpa only [rankOnePolynomialGradedLexData_termWeight]
    obtain ⟨j, hj⟩ :=
      (G₁).exists_weightAt_eq hpositive D hweight
    by_contra hnot
    have hlt : Finsupp.weight (fun j => toLex (multiDegree j)) d <
        (G₁).weightAt hpositive D i := lt_of_not_ge hnot
    have hji : j < i :=
      ((G₁).weightAt_lt_iff hpositive D j i).mp (by
        rw [hj]
        exact hlt)
    have hcoordzero :
        (G₁).windowOrderedWeightLinearEquiv hpositive D P j = 0 := by
      have hjzero := congrFun hprefix j
      simpa [finiteWeightPrefixProjection_apply, hji] using hjzero
    have hzero :
        (((((G₁).windowOrderedWeightLinearEquiv hpositive D P j :
              (G₁).orderedWeightPiece B hpositive D j) :
            artinianFreePolynomialModule B n 1) 0).coeff d) = 0 := by
      rw [hcoordzero]
      simp
    rw [rankOne_windowOrderedWeightLinearEquiv_apply_zero,
      MvPolynomial.coeff_weightedHomogeneousComponent,
      if_pos hj.symm] at hzero
    exact hcoeff hzero
  · intro hbound
    funext j
    rw [finiteWeightPrefixProjection_apply]
    by_cases hji : j.val < i.val
    · rw [if_pos hji]
      apply Subtype.ext
      funext k
      have hk : k = 0 := Subsingleton.elim k 0
      subst k
      apply MvPolynomial.ext
      intro d
      rw [rankOne_windowOrderedWeightLinearEquiv_apply_zero,
        MvPolynomial.coeff_weightedHomogeneousComponent]
      by_cases hweight :
          Finsupp.weight (fun q => toLex (multiDegree q)) d =
            (G₁).weightAt hpositive D j
      · rw [if_pos hweight]
        by_cases hcoeff :
            ((P : artinianFreePolynomialModule B n 1) 0).coeff d = 0
        · exact hcoeff
        · exfalso
          have hge := hbound d
            (MvPolynomial.mem_support_iff.mpr hcoeff)
          rw [hweight] at hge
          exact (not_lt_of_ge hge)
            (((G₁).weightAt_lt_iff hpositive D j i).mpr hji)
      · exact if_neg hweight
    · rw [if_neg hji]
      simp

/-! ## Coordinate initial pieces -/

/-- For an ordinary homogeneous ideal, the `i`th finite initial piece of
its bounded ordered-weight part consists exactly of the `i`th weight piece
of the full lexicographic initial ideal. -/
theorem mem_finiteWeightInitialPiece_polynomialWindow_rankOne_iff
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun j => (ordinaryDegree j : ℤ))))
    (i : Fin ((G₁).weightCount hpositive D))
    (v : (G₁).orderedWeightPiece B hpositive D i) :
    v ∈ finiteWeightInitialPiece
        ((G₁).polynomialWindowOrderedWeightPart hpositive D
          (rankOnePolynomialIdealSubmodule I)) i ↔
      ((v : artinianFreePolynomialModule B n 1) 0) ∈
        lexicographicInitialIdeal multiDegree I := by
  classical
  let E := (G₁).windowOrderedWeightLinearEquiv (B := B) hpositive D
  constructor
  · rintro ⟨x, hx, hxv⟩
    have hxU := hx.1
    have hxprefix : finiteWeightPrefixProjection B
        (fun j : Fin ((G₁).weightCount hpositive D) =>
          (G₁).orderedWeightPiece B hpositive D j) i.val x = 0 := hx.2
    let P : (G₁).windowModule B hpositive D := E.symm x
    have hPI : ((P : artinianFreePolynomialModule B n 1) 0) ∈ I := by
      exact ((G₁).mem_polynomialWindowOrderedWeightPart_rankOneIdeal_iff
        hpositive D I x).mp hxU
    have hEP : E P = x := E.apply_symm_apply x
    have hprefix : finiteWeightPrefixProjection B
        (fun j : Fin ((G₁).weightCount hpositive D) =>
          (G₁).orderedWeightPiece B hpositive D j) i.val (E P) = 0 := by
      rw [hEP]
      exact hxprefix
    have hbound :=
      (rankOne_finiteWeightPrefixProjection_eq_zero_iff_support_bound
        ordinaryDegree multiDegree hpositive D P i).mp hprefix
    change x i = v at hxv
    have hcomponent :
        MvPolynomial.weightedHomogeneousComponent
            (fun j => toLex (multiDegree j))
            ((G₁).weightAt hpositive D i)
            ((P : artinianFreePolynomialModule B n 1) 0) =
          ((v : artinianFreePolynomialModule B n 1) 0) := by
      rw [← rankOne_windowOrderedWeightLinearEquiv_apply_zero
        ordinaryDegree multiDegree hpositive D P i, hEP, hxv]
    by_cases hvzero : ((v : artinianFreePolynomialModule B n 1) 0) = 0
    · rw [hvzero]
      exact (lexicographicInitialIdeal multiDegree I).zero_mem
    · have hcomponent_ne :
          MvPolynomial.weightedHomogeneousComponent
              (fun j => toLex (multiDegree j))
              ((G₁).weightAt hpositive D i)
              ((P : artinianFreePolynomialModule B n 1) 0) ≠ 0 := by
        rwa [hcomponent]
      have hmin := lexicographicMinimumWeight_eq_of_component_ne_zero
        multiDegree ((P : artinianFreePolynomialModule B n 1) 0)
        ((G₁).weightAt hpositive D i) hbound hcomponent_ne
      have hform : lexicographicInitialForm multiDegree
          ((P : artinianFreePolynomialModule B n 1) 0) =
          ((v : artinianFreePolynomialModule B n 1) 0) := by
        rw [lexicographicInitialForm, hmin, hcomponent]
      rw [← hform]
      exact lexicographicInitialForm_mem_initialIdeal multiDegree I hPI
  · intro hvI
    have hvhom := rankOne_windowWeightPiece_isWeightedHomogeneous
      ordinaryDegree multiDegree hpositive D
      ((G₁).weightAt hpositive D i) v
    obtain ⟨f, hfI, hfbound, hfcomponent⟩ :=
      exists_component_lift_lexicographicInitialIdeal
        multiDegree I hvI hvhom
    let fD := rankOneOrdinaryWindowProjection ordinaryDegree D f
    have hfDI : fD ∈ I :=
      rankOneOrdinaryWindowProjection_mem_of_isHomogeneous
        ordinaryDegree D I hI hfI
    have hfDwindow : fD ∈
        (G₁).rankOnePolynomialWindowPreimage hpositive D :=
      rankOneOrdinaryWindowProjection_mem_window
        ordinaryDegree multiDegree hpositive D f
    have hfDbound : ∀ d ∈ fD.support,
        (G₁).weightAt hpositive D i ≤
          Finsupp.weight (fun j => toLex (multiDegree j)) d :=
      rankOneOrdinaryWindowProjection_support_bound
        ordinaryDegree D multiDegree ((G₁).weightAt hpositive D i)
        hfbound
    have hvwindow : ((v : artinianFreePolynomialModule B n 1) 0) ∈
        (G₁).rankOnePolynomialWindowPreimage hpositive D :=
      rankOne_windowWeightPiece_mem_window ordinaryDegree multiDegree
        hpositive D ((G₁).weightAt hpositive D i) v
    have hfDcomponent :
        MvPolynomial.weightedHomogeneousComponent
            (fun j => toLex (multiDegree j))
            ((G₁).weightAt hpositive D i) fD =
          ((v : artinianFreePolynomialModule B n 1) 0) := by
      calc
        _ = rankOneOrdinaryWindowProjection ordinaryDegree D
              (MvPolynomial.weightedHomogeneousComponent
                (fun j => toLex (multiDegree j))
                ((G₁).weightAt hpositive D i) f) :=
          weightedHomogeneousComponent_rankOneOrdinaryWindowProjection
            ordinaryDegree D multiDegree ((G₁).weightAt hpositive D i) f
        _ = rankOneOrdinaryWindowProjection ordinaryDegree D
              ((v : artinianFreePolynomialModule B n 1) 0) := by
          rw [hfcomponent]
        _ = ((v : artinianFreePolynomialModule B n 1) 0) :=
          rankOneOrdinaryWindowProjection_eq_self_of_mem_window
            ordinaryDegree multiDegree hpositive D hvwindow
    let P : (G₁).windowModule B hpositive D :=
      ⟨rankOnePolynomialModuleCoeffEquiv fD,
        ((G₁).mem_rankOnePolynomialWindowPreimage_iff
          hpositive D fD).mp hfDwindow⟩
    refine ⟨E P, ⟨?_, ?_⟩, ?_⟩
    · apply ((G₁).mem_polynomialWindowOrderedWeightPart_rankOneIdeal_iff
        hpositive D I (E P)).mpr
      rw [E.symm_apply_apply]
      change fD ∈ I
      exact hfDI
    · apply (rankOne_finiteWeightPrefixProjection_eq_zero_iff_support_bound
        ordinaryDegree multiDegree hpositive D P i).mpr
      simpa only [P, rankOnePolynomialModuleCoeffEquiv_apply] using hfDbound
    · change E P i = v
      apply Subtype.ext
      funext k
      have hk : k = 0 := Subsingleton.elim k 0
      subst k
      calc
        (((E P i : (G₁).orderedWeightPiece B hpositive D i) :
              artinianFreePolynomialModule B n 1) 0) =
            MvPolynomial.weightedHomogeneousComponent
              (fun j => toLex (multiDegree j))
              ((G₁).weightAt hpositive D i) fD := by
          simpa only [P, rankOnePolynomialModuleCoeffEquiv_apply] using
            rankOne_windowOrderedWeightLinearEquiv_apply_zero
              ordinaryDegree multiDegree hpositive D P i
        _ = ((v : artinianFreePolynomialModule B n 1) 0) := hfDcomponent

/-! ## The full bounded-window identity -/

/-- Restricting a full lexicographic initial ideal to a finite ordinary
degree window agrees exactly with finite-weight initial formation on the
ordered coordinates of the original ideal. -/
theorem polynomialWindowOrderedWeightPart_rankOne_lexicographicInitialIdeal
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun j => (ordinaryDegree j : ℤ)))) :
    (G₁).polynomialWindowOrderedWeightPart hpositive D
        (rankOnePolynomialIdealSubmodule
          (lexicographicInitialIdeal multiDegree I)) =
      finiteWeightInitial
        ((G₁).polynomialWindowOrderedWeightPart hpositive D
          (rankOnePolynomialIdealSubmodule I)) := by
  classical
  let E := (G₁).windowOrderedWeightLinearEquiv (B := B) hpositive D
  apply le_antisymm
  · intro x hx
    apply (mem_finiteWeightInitial_iff _ x).mpr
    intro i
    apply (mem_finiteWeightInitialPiece_polynomialWindow_rankOne_iff
      ordinaryDegree multiDegree hpositive D I hI i (x i)).mpr
    have hxI :=
      ((G₁).mem_polynomialWindowOrderedWeightPart_rankOneIdeal_iff
        hpositive D (lexicographicInitialIdeal multiDegree I) x).mp hx
    let P : (G₁).windowModule B hpositive D := E.symm x
    have hEP : E P = x := E.apply_symm_apply x
    have hcomponent := lexicographicInitialIdeal_component_mem
      multiDegree I hxI ((G₁).weightAt hpositive D i)
    have hcoordinate : ((x i : (G₁).orderedWeightPiece B hpositive D i) :
          artinianFreePolynomialModule B n 1) 0 =
        MvPolynomial.weightedHomogeneousComponent
          (fun j => toLex (multiDegree j))
          ((G₁).weightAt hpositive D i)
          ((P : artinianFreePolynomialModule B n 1) 0) := by
      rw [← hEP]
      exact rankOne_windowOrderedWeightLinearEquiv_apply_zero
        ordinaryDegree multiDegree hpositive D P i
    rw [hcoordinate]
    exact hcomponent
  · intro x hx
    rw [← LinearMap.sum_single_apply
      (fun i : Fin ((G₁).weightCount hpositive D) =>
        (G₁).orderedWeightPiece B hpositive D i) x]
    apply Submodule.sum_mem
    intro i hi
    apply ((G₁).mem_polynomialWindowOrderedWeightPart_rankOneIdeal_iff
      hpositive D (lexicographicInitialIdeal multiDegree I)
      (Pi.single i (x i))).mpr
    have hipiece := (mem_finiteWeightInitial_iff _ x).mp hx i
    have hiI :=
      (mem_finiteWeightInitialPiece_polynomialWindow_rankOne_iff
        ordinaryDegree multiDegree hpositive D I hI i (x i)).mp hipiece
    rw [(G₁).windowOrderedWeightLinearEquiv_symm_single_coe]
    exact hiI

/-! ## One fixed ordinary-degree slice -/

/-- Include one ordinary-degree piece in a containing window and then pass
to ordered weight coordinates. -/
def PolynomialGradedLexData.ordinaryDegreeOrderedWeightEmbedding
    (G : PolynomialGradedLexData n 1 h)
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D degree : ℤ)
    (hdegree : degree ≤ D) :
    artinianPolynomialModulePiece (B := B)
        G.ordinaryDegree G.ordinaryShift degree →ₗ[B]
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :=
  (G.windowOrderedWeightLinearEquiv hpositive D).toLinearMap.comp
    (Submodule.inclusion
      (G.ordinaryPiece_le_windowModule hpositive D degree hdegree))

/-- The fixed-degree embedding loses no information. -/
theorem PolynomialGradedLexData.ordinaryDegreeOrderedWeightEmbedding_injective
    (G : PolynomialGradedLexData n 1 h)
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D degree : ℤ)
    (hdegree : degree ≤ D) :
    Function.Injective
      (G.ordinaryDegreeOrderedWeightEmbedding (B := B)
        hpositive D degree hdegree) := by
  exact (G.windowOrderedWeightLinearEquiv
    (B := B) hpositive D).injective.comp
      (Submodule.inclusion_injective
        (G.ordinaryPiece_le_windowModule hpositive D degree hdegree))

@[simp]
theorem PolynomialGradedLexData.windowEquiv_symm_ordinaryDegreeEmbedding
    (G : PolynomialGradedLexData n 1 h)
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D degree : ℤ)
    (hdegree : degree ≤ D)
    (P : artinianPolynomialModulePiece (B := B)
      G.ordinaryDegree G.ordinaryShift degree) :
    (G.windowOrderedWeightLinearEquiv hpositive D).symm
        (G.ordinaryDegreeOrderedWeightEmbedding hpositive D degree hdegree P) =
      Submodule.inclusion
        (G.ordinaryPiece_le_windowModule hpositive D degree hdegree) P := by
  exact (G.windowOrderedWeightLinearEquiv
    (B := B) hpositive D).symm_apply_apply _

/-- The ordered image of the part of a rank-one ideal in one ordinary
degree.  Its ambient module is the same finite product as the whole bounded
window, so finite-weight initial formation applies literally. -/
def PolynomialGradedLexData.rankOnePolynomialDegreeOrderedWeightPart
    (G : PolynomialGradedLexData n 1 h)
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D degree : ℤ)
    (hdegree : degree ≤ D)
    (I : Ideal (MvPolynomial (Fin n) B)) :
    Submodule B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :=
  (artinianPolynomialSubmoduleDegree
      (rankOnePolynomialIdealSubmodule I)
      G.ordinaryDegree G.ordinaryShift degree).map
    (G.ordinaryDegreeOrderedWeightEmbedding
      hpositive D degree hdegree)

/-- For the canonical rank-one grading, membership in a module ordinary
piece is exactly polynomial weighted homogeneity in the unique coordinate. -/
theorem rankOne_mem_ordinaryPiece_iff_isWeightedHomogeneous
    (degree : ℕ) (P : artinianFreePolynomialModule B n 1) :
    P ∈ artinianPolynomialModulePiece (B := B)
        ordinaryDegree (G₁).ordinaryShift (degree : ℤ) ↔
      (P 0).IsWeightedHomogeneous
        (fun i => (ordinaryDegree i : ℤ)) (degree : ℤ) := by
  classical
  constructor
  · intro hP d hd
    have hterm := (mem_artinianPolynomialModuleSupported _ _).mp hP
      0 d hd
    change artinianPolynomialTermDegree ordinaryDegree (fun _ : Fin 1 => 0)
      ((0 : Fin 1), d) = (degree : ℤ) at hterm
    change Finsupp.weight (fun i => (ordinaryDegree i : ℤ)) d =
      (degree : ℤ)
    rw [finsupp_weight_natCast]
    simpa only [artinianPolynomialTermDegree, add_zero] using hterm
  · intro hP
    apply (mem_artinianPolynomialModuleSupported _ _).mpr
    intro k d hd
    have hk : k = 0 := Subsingleton.elim k 0
    subst k
    have hdegree := hP hd
    change artinianPolynomialTermDegree ordinaryDegree (fun _ : Fin 1 => 0)
      ((0 : Fin 1), d) = (degree : ℤ)
    simp only [artinianPolynomialTermDegree, add_zero]
    rw [← finsupp_weight_natCast]
    exact hdegree

/-- A concrete membership test for the ordered image of one degree slice. -/
theorem mem_rankOnePolynomialDegreeOrderedWeightPart_iff
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (degree : ℕ) (hdegree : (degree : ℤ) ≤ D)
    (I : Ideal (MvPolynomial (Fin n) B))
    (x : (i : Fin ((G₁).weightCount hpositive D)) →
      (G₁).orderedWeightPiece B hpositive D i) :
    x ∈ (G₁).rankOnePolynomialDegreeOrderedWeightPart
        hpositive D (degree : ℤ) hdegree I ↔
      (((((G₁).windowOrderedWeightLinearEquiv
          (B := B) hpositive D).symm x :
            (G₁).windowModule B hpositive D) :
          artinianFreePolynomialModule B n 1) 0) ∈ I ∧
      (((((G₁).windowOrderedWeightLinearEquiv
          (B := B) hpositive D).symm x :
            (G₁).windowModule B hpositive D) :
          artinianFreePolynomialModule B n 1) 0).IsWeightedHomogeneous
            (fun i => (ordinaryDegree i : ℤ)) (degree : ℤ) := by
  classical
  let E := (G₁).windowOrderedWeightLinearEquiv (B := B) hpositive D
  constructor
  · rintro ⟨P, hP, rfl⟩
    have hback := (G₁).windowEquiv_symm_ordinaryDegreeEmbedding
      (B := B) hpositive D (degree : ℤ) hdegree P
    have hPI :
        (((P : artinianPolynomialModulePiece (B := B)
            ordinaryDegree (G₁).ordinaryShift (degree : ℤ)) :
          artinianFreePolynomialModule B n 1) 0) ∈ I := by
      change ((P : artinianPolynomialModulePiece (B := B)
        ordinaryDegree (G₁).ordinaryShift (degree : ℤ)) :
          artinianFreePolynomialModule B n 1) ∈
        rankOnePolynomialIdealSubmodule I at hP
      exact (mem_rankOnePolynomialIdealSubmodule_iff I _).mp hP
    constructor
    · rw [hback]
      exact hPI
    · rw [hback]
      exact (rankOne_mem_ordinaryPiece_iff_isWeightedHomogeneous
        ordinaryDegree multiDegree degree
          (P : artinianFreePolynomialModule B n 1)).mp P.property
  · rintro ⟨hxI, hxhom⟩
    let P : artinianPolynomialModulePiece (B := B)
        ordinaryDegree (G₁).ordinaryShift (degree : ℤ) :=
      ⟨((E.symm x : (G₁).windowModule B hpositive D) :
          artinianFreePolynomialModule B n 1),
        (rankOne_mem_ordinaryPiece_iff_isWeightedHomogeneous
          ordinaryDegree multiDegree degree _).mpr hxhom⟩
    refine ⟨P, ?_, ?_⟩
    · change ((P : artinianPolynomialModulePiece (B := B)
        ordinaryDegree (G₁).ordinaryShift (degree : ℤ)) :
          artinianFreePolynomialModule B n 1) ∈
        rankOnePolynomialIdealSubmodule I
      apply (mem_rankOnePolynomialIdealSubmodule_iff I _).mpr
      exact hxI
    · change E (Submodule.inclusion
          ((G₁).ordinaryPiece_le_windowModule
            hpositive D (degree : ℤ) hdegree) P) = x
      exact E.apply_symm_apply x

/-- The fixed-degree analogue of the coordinate-piece characterization.
The extra conjunct records the selected ordinary degree. -/
theorem mem_finiteWeightInitialPiece_rankOnePolynomialDegree_iff
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (degree : ℕ) (hdegree : (degree : ℤ) ≤ D)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun j => (ordinaryDegree j : ℤ))))
    (i : Fin ((G₁).weightCount hpositive D))
    (v : (G₁).orderedWeightPiece B hpositive D i) :
    v ∈ finiteWeightInitialPiece
        ((G₁).rankOnePolynomialDegreeOrderedWeightPart
          hpositive D (degree : ℤ) hdegree I) i ↔
        ((v : artinianFreePolynomialModule B n 1) 0) ∈
          lexicographicInitialIdeal multiDegree I ∧
        ((v : artinianFreePolynomialModule B n 1) 0).IsWeightedHomogeneous
          (fun j => (ordinaryDegree j : ℤ)) (degree : ℤ) := by
  classical
  let E := (G₁).windowOrderedWeightLinearEquiv (B := B) hpositive D
  constructor
  · rintro ⟨x, hx, hxv⟩
    have hxslice :=
      (mem_rankOnePolynomialDegreeOrderedWeightPart_iff
        ordinaryDegree multiDegree hpositive D degree hdegree I x).mp hx.1
    have hxwhole : x ∈
        (G₁).polynomialWindowOrderedWeightPart hpositive D
          (rankOnePolynomialIdealSubmodule I) := by
      apply ((G₁).mem_polynomialWindowOrderedWeightPart_rankOneIdeal_iff
        hpositive D I x).mpr
      exact hxslice.1
    have hvwhole : v ∈ finiteWeightInitialPiece
        ((G₁).polynomialWindowOrderedWeightPart hpositive D
          (rankOnePolynomialIdealSubmodule I)) i := by
      exact ⟨x, ⟨hxwhole, hx.2⟩, hxv⟩
    have hvI :=
      (mem_finiteWeightInitialPiece_polynomialWindow_rankOne_iff
        ordinaryDegree multiDegree hpositive D I hI i v).mp hvwhole
    change x i = v at hxv
    let P : (G₁).windowModule B hpositive D := E.symm x
    have hEP : E P = x := E.apply_symm_apply x
    have hPordinary :
        ((P : artinianFreePolynomialModule B n 1) 0).IsWeightedHomogeneous
          (fun j => (ordinaryDegree j : ℤ)) (degree : ℤ) := hxslice.2
    have hvordinary :
        ((v : artinianFreePolynomialModule B n 1) 0).IsWeightedHomogeneous
          (fun j => (ordinaryDegree j : ℤ)) (degree : ℤ) := by
      rw [← hxv, ← hEP,
        rankOne_windowOrderedWeightLinearEquiv_apply_zero]
      exact weightedHomogeneousComponent_preserves_homogeneity
        (fun j => toLex (multiDegree j))
        (fun j => (ordinaryDegree j : ℤ))
        ((G₁).weightAt hpositive D i) hPordinary
    exact ⟨hvI, hvordinary⟩
  · rintro ⟨hvI, hvordinary⟩
    have hvmulti := rankOne_windowWeightPiece_isWeightedHomogeneous
      ordinaryDegree multiDegree hpositive D
      ((G₁).weightAt hpositive D i) v
    obtain ⟨f, hfI, hfordinary, hfbound, hfcomponent⟩ :=
      exists_secondaryHomogeneous_component_lift_lexicographicInitialIdeal
        (fun j => (ordinaryDegree j : ℤ)) multiDegree I hI
        hvI hvmulti hvordinary
    have hPordinary : rankOnePolynomialModuleCoeffEquiv f ∈
        artinianPolynomialModulePiece (B := B)
          ordinaryDegree (G₁).ordinaryShift (degree : ℤ) :=
      (rankOne_mem_ordinaryPiece_iff_isWeightedHomogeneous
        ordinaryDegree multiDegree degree _).mpr hfordinary
    let P : (G₁).windowModule B hpositive D :=
      ⟨rankOnePolynomialModuleCoeffEquiv f,
        (G₁).ordinaryPiece_le_windowModule hpositive D
          (degree : ℤ) hdegree hPordinary⟩
    refine ⟨E P, ⟨?_, ?_⟩, ?_⟩
    · apply (mem_rankOnePolynomialDegreeOrderedWeightPart_iff
        ordinaryDegree multiDegree hpositive D degree hdegree I (E P)).mpr
      rw [E.symm_apply_apply]
      exact ⟨hfI, hfordinary⟩
    · apply (rankOne_finiteWeightPrefixProjection_eq_zero_iff_support_bound
        ordinaryDegree multiDegree hpositive D P i).mpr
      simpa only [P, rankOnePolynomialModuleCoeffEquiv_apply] using hfbound
    · change E P i = v
      apply Subtype.ext
      funext k
      have hk : k = 0 := Subsingleton.elim k 0
      subst k
      calc
        (((E P i : (G₁).orderedWeightPiece B hpositive D i) :
              artinianFreePolynomialModule B n 1) 0) =
            MvPolynomial.weightedHomogeneousComponent
              (fun j => toLex (multiDegree j))
              ((G₁).weightAt hpositive D i) f := by
          simpa only [P, rankOnePolynomialModuleCoeffEquiv_apply] using
            rankOne_windowOrderedWeightLinearEquiv_apply_zero
              ordinaryDegree multiDegree hpositive D P i
        _ = ((v : artinianFreePolynomialModule B n 1) 0) := hfcomponent

/-- Lexicographic initial formation commutes with finite-weight initial
formation on the ordered image of every fixed ordinary degree. -/
theorem rankOnePolynomialDegreeOrderedWeightPart_lexicographicInitialIdeal
    (hpositive : ∀ i, 0 < ordinaryDegree i) (D : ℤ)
    (degree : ℕ) (hdegree : (degree : ℤ) ≤ D)
    (I : Ideal (MvPolynomial (Fin n) B))
    (hI : I.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun j => (ordinaryDegree j : ℤ)))) :
    (G₁).rankOnePolynomialDegreeOrderedWeightPart
        hpositive D (degree : ℤ) hdegree
        (lexicographicInitialIdeal multiDegree I) =
      finiteWeightInitial
        ((G₁).rankOnePolynomialDegreeOrderedWeightPart
          hpositive D (degree : ℤ) hdegree I) := by
  classical
  let E := (G₁).windowOrderedWeightLinearEquiv (B := B) hpositive D
  apply le_antisymm
  · intro x hx
    apply (mem_finiteWeightInitial_iff _ x).mpr
    intro i
    apply (mem_finiteWeightInitialPiece_rankOnePolynomialDegree_iff
      ordinaryDegree multiDegree hpositive D degree hdegree I hI i (x i)).mpr
    have hxslice :=
      (mem_rankOnePolynomialDegreeOrderedWeightPart_iff
        ordinaryDegree multiDegree hpositive D degree hdegree
        (lexicographicInitialIdeal multiDegree I) x).mp hx
    let P : (G₁).windowModule B hpositive D := E.symm x
    have hEP : E P = x := E.apply_symm_apply x
    have hxcomponent := lexicographicInitialIdeal_component_mem
      multiDegree I hxslice.1 ((G₁).weightAt hpositive D i)
    have hxordinary :
        ((x i : artinianFreePolynomialModule B n 1) 0).IsWeightedHomogeneous
          (fun j => (ordinaryDegree j : ℤ)) (degree : ℤ) := by
      rw [← hEP,
        rankOne_windowOrderedWeightLinearEquiv_apply_zero]
      exact weightedHomogeneousComponent_preserves_homogeneity
        (fun j => toLex (multiDegree j))
        (fun j => (ordinaryDegree j : ℤ))
        ((G₁).weightAt hpositive D i) hxslice.2
    have hcoordinate : ((x i : (G₁).orderedWeightPiece B hpositive D i) :
          artinianFreePolynomialModule B n 1) 0 =
        MvPolynomial.weightedHomogeneousComponent
          (fun j => toLex (multiDegree j))
          ((G₁).weightAt hpositive D i)
          ((P : artinianFreePolynomialModule B n 1) 0) := by
      rw [← hEP]
      exact rankOne_windowOrderedWeightLinearEquiv_apply_zero
        ordinaryDegree multiDegree hpositive D P i
    rw [← hcoordinate] at hxcomponent
    exact ⟨hxcomponent, hxordinary⟩
  · intro x hx
    rw [← LinearMap.sum_single_apply
      (fun i : Fin ((G₁).weightCount hpositive D) =>
        (G₁).orderedWeightPiece B hpositive D i) x]
    apply Submodule.sum_mem
    intro i hi
    apply (mem_rankOnePolynomialDegreeOrderedWeightPart_iff
      ordinaryDegree multiDegree hpositive D degree hdegree
      (lexicographicInitialIdeal multiDegree I) (Pi.single i (x i))).mpr
    have hipiece := (mem_finiteWeightInitial_iff _ x).mp hx i
    have hi :=
      (mem_finiteWeightInitialPiece_rankOnePolynomialDegree_iff
        ordinaryDegree multiDegree hpositive D degree hdegree
        I hI i (x i)).mp hipiece
    rw [(G₁).windowOrderedWeightLinearEquiv_symm_single_coe]
    exact hi

end CanonicalRankOneGrading

end AbelFormalization
