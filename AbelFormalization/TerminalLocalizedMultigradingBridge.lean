import AbelFormalization.TerminalMultiblockElimination
import AbelFormalization.TerminalGlobalStirling
import AbelFormalization.WeightedGroupEvaluation
import AbelFormalization.GroupLaurentWeightedIdeal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Global multigrading after simultaneous terminal localization

Commuting the polynomial and Laurent layers and then applying the positive
higher-variable shear turns the simultaneous localization into an ordinary
group-weighted evaluation.  Global component closure therefore transports to
the exact localized multigrading used by terminal multiblock elimination.
-/

noncomputable section

namespace AbelFormalization

universe u v

attribute [local instance] MvPolynomial.weightedGradedAlgebra

@[simp]
theorem algEquiv_toRingEquiv_toRingHom_apply
    {S A B : Type*} [CommSemiring S] [CommSemiring A] [CommSemiring B]
    [Algebra S A] [Algebra S B] (e : A ≃ₐ[S] B) (x : A) :
    e.toRingEquiv.toRingHom x = e x :=
  rfl

/-- Polynomial higher-variable coefficients after commuting the two monoid
algebra layers. -/
abbrev TerminalMultiblockPolynomialCoefficientRing
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :=
  MvPolynomial (TerminalMultiblockHigherIndex h d)
    (TerminalMultiblockRetainedRing R Keep)

/-- The global natural source weight embedded into the integer Laurent
multidegree. -/
def terminalMultiblockSourceWeight
    (h : ℕ) (d : Fin h → ℕ) (Keep : Type*)
    (x : TerminalMultiblockSourceIndex h d Keep) :
    TerminalMultiblockDegree h :=
  finiteLaurentExponentHom h
    (terminalGlobalWeight (Fin h) (fun b ↦ d b + 1) Keep x)

@[simp]
theorem terminalMultiblockSourceWeight_first
    (h : ℕ) (d : Fin h → ℕ) (Keep : Type*) (b : Fin h) :
    terminalMultiblockSourceWeight h d Keep
        (Sum.inl ⟨b, (0 : Fin (d b + 1))⟩) =
      terminalMultiblockFirstExponent h b := by
  rfl

@[simp]
theorem terminalMultiblockSourceWeight_higher
    (h : ℕ) (d : Fin h → ℕ) (Keep : Type*)
    (b : Fin h) (j : Fin (d b)) :
    terminalMultiblockSourceWeight h d Keep
        (Sum.inl ⟨b, j.succ⟩) =
      terminalMultiblockHigherWeight h d ⟨b, j⟩ := by
  funext c
  by_cases hbc : b = c
  · subst c
    simp [terminalMultiblockSourceWeight, terminalGlobalWeight,
      terminalMultiblockHigherWeight, terminalMultiblockFirstExponent]
    omega
  · simp [terminalMultiblockSourceWeight, terminalGlobalWeight,
      terminalMultiblockHigherWeight, terminalMultiblockFirstExponent,
      hbc]

@[simp]
theorem terminalMultiblockSourceWeight_keep
    (h : ℕ) (d : Fin h → ℕ) (Keep : Type*) (k : Keep) :
    terminalMultiblockSourceWeight h d Keep (Sum.inr k) = 0 := by
  simp [terminalMultiblockSourceWeight]

/-- The coefficient-polynomial part of every source variable after
localization and positive shear. -/
def terminalMultiblockPolynomialVariableImage
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    TerminalMultiblockSourceIndex h d Keep →
      TerminalMultiblockPolynomialCoefficientRing R Keep h d
  | Sum.inl ⟨b, r⟩ =>
      Fin.cases
        (1 : TerminalMultiblockPolynomialCoefficientRing R Keep h d)
        (fun j ↦ MvPolynomial.X
          (⟨b, j⟩ : TerminalMultiblockHigherIndex h d)) r
  | Sum.inr k => MvPolynomial.C (MvPolynomial.X k)

@[simp]
theorem terminalMultiblockPolynomialVariableImage_first
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) (b : Fin h) :
    terminalMultiblockPolynomialVariableImage R Keep h d
        (Sum.inl ⟨b, (0 : Fin (d b + 1))⟩) = 1 :=
  rfl

@[simp]
theorem terminalMultiblockPolynomialVariableImage_higher
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) (b : Fin h) (j : Fin (d b)) :
    terminalMultiblockPolynomialVariableImage R Keep h d
        (Sum.inl ⟨b, j.succ⟩) =
      MvPolynomial.X
        (⟨b, j⟩ : TerminalMultiblockHigherIndex h d) :=
  rfl

@[simp]
theorem terminalMultiblockPolynomialVariableImage_keep
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) (k : Keep) :
    terminalMultiblockPolynomialVariableImage R Keep h d (Sum.inr k) =
      MvPolynomial.C (MvPolynomial.X k) :=
  rfl

/-- Scalars included into the retained-polynomial then higher-polynomial
coefficient ring. -/
def terminalMultiblockPolynomialBaseMap
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    R →+* TerminalMultiblockPolynomialCoefficientRing R Keep h d :=
  (MvPolynomial.C :
      TerminalMultiblockRetainedRing R Keep →+*
        TerminalMultiblockPolynomialCoefficientRing R Keep h d).comp
    (MvPolynomial.C : R →+* TerminalMultiblockRetainedRing R Keep)

/-- The total-grading presentation: commute the monoid-algebra layers and
then shear a higher monomial by its positive global weight. -/
def terminalMultiblockTotalGradingEquiv
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    TerminalMultiblockLocalizedRing R Keep h d ≃ₐ[
      TerminalMultiblockRetainedRing R Keep]
      AddMonoidAlgebra
        (TerminalMultiblockPolynomialCoefficientRing R Keep h d)
        (TerminalMultiblockDegree h) :=
  (terminalMultiblockPolynomialLaurentEquiv R Keep h d).trans
    (groupLaurentWeightRescaling
      (R := TerminalMultiblockRetainedRing R Keep)
      (terminalMultiblockHigherWeight h d))

/-- Simultaneous localization expressed in its total integer grading. -/
def terminalMultiblockTotalGradingLocalizationHom
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    TerminalMultiblockSourceRing R h d Keep →+*
      AddMonoidAlgebra
        (TerminalMultiblockPolynomialCoefficientRing R Keep h d)
        (TerminalMultiblockDegree h) :=
  (terminalMultiblockTotalGradingEquiv R Keep h d).toRingHom.comp
    (terminalMultiblockLocalizationHom R Keep h d)

/-- The rescaled simultaneous localization is the literal weighted group
evaluation of the source variables. -/
theorem terminalMultiblockTotalGradingLocalizationHom_eq_evaluation
    (R Keep : Type*) [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) :
    terminalMultiblockTotalGradingLocalizationHom R Keep h d =
      weightedGroupEvaluation
        (terminalMultiblockPolynomialBaseMap R Keep h d)
        (terminalMultiblockPolynomialVariableImage R Keep h d)
        (terminalMultiblockSourceWeight h d Keep) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [terminalMultiblockTotalGradingLocalizationHom,
      terminalMultiblockTotalGradingEquiv,
      terminalMultiblockPolynomialLaurentEquiv,
      algEquiv_toRingEquiv_toRingHom_apply, AlgEquiv.trans_apply,
      RingHom.comp_apply,
      terminalMultiblockLocalizationHom_C,
      groupAlgebraC_apply,
      weightedGroupEvaluation_C,
      terminalMultiblockPolynomialBaseMap]
    simp only [MvPolynomial.C_apply,
      ← MvPolynomial.single_eq_monomial,
      AddMonoidAlgebra.commAlgEquiv_single_single]
    exact groupLaurentWeightRescaling_single_C
      (terminalMultiblockHigherWeight h d)
      (AddMonoidAlgebra.single 0 r)
  · rintro (⟨b, r⟩ | k)
    · refine Fin.cases ?_ (fun j ↦ ?_) r
      · simp only [terminalMultiblockTotalGradingLocalizationHom,
          terminalMultiblockTotalGradingEquiv,
          terminalMultiblockPolynomialLaurentEquiv,
          algEquiv_toRingEquiv_toRingHom_apply, AlgEquiv.trans_apply,
          RingHom.comp_apply,
          terminalMultiblockLocalizationHom_X_first,
          weightedGroupEvaluation_X,
          terminalMultiblockPolynomialVariableImage_first,
          terminalMultiblockSourceWeight_first]
        simp only [terminalMultiblockFirstVariable,
          MvPolynomial.C_apply,
          ← MvPolynomial.single_eq_monomial,
          AddMonoidAlgebra.commAlgEquiv_single_single]
        exact groupLaurentWeightRescaling_single_one
          (R := TerminalMultiblockRetainedRing R Keep)
          (terminalMultiblockHigherWeight h d)
          (terminalMultiblockFirstExponent h b)
      · simp only [terminalMultiblockTotalGradingLocalizationHom,
          terminalMultiblockTotalGradingEquiv,
          terminalMultiblockPolynomialLaurentEquiv,
          algEquiv_toRingEquiv_toRingHom_apply, AlgEquiv.trans_apply,
          RingHom.comp_apply,
          terminalMultiblockLocalizationHom_X_higher,
          weightedGroupEvaluation_X,
          terminalMultiblockPolynomialVariableImage_higher,
          terminalMultiblockSourceWeight_higher]
        simp only [MvPolynomial.X,
          ← MvPolynomial.single_eq_monomial,
          AddMonoidAlgebra.commAlgEquiv_single_zero]
        exact groupLaurentWeightRescaling_single_X
          (R := TerminalMultiblockRetainedRing R Keep)
          (terminalMultiblockHigherWeight h d) ⟨b, j⟩
    · simp only [terminalMultiblockTotalGradingLocalizationHom,
        terminalMultiblockTotalGradingEquiv,
        terminalMultiblockPolynomialLaurentEquiv,
        algEquiv_toRingEquiv_toRingHom_apply, AlgEquiv.trans_apply,
        RingHom.comp_apply,
        terminalMultiblockLocalizationHom_X_keep,
        groupAlgebraC_apply,
        weightedGroupEvaluation_X,
        terminalMultiblockPolynomialVariableImage_keep,
        terminalMultiblockSourceWeight_keep]
      simp only [MvPolynomial.C_apply,
        ← MvPolynomial.single_eq_monomial,
        AddMonoidAlgebra.commAlgEquiv_single_single]
      exact groupLaurentWeightRescaling_single_C
        (terminalMultiblockHigherWeight h d) (MvPolynomial.X k)

/-- The integer source weight of a monomial is the natural global weight
embedded coordinatewise into the Laurent degree group. -/
theorem terminalMultiblockSourceWeight_weight
    (h : ℕ) (d : Fin h → ℕ) (Keep : Type*)
    (m : TerminalMultiblockSourceIndex h d Keep →₀ ℕ) :
    Finsupp.weight (terminalMultiblockSourceWeight h d Keep) m =
      finiteLaurentExponentHom h
        (Finsupp.weight
          (terminalGlobalWeight (Fin h) (fun b ↦ d b + 1) Keep) m) := by
  classical
  induction m using Finsupp.induction with
  | zero => simp
  | @single_add x n m hx hn ih =>
      simp [Finsupp.weight_single, terminalMultiblockSourceWeight, ih]

/-- A globally weighted-homogeneous source polynomial stays homogeneous after
embedding its natural multidegree into the Laurent degree group. -/
theorem terminalGlobal_isWeightedHomogeneous_sourceWeight
    {R : Type*} [CommRing R]
    (h : ℕ) (d : Fin h → ℕ) (Keep : Type*)
    {P : TerminalMultiblockSourceRing R h d Keep}
    {degree : TerminalMultidegree (Fin h)}
    (hP : P.IsWeightedHomogeneous
      (terminalGlobalWeight (Fin h) (fun b ↦ d b + 1) Keep) degree) :
    P.IsWeightedHomogeneous
      (terminalMultiblockSourceWeight h d Keep)
      (finiteLaurentExponentHom h degree) := by
  intro m hm
  rw [terminalMultiblockSourceWeight_weight]
  exact congrArg (finiteLaurentExponentHom h) (hP hm)

/-- Under the total-grading presentation, the image of a globally
multigraded ideal is an ordinary homogeneous ideal in the group algebra. -/
theorem terminalMultiblockTotalGradingMappedIdeal_isHomogeneous
    {R Keep : Type*} [CommRing R]
    {h : ℕ} {d : Fin h → ℕ}
    (I : Ideal (TerminalMultiblockSourceRing R h d Keep))
    (hgraded : IsTerminalMultigradedIdeal R (Fin h)
      (fun b ↦ d b + 1) Keep I) :
    (I.map (terminalMultiblockTotalGradingLocalizationHom R Keep h d)).IsHomogeneous
      (AddMonoidAlgebra.grade
        (TerminalMultiblockPolynomialCoefficientRing R Keep h d)) := by
  classical
  have hIhom : I.IsHomogeneous
    (MvPolynomial.weightedHomogeneousSubmodule R
        (terminalGlobalWeight (Fin h) (fun b ↦ d b + 1) Keep)) := by
    intro degree P hP
    rw [← DirectSum.Decomposition.decompose'_eq]
    rw [MvPolynomial.weightedDecomposition.decompose'_apply]
    exact hgraded P hP degree
  obtain ⟨S, hS⟩ :=
    (Ideal.IsHomogeneous.iff_exists
      (MvPolynomial.weightedHomogeneousSubmodule R
        (terminalGlobalWeight (Fin h) (fun b ↦ d b + 1) Keep)) I).mp hIhom
  rw [terminalMultiblockTotalGradingLocalizationHom_eq_evaluation, hS]
  apply weightedGroupEvaluation_span_isHomogeneous
  rintro P ⟨Q, _, rfl⟩
  obtain ⟨degree, hdegree⟩ := Q.property
  refine ⟨finiteLaurentExponentHom h degree, ?_⟩
  exact terminalGlobal_isWeightedHomogeneous_sourceWeight h d Keep hdegree

/-- Commuting the polynomial and Laurent layers swaps their two coefficient
indices exactly. -/
@[simp]
theorem terminalMultiblockPolynomialLaurentEquiv_coeff_coeff
    {R Keep : Type*} [CommRing R]
    {h : ℕ} {d : Fin h → ℕ}
    (P : TerminalMultiblockLocalizedRing R Keep h d)
    (g : TerminalMultiblockDegree h)
    (m : TerminalMultiblockHigherIndex h d →₀ ℕ) :
    (((terminalMultiblockPolynomialLaurentEquiv R Keep h d P).coeff g).coeff m) =
      ((P.coeff m).coeff g) := by
  simp [terminalMultiblockPolynomialLaurentEquiv,
    AddMonoidAlgebra.commAlgEquiv,
    AddMonoidAlgebra.curryAlgEquiv,
    AddMonoidAlgebra.curryRingEquiv,
    AddMonoidAlgebra.curryAddEquiv]

open scoped Classical in
/-- Coefficients of the explicit localized component are retained exactly
when their Laurent degree plus higher-monomial weight is the target degree. -/
@[simp]
theorem terminalMultiblockLocalizedComponent_coeff_coeff
    {R Keep : Type*} [CommRing R]
    {h : ℕ} {d : Fin h → ℕ}
    (degree : TerminalMultiblockDegree h)
    (P : TerminalMultiblockLocalizedRing R Keep h d)
    (m : TerminalMultiblockHigherIndex h d →₀ ℕ)
    (g : TerminalMultiblockDegree h) :
    ((terminalMultiblockLocalizedComponent R Keep h d degree P).coeff m).coeff g =
      if g + Finsupp.weight (terminalMultiblockHigherWeight h d) m = degree
      then (P.coeff m).coeff g else 0 := by
  classical
  have houter :
      (terminalMultiblockLocalizedComponent R Keep h d degree P).coeff m =
        if m ∈ P.support then
          AddMonoidAlgebra.single
            (degree - Finsupp.weight (terminalMultiblockHigherWeight h d) m)
            ((P.coeff m).coeff
              (degree - Finsupp.weight
                (terminalMultiblockHigherWeight h d) m))
        else 0 := by
    simp only [terminalMultiblockLocalizedComponent,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
      Finset.sum_ite_eq']
  rw [houter]
  by_cases hm : m ∈ P.support
  · simp only [hm, if_pos, AddMonoidAlgebra.coeff_single_apply]
    by_cases hw : g + Finsupp.weight
        (terminalMultiblockHigherWeight h d) m = degree
    · have hs : degree - Finsupp.weight
          (terminalMultiblockHigherWeight h d) m = g :=
        (sub_eq_iff_eq_add).2 hw.symm
      simp [hw, hs]
    · have hs : degree - Finsupp.weight
          (terminalMultiblockHigherWeight h d) m ≠ g := by
        intro hs
        apply hw
        exact (sub_eq_iff_eq_add.mp hs).symm
      simp [hw, hs]
  · have hzero : P.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hm
    simp [hm, hzero]

/-- The layer-commuting equivalence sends the explicit localized component
to the corresponding total-weight component before shearing. -/
theorem terminalMultiblockPolynomialLaurentEquiv_localizedComponent
    {R Keep : Type*} [CommRing R]
    {h : ℕ} {d : Fin h → ℕ}
    (degree : TerminalMultiblockDegree h)
    (P : TerminalMultiblockLocalizedRing R Keep h d) :
    terminalMultiblockPolynomialLaurentEquiv R Keep h d
        (terminalMultiblockLocalizedComponent R Keep h d degree P) =
      groupLaurentWeightComponent
        (terminalMultiblockHigherWeight h d) degree
        (terminalMultiblockPolynomialLaurentEquiv R Keep h d P) := by
  classical
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro g
  apply MvPolynomial.ext
  intro m
  simp only [terminalMultiblockPolynomialLaurentEquiv_coeff_coeff,
    terminalMultiblockLocalizedComponent_coeff_coeff,
    groupLaurentWeightComponent_coeff]

/-- After the positive shear, the explicit localized component is the single
ordinary group-algebra component of the total-grading presentation. -/
@[simp]
theorem terminalMultiblockTotalGradingEquiv_localizedComponent
    {R Keep : Type*} [CommRing R]
    {h : ℕ} {d : Fin h → ℕ}
    (degree : TerminalMultiblockDegree h)
    (P : TerminalMultiblockLocalizedRing R Keep h d) :
    terminalMultiblockTotalGradingEquiv R Keep h d
        (terminalMultiblockLocalizedComponent R Keep h d degree P) =
      AddMonoidAlgebra.single degree
        ((terminalMultiblockTotalGradingEquiv R Keep h d P).coeff degree) := by
  change groupLaurentWeightRescaling
      (R := TerminalMultiblockRetainedRing R Keep)
      (terminalMultiblockHigherWeight h d)
      (terminalMultiblockPolynomialLaurentEquiv R Keep h d
        (terminalMultiblockLocalizedComponent R Keep h d degree P)) =
    AddMonoidAlgebra.single degree
      ((groupLaurentWeightRescaling
        (R := TerminalMultiblockRetainedRing R Keep)
        (terminalMultiblockHigherWeight h d)
        (terminalMultiblockPolynomialLaurentEquiv R Keep h d P)).coeff degree)
  rw [terminalMultiblockPolynomialLaurentEquiv_localizedComponent,
    groupLaurentWeightComponent_rescaling]

/-- In a homogeneous group-algebra ideal, every single coefficient component
of every member is again in the ideal. -/
theorem groupAlgebra_single_coeff_mem_of_isHomogeneous
    {A G : Type*} [CommRing A] [AddCommGroup G] [DecidableEq G]
    (J : Ideal (AddMonoidAlgebra A G))
    (hJ : J.IsHomogeneous (AddMonoidAlgebra.grade A))
    {f : AddMonoidAlgebra A G} (hf : f ∈ J) (g : G) :
    AddMonoidAlgebra.single g (f.coeff g) ∈ J := by
  have hc := groupAlgebra_homogeneousIdeal_coeff_mem J hJ hf g
  change groupAlgebraC A G (f.coeff g) ∈ J at hc
  simpa only [groupAlgebraC_apply,
    AddMonoidAlgebra.single_mul_single, add_zero, one_mul] using
    J.mul_mem_left (AddMonoidAlgebra.single g 1) hc

/-- Global terminal multigrading supplies the precise component closure needed
after simultaneous localization in every terminal block. -/
theorem terminalMultiblockLocalizationHom_map_isMultigraded
    {R Keep : Type*} [CommRing R]
    {h : ℕ} {d : Fin h → ℕ}
    (I : Ideal (TerminalMultiblockSourceRing R h d Keep))
    (hgraded : IsTerminalMultigradedIdeal R (Fin h)
      (fun b ↦ d b + 1) Keep I) :
    IsTerminalMultiblockLocalizedMultigraded R Keep h d
      (I.map (terminalMultiblockLocalizationHom R Keep h d)) := by
  classical
  let E := terminalMultiblockTotalGradingEquiv R Keep h d
  let K := I.map (terminalMultiblockLocalizationHom R Keep h d)
  have hmap : K.map E.toRingHom =
      I.map (terminalMultiblockTotalGradingLocalizationHom R Keep h d) := by
    change
      (I.map (terminalMultiblockLocalizationHom R Keep h d)).map
          (terminalMultiblockTotalGradingEquiv R Keep h d).toRingHom = _
    rw [Ideal.map_map]
    rfl
  have hhom : (K.map E.toRingHom).IsHomogeneous
      (AddMonoidAlgebra.grade
        (TerminalMultiblockPolynomialCoefficientRing R Keep h d)) := by
    rw [hmap]
    exact terminalMultiblockTotalGradingMappedIdeal_isHomogeneous I hgraded
  intro P hP degree
  have hEP : E P ∈ K.map E.toRingHom :=
    Ideal.mem_map_of_mem E.toRingHom hP
  have hsingle : AddMonoidAlgebra.single degree ((E P).coeff degree) ∈
      K.map E.toRingHom :=
    groupAlgebra_single_coeff_mem_of_isHomogeneous
      (K.map E.toRingHom) hhom hEP degree
  apply (Ideal.apply_mem_of_equiv_iff
    (I := K) (f := E.toRingEquiv)
    (x := terminalMultiblockLocalizedComponent R Keep h d degree P)).mp
  change E (terminalMultiblockLocalizedComponent R Keep h d degree P) ∈
    K.map E.toRingHom
  rw [terminalMultiblockTotalGradingEquiv_localizedComponent]
  exact hsingle

end AbelFormalization
