import AbelFormalization.TransferInitialCertificate
import AbelFormalization.TerminalGlobalParameterDeformation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Central deformation after adjoining unused representative variables

This scratch module proves the algebraic simplification used after a cluster's
representative variables have already been removed.  We adjoin fresh variables
through `Sum.inr`, give those fresh variables the negative standard weights,
and give the retained derivative variables their positive terminal weights.

The main input is an arbitrary ideal in the retained polynomial ring.  No
Noetherianity, finiteness, domain, or characteristic assumption is used in the
initial-ideal or contraction equalities.  Finiteness and Noetherianity enter
only in the optional height statement for polynomial extension.
-/

noncomputable section

namespace AbelFormalization

universe u v w

/-! ## Polynomial extension along the right summand -/

variable {R Q X : Type*} [CommRing R]

/-- Extend an ideal by a disjoint family `Q` of unused polynomial variables. -/
def unusedPolynomialExtension (Q : Type*)
    (K : Ideal (MvPolynomial X R)) :
    Ideal (MvPolynomial (Q ⊕ X) R) :=
  K.map (MvPolynomial.rename (Sum.inr : X → Q ⊕ X))

/-- Regrouping the unused variables as outer polynomial variables identifies
the right-summand extension with ordinary coefficient extension. -/
theorem unusedPolynomialExtension_map_sumAlgEquiv
    (K : Ideal (MvPolynomial X R)) :
    (unusedPolynomialExtension Q K).map
        (MvPolynomial.sumAlgEquiv R Q X).toRingHom =
      K.map (MvPolynomial.C :
        MvPolynomial X R →+* MvPolynomial Q (MvPolynomial X R)) := by
  change
    (K.map
      (MvPolynomial.rename (Sum.inr : X → Q ⊕ X)).toRingHom).map
        (MvPolynomial.sumAlgEquiv R Q X).toRingHom = _
  rw [Ideal.map_map]
  change K.map
      ((MvPolynomial.sumAlgEquiv R Q X).toAlgHom.comp
        (MvPolynomial.rename (Sum.inr : X → Q ⊕ X))).toRingHom =
    K.map (MvPolynomial.C :
      MvPolynomial X R →+* MvPolynomial Q (MvPolynomial X R))
  rw [MvPolynomial.sumAlgEquiv_comp_rename_inr]
  rfl

/-- Membership in the unused-variable extension is coefficientwise after
regrouping by `sumAlgEquiv`. -/
theorem mem_unusedPolynomialExtension_iff
    (K : Ideal (MvPolynomial X R)) (P : MvPolynomial (Q ⊕ X) R) :
    P ∈ unusedPolynomialExtension Q K ↔
      ∀ a : Q →₀ ℕ,
        ((MvPolynomial.sumAlgEquiv R Q X P).coeff a) ∈ K := by
  have he :
      MvPolynomial.sumAlgEquiv R Q X P ∈
          (unusedPolynomialExtension Q K).map
            (MvPolynomial.sumAlgEquiv R Q X).toRingHom ↔
        P ∈ unusedPolynomialExtension Q K :=
    Ideal.apply_mem_of_equiv_iff
  rw [← he, unusedPolynomialExtension_map_sumAlgEquiv,
    MvPolynomial.mem_map_C_iff]

/-- A translation of only the unused coordinates preserves the extended
ideal.  This includes the paper's change `x_i ↦ q_i - 1`. -/
theorem polynomialCoordinateTranslation_unusedPolynomialExtension
    (c : Q → R) (K : Ideal (MvPolynomial X R)) :
    (unusedPolynomialExtension Q K).map
        (polynomialCoordinateTranslation
          (Sum.elim c (fun _ : X ↦ 0))).toRingHom =
      unusedPolynomialExtension Q K := by
  change
    (K.map
      (MvPolynomial.rename (Sum.inr : X → Q ⊕ X)).toRingHom).map
        (polynomialCoordinateTranslation
          (Sum.elim c (fun _ : X ↦ 0))).toRingHom =
      K.map (MvPolynomial.rename (Sum.inr : X → Q ⊕ X)).toRingHom
  rw [Ideal.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp

/-! ## Initial ideals commute with adjoining independently weighted variables -/

variable {n : ℕ}

private theorem sumWeight_join
    (qWeight : Q → Fin n → ℤ) (xWeight : X → Fin n → ℤ)
    (a : Q →₀ ℕ) (d : X →₀ ℕ) :
    Finsupp.weight
        (fun i : Q ⊕ X ↦ toLex (Sum.elim qWeight xWeight i))
        ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm (a, d)) =
      Finsupp.weight (fun i ↦ toLex (qWeight i)) a +
        Finsupp.weight (fun i ↦ toLex (xWeight i)) d := by
  classical
  change Finsupp.linearCombination ℕ
      (fun i : Q ⊕ X ↦ toLex (Sum.elim qWeight xWeight i))
        (Finsupp.sumElim a d) =
    Finsupp.linearCombination ℕ (fun i : Q ↦ toLex (qWeight i)) a +
      Finsupp.linearCombination ℕ (fun i : X ↦ toLex (xWeight i)) d
  rw [Finsupp.sumElim_eq_add, map_add,
    Finsupp.linearCombination_mapDomain,
    Finsupp.linearCombination_mapDomain]
  rfl

private theorem sumWeight_mapDomain_inr
    (qWeight : Q → Fin n → ℤ) (xWeight : X → Fin n → ℤ)
    (d : X →₀ ℕ) :
    Finsupp.weight
        (fun i : Q ⊕ X ↦ toLex (Sum.elim qWeight xWeight i))
        (d.mapDomain (Sum.inr : X → Q ⊕ X)) =
      Finsupp.weight (fun i ↦ toLex (xWeight i)) d := by
  classical
  change Finsupp.linearCombination ℕ
      (fun i : Q ⊕ X ↦ toLex (Sum.elim qWeight xWeight i))
        (d.mapDomain (Sum.inr : X → Q ⊕ X)) =
    Finsupp.linearCombination ℕ (fun i : X ↦ toLex (xWeight i)) d
  rw [Finsupp.linearCombination_mapDomain]
  rfl

private theorem lexicographicMinimumWeight_rename_inr
    (qWeight : Q → Fin n → ℤ) (xWeight : X → Fin n → ℤ)
    (f : MvPolynomial X R) :
    lexicographicMinimumWeight (Sum.elim qWeight xWeight)
        (MvPolynomial.rename (Sum.inr : X → Q ⊕ X) f) =
      lexicographicMinimumWeight xWeight f := by
  classical
  by_cases hf : f = 0
  · subst f
    simp
  have hrename :
      MvPolynomial.rename (Sum.inr : X → Q ⊕ X) f ≠ 0 := by
    intro hz
    apply hf
    apply MvPolynomial.rename_injective
      (Sum.inr : X → Q ⊕ X) Sum.inr_injective
    simpa using hz
  apply le_antisymm
  · obtain ⟨d, hd, hweight⟩ :=
      exists_support_lexicographicWeight_eq_minimum xWeight hf
    have hdmap : d.mapDomain (Sum.inr : X → Q ⊕ X) ∈
        (MvPolynomial.rename (Sum.inr : X → Q ⊕ X) f).support := by
      rw [MvPolynomial.support_rename_of_injective Sum.inr_injective]
      exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
    calc
      lexicographicMinimumWeight (Sum.elim qWeight xWeight)
          (MvPolynomial.rename (Sum.inr : X → Q ⊕ X) f) ≤
          Finsupp.weight
            (fun i : Q ⊕ X ↦ toLex (Sum.elim qWeight xWeight i))
            (d.mapDomain (Sum.inr : X → Q ⊕ X)) :=
        lexicographicMinimumWeight_le _ _ hdmap
      _ = Finsupp.weight (fun i ↦ toLex (xWeight i)) d :=
        sumWeight_mapDomain_inr qWeight xWeight d
      _ = lexicographicMinimumWeight xWeight f := hweight
  · obtain ⟨e, he, hweight⟩ :=
      exists_support_lexicographicWeight_eq_minimum
        (Sum.elim qWeight xWeight) hrename
    obtain ⟨d, hdmap, hd⟩ :=
      MvPolynomial.coeff_rename_ne_zero
        (Sum.inr : X → Q ⊕ X) f e
        (MvPolynomial.mem_support_iff.mp he)
    have hdsupport : d ∈ f.support := MvPolynomial.mem_support_iff.mpr hd
    calc
      lexicographicMinimumWeight xWeight f ≤
          Finsupp.weight (fun i ↦ toLex (xWeight i)) d :=
        lexicographicMinimumWeight_le _ _ hdsupport
      _ = Finsupp.weight
            (fun i : Q ⊕ X ↦ toLex (Sum.elim qWeight xWeight i))
            (d.mapDomain (Sum.inr : X → Q ⊕ X)) :=
        (sumWeight_mapDomain_inr qWeight xWeight d).symm
      _ = Finsupp.weight
            (fun i : Q ⊕ X ↦ toLex (Sum.elim qWeight xWeight i)) e := by
        rw [hdmap]
      _ = lexicographicMinimumWeight (Sum.elim qWeight xWeight)
          (MvPolynomial.rename (Sum.inr : X → Q ⊕ X) f) := hweight

private theorem lexicographicInitialForm_rename_inr
    (qWeight : Q → Fin n → ℤ) (xWeight : X → Fin n → ℤ)
    (f : MvPolynomial X R) :
    MvPolynomial.rename (Sum.inr : X → Q ⊕ X)
        (lexicographicInitialForm xWeight f) =
      lexicographicInitialForm (Sum.elim qWeight xWeight)
        (MvPolynomial.rename (Sum.inr : X → Q ⊕ X) f) := by
  classical
  apply MvPolynomial.ext
  intro e
  by_cases he : ∃ d : X →₀ ℕ,
      d.mapDomain (Sum.inr : X → Q ⊕ X) = e
  · obtain ⟨d, rfl⟩ := he
    simp only [MvPolynomial.coeff_rename_mapDomain _ Sum.inr_injective,
      lexicographicInitialForm_coeff,
      lexicographicMinimumWeight_rename_inr qWeight xWeight f,
      sumWeight_mapDomain_inr qWeight xWeight d]
  · have hleft :
        (MvPolynomial.rename (Sum.inr : X → Q ⊕ X)
          (lexicographicInitialForm xWeight f)).coeff e = 0 :=
      MvPolynomial.coeff_rename_eq_zero _ _ _
        (fun d hd ↦ (he ⟨d, hd⟩).elim)
    have hright :
        (MvPolynomial.rename (Sum.inr : X → Q ⊕ X) f).coeff e = 0 :=
      MvPolynomial.coeff_rename_eq_zero _ _ _
        (fun d hd ↦ (he ⟨d, hd⟩).elim)
    rw [hleft, lexicographicInitialForm_coeff, hright]
    simp

private theorem sumAlgEquiv_lexicographicInitialForm_coeff
    (qWeight : Q → Fin n → ℤ) (xWeight : X → Fin n → ℤ)
    (P : MvPolynomial (Q ⊕ X) R) (a : Q →₀ ℕ) :
    ((MvPolynomial.sumAlgEquiv R Q X
        (lexicographicInitialForm (Sum.elim qWeight xWeight) P)).coeff a) =
      MvPolynomial.weightedHomogeneousComponent
        (fun i ↦ toLex (xWeight i))
        (lexicographicMinimumWeight (Sum.elim qWeight xWeight) P -
          Finsupp.weight (fun i ↦ toLex (qWeight i)) a)
        ((MvPolynomial.sumAlgEquiv R Q X P).coeff a) := by
  classical
  apply MvPolynomial.ext
  intro d
  let join : (Q ⊕ X) →₀ ℕ :=
    (Finsupp.sumFinsuppAddEquivProdFinsupp).symm (a, d)
  let outer : Lex (Fin n → ℤ) :=
    Finsupp.weight (fun i ↦ toLex (qWeight i)) a
  let inner : Lex (Fin n → ℤ) :=
    Finsupp.weight (fun i ↦ toLex (xWeight i)) d
  let beta : Lex (Fin n → ℤ) :=
    lexicographicMinimumWeight (Sum.elim qWeight xWeight) P
  have hleft :
      ((MvPolynomial.sumAlgEquiv R Q X
          (lexicographicInitialForm (Sum.elim qWeight xWeight) P)).coeff a).coeff d =
        (lexicographicInitialForm (Sum.elim qWeight xWeight) P).coeff join := by
    symm
    simpa only [join, AlgEquiv.symm_apply_apply] using
      (terminalSumAlgEquiv_symm_coeff
        (MvPolynomial.sumAlgEquiv R Q X
          (lexicographicInitialForm (Sum.elim qWeight xWeight) P)) a d)
  have hcoefficient :
      P.coeff join =
        ((MvPolynomial.sumAlgEquiv R Q X P).coeff a).coeff d := by
    simpa only [join, AlgEquiv.symm_apply_apply] using
      (terminalSumAlgEquiv_symm_coeff
        (MvPolynomial.sumAlgEquiv R Q X P) a d)
  rw [hleft, lexicographicInitialForm_coeff,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  have hsplit :
      Finsupp.weight
          (fun i : Q ⊕ X ↦ toLex (Sum.elim qWeight xWeight i)) join =
        outer + inner := by
    simpa only [join, outer, inner] using
      (sumWeight_join qWeight xWeight a d)
  rw [hsplit]
  change (if outer + inner = beta then P.coeff join else 0) =
    if inner = beta - outer then
      ((MvPolynomial.sumAlgEquiv R Q X P).coeff a).coeff d else 0
  rw [hcoefficient]
  by_cases hw : inner = beta - outer
  · have hw' : outer + inner = beta := by rw [hw]; abel
    simp [hw, hw']
  · have hw' : outer + inner ≠ beta := by
      intro heq
      apply hw
      rw [← heq]
      abel
    simp [hw, hw']

/-- Full lexicographic initial formation commutes with adjoining any family
of unused variables, even when those variables carry arbitrary weights.
The proof is coefficientwise and therefore works over every commutative
coefficient ring, including rings with zero divisors. -/
theorem lexicographicInitialIdeal_unusedPolynomialExtension
    (qWeight : Q → Fin n → ℤ) (xWeight : X → Fin n → ℤ)
    (K : Ideal (MvPolynomial X R)) :
    lexicographicInitialIdeal (Sum.elim qWeight xWeight)
        (unusedPolynomialExtension Q K) =
      unusedPolynomialExtension Q (lexicographicInitialIdeal xWeight K) := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨P, hP, rfl⟩
    change lexicographicInitialForm (Sum.elim qWeight xWeight) P ∈
      unusedPolynomialExtension Q (lexicographicInitialIdeal xWeight K)
    apply (mem_unusedPolynomialExtension_iff
      (Q := Q) (lexicographicInitialIdeal xWeight K)
      (lexicographicInitialForm (Sum.elim qWeight xWeight) P)).mpr
    intro a
    let F := MvPolynomial.sumAlgEquiv R Q X P
    let outer : Lex (Fin n → ℤ) :=
      Finsupp.weight (fun i ↦ toLex (qWeight i)) a
    let beta : Lex (Fin n → ℤ) :=
      lexicographicMinimumWeight (Sum.elim qWeight xWeight) P
    let gamma : Lex (Fin n → ℤ) := beta - outer
    let component : MvPolynomial X R :=
      MvPolynomial.weightedHomogeneousComponent
        (fun i ↦ toLex (xWeight i)) gamma (F.coeff a)
    have hFK : ∀ b : Q →₀ ℕ, F.coeff b ∈ K := by
      exact (mem_unusedPolynomialExtension_iff K P).mp hP
    have hcomponent :
        ((MvPolynomial.sumAlgEquiv R Q X
          (lexicographicInitialForm (Sum.elim qWeight xWeight) P)).coeff a) =
          component := by
      exact sumAlgEquiv_lexicographicInitialForm_coeff
        qWeight xWeight P a
    by_cases hzero :
        ((MvPolynomial.sumAlgEquiv R Q X
          (lexicographicInitialForm (Sum.elim qWeight xWeight) P)).coeff a) = 0
    · rw [hzero]
      exact Ideal.zero_mem _
    · have hcomponent_ne : component ≠ 0 := by
        rwa [hcomponent] at hzero
      have hbound : ∀ d ∈ (F.coeff a).support,
          gamma ≤ Finsupp.weight (fun i ↦ toLex (xWeight i)) d := by
        intro d hd
        let join : (Q ⊕ X) →₀ ℕ :=
          (Finsupp.sumFinsuppAddEquivProdFinsupp).symm (a, d)
        have hjoined : join ∈ P.support := by
          apply MvPolynomial.mem_support_iff.mpr
          have hc : P.coeff join = (F.coeff a).coeff d := by
            simpa only [F, join, AlgEquiv.symm_apply_apply] using
              (terminalSumAlgEquiv_symm_coeff F a d)
          rw [hc]
          exact MvPolynomial.mem_support_iff.mp hd
        have hglobal :=
          lexicographicMinimumWeight_le
            (Sum.elim qWeight xWeight) P hjoined
        change beta - outer ≤
          Finsupp.weight (fun i ↦ toLex (xWeight i)) d
        rw [sub_le_iff_le_add]
        change beta ≤
          Finsupp.weight (fun i ↦ toLex (xWeight i)) d + outer
        have hsplit := sumWeight_join qWeight xWeight a d
        change beta ≤
          Finsupp.weight
            (fun i : Q ⊕ X ↦ toLex (Sum.elim qWeight xWeight i)) join
          at hglobal
        rw [hsplit] at hglobal
        simpa only [add_comm] using hglobal
      have hminimum :
          lexicographicMinimumWeight xWeight (F.coeff a) = gamma :=
        lexicographicMinimumWeight_eq_of_component_ne_zero
          xWeight (F.coeff a) gamma hbound hcomponent_ne
      have heq : component = lexicographicInitialForm xWeight (F.coeff a) := by
        change MvPolynomial.weightedHomogeneousComponent
            (fun i ↦ toLex (xWeight i)) gamma (F.coeff a) =
          MvPolynomial.weightedHomogeneousComponent
            (fun i ↦ toLex (xWeight i))
              (lexicographicMinimumWeight xWeight (F.coeff a)) (F.coeff a)
        rw [hminimum]
      rw [hcomponent, heq]
      exact lexicographicInitialForm_mem_initialIdeal xWeight K (hFK a)
  · rw [unusedPolynomialExtension, Ideal.map_le_iff_le_comap,
      lexicographicInitialIdeal]
    apply Ideal.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    change MvPolynomial.rename (Sum.inr : X → Q ⊕ X)
        (lexicographicInitialForm xWeight f) ∈
      lexicographicInitialIdeal (Sum.elim qWeight xWeight)
        (unusedPolynomialExtension Q K)
    rw [lexicographicInitialForm_rename_inr qWeight xWeight]
    exact lexicographicInitialForm_mem_initialIdeal _ _
      (Ideal.mem_map_of_mem _ hf)

/-! ## Laurent normalization of a retained initial ideal -/

private theorem centralLaurentRescaledMap_comp_rename_inr
    (omega : X → Fin n → ℤ) :
    (centralLaurentRescaledMap (R := R) omega).comp
        (MvPolynomial.rename (Sum.inr : X → Fin n ⊕ X)).toRingHom =
      weightedGroupEvaluation
        (MvPolynomial.C : R →+* MvPolynomial X R)
        (fun i ↦ MvPolynomial.X i) omega := by
  rw [centralLaurentRescaledMap_eq_evaluation]
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp [centralLaurentWeight]

private theorem unusedPolynomialExtension_map_centralLaurentRescaledMap
    (omega : X → Fin n → ℤ) (K : Ideal (MvPolynomial X R)) :
    (unusedPolynomialExtension (Fin n) K).map
        (centralLaurentRescaledMap (R := R) omega) =
      K.map (weightedGroupEvaluation
        (MvPolynomial.C : R →+* MvPolynomial X R)
        (fun i ↦ MvPolynomial.X i) omega) := by
  change
    (K.map
      (MvPolynomial.rename (Sum.inr : X → Fin n ⊕ X)).toRingHom).map
        (centralLaurentRescaledMap (R := R) omega) = _
  rw [Ideal.map_map]
  congr 1
  exact centralLaurentRescaledMap_comp_rename_inr omega

/-- Rescaling an initial ideal by the opposite of its defining vector weight
only attaches an invertible Laurent monomial to each homogeneous generator.
Consequently its Laurent image is exactly its coefficient extension. -/
private theorem weightedGroupEvaluation_neg_initial_eq_map_C
    (weight : X → Fin n → ℤ) (K : Ideal (MvPolynomial X R)) :
    (lexicographicInitialIdeal weight K).map
        (weightedGroupEvaluation
          (MvPolynomial.C : R →+* MvPolynomial X R)
          (fun i ↦ MvPolynomial.X i) (fun i ↦ -weight i)) =
      (lexicographicInitialIdeal weight K).map
        (groupAlgebraC (MvPolynomial X R) (Fin n → ℤ)) := by
  let Source := {f : MvPolynomial X R // f ∈ K}
  let p : Source → MvPolynomial X R :=
    fun f ↦ lexicographicInitialForm weight f.1
  let degree : Source → (Fin n → ℤ) :=
    fun f ↦ -ofLex (lexicographicMinimumWeight weight f.1)
  have hp : ∀ i, (p i).IsWeightedHomogeneous
      (fun x ↦ -weight x) (degree i) := by
    intro i
    exact isWeightedHomogeneous_neg_group weight
      (lexicographicInitialForm_isWeightedHomogeneous weight i.1)
  have heq := weightedGroupEvaluation_span_eq_normalized_map
    (c := (MvPolynomial.C : R →+* MvPolynomial X R))
    (a := fun i ↦ MvPolynomial.X i)
    (ν := fun i ↦ -weight i) p degree hp
  have hrange : Set.range p =
      lexicographicInitialForm weight '' (K : Set (MvPolynomial X R)) := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hnormalized :
      (fun i ↦ MvPolynomial.eval₂Hom
        (MvPolynomial.C : R →+* MvPolynomial X R)
        (fun x ↦ MvPolynomial.X x) (p i)) = p := by
    funext i
    exact MvPolynomial.eval₂_eta (p i)
  rw [hrange, hnormalized, hrange] at heq
  exact heq

/-! ## The terminal specialization -/

variable (R : Type u) [CommRing R]
variable {h : ℕ} (totalD : Fin h → ℕ) (Time : Type w)

/-- The retained central ideal, extended by fresh representative variables
indexed by the same blocks. -/
def unusedRepresentativeExtension
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    Ideal (MvPolynomial
      (Fin h ⊕ CentralPolynomialIndex (Fin h) totalD Time) R) :=
  unusedPolynomialExtension (Fin h) K

/-- Positive terminal weight, written with the signed codomain required by
lexicographic initial ideals. -/
def signedTerminalWeight
    (x : CentralPolynomialIndex (Fin h) totalD Time) (b : Fin h) : ℤ :=
  (terminalGlobalWeight (Fin h) totalD Time x b : ℕ)

/-- The shear parameter has the opposite sign from the retained initial
weight.  With this convention the central initial weight of a derivative
variable is positive. -/
def negativeTerminalWeight
    (x : CentralPolynomialIndex (Fin h) totalD Time) (b : Fin h) : ℤ :=
  -signedTerminalWeight totalD Time x b

@[simp]
theorem centralLaurentWeight_negativeTerminalWeight_inl
    (i j : Fin h) :
    centralLaurentWeight (negativeTerminalWeight totalD Time)
        (Sum.inl i) j = if i = j then -1 else 0 := by
  classical
  by_cases hij : i = j <;>
    simp [centralLaurentWeight, finiteLaurentExponentHom_apply,
      Finsupp.single_apply, hij]

@[simp]
theorem centralLaurentWeight_negativeTerminalWeight_inr
    (x : CentralPolynomialIndex (Fin h) totalD Time) (b : Fin h) :
    centralLaurentWeight (negativeTerminalWeight totalD Time)
        (Sum.inr x) b = signedTerminalWeight totalD Time x b := by
  simp [centralLaurentWeight, negativeTerminalWeight]

/-- The preliminary translation `x_i ↦ q_i - 1` fixes an ideal which was
extended from the retained variables. -/
theorem polynomialCoordinateTranslation_unusedRepresentativeExtension
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    (unusedRepresentativeExtension R totalD Time K).map
        (polynomialCoordinateTranslation
          (Sum.elim (fun _ : Fin h ↦ (-1 : R))
            (fun _ : CentralPolynomialIndex (Fin h) totalD Time ↦ 0))).toRingHom =
      unusedRepresentativeExtension R totalD Time K := by
  exact polynomialCoordinateTranslation_unusedPolynomialExtension
    (Q := Fin h) (X := CentralPolynomialIndex (Fin h) totalD Time)
    (fun _ ↦ (-1 : R)) K

/-- Short interface name used by the separated-cluster assembly. -/
theorem polynomialCoordinateTranslation_unusedExtension
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    (unusedRepresentativeExtension R totalD Time K).map
        (polynomialCoordinateTranslation
          (Sum.elim (fun _ : Fin h ↦ (-1 : R))
            (fun _ : CentralPolynomialIndex (Fin h) totalD Time ↦ 0))).toRingHom =
      unusedRepresentativeExtension R totalD Time K :=
  polynomialCoordinateTranslation_unusedRepresentativeExtension R totalD Time K

/-- Adjoining the unused representative variables commutes exactly with the
terminal full lexicographic initial ideal. -/
theorem lexicographicInitialIdeal_unusedRepresentativeExtension
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    lexicographicInitialIdeal
        (centralLaurentWeight (negativeTerminalWeight totalD Time))
        (unusedRepresentativeExtension R totalD Time K) =
      unusedRepresentativeExtension R totalD Time
        (lexicographicInitialIdeal (signedTerminalWeight totalD Time) K) := by
  have hweight :
      centralLaurentWeight (negativeTerminalWeight totalD Time) =
        Sum.elim
          (fun i ↦ -finiteLaurentExponentHom h (Finsupp.single i 1))
          (signedTerminalWeight totalD Time) := by
    funext i b
    cases i with
    | inl i => rfl
    | inr x => simp [centralLaurentWeight, negativeTerminalWeight]
  rw [hweight]
  change
    lexicographicInitialIdeal
        (Sum.elim
          (fun i ↦ -finiteLaurentExponentHom h (Finsupp.single i 1))
          (signedTerminalWeight totalD Time))
        (unusedPolynomialExtension (Fin h) K) =
      unusedPolynomialExtension (Fin h)
        (lexicographicInitialIdeal (signedTerminalWeight totalD Time) K)
  exact lexicographicInitialIdeal_unusedPolynomialExtension _ _ K

/-- Short interface name used by the separated-cluster assembly. -/
theorem lexicographicInitial_unusedExtension
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    lexicographicInitialIdeal
        (centralLaurentWeight (negativeTerminalWeight totalD Time))
        (unusedRepresentativeExtension R totalD Time K) =
      unusedRepresentativeExtension R totalD Time
        (lexicographicInitialIdeal (signedTerminalWeight totalD Time) K) :=
  lexicographicInitialIdeal_unusedRepresentativeExtension R totalD Time K

/-- For an unused representative extension, the shifted Laurent contraction
is exactly the retained terminal initial ideal. -/
theorem centralShiftedLaurentContraction_unusedRepresentativeExtension
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    centralShiftedLaurentContraction
        (negativeTerminalWeight totalD Time)
        (unusedRepresentativeExtension R totalD Time K) =
      lexicographicInitialIdeal (signedTerminalWeight totalD Time) K := by
  let weight := signedTerminalWeight totalD Time
  let initial := lexicographicInitialIdeal weight K
  calc
    centralShiftedLaurentContraction
        (negativeTerminalWeight totalD Time)
        (unusedRepresentativeExtension R totalD Time K) =
      centralLaurentContraction
        (negativeTerminalWeight totalD Time)
        (unusedRepresentativeExtension R totalD Time K) := by
          rw [centralShiftedLaurentContraction,
            polynomialCoordinateTranslation_unusedRepresentativeExtension]
    _ = (((lexicographicInitialIdeal
          (centralLaurentWeight (negativeTerminalWeight totalD Time))
          (unusedRepresentativeExtension R totalD Time K)).map
            (centralLaurentRescaledMap
              (negativeTerminalWeight totalD Time))).comap
        (groupAlgebraC
          (CentralPolynomial R (Fin h) totalD Time) (Fin h → ℤ))) :=
      centralLaurentContraction_eq _ _
    _ = ((unusedRepresentativeExtension R totalD Time initial).map
          (centralLaurentRescaledMap
            (negativeTerminalWeight totalD Time))).comap
        (groupAlgebraC
          (CentralPolynomial R (Fin h) totalD Time) (Fin h → ℤ)) := by
      rw [lexicographicInitialIdeal_unusedRepresentativeExtension]
    _ = (initial.map
          (weightedGroupEvaluation
            (MvPolynomial.C : R →+*
              CentralPolynomial R (Fin h) totalD Time)
            (fun i ↦ MvPolynomial.X i)
            (negativeTerminalWeight totalD Time))).comap
        (groupAlgebraC
          (CentralPolynomial R (Fin h) totalD Time) (Fin h → ℤ)) := by
      rw [unusedRepresentativeExtension,
        unusedPolynomialExtension_map_centralLaurentRescaledMap]
    _ = (initial.map
          (groupAlgebraC
            (CentralPolynomial R (Fin h) totalD Time) (Fin h → ℤ))).comap
        (groupAlgebraC
          (CentralPolynomial R (Fin h) totalD Time) (Fin h → ℤ)) := by
      have hnegative : negativeTerminalWeight totalD Time =
          fun i ↦ -weight i := rfl
      rw [hnegative]
      exact congrArg
        (fun J : Ideal
            (AddMonoidAlgebra
              (CentralPolynomial R (Fin h) totalD Time) (Fin h → ℤ)) ↦
          J.comap (groupAlgebraC
            (CentralPolynomial R (Fin h) totalD Time) (Fin h → ℤ)))
        (weightedGroupEvaluation_neg_initial_eq_map_C weight K)
    _ = initial := groupAlgebra_comap_map_C_eq initial
    _ = lexicographicInitialIdeal (signedTerminalWeight totalD Time) K := rfl

/-- Interface name matching the central-contraction stage of the cluster
argument.  The contraction here includes the preliminary shift by definition. -/
theorem centralLaurentContraction_unusedExtension
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    centralShiftedLaurentContraction
        (negativeTerminalWeight totalD Time)
        (unusedRepresentativeExtension R totalD Time K) =
      lexicographicInitialIdeal (signedTerminalWeight totalD Time) K :=
  centralShiftedLaurentContraction_unusedRepresentativeExtension R totalD Time K

/-- The entire central construction therefore reduces to the final central
polynomial equivalence applied to the retained terminal initial ideal. -/
theorem centralIdealConstruction_unusedRepresentativeExtension
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    centralIdealConstruction
        (negativeTerminalWeight totalD Time)
        (unusedRepresentativeExtension R totalD Time K) =
      (lexicographicInitialIdeal (signedTerminalWeight totalD Time) K).map
        (centralPolynomialPhi R (Fin h) totalD Time).toRingHom := by
  rw [centralIdealConstruction,
    centralShiftedLaurentContraction_unusedRepresentativeExtension]

/-- Short interface name used by the separated-cluster assembly. -/
theorem centralIdealConstruction_unusedExtension
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    centralIdealConstruction
        (negativeTerminalWeight totalD Time)
        (unusedRepresentativeExtension R totalD Time K) =
      (lexicographicInitialIdeal (signedTerminalWeight totalD Time) K).map
        (centralPolynomialPhi R (Fin h) totalD Time).toRingHom :=
  centralIdealConstruction_unusedRepresentativeExtension R totalD Time K

/-! ## Height bookkeeping -/

/-- Adding the finite family of unused representative variables preserves
height.  These are the only extra hypotheses needed for this height equality. -/
theorem unusedRepresentativeExtension_height
    [IsNoetherianRing R] [Finite Time]
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    (unusedRepresentativeExtension R totalD Time K).height = K.height := by
  calc
    (unusedRepresentativeExtension R totalD Time K).height =
        ((unusedRepresentativeExtension R totalD Time K).map
          (MvPolynomial.sumAlgEquiv R (Fin h)
            (CentralPolynomialIndex (Fin h) totalD Time)).toRingHom).height :=
      ((MvPolynomial.sumAlgEquiv R (Fin h)
        (CentralPolynomialIndex (Fin h) totalD Time)).toRingEquiv.height_map _).symm
    _ = (K.map (MvPolynomial.C :
          CentralPolynomial R (Fin h) totalD Time →+*
            MvPolynomial (Fin h)
              (CentralPolynomial R (Fin h) totalD Time))).height := by
      rw [unusedRepresentativeExtension,
        unusedPolynomialExtension_map_sumAlgEquiv]
    _ = K.height := mvPolynomial_height_map_C K

/-- The simplified central construction has exactly the height of the
retained terminal initial ideal; this equality itself needs no finiteness or
Noetherianity. -/
theorem centralIdealConstruction_unusedRepresentativeExtension_height
    (K : Ideal (CentralPolynomial R (Fin h) totalD Time)) :
    (centralIdealConstruction
      (negativeTerminalWeight totalD Time)
      (unusedRepresentativeExtension R totalD Time K)).height =
        (lexicographicInitialIdeal (signedTerminalWeight totalD Time) K).height := by
  rw [centralIdealConstruction_unusedRepresentativeExtension,
    centralPolynomialPhi_height_map]

end AbelFormalization
