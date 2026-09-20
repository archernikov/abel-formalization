import AbelFormalization.TerminalGlobalParameterDeformation
import AbelFormalization.TerminalIndexSplit
import AbelFormalization.TerminalInvariantDerivations
import AbelFormalization.WeightedInitialComponents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Specializing the global Stirling deformation to one block

Killing every parameter except one and identifying the remaining polynomial
variable with the ordinary univariate parameter recovers the one-block
Stirling homomorphism.  Combined with global homogeneous decomposition, this
proves actual coefficient membership and hence preservation by all bounded
terminal block vector fields.
-/

noncomputable section

namespace AbelFormalization

universe u v w

/-- The singleton parameter variable selecting block `b`. -/
def terminalBlockSingletonEmbedding (Block : Type v) (b : Block) :
    PUnit.{1} ↪ Block where
  toFun := fun _ ↦ b
  inj' := fun _ _ _ ↦ Subsingleton.elim _ _

section Specialization

variable (R : Type u) [CommRing R]
variable (Block : Type v) (d : Block → ℕ) (Time : Type w) (b : Block)

/-- Set every global parameter outside block `b` to zero, transport the
coefficient polynomial through the split-index equivalence, and regard the
remaining singleton-indexed polynomial as a univariate polynomial. -/
def terminalBlockAxisPolynomialSpecialization :
    MvPolynomial Block (CentralPolynomial R Block d Time) →+*
      Polynomial
        (MvPolynomial
          (TerminalBlockKeepIndex Block d Time b ⊕ Fin (d b)) R) :=
  (MvPolynomial.uniqueAlgEquiv
      (MvPolynomial
        (TerminalBlockKeepIndex Block d Time b ⊕ Fin (d b)) R)
      PUnit.{1}).toRingHom.comp
    ((MvPolynomial.map
        (terminalSplitRenameEquiv R Block d Time b).toRingHom).comp
      (MvPolynomial.killCompl
        (terminalBlockSingletonEmbedding Block b).injective).toRingHom)

/-- The `k`th specialized coefficient is exactly the pure-axis global
parameter coefficient, after the split-index rename. -/
theorem terminalBlockAxisPolynomialSpecialization_coeff
    (F : MvPolynomial Block (CentralPolynomial R Block d Time)) (k : ℕ) :
    (terminalBlockAxisPolynomialSpecialization R Block d Time b F).coeff k =
      terminalSplitRenameEquiv R Block d Time b
        (F.coeff (terminalBlockAxis Block b k)) := by
  classical
  rw [terminalBlockAxisPolynomialSpecialization,
    RingHom.comp_apply, RingHom.comp_apply]
  change
    ((MvPolynomial.uniqueAlgEquiv
      (MvPolynomial
        (TerminalBlockKeepIndex Block d Time b ⊕ Fin (d b)) R)
      PUnit.{1})
      (MvPolynomial.map
        (terminalSplitRenameEquiv R Block d Time b).toRingHom
        (MvPolynomial.killCompl
          (terminalBlockSingletonEmbedding Block b).injective F))).coeff k = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv,
    MvPolynomial.coeff_map,
    MvPolynomial.coeff_killCompl]
  change
    terminalSplitRenameEquiv R Block d Time b
        (F.coeff
          ((Finsupp.single (default : PUnit.{1}) k).mapDomain
            (terminalBlockSingletonEmbedding Block b))) =
      terminalSplitRenameEquiv R Block d Time b
        (F.coeff (terminalBlockAxis Block b k))
  apply congrArg (terminalSplitRenameEquiv R Block d Time b)
  apply congrArg F.coeff
  rw [Finsupp.mapDomain_single]
  rfl

end Specialization

section AxisCoefficients

variable (R : Type u) [CommRing R]
variable (Block : Type v) (d : Block → ℕ) (Time : Type w)

/-- The pure `b`-axis coefficient of the parameter image of a variable in
that same block. -/
theorem terminalGlobalStirlingParameterVariable_coeff_axis_same
    (b : Block) (r : Fin (d b)) (k : ℕ) :
    (terminalGlobalStirlingParameterVariable R Block d Time
        (Sum.inl ⟨b, r⟩)).coeff (terminalBlockAxis Block b k) =
      if hk : k ≤ r.val then
        MvPolynomial.monomial
          (Finsupp.single
            (Sum.inl
              ⟨b, (⟨r.val - k,
                (Nat.sub_le r.val k).trans_lt r.isLt⟩ : Fin (d b))⟩ :
                CentralPolynomialIndex Block d Time) 1)
          (signedStirling (r.val + 1) (r.val - k + 1) : R)
      else 0 := by
  classical
  change
    ((MvPolynomial.coeffAddMonoidHom (terminalBlockAxis Block b k))
      (∑ j : Fin (d b),
        MvPolynomial.monomial (Finsupp.single b (r.val - j.val))
          (MvPolynomial.monomial
            (Finsupp.single
              (Sum.inl ⟨b, j⟩ : CentralPolynomialIndex Block d Time) 1)
            (if j ≤ r then
              (signedStirling (r.val + 1) (j.val + 1) : R)
            else 0)))) = _
  rw [map_sum]
  change
    (∑ j : Fin (d b),
      (MvPolynomial.monomial (Finsupp.single b (r.val - j.val))
        (MvPolynomial.monomial
          (Finsupp.single
            (Sum.inl ⟨b, j⟩ : CentralPolynomialIndex Block d Time) 1)
          (if j ≤ r then
            (signedStirling (r.val + 1) (j.val + 1) : R)
          else 0))).coeff (terminalBlockAxis Block b k)) = _
  by_cases hk : k ≤ r.val
  · rw [dite_eq_left hk]
    let j₀ : Fin (d b) := ⟨r.val - k,
      (Nat.sub_le r.val k).trans_lt r.isLt⟩
    have hj₀r : j₀ ≤ r := by
      apply Fin.mk_le_mk.mpr
      exact Nat.sub_le r.val k
    rw [Finset.sum_eq_single j₀]
    · simp [j₀, hj₀r, terminalBlockAxis, Nat.sub_sub_self hk]
    · intro j hj hne
      by_cases hjr : j ≤ r
      · have hexponent : r.val - j.val ≠ k := by
          intro heq
          apply hne
          apply Fin.ext
          dsimp [j₀]
          omega
        have hFinsupp : Finsupp.single b (r.val - j.val) ≠
            terminalBlockAxis Block b k := by
          intro heq
          have heval := congrFun (congrArg DFunLike.coe heq) b
          simp [terminalBlockAxis] at heval
          exact hexponent heval
        rw [MvPolynomial.coeff_monomial, ite_eq_right hFinsupp]
      · simp [hjr]
    · intro hmissing
      exact (hmissing (Finset.mem_univ j₀)).elim
  · rw [dite_eq_right hk]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hjr : j ≤ r
    · have hexponent : r.val - j.val ≠ k := by omega
      have hFinsupp : Finsupp.single b (r.val - j.val) ≠
          terminalBlockAxis Block b k := by
        intro heq
        have heval := congrFun (congrArg DFunLike.coe heq) b
        simp [terminalBlockAxis] at heval
        exact hexponent heval
      rw [MvPolynomial.coeff_monomial, ite_eq_right hFinsupp]
    · simp [hjr]

/-- A pure `b`-axis coefficient of a parameter image in another block is
constant in the selected parameter. -/
theorem terminalGlobalStirlingParameterVariable_coeff_axis_other
    (b c : Block) (hcb : c ≠ b) (r : Fin (d c)) (k : ℕ) :
    (terminalGlobalStirlingParameterVariable R Block d Time
        (Sum.inl ⟨c, r⟩)).coeff (terminalBlockAxis Block b k) =
      if k = 0 then
        MvPolynomial.X
          (Sum.inl ⟨c, r⟩ : CentralPolynomialIndex Block d Time)
      else 0 := by
  classical
  change
    ((MvPolynomial.coeffAddMonoidHom (terminalBlockAxis Block b k))
      (∑ j : Fin (d c),
        MvPolynomial.monomial (Finsupp.single c (r.val - j.val))
          (MvPolynomial.monomial
            (Finsupp.single
              (Sum.inl ⟨c, j⟩ : CentralPolynomialIndex Block d Time) 1)
            (if j ≤ r then
              (signedStirling (r.val + 1) (j.val + 1) : R)
            else 0)))) = _
  rw [map_sum]
  change
    (∑ j : Fin (d c),
      (MvPolynomial.monomial (Finsupp.single c (r.val - j.val))
        (MvPolynomial.monomial
          (Finsupp.single
            (Sum.inl ⟨c, j⟩ : CentralPolynomialIndex Block d Time) 1)
          (if j ≤ r then
            (signedStirling (r.val + 1) (j.val + 1) : R)
          else 0))).coeff (terminalBlockAxis Block b k)) = _
  by_cases hk : k = 0
  · subst k
    rw [if_pos rfl]
    rw [Finset.sum_eq_single r]
    · simp [terminalBlockAxis, signedStirling_self,
        ← MvPolynomial.C_mul_X_eq_monomial]
    · intro j hj hne
      by_cases hjr : j ≤ r
      · have hlt : j < r := lt_of_le_of_ne hjr hne
        have hpos : 0 < r.val - j.val := by omega
        have hsingle : Finsupp.single c (r.val - j.val) ≠
            (0 : Block →₀ ℕ) := by
          intro hzero
          have := congrFun (congrArg DFunLike.coe hzero) c
          simp [hpos.ne'] at this
        have haxiszero : terminalBlockAxis Block b 0 =
            (0 : Block →₀ ℕ) := by
          ext x
          simp [terminalBlockAxis]
        rw [MvPolynomial.coeff_monomial, haxiszero,
          ite_eq_right hsingle]
      · simp [hjr]
    · intro hmissing
      exact (hmissing (Finset.mem_univ r)).elim
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro j hj
    rw [MvPolynomial.coeff_monomial]
    have haxis : terminalBlockAxis Block b k ≠ 0 := by
      intro hzero
      have := congrFun (congrArg DFunLike.coe hzero) b
      simp [terminalBlockAxis, hk] at this
    by_cases hjr : j ≤ r
    · by_cases he : Finsupp.single c (r.val - j.val) =
          terminalBlockAxis Block b k
      · have hc := congrFun (congrArg DFunLike.coe he) c
        have hb := congrFun (congrArg DFunLike.coe he) b
        by_cases hbc : b = c
        · exact (hcb hbc.symm).elim
        · simp [terminalBlockAxis, hcb, hbc] at hc hb
          exact (hk hb.symm).elim
      · rw [ite_eq_right he]
    · simp [hjr]

/-- Retained variables are constant in every block parameter. -/
theorem terminalGlobalStirlingParameterVariable_coeff_axis_time
    (b : Block) (t : Time) (k : ℕ) :
    (terminalGlobalStirlingParameterVariable R Block d Time
        (Sum.inr t)).coeff (terminalBlockAxis Block b k) =
      if k = 0 then
        MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time)
      else 0 := by
  classical
  simp [terminalGlobalStirlingParameterVariable,
    terminalBlockAxis, MvPolynomial.coeff_C, eq_comm]

end AxisCoefficients

section OneBlockIdentification

variable (R : Type u) [CommRing R] [Algebra ℚ R]
variable (Block : Type v) (d : Block → ℕ) (Time : Type w) (b : Block)

/-- Specializing the simultaneous parameter deformation to the axis of one
block is the existing one-block Stirling parameter homomorphism after the
split-index rename. -/
theorem terminalBlockAxisPolynomialSpecialization_globalParameter
    (P : CentralPolynomial R Block d Time) :
    terminalBlockAxisPolynomialSpecialization R Block d Time b
        (terminalGlobalStirlingParameterHom R Block d Time P) =
      stirlingParameterHom R
        (TerminalBlockKeepIndex Block d Time b) (d b)
        (terminalSplitRenameEquiv R Block d Time b P) := by
  classical
  let left : CentralPolynomial R Block d Time →+*
      Polynomial
        (MvPolynomial
          (TerminalBlockKeepIndex Block d Time b ⊕ Fin (d b)) R) :=
    (terminalBlockAxisPolynomialSpecialization R Block d Time b).comp
      (terminalGlobalStirlingParameterHom R Block d Time).toRingHom
  let right : CentralPolynomial R Block d Time →+*
      Polynomial
        (MvPolynomial
          (TerminalBlockKeepIndex Block d Time b ⊕ Fin (d b)) R) :=
    (stirlingParameterHom R
      (TerminalBlockKeepIndex Block d Time b) (d b)).toRingHom.comp
        (terminalSplitRenameEquiv R Block d Time b).toRingHom
  have hhom : left = right := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [left, right, terminalBlockAxisPolynomialSpecialization,
        terminalGlobalStirlingParameterHom]
    · intro x
      rcases x with ⟨c, r⟩ | t
      · by_cases hcb : c = b
        · subst c
          apply Polynomial.ext
          intro k
          rw [show left (MvPolynomial.X
                (Sum.inl ⟨b, r⟩ : CentralPolynomialIndex Block d Time)) =
              terminalBlockAxisPolynomialSpecialization R Block d Time b
                (terminalGlobalStirlingParameterVariable R Block d Time
                  (Sum.inl ⟨b, r⟩)) by simp [left]]
          rw [terminalBlockAxisPolynomialSpecialization_coeff,
            terminalGlobalStirlingParameterVariable_coeff_axis_same]
          rw [show right (MvPolynomial.X
                (Sum.inl ⟨b, r⟩ : CentralPolynomialIndex Block d Time)) =
              stirlingParameterVariable R
                (TerminalBlockKeepIndex Block d Time b) (d b) r by
              simp [right]]
          rw [stirlingParameterVariable_coeff]
          by_cases hk : k ≤ r.val
          · rw [dite_eq_left hk, dite_eq_left hk]
            simp [MvPolynomial.monomial_eq,
              terminalSplitRenameEquiv_X_sameBlock]
          · rw [dite_eq_right hk, dite_eq_right hk]
            simp
        · apply Polynomial.ext
          intro k
          rw [show left (MvPolynomial.X
                (Sum.inl ⟨c, r⟩ : CentralPolynomialIndex Block d Time)) =
              terminalBlockAxisPolynomialSpecialization R Block d Time b
                (terminalGlobalStirlingParameterVariable R Block d Time
                  (Sum.inl ⟨c, r⟩)) by simp [left]]
          rw [terminalBlockAxisPolynomialSpecialization_coeff,
            terminalGlobalStirlingParameterVariable_coeff_axis_other
              R Block d Time b c hcb r k]
          rw [show right (MvPolynomial.X
                (Sum.inl ⟨c, r⟩ : CentralPolynomialIndex Block d Time)) =
              Polynomial.C
                (MvPolynomial.X
                  (Sum.inl (Sum.inl ⟨⟨c, hcb⟩, r⟩))) by
              simp [right, hcb]]
          rw [Polynomial.coeff_C]
          by_cases hk : k = 0
          · subst k
            simp [terminalSplitRenameEquiv_X_otherBlock, hcb]
          · simp [hk]
      · apply Polynomial.ext
        intro k
        rw [show left (MvPolynomial.X
              (Sum.inr t : CentralPolynomialIndex Block d Time)) =
            terminalBlockAxisPolynomialSpecialization R Block d Time b
              (MvPolynomial.C
                (MvPolynomial.X
                  (Sum.inr t : CentralPolynomialIndex Block d Time))) by
            simp [left]]
        rw [terminalBlockAxisPolynomialSpecialization_coeff]
        rw [show right (MvPolynomial.X
              (Sum.inr t : CentralPolynomialIndex Block d Time)) =
            Polynomial.C
              (MvPolynomial.X (Sum.inl (Sum.inr t))) by
            simp [right]]
        rw [Polynomial.coeff_C]
        by_cases hk : k = 0
        · subst k
          simp [terminalBlockAxis, terminalSplitRenameEquiv_X_time]
        · have haxis : terminalBlockAxis Block b k ≠ 0 := by
            intro hzero
            have heval := congrFun (congrArg DFunLike.coe hzero) b
            simp [terminalBlockAxis, hk] at heval
          change Finsupp.single b k ≠ (0 : Block →₀ ℕ) at haxis
          have haxis' : (0 : Block →₀ ℕ) ≠
              terminalBlockAxis Block b k := by
            change (0 : Block →₀ ℕ) ≠ Finsupp.single b k
            exact haxis.symm
          rw [MvPolynomial.coeff_C,
            ite_eq_right haxis']
          simp [hk]
  exact RingHom.congr_fun hhom P

/-- The existing one-block coefficient is the pure-axis coefficient of the
simultaneous deformation, transported through the split-index equivalence. -/
theorem stirlingParameterHom_coeff_eq_globalParameter_axis
    (P : CentralPolynomial R Block d Time) (k : ℕ) :
    (stirlingParameterHom R
      (TerminalBlockKeepIndex Block d Time b) (d b)
      (terminalSplitRenameEquiv R Block d Time b P)).coeff k =
      terminalSplitRenameEquiv R Block d Time b
        ((terminalGlobalStirlingParameterHom R Block d Time P).coeff
          (terminalBlockAxis Block b k)) := by
  rw [← terminalBlockAxisPolynomialSpecialization_globalParameter
    R Block d Time b P]
  exact terminalBlockAxisPolynomialSpecialization_coeff
    R Block d Time b _ k

/-- Correct homogeneous-input bridge from a one-block coefficient to the
actual component of the simultaneous signed-Stirling image. -/
theorem stirlingParameterHom_coeff_eq_globalComponent_of_add
    {P : CentralPolynomial R Block d Time}
    {inputDegree outputDegree : TerminalMultidegree Block}
    (k : ℕ)
    (hP : MvPolynomial.IsWeightedHomogeneous
      (terminalGlobalWeight Block d Time) P inputDegree)
    (hadd : outputDegree + terminalBlockAxis Block b k = inputDegree) :
    (stirlingParameterHom R
      (TerminalBlockKeepIndex Block d Time b) (d b)
      (terminalSplitRenameEquiv R Block d Time b P)).coeff k =
      terminalSplitRenameEquiv R Block d Time b
        (terminalGlobalComponent R Block d Time outputDegree
          (terminalGlobalStirlingEquiv R Block d Time P)) := by
  rw [stirlingParameterHom_coeff_eq_globalParameter_axis]
  rw [terminalGlobalStirlingParameter_coeff_eq_component_of_add
    R Block d Time hP hadd]

/-- A parameter coefficient beyond the input degree in its chosen block is
zero. -/
theorem stirlingParameterHom_coeff_eq_zero_of_globalHomogeneous
    {P : CentralPolynomial R Block d Time}
    {inputDegree : TerminalMultidegree Block}
    (k : ℕ)
    (hP : MvPolynomial.IsWeightedHomogeneous
      (terminalGlobalWeight Block d Time) P inputDegree)
    (hk : inputDegree b < k) :
    (stirlingParameterHom R
      (TerminalBlockKeepIndex Block d Time b) (d b)
      (terminalSplitRenameEquiv R Block d Time b P)).coeff k = 0 := by
  have hglobal :
      (terminalGlobalStirlingParameterHom R Block d Time P).coeff
        (terminalBlockAxis Block b k) = 0 := by
    by_contra hne
    obtain ⟨m, hm⟩ := MvPolynomial.exists_coeff_ne_zero hne
    have hdegree := terminalGlobalStirlingParameter_coeff_degree
      R Block d Time hP hm
    have hb := congrFun (congrArg DFunLike.coe hdegree) b
    simp [terminalBlockAxis] at hb
    omega
  rw [stirlingParameterHom_coeff_eq_globalParameter_axis,
    hglobal, map_zero]

/-- The exact in-range/out-of-range homogeneous coefficient formula. -/
theorem stirlingParameterHom_coeff_of_globalHomogeneous
    {P : CentralPolynomial R Block d Time}
    {inputDegree : TerminalMultidegree Block}
    (k : ℕ)
    (hP : MvPolynomial.IsWeightedHomogeneous
      (terminalGlobalWeight Block d Time) P inputDegree) :
    (stirlingParameterHom R
      (TerminalBlockKeepIndex Block d Time b) (d b)
      (terminalSplitRenameEquiv R Block d Time b P)).coeff k =
      if k ≤ inputDegree b then
        terminalSplitRenameEquiv R Block d Time b
          (terminalGlobalComponent R Block d Time
            (inputDegree - terminalBlockAxis Block b k)
            (terminalGlobalStirlingEquiv R Block d Time P))
      else 0 := by
  classical
  by_cases hk : k ≤ inputDegree b
  · rw [ite_eq_left hk]
    have haxis : terminalBlockAxis Block b k ≤ inputDegree := by
      simpa [terminalBlockAxis] using hk
    exact stirlingParameterHom_coeff_eq_globalComponent_of_add
      R Block d Time b k hP (tsub_add_cancel_of_le haxis)
  · rw [ite_eq_right hk]
    exact stirlingParameterHom_coeff_eq_zero_of_globalHomogeneous
      R Block d Time b k hP (Nat.lt_of_not_ge hk)

end OneBlockIdentification

section IdealCoefficientClosure

variable (R : Type u) [CommRing R] [Algebra ℚ R]
variable (Block : Type v) (d : Block → ℕ) (Time : Type w)

/-- Every one-block parameter coefficient of the renamed image of a global
ideal element belongs to the renamed ideal.  This is proved by finite global
homogeneous decomposition; no false component identity for nonhomogeneous
inputs is assumed. -/
theorem terminalSplitStirlingParameter_coeff_mem_of_global
    (I : Ideal (CentralPolynomial R Block d Time))
    (hgraded : IsTerminalMultigradedIdeal R Block d Time I)
    (hJ : IsTerminalGlobalStirlingInvariant R Block d Time I)
    (b : Block) (P : CentralPolynomial R Block d Time) (hP : P ∈ I)
    (k : ℕ) :
    (stirlingParameterHom R
      (TerminalBlockKeepIndex Block d Time b) (d b)
      (terminalSplitRenameEquiv R Block d Time b P)).coeff k ∈
        I.map (terminalSplitRenameEquiv R Block d Time b).toRingHom := by
  classical
  rw [← sum_weightedHomogeneousComponent_support
    (terminalGlobalWeight Block d Time) P]
  simp only [map_sum, Polynomial.finsetSum_coeff]
  apply Ideal.sum_mem
  intro degree hdegree
  let Q : CentralPolynomial R Block d Time :=
    terminalGlobalComponent R Block d Time degree P
  have hQ : Q ∈ I := hgraded P hP degree
  have hQhom : MvPolynomial.IsWeightedHomogeneous
      (terminalGlobalWeight Block d Time) Q degree :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous degree P
  by_cases hk : k ≤ degree b
  · have haxis : terminalBlockAxis Block b k ≤ degree := by
      simpa [terminalBlockAxis] using hk
    change
      (stirlingParameterHom R
        (TerminalBlockKeepIndex Block d Time b) (d b)
        (terminalSplitRenameEquiv R Block d Time b Q)).coeff k ∈
          I.map (terminalSplitRenameEquiv R Block d Time b).toRingHom
    rw [stirlingParameterHom_coeff_eq_globalComponent_of_add
      R Block d Time b k hQhom (tsub_add_cancel_of_le haxis)]
    apply (Ideal.apply_mem_of_equiv_iff
      (I := I)
      (f := (terminalSplitRenameEquiv R Block d Time b).toRingEquiv)).2
    exact hgraded
      (terminalGlobalStirlingEquiv R Block d Time Q) (hJ Q hQ)
      (degree - terminalBlockAxis Block b k)
  · change
      (stirlingParameterHom R
        (TerminalBlockKeepIndex Block d Time b) (d b)
        (terminalSplitRenameEquiv R Block d Time b Q)).coeff k ∈
          I.map (terminalSplitRenameEquiv R Block d Time b).toRingHom
    rw [stirlingParameterHom_coeff_eq_zero_of_globalHomogeneous
      R Block d Time b k hQhom (Nat.lt_of_not_ge hk)]
    exact (I.map
      (terminalSplitRenameEquiv R Block d Time b).toRingHom).zero_mem

/-- Coefficient closure for every member of the renamed one-block ideal. -/
theorem terminalSplitStirlingParameter_coeff_mem
    (I : Ideal (CentralPolynomial R Block d Time))
    (hgraded : IsTerminalMultigradedIdeal R Block d Time I)
    (hJ : IsTerminalGlobalStirlingInvariant R Block d Time I)
    (b : Block) :
    ∀ P ∈ I.map (terminalSplitRenameEquiv R Block d Time b).toRingHom,
      ∀ k,
      (stirlingParameterHom R
        (TerminalBlockKeepIndex Block d Time b) (d b) P).coeff k ∈
          I.map (terminalSplitRenameEquiv R Block d Time b).toRingHom := by
  intro P hP k
  let e := terminalSplitRenameEquiv R Block d Time b
  have hpre : e.symm P ∈ I := by
    exact (Ideal.symm_apply_mem_of_equiv_iff
      (I := I) (f := e.toRingEquiv) (y := P)).2 hP
  have hcoeff := terminalSplitStirlingParameter_coeff_mem_of_global
    R Block d Time I hgraded hJ b (e.symm P) hpre k
  simpa only [e, AlgEquiv.apply_symm_apply] using hcoeff

/-- Global multigrading and simultaneous signed-Stirling invariance imply
preservation of the renamed ideal by every bounded vector field in the chosen
block. -/
theorem terminalSplitBlockVectorFields_preserve
    (I : Ideal (CentralPolynomial R Block d Time))
    (hgraded : IsTerminalMultigradedIdeal R Block d Time I)
    (hJ : IsTerminalGlobalStirlingInvariant R Block d Time I)
    (b : Block) :
    ∀ q, 1 ≤ q → derivationPreservesIdeal
      (I.map (terminalSplitRenameEquiv R Block d Time b).toRingHom)
      (terminalBlockVectorField R
        (TerminalBlockKeepIndex Block d Time b) (d b) q) := by
  let Ib : Ideal
      (MvPolynomial
        (TerminalBlockKeepIndex Block d Time b ⊕ Fin (d b)) R) :=
    I.map (terminalSplitRenameEquiv R Block d Time b).toRingHom
  have hcoeff : ∀ P ∈ Ib, ∀ k,
      (stirlingParameterHom R
        (TerminalBlockKeepIndex Block d Time b) (d b) P).coeff k ∈ Ib := by
    exact terminalSplitStirlingParameter_coeff_mem
      R Block d Time I hgraded hJ b
  have hL₁ : derivationPreservesIdeal Ib
      (stirlingParameterFirstDerivation R
        (TerminalBlockKeepIndex Block d Time b) (d b)) :=
    polynomialParameterFirstDerivation_preserves_ideal
      (stirlingParameterHom R
        (TerminalBlockKeepIndex Block d Time b) (d b))
      (stirlingParameterHom_coeff_zero R
        (TerminalBlockKeepIndex Block d Time b) (d b)) Ib
      (fun P hP ↦ hcoeff P hP 1)
  have hL₂ : derivationPreservesIdeal Ib
      (stirlingParameterSecondLogDerivation R
        (TerminalBlockKeepIndex Block d Time b) (d b)) :=
    polynomialParameterSecondLogDerivation_preserves_ideal
      (stirlingParameterHom R
        (TerminalBlockKeepIndex Block d Time b) (d b))
      (stirlingParameterHom_coeff_zero R
        (TerminalBlockKeepIndex Block d Time b) (d b)) Ib
      (fun P hP ↦ hcoeff P hP 1)
      (fun P hP ↦ hcoeff P hP 2)
  have hV₁ : derivationPreservesIdeal Ib
      (terminalBlockVectorField R
        (TerminalBlockKeepIndex Block d Time b) (d b) 1) := by
    rw [stirlingParameterFirstDerivation_eq_neg_vectorField] at hL₁
    have hneg := hL₁.neg
    rw [neg_neg] at hneg
    exact hneg
  have hhalfV₂ : derivationPreservesIdeal Ib
      ((1 / 2 : ℚ) • terminalBlockVectorField R
        (TerminalBlockKeepIndex Block d Time b) (d b) 2) := by
    rw [← stirlingParameterSecondLogDerivation_eq_half_vectorField]
    exact hL₂
  have hV₂ : derivationPreservesIdeal Ib
      (terminalBlockVectorField R
        (TerminalBlockKeepIndex Block d Time b) (d b) 2) :=
    hhalfV₂.of_smul (by norm_num)
  exact terminalBlockVectorFields_preserve_of_one_two R
    (TerminalBlockKeepIndex Block d Time b) (d b) Ib hV₁ hV₂

end IdealCoefficientClosure

end AbelFormalization
