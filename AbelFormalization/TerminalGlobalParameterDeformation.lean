import AbelFormalization.TerminalGlobalStirling
import Mathlib.Algebra.MvPolynomial.Equiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# The simultaneous terminal Stirling parameter deformation

The signed-Stirling automorphism is refined by one polynomial parameter for
each derivative block.  A parameter exponent records the exact loss of block
weight.  After flattening the nested polynomial ring, parameter weight plus
output-variable weight is conserved.  Consequently a pure parameter
coefficient of a globally homogeneous input is an actual global homogeneous
component of the signed-Stirling image.
-/

noncomputable section

namespace AbelFormalization

universe u v w

section GenericWeightedEvaluation

variable {R S σ τ M : Type*}
variable [CommSemiring R] [CommSemiring S] [AddCommMonoid M]

/-- A weighted-homogeneous polynomial remains homogeneous after evaluation
when coefficients have degree zero and every variable image has its prescribed
source weight. -/
theorem weightedHomogeneous_eval₂
    {sourceWeight : σ → M} {targetWeight : τ → M}
    {P : MvPolynomial σ R} {degree : M}
    (hP : P.IsWeightedHomogeneous sourceWeight degree)
    (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S)
    (hf : ∀ r, (f r).IsWeightedHomogeneous targetWeight 0)
    (hg : ∀ i, (g i).IsWeightedHomogeneous targetWeight (sourceWeight i)) :
    (MvPolynomial.eval₂ f g P).IsWeightedHomogeneous targetWeight degree := by
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro m hm
  have hmcoeff : P.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hmweight : Finsupp.weight sourceWeight m = degree := hP hmcoeff
  rw [← zero_add degree]
  apply (hf (P.coeff m)).mul
  convert MvPolynomial.IsWeightedHomogeneous.prod m.support
      (fun i ↦ g i ^ m i) (fun i ↦ m i • sourceWeight i) ?_ using 1
  · rw [← hmweight, Finsupp.weight_apply]
    rfl
  · intro i hi
    exact (hg i).pow (m i)

/-- Algebraic evaluation is the coefficient-degree-zero case of the preceding
weighted evaluation lemma. -/
theorem weightedHomogeneous_aeval
    [Algebra R S]
    {sourceWeight : σ → M} {targetWeight : τ → M}
    {P : MvPolynomial σ R} {degree : M}
    (hP : P.IsWeightedHomogeneous sourceWeight degree)
    (g : σ → MvPolynomial τ S)
    (hg : ∀ i, (g i).IsWeightedHomogeneous targetWeight (sourceWeight i)) :
    (MvPolynomial.aeval g P).IsWeightedHomogeneous targetWeight degree := by
  rw [MvPolynomial.aeval_def]
  exact weightedHomogeneous_eval₂ hP
    (algebraMap R (MvPolynomial τ S)) g
    (fun r ↦ MvPolynomial.isWeightedHomogeneous_C targetWeight
      (algebraMap R S r)) hg

end GenericWeightedEvaluation

section NestedPolynomialCoefficients

variable {R Parameter Variable : Type*} [CommSemiring R]

/-- Flattening a nested monomial concatenates its two exponent vectors. -/
theorem terminalSumAlgEquiv_symm_monomial
    (parameterExponent : Parameter →₀ ℕ)
    (variableExponent : Variable →₀ ℕ) (a : R) :
    (MvPolynomial.sumAlgEquiv R Parameter Variable).symm
        (MvPolynomial.monomial parameterExponent
          (MvPolynomial.monomial variableExponent a)) =
      MvPolynomial.monomial
        ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm
          (parameterExponent, variableExponent)) a := by
  simp [MvPolynomial.sumAlgEquiv, MvPolynomial.monomial, MvPolynomial]

/-- A coefficient in each layer of a nested polynomial is the corresponding
coefficient of its flattening. -/
theorem terminalSumAlgEquiv_symm_coeff
    (F : MvPolynomial Parameter (MvPolynomial Variable R))
    (parameterExponent : Parameter →₀ ℕ)
    (variableExponent : Variable →₀ ℕ) :
    ((MvPolynomial.sumAlgEquiv R Parameter Variable).symm F).coeff
        ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm
          (parameterExponent, variableExponent)) =
      (F.coeff parameterExponent).coeff variableExponent := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [map_add, MvPolynomial.coeff_add, hP, hQ]
  | monomial outer P =>
      induction P using MvPolynomial.induction_on' with
      | add P Q hP hQ =>
          simp only [map_add, MvPolynomial.coeff_add, hP, hQ]
      | monomial inner a =>
          rw [terminalSumAlgEquiv_symm_monomial]
          by_cases houter : outer = parameterExponent
          · subst outer
            by_cases hinner : inner = variableExponent
            · subst inner
              rw [MvPolynomial.coeff_monomial
                    ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm
                      (parameterExponent, variableExponent))
                    ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm
                      (parameterExponent, variableExponent)) a,
                  ite_eq_left rfl,
                  MvPolynomial.coeff_monomial parameterExponent
                    parameterExponent
                    (MvPolynomial.monomial variableExponent a),
                  ite_eq_left rfl,
                  MvPolynomial.coeff_monomial variableExponent
                    variableExponent a,
                  ite_eq_left rfl]
            · have hcombined :
                  (Finsupp.sumFinsuppAddEquivProdFinsupp).symm
                      (parameterExponent, inner) ≠
                    (Finsupp.sumFinsuppAddEquivProdFinsupp).symm
                      (parameterExponent, variableExponent) := by
                  intro h
                  have hp :=
                    (Finsupp.sumFinsuppAddEquivProdFinsupp).symm.injective h
                  exact hinner (Prod.mk.inj hp).2
              rw [MvPolynomial.coeff_monomial
                    ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm
                      (parameterExponent, variableExponent))
                    ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm
                      (parameterExponent, inner)) a,
                  ite_eq_right hcombined,
                  MvPolynomial.coeff_monomial parameterExponent
                    parameterExponent (MvPolynomial.monomial inner a),
                  ite_eq_left rfl,
                  MvPolynomial.coeff_monomial variableExponent inner a,
                  ite_eq_right hinner]
          · have hcombined :
                (Finsupp.sumFinsuppAddEquivProdFinsupp).symm (outer, inner) ≠
                  (Finsupp.sumFinsuppAddEquivProdFinsupp).symm
                    (parameterExponent, variableExponent) := by
                intro h
                have hp :=
                  (Finsupp.sumFinsuppAddEquivProdFinsupp).symm.injective h
                exact houter (Prod.mk.inj hp).1
            rw [MvPolynomial.coeff_monomial
                  ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm
                    (parameterExponent, variableExponent))
                  ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm
                    (outer, inner)) a,
                ite_eq_right hcombined,
                MvPolynomial.coeff_monomial parameterExponent outer
                  (MvPolynomial.monomial inner a),
                ite_eq_right houter]
            simp

end NestedPolynomialCoefficients

section GlobalParameter

variable (R : Type u) [CommRing R]
variable (Block : Type v) (d : Block → ℕ) (Time : Type w)

/-- The simultaneous parameter image of one global polynomial variable.  The
outer exponent records the loss in its block. -/
def terminalGlobalStirlingParameterVariable
    (x : CentralPolynomialIndex Block d Time) :
    MvPolynomial Block (CentralPolynomial R Block d Time) :=
  match x with
  | Sum.inl ⟨b, r⟩ =>
      ∑ j : Fin (d b),
        MvPolynomial.monomial (Finsupp.single b (r.val - j.val))
          (MvPolynomial.monomial
            (Finsupp.single
              (Sum.inl ⟨b, j⟩ : CentralPolynomialIndex Block d Time) 1)
            (if j ≤ r then
              (signedStirling (r.val + 1) (j.val + 1) : R)
            else 0))
  | Sum.inr t =>
      MvPolynomial.C
        (MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time))

/-- One polynomial parameter for every block refines the global
signed-Stirling automorphism. -/
def terminalGlobalStirlingParameterHom :
    CentralPolynomial R Block d Time →ₐ[R]
      MvPolynomial Block (CentralPolynomial R Block d Time) :=
  MvPolynomial.aeval
    (terminalGlobalStirlingParameterVariable R Block d Time)

@[simp]
theorem terminalGlobalStirlingParameterHom_C (a : R) :
    terminalGlobalStirlingParameterHom R Block d Time (MvPolynomial.C a) =
      MvPolynomial.C (MvPolynomial.C a) := by
  simp [terminalGlobalStirlingParameterHom]

@[simp]
theorem terminalGlobalStirlingParameterHom_X_block
    (b : Block) (r : Fin (d b)) :
    terminalGlobalStirlingParameterHom R Block d Time
        (MvPolynomial.X
          (Sum.inl ⟨b, r⟩ : CentralPolynomialIndex Block d Time)) =
      terminalGlobalStirlingParameterVariable R Block d Time
        (Sum.inl ⟨b, r⟩) := by
  simp [terminalGlobalStirlingParameterHom]

@[simp]
theorem terminalGlobalStirlingParameterHom_X_time (t : Time) :
    terminalGlobalStirlingParameterHom R Block d Time
        (MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time)) =
      MvPolynomial.C
        (MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time)) := by
  simp [terminalGlobalStirlingParameterHom,
    terminalGlobalStirlingParameterVariable]

/-- Joint weight on parameter variables and output polynomial variables. -/
def terminalGlobalParameterWeight :
    Block ⊕ CentralPolynomialIndex Block d Time → TerminalMultidegree Block
  | Sum.inl b => Finsupp.single b 1
  | Sum.inr x => terminalGlobalWeight Block d Time x

/-- Flatten the simultaneous parameter polynomial to expose its conserved
joint multidegree. -/
def terminalGlobalStirlingParameterFlatHom :
    CentralPolynomial R Block d Time →ₐ[R]
      MvPolynomial (Block ⊕ CentralPolynomialIndex Block d Time) R :=
  (MvPolynomial.sumAlgEquiv R Block
      (CentralPolynomialIndex Block d Time)).symm.toAlgHom.comp
    (terminalGlobalStirlingParameterHom R Block d Time)

theorem terminalGlobalParameterWeight_parameters
    (parameterExponent : Block →₀ ℕ) :
    Finsupp.weight (terminalGlobalParameterWeight Block d Time)
        (Finsupp.mapDomain Sum.inl parameterExponent) =
      parameterExponent := by
  classical
  induction parameterExponent using Finsupp.induction with
  | zero => simp
  | @single_add b n f hb hn hf =>
      rw [Finsupp.mapDomain_add, map_add, hf]
      rw [Finsupp.mapDomain_single, Finsupp.weight_single]
      ext c
      by_cases hbc : b = c
      · subst c
        simp [terminalGlobalParameterWeight]
      · simp [terminalGlobalParameterWeight, Finsupp.single_apply, hbc]

theorem terminalGlobalParameterWeight_variables
    (variableExponent : CentralPolynomialIndex Block d Time →₀ ℕ) :
    Finsupp.weight (terminalGlobalParameterWeight Block d Time)
        (Finsupp.mapDomain Sum.inr variableExponent) =
      Finsupp.weight (terminalGlobalWeight Block d Time) variableExponent := by
  classical
  induction variableExponent using Finsupp.induction with
  | zero => simp
  | @single_add x n f hx hn hf =>
      rw [Finsupp.mapDomain_add, map_add, hf, map_add]
      rw [Finsupp.mapDomain_single, Finsupp.weight_single,
        Finsupp.weight_single]
      rfl

/-- The joint weight of concatenated exponents is parameter loss plus
remaining global-variable weight. -/
theorem terminalGlobalParameterWeight_split
    (parameterExponent : Block →₀ ℕ)
    (variableExponent : CentralPolynomialIndex Block d Time →₀ ℕ) :
    Finsupp.weight (terminalGlobalParameterWeight Block d Time)
        ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm
          (parameterExponent, variableExponent)) =
      parameterExponent +
        Finsupp.weight (terminalGlobalWeight Block d Time) variableExponent := by
  rw [show (Finsupp.sumFinsuppAddEquivProdFinsupp).symm
      (parameterExponent, variableExponent) =
        Finsupp.sumElim parameterExponent variableExponent by rfl,
    Finsupp.sumElim_eq_add, map_add,
    terminalGlobalParameterWeight_parameters,
    terminalGlobalParameterWeight_variables]

theorem terminalGlobalStirlingParameterFlatHom_X_block
    (b : Block) (r : Fin (d b)) :
    terminalGlobalStirlingParameterFlatHom R Block d Time
        (MvPolynomial.X
          (Sum.inl ⟨b, r⟩ : CentralPolynomialIndex Block d Time)) =
      ∑ j : Fin (d b),
        MvPolynomial.monomial
          ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm
            (Finsupp.single b (r.val - j.val),
              Finsupp.single
                (Sum.inl ⟨b, j⟩ : CentralPolynomialIndex Block d Time) 1))
          (if j ≤ r then
            (signedStirling (r.val + 1) (j.val + 1) : R)
          else 0) := by
  classical
  simp [terminalGlobalStirlingParameterFlatHom,
    terminalGlobalStirlingParameterVariable,
    terminalSumAlgEquiv_symm_monomial]

theorem terminalGlobalStirlingParameterFlatHom_X_time (t : Time) :
    terminalGlobalStirlingParameterFlatHom R Block d Time
        (MvPolynomial.X
          (Sum.inr t : CentralPolynomialIndex Block d Time)) =
      MvPolynomial.X (Sum.inr
        (Sum.inr t : CentralPolynomialIndex Block d Time)) := by
  simp [terminalGlobalStirlingParameterFlatHom,
    terminalGlobalStirlingParameterHom,
    terminalGlobalStirlingParameterVariable]

/-- Every generator image has exactly its original global multidegree after
parameter and output weights are added. -/
theorem terminalGlobalStirlingParameterFlatHom_X_isWeightedHomogeneous
    (x : CentralPolynomialIndex Block d Time) :
    MvPolynomial.IsWeightedHomogeneous
      (terminalGlobalParameterWeight Block d Time)
      (terminalGlobalStirlingParameterFlatHom R Block d Time
        (MvPolynomial.X x))
      (terminalGlobalWeight Block d Time x) := by
  classical
  rcases x with ⟨b, r⟩ | t
  · rw [terminalGlobalStirlingParameterFlatHom_X_block]
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro j hj
    by_cases hjr : j ≤ r
    · apply MvPolynomial.isWeightedHomogeneous_monomial
      rw [terminalGlobalParameterWeight_split]
      rw [Finsupp.weight_single, one_nsmul,
        terminalGlobalWeight_block]
      ext c
      by_cases hcb : c = b
      · subst c
        simp [Finsupp.single_apply]
        omega
      · simp [Finsupp.single_apply, hcb]
    · simp only [hjr, ↓reduceIte, MvPolynomial.monomial_zero]
      exact MvPolynomial.isWeightedHomogeneous_zero R
        (terminalGlobalParameterWeight Block d Time)
        (terminalGlobalWeight Block d Time (Sum.inl ⟨b, r⟩))
  · rw [terminalGlobalStirlingParameterFlatHom_X_time]
    simpa [terminalGlobalParameterWeight, terminalGlobalWeight] using
      MvPolynomial.isWeightedHomogeneous_X R
        (terminalGlobalParameterWeight Block d Time)
        (Sum.inr (Sum.inr t : CentralPolynomialIndex Block d Time))

/-- The flattened parameter deformation preserves every actual global
homogeneous degree. -/
theorem terminalGlobalStirlingParameterFlatHom_isWeightedHomogeneous
    {P : CentralPolynomial R Block d Time}
    {degree : TerminalMultidegree Block}
    (hP : MvPolynomial.IsWeightedHomogeneous
      (terminalGlobalWeight Block d Time) P degree) :
    MvPolynomial.IsWeightedHomogeneous
      (terminalGlobalParameterWeight Block d Time)
      (terminalGlobalStirlingParameterFlatHom R Block d Time P) degree := by
  let F : CentralPolynomial R Block d Time →ₐ[R]
      MvPolynomial (Block ⊕ CentralPolynomialIndex Block d Time) R :=
    MvPolynomial.aeval (fun x ↦
      terminalGlobalStirlingParameterFlatHom R Block d Time
        (MvPolynomial.X x))
  have hF : F = terminalGlobalStirlingParameterFlatHom R Block d Time := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [F]
  rw [← hF]
  exact weightedHomogeneous_aeval hP _
    (terminalGlobalStirlingParameterFlatHom_X_isWeightedHomogeneous
      R Block d Time)

/-- Every nonzero monomial of a parameter coefficient satisfies the exact
additive degree equation: parameter loss plus remaining variable degree is
the input degree. -/
theorem terminalGlobalStirlingParameter_coeff_degree
    {P : CentralPolynomial R Block d Time}
    {degree : TerminalMultidegree Block}
    (hP : MvPolynomial.IsWeightedHomogeneous
      (terminalGlobalWeight Block d Time) P degree)
    {parameterExponent : Block →₀ ℕ}
    {variableExponent : CentralPolynomialIndex Block d Time →₀ ℕ}
    (hcoeff :
      ((terminalGlobalStirlingParameterHom R Block d Time P).coeff
        parameterExponent).coeff variableExponent ≠ 0) :
    parameterExponent +
        Finsupp.weight (terminalGlobalWeight Block d Time) variableExponent =
      degree := by
  have hflat :=
    terminalGlobalStirlingParameterFlatHom_isWeightedHomogeneous
      R Block d Time hP
  have hflatCoeff :
      (terminalGlobalStirlingParameterFlatHom R Block d Time P).coeff
          ((Finsupp.sumFinsuppAddEquivProdFinsupp).symm
            (parameterExponent, variableExponent)) ≠ 0 := by
    rw [terminalGlobalStirlingParameterFlatHom, AlgHom.comp_apply]
    intro hzero
    apply hcoeff
    rw [← terminalSumAlgEquiv_symm_coeff
      (R := R) (Parameter := Block)
      (Variable := CentralPolynomialIndex Block d Time)
      (terminalGlobalStirlingParameterHom R Block d Time P)
      parameterExponent variableExponent]
    exact hzero
  have hdegree := hflat hflatCoeff
  rwa [terminalGlobalParameterWeight_split] at hdegree

/-- Evaluation of all block parameters at one is the actual simultaneous
signed-Stirling automorphism. -/
theorem terminalGlobalStirlingParameter_eval_one
    (P : CentralPolynomial R Block d Time) :
    MvPolynomial.eval
        (fun _ : Block ↦ (1 : CentralPolynomial R Block d Time))
        (terminalGlobalStirlingParameterHom R Block d Time P) =
      terminalGlobalStirlingEquiv R Block d Time P := by
  let E : CentralPolynomial R Block d Time →+*
      CentralPolynomial R Block d Time :=
    (MvPolynomial.eval
      (fun _ : Block ↦ (1 : CentralPolynomial R Block d Time))).comp
        (terminalGlobalStirlingParameterHom R Block d Time).toRingHom
  have hE : E = (terminalGlobalStirlingEquiv R Block d Time).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [E]
    · intro x
      rcases x with ⟨b, r⟩ | t
      · rw [show E (MvPolynomial.X
              (Sum.inl ⟨b, r⟩ : CentralPolynomialIndex Block d Time)) =
            MvPolynomial.eval
              (fun _ : Block ↦ (1 : CentralPolynomial R Block d Time))
              (terminalGlobalStirlingParameterVariable R Block d Time
                (Sum.inl ⟨b, r⟩)) by
            simp [E]]
        change
          MvPolynomial.eval
              (fun _ : Block ↦ (1 : CentralPolynomial R Block d Time))
              (terminalGlobalStirlingParameterVariable R Block d Time
                (Sum.inl ⟨b, r⟩)) =
            terminalGlobalStirlingEquiv R Block d Time
              (MvPolynomial.X
                (Sum.inl ⟨b, r⟩ : CentralPolynomialIndex Block d Time))
        rw [terminalGlobalStirlingEquiv_X_block]
        simp [terminalGlobalStirlingParameterVariable,
          MvPolynomial.eval_monomial,
          ← MvPolynomial.C_mul_X_eq_monomial]
      · simp [E, terminalGlobalStirlingParameterVariable]
  exact RingHom.congr_fun hE P

/-- Evaluating all parameters at one is the finite sum of all parameter
coefficients. -/
theorem terminalGlobalParameter_eval_one_eq_sum_coeff
    (F : MvPolynomial Block (CentralPolynomial R Block d Time)) :
    MvPolynomial.eval
        (fun _ : Block ↦ (1 : CentralPolynomial R Block d Time)) F =
      ∑ parameterExponent ∈ F.support, F.coeff parameterExponent := by
  rw [MvPolynomial.eval_eq]
  simp

/-- For a homogeneous input, a parameter coefficient whose exponent completes
`outputDegree` to the input degree is exactly that component of the global
signed-Stirling image. -/
theorem terminalGlobalStirlingParameter_coeff_eq_component_of_add
    {P : CentralPolynomial R Block d Time}
    {inputDegree outputDegree parameterExponent : TerminalMultidegree Block}
    (hP : MvPolynomial.IsWeightedHomogeneous
      (terminalGlobalWeight Block d Time) P inputDegree)
    (hadd : outputDegree + parameterExponent = inputDegree) :
    (terminalGlobalStirlingParameterHom R Block d Time P).coeff
        parameterExponent =
      terminalGlobalComponent R Block d Time outputDegree
        (terminalGlobalStirlingEquiv R Block d Time P) := by
  classical
  let G := terminalGlobalStirlingParameterHom R Block d Time P
  have hsame : MvPolynomial.IsWeightedHomogeneous
      (terminalGlobalWeight Block d Time) (G.coeff parameterExponent)
      outputDegree := by
    intro m hm
    have hdegree := terminalGlobalStirlingParameter_coeff_degree
      R Block d Time hP hm
    have heq : parameterExponent +
        Finsupp.weight (terminalGlobalWeight Block d Time) m =
          parameterExponent + outputDegree := by
      calc
        parameterExponent +
            Finsupp.weight (terminalGlobalWeight Block d Time) m =
          inputDegree := hdegree
        _ = outputDegree + parameterExponent := hadd.symm
        _ = parameterExponent + outputDegree := add_comm _ _
    exact add_left_cancel heq
  have hother (other : TerminalMultidegree Block)
      (hne : other ≠ parameterExponent) :
      terminalGlobalComponent R Block d Time outputDegree
          (G.coeff other) = 0 := by
    apply MvPolynomial.weightedHomogeneousComponent_eq_zero'
    intro m hm
    have hmcoeff : (G.coeff other).coeff m ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hm
    have hdegree := terminalGlobalStirlingParameter_coeff_degree
      R Block d Time hP hmcoeff
    intro hweight
    have heq : other + outputDegree = parameterExponent + outputDegree := by
      calc
        other + outputDegree =
            other + Finsupp.weight
              (terminalGlobalWeight Block d Time) m := by rw [hweight]
        _ = inputDegree := hdegree
        _ = outputDegree + parameterExponent := hadd.symm
        _ = parameterExponent + outputDegree := add_comm _ _
    exact hne (add_right_cancel heq)
  have hJ : terminalGlobalStirlingEquiv R Block d Time P =
      ∑ other ∈ G.support, G.coeff other := by
    rw [← terminalGlobalStirlingParameter_eval_one R Block d Time P,
      terminalGlobalParameter_eval_one_eq_sum_coeff]
  symm
  rw [hJ, map_sum]
  by_cases hmem : parameterExponent ∈ G.support
  · rw [Finset.sum_eq_single parameterExponent]
    · exact hsame.weightedHomogeneousComponent_same
    · intro other hotherMem hne
      exact hother other hne
    · intro hnot
      exact (hnot hmem).elim
  · have hzero : G.coeff parameterExponent = 0 :=
      MvPolynomial.notMem_support_iff.mp hmem
    rw [hzero]
    apply Finset.sum_eq_zero
    intro other hotherMem
    exact hother other (fun heq ↦ hmem (heq ▸ hotherMem))

end GlobalParameter

end AbelFormalization
