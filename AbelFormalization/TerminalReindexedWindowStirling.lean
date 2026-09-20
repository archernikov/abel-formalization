import AbelFormalization.PolynomialWindowDescent
import AbelFormalization.TerminalGlobalParameterDeformation

set_option autoImplicit false

/-!
# The terminal Stirling automorphism in finite window coordinates

This is a source draft for the remaining terminal/window bridge.  The core
definitions below deliberately take an explicit finite reindexing.  A final
application may use `(Finite.equivFin _).symm`, but none of the proofs should
depend on that arbitrary enumeration of the polynomial variables.

The declarations through strict multidegree loss form the foundational bridge
to the finite-window API.  The last section restricts the automorphism to the
ordinary-degree window and transports its strict lowering property to the
ordered finite product.  This file contains no unsupported assumption or placeholder proof.
-/

noncomputable section

namespace AbelFormalization

universe u w

variable {R : Type u} [CommRing R]
variable {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)

/-- A chosen enumeration of all terminal polynomial variables. -/
abbrev TerminalFiniteReindex :=
  Fin n ≃ CentralPolynomialIndex (Fin h) d Time

/-- Rename finite variables to the block/time presentation. -/
def terminalReindexedRenameEquiv
    (e : TerminalFiniteReindex (n := n) d Time) :
    MvPolynomial (Fin n) R ≃ₐ[R] CentralPolynomial R (Fin h) d Time :=
  MvPolynomial.renameEquiv R e

/-- Conjugate the simultaneous signed-Stirling automorphism through a finite
enumeration of its variables. -/
def terminalReindexedGlobalStirlingEquiv
    (e : TerminalFiniteReindex (n := n) d Time) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R :=
  (terminalReindexedRenameEquiv (R := R) d Time e).trans
    ((terminalGlobalStirlingEquiv R (Fin h) d Time).trans
      (terminalReindexedRenameEquiv (R := R) d Time e).symm)

/-- Total polynomial degree and the genuine block multidegree, transported
to finite variables.  The rank-one module has zero shifts. -/
def terminalReindexedGradedLexData
    (e : TerminalFiniteReindex (n := n) d Time) :
    PolynomialGradedLexData n 1 h where
  ordinaryDegree := fun _ ↦ 1
  multiDegree := fun i b ↦
    ((terminalGlobalWeight (Fin h) d Time (e i)) b : ℤ)
  ordinaryShift := fun _ ↦ 0
  multiShift := fun _ _ ↦ 0

@[simp]
theorem terminalReindexedGradedLexData_ordinaryDegree
    (e : TerminalFiniteReindex (n := n) d Time) (i : Fin n) :
    (terminalReindexedGradedLexData d Time e).ordinaryDegree i = 1 :=
  rfl

theorem terminalReindexedGradedLexData_ordinaryDegree_pos
    (e : TerminalFiniteReindex (n := n) d Time) :
    ∀ i : Fin n,
      0 < (terminalReindexedGradedLexData d Time e).ordinaryDegree i := by
  intro i
  simp

@[simp]
theorem terminalReindexedGradedLexData_multiDegree
    (e : TerminalFiniteReindex (n := n) d Time) (i : Fin n) (b : Fin h) :
    (terminalReindexedGradedLexData d Time e).multiDegree i b =
      ((terminalGlobalWeight (Fin h) d Time (e i)) b : ℤ) :=
  rfl

/-- Apply the reindexed algebra equivalence in the unique free-module
coordinate. -/
def terminalReindexedGlobalStirlingModuleEquiv
    (e : TerminalFiniteReindex (n := n) d Time) :
    artinianFreePolynomialModule R n 1 ≃ₗ[R]
      artinianFreePolynomialModule R n 1 :=
  LinearEquiv.piCongrRight (fun _ : Fin 1 ↦
    (terminalReindexedGlobalStirlingEquiv (R := R) d Time e).toLinearEquiv)

@[simp]
theorem terminalReindexedGlobalStirlingModuleEquiv_apply
    (e : TerminalFiniteReindex (n := n) d Time)
    (P : artinianFreePolynomialModule R n 1) (k : Fin 1) :
    terminalReindexedGlobalStirlingModuleEquiv (R := R) d Time e P k =
      terminalReindexedGlobalStirlingEquiv (R := R) d Time e (P k) :=
  rfl

/-! ## Parameter-zero and multidegree transport helpers -/

/-- The zero-parameter coefficient of each global parameter-variable image
is its diagonal variable. -/
@[simp]
theorem terminalGlobalStirlingParameterVariable_coeff_zero
    (x : CentralPolynomialIndex (Fin h) d Time) :
    (terminalGlobalStirlingParameterVariable R (Fin h) d Time x).coeff 0 =
      MvPolynomial.X x := by
  classical
  rcases x with ⟨b, r⟩ | t
  · change
      (MvPolynomial.coeffAddMonoidHom (0 : Fin h →₀ ℕ))
          (∑ j : Fin (d b),
            MvPolynomial.monomial (Finsupp.single b (r.val - j.val))
              (MvPolynomial.monomial
                (Finsupp.single
                  (Sum.inl ⟨b, j⟩ :
                    CentralPolynomialIndex (Fin h) d Time) 1)
                (if j ≤ r then
                  (signedStirling (r.val + 1) (j.val + 1) : R)
                else 0))) =
        MvPolynomial.X
          (Sum.inl ⟨b, r⟩ : CentralPolynomialIndex (Fin h) d Time)
    rw [map_sum]
    change
      (∑ j : Fin (d b),
        (MvPolynomial.monomial (Finsupp.single b (r.val - j.val))
          (MvPolynomial.monomial
            (Finsupp.single
              (Sum.inl ⟨b, j⟩ :
                CentralPolynomialIndex (Fin h) d Time) 1)
            (if j ≤ r then
              (signedStirling (r.val + 1) (j.val + 1) : R)
            else 0))).coeff 0) = _
    rw [Finset.sum_eq_single r]
    · simp [signedStirling_self, ← MvPolynomial.C_mul_X_eq_monomial]
    · intro j hj hne
      by_cases hjr : j ≤ r
      · have hlt : j < r := lt_of_le_of_ne hjr hne
        have hpos : 0 < r.val - j.val := by omega
        have hsingle : Finsupp.single b (r.val - j.val) ≠
            (0 : Fin h →₀ ℕ) := by
          intro hzero
          have hb := congrFun (congrArg DFunLike.coe hzero) b
          simp [hpos.ne'] at hb
        rw [MvPolynomial.coeff_monomial, ite_eq_right hsingle]
      · simp [hjr]
    · intro hmissing
      exact (hmissing (Finset.mem_univ r)).elim
  · simp [terminalGlobalStirlingParameterVariable]

/-- Taking the zero parameter coefficient of the global deformation is the
identity homomorphism. -/
@[simp]
theorem terminalGlobalStirlingParameterHom_coeff_zero
    (P : CentralPolynomial R (Fin h) d Time) :
    (terminalGlobalStirlingParameterHom R (Fin h) d Time P).coeff 0 = P := by
  have h :
      MvPolynomial.constantCoeff.comp
          (terminalGlobalStirlingParameterHom R (Fin h) d Time).toRingHom =
        RingHom.id (CentralPolynomial R (Fin h) d Time) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · rintro (⟨b, r⟩ | t)
      · simp only [RingHom.comp_apply,
          RingHom.id_apply]
        change
          (terminalGlobalStirlingParameterHom R (Fin h) d Time
            (MvPolynomial.X (Sum.inl ⟨b, r⟩))).coeff 0 = _
        rw [terminalGlobalStirlingParameterHom_X_block]
        exact terminalGlobalStirlingParameterVariable_coeff_zero
          (R := R) d Time (Sum.inl ⟨b, r⟩)
      · simp [terminalGlobalStirlingParameterVariable]
  exact RingHom.congr_fun h P

/-- Coordinatewise coercion of a natural terminal multidegree to an integral
multidegree. -/
def terminalMultidegreeCast (h : ℕ) :
    TerminalMultidegree (Fin h) →+ (Fin h → ℤ) where
  toFun α := fun b ↦ (α b : ℤ)
  map_zero' := by
    funext b
    simp
  map_add' α β := by
    funext b
    simp

@[simp]
theorem terminalMultidegreeCast_apply
    (α : TerminalMultidegree (Fin h)) (b : Fin h) :
    terminalMultidegreeCast h α b = (α b : ℤ) :=
  rfl

/-- Embed natural terminal multidegrees into the lexicographically ordered
integral weight group used by `PolynomialGradedLexData`. -/
def terminalMultidegreeToLex
    (α : TerminalMultidegree (Fin h)) : PolynomialLexWeight h :=
  toLex (terminalMultidegreeCast h α)

theorem terminalMultidegreeToLex_injective :
    Function.Injective (terminalMultidegreeToLex (h := h)) := by
  intro α β hαβ
  apply Finsupp.ext
  intro b
  have hb : (α b : ℤ) = (β b : ℤ) :=
    congrFun (toLex_inj.mp hαβ) b
  exact Nat.cast_injective hb

/-- A nonzero natural loss makes the remaining multidegree strictly smaller
after passage to the lexicographic integral weight group. -/
theorem terminalMultidegreeToLex_lt_of_add_eq
    {κ output input : TerminalMultidegree (Fin h)}
    (hκ : κ ≠ 0) (hadd : κ + output = input) :
    terminalMultidegreeToLex output < terminalMultidegreeToLex input := by
  apply Pi.toLex_strictMono
  apply lt_of_le_of_ne
  · intro b
    change (output b : ℤ) ≤ (input b : ℤ)
    have hb : κ b + output b = input b :=
      congrArg (fun α : TerminalMultidegree (Fin h) ↦ α b) hadd
    omega
  · intro heq
    apply hκ
    apply Finsupp.ext
    intro b
    have hb : κ b + output b = input b :=
      congrArg (fun α : TerminalMultidegree (Fin h) ↦ α b) hadd
    have hout : output b = input b :=
      Nat.cast_injective (congrFun heq b)
    rw [Finsupp.zero_apply]
    omega

/-- Weighted degree commutes with transporting a finite exponent along the
chosen variable equivalence. -/
theorem terminalGlobalWeight_mapDomain
    (e : TerminalFiniteReindex (n := n) d Time) (m : Fin n →₀ ℕ) :
    Finsupp.weight (terminalGlobalWeight (Fin h) d Time) (m.mapDomain e) =
      Finsupp.weight
        (fun i ↦ terminalGlobalWeight (Fin h) d Time (e i)) m := by
  classical
  induction m using Finsupp.induction with
  | zero => simp
  | @single_add i c f hi hc ih =>
      simp [Finsupp.mapDomain_add, Finsupp.mapDomain_single,
        Finsupp.weight_single, ih]

/-- Weighted homogeneity is transported by renaming variables along an
equivalence. -/
theorem weightedHomogeneous_renameEquiv
    {σ τ M : Type*} [AddCommMonoid M]
    (e : σ ≃ τ) (weight : τ → M)
    {P : MvPolynomial σ R} {degree : M}
    (hP : P.IsWeightedHomogeneous (weight ∘ e) degree) :
    (MvPolynomial.renameEquiv R e P).IsWeightedHomogeneous weight degree := by
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_eq_aeval]
  exact weightedHomogeneous_aeval hP _ (fun i ↦ by
    simpa [Function.comp_apply] using
      MvPolynomial.isWeightedHomogeneous_X R weight (e i))

/-- Reindexing the terminal variables transports the genuine terminal
multidegree to the `termWeight` stored in the finite polynomial grading. -/
theorem terminalReindexedGradedLexData_termWeight
    (e : TerminalFiniteReindex (n := n) d Time) (m : Fin n →₀ ℕ) :
    (terminalReindexedGradedLexData d Time e).termWeight (0, m) =
      terminalMultidegreeToLex
        (Finsupp.weight (terminalGlobalWeight (Fin h) d Time)
          (m.mapDomain e)) := by
  classical
  have hweight :
      Finsupp.weight
          (fun i b ↦
            ((terminalGlobalWeight (Fin h) d Time (e i)) b : ℤ)) m =
        terminalMultidegreeCast h
          (Finsupp.weight (terminalGlobalWeight (Fin h) d Time)
            (m.mapDomain e)) := by
    induction m using Finsupp.induction with
    | zero => simp
    | @single_add i c f hi hc ih =>
        simp [Finsupp.mapDomain_add, Finsupp.mapDomain_single,
          Finsupp.weight_single, ih, terminalMultidegreeCast,
          Nat.cast_add, Nat.cast_mul]
        rfl
  change toLex
      (Finsupp.weight
          (fun i b ↦
            ((terminalGlobalWeight (Fin h) d Time (e i)) b : ℤ)) m +
        (0 : Fin h → ℤ)) = _
  rw [add_zero]
  exact congrArg toLex hweight

/-! ## Strict lowering of genuine terminal multidegree -/

/-- On a genuinely terminal-homogeneous input, subtracting the diagonal term
from the global Stirling image leaves only strictly smaller lexicographic
terminal weights. -/
theorem terminalGlobalStirlingEquiv_sub_self_weight_lt
    {P : CentralPolynomial R (Fin h) d Time}
    {inputDegree : TerminalMultidegree (Fin h)}
    (hP : P.IsWeightedHomogeneous
      (terminalGlobalWeight (Fin h) d Time) inputDegree)
    {m : CentralPolynomialIndex (Fin h) d Time →₀ ℕ}
    (hm :
      (terminalGlobalStirlingEquiv R (Fin h) d Time P - P).coeff m ≠ 0) :
    terminalMultidegreeToLex
        (Finsupp.weight (terminalGlobalWeight (Fin h) d Time) m) <
      terminalMultidegreeToLex inputDegree := by
  classical
  by_cases hPzero : P = 0
  · subst P
    simp at hm
  · let F := terminalGlobalStirlingParameterHom R (Fin h) d Time P
    have hzero : F.coeff 0 = P :=
      terminalGlobalStirlingParameterHom_coeff_zero
        (R := R) d Time P
    have hzeroMem : (0 : Fin h →₀ ℕ) ∈ F.support := by
      apply MvPolynomial.mem_support_iff.mpr
      rw [hzero]
      exact hPzero
    have hJ : terminalGlobalStirlingEquiv R (Fin h) d Time P =
        ∑ κ ∈ F.support, F.coeff κ := by
      rw [← terminalGlobalStirlingParameter_eval_one R (Fin h) d Time P,
        terminalGlobalParameter_eval_one_eq_sum_coeff]
    have hdiff : terminalGlobalStirlingEquiv R (Fin h) d Time P - P =
        ∑ κ ∈ F.support.erase 0, F.coeff κ := by
      rw [hJ, ← hzero,
        ← F.support.sum_erase_add (fun κ ↦ F.coeff κ) hzeroMem]
      abel
    rw [hdiff, MvPolynomial.coeff_sum] at hm
    obtain ⟨κ, hκMem, hκCoeff⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero hm
    have hκ : κ ≠ 0 := (Finset.mem_erase.mp hκMem).1
    have hdegree : κ +
        Finsupp.weight (terminalGlobalWeight (Fin h) d Time) m =
          inputDegree :=
      terminalGlobalStirlingParameter_coeff_degree
        R (Fin h) d Time hP hκCoeff
    exact terminalMultidegreeToLex_lt_of_add_eq hκ hdegree

/-- The strict lowering statement after conjugating the global Stirling map
through the chosen finite enumeration of terminal variables. -/
theorem terminalReindexedGlobalStirlingEquiv_sub_self_weight_lt
    (e : TerminalFiniteReindex (n := n) d Time)
    {P : MvPolynomial (Fin n) R} {weight : PolynomialLexWeight h}
    (hP : ∀ m, P.coeff m ≠ 0 →
      (terminalReindexedGradedLexData d Time e).termWeight
        (0, m) = weight)
    {m : Fin n →₀ ℕ}
    (hm :
      (terminalReindexedGlobalStirlingEquiv (R := R) d Time e P - P).coeff m ≠
        0) :
    (terminalReindexedGradedLexData d Time e).termWeight (0, m) <
      weight := by
  classical
  by_cases hPzero : P = 0
  · subst P
    simp at hm
  · obtain ⟨m₀, hm₀⟩ := MvPolynomial.exists_coeff_ne_zero hPzero
    let inputDegree : TerminalMultidegree (Fin h) :=
      Finsupp.weight (terminalGlobalWeight (Fin h) d Time)
        (m₀.mapDomain e)
    have hinputWeight : terminalMultidegreeToLex inputDegree = weight := by
      have hm₀Weight := hP m₀ hm₀
      rw [terminalReindexedGradedLexData_termWeight d Time e m₀]
        at hm₀Weight
      simpa only [inputDegree] using hm₀Weight
    have hPhom : P.IsWeightedHomogeneous
        (fun i ↦ terminalGlobalWeight (Fin h) d Time (e i))
        inputDegree := by
      intro m' hm'
      have hm'Weight := hP m' hm'
      rw [terminalReindexedGradedLexData_termWeight d Time e m']
        at hm'Weight
      have hlex :
          terminalMultidegreeToLex
              (Finsupp.weight (terminalGlobalWeight (Fin h) d Time)
                (m'.mapDomain e)) =
            terminalMultidegreeToLex inputDegree :=
        hm'Weight.trans hinputWeight.symm
      have hdegree := terminalMultidegreeToLex_injective hlex
      exact (terminalGlobalWeight_mapDomain d Time e m').symm.trans hdegree
    have hQhom :
        (terminalReindexedRenameEquiv (R := R) d Time e P).IsWeightedHomogeneous
          (terminalGlobalWeight (Fin h) d Time) inputDegree := by
      apply weightedHomogeneous_renameEquiv
      change P.IsWeightedHomogeneous
        (fun i ↦ terminalGlobalWeight (Fin h) d Time (e i)) inputDegree
      exact hPhom
    have hconj :
        terminalReindexedRenameEquiv (R := R) d Time e
            (terminalReindexedGlobalStirlingEquiv
                (R := R) d Time e P - P) =
          terminalGlobalStirlingEquiv R (Fin h) d Time
              (terminalReindexedRenameEquiv (R := R) d Time e P) -
            terminalReindexedRenameEquiv (R := R) d Time e P := by
      simp [terminalReindexedGlobalStirlingEquiv]
    have hmGlobal :
        (terminalGlobalStirlingEquiv R (Fin h) d Time
              (terminalReindexedRenameEquiv (R := R) d Time e P) -
            terminalReindexedRenameEquiv (R := R) d Time e P).coeff
          (m.mapDomain e) ≠ 0 := by
      rw [← hconj]
      change
        (MvPolynomial.rename e
            (terminalReindexedGlobalStirlingEquiv
                (R := R) d Time e P - P)).coeff (m.mapDomain e) ≠ 0
      rw [MvPolynomial.coeff_rename_mapDomain e e.injective]
      exact hm
    have hlower := terminalGlobalStirlingEquiv_sub_self_weight_lt
      (R := R) d Time hQhom hmGlobal
    rw [terminalReindexedGradedLexData_termWeight d Time e m,
      ← hinputWeight]
    exact hlower

/-! ## Ordinary degree and the bounded window -/

/-- A block-linear substitution which fixes the retained variables preserves
ordinary homogeneous degree. -/
theorem centralBlockAffineHom_zero_isHomogeneous
    (A : ∀ b : Fin h, Matrix (Fin (d b)) (Fin (d b)) R)
    {P : CentralPolynomial R (Fin h) d Time} {degree : ℕ}
    (hP : P.IsHomogeneous degree) :
    (centralBlockAffineHom R (Fin h) d Time A (fun _ ↦ 0) P).IsHomogeneous
      degree := by
  have hvariable :
      ∀ x : CentralPolynomialIndex (Fin h) d Time,
        (centralBlockAffineVariable R (Fin h) d Time A
          (fun _ ↦ 0) x).IsHomogeneous 1 := by
    rintro (⟨b, i⟩ | t)
    · change
        (∑ j : Fin (d b), MvPolynomial.C (A b i j) *
          MvPolynomial.X
            (Sum.inl ⟨b, j⟩ :
              CentralPolynomialIndex (Fin h) d Time)).IsHomogeneous 1
      apply MvPolynomial.IsHomogeneous.sum
      intro j hj
      exact MvPolynomial.isHomogeneous_C_mul_X _ _
    · change
        (MvPolynomial.X
            (Sum.inr t : CentralPolynomialIndex (Fin h) d Time) +
          MvPolynomial.C (0 : R)).IsHomogeneous 1
      simpa using MvPolynomial.isHomogeneous_X R
        (Sum.inr t : CentralPolynomialIndex (Fin h) d Time)
  have hEval := hP.aeval
    (centralBlockAffineVariable R (Fin h) d Time A (fun _ ↦ 0))
    hvariable
  simpa [centralBlockAffineHom] using hEval

theorem terminalGlobalStirlingEquiv_isHomogeneous
    {P : CentralPolynomial R (Fin h) d Time} {degree : ℕ}
    (hP : P.IsHomogeneous degree) :
    (terminalGlobalStirlingEquiv R (Fin h) d Time P).IsHomogeneous degree := by
  change
    (centralBlockAffineHom R (Fin h) d Time
      (fun b ↦ centralSignedStirlingMatrix R (d b))
      (fun _ ↦ 0) P).IsHomogeneous degree
  exact centralBlockAffineHom_zero_isHomogeneous d Time _ hP

theorem terminalGlobalStirlingEquiv_symm_isHomogeneous
    {P : CentralPolynomial R (Fin h) d Time} {degree : ℕ}
    (hP : P.IsHomogeneous degree) :
    ((terminalGlobalStirlingEquiv R (Fin h) d Time).symm P).IsHomogeneous
      degree := by
  change
    (centralBlockAffineHom R (Fin h) d Time
      (fun b ↦ (centralSignedStirlingMatrix R (d b))⁻¹)
      (fun _ ↦ 0) P).IsHomogeneous degree
  exact centralBlockAffineHom_zero_isHomogeneous d Time _ hP

/-- Both directions of the terminal automorphism preserve homogeneous degree
after transporting through a finite enumeration of the variables. -/
theorem terminalReindexedGlobalStirlingEquiv_isHomogeneous
    (e : TerminalFiniteReindex (n := n) d Time)
    {P : MvPolynomial (Fin n) R} {degree : ℕ}
    (hP : P.IsHomogeneous degree) :
    (terminalReindexedGlobalStirlingEquiv
      (R := R) d Time e P).IsHomogeneous degree := by
  have hrename :
      (terminalReindexedRenameEquiv
        (R := R) d Time e P).IsHomogeneous degree := by
    change (MvPolynomial.rename e P).IsHomogeneous degree
    exact hP.rename_isHomogeneous
  have hglobal := terminalGlobalStirlingEquiv_isHomogeneous
    (R := R) d Time hrename
  have hback := hglobal.rename_isHomogeneous (f := e.symm)
  simpa [terminalReindexedGlobalStirlingEquiv,
    terminalReindexedRenameEquiv] using hback

theorem terminalReindexedGlobalStirlingEquiv_symm_isHomogeneous
    (e : TerminalFiniteReindex (n := n) d Time)
    {P : MvPolynomial (Fin n) R} {degree : ℕ}
    (hP : P.IsHomogeneous degree) :
    ((terminalReindexedGlobalStirlingEquiv
      (R := R) d Time e).symm P).IsHomogeneous degree := by
  have hrename :
      (terminalReindexedRenameEquiv
        (R := R) d Time e P).IsHomogeneous degree := by
    change (MvPolynomial.rename e P).IsHomogeneous degree
    exact hP.rename_isHomogeneous
  have hglobal := terminalGlobalStirlingEquiv_symm_isHomogeneous
    (R := R) d Time hrename
  have hback := hglobal.rename_isHomogeneous (f := e.symm)
  simpa [terminalReindexedGlobalStirlingEquiv,
    terminalReindexedRenameEquiv] using hback

theorem terminalReindexedGlobalStirlingEquiv_preserves_ordinaryHomogeneous
    (e : TerminalFiniteReindex (n := n) d Time)
    {P : MvPolynomial (Fin n) R} {degree : ℕ}
    (hP : P.IsWeightedHomogeneous (fun _ : Fin n ↦ 1) degree) :
    (terminalReindexedGlobalStirlingEquiv
      (R := R) d Time e P).IsWeightedHomogeneous
        (fun _ : Fin n ↦ 1) degree := by
  change P.IsHomogeneous degree at hP
  change
    (terminalReindexedGlobalStirlingEquiv
      (R := R) d Time e P).IsHomogeneous degree
  exact terminalReindexedGlobalStirlingEquiv_isHomogeneous d Time e hP

theorem terminalReindexedGlobalStirlingEquiv_symm_preserves_ordinaryHomogeneous
    (e : TerminalFiniteReindex (n := n) d Time)
    {P : MvPolynomial (Fin n) R} {degree : ℕ}
    (hP : P.IsWeightedHomogeneous (fun _ : Fin n ↦ 1) degree) :
    ((terminalReindexedGlobalStirlingEquiv
      (R := R) d Time e).symm P).IsWeightedHomogeneous
        (fun _ : Fin n ↦ 1) degree := by
  change P.IsHomogeneous degree at hP
  change
    ((terminalReindexedGlobalStirlingEquiv
      (R := R) d Time e).symm P).IsHomogeneous degree
  exact terminalReindexedGlobalStirlingEquiv_symm_isHomogeneous d Time e hP

/-- Every output monomial has the ordinary degree of a source monomial. -/
theorem terminalReindexedGlobalStirlingEquiv_coeff_degree
    (e : TerminalFiniteReindex (n := n) d Time)
    {P : MvPolynomial (Fin n) R} {m : Fin n →₀ ℕ}
    (hm : (terminalReindexedGlobalStirlingEquiv
      (R := R) d Time e P).coeff m ≠ 0) :
    ∃ m₀ : Fin n →₀ ℕ, P.coeff m₀ ≠ 0 ∧
      m₀.degree = m.degree := by
  classical
  rw [← P.support_sum_monomial_coeff, map_sum,
    MvPolynomial.coeff_sum] at hm
  obtain ⟨m₀, hm₀mem, hm₀image⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨m₀, MvPolynomial.mem_support_iff.mp hm₀mem, ?_⟩
  have hmono :
      (MvPolynomial.monomial m₀ (P.coeff m₀)).IsHomogeneous m₀.degree :=
    MvPolynomial.isHomogeneous_monomial _ rfl
  have himage := terminalReindexedGlobalStirlingEquiv_isHomogeneous
    (R := R) d Time e hmono
  have hdegree : m.degree = m₀.degree := by
    calc
      m.degree = Finsupp.weight (fun _ : Fin n ↦ 1) m := by
        rw [Finsupp.degree_eq_weight_one]
      _ = m₀.degree := himage hm₀image
  exact hdegree.symm

theorem terminalReindexedGlobalStirlingEquiv_symm_coeff_degree
    (e : TerminalFiniteReindex (n := n) d Time)
    {P : MvPolynomial (Fin n) R} {m : Fin n →₀ ℕ}
    (hm : ((terminalReindexedGlobalStirlingEquiv
      (R := R) d Time e).symm P).coeff m ≠ 0) :
    ∃ m₀ : Fin n →₀ ℕ, P.coeff m₀ ≠ 0 ∧
      m₀.degree = m.degree := by
  classical
  rw [← P.support_sum_monomial_coeff, map_sum,
    MvPolynomial.coeff_sum] at hm
  obtain ⟨m₀, hm₀mem, hm₀image⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨m₀, MvPolynomial.mem_support_iff.mp hm₀mem, ?_⟩
  have hmono :
      (MvPolynomial.monomial m₀ (P.coeff m₀)).IsHomogeneous m₀.degree :=
    MvPolynomial.isHomogeneous_monomial _ rfl
  have himage := terminalReindexedGlobalStirlingEquiv_symm_isHomogeneous
    (R := R) d Time e hmono
  have hdegree : m.degree = m₀.degree := by
    calc
      m.degree = Finsupp.weight (fun _ : Fin n ↦ 1) m := by
        rw [Finsupp.degree_eq_weight_one]
      _ = m₀.degree := himage hm₀image
  exact hdegree.symm

@[simp]
theorem terminalReindexedGradedLexData_termOrdinaryDegree
    (e : TerminalFiniteReindex (n := n) d Time) (m : Fin n →₀ ℕ) :
    (terminalReindexedGradedLexData d Time e).termOrdinaryDegree
        ((0 : Fin 1), m) =
      (m.degree : ℤ) := by
  simp [PolynomialGradedLexData.termOrdinaryDegree,
    artinianPolynomialTermDegree, terminalReindexedGradedLexData,
    ← Finsupp.degree_eq_weight_one]

@[simp]
theorem terminalReindexedGlobalStirlingModuleEquiv_symm_apply
    (e : TerminalFiniteReindex (n := n) d Time)
    (P : artinianFreePolynomialModule R n 1) (k : Fin 1) :
    (terminalReindexedGlobalStirlingModuleEquiv
      (R := R) d Time e).symm P k =
      (terminalReindexedGlobalStirlingEquiv
        (R := R) d Time e).symm (P k) :=
  rfl

/-- The reindexed module automorphism preserves every bounded ordinary-degree
window. -/
theorem terminalReindexedGlobalStirlingModuleEquiv_map_window
    (e : TerminalFiniteReindex (n := n) d Time) (D : ℤ) :
    let G := terminalReindexedGradedLexData d Time e
    let hpositive := terminalReindexedGradedLexData_ordinaryDegree_pos d Time e
    (G.windowModule R hpositive D).map
        (terminalReindexedGlobalStirlingModuleEquiv
          (R := R) d Time e).toLinearMap =
      G.windowModule R hpositive D := by
  let G := terminalReindexedGradedLexData d Time e
  let hpositive : ∀ i : Fin n, 0 < G.ordinaryDegree i :=
    terminalReindexedGradedLexData_ordinaryDegree_pos d Time e
  let J := terminalReindexedGlobalStirlingModuleEquiv (R := R) d Time e
  have htermDegree (m : Fin n →₀ ℕ) :
      G.termOrdinaryDegree ((0 : Fin 1), m) = (m.degree : ℤ) := by
    exact terminalReindexedGradedLexData_termOrdinaryDegree d Time e m
  change (G.windowModule R hpositive D).map J.toLinearMap =
    G.windowModule R hpositive D
  apply le_antisymm
  · rintro _ ⟨P, hP, rfl⟩
    apply (mem_artinianPolynomialModuleSupported _ _).mpr
    intro k m hm
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    have hm' :
        (terminalReindexedGlobalStirlingEquiv
          (R := R) d Time e (P 0)).coeff m ≠ 0 := by
      change
        (terminalReindexedGlobalStirlingEquiv
          (R := R) d Time e (P 0)).coeff m ≠ 0 at hm
      exact hm
    obtain ⟨m₀, hm₀, hdegree⟩ :=
      terminalReindexedGlobalStirlingEquiv_coeff_degree
        (R := R) d Time e hm'
    have hterm₀ :=
      (mem_artinianPolynomialModuleSupported _ _).mp hP 0 m₀ hm₀
    change ((0 : Fin 1), m₀) ∈ G.windowTermFinset hpositive D at hterm₀
    change ((0 : Fin 1), m) ∈ G.windowTermFinset hpositive D
    apply (G.mem_windowTermFinset_iff_le hpositive D _).mpr
    rw [htermDegree m, ← hdegree]
    have hle₀ :=
      (G.mem_windowTermFinset_iff_le hpositive D _).mp hterm₀
    rwa [htermDegree m₀] at hle₀
  · intro P hP
    refine ⟨J.symm P, ?_, J.apply_symm_apply P⟩
    apply (mem_artinianPolynomialModuleSupported _ _).mpr
    intro k m hm
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    have hm' :
        ((terminalReindexedGlobalStirlingEquiv
          (R := R) d Time e).symm (P 0)).coeff m ≠ 0 := by
      simpa only [J,
        terminalReindexedGlobalStirlingModuleEquiv_symm_apply] using hm
    obtain ⟨m₀, hm₀, hdegree⟩ :=
      terminalReindexedGlobalStirlingEquiv_symm_coeff_degree
        (R := R) d Time e hm'
    have hterm₀ :=
      (mem_artinianPolynomialModuleSupported _ _).mp hP 0 m₀ hm₀
    change ((0 : Fin 1), m₀) ∈ G.windowTermFinset hpositive D at hterm₀
    change ((0 : Fin 1), m) ∈ G.windowTermFinset hpositive D
    apply (G.mem_windowTermFinset_iff_le hpositive D _).mpr
    rw [htermDegree m, ← hdegree]
    have hle₀ :=
      (G.mem_windowTermFinset_iff_le hpositive D _).mp hterm₀
    rwa [htermDegree m₀] at hle₀

/-- Restriction to the finite ordinary-degree window. -/
def terminalReindexedGlobalStirlingWindowEquiv
    (e : TerminalFiniteReindex (n := n) d Time) (D : ℤ) :
    let G := terminalReindexedGradedLexData d Time e
    let hpositive := terminalReindexedGradedLexData_ordinaryDegree_pos d Time e
    G.windowModule R hpositive D ≃ₗ[R] G.windowModule R hpositive D :=
  by
    dsimp
    exact
      (terminalReindexedGradedLexData d Time e).windowRestriction
        (terminalReindexedGradedLexData_ordinaryDegree_pos d Time e) D
        (terminalReindexedGlobalStirlingModuleEquiv (R := R) d Time e)
        (terminalReindexedGlobalStirlingModuleEquiv_map_window
          (R := R) d Time e D)

/-! ## Triangularity in the ordered weight window -/

theorem terminalReindexedGlobalStirlingModuleEquiv_isWindowWeightTriangular
    (e : TerminalFiniteReindex (n := n) d Time) (D : ℤ) :
    let G := terminalReindexedGradedLexData d Time e
    let hpositive := terminalReindexedGradedLexData_ordinaryDegree_pos d Time e
    G.IsWindowWeightTriangular hpositive D
      (terminalReindexedGlobalStirlingModuleEquiv (R := R) d Time e) := by
  let G := terminalReindexedGradedLexData d Time e
  let hpositive : ∀ i : Fin n, 0 < G.ordinaryDegree i :=
    terminalReindexedGradedLexData_ordinaryDegree_pos d Time e
  let J := terminalReindexedGlobalStirlingModuleEquiv (R := R) d Time e
  change G.IsWindowWeightTriangular hpositive D J
  intro weight P hP
  have hPwindow : P ∈ G.windowModule R hpositive D :=
    G.windowWeightPiece_le_windowModule hpositive D weight hP
  have hmap : (G.windowModule R hpositive D).map J.toLinearMap =
      G.windowModule R hpositive D := by
    exact terminalReindexedGlobalStirlingModuleEquiv_map_window
      (R := R) d Time e D
  have hJPwindow : J P ∈ G.windowModule R hpositive D := by
    rw [← hmap]
    exact ⟨P, hPwindow, rfl⟩
  have hdiffWindow : J P - P ∈ G.windowModule R hpositive D :=
    (G.windowModule R hpositive D).sub_mem hJPwindow hPwindow
  apply (mem_artinianPolynomialModuleSupported _ _).mpr
  intro k m hm
  have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
  subst k
  have htermWindow :=
    (mem_artinianPolynomialModuleSupported _ _).mp hdiffWindow 0 m hm
  have hPweight : ∀ m', (P 0).coeff m' ≠ 0 →
      G.termWeight ((0 : Fin 1), m') = weight := by
    intro m' hm'
    exact ((mem_artinianPolynomialModuleSupported _ _).mp
      hP 0 m' hm').2
  have hm' :
      (terminalReindexedGlobalStirlingEquiv
          (R := R) d Time e (P 0) - P 0).coeff m ≠ 0 := by
    simpa only [J, Pi.sub_apply,
      terminalReindexedGlobalStirlingModuleEquiv_apply] using hm
  exact ⟨htermWindow,
    terminalReindexedGlobalStirlingEquiv_sub_self_weight_lt
      (R := R) d Time e hPweight hm'⟩

/-- The finite product automorphism obtained from the terminal substitution. -/
def terminalReindexedGlobalStirlingOrderedWindowEquiv
    (e : TerminalFiniteReindex (n := n) d Time) (D : ℤ) :
    let G := terminalReindexedGradedLexData d Time e
    let hpositive := terminalReindexedGradedLexData_ordinaryDegree_pos d Time e
    ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece R hpositive D i) ≃ₗ[R]
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece R hpositive D i) :=
  by
    dsimp
    exact
      (terminalReindexedGradedLexData d Time e).windowOrderedWeightConjugate
        (terminalReindexedGradedLexData_ordinaryDegree_pos d Time e) D
        (terminalReindexedGlobalStirlingModuleEquiv (R := R) d Time e)
        (terminalReindexedGlobalStirlingModuleEquiv_map_window
          (R := R) d Time e D)

theorem terminalReindexedGlobalStirlingOrderedWindowEquiv_triangular
    (e : TerminalFiniteReindex (n := n) d Time) (D : ℤ) :
    let G := terminalReindexedGradedLexData d Time e
    let hpositive := terminalReindexedGradedLexData_ordinaryDegree_pos d Time e
    let A := terminalReindexedGlobalStirlingOrderedWindowEquiv
      (R := R) d Time e D
    ∀ i (v : G.orderedWeightPiece R hpositive D i),
      A (Pi.single
          (M := fun j : Fin (G.weightCount hpositive D) ↦
            G.orderedWeightPiece R hpositive D j) i v) =
        Pi.single
          (M := fun j : Fin (G.weightCount hpositive D) ↦
            G.orderedWeightPiece R hpositive D j) i v +
        finiteWeightPrefixProjection R
          (fun j : Fin (G.weightCount hpositive D) ↦
            G.orderedWeightPiece R hpositive D j) i.val
          (A (Pi.single
            (M := fun j : Fin (G.weightCount hpositive D) ↦
              G.orderedWeightPiece R hpositive D j) i v)) :=
  by
    dsimp
    exact
      (terminalReindexedGradedLexData d Time e).windowOrderedWeightConjugate_triangular
          (terminalReindexedGradedLexData_ordinaryDegree_pos d Time e) D
          (terminalReindexedGlobalStirlingModuleEquiv (R := R) d Time e)
          (terminalReindexedGlobalStirlingModuleEquiv_map_window
            (R := R) d Time e D)
          (terminalReindexedGlobalStirlingModuleEquiv_isWindowWeightTriangular
            (R := R) d Time e D)

/-!
## Implementation notes

1. The global analogues of `stirlingParameterHom_coeff_zero` are implemented
above:

```lean
@[simp] theorem terminalGlobalStirlingParameterVariable_coeff_zero (x) :
  (terminalGlobalStirlingParameterVariable R (Fin h) d Time x).coeff 0 =
    MvPolynomial.X x

@[simp] theorem terminalGlobalStirlingParameterHom_coeff_zero (P) :
  (terminalGlobalStirlingParameterHom R (Fin h) d Time P).coeff 0 = P
```

Prove it by composing the outer `MvPolynomial.constantCoeff` with the
parameter hom and applying `MvPolynomial.ringHom_ext`.  The variable case is
the diagonal `j = r` term and `signedStirling_self`; retained variables close
by simp.  This exactly parallels `stirlingParameterVariable_coeff_zero` and
`stirlingParameterHom_coeff_zero` in `StirlingParameterHom.lean`.
If the bridge is allowed to import `TerminalBlockParameterSpecialization`,
the block-variable case can instead be obtained immediately from
`terminalGlobalStirlingParameterVariable_coeff_axis_same ... k := 0`, since
`terminalBlockAxis Block b 0 = 0`; this avoids repeating the finite-sum proof.

2. Encode a terminal multidegree in the lexicographic group:

```lean
def terminalMultidegreeToLex
    (α : TerminalMultidegree (Fin h)) : PolynomialLexWeight h :=
  toLex (fun b ↦ (α b : ℤ))
```

Prove that this map is injective and commutes with `Finsupp.weight`.  Prove
the strict loss lemma

```lean
κ ≠ 0 → κ + output = input →
  terminalMultidegreeToLex output < terminalMultidegreeToLex input.
```

There is no need to choose the first nonzero coordinate.  The additive
equation gives the pointwise inequality between the integer-valued functions;
`κ ≠ 0` makes the functions unequal.  Thus they are strictly ordered in
the pointwise Pi order, and `Pi.toLex_strictMono` gives the lexicographic
inequality.  This also handles `h = 0`, since then `κ ≠ 0` is impossible.

The exact reindexing identity needed on every finite exponent is:

```lean
theorem terminalReindexedGradedLexData_termWeight
    (e : TerminalFiniteReindex (n := n) d Time) (m : Fin n →₀ ℕ) :
    (terminalReindexedGradedLexData d Time e).termWeight (0, m) =
      terminalMultidegreeToLex
        (Finsupp.weight (terminalGlobalWeight (Fin h) d Time)
          (m.mapDomain e))
```

Prove the underlying equality of `Fin h → ℤ` by `Finsupp.induction`;
`Finsupp.weight_single`, `Finsupp.mapDomain_single`, and `map_add` close its
two inductive cases.  This lemma is also the clean bridge between membership
in `windowWeightPiece` and genuine terminal-global homogeneity after
`renameEquiv R e`.

3. If a nonzero polynomial is homogeneous for the encoded lex weight, choose
one supported monomial.  Injectivity of `terminalMultidegreeToLex` shows that
it is homogeneous for the original `terminalGlobalWeight`.  Now use
`terminalGlobalStirlingParameter_coeff_degree`, evaluation at one, and helper
(1): after subtracting `P`, every surviving parameter exponent is nonzero,
so helper (2) puts every coefficient of `J P - P` at a strictly lower weight.

4. Transport this scalar support theorem through
`terminalReindexedRenameEquiv`.  A useful generic lemma is

```lean
theorem weightedHomogeneous_renameEquiv
    (e : σ ≃ τ) (weight : τ → M) ... :
  p.IsWeightedHomogeneous (weight ∘ e) degree →
  (MvPolynomial.renameEquiv R e p).IsWeightedHomogeneous weight degree
```

and follows immediately from the existing `weightedHomogeneous_aeval`.
For coefficients use `MvPolynomial.coeff_rename_mapDomain`; for weights add
the elementary identity that `Finsupp.weight` commutes with `mapDomain` along
an equivalence.

The central scalar theorem worth exposing before transport is:

```lean
theorem terminalGlobalStirlingEquiv_sub_self_weight_lt
    {P : CentralPolynomial R (Fin h) d Time}
    {inputDegree : TerminalMultidegree (Fin h)}
    (hP : P.IsWeightedHomogeneous
      (terminalGlobalWeight (Fin h) d Time) inputDegree) :
    ∀ m,
      (terminalGlobalStirlingEquiv R (Fin h) d Time P - P).coeff m ≠ 0 →
        terminalMultidegreeToLex
            (Finsupp.weight
              (terminalGlobalWeight (Fin h) d Time) m) <
          terminalMultidegreeToLex inputDegree
```

The reindexed scalar support theorem above follows by applying this to
`renameEquiv R e P` and transporting the output exponent through `e.symm`.

To prove `IsWindowWeightTriangular`, unfold only that predicate and
`windowStrictLowerPiece`.  Given `hP : P ∈ G.windowWeightPiece ... weight`,
`mem_artinianPolynomialModuleSupported.mp hP` supplies the displayed scalar
support hypothesis for `P 0`.  The strict inequality comes from
`terminalReindexedGlobalStirlingEquiv_sub_self_weight_lt`.  The window half
comes from `windowWeightPiece_le_windowModule`, the forward inclusion encoded
by `terminalReindexedGlobalStirlingModuleEquiv_map_window`, and closure of the
window submodule under subtraction.  Thus no statement about individual
ordinary-degree/weight intersections is needed here.

5. Ordinary-degree preservation is easier: the image under both the forward
and inverse substitutions of every variable is an `R`-linear combination of
variables.  Use mathlib's `MvPolynomial.IsHomogeneous.aeval` (or the project
lemma `weightedHomogeneous_aeval` with constant weight one).  Renaming is
already covered by `MvPolynomial.IsHomogeneous.rename_isHomogeneous`; total
degree itself is unchanged by reindexing via `MvPolynomial.totalDegree_renameEquiv`.
Decompose a bounded polynomial with
`sum_weightedHomogeneousComponent_support`; each image remains in the same
degree.  Alternatively prove the displayed coefficient-degree witness and
use `mem_artinianPolynomialModuleSupported`.  Applying the argument to the
equivalence and its inverse proves the displayed map equality for
`windowModule`; using both directions is essential to obtain equality rather
than only `map ≤`.

A small generic lemma makes both directions immediate:

```lean
theorem centralBlockAffineHom_zero_isHomogeneous
    (A : ∀ b : Block, Matrix (Fin (d b)) (Fin (d b)) R)
    {P : CentralPolynomial R Block d Time} {degree : ℕ}
    (hP : P.IsHomogeneous degree) :
    (centralBlockAffineHom R Block d Time A (fun _ ↦ 0) P).
      IsHomogeneous degree
```

For a block generator, use `centralBlockAffineHom_X_block` and
`MvPolynomial.IsHomogeneous.sum`; every summand is `C a * X`.  For a time
generator, `centralBlockAffineHom_X_time` simplifies to `X`.  Instantiate
`A` first with `centralSignedStirlingMatrix`, then with its matrix inverse.
No triangularity theorem for the inverse matrix is needed.
-/

end AbelFormalization
