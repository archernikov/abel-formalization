import AbelFormalization.MvPolynomialDerivativeIdealExtension
import AbelFormalization.TerminalInvariantDerivations
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Terminal Laurent localization and partial-derivative extraction

This file gives the one-block form of the localization step in the terminal
ideal lemma.  The other finite blocks may be included among `Keep`, so this
statement is designed to be iterated block by block.

For a block with variables indexed by `Fin (d + 1)`, its index-zero variable
is sent to the Laurent unit `T`, while the remaining variables are retained
as the polynomial variables `Fin d`.  The transported terminal vector fields
form an upper-triangular family whose diagonal entry is multiplication by
`T`.  Descending triangular elimination therefore recovers every partial
derivative in the retained variables.  The finite-variable derivative
extension theorem then removes all of those variables from the mapped ideal.
-/

noncomputable section

namespace AbelFormalization

/-! ## The explicit one-block Laurent presentation -/

/-- Coefficients after moving the retained variables into the coefficient
ring and adjoining the inverse of the first variable in the block. -/
abbrev TerminalLaurentCoefficientRing (R Keep : Type*) [CommRing R] :=
  LaurentPolynomial (MvPolynomial Keep R)

/-- The localized presentation in which the `d` higher variables in the
block remain polynomial variables. -/
abbrev TerminalLaurentPolynomialRing
    (R Keep : Type*) [CommRing R] (d : ℕ) :=
  MvPolynomial (Fin d) (TerminalLaurentCoefficientRing R Keep)

/-- The original one-block presentation.  Block index zero represents the
first derivative variable and `k.succ` represents the higher variable kept
as target variable `k`. -/
abbrev TerminalLaurentSourceRing
    (R Keep : Type*) [CommRing R] (d : ℕ) :=
  MvPolynomial (Keep ⊕ Fin (d + 1)) R

section Presentation

variable (R Keep : Type*) [CommRing R] (d : ℕ)

/-- The coefficient map from the original base ring into the Laurent
coefficient ring. -/
def terminalLaurentCoefficientMap :
    R →+* TerminalLaurentCoefficientRing R Keep :=
  (LaurentPolynomial.C :
      MvPolynomial Keep R →+* TerminalLaurentCoefficientRing R Keep).comp
    (MvPolynomial.C : R →+* MvPolynomial Keep R)

/-- The original coefficient map all the way into the localized polynomial
presentation. -/
def terminalLaurentBaseMap :
    R →+* TerminalLaurentPolynomialRing R Keep d :=
  (MvPolynomial.C :
      TerminalLaurentCoefficientRing R Keep →+*
        TerminalLaurentPolynomialRing R Keep d).comp
    (terminalLaurentCoefficientMap R Keep)

/-- The first block variable, represented by the Laurent monomial `T`. -/
def terminalLaurentFirstVariable :
    TerminalLaurentPolynomialRing R Keep d :=
  MvPolynomial.C (LaurentPolynomial.T 1)

/-- An explicit inverse for the first block variable. -/
def terminalLaurentFirstVariableInv :
    TerminalLaurentPolynomialRing R Keep d :=
  MvPolynomial.C (LaurentPolynomial.T (-1))

/-- Image of a block variable.  Index zero is Laurent and every successor
index stays polynomial. -/
def terminalLaurentBlockVariable :
    Fin (d + 1) → TerminalLaurentPolynomialRing R Keep d :=
  Fin.cases (terminalLaurentFirstVariable R Keep d)
    (fun k ↦ MvPolynomial.X k)

@[simp]
theorem terminalLaurentBlockVariable_zero :
    terminalLaurentBlockVariable R Keep d 0 =
      terminalLaurentFirstVariable R Keep d :=
  rfl

@[simp]
theorem terminalLaurentBlockVariable_succ (k : Fin d) :
    terminalLaurentBlockVariable R Keep d k.succ = MvPolynomial.X k :=
  rfl

/-- Images of all variables in the source presentation. -/
def terminalLaurentVariableImage :
    Keep ⊕ Fin (d + 1) → TerminalLaurentPolynomialRing R Keep d
  | Sum.inl k =>
      MvPolynomial.C (LaurentPolynomial.C (MvPolynomial.X k))
  | Sum.inr r => terminalLaurentBlockVariable R Keep d r

/-- The ring homomorphism from the original block presentation to the
presentation in which the first block variable is Laurent. -/
def terminalLaurentLocalizationHom :
    TerminalLaurentSourceRing R Keep d →+*
      TerminalLaurentPolynomialRing R Keep d :=
  MvPolynomial.eval₂Hom (terminalLaurentBaseMap R Keep d)
    (terminalLaurentVariableImage R Keep d)

@[simp]
theorem terminalLaurentLocalizationHom_C (a : R) :
    terminalLaurentLocalizationHom R Keep d (MvPolynomial.C a) =
      MvPolynomial.C (LaurentPolynomial.C (MvPolynomial.C a)) := by
  simp [terminalLaurentLocalizationHom, terminalLaurentBaseMap,
    terminalLaurentCoefficientMap]

@[simp]
theorem terminalLaurentLocalizationHom_X_keep (k : Keep) :
    terminalLaurentLocalizationHom R Keep d
        (MvPolynomial.X (Sum.inl k)) =
      MvPolynomial.C (LaurentPolynomial.C (MvPolynomial.X k)) := by
  simp [terminalLaurentLocalizationHom, terminalLaurentVariableImage]

@[simp]
theorem terminalLaurentLocalizationHom_X_block (r : Fin (d + 1)) :
    terminalLaurentLocalizationHom R Keep d
        (MvPolynomial.X (Sum.inr r)) =
      terminalLaurentBlockVariable R Keep d r := by
  simp [terminalLaurentLocalizationHom, terminalLaurentVariableImage]

@[simp]
theorem terminalLaurentLocalizationHom_X_first :
    terminalLaurentLocalizationHom R Keep d
        (MvPolynomial.X (Sum.inr (0 : Fin (d + 1)))) =
      terminalLaurentFirstVariable R Keep d := by
  simp

@[simp]
theorem terminalLaurentLocalizationHom_X_succ (k : Fin d) :
    terminalLaurentLocalizationHom R Keep d
        (MvPolynomial.X (Sum.inr k.succ)) =
      MvPolynomial.X k := by
  simp

/-- The localized first variable is a unit. -/
theorem terminalLaurentFirstVariable_isUnit :
    IsUnit (terminalLaurentFirstVariable R Keep d) := by
  simpa only [terminalLaurentFirstVariable] using
    (LaurentPolynomial.isUnit_T
      (R := MvPolynomial Keep R) 1).map
        (MvPolynomial.C :
          TerminalLaurentCoefficientRing R Keep →+*
            TerminalLaurentPolynomialRing R Keep d)

@[simp]
theorem terminalLaurentFirstVariableInv_mul :
    terminalLaurentFirstVariableInv R Keep d *
        terminalLaurentFirstVariable R Keep d = 1 := by
  rw [terminalLaurentFirstVariableInv, terminalLaurentFirstVariable,
    ← MvPolynomial.C_mul, ← LaurentPolynomial.T_add]
  norm_num

@[simp]
theorem terminalLaurentFirstVariable_mul_inv :
    terminalLaurentFirstVariable R Keep d *
        terminalLaurentFirstVariableInv R Keep d = 1 := by
  rw [terminalLaurentFirstVariableInv, terminalLaurentFirstVariable,
    ← MvPolynomial.C_mul, ← LaurentPolynomial.T_add]
  norm_num

end Presentation

/-! ## Transported triangular vector fields -/

section TriangularFields

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ)

/-- For `j < k`, this is the target variable corresponding to the source
block index `(k+1)-(j+1)`. -/
def terminalLaurentHigherIndex (j k : Fin d) (hjk : j < k) : Fin d :=
  ⟨k.val - j.val - 1, by omega⟩

/-- The off-diagonal coefficient in the localized triangular field. -/
def terminalLaurentOffDiagonalCoefficient (j k : Fin d) :
    TerminalLaurentPolynomialRing R Keep d :=
  if hjk : j < k then
    ((k.val + 2).choose (j.val + 2) :
        TerminalLaurentPolynomialRing R Keep d) *
      MvPolynomial.X (terminalLaurentHigherIndex d j k hjk)
  else 0

theorem terminalLaurentOffDiagonalCoefficient_of_lt
    (j k : Fin d) (hjk : j < k) :
    terminalLaurentOffDiagonalCoefficient R Keep d j k =
      ((k.val + 2).choose (j.val + 2) :
          TerminalLaurentPolynomialRing R Keep d) *
        MvPolynomial.X (terminalLaurentHigherIndex d j k hjk) := by
  simp [terminalLaurentOffDiagonalCoefficient, hjk]

@[simp]
theorem terminalLaurentOffDiagonalCoefficient_of_not_lt
    (j k : Fin d) (hjk : ¬ j < k) :
    terminalLaurentOffDiagonalCoefficient R Keep d j k = 0 := by
  simp [terminalLaurentOffDiagonalCoefficient, hjk]

/-- The higher-variable partial derivative, viewed over `ℚ`. -/
def terminalLaurentHigherPDeriv (j : Fin d) :
    Derivation ℚ (TerminalLaurentPolynomialRing R Keep d)
      (TerminalLaurentPolynomialRing R Keep d) :=
  (MvPolynomial.pderiv j :
      Derivation (TerminalLaurentCoefficientRing R Keep)
        (TerminalLaurentPolynomialRing R Keep d)
        (TerminalLaurentPolynomialRing R Keep d)).restrictScalars ℚ

@[simp]
theorem terminalLaurentHigherPDeriv_C
    (j : Fin d) (a : TerminalLaurentCoefficientRing R Keep) :
    terminalLaurentHigherPDeriv R Keep d j (MvPolynomial.C a) = 0 := by
  simp [terminalLaurentHigherPDeriv]

@[simp]
theorem terminalLaurentHigherPDeriv_X_self (j : Fin d) :
    terminalLaurentHigherPDeriv R Keep d j (MvPolynomial.X j) = 1 := by
  simp [terminalLaurentHigherPDeriv]

theorem terminalLaurentHigherPDeriv_X_of_ne
    (j k : Fin d) (hkj : k ≠ j) :
    terminalLaurentHigherPDeriv R Keep d j (MvPolynomial.X k) = 0 := by
  simp [terminalLaurentHigherPDeriv, hkj]

/-- The localized field attached to `V_(j+1)`.  Defining it by its values on
the retained variables makes the transport identity formal; the explicit
triangular formula is proved below. -/
def terminalLaurentTriangularField (j : Fin d) :
    Derivation ℚ (TerminalLaurentPolynomialRing R Keep d)
      (TerminalLaurentPolynomialRing R Keep d) :=
  (MvPolynomial.mkDerivation (TerminalLaurentCoefficientRing R Keep)
    (fun k ↦
      terminalLaurentLocalizationHom R Keep d
        (terminalBlockVectorField R Keep (d + 1) (j.val + 1)
          (MvPolynomial.X (Sum.inr k.succ))))).restrictScalars ℚ

@[simp]
theorem terminalLaurentTriangularField_C
    (j : Fin d) (a : TerminalLaurentCoefficientRing R Keep) :
    terminalLaurentTriangularField R Keep d j (MvPolynomial.C a) = 0 := by
  simp [terminalLaurentTriangularField]

@[simp]
theorem terminalLaurentTriangularField_X (j k : Fin d) :
    terminalLaurentTriangularField R Keep d j (MvPolynomial.X k) =
      terminalLaurentLocalizationHom R Keep d
        (terminalBlockVectorField R Keep (d + 1) (j.val + 1)
          (MvPolynomial.X (Sum.inr k.succ))) := by
  simp [terminalLaurentTriangularField]

/-- The localization hom intertwines `V_(j+1)` with its localized
triangular field on every source generator. -/
theorem terminalLaurentLocalizationHom_vectorField_X
    (j : Fin d) (z : Keep ⊕ Fin (d + 1)) :
    terminalLaurentLocalizationHom R Keep d
        (terminalBlockVectorField R Keep (d + 1) (j.val + 1)
          (MvPolynomial.X z)) =
      terminalLaurentTriangularField R Keep d j
        (terminalLaurentLocalizationHom R Keep d (MvPolynomial.X z)) := by
  rcases z with k | r
  · simp
  · refine Fin.cases ?_ (fun k ↦ ?_) r
    · have hjpos : 1 ≤ j.val + 1 :=
        Nat.succ_le_succ (Nat.zero_le j.val)
      have hfield := terminalBlockVectorField_X_first
        R Keep (d + 1) (j.val + 1) hjpos
          (0 : Fin (d + 1)) rfl
      calc
        terminalLaurentLocalizationHom R Keep d
            (terminalBlockVectorField R Keep (d + 1) (j.val + 1)
              (MvPolynomial.X
                (Sum.inr (0 : Fin (d + 1))))) =
          terminalLaurentLocalizationHom R Keep d 0 :=
            congrArg (terminalLaurentLocalizationHom R Keep d) hfield
        _ = 0 := map_zero _
        _ = terminalLaurentTriangularField R Keep d j
              (MvPolynomial.C (LaurentPolynomial.T 1)) :=
            (terminalLaurentTriangularField_C R Keep d j
              (LaurentPolynomial.T 1)).symm
        _ = terminalLaurentTriangularField R Keep d j
              (terminalLaurentLocalizationHom R Keep d
                (MvPolynomial.X
                  (Sum.inr (0 : Fin (d + 1))))) := by
            rw [terminalLaurentLocalizationHom_X_first,
              terminalLaurentFirstVariable]
    · simp

/-- The complete intertwining identity, not merely its values on
generators. -/
theorem terminalLaurentLocalizationHom_vectorField
    (j : Fin d) (P : TerminalLaurentSourceRing R Keep d) :
    terminalLaurentLocalizationHom R Keep d
        (terminalBlockVectorField R Keep (d + 1) (j.val + 1) P) =
      terminalLaurentTriangularField R Keep d j
        (terminalLaurentLocalizationHom R Keep d P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P z hP =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
        hP, terminalLaurentLocalizationHom_vectorField_X]

/-- Entries below the diagonal vanish. -/
theorem terminalLaurentTriangularField_X_of_lt
    (j k : Fin d) (hkj : k < j) :
    terminalLaurentTriangularField R Keep d j (MvPolynomial.X k) = 0 := by
  have hnot : ¬ j.val + 1 ≤ k.succ.val := by
    simpa using not_le_of_gt (Nat.succ_lt_succ hkj)
  rw [terminalLaurentTriangularField_X,
    terminalBlockVectorField_X_block, ite_eq_right hnot]
  simp

/-- The diagonal entry is the Laurent unit representing the first block
variable. -/
theorem terminalLaurentTriangularField_X_self (j : Fin d) :
    terminalLaurentTriangularField R Keep d j (MvPolynomial.X j) =
      terminalLaurentFirstVariable R Keep d := by
  rw [terminalLaurentTriangularField_X,
    terminalBlockVectorField_X_block, ite_eq_left (by simp), map_mul,
    map_natCast, terminalLaurentLocalizationHom_X_block]
  have hz :
      (⟨j.succ.val - (j.val + 1),
          (Nat.sub_le j.succ.val (j.val + 1)).trans_lt j.succ.isLt⟩ :
        Fin (d + 1)) = 0 := by
    apply Fin.ext
    simp
  rw [hz, terminalLaurentBlockVariable_zero]
  simp

/-- Every strict upper-triangular entry is the expected binomial multiple
of an earlier higher variable. -/
theorem terminalLaurentTriangularField_X_of_gt
    (j k : Fin d) (hjk : j < k) :
    terminalLaurentTriangularField R Keep d j (MvPolynomial.X k) =
      ((k.val + 2).choose (j.val + 2) :
          TerminalLaurentPolynomialRing R Keep d) *
        MvPolynomial.X (terminalLaurentHigherIndex d j k hjk) := by
  have hle : j.val + 1 ≤ k.succ.val := by
    simpa using Nat.succ_le_succ (Nat.le_of_lt hjk)
  rw [terminalLaurentTriangularField_X,
    terminalBlockVectorField_X_block, ite_eq_left hle, map_mul,
    map_natCast, terminalLaurentLocalizationHom_X_block]
  have hr :
      (⟨k.succ.val - (j.val + 1),
          (Nat.sub_le k.succ.val (j.val + 1)).trans_lt k.succ.isLt⟩ :
        Fin (d + 1)) =
          (terminalLaurentHigherIndex d j k hjk).succ := by
    apply Fin.ext
    simp [terminalLaurentHigherIndex]
    omega
  rw [hr, terminalLaurentBlockVariable_succ]
  simp

end TriangularFields

/-! ## Ideal preservation under maps and finite triangular elimination -/

section PreservationInfrastructure

variable {A : Type*} [CommRing A] [Algebra ℚ A]

theorem derivationPreservesIdeal.zero (I : Ideal A) :
    derivationPreservesIdeal I (0 : Derivation ℚ A A) := by
  intro x hx
  simpa only [Derivation.zero_apply] using I.zero_mem

theorem derivationPreservesIdeal.add
    {I : Ideal A} {D E : Derivation ℚ A A}
    (hD : derivationPreservesIdeal I D)
    (hE : derivationPreservesIdeal I E) :
    derivationPreservesIdeal I (D + E) := by
  intro x hx
  rw [Derivation.add_apply]
  exact I.add_mem (hD x hx) (hE x hx)

/-- Ideal preservation is closed under scaling a derivation by an arbitrary
element of the ambient ring. -/
theorem derivationPreservesIdeal.smulRing
    {I : Ideal A} {D : Derivation ℚ A A}
    (hD : derivationPreservesIdeal I D) (c : A) :
    derivationPreservesIdeal I (c • D) := by
  intro x hx
  rw [Derivation.smul_apply, smul_eq_mul]
  exact I.mul_mem_left c (hD x hx)

theorem derivationPreservesIdeal.finsetSum
    {ι : Type*} {I : Ideal A} (s : Finset ι)
    (D : ι → Derivation ℚ A A)
    (hD : ∀ i ∈ s, derivationPreservesIdeal I (D i)) :
    derivationPreservesIdeal I (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using derivationPreservesIdeal.zero I
  | @insert q s hqs ih =>
      rw [Finset.sum_insert hqs]
      exact (hD q (Finset.mem_insert_self q s)).add
        (ih (fun r hr ↦ hD r (Finset.mem_insert_of_mem hr)))

/-- Evaluation commutes with a finite sum of derivations. -/
theorem terminalDerivationFinsetSum_apply
    {ι : Type*} (s : Finset ι) (D : ι → Derivation ℚ A A) (x : A) :
    (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Derivation.zero_apply]
  | @insert q s hqs ih =>
      simp only [Finset.sum_insert hqs, Derivation.add_apply, ih]

/-- A derivation which intertwines a ring homomorphism with a source
derivation preserves the mapped ideal whenever the source derivation
preserves the original ideal. -/
theorem derivationPreservesIdeal_map_of_intertwining
    {B : Type*} [CommRing B] [Algebra ℚ B]
    (f : A →+* B) (I : Ideal A)
    (D : Derivation ℚ A A) (E : Derivation ℚ B B)
    (hintertwine : ∀ x, f (D x) = E (f x))
    (hD : derivationPreservesIdeal I D) :
    derivationPreservesIdeal (I.map f) E := by
  intro x hx
  change x ∈ Ideal.span (f '' I) at hx
  refine Submodule.span_induction
    (p := fun y _ ↦ E y ∈ I.map f) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, ha, rfl⟩
    rw [← hintertwine a]
    exact Ideal.mem_map_of_mem f (hD a ha)
  · simpa only [map_zero] using (I.map f).zero_mem
  · intro y z hy hz hEy hEz
    rw [map_add]
    exact (I.map f).add_mem hEy hEz
  · intro b y hy hEy
    rw [smul_eq_mul, E.leibniz, smul_eq_mul, smul_eq_mul]
    exact (I.map f).add_mem
      ((I.map f).mul_mem_left b hEy)
      (by
        simpa only [mul_comm] using
          (I.map f).mul_mem_left (E b) hy)

/-- Descending elimination for a finite upper-triangular family of
derivations with a common unit on the diagonal. -/
theorem derivationPreservesIdeal_of_unit_upperTriangular
    {d : ℕ} (I : Ideal A) (u : A) (hu : IsUnit u)
    (D W : Fin d → Derivation ℚ A A) (a : Fin d → Fin d → A)
    (hW : ∀ j, derivationPreservesIdeal I (W j))
    (htriangular : ∀ j,
      W j = u • D j + ∑ k ∈ Finset.Ioi j, a j k • D k) :
    ∀ j, derivationPreservesIdeal I (D j) := by
  classical
  have hextract : ∀ j : Fin d,
      (∀ k : Fin d, j < k → derivationPreservesIdeal I (D k)) →
        derivationPreservesIdeal I (D j) := by
    intro j hhigher
    have hsum : derivationPreservesIdeal I
        (∑ k ∈ Finset.Ioi j, a j k • D k) := by
      apply derivationPreservesIdeal.finsetSum
      intro k hk
      exact derivationPreservesIdeal.smulRing
        (hhigher k (Finset.mem_Ioi.mp hk)) (a j k)
    have hdiff : derivationPreservesIdeal I
        (W j + -(∑ k ∈ Finset.Ioi j, a j k • D k)) :=
      (hW j).add hsum.neg
    have heq :
        W j + -(∑ k ∈ Finset.Ioi j, a j k • D k) = u • D j := by
      rw [htriangular j]
      abel
    rw [heq] at hdiff
    intro x hx
    apply (Ideal.unit_mul_mem_iff_mem I hu).mp
    simpa only [Derivation.smul_apply, smul_eq_mul] using hdiff x hx
  cases d with
  | zero =>
      intro j
      exact Fin.elim0 j
  | succ n =>
      have htail : ∀ j : Fin (n + 1),
          ∀ k : Fin (n + 1), j ≤ k →
            derivationPreservesIdeal I (D k) := by
        intro j
        induction j using Fin.reverseInduction with
        | last =>
            intro k hjk
            have hk : k = Fin.last n :=
              le_antisymm (Fin.le_last k) hjk
            subst k
            apply hextract
            intro l hlt
            exact (not_lt_of_ge (Fin.le_last l) hlt).elim
        | cast j ih =>
            intro k hjk
            by_cases hk : k = Fin.castSucc j
            · subst k
              apply hextract
              intro l hlt
              apply ih l
              change j.val + 1 ≤ l.val
              exact Nat.succ_le_of_lt hlt
            · apply ih k
              have hlt : Fin.castSucc j < k :=
                lt_of_le_of_ne hjk (Ne.symm hk)
              change j.val + 1 ≤ k.val
              exact Nat.succ_le_of_lt hlt
      intro j
      exact htail j j le_rfl

end PreservationInfrastructure

/-! ## Triangular identity and derivative-stable mapped ideal -/

section Extraction

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R] (d : ℕ)

/-- The localized field is the Laurent-unit multiple of its diagonal
partial derivative plus partial derivatives with strictly larger indices. -/
theorem terminalLaurentTriangularField_eq
    (j : Fin d) :
    terminalLaurentTriangularField R Keep d j =
      terminalLaurentFirstVariable R Keep d •
          terminalLaurentHigherPDeriv R Keep d j +
        ∑ k ∈ Finset.Ioi j,
          terminalLaurentOffDiagonalCoefficient R Keep d j k •
            terminalLaurentHigherPDeriv R Keep d k := by
  classical
  apply mvPolynomial_derivation_ext_C_X
  · intro c
    rw [Derivation.add_apply, terminalDerivationFinsetSum_apply]
    simp only [terminalLaurentTriangularField_C,
      Derivation.smul_apply, smul_eq_mul,
      terminalLaurentHigherPDeriv_C, mul_zero,
      Finset.sum_const_zero, add_zero]
  · intro k
    rw [Derivation.add_apply, terminalDerivationFinsetSum_apply]
    simp only [Derivation.smul_apply, smul_eq_mul]
    by_cases hjk : j = k
    · subst k
      rw [terminalLaurentTriangularField_X_self,
        terminalLaurentHigherPDeriv_X_self]
      have hsum :
          ∑ l ∈ Finset.Ioi j,
              terminalLaurentOffDiagonalCoefficient R Keep d j l *
                terminalLaurentHigherPDeriv R Keep d l
                  (MvPolynomial.X j) = 0 := by
        apply Finset.sum_eq_zero
        intro l hl
        have hjl : j ≠ l := ne_of_lt (Finset.mem_Ioi.mp hl)
        rw [terminalLaurentHigherPDeriv_X_of_ne R Keep d l j hjl,
          mul_zero]
      rw [hsum, mul_one, add_zero]
    · by_cases hkj : k < j
      · rw [terminalLaurentTriangularField_X_of_lt R Keep d j k hkj,
          terminalLaurentHigherPDeriv_X_of_ne R Keep d j k
            (ne_of_lt hkj)]
        have hsum :
            ∑ l ∈ Finset.Ioi j,
                terminalLaurentOffDiagonalCoefficient R Keep d j l *
                  terminalLaurentHigherPDeriv R Keep d l
                    (MvPolynomial.X k) = 0 := by
          apply Finset.sum_eq_zero
          intro l hl
          have hkl : k ≠ l := by
            have hjl := Finset.mem_Ioi.mp hl
            omega
          rw [terminalLaurentHigherPDeriv_X_of_ne R Keep d l k hkl,
            mul_zero]
        rw [hsum, mul_zero, zero_add]
      · have hjk' : j < k := lt_of_le_of_ne (not_lt.mp hkj) hjk
        have hk : k ∈ Finset.Ioi j := Finset.mem_Ioi.mpr hjk'
        have hsum :
            ∑ l ∈ Finset.Ioi j,
                terminalLaurentOffDiagonalCoefficient R Keep d j l *
                  terminalLaurentHigherPDeriv R Keep d l
                    (MvPolynomial.X k) =
              terminalLaurentOffDiagonalCoefficient R Keep d j k := by
          calc
            ∑ l ∈ Finset.Ioi j,
                terminalLaurentOffDiagonalCoefficient R Keep d j l *
                  terminalLaurentHigherPDeriv R Keep d l
                    (MvPolynomial.X k) =
                terminalLaurentOffDiagonalCoefficient R Keep d j k *
                  terminalLaurentHigherPDeriv R Keep d k
                    (MvPolynomial.X k) := by
              apply Finset.sum_eq_single k
              · intro l hl hlk
                rw [terminalLaurentHigherPDeriv_X_of_ne R Keep d l k
                  hlk.symm, mul_zero]
              · intro hknot
                exact (hknot hk).elim
            _ = terminalLaurentOffDiagonalCoefficient R Keep d j k := by
              rw [terminalLaurentHigherPDeriv_X_self, mul_one]
        rw [terminalLaurentTriangularField_X_of_gt R Keep d j k hjk',
          terminalLaurentHigherPDeriv_X_of_ne R Keep d j k
            (ne_of_gt hjk'), hsum,
          terminalLaurentOffDiagonalCoefficient_of_lt R Keep d j k hjk',
          mul_zero, zero_add]

/-- Every transported triangular field preserves the mapped ideal. -/
theorem terminalLaurentTriangularField_preserves_mappedIdeal
    (I : Ideal (TerminalLaurentSourceRing R Keep d))
    (hV : ∀ q, 1 ≤ q →
      derivationPreservesIdeal I
        (terminalBlockVectorField R Keep (d + 1) q))
    (j : Fin d) :
    derivationPreservesIdeal
      (I.map (terminalLaurentLocalizationHom R Keep d))
      (terminalLaurentTriangularField R Keep d j) := by
  apply derivationPreservesIdeal_map_of_intertwining
    (A := TerminalLaurentSourceRing R Keep d)
    (B := TerminalLaurentPolynomialRing R Keep d)
    (terminalLaurentLocalizationHom R Keep d) I
    (terminalBlockVectorField R Keep (d + 1) (j.val + 1))
    (terminalLaurentTriangularField R Keep d j)
  · exact terminalLaurentLocalizationHom_vectorField R Keep d j
  · exact hV (j.val + 1) (by omega)

/-- After the first block variable is made Laurent, the mapped ideal is
stable under every partial derivative in the higher block variables. -/
theorem terminalLaurentMappedIdeal_pderiv_stable
    (I : Ideal (TerminalLaurentSourceRing R Keep d))
    (hV : ∀ q, 1 ≤ q →
      derivationPreservesIdeal I
        (terminalBlockVectorField R Keep (d + 1) q)) :
    ∀ j P,
      P ∈ I.map (terminalLaurentLocalizationHom R Keep d) →
        MvPolynomial.pderiv j P ∈
          I.map (terminalLaurentLocalizationHom R Keep d) := by
  have hpartial : ∀ j : Fin d,
      derivationPreservesIdeal
        (I.map (terminalLaurentLocalizationHom R Keep d))
        (terminalLaurentHigherPDeriv R Keep d j) := by
    apply derivationPreservesIdeal_of_unit_upperTriangular
      (I.map (terminalLaurentLocalizationHom R Keep d))
      (terminalLaurentFirstVariable R Keep d)
      (terminalLaurentFirstVariable_isUnit R Keep d)
      (terminalLaurentHigherPDeriv R Keep d)
      (terminalLaurentTriangularField R Keep d)
      (terminalLaurentOffDiagonalCoefficient R Keep d)
    · exact terminalLaurentTriangularField_preserves_mappedIdeal
        R Keep d I hV
    · exact terminalLaurentTriangularField_eq R Keep d
  intro j P hP
  simpa only [terminalLaurentHigherPDeriv,
    Derivation.restrictScalars_apply] using hpartial j P hP

/-- Elimination of all higher variables: the localized image ideal is
extended from the Laurent coefficient ring. -/
theorem terminalLaurentMappedIdeal_eq_map_comap
    (I : Ideal (TerminalLaurentSourceRing R Keep d))
    (hV : ∀ q, 1 ≤ q →
      derivationPreservesIdeal I
        (terminalBlockVectorField R Keep (d + 1) q)) :
    I.map (terminalLaurentLocalizationHom R Keep d) =
      ((I.map (terminalLaurentLocalizationHom R Keep d)).comap
          MvPolynomial.C).map MvPolynomial.C := by
  exact mvPolynomial_pderiv_stable_ideal_eq_map_comap d
    (I.map (terminalLaurentLocalizationHom R Keep d))
    (terminalLaurentMappedIdeal_pderiv_stable R Keep d I hV)

end Extraction

end AbelFormalization
