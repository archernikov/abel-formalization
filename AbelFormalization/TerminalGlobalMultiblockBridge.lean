import AbelFormalization.TerminalBlockParameterSpecialization
import AbelFormalization.TerminalMultiblockElimination

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Global terminal fields in the simultaneous multiblock presentation

The one-block fields obtained from the global Stirling deformation are
transported back through the split-index equivalence.  This file then proves
that they intertwine the simultaneous Laurent localization with the explicit
upper-triangular fields used by finite multiblock elimination.
-/

noncomputable section

namespace AbelFormalization

universe u v w

section Conjugation

variable {S A B : Type*}
variable [CommRing S] [CommRing A] [CommRing B]
variable [Algebra S A] [Algebra S B]

/-- Conjugate a derivation through an algebra equivalence. -/
def derivationConjugate (e : A ≃ₐ[S] B) (D : Derivation S B B) :
    Derivation S A A :=
  Derivation.mk'
    (e.symm.toLinearMap.comp (D.toLinearMap.comp e.toLinearMap))
    (by
      intro a b
      change e.symm (D (e (a * b))) =
        a * e.symm (D (e b)) + b * e.symm (D (e a))
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add,
        AlgEquiv.symm_apply_apply])

@[simp]
theorem derivationConjugate_apply
    (e : A ≃ₐ[S] B) (D : Derivation S B B) (a : A) :
    derivationConjugate e D a = e.symm (D (e a)) :=
  rfl

end Conjugation

section ConjugationPreservation

variable {A B : Type*}
variable [CommRing A] [CommRing B]
variable [Algebra ℚ A] [Algebra ℚ B]

/-- Preservation descends from an equivalent presentation after conjugating
the derivation. -/
theorem derivationPreservesIdeal_conjugate
    (e : A ≃ₐ[ℚ] B) (I : Ideal A) (D : Derivation ℚ B B)
    (hD : derivationPreservesIdeal (I.map e.toRingHom) D) :
    derivationPreservesIdeal I (derivationConjugate e D) := by
  intro a ha
  apply (Ideal.apply_mem_of_equiv_iff
    (I := I) (f := e.toRingEquiv)).1
  have hmem := hD (e a)
    ((Ideal.apply_mem_of_equiv_iff
      (I := I) (f := e.toRingEquiv)).2 ha)
  change e (derivationConjugate e D a) ∈ I.map e.toRingHom
  rw [derivationConjugate_apply, e.apply_symm_apply]
  exact hmem

end ConjugationPreservation

section GlobalFields

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R]
variable (h : ℕ) (d : Fin h → ℕ)

/-- The field in one chosen global block, obtained by conjugating the
corresponding split block field back to the simultaneous source ring. -/
def terminalGlobalBlockVectorField (b : Fin h) (q : ℕ) :
    Derivation ℚ (TerminalMultiblockSourceRing R h d Keep)
      (TerminalMultiblockSourceRing R h d Keep) :=
  derivationConjugate
    ((terminalSplitRenameEquiv R (Fin h)
      (fun c ↦ d c + 1) Keep b).restrictScalars ℚ)
    (terminalBlockVectorField R
      (TerminalBlockKeepIndex (Fin h) (fun c ↦ d c + 1) Keep b)
      (d b + 1) q)

/-- The conjugated global field is exactly the split field after applying
the split-index rename. -/
theorem terminalSplitRenameEquiv_globalBlockVectorField
    (b : Fin h) (q : ℕ) (P : TerminalMultiblockSourceRing R h d Keep) :
    terminalSplitRenameEquiv R (Fin h) (fun c ↦ d c + 1) Keep b
        (terminalGlobalBlockVectorField R Keep h d b q P) =
      terminalBlockVectorField R
        (TerminalBlockKeepIndex (Fin h) (fun c ↦ d c + 1) Keep b)
        (d b + 1) q
        (terminalSplitRenameEquiv R (Fin h)
          (fun c ↦ d c + 1) Keep b P) := by
  simp [terminalGlobalBlockVectorField]

/-- Global multigrading and global signed-Stirling invariance preserve every
positive lowering field in every block of the simultaneous source. -/
theorem terminalGlobalBlockVectorFields_preserve
    (I : Ideal (TerminalMultiblockSourceRing R h d Keep))
    (hgraded : IsTerminalMultigradedIdeal R (Fin h)
      (fun c ↦ d c + 1) Keep I)
    (hJ : IsTerminalGlobalStirlingInvariant R (Fin h)
      (fun c ↦ d c + 1) Keep I) :
    ∀ b q, 1 ≤ q → derivationPreservesIdeal I
      (terminalGlobalBlockVectorField R Keep h d b q) := by
  intro b q hq
  apply derivationPreservesIdeal_conjugate
    ((terminalSplitRenameEquiv R (Fin h)
      (fun c ↦ d c + 1) Keep b).restrictScalars ℚ) I
  simpa using terminalSplitBlockVectorFields_preserve
    R (Fin h) (fun c ↦ d c + 1) Keep I hgraded hJ b q hq

end GlobalFields

section GlobalFieldActions

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R]
variable (h : ℕ) (d : Fin h → ℕ)

@[simp]
theorem terminalGlobalBlockVectorField_C
    (b : Fin h) (q : ℕ) (a : R) :
    terminalGlobalBlockVectorField R Keep h d b q (MvPolynomial.C a) = 0 := by
  simp [terminalGlobalBlockVectorField]

@[simp]
theorem terminalGlobalBlockVectorField_X_keep
    (b : Fin h) (q : ℕ) (k : Keep) :
    terminalGlobalBlockVectorField R Keep h d b q
        (MvPolynomial.X
          (Sum.inr k : TerminalMultiblockSourceIndex h d Keep)) = 0 := by
  simp [terminalGlobalBlockVectorField]

/-- A field in block `b` annihilates source variables in another block. -/
theorem terminalGlobalBlockVectorField_X_other
    (b c : Fin h) (hcb : c ≠ b) (q : ℕ) (r : Fin (d c + 1)) :
    terminalGlobalBlockVectorField R Keep h d b q
        (MvPolynomial.X
          (Sum.inl ⟨c, r⟩ : TerminalMultiblockSourceIndex h d Keep)) = 0 := by
  simp [terminalGlobalBlockVectorField, hcb]

/-- Exact action of the conjugated global field on a variable in its chosen
block. -/
theorem terminalGlobalBlockVectorField_X_same
    (b : Fin h) (q : ℕ) (r : Fin (d b + 1)) :
    terminalGlobalBlockVectorField R Keep h d b q
        (MvPolynomial.X
          (Sum.inl ⟨b, r⟩ : TerminalMultiblockSourceIndex h d Keep)) =
      if q ≤ r.val then
        ((r.val + 1).choose (q + 1) :
          TerminalMultiblockSourceRing R h d Keep) *
          MvPolynomial.X
            (Sum.inl
              ⟨b, (⟨r.val - q,
                (Nat.sub_le r.val q).trans_lt r.isLt⟩ : Fin (d b + 1))⟩ :
              TerminalMultiblockSourceIndex h d Keep)
      else 0 := by
  rw [terminalGlobalBlockVectorField, derivationConjugate_apply]
  change
    (terminalSplitRenameEquiv R (Fin h)
      (fun c ↦ d c + 1) Keep b).symm
      (terminalBlockVectorField R
        (TerminalBlockKeepIndex (Fin h) (fun c ↦ d c + 1) Keep b)
        (d b + 1) q
        (terminalSplitRenameEquiv R (Fin h)
          (fun c ↦ d c + 1) Keep b
          (MvPolynomial.X (Sum.inl ⟨b, r⟩)))) = _
  rw [terminalSplitRenameEquiv_X_sameBlock,
    terminalBlockVectorField_X_block]
  by_cases hqr : q ≤ r.val
  · rw [if_pos hqr, map_mul, map_natCast,
      terminalSplitRenameEquiv_symm_X_sameBlock, if_pos hqr]
  · rw [if_neg hqr, map_zero, if_neg hqr]

end GlobalFieldActions

section LocalizedFieldActions

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R]
variable (h : ℕ) (d : Fin h → ℕ)

@[simp]
theorem derivation_finsetSum_apply
    {ι A : Type*} [CommRing A] [Algebra ℚ A]
    (s : Finset ι) (D : ι → Derivation ℚ A A) (a : A) :
    (s.sum D) a = s.sum (fun i ↦ D i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, Derivation.add_apply]

/-- Evaluation at one ring element as an additive homomorphism on
derivations. -/
def derivationApplyAddHom
    {A : Type*} [CommRing A] [Algebra ℚ A] (a : A) :
    Derivation ℚ A A →+ A where
  toFun := fun D ↦ D a
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

@[simp]
theorem derivationApplyAddHom_apply
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (a : A) (D : Derivation ℚ A A) :
    derivationApplyAddHom a D = D a :=
  rfl

@[simp]
theorem terminalMultiblockTriangularField_C
    (b : Fin h) (j : Fin (d b))
    (a : TerminalMultiblockLaurentRing R Keep h) :
    terminalMultiblockTriangularField R Keep h d b j
        (MvPolynomial.C a) = 0 := by
  rw [terminalMultiblockTriangularField]
  change derivationApplyAddHom (MvPolynomial.C a) (_ + _) = 0
  rw [map_add, map_sum]
  simp [terminalMultiblockHigherPDeriv]

/-- A triangular field in block `b` annihilates higher variables in every
other block. -/
theorem terminalMultiblockTriangularField_X_other
    (b c : Fin h) (hcb : c ≠ b) (j : Fin (d b)) (k : Fin (d c)) :
    terminalMultiblockTriangularField R Keep h d b j
        (MvPolynomial.X
          (⟨c, k⟩ : TerminalMultiblockHigherIndex h d)) = 0 := by
  classical
  rw [terminalMultiblockTriangularField]
  change derivationApplyAddHom
    (MvPolynomial.X
      (⟨c, k⟩ : TerminalMultiblockHigherIndex h d) :
        TerminalMultiblockLocalizedRing R Keep h d) (_ + _) = 0
  rw [map_add, map_sum]
  simp [
    terminalMultiblockHigherPDeriv, terminalMultiblockOffDiagonalCoefficient,
    hcb]
  apply Finset.sum_eq_zero
  intro x hx
  have hjx : j < x := Finset.mem_Ioi.mp hx
  simp [DFunLike.dite_apply, terminalMultiblockHigherPDeriv, hjx, hcb]

/-- The diagonal action is multiplication by the Laurent first variable. -/
theorem terminalMultiblockTriangularField_X_self
    (b : Fin h) (j : Fin (d b)) :
    terminalMultiblockTriangularField R Keep h d b j
        (MvPolynomial.X
          (⟨b, j⟩ : TerminalMultiblockHigherIndex h d)) =
      terminalMultiblockFirstVariable R Keep h d b := by
  classical
  rw [terminalMultiblockTriangularField]
  change derivationApplyAddHom
    (MvPolynomial.X
      (⟨b, j⟩ : TerminalMultiblockHigherIndex h d) :
        TerminalMultiblockLocalizedRing R Keep h d) (_ + _) = _
  rw [map_add, map_sum]
  simp [
    terminalMultiblockHigherPDeriv, terminalMultiblockOffDiagonalCoefficient]
  apply Finset.sum_eq_zero
  intro x hx
  have hjx : j < x := Finset.mem_Ioi.mp hx
  simp [DFunLike.dite_apply, terminalMultiblockHigherPDeriv, hjx,
    ne_of_gt hjx]

/-- Entries below the block diagonal vanish. -/
theorem terminalMultiblockTriangularField_X_of_lt
    (b : Fin h) (j k : Fin (d b)) (hkj : k < j) :
    terminalMultiblockTriangularField R Keep h d b j
        (MvPolynomial.X
          (⟨b, k⟩ : TerminalMultiblockHigherIndex h d)) = 0 := by
  classical
  rw [terminalMultiblockTriangularField]
  change derivationApplyAddHom
    (MvPolynomial.X
      (⟨b, k⟩ : TerminalMultiblockHigherIndex h d) :
        TerminalMultiblockLocalizedRing R Keep h d) (_ + _) = 0
  rw [map_add, map_sum]
  simp [
    terminalMultiblockHigherPDeriv, terminalMultiblockOffDiagonalCoefficient,
    ne_of_gt hkj]
  apply Finset.sum_eq_zero
  intro x hx
  have hjx : j < x := Finset.mem_Ioi.mp hx
  have hkx : k < x := lt_trans hkj hjx
  simp [DFunLike.dite_apply, terminalMultiblockHigherPDeriv, hjx,
    ne_of_gt hkx]

/-- A strict upper-diagonal entry is the expected binomial multiple of the
earlier higher variable in the same block. -/
theorem terminalMultiblockTriangularField_X_of_gt
    (b : Fin h) (j k : Fin (d b)) (hjk : j < k) :
    terminalMultiblockTriangularField R Keep h d b j
        (MvPolynomial.X
          (⟨b, k⟩ : TerminalMultiblockHigherIndex h d)) =
      ((k.val + 2).choose (j.val + 2) :
          TerminalMultiblockLocalizedRing R Keep h d) *
        MvPolynomial.X
          (⟨b, terminalLaurentHigherIndex (d b) j k hjk⟩ :
            TerminalMultiblockHigherIndex h d) := by
  classical
  rw [terminalMultiblockTriangularField]
  change derivationApplyAddHom
    (MvPolynomial.X
      (⟨b, k⟩ : TerminalMultiblockHigherIndex h d) :
        TerminalMultiblockLocalizedRing R Keep h d) (_ + _) = _
  rw [map_add, map_sum]
  simp [
    terminalMultiblockHigherPDeriv, terminalMultiblockOffDiagonalCoefficient,
    hjk, ne_of_lt hjk]
  rw [Finset.sum_eq_single k]
  · simp [DFunLike.dite_apply, terminalMultiblockHigherPDeriv, hjk]
  · intro x hx hne
    have hjx : j < x := Finset.mem_Ioi.mp hx
    simp [DFunLike.dite_apply, terminalMultiblockHigherPDeriv, hjx, hne]
  · intro hk
    exact (hk (Finset.mem_Ioi.mpr hjk)).elim

end LocalizedFieldActions

section LocalizationIntertwining

variable (R Keep : Type*) [CommRing R] [Algebra ℚ R]
variable (h : ℕ) (d : Fin h → ℕ)

/-- The simultaneous localization intertwines a global block field with the
displayed localized triangular field on every source generator. -/
theorem terminalMultiblockLocalizationHom_globalBlockVectorField_X
    (b : Fin h) (j : Fin (d b))
    (z : TerminalMultiblockSourceIndex h d Keep) :
    terminalMultiblockLocalizationHom R Keep h d
        (terminalGlobalBlockVectorField R Keep h d b (j.val + 1)
          (MvPolynomial.X z)) =
      terminalMultiblockTriangularField R Keep h d b j
        (terminalMultiblockLocalizationHom R Keep h d
          (MvPolynomial.X z)) := by
  classical
  rcases z with x | t
  · rcases x with ⟨c, r⟩
    by_cases hcb : c = b
    · subst c
      refine Fin.cases ?_ (fun k ↦ ?_) r
      · have hnot : ¬j.val + 1 ≤ (0 : Fin (d b + 1)).val := by simp
        rw [terminalGlobalBlockVectorField_X_same, if_neg hnot, map_zero,
          terminalMultiblockLocalizationHom_X_first,
          terminalMultiblockFirstVariable,
          terminalMultiblockTriangularField_C]
      · rcases lt_trichotomy k j with hkj | hkj | hjk
        · have hnot : ¬j.val + 1 ≤ k.succ.val := by
            simpa using not_le_of_gt (Nat.succ_lt_succ hkj)
          rw [terminalGlobalBlockVectorField_X_same, if_neg hnot, map_zero,
            terminalMultiblockLocalizationHom_X_higher,
            terminalMultiblockTriangularField_X_of_lt R Keep h d b j k hkj]
        · subst k
          rw [terminalGlobalBlockVectorField_X_same,
            if_pos (by simp), map_mul, map_natCast]
          have hz :
              (⟨j.succ.val - (j.val + 1),
                (Nat.sub_le j.succ.val (j.val + 1)).trans_lt j.succ.isLt⟩ :
                  Fin (d b + 1)) = 0 := by
            apply Fin.ext
            simp
          rw [hz, terminalMultiblockLocalizationHom_X_first,
            terminalMultiblockLocalizationHom_X_higher,
            terminalMultiblockTriangularField_X_self]
          simp
        · have hle : j.val + 1 ≤ k.succ.val := by
            simpa using Nat.succ_le_succ (Nat.le_of_lt hjk)
          rw [terminalGlobalBlockVectorField_X_same, if_pos hle,
            map_mul, map_natCast]
          have hr :
              (⟨k.succ.val - (j.val + 1),
                (Nat.sub_le k.succ.val (j.val + 1)).trans_lt k.succ.isLt⟩ :
                  Fin (d b + 1)) =
                (terminalLaurentHigherIndex (d b) j k hjk).succ := by
            apply Fin.ext
            simp [terminalLaurentHigherIndex]
            omega
          rw [hr, terminalMultiblockLocalizationHom_X_higher,
            terminalMultiblockLocalizationHom_X_higher,
            terminalMultiblockTriangularField_X_of_gt R Keep h d b j k hjk]
          simp
    · refine Fin.cases ?_ (fun k ↦ ?_) r
      · rw [terminalGlobalBlockVectorField_X_other R Keep h d b c hcb,
          map_zero, terminalMultiblockLocalizationHom_X_first,
          terminalMultiblockFirstVariable,
          terminalMultiblockTriangularField_C]
      · rw [terminalGlobalBlockVectorField_X_other R Keep h d b c hcb,
          map_zero, terminalMultiblockLocalizationHom_X_higher,
          terminalMultiblockTriangularField_X_other R Keep h d b c hcb]
  · rw [terminalGlobalBlockVectorField_X_keep, map_zero,
      terminalMultiblockLocalizationHom_X_keep,
      terminalMultiblockTriangularField_C]

/-- The generator calculation extends to the complete source polynomial
ring. -/
theorem terminalMultiblockLocalizationHom_globalBlockVectorField
    (b : Fin h) (j : Fin (d b))
    (P : TerminalMultiblockSourceRing R h d Keep) :
    terminalMultiblockLocalizationHom R Keep h d
        (terminalGlobalBlockVectorField R Keep h d b (j.val + 1) P) =
      terminalMultiblockTriangularField R Keep h d b j
        (terminalMultiblockLocalizationHom R Keep h d P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P z hP =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
        hP, terminalMultiblockLocalizationHom_globalBlockVectorField_X]

/-- The source fields required by multiblock elimination preserve the global
ideal and have exactly the localized triangular form. -/
theorem terminalMultiblockTriangularFields_preserve_mappedIdeal_of_global
    (I : Ideal (TerminalMultiblockSourceRing R h d Keep))
    (hgraded : IsTerminalMultigradedIdeal R (Fin h)
      (fun c ↦ d c + 1) Keep I)
    (hJ : IsTerminalGlobalStirlingInvariant R (Fin h)
      (fun c ↦ d c + 1) Keep I) :
    ∀ (b : Fin h) (j : Fin (d b)), derivationPreservesIdeal
      (I.map (terminalMultiblockLocalizationHom R Keep h d))
      (terminalMultiblockTriangularField R Keep h d b j) := by
  apply terminalMultiblockTriangularField_preserves_mappedIdeal
    R Keep h d I
    (fun b j ↦ terminalGlobalBlockVectorField R Keep h d b (j.val + 1))
  · intro b j
    exact terminalGlobalBlockVectorFields_preserve R Keep h d I hgraded hJ
      b (j.val + 1) (Nat.succ_le_succ (Nat.zero_le j.val))
  · exact terminalMultiblockLocalizationHom_globalBlockVectorField
      R Keep h d

end LocalizationIntertwining

end AbelFormalization
