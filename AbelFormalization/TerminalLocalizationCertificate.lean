import AbelFormalization.TerminalGlobalHeightReduction
import AbelFormalization.LocalizedSubmoduleClearing
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# A common first-derivative denominator for terminal localization

The simultaneous terminal localization inverts the first derivative variable
in every finite block.  This file records that every element of its defining
submonoid divides a power of the product of all those first variables.  Thus a
single denominator supplied by finite localization clearing can be replaced
by one common product power, as required by the backwards quantitative trace.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace AbelFormalization

open scoped BigOperators Pointwise

/-- Regroup the terminal source first by retained variables and then by the
first derivative variable of each block. -/
def terminalFirstDerivativePolynomialEquiv
    (R Keep : Type*) [CommRing R] (h : Nat) (d : Fin h → Nat) :
    TerminalMultiblockSourceRing R h d Keep ≃+*
      MvPolynomial (Fin h)
        (MvPolynomial (TerminalMultiblockHigherIndex h d)
          (TerminalMultiblockRetainedRing R Keep)) :=
  (terminalMultiblockCentralSourceEquiv R Keep h d).toRingEquiv.trans
    (MvPolynomial.sumAlgEquiv
      (TerminalMultiblockRetainedRing R Keep)
      (Fin h) (TerminalMultiblockHigherIndex h d)).toRingEquiv

@[simp]
theorem terminalFirstDerivativePolynomialEquiv_X_first
    (R Keep : Type*) [CommRing R] (h : Nat) (d : Fin h → Nat)
    (b : Fin h) :
    terminalFirstDerivativePolynomialEquiv R Keep h d
        (MvPolynomial.X (Sum.inl ⟨b, (0 : Fin (d b + 1))⟩)) =
      MvPolynomial.X b := by
  simp [terminalFirstDerivativePolynomialEquiv,
    terminalMultiblockCentralSourceEquiv]

/-- Product of all first derivative variables, expressed through the
regrouping equivalence so powers interact directly with the localization
submonoid. -/
def terminalFirstDerivativeProduct
    (R Keep : Type*) [CommRing R] (h : Nat) (d : Fin h → Nat) :
    TerminalMultiblockSourceRing R h d Keep :=
  (terminalFirstDerivativePolynomialEquiv R Keep h d).symm
    (∏ b : Fin h, MvPolynomial.X b)

/-- The abstract product is the literal product of the first variables in
the original terminal source presentation. -/
theorem terminalFirstDerivativeProduct_eq_prod
    (R Keep : Type*) [CommRing R] (h : Nat) (d : Fin h → Nat) :
    terminalFirstDerivativeProduct R Keep h d =
      ∏ b : Fin h,
        MvPolynomial.X (Sum.inl ⟨b, (0 : Fin (d b + 1))⟩) := by
  apply (terminalFirstDerivativePolynomialEquiv R Keep h d).injective
  simp [terminalFirstDerivativeProduct]

/-- Every allowed simultaneous-localization denominator divides a power of
the common product of first derivative variables. -/
theorem terminalLocalizationSubmonoid_dvd_product_pow
    (R Keep : Type*) [CommRing R] (h : Nat) (d : Fin h → Nat)
    (s : terminalMultiblockLocalizationSubmonoid R Keep h d) :
    ∃ a : Nat, (s : TerminalMultiblockSourceRing R h d Keep) ∣
      terminalFirstDerivativeProduct R Keep h d ^ a := by
  let e := terminalFirstDerivativePolynomialEquiv R Keep h d
  have hs := s.property
  change e (s : TerminalMultiblockSourceRing R h d Keep) ∈
    laurentVariableSubmonoid (Fin h)
      (MvPolynomial (TerminalMultiblockHigherIndex h d)
        (TerminalMultiblockRetainedRing R Keep)) at hs
  change e (s : TerminalMultiblockSourceRing R h d Keep) ∈
    Submonoid.closure (Set.range MvPolynomial.X) at hs
  obtain ⟨exponent, hexponent⟩ :=
    Submonoid.exists_of_mem_closure_range
      (fun b : Fin h =>
        (MvPolynomial.X b : MvPolynomial (Fin h)
          (MvPolynomial (TerminalMultiblockHigherIndex h d)
            (TerminalMultiblockRetainedRing R Keep))))
      (e (s : TerminalMultiblockSourceRing R h d Keep)) hs
  let a : Nat := ∑ b : Fin h, exponent b
  have hle (b : Fin h) : exponent b ≤ a := by
    dsimp only [a]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (exponent i))
      (Finset.mem_univ b)
  have htarget :
      e (s : TerminalMultiblockSourceRing R h d Keep) ∣
        (∏ b : Fin h, MvPolynomial.X b) ^ a := by
    rw [hexponent, ← Finset.prod_pow]
    exact Finset.prod_dvd_prod_of_dvd _ _
      (fun b _ => pow_dvd_pow (MvPolynomial.X b) (hle b))
  refine ⟨a, ?_⟩
  have hback := map_dvd e.symm htarget
  simpa only [e, RingEquiv.symm_apply_apply, map_pow,
    terminalFirstDerivativeProduct] using hback

/-- If one scalar divides another, clearing an ideal by the first scalar also
clears it by the second. -/
theorem ideal_smul_le_of_dvd_of_smul_le
    {A : Type*} [CommRing A] (P Q : Ideal A) {s v : A}
    (hsv : s ∣ v) (hs : s • P ≤ Q) : v • P ≤ Q := by
  obtain ⟨q, rfl⟩ := hsv
  rw [mul_smul]
  simpa only [← mul_smul, mul_comm] using
    (smul_le_smul_left q hs).trans (Q.smul_le_self_of_tower q)

/-- Ideal-map containment over a localization admits one common clearing
denominator when the source ideal is finitely generated. -/
theorem exists_smul_le_of_ideal_map_le
    {A T : Type*} [CommRing A] [CommRing T] [Algebra A T]
    (S : Submonoid A) [IsLocalization S T]
    (P Q : Ideal A) (hP : P.FG)
    (hPQ : P.map (algebraMap A T) ≤ Q.map (algebraMap A T)) :
    ∃ s : S, s • P ≤ Q := by
  apply exists_smul_le_of_localized'_le
    (R := A) (T := T) (M := A) (Mloc := T)
    S (Algebra.linearMap A T) hP
  simpa only [Ideal.localized'_eq_map] using hPQ

/-- Use simultaneous terminal localization as the source algebra map. -/
local instance terminalLocalizationCertificateAlgebra
    (R Keep : Type*) [CommRing R]
    (h : Nat) (d : Fin h → Nat) :
    Algebra (TerminalMultiblockSourceRing R h d Keep)
      (TerminalMultiblockLocalizedRing R Keep h d) :=
  (terminalMultiblockLocalizationHom R Keep h d).toAlgebra

/-- A finitely generated ideal inclusion after simultaneous terminal
localization can be cleared by one element of the defining submonoid. -/
theorem exists_terminalLocalizationSubmonoid_smul_le
    (R Keep : Type*) [CommRing R] (h : Nat) (d : Fin h → Nat)
    (P Q : Ideal (TerminalMultiblockSourceRing R h d Keep))
    (hP : P.FG)
    (hPQ :
      P.map (terminalMultiblockLocalizationHom R Keep h d) ≤
        Q.map (terminalMultiblockLocalizationHom R Keep h d)) :
    ∃ s : terminalMultiblockLocalizationSubmonoid R Keep h d,
      s • P ≤ Q := by
  let _ : IsLocalization
      (terminalMultiblockLocalizationSubmonoid R Keep h d)
      (TerminalMultiblockLocalizedRing R Keep h d) :=
    terminalMultiblock_isLocalization R Keep h d
  rw [← RingHom.algebraMap_toAlgebra
    (terminalMultiblockLocalizationHom R Keep h d)] at hPQ
  exact exists_smul_le_of_ideal_map_le
    (A := TerminalMultiblockSourceRing R h d Keep)
    (T := TerminalMultiblockLocalizedRing R Keep h d)
    (terminalMultiblockLocalizationSubmonoid R Keep h d)
    P Q hP hPQ

/-- A localized inclusion from a finitely generated ideal can be cleared by a
power of the single product of all first derivative variables. -/
theorem exists_common_firstDerivativeProduct_pow_smul_le
    (R Keep : Type*) [CommRing R] (h : Nat) (d : Fin h → Nat)
    (P Q : Ideal (TerminalMultiblockSourceRing R h d Keep))
    (hP : P.FG)
    (hPQ :
      P.map (terminalMultiblockLocalizationHom R Keep h d) ≤
        Q.map (terminalMultiblockLocalizationHom R Keep h d)) :
    ∃ a : Nat,
      terminalFirstDerivativeProduct R Keep h d ^ a • P ≤ Q := by
  obtain ⟨s, hs⟩ :=
    exists_terminalLocalizationSubmonoid_smul_le R Keep h d P Q hP hPQ
  obtain ⟨a, ha⟩ :=
    terminalLocalizationSubmonoid_dvd_product_pow R Keep h d s
  exact ⟨a, ideal_smul_le_of_dvd_of_smul_le P Q ha hs⟩

end AbelFormalization
