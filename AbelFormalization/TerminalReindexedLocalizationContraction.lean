import AbelFormalization.TerminalReindexedLocalizationIteration
import AbelFormalization.LocalizedSubmoduleClearing
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.Basic

set_option autoImplicit false

/-!
# Contraction of a stabilized localized terminal iteration

This file implements the ideal-level localization, contraction, and
denominator-clearing step.  The generic lemmas first record that an ideal in
a localization is recovered from its contraction and that invariance under a
commuting automorphism descends to the contraction.  They then clear one
denominator from an ideal having the same localization as that contraction.

For a coefficient localization `B → Localization S`, the polynomial ring
over the localization is the localization of `MvPolynomial (Fin n) B` at
`S.map MvPolynomial.C`.  Consequently the denominator supplied by the generic
lemma is represented by `MvPolynomial.C b` for one `b : S`, which gives the
principal-ideal sandwich used in the descent argument.
-/

noncomputable section

namespace AbelFormalization

open scoped Pointwise

universe u v w

/- `MvPolynomial.isLocalization` is stated for this canonical, deliberately
non-global algebra structure. -/
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## Generic ideal contraction lemmas -/

/-- The contraction of an ideal from a localization is finitely generated
when the source ring is Noetherian. -/
theorem idealLocalizationContraction_fg
    {A : Type u} {T : Type v} [CommRing A] [CommRing T]
    [Algebra A T] [IsNoetherianRing A]
    (M : Submonoid A) [IsLocalization M T]
    (L : Ideal T) :
    (L.comap (algebraMap A T)).FG :=
  IsNoetherian.noetherian _

/-- Extending a contracted ideal back to a localization recovers the
original ideal. -/
theorem map_idealLocalizationContraction
    {A : Type u} {T : Type v} [CommRing A] [CommRing T]
    [Algebra A T]
    (M : Submonoid A) [IsLocalization M T]
    (L : Ideal T) :
    (L.comap (algebraMap A T)).map (algebraMap A T) = L :=
  IsLocalization.map_under M T L

/-- Invariance descends through a commuting ring-homomorphism square.  This
does not require localization; it is separated out because the same argument
applies to any contraction along a ring map. -/
theorem map_idealComap_eq_of_equiv_commutes
    {A : Type u} {T : Type v} [CommRing A] [CommRing T]
    (f : A →+* T) (J : A ≃+* A) (J' : T ≃+* T)
    (L : Ideal T)
    (hJ : f.comp J.toRingHom = J'.toRingHom.comp f)
    (hL : L.map J'.toRingHom = L) :
    (L.comap f).map J.toRingHom = L.comap f := by
  have hJsymm : f.comp (J.symm : A →+* A) =
      (J'.symm : T →+* T).comp f := by
    ext x
    change f (J.symm x) = J'.symm (f x)
    apply J'.injective
    rw [J'.apply_symm_apply]
    have hx := RingHom.congr_fun hJ (J.symm x)
    change f (J (J.symm x)) = J' (f (J.symm x)) at hx
    rw [J.apply_symm_apply] at hx
    exact hx.symm
  have hL' : L.map (J' : T →+* T) = L := by
    simpa only [RingEquiv.toRingHom_eq_coe] using hL
  calc
    (L.comap f).map (J : A →+* A) =
        (L.comap f).comap (J.symm : A →+* A) :=
      Ideal.map_comap_of_equiv J
    _ = L.comap (f.comp (J.symm : A →+* A)) := by
      rw [Ideal.comap_comap]
    _ = L.comap ((J'.symm : T →+* T).comp f) := by rw [hJsymm]
    _ = (L.comap (J'.symm : T →+* T)).comap f := by
      rw [Ideal.comap_comap]
    _ = (L.map (J' : T →+* T)).comap f := by
      exact congrArg (fun P : Ideal T => P.comap f)
        (Ideal.map_comap_of_equiv (I := L) J').symm
    _ = L.comap f := by rw [hL']

/-- If an ideal and a localized ideal agree after extension, one element of
the localizing submonoid sandwiches the source ideal between a multiple of
the contraction and the contraction. -/
theorem exists_smul_idealLocalizationContraction_le_and_le
    {A : Type u} {T : Type v} [CommRing A] [CommRing T]
    [Algebra A T] [IsNoetherianRing A]
    (M : Submonoid A) [IsLocalization M T]
    (N : Ideal A) (L : Ideal T)
    (hNL : N.map (algebraMap A T) = L) :
    ∃ s : M,
      (s : A) • L.comap (algebraMap A T) ≤ N ∧
        N ≤ L.comap (algebraMap A T) := by
  let K : Ideal A := L.comap (algebraMap A T)
  have hKfg : K.FG := by
    simpa only [K] using idealLocalizationContraction_fg M L
  have hKloc :
      K.localized' T M (Algebra.linearMap A T) =
        N.localized' T M (Algebra.linearMap A T) := by
    rw [Ideal.localized'_eq_map, Ideal.localized'_eq_map,
      show K.map (algebraMap A T) = L by
        simpa only [K] using map_idealLocalizationContraction M L,
      hNL]
  obtain ⟨s, hs⟩ := exists_smul_le_of_localized'_le M
    (Algebra.linearMap A T) hKfg hKloc.le
  refine ⟨s, ?_, ?_⟩
  · change (s : A) • K ≤ N at hs
    simpa only [K] using hs
  · simpa only [K] using
      (Ideal.map_le_iff_le_comap.mp hNL.le)

/-! ## Polynomial coefficient localization -/

variable {B : Type u} [CommRing B] [IsNoetherianRing B]
variable {h n : ℕ} (d : Fin h → ℕ) (Time : Type w)

/-- Contracting a stabilized localized terminal ideal gives a finitely
generated invariant ideal in the source polynomial ring, and one coefficient
denominator gives the required ideal sandwich. -/
theorem terminalReindexedLocalizationContraction_sandwich
    (S : Submonoid B)
    (e : TerminalFiniteReindex (n := n) d Time)
    (I_j : Ideal (MvPolynomial (Fin n) B))
    (L : Ideal (MvPolynomial (Fin n) (Localization S)))
    (hI_jL : I_j.map
      (MvPolynomial.map (algebraMap B (Localization S))) = L)
    (hL : L.map
      (terminalReindexedGlobalStirlingEquiv
        (R := Localization S) d Time e).toRingEquiv.toRingHom = L) :
    let φ := MvPolynomial.map (algebraMap B (Localization S))
    let sourceJ := (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).toRingEquiv
    let K := L.comap φ
    K.FG ∧
      K.map φ = L ∧
      K.map sourceJ.toRingHom = K ∧
      ∃ b : S,
        Ideal.span {MvPolynomial.C (b : B)} * K ≤ I_j ∧ I_j ≤ K := by
  let A := MvPolynomial (Fin n) B
  let T := MvPolynomial (Fin n) (Localization S)
  let φ : A →+* T :=
    MvPolynomial.map (algebraMap B (Localization S))
  let sourceJ := (terminalReindexedGlobalStirlingEquiv
    (R := B) d Time e).toRingEquiv
  let localizedJ := (terminalReindexedGlobalStirlingEquiv
    (R := Localization S) d Time e).toRingEquiv
  let polynomialS : Submonoid A :=
    S.map (MvPolynomial.C : B →+* A)
  let K : Ideal A := L.comap φ
  have hI_jL' : I_j.map (algebraMap A T) = L := by
    simpa only [A, T, φ, MvPolynomial.algebraMap_def] using hI_jL
  have hKfg : K.FG := by
    simpa only [K, φ, A, T, MvPolynomial.algebraMap_def] using
      (idealLocalizationContraction_fg polynomialS L)
  have hKmap : K.map φ = L := by
    simpa only [K, φ, A, T, MvPolynomial.algebraMap_def] using
      (map_idealLocalizationContraction polynomialS L)
  have hcommute : φ.comp sourceJ.toRingHom =
      localizedJ.toRingHom.comp φ := by
    simpa only [φ, sourceJ, localizedJ, A, T] using
      map_comp_terminalReindexedGlobalStirlingEquiv d Time e
        (algebraMap B (Localization S))
  have hKinv : K.map sourceJ.toRingHom = K := by
    simpa only [K] using
      map_idealComap_eq_of_equiv_commutes φ sourceJ localizedJ L
        hcommute hL
  obtain ⟨s, hsK, hIK⟩ :=
    exists_smul_idealLocalizationContraction_le_and_le
      polynomialS I_j L hI_jL'
  have hsprop := s.property
  change (s : A) ∈ S.map (MvPolynomial.C : B →+* A) at hsprop
  obtain ⟨b, hb, hb_eq⟩ := Submonoid.mem_map.mp hsprop
  refine ⟨hKfg, hKmap, hKinv, ⟨⟨b, hb⟩, ?_, ?_⟩⟩
  · rw [← Ideal.smul_eq_mul,
      Submodule.ideal_span_singleton_smul, hb_eq]
    simpa only [K, φ, A, T, MvPolynomial.algebraMap_def] using hsK
  · simpa only [K, φ, A, T, MvPolynomial.algebraMap_def] using hIK

/-! ## Direct application to one localized terminal iterate -/

/-- Once the localized image of a terminal iterate is fixed by the localized
Stirling automorphism, its contraction and coefficient-denominator sandwich
have all the properties needed by the next descent stage. -/
theorem terminalReindexedIteration_localizationContraction_sandwich
    (S : Submonoid B)
    (e : TerminalFiniteReindex (n := n) d Time)
    (Q : Ideal (MvPolynomial (Fin n) B)) (j : ℕ)
    (hfixed :
      ((lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e)
          (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingEquiv Q j).map
        (MvPolynomial.map (algebraMap B (Localization S)))).map
          (terminalReindexedGlobalStirlingEquiv
            (R := Localization S) d Time e).toRingEquiv.toRingHom =
        (lexicographicInitialIdealIteration
          (terminalReindexedMultiDegree d Time e)
          (terminalReindexedGlobalStirlingEquiv
            (R := B) d Time e).toRingEquiv Q j).map
          (MvPolynomial.map (algebraMap B (Localization S)))) :
    let φ := MvPolynomial.map (algebraMap B (Localization S))
    let sourceJ := (terminalReindexedGlobalStirlingEquiv
      (R := B) d Time e).toRingEquiv
    let I_j := lexicographicInitialIdealIteration
      (terminalReindexedMultiDegree d Time e) sourceJ Q j
    let L := I_j.map φ
    let K := L.comap φ
    K.FG ∧
      K.map φ = L ∧
      K.map sourceJ.toRingHom = K ∧
      ∃ b : S,
        Ideal.span {MvPolynomial.C (b : B)} * K ≤ I_j ∧ I_j ≤ K := by
  let φ : MvPolynomial (Fin n) B →+*
      MvPolynomial (Fin n) (Localization S) :=
    MvPolynomial.map (algebraMap B (Localization S))
  let sourceJ := (terminalReindexedGlobalStirlingEquiv
    (R := B) d Time e).toRingEquiv
  let I_j := lexicographicInitialIdealIteration
    (terminalReindexedMultiDegree d Time e) sourceJ Q j
  let L := I_j.map φ
  exact terminalReindexedLocalizationContraction_sandwich
    (B := B) d Time S e I_j L rfl (by
      simpa only [φ, sourceJ, I_j, L] using hfixed)

end AbelFormalization
