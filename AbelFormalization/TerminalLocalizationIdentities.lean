import AbelFormalization.TerminalLocalizationCertificate
import Mathlib.RingTheory.Ideal.Operations

/-!
# Literal identities after clearing terminal localization denominators

Finite ideal generators turn the ideal containment supplied by terminal
localization clearing into finitely many literal polynomial identities.  The
coefficient family produced here is allowed to depend on the source
generator, while the exponent of the common first-derivative product is
uniform over the whole source family.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

open scoped BigOperators Pointwise

/-- If multiplying an ideal by `v` lands in the span of a finite family, then
each chosen member of the ideal has a literal finite linear-combination
identity after multiplication by `v`. -/
theorem ideal_smul_le_span_range_exists_generator_coefficients
    {A L J : Type*} [CommRing A] [Fintype L] [Fintype J]
    (P : Ideal A) (c : L → A) (G : J → A) (v : A)
    (hc : ∀ l, c l ∈ P)
    (hclear : v • P ≤ Ideal.span (Set.range G)) :
    ∃ b : L → J → A, ∀ l,
      v * c l = ∑ j, b l j * G j := by
  classical
  have hcoeff : ∀ l : L, ∃ b : J → A,
      v * c l = ∑ j, b j * G j := by
    intro l
    have hmem : v * c l ∈ Ideal.span (Set.range G) := by
      apply hclear
      simpa only [smul_eq_mul] using
        (Submodule.smul_mem_pointwise_smul
          (α := A) (R := A) (M := A) (c l) v P (hc l))
    obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
    exact ⟨b, hb.symm⟩
  choose b hb using hcoeff
  exact ⟨b, hb⟩

/-- A pointwise-cleared containment between two ideals displayed by finite
generating families yields, on the displayed source generators, a matrix of
literal finite linear-combination identities. -/
theorem ideal_smul_le_exists_generator_identities
    {A L J : Type*} [CommRing A] [Fintype L] [Fintype J]
    (P Q : Ideal A) (c : L → A) (G : J → A) (v : A)
    (hP : Ideal.span (Set.range c) = P)
    (hQ : Ideal.span (Set.range G) = Q)
    (hclear : v • P ≤ Q) :
    ∃ b : L → J → A, ∀ l,
      v * c l = ∑ j, b l j * G j := by
  have hc : ∀ l, c l ∈ P := by
    intro l
    rw [← hP]
    exact Ideal.mem_span_range_self
  have hclear' : v • P ≤ Ideal.span (Set.range G) := by
    rw [hQ]
    exact hclear
  exact ideal_smul_le_span_range_exists_generator_coefficients
    P c G v hc hclear'

/-- Localized containment between ideals displayed by finite generating
families gives one exponent and one coefficient matrix witnessing all
cleared source-generator identities.  In particular, the common exponent
does not depend on the source-generator index. -/
theorem exists_common_firstDerivativeProduct_pow_generator_identities
    (R Keep L J : Type*) [CommRing R]
    [Fintype L] [Fintype J]
    (h : Nat) (d : Fin h → Nat)
    (P Q : Ideal (TerminalMultiblockSourceRing R h d Keep))
    (c : L → TerminalMultiblockSourceRing R h d Keep)
    (G : J → TerminalMultiblockSourceRing R h d Keep)
    (hP : Ideal.span (Set.range c) = P)
    (hQ : Ideal.span (Set.range G) = Q)
    (hPQ :
      P.map (terminalMultiblockLocalizationHom R Keep h d) ≤
        Q.map (terminalMultiblockLocalizationHom R Keep h d)) :
    ∃ a : Nat,
      ∃ b : L → J → TerminalMultiblockSourceRing R h d Keep,
        ∀ l,
          terminalFirstDerivativeProduct R Keep h d ^ a * c l =
            ∑ j, b l j * G j := by
  have hPfg : P.FG := by
    rw [← hP]
    exact Submodule.fg_span (Set.finite_range c)
  obtain ⟨a, hclear⟩ :=
    exists_common_firstDerivativeProduct_pow_smul_le
      R Keep h d P Q hPfg hPQ
  obtain ⟨b, hb⟩ := ideal_smul_le_exists_generator_identities
    P Q c G (terminalFirstDerivativeProduct R Keep h d ^ a)
    hP hQ hclear
  exact ⟨a, b, hb⟩

end AbelFormalization
