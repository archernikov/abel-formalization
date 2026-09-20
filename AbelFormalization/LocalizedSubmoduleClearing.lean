import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Clearing a denominator from an inclusion of localized submodules

If a finitely generated submodule becomes contained in another submodule after
localization, one element of the localizing submonoid clears the inclusion for
all of its elements at once.
-/

namespace AbelFormalization

open scoped Pointwise

variable {R T M Mloc : Type*}
variable [CommRing R] [CommRing T]
variable [AddCommGroup M] [AddCommGroup Mloc]
variable [Module R M] [Module R Mloc]
variable [Algebra R T] [Module T Mloc] [IsScalarTower R T Mloc]

/-- A localized inclusion out of a finitely generated submodule can be cleared
by one denominator. -/
theorem exists_smul_le_of_localized'_le
    (S : Submonoid R) [IsLocalization S T]
    (q : M →ₗ[R] Mloc) [IsLocalizedModule S q]
    {P Q : Submodule R M} (hP : P.FG)
    (hPQ : P.localized' T S q ≤ Q.localized' T S q) :
    ∃ s : S, s • P ≤ Q := by
  let _ : Module.Finite R P := Module.Finite.of_fg hP
  let fQ : M ⧸ Q →ₗ[R] Mloc ⧸ Q.localized' T S q :=
    Q.toLocalizedQuotient' T S q
  let _ : IsLocalizedModule S fQ := by
    dsimp [fQ]
    infer_instance
  let g₁ : P →ₗ[R] M ⧸ Q := Q.mkQ.comp P.subtype
  let g₂ : P →ₗ[R] M ⧸ Q := 0
  have hcomp : fQ.comp g₁ = fQ.comp g₂ := by
    ext x
    have hxloc : q (x : M) ∈ Q.localized' T S q :=
      hPQ ⟨x, x.property, 1, by simp⟩
    simpa only [fQ, g₁, g₂, LinearMap.comp_apply, LinearMap.zero_apply,
      map_zero, Submodule.subtype_apply, Submodule.mkQ_apply,
      Submodule.toLocalizedQuotient'_mk] using
        (Submodule.Quotient.mk_eq_zero _).2 hxloc
  obtain ⟨s, hs⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S fQ g₁ g₂ hcomp
  change (s : R) • g₁ = (s : R) • g₂ at hs
  refine ⟨s, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← Submodule.Quotient.mk_eq_zero Q]
  simp only [DistribSMul.toLinearMap_apply]
  rw [Submodule.Quotient.mk_smul]
  simpa only [g₁, g₂, LinearMap.smul_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, LinearMap.zero_apply, smul_zero, Submodule.mkQ_apply] using
      LinearMap.congr_fun hs ⟨x, hx⟩

/-- For a finitely generated submodule, localized inclusion is equivalent to
inclusion after multiplication by one element of the localizing submonoid. -/
theorem localized'_le_iff_exists_smul_le
    (S : Submonoid R) [IsLocalization S T]
    (q : M →ₗ[R] Mloc) [IsLocalizedModule S q]
    {P Q : Submodule R M} (hP : P.FG) :
    P.localized' T S q ≤ Q.localized' T S q ↔
      ∃ s : S, s • P ≤ Q := by
  constructor
  · exact exists_smul_le_of_localized'_le S q hP
  · rintro ⟨s, hs⟩
    exact Submodule.localized'_le_localized'_of_smul_le
      (S := T) (p := S) (f := q) s hs

end AbelFormalization
