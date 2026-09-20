import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The algebraic step from convergent division to Noetherianity

For each nonzero ideal it suffices to find a member whose principal quotient
is Noetherian. Convergent division will supply such quotients as finite modules
over a lower-dimensional analytic-germ ring. This module proves the abstract
algebraic implication; it does not assert that the analytic input is complete.
-/

namespace AbelFormalization

variable {R : Type*} [CommRing R]

/-- Finite generation lifts from the quotient by one member of the ideal. -/
theorem ideal_fg_of_principal_quotient_noetherian (I : Ideal R) (f : R) (hf : f ∈ I)
    [IsNoetherianRing (R ⧸ Ideal.span {f})] : I.FG := by
  apply Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective
    (f := Ideal.Quotient.mk (Ideal.span {f}))
  · exact Ideal.fg_of_isNoetherianRing _
  · rw [Ideal.mk_ker, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem I).mpr hf)]
    exact Submodule.fg_span_singleton f
  · exact Ideal.Quotient.mk_surjective

/-- One Noetherian principal quotient for each nonzero ideal suffices. -/
theorem isNoetherianRing_of_ideal_principal_quotients
    (h : ∀ I : Ideal R, I ≠ ⊥ → ∃ f ∈ I, IsNoetherianRing (R ⧸ Ideal.span {f})) :
    IsNoetherianRing R := by
  apply (isNoetherianRing_iff_ideal_fg R).mpr
  intro I
  by_cases hI : I = ⊥
  · exact hI ▸ Submodule.fg_bot
  obtain ⟨f, hf, hQ⟩ := h I hI
  let := hQ
  exact ideal_fg_of_principal_quotient_noetherian I f hf

/-- In particular it suffices to prove Noetherianity of all quotients by a
nonzero element. No domain hypothesis is needed for this implication. -/
theorem isNoetherianRing_of_nonzero_principal_quotients
    (h : ∀ f : R, f ≠ 0 → IsNoetherianRing (R ⧸ Ideal.span {f})) :
    IsNoetherianRing R := by
  apply isNoetherianRing_of_ideal_principal_quotients
  intro I hI
  obtain ⟨f, hf, hfn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact ⟨f, hf, h f hfn⟩

section FiniteQuotient

variable {A : Type*} [CommRing A] [Algebra R A]

/-- A division identity with uniformly bounded remainder degree makes the
principal quotient a finite module over the coefficient ring. -/
theorem moduleFinite_principal_quotient_of_division (f t : A) (n : ℕ)
    (hdivision : ∀ g : A, ∃ q : A, ∃ c : Fin n → R,
      g = f * q + ∑ k, c k • t ^ (k : ℕ)) :
    Module.Finite R (A ⧸ Ideal.span {f}) := by
  classical
  let π : A →ₐ[R] A ⧸ Ideal.span {f} := Ideal.Quotient.mkₐ R (Ideal.span {f})
  let b : Fin n → A ⧸ Ideal.span {f} := fun k => π (t ^ (k : ℕ))
  have hzero : π f = 0 := Ideal.Quotient.mk_singleton_self f
  have hspan : Submodule.span R (Set.range b) = ⊤ := by
    apply eq_top_iff.mpr
    apply (Submodule.top_le_span_range_iff_forall_exists_fun R).mpr
    intro x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, c, hg⟩ := hdivision g
    refine ⟨c, ?_⟩
    change (∑ k, c k • π (t ^ (k : ℕ))) = π g
    rw [hg, map_add, map_mul, hzero, zero_mul, zero_add, map_sum]
    simp only [map_smul]
  exact Module.Finite.of_fg_top
    (Submodule.fg_iff_exists_fin_generating_family.mpr ⟨n, b, hspan⟩)

/-- Division over a Noetherian coefficient ring gives a Noetherian principal
quotient. The convergence and division hypotheses must be proved separately. -/
theorem isNoetherianRing_principal_quotient_of_division [IsNoetherianRing R]
    (f t : A) (n : ℕ)
    (hdivision : ∀ g : A, ∃ q : A, ∃ c : Fin n → R,
      g = f * q + ∑ k, c k • t ^ (k : ℕ)) :
    IsNoetherianRing (A ⧸ Ideal.span {f}) := by
  let := moduleFinite_principal_quotient_of_division f t n hdivision
  exact IsNoetherianRing.of_finite R (A ⧸ Ideal.span {f})

end FiniteQuotient

end AbelFormalization
