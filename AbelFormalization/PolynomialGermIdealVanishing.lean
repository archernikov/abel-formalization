import AbelFormalization.PolynomialGermIdentities
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Ideal membership and actual zeros near an analytic base point

Only finitely many germ identities are used. Their polynomial-valued
representatives agree on one neighborhood before any symbol values are
substituted, so this statement imposes no boundedness restriction on symbols.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace AbelFormalization

variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Fintype κ]

/-- Membership in an ideal with finitely many displayed generators gives
vanishing of any chosen representative at their common zeros, on one
neighborhood and for every assignment of the independent symbols. -/
theorem analyticPolynomial_mem_span_eventually_vanish (x : E)
    (p : κ → MvPolynomial ι (AnalyticGermAt x))
    (f : MvPolynomial ι (AnalyticGermAt x))
    (P : κ → E → MvPolynomial ι ℝ) (F : E → MvPolynomial ι ℝ)
    (hP : ∀ i, analyticPolynomialGermHom x (p i) =
      (P i : Germ (𝓝 x) (MvPolynomial ι ℝ)))
    (hF : analyticPolynomialGermHom x f = (F : Germ (𝓝 x) (MvPolynomial ι ℝ)))
    (hf : f ∈ Ideal.span (Set.range p)) :
    ∀ᶠ w in 𝓝 x, ∀ z : ι → ℝ,
      (∀ i, MvPolynomial.eval z (P i w) = 0) → MvPolynomial.eval z (F w) = 0 := by
  classical
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  obtain ⟨A, U, hUopen, hxU, hsupport, hanalytic, hA⟩ :=
    exists_analyticPolynomialRepresentatives x a
  have hid : f = ∑ i ∈ (Finset.univ : Finset κ), a i * p i := by
    simpa using ha.symm
  have hevent := analyticPolynomialIdentity_eventually x Finset.univ f a p F A P hF
    (fun i _ => hA i) (fun i _ => hP i) hid
  filter_upwards [hevent] with w hw
  intro z hz
  rw [hw, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  simp [hz]

/-- A finite family of ideal members shares one neighborhood of vanishing
at the common zeros of finitely many chosen generator representatives. -/
theorem exists_open_analyticPolynomial_members_vanish {τ : Type*} [Finite τ]
    (x : E) (p : κ → MvPolynomial ι (AnalyticGermAt x))
    (f : τ → MvPolynomial ι (AnalyticGermAt x))
    (P : κ → E → MvPolynomial ι ℝ) (F : τ → E → MvPolynomial ι ℝ)
    (hP : ∀ i, analyticPolynomialGermHom x (p i) =
      (P i : Germ (𝓝 x) (MvPolynomial ι ℝ)))
    (hF : ∀ j, analyticPolynomialGermHom x (f j) =
      (F j : Germ (𝓝 x) (MvPolynomial ι ℝ)))
    (hf : ∀ j, f j ∈ Ideal.span (Set.range p))
    (W₀ : Set E) (hW₀ : IsOpen W₀) (hxW₀ : x ∈ W₀) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ W₀ ∧
      ∀ w ∈ W, ∀ z : ι → ℝ,
        (∀ i, MvPolynomial.eval z (P i w) = 0) →
          ∀ j, MvPolynomial.eval z (F j w) = 0 := by
  have hall : ∀ᶠ w in 𝓝 x, ∀ j, ∀ z : ι → ℝ,
      (∀ i, MvPolynomial.eval z (P i w) = 0) →
        MvPolynomial.eval z (F j w) = 0 :=
    eventually_all.mpr fun j =>
      analyticPolynomial_mem_span_eventually_vanish x p (f j) P (F j) hP (hF j) (hf j)
  have hlocal := hall.and (hW₀.mem_nhds hxW₀)
  obtain ⟨W, hW, hWopen, hxW⟩ := eventually_nhds_iff.mp hlocal
  refine ⟨W, hWopen, hxW, fun w hw => (hW w hw).2, ?_⟩
  intro w hw z hz j
  exact (hW w hw).1 j z hz

omit [Fintype κ] in
/-- A finitely generated ideal of analytic-coefficient polynomials has
finite analytic generator representatives on one common neighborhood. -/
theorem exists_analyticPolynomial_ideal_generators (x : E)
    (I : Ideal (MvPolynomial ι (AnalyticGermAt x))) (hI : I.FG) :
    ∃ c : ℕ, ∃ g : Fin c → MvPolynomial ι (AnalyticGermAt x),
      ∃ G : Fin c → E → MvPolynomial ι ℝ, ∃ W : Set E,
        Ideal.span (Set.range g) = I ∧ IsOpen W ∧ x ∈ W ∧
        (∀ j w, (G j w).support ⊆ (g j).support) ∧
        (∀ j d, AnalyticOnNhd ℝ (fun w => (G j w).coeff d) W) ∧
        ∀ j, analyticPolynomialGermHom x (g j) =
          (G j : Germ (𝓝 x) (MvPolynomial ι ℝ)) := by
  obtain ⟨c, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  obtain ⟨G, W, hWopen, hxW, hsupport, hanalytic, hG⟩ :=
    exists_analyticPolynomialRepresentatives x g
  exact ⟨c, g, G, W, hg, hWopen, hxW, hsupport, hanalytic, hG⟩

end AbelFormalization
