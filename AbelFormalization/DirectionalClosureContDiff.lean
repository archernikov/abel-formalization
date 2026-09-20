import AbelFormalization.RestrictedStrictDifferentiability
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

open Set Filter Function
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem DirectionallyClosedOn.contDiffOn_nat
    (B : Subalgebra ℝ (E → ℝ)) (Omega : Set E)
    (basis : Module.Basis κ ℝ E) (j₀ : κ)
    (hclosed : ∀ j, DirectionallyClosedOn B Omega (basis j))
    (hOmega : IsOpen Omega) (n : ℕ) (f : E → ℝ) (hf : f ∈ B) :
    ContDiffOn ℝ n f Omega := by
  induction n generalizing f with
  | zero =>
      apply contDiffOn_zero.mpr
      intro x hx
      obtain ⟨df, hdfmem, hdfderiv⟩ := hclosed j₀ f hf
      exact (hdfderiv x hx).1.continuousAt.continuousWithinAt
  | succ n ih =>
      have hchoice : ∀ j, ∃ df : E → ℝ,
          df ∈ B ∧ HasDirectionalDerivOn Omega (basis j) f df :=
        fun j ↦ hclosed j f hf
      choose df hdfmem hdfderiv using hchoice
      let f' : E → E →L[ℝ] ℝ := fun x ↦
        continuousLinearMapFromBasis basis (fun j ↦ df j x)
      have hf'eq : ∀ x ∈ Omega, f' x = fderiv ℝ f x := by
        intro x hx
        apply ContinuousLinearMap.coe_injective
        apply basis.ext
        intro j
        change continuousLinearMapFromBasis basis (fun k ↦ df k x)
          (basis j) = fderiv ℝ f x (basis j)
        rw [continuousLinearMapFromBasis_apply_basis]
        exact (hdfderiv j x hx).2.symm
      have hf'contDiff : ContDiffOn ℝ n f' Omega := by
        change ContDiffOn ℝ n
          (fun x ↦ ∑ j, df j x • LinearMap.toContinuousLinearMap (basis.coord j)) Omega
        apply ContDiffOn.sum
        intro j hj
        exact (ih (df j) (hdfmem j)).smul contDiffOn_const
      have hhas : ∀ x ∈ Omega, HasFDerivAt f (f' x) x := by
        intro x hx
        rw [hf'eq x hx]
        exact (hdfderiv j₀ x hx).1.hasFDerivAt
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hOmega.uniqueDiffOn]
      refine ⟨by simp, f', hf'contDiff, ?_⟩
      intro x hx
      exact (hhas x hx).hasFDerivWithinAt

theorem DirectionallyClosedOn.contDiffOn_infty
    (B : Subalgebra ℝ (E → ℝ)) (Omega : Set E)
    (basis : Module.Basis κ ℝ E) (j₀ : κ)
    (hclosed : ∀ j, DirectionallyClosedOn B Omega (basis j))
    (hOmega : IsOpen Omega) (f : E → ℝ) (hf : f ∈ B) :
    ContDiffOn ℝ ∞ f Omega := by
  rw [_root_.contDiffOn_infty]
  intro n
  exact DirectionallyClosedOn.contDiffOn_nat
    B Omega basis j₀ hclosed hOmega n f hf

variable {ι : Type*}

theorem IsAbel.contDiffOn_infty_of_mem_restrictedAbelTower_level
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (level : ℕ)
    (basis : Module.Basis κ ℝ (RestrictedSource m p a)) (j₀ : κ)
    {f : RestrictedSource m p a → ℝ} (hf : f ∈ T.level level) :
    ContDiffOn ℝ ∞ f
      (interior (restrictedAbelJetDomain (a := a) D representative offset)) := by
  apply DirectionallyClosedOn.contDiffOn_infty
    (T.level level)
    (interior (restrictedAbelJetDomain (a := a) D representative offset))
    basis j₀
  · intro j g hg
    obtain ⟨dg, hdg, hdir⟩ :=
      hA.restrictedAbelTower_directionallyClosedOn_level
        representative offset T (basis j) level g hg
    exact ⟨dg, hdg, hdir.mono interior_subset⟩
  · exact isOpen_interior
  · exact hf

end AbelFormalization
