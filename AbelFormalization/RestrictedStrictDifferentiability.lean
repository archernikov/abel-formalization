import AbelFormalization.RestrictedAdjunctionClosedness
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Dual.Basis

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Reassemble a continuous linear functional from its values on a finite
basis. -/
def continuousLinearMapFromBasis (basis : Module.Basis κ ℝ E)
    (v : κ → ℝ) : E →L[ℝ] ℝ :=
  ∑ j, v j • LinearMap.toContinuousLinearMap (basis.coord j)

@[simp]
theorem continuousLinearMapFromBasis_apply_basis
    (basis : Module.Basis κ ℝ E) (v : κ → ℝ) (j : κ) :
    continuousLinearMapFromBasis basis v (basis j) = v j := by
  simp [continuousLinearMapFromBasis, Finsupp.single_apply]

theorem hasStrictFDerivAt_of_eventually_directionalDerivatives
    (basis : Module.Basis κ ℝ E) (f : E → ℝ)
    (df : κ → E → ℝ) (x : E)
    (hderiv : ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ f y ∧
        ∀ j, df j y = fderiv ℝ f y (basis j))
    (hcont : ∀ j, ContinuousAt (df j) x) :
    HasStrictFDerivAt f (fderiv ℝ f x) x := by
  let f' : E → E →L[ℝ] ℝ := fun y ↦
    continuousLinearMapFromBasis basis (fun j ↦ df j y)
  have hf'eq : ∀ᶠ y in 𝓝 x, f' y = fderiv ℝ f y := by
    filter_upwards [hderiv] with y hy
    apply ContinuousLinearMap.coe_injective
    apply basis.ext
    intro j
    change continuousLinearMapFromBasis basis (fun k ↦ df k y)
      (basis j) = fderiv ℝ f y (basis j)
    rw [continuousLinearMapFromBasis_apply_basis]
    exact hy.2 j
  have hhas : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y := by
    filter_upwards [hderiv, hf'eq] with y hy hyeq
    rw [hyeq]
    exact hy.1.hasFDerivAt
  have hf'cont : ContinuousAt f' x := by
    change ContinuousAt (fun y ↦
      ∑ j, df j y • LinearMap.toContinuousLinearMap (basis.coord j)) x
    exact tendsto_finsetSum Finset.univ fun j _ ↦
      (hcont j).smul continuousAt_const
  have hstrict :=
    hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt hhas hf'cont
  have hxeq : f' x = fderiv ℝ f x := hf'eq.self_of_nhds
  rwa [hxeq] at hstrict

/-- Directional closure along a finite basis, applied twice, supplies a
continuous full derivative and hence strict differentiability. -/
theorem DirectionallyClosedOn.hasStrictFDerivAt_of_mem_of_isOpen
    (B : Subalgebra ℝ (E → ℝ)) (Omega : Set E)
    (basis : Module.Basis κ ℝ E) (j₀ : κ)
    (hclosed : ∀ j, DirectionallyClosedOn B Omega (basis j))
    (hOmega : IsOpen Omega) (f : E → ℝ) (hf : f ∈ B)
    {x : E} (hx : x ∈ Omega) :
    HasStrictFDerivAt f (fderiv ℝ f x) x := by
  have hchoice : ∀ j, ∃ df : E → ℝ,
      df ∈ B ∧ HasDirectionalDerivOn Omega (basis j) f df :=
    fun j ↦ hclosed j f hf
  choose df hdfmem hdfderiv using hchoice
  have heventually : ∀ᶠ y in 𝓝 x,
      DifferentiableAt ℝ f y ∧
        ∀ j, df j y = fderiv ℝ f y (basis j) := by
    filter_upwards [hOmega.mem_nhds hx] with y hy
    exact ⟨(hdfderiv j₀ y hy).1, fun j ↦ (hdfderiv j y hy).2.symm⟩
  have hcont : ∀ j, ContinuousAt (df j) x := by
    intro j
    obtain ⟨ddf, hddfmem, hddfderiv⟩ := hclosed j₀ (df j) (hdfmem j)
    exact (hddfderiv x hx).1.continuousAt
  exact hasStrictFDerivAt_of_eventually_directionalDerivatives
    basis f df x heventually hcont

theorem IsAbel.hasStrictFDerivAt_of_mem_restrictedAbelTower_level_of_mem_interior
    {A : ℝ → ℝ} (hA : IsAbel A)
    {ι : Type*} {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (level : ℕ)
    (basis : Module.Basis κ ℝ (RestrictedSource m p a)) (j₀ : κ)
    {f : RestrictedSource m p a → ℝ} (hf : f ∈ T.level level)
    {x : RestrictedSource m p a}
    (hx : x ∈ interior
      (restrictedAbelJetDomain (a := a) D representative offset)) :
    HasStrictFDerivAt f (fderiv ℝ f x) x := by
  apply DirectionallyClosedOn.hasStrictFDerivAt_of_mem_of_isOpen
    (T.level level)
      (interior (restrictedAbelJetDomain (a := a) D representative offset))
      basis j₀
  · intro j
    intro g hg
    obtain ⟨dg, hdg, hdir⟩ :=
      hA.restrictedAbelTower_directionallyClosedOn_level
        representative offset T (basis j) level g hg
    exact ⟨dg, hdg, hdir.mono interior_subset⟩
  · exact isOpen_interior
  · exact hf
  · exact hx

theorem isOpen_restrictedBaseOpenDomain {m p a : ℕ}
    (D : RestrictedBox p) (R : ℝ) :
    IsOpen (restrictedBaseOpenDomain (m := m) (a := a) D R) := by
  have hs : IsOpen {x : RestrictedSource m p a | ∀ i, R < x.1.1 i} := by
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt continuous_const
      ((continuous_apply i).comp (continuous_fst.comp continuous_fst))
  have hw : IsOpen {x : RestrictedSource m p a | x.1.2 ∈ D.openBox} :=
    D.isOpen_openBox.preimage (continuous_snd.comp continuous_fst)
  exact hs.inter hw

theorem restrictedBaseOpenDomain_subset_interior_AbelJetDomain
    {ι : Type*} {m p a : ℕ} (D : RestrictedBox p) (R : ℝ)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset) :
    restrictedBaseOpenDomain (m := m) (a := a) D R ⊆
      interior (restrictedAbelJetDomain (a := a) D representative offset) := by
  have hsub : restrictedBaseOpenDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset :=
    (restrictedBaseOpenDomain_subset_closedDomain D R).trans hDomain
  intro x hx
  apply interior_mono hsub
  rwa [(isOpen_restrictedBaseOpenDomain D R).interior_eq]

theorem restrictedExponentialAdjunctionClosedCurve_mem_baseOpenDomain
    {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    {x : RestrictedSource m p ((a + 1) + 1)}
    (hx : x ∈ restrictedExponentialAdjunctionClosedCurve H D R J) :
    x ∈ restrictedBaseOpenDomain (m := m) (a := (a + 1) + 1) D R := by
  have hdrop := restrictedExponentialAdjunctionClosedCurve_drop_mem
    H D R J hx
  have hb := (mem_restrictedExponentialAdjunctionCurve_iff
    H D R J (restrictedSourceDropAux 1 x)).mp hdrop
  exact ⟨hb.2.1.1, hb.2.1.2.1⟩

theorem restrictedExponentialAdjunctionClosedCurve_mem_interior_AbelJetDomain
    {ι : Type*} {m p a r : ℕ}
    (H : Fin r → RestrictedSource m p (a + 1) → ℝ)
    (D : RestrictedBox p) (R : ℝ)
    (J : RestrictedSource m p (a + 1) → ℝ)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (hDomain : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset)
    {x : RestrictedSource m p ((a + 1) + 1)}
    (hx : x ∈ restrictedExponentialAdjunctionClosedCurve H D R J) :
    x ∈ interior (restrictedAbelJetDomain (a := (a + 1) + 1)
      D representative offset) := by
  exact restrictedBaseOpenDomain_subset_interior_AbelJetDomain
    D R representative offset hDomain
      (restrictedExponentialAdjunctionClosedCurve_mem_baseOpenDomain
        H D R J hx)

end AbelFormalization
