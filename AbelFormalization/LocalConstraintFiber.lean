import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section

open Set Filter Function
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

variable {X : Type*} [TopologicalSpace X]

theorem mem_connectedComponent_of_mem_preconnected_subset
    {M S : Set X} {x y : X}
    (hxM : x ∈ M) (hyM : y ∈ M)
    (hxS : x ∈ S) (hyS : y ∈ S)
    (hSM : S ⊆ M) (hS : IsPreconnected S) :
    (⟨y, hyM⟩ : M) ∈ connectedComponent (⟨x, hxM⟩ : M) := by
  let T : Set M := ((↑) : M → X) ⁻¹' S
  have hT : IsPreconnected T := by
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    simpa [T, Subtype.image_preimage_coe, inter_eq_right.mpr hSM] using hS
  exact hT.subset_connectedComponent hxS hyS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A surjective strict derivative gives a preconnected local piece of its
level set.  If that local level set lies in `M`, all sufficiently nearby
points of the same level lie in the connected component of the base point
inside `M`. -/
theorem HasStrictFDerivAt.exists_local_level_connectedComponent
    {f : E → F} {f' : E →L[ℝ] F} {a : E} {M : Set E}
    (hf : HasStrictFDerivAt f f' a) (hsurj : f'.range = ⊤)
    (haM : a ∈ M)
    (hlocalLevel : ∃ V ∈ 𝓝 a,
      V ∩ {x | f x = f a} ⊆ M) :
    ∃ U ∈ 𝓝 a, ∀ y ∈ U, f y = f a →
      ∃ hyM : y ∈ M,
        (⟨y, hyM⟩ : M) ∈ connectedComponent (⟨a, haM⟩ : M) := by
  let e : OpenPartialHomeomorph E (F × f'.ker) :=
    hf.implicitToOpenPartialHomeomorph f f' hsurj
  have haSource : a ∈ e.source := hf.mem_implicitToOpenPartialHomeomorph_source hsurj
  have hpTarget : (f a, (0 : f'.ker)) ∈ e.target :=
    hf.mem_implicitToOpenPartialHomeomorph_target hsurj
  have heSelf : e a = (f a, (0 : f'.ker)) := by
    simpa [e] using hf.implicitToOpenPartialHomeomorph_self hsurj
  have hsymmSelf : e.symm (f a, (0 : f'.ker)) = a := by
    rw [← heSelf]
    exact e.left_inv haSource
  obtain ⟨V, hVnhds, hVlevel⟩ := hlocalLevel
  have htargetV : e.target ∩ e.symm ⁻¹' V ∈ 𝓝 (f a, (0 : f'.ker)) := by
    exact inter_mem (e.open_target.mem_nhds hpTarget)
      ((e.continuousAt_symm hpTarget) (by simpa [hsymmSelf] using hVnhds))
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp htargetV
  obtain ⟨ε, hε, hballv⟩ := Metric.mem_nhds_iff.mp hv
  let S : Set (F × f'.ker) := {f a} ×ˢ Metric.ball 0 ε
  have hSpre : IsPreconnected S := by
    exact isPreconnected_singleton.prod Metric.isPreconnected_ball
  have hStargetV : S ⊆ e.target ∩ e.symm ⁻¹' V := by
    intro p hp
    have hpu : p.1 ∈ u := by
      rw [hp.1]
      exact mem_of_mem_nhds hu
    have hpv : p.2 ∈ v := hballv hp.2
    exact huv ⟨hpu, hpv⟩
  have hStarget : S ⊆ e.target := fun p hp ↦ (hStargetV hp).1
  let P : Set E := e.symm '' S
  have hPpre : IsPreconnected P := by
    exact hSpre.image e.symm (e.continuousOn_symm.mono hStarget)
  have haP : a ∈ P := by
    refine ⟨(f a, (0 : f'.ker)), ?_, ?_⟩
    · exact ⟨rfl, Metric.mem_ball_self hε⟩
    · exact hsymmSelf
  have hPM : P ⊆ M := by
    intro y hy
    obtain ⟨p, hpS, rfl⟩ := hy
    have hpTV := hStargetV hpS
    apply hVlevel
    constructor
    · exact hpTV.2
    · change f (e.symm p) = f a
      have hright : e (e.symm p) = p := e.right_inv hpTV.1
      have hfirst := congrArg Prod.fst hright
      have hfirst' : f (e.symm p) = p.1 := by simpa [e] using hfirst
      have hpfirst : p.1 = f a := by simpa [S] using hpS.1
      exact hfirst'.trans hpfirst
  let U : Set E := e.source ∩ e ⁻¹' (Set.univ ×ˢ Metric.ball 0 ε)
  have hUnhds : U ∈ 𝓝 a := by
    apply inter_mem (e.open_source.mem_nhds haSource)
    apply e.continuousAt haSource
    rw [heSelf]
    rw [prod_mem_nhds_iff]
    exact ⟨univ_mem, Metric.ball_mem_nhds _ hε⟩
  refine ⟨U, hUnhds, ?_⟩
  intro y hyU hyLevel
  have hyP : y ∈ P := by
    refine ⟨e y, ?_, e.left_inv hyU.1⟩
    exact ⟨by simpa [e] using hyLevel, hyU.2.2⟩
  have hyM : y ∈ M := hPM hyP
  exact ⟨hyM,
    mem_connectedComponent_of_mem_preconnected_subset
      haM hyM haP hyP hPM hPpre⟩

end AbelFormalization
