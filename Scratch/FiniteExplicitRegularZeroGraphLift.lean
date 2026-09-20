import AbelFormalization.FiniteImplicitRegularZeroGraphLift

/-!
# Explicit finite vector graph lifts

This specializes the finite implicit graph theorem to the equations
`z - zeta(x) = 0`, whose vertical derivative is the identity.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Equations of an explicit vector-valued graph. -/
def finiteExplicitGraphEquation (zeta : E → G) : E × G → G :=
  fun p ↦ p.2 - zeta p.1

/-- A square lift combining an ambient equation map with an explicit finite
graph equation. -/
def finiteExplicitGraphLiftSystem (Ftilde : E × G → F) (zeta : E → G) :
    E × G → F × G :=
  finiteImplicitGraphLiftSystem Ftilde (finiteExplicitGraphEquation zeta)

/-- The vertical derivative block of an explicit graph equation is the
identity and hence surjective. -/
theorem surjective_finiteGraphLiftZBlock_fderiv_finiteExplicitGraphEquation
    {zeta : E → G} {x : E} (hzeta : DifferentiableAt ℝ zeta x) :
    Function.Surjective
      (finiteGraphLiftZBlock
        (fderiv ℝ (finiteExplicitGraphEquation zeta) (x, zeta x))) := by
  let fstL : (E × G) →L[ℝ] E := ContinuousLinearMap.fst ℝ E G
  let sndL : (E × G) →L[ℝ] G := ContinuousLinearMap.snd ℝ E G
  have hfst : HasFDerivAt (fun p : E × G ↦ p.1) fstL (x, zeta x) :=
    fstL.hasFDerivAt
  have hsnd : HasFDerivAt (fun p : E × G ↦ p.2) sndL (x, zeta x) :=
    sndL.hasFDerivAt
  have hzcomp : HasFDerivAt (fun p : E × G ↦ zeta p.1)
      ((fderiv ℝ zeta x).comp fstL) (x, zeta x) :=
    hzeta.hasFDerivAt.comp (x, zeta x) hfst
  have hgraph : HasFDerivAt (finiteExplicitGraphEquation zeta)
      (sndL - (fderiv ℝ zeta x).comp fstL) (x, zeta x) :=
    hsnd.sub hzcomp
  rw [hgraph.fderiv]
  intro y
  refine ⟨y, ?_⟩
  change (sndL - (fderiv ℝ zeta x).comp fstL) (0, y) = y
  simp [fstL, sndL]

/-- Simultaneously adjoining explicit finite graph equations preserves
regular-zero membership. -/
theorem mem_regularZeroSet_finiteExplicitGraphLift_iff
    [FiniteDimensional ℝ G]
    {Omega : Set E} {Ftilde : E × G → F}
    {zeta : E → G} {x : E}
    (hF : DifferentiableAt ℝ Ftilde (x, zeta x))
    (hzeta : DifferentiableAt ℝ zeta x) :
    x ∈ regularZeroSet Omega (finiteGraphSubstitution Ftilde zeta) ↔
      (x, zeta x) ∈ regularZeroSet
        ((fun p : E × G ↦ p.1) ⁻¹' Omega)
        (finiteExplicitGraphLiftSystem Ftilde zeta) := by
  apply mem_regularZeroSet_finiteImplicitGraphLift_iff hF
  · exact differentiableAt_snd.sub
      (hzeta.comp (x, zeta x) differentiableAt_fst)
  · exact hzeta
  · exact Filter.Eventually.of_forall fun y ↦ by
      simp [finiteExplicitGraphEquation]
  · exact surjective_finiteGraphLiftZBlock_fderiv_finiteExplicitGraphEquation
      hzeta

end AbelFormalization
