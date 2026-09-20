import AbelFormalization.MaxwellCompactInjectiveSelectorContinuity
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smoothness of a continuous selector on a regular implicit branch

The compact injective-graph argument supplies continuity of the selected
witness.  If the graph also lies in a smooth square implicit system whose
hidden derivative is invertible, continuity keeps the selected points inside
the local uniqueness neighborhood of the implicit-function theorem.  Hence
the chosen selector agrees locally with the smooth implicit function and is
differentiable.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace AbelFormalization

set_option autoImplicit false

/-- A continuous solution of a regular square implicit equation agrees
locally with mathlib's implicit function and is differentiable at the base
point. -/
theorem differentiableAt_of_continuousAt_of_regular_implicitEquation
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Phi : ℝ × E → E) (phi : ℝ → E) (t : ℝ)
    (hPhi : ContDiffAt ℝ 1 Phi (t, phi t))
    (hvertical :
      (fderiv ℝ Phi (t, phi t) ∘L
        ContinuousLinearMap.inr ℝ ℝ E).IsInvertible)
    (hphiContinuous : ContinuousAt phi t)
    (hEquation :
      ∀ᶠ s in 𝓝 t, Phi (s, phi s) = Phi (t, phi t)) :
    DifferentiableAt ℝ phi t := by
  let psi : ℝ → E := hPhi.implicitFunction (by norm_num) hvertical
  have hpsiDifferentiable : DifferentiableAt ℝ psi t :=
    (hPhi.contDiffAt_implicitFunction (by norm_num) hvertical).differentiableAt
      (by norm_num)
  have hlocal :=
    hPhi.eventually_apply_eq_iff_implicitFunction (by norm_num) hvertical
  have hpulled :=
    (continuousAt_id.prodMk hphiContinuous).tendsto.eventually hlocal
  have hphiEq : phi =ᶠ[𝓝 t] psi := by
    filter_upwards [hpulled, hEquation] with s hs hEq
    exact (hs.mp hEq).symm
  exact hpsiDifferentiable.congr_of_eventuallyEq hphiEq

/-- A selected graph in a compact injective relation is differentiable at
every point where it is cut out by a regular smooth square system. -/
theorem differentiableAt_selectedWitness_of_compact_injective_of_regularImplicit
    {n : ℕ} {P : Set (RealEuclidean (1 + n))}
    (hPcompact : IsCompact P)
    (hinjective : Set.InjOn realEuclideanTakeLeft P)
    {U : Set ℝ} (hUopen : IsOpen U)
    {phi : ℝ → RealEuclidean n}
    (hgraphSubset : wilkie28SelectedWitnessGraph U phi ⊆ P)
    (Phi : ℝ × RealEuclidean n → RealEuclidean n)
    (hPhi : ContDiff ℝ 1 Phi)
    (hPhiGraph : ∀ t ∈ U, Phi (t, phi t) = 0)
    (hvertical : ∀ t ∈ U,
      (fderiv ℝ Phi (t, phi t) ∘L
        ContinuousLinearMap.inr ℝ ℝ (RealEuclidean n)).IsInvertible)
    {t : ℝ} (ht : t ∈ U) :
    DifferentiableAt ℝ phi t := by
  have hphiContinuousOn : ContinuousOn phi U :=
    continuousOn_of_selectedWitnessGraph_subset_compact_injective
      hPcompact hinjective hgraphSubset
  have hphiContinuousAt : ContinuousAt phi t :=
    (hphiContinuousOn t ht).continuousAt (hUopen.mem_nhds ht)
  apply differentiableAt_of_continuousAt_of_regular_implicitEquation
    Phi phi t hPhi.contDiffAt (hvertical t ht) hphiContinuousAt
  filter_upwards [hUopen.mem_nhds ht] with s hs
  rw [hPhiGraph s hs, hPhiGraph t ht]

/-- Pointwise version on the whole selected domain. -/
theorem differentiableOn_selectedWitness_of_compact_injective_of_regularImplicit
    {n : ℕ} {P : Set (RealEuclidean (1 + n))}
    (hPcompact : IsCompact P)
    (hinjective : Set.InjOn realEuclideanTakeLeft P)
    {U : Set ℝ} (hUopen : IsOpen U)
    {phi : ℝ → RealEuclidean n}
    (hgraphSubset : wilkie28SelectedWitnessGraph U phi ⊆ P)
    (Phi : ℝ × RealEuclidean n → RealEuclidean n)
    (hPhi : ContDiff ℝ 1 Phi)
    (hPhiGraph : ∀ t ∈ U, Phi (t, phi t) = 0)
    (hvertical : ∀ t ∈ U,
      (fderiv ℝ Phi (t, phi t) ∘L
        ContinuousLinearMap.inr ℝ ℝ (RealEuclidean n)).IsInvertible) :
    ∀ t ∈ U, DifferentiableAt ℝ phi t := by
  intro t ht
  exact differentiableAt_selectedWitness_of_compact_injective_of_regularImplicit
    hPcompact hinjective hUopen hgraphSubset Phi hPhi hPhiGraph hvertical ht

end AbelFormalization
