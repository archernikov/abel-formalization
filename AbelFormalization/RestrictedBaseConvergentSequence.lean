import AbelFormalization.RestrictedRegularZeroInduction
import Mathlib.Topology.Sequences

/-!
# Sequential form of restricted base regular-zero finiteness

The outer representative-count argument in the manuscript starts from an
infinite regular-zero set and passes to a sequence whose bounded coordinate
converges in the closed parameter box.  This module proves that reduction
from compactness, so the remaining outer argument can use the normalized
sequence directly.
-/

noncomputable section

open Filter Set Topology

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- Contradiction-shaped version of the level-zero assertion: there is no
injective sequence of regular zeros whose bounded coordinate converges in
the closed parameter box. -/
def RestrictedBaseNoBoxConvergentRegularZeroSequence
    (A : ℝ → ℝ) {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D) : Prop :=
  ∀ {a : ℕ} (R : ℝ)
    (_hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin ((m + p) + a) → RestrictedSource m p a → ℝ),
    (∀ k, F k ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)) →
    ∀ (x : ℕ → RestrictedSource m p a) (w₀ : RestrictedBoxSpace p),
      Function.Injective x →
      (∀ n, x n ∈ regularZeroSet (restrictedBaseOpenDomain D R)
        (constraintMap F)) →
      w₀ ∈ D.closedBox →
      Tendsto (fun n ↦ (x n).1.2) atTop (𝓝 w₀) → False

/-- A restricted base system has finitely many regular zeros exactly when it
admits no injective regular-zero sequence with a convergent bounded-box
coordinate. -/
theorem restrictedBaseRegularZeroFinite_iff_no_boxConvergent_sequence
    {A : ℝ → ℝ} {m p : ℕ} {D : RestrictedBox p}
    {representative : ι → Fin m}
    {offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D} :
    RestrictedBaseRegularZeroFinite A D representative offset ↔
      RestrictedBaseNoBoxConvergentRegularZeroSequence
        A D representative offset := by
  constructor
  · intro hfinite a R hDomain F hF x w₀ hxinj hxmem _ _
    exact (Set.infinite_of_injective_forall_mem hxinj hxmem)
      (hfinite R hDomain F hF)
  · intro hno a R hDomain F hF
    classical
    by_contra hfinite
    have hZ : (regularZeroSet (restrictedBaseOpenDomain D R)
        (constraintMap F)).Infinite := hfinite
    let e : ℕ ↪ (regularZeroSet (restrictedBaseOpenDomain D R)
        (constraintMap F)) := hZ.natEmbedding
    let z : ℕ → RestrictedSource m p a := fun n ↦ (e n : _)
    have hzinj : Function.Injective z := by
      intro i j hij
      exact e.injective (Subtype.ext hij)
    have hzmem : ∀ n, z n ∈ regularZeroSet
        (restrictedBaseOpenDomain D R) (constraintMap F) :=
      fun n ↦ (e n).property
    have hwmem : ∀ n, (z n).1.2 ∈ D.closedBox := fun n ↦
      D.openBox_subset_closedBox (hzmem n).1.2
    obtain ⟨w₀, hw₀, φ, hφ, hlim⟩ :=
      D.isCompact_closedBox.tendsto_subseq hwmem
    exact hno R hDomain F hF (fun n ↦ z (φ n)) w₀
      (hzinj.comp hφ.injective) (fun n ↦ hzmem (φ n)) hw₀
      (by
        change Tendsto ((fun n ↦ (z n).1.2) ∘ φ) atTop (𝓝 w₀)
        exact hlim)

end AbelFormalization
