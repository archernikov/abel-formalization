import AbelFormalization.CharbonnelWeakStructure
import AbelFormalization.Wilkie28ExceptionalMathlibOnly

/-!
# Source-only Wilkie 2.8 witness-selection composition

Wilkie's weak selection theorem (2.3) first gives a weak-family graph of
singular witnesses on a nonempty open set. His almost-everywhere smoothness
theorem (2.4), used as in remark 2.5, gives a closed empty-interior bad set
outside which that graph's function is `C¹`. The topological composition below
is independent of the missing general theorems.

This is an uncompiled draft. It does not assert weak selection or smoothness,
and no axiom or `sorry` is introduced. The hypotheses of the final theorem are
the exact two interfaces still to be formalized for the maintained family.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The graph of a witness curve, embedded in the Euclidean family arity
`1 + n`. The first coordinate records the singular parameter. -/
def wilkie28SelectedWitnessGraph {n : ℕ}
    (U : Set ℝ) (φ : ℝ → RealEuclidean n) :
    Set (RealEuclidean (1 + n)) :=
  {z | ∃ t ∈ U,
    z = realEuclideanAppend (fun _ : Fin 1 ↦ t) (φ t)}

/-- A result of Wilkie 2.3 for the singular-witness incidence relation.
Family membership of the selected graph is retained so that 2.4 applies. -/
structure Wilkie28WeakSelectedWitness
    (C : EuclideanSetFamily) {n k : ℕ}
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclidean n → ℝ) (a : RealEuclidean k) where
  U : Set ℝ
  φ : ℝ → RealEuclidean n
  U_open : IsOpen U
  U_nonempty : U.Nonempty
  graph_mem : wilkie28SelectedWitnessGraph U φ ∈ C (1 + n)
  F_eq : ∀ t ∈ U, F (φ t) = a
  f_eq : ∀ t ∈ U, f (φ t) = t
  singular : ∀ t ∈ U,
    ¬ Function.Surjective
      (fun v : RealEuclidean n ↦
        (fderiv ℝ F (φ t) v, fderiv ℝ f (φ t) v))

/-- A closed empty-interior exceptional set leaves a nonempty open smooth
patch inside every nonempty open domain. This is the elementary last step of
Wilkie's remark 2.5. -/
theorem exists_nonempty_open_differentiable_patch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U A : Set ℝ} (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (hAclosed : IsClosed A) (hAempty : interior A = ∅)
    (φ : ℝ → E)
    (hφdiff : ∀ t ∈ U \ A, DifferentiableAt ℝ φ t) :
    ∃ V : Set ℝ,
      IsOpen V ∧ V.Nonempty ∧ V ⊆ U ∧
        ∀ t ∈ V, DifferentiableAt ℝ φ t := by
  have hUnotSubset : ¬ U ⊆ A := by
    intro hsubset
    have hUint : U ⊆ interior A :=
      hUopen.subset_interior_iff.mpr hsubset
    obtain ⟨t, ht⟩ := hUnonempty
    have htA : t ∈ interior A := hUint ht
    simpa [hAempty] using htA
  obtain ⟨t, htU, htA⟩ := Set.not_subset.mp hUnotSubset
  refine ⟨U \ A, hUopen.sdiff hAclosed, ⟨t, htU, htA⟩,
    Set.diff_subset, ?_⟩
  intro s hs
  exact hφdiff s hs

/-- The precise composition of source theorems 2.3 and 2.4 into the
`SmoothSingularWitnessSelection` input of the maintained Wilkie 2.8
differential contradiction. -/
theorem wilkie28_smoothSingularWitnessSelection_of_weakSelection_and_aeSmooth
    (C : EuclideanSetFamily) {n k : ℕ}
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclidean n → ℝ) (a : RealEuclidean k)
    (hweak :
      (interior (Wilkie28MathlibOnly.exceptionalParameterSet F f a)).Nonempty →
        Nonempty (Wilkie28WeakSelectedWitness C F f a))
    (haeSmooth :
      ∀ s : Wilkie28WeakSelectedWitness C F f a,
        ∃ A : Set ℝ,
          IsClosed A ∧ interior A = ∅ ∧
            (∀ t ∈ s.U \ A, DifferentiableAt ℝ s.φ t)) :
    Wilkie28MathlibOnly.SmoothSingularWitnessSelection F f a := by
  intro hI
  obtain ⟨s⟩ := hweak hI
  obtain ⟨A, hAclosed, hAempty, hφdiff⟩ := haeSmooth s
  obtain ⟨V, hVopen, hVnonempty, hVsubset, hVdiff⟩ :=
    exists_nonempty_open_differentiable_patch
      s.U_open s.U_nonempty hAclosed hAempty s.φ hφdiff
  refine ⟨V, s.φ, hVopen, hVnonempty, ?_, ?_, ?_, hVdiff⟩
  · intro t ht
    exact s.F_eq t (hVsubset ht)
  · intro t ht
    exact s.f_eq t (hVsubset ht)
  · intro t ht
    exact s.singular t (hVsubset ht)

end AbelFormalization
