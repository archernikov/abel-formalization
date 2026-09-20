import AbelFormalization.Wilkie28WeakSelectionCompactExtraction

/-!
# Maxwell almost-everywhere smoothness interface

Wilkie's source theorem 2.4 applies to a function whose open domain and graph
belong to the weak family.  It removes a closed family member with empty
interior and obtains arbitrary finite differentiability order on the
complement.

This module records that family-level statement and proves the coordinate
adapter needed by the one-parameter selector in theorem 2.8.  In particular,
membership of the selector's domain is not an extra assumption: it follows by
projecting its graph in the Charbonnel closure.
-/

noncomputable section

open Set
open scoped ContDiff

namespace AbelFormalization

set_option autoImplicit false

/-- The graph of a function between finite Euclidean coordinate spaces. -/
def maxwellFunctionGraph {p q : ℕ}
    (U : Set (RealEuclidean p))
    (Phi : RealEuclidean p → RealEuclidean q) :
    Set (RealEuclidean (p + q)) :=
  {z | ∃ x ∈ U, z = realEuclideanAppend x (Phi x)}

/-- Projecting a function graph onto its visible coordinates recovers its
domain. -/
theorem realEuclideanExistentialProjection_maxwellFunctionGraph
    {p q : ℕ} (U : Set (RealEuclidean p))
    (Phi : RealEuclidean p → RealEuclidean q) :
    realEuclideanExistentialProjection (maxwellFunctionGraph U Phi) = U := by
  ext x
  constructor
  · rintro ⟨y, x', hx', hxy⟩
    have hxx' : x = x' := by
      simpa only [realEuclideanTakeLeft_append] using
        congrArg realEuclideanTakeLeft hxy
    simpa only [hxx'] using hx'
  · intro hx
    exact ⟨Phi x, x, hx, rfl⟩

/-- Pull a real one-parameter domain back to the unique coordinate of
Euclidean one-space. -/
def maxwellScalarDomainLift (U : Set ℝ) : Set (RealEuclidean 1) :=
  {x | x 0 ∈ U}

/-- Regard a real one-parameter map as a map on Euclidean one-space. -/
def maxwellScalarFunctionLift {n : ℕ}
    (phi : ℝ → RealEuclidean n) :
    RealEuclidean 1 → RealEuclidean n :=
  fun x ↦ phi (x 0)

/-- The generic Euclidean graph of the lifted selector is the selected
witness graph used by the Wilkie 2.8 development. -/
theorem maxwellFunctionGraph_scalarLift_eq_selectedWitnessGraph
    {n : ℕ} (U : Set ℝ) (phi : ℝ → RealEuclidean n) :
    maxwellFunctionGraph
        (maxwellScalarDomainLift U) (maxwellScalarFunctionLift phi) =
      wilkie28SelectedWitnessGraph U phi := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x 0, hx, ?_⟩
    congr 1
    funext i
    exact Fin.eq_zero i ▸ rfl
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(fun _ : Fin 1 ↦ t), ht, rfl⟩

/-- The selected witness graph projects to the lifted scalar domain. -/
theorem realEuclideanExistentialProjection_selectedWitnessGraph
    {n : ℕ} (U : Set ℝ) (phi : ℝ → RealEuclidean n) :
    realEuclideanExistentialProjection
        (wilkie28SelectedWitnessGraph U phi) =
      maxwellScalarDomainLift U := by
  rw [← maxwellFunctionGraph_scalarLift_eq_selectedWitnessGraph]
  exact realEuclideanExistentialProjection_maxwellFunctionGraph _ _

/-- A weak selected witness in the Charbonnel closure automatically has a
family-member one-dimensional domain after the scalar coordinate lift. -/
theorem Wilkie28WeakSelectedWitness.scalarDomainLift_mem
    {S : EuclideanSetFamily} {n k : ℕ}
    {F : RealEuclidean n → RealEuclidean k}
    {f : RealEuclidean n → ℝ} {a : RealEuclidean k}
    (s : Wilkie28WeakSelectedWitness (charbonnelClosure S) F f a) :
    maxwellScalarDomainLift s.U ∈ charbonnelClosure S 1 := by
  rw [← realEuclideanExistentialProjection_selectedWitnessGraph]
  exact charbonnelClosure_projection (by omega) s.graph_mem

/-- Source-shaped family-level form of Maxwell's theorem 2.4.  For every
finite differentiability order, an open family-member function graph is
smooth away from a closed family-member exceptional set with empty
interior. -/
def MaxwellAlmostEverywhereSmoothness
    (C : EuclideanSetFamily) : Prop :=
  ∀ (N : ℕ) {p q : ℕ}, 0 < p → 0 < q →
    ∀ (U : Set (RealEuclidean p))
      (Phi : RealEuclidean p → RealEuclidean q),
      IsOpen U →
      U ∈ C p →
      maxwellFunctionGraph U Phi ∈ C (p + q) →
      ∃ A : Set (RealEuclidean p),
        IsClosed A ∧ A ∈ C p ∧ interior A = ∅ ∧
          ContDiffOn ℝ N Phi (U \ A)

/-- Maxwell's family-level theorem 2.4 implies the exact scalar
almost-everywhere differentiability interface used after weak selection.
The exceptional set is transported through the canonical equivalence
between Euclidean one-space and the reals. -/
theorem wilkie28_aeSmooth_of_MaxwellAlmostEverywhereSmoothness
    {S : EuclideanSetFamily} {n k : ℕ}
    {F : RealEuclidean n → RealEuclidean k}
    {f : RealEuclidean n → ℝ} {a : RealEuclidean k}
    (hMaxwell :
      MaxwellAlmostEverywhereSmoothness (charbonnelClosure S))
    (hn : 0 < n)
    (s : Wilkie28WeakSelectedWitness (charbonnelClosure S) F f a) :
    ∃ A : Set ℝ,
      IsClosed A ∧ interior A = ∅ ∧
        ∀ t ∈ s.U \ A, DifferentiableAt ℝ s.φ t := by
  let U₁ := maxwellScalarDomainLift s.U
  let Phi := maxwellScalarFunctionLift s.φ
  have hU₁open : IsOpen U₁ := by
    exact s.U_open.preimage (continuous_apply 0)
  have hU₁mem : U₁ ∈ charbonnelClosure S 1 :=
    s.scalarDomainLift_mem
  have hgraphMem :
      maxwellFunctionGraph U₁ Phi ∈ charbonnelClosure S (1 + n) := by
    rw [maxwellFunctionGraph_scalarLift_eq_selectedWitnessGraph]
    exact s.graph_mem
  obtain ⟨A₁, hA₁closed, _hA₁mem, hA₁empty, hPhiSmooth⟩ :=
    hMaxwell 1 (by omega) hn U₁ Phi hU₁open hU₁mem hgraphMem
  let E := realEuclideanOneEquivReal
  refine ⟨E '' A₁, ?_, ?_, ?_⟩
  · exact E.toHomeomorph.isClosedMap A₁ hA₁closed
  · change interior (E.toHomeomorph '' A₁) = ∅
    rw [← E.toHomeomorph.image_interior]
    simp only [hA₁empty, image_empty]
  · intro t ht
    have hxU : E.symm t ∈ U₁ := by
      change (E.symm t) 0 ∈ s.U
      simpa [E, realEuclideanOneEquivReal] using ht.1
    have hxA : E.symm t ∉ A₁ := by
      intro hx
      apply ht.2
      exact ⟨E.symm t, hx, E.apply_symm_apply t⟩
    have hPhiAt : ContDiffAt ℝ 1 Phi (E.symm t) :=
      hPhiSmooth.contDiffAt
        ((hU₁open.sdiff hA₁closed).mem_nhds ⟨hxU, hxA⟩)
    have hcomp :
        DifferentiableAt ℝ (Phi ∘ fun u : ℝ ↦ E.symm u) t :=
      (hPhiAt.differentiableAt (by norm_num)).comp
        t E.symm.differentiableAt
    simpa [Phi, maxwellScalarFunctionLift, E,
      realEuclideanOneEquivReal, Function.comp_def] using hcomp

/-- Combining weak selection with the source-shaped Maxwell theorem 2.4
produces the smooth singular-witness selection needed by Wilkie 2.8. -/
theorem wilkie28_smoothSingularWitnessSelection_of_weakSelection_and_Maxwell
    {S : EuclideanSetFamily} {n k : ℕ}
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclidean n → ℝ) (a : RealEuclidean k)
    (hweak :
      (interior (Wilkie28MathlibOnly.exceptionalParameterSet F f a)).Nonempty →
        Nonempty
          (Wilkie28WeakSelectedWitness (charbonnelClosure S) F f a))
    (hMaxwell :
      MaxwellAlmostEverywhereSmoothness (charbonnelClosure S))
    (hn : 0 < n) :
    Wilkie28MathlibOnly.SmoothSingularWitnessSelection F f a :=
  wilkie28_smoothSingularWitnessSelection_of_weakSelection_and_aeSmooth
    (charbonnelClosure S) F f a hweak
      (wilkie28_aeSmooth_of_MaxwellAlmostEverywhereSmoothness hMaxwell hn)

end AbelFormalization
