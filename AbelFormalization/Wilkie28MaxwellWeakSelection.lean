import AbelFormalization.MaxwellScalarDiscontinuityEscape
import AbelFormalization.MaxwellAlmostEverywhereSmoothness
import AbelFormalization.Wilkie28WeakSelectionCompactExtraction

/-!
# Maxwell weak selection for Wilkie's singular incidence

The singular-value incidence used in Wilkie's Theorem 2.8 is already a
member of the literal-zero Charbonnel closure, and its projection is the
exceptional parameter slice.  On a small open ball inside that slice every
fiber is nonempty.  Maxwell's continuous weak-selection theorem can therefore
be applied directly; no separate compact graph-extraction hypothesis is
needed.

Every declaration in this file has a proof.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- A Maxwell selection over `RealEuclidean 1` transports to the real-domain
graph convention used by the Wilkie 2.8 witness structure. -/
theorem wilkie28_weakSelection_of_MaxwellContinuousWeakSelection
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {n k : ℕ} (hn : 0 < n)
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n)
    (hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)))
    (hweak : MaxwellContinuousWeakSelection
      (charbonnelClosure (literalZeroSetFamily G))) :
    (interior (Wilkie28MathlibOnly.exceptionalParameterSet F f a)).Nonempty →
      Nonempty (Wilkie28WeakSelectedWitness
        (charbonnelClosure (literalZeroSetFamily G)) F f a) := by
  intro hinterior
  obtain ⟨_hincidenceClosed, hincidenceMem, _hsliceMem, hprojection⟩ :=
    wilkie28WeakSelectionIncidence_sourceData
      hG hsmooth hderiv F f a hF hf
  have hsliceEq :=
    wilkie28FlatExceptionalSlice_eq_exceptionalParameterSet
      hsmooth F f a hF hf
  have hinteriorSlice :
      (interior (wilkie28FlatExceptionalSlice F f a)).Nonempty := by
    rw [hsliceEq]
    exact realEuclideanOne_coordinatePreimage_interior_nonempty hinterior
  obtain ⟨x, r, hr, hball⟩ :=
    exists_openBall_subset_of_interior_nonempty hinteriorSlice
  let B : Set (RealEuclidean 1) := Metric.ball x r
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBnonempty : B.Nonempty := ⟨x, Metric.mem_ball_self hr⟩
  have hBmem :
      B ∈ charbonnelClosure (literalZeroSetFamily G) 1 :=
    hC.ws2_polynomialSign (by omega)
      (polynomialSignConstructible_ball x hr)
  have hfull : MaxwellHasFullFibersOver B
      (wilkie28WeakSelectionIncidence F f a) := by
    rw [maxwellHasFullFibersOver_iff_subset_domain,
      maxwellRelationDomain_eq_existentialProjection, ← hprojection]
    exact hball
  obtain ⟨s⟩ := hweak (by omega) hn hBopen hBnonempty hBmem
    hincidenceMem hfull
  let E := realEuclideanOneEquivReal
  let U : Set ℝ := {t | E.symm t ∈ s.U}
  let phi : ℝ → RealEuclidean n := fun t ↦ s.phi (E.symm t)
  have hUopen : IsOpen U :=
    s.U_open.preimage E.symm.continuous
  have hUnonempty : U.Nonempty := by
    obtain ⟨u, hu⟩ := s.U_nonempty
    refine ⟨E u, ?_⟩
    simpa [U]
  have hgraph :
      wilkie28SelectedWitnessGraph U phi =
        maxwellFunctionGraph s.U s.phi := by
    have hEconst : ∀ t : ℝ, (fun _ : Fin 1 ↦ t) = E.symm t := by
      intro t
      apply E.injective
      rw [E.apply_symm_apply]
      rfl
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨E.symm t, ht, ?_⟩
      rw [hEconst]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨E u, ?_, ?_⟩
      · simpa [U]
      · simp only [phi]
        rw [hEconst, E.symm_apply_apply]
  refine ⟨wilkie28WeakSelectedWitness_of_graph_subset_incidence
    hsmooth F f a hF hf
    (charbonnelClosure (literalZeroSetFamily G)) U phi
    hUopen hUnonempty ?_ ?_⟩
  · rw [hgraph]
    exact s.graph_mem
  · rw [hgraph]
    exact s.graph_subset

/-- Figueiredo--Maxwell Lemma 2.3.1, instantiated by Charbonnel Theorem 2.1,
supplies Wilkie's weak singular-witness selector directly. -/
theorem wilkie28_weakSelection_of_theorem21
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {n k : ℕ} (hn : 0 < n)
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n)
    (hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure (literalZeroSetFamily G))) :
    (interior (Wilkie28MathlibOnly.exceptionalParameterSet F f a)).Nonempty →
      Nonempty (Wilkie28WeakSelectedWitness
        (charbonnelClosure (literalZeroSetFamily G)) F f a) :=
  wilkie28_weakSelection_of_MaxwellContinuousWeakSelection
    hG hsmooth hderiv hn F f a hF hf hC
      (maxwellContinuousWeakSelection_of_theorem21 hC h21)

/-- Charbonnel Theorem 2.1 supplies Wilkie 2.3, and Maxwell's family-level
Theorem 2.4 upgrades the selected graph to the differentiable singular
witness used in Wilkie 2.8. -/
theorem
    wilkie28_smoothSingularWitnessSelection_of_theorem21_and_Maxwell
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {n k : ℕ} (hn : 0 < n)
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n)
    (hC : PositiveArityOMinimalWeakSetStructure
      (charbonnelClosure (literalZeroSetFamily G)))
    (h21 : CharbonnelTheorem21
      (charbonnelClosure (literalZeroSetFamily G)))
    (hMaxwell : MaxwellAlmostEverywhereSmoothness
      (charbonnelClosure (literalZeroSetFamily G))) :
    Wilkie28MathlibOnly.SmoothSingularWitnessSelection F f a :=
  wilkie28_smoothSingularWitnessSelection_of_weakSelection_and_Maxwell
    F f a
      (wilkie28_weakSelection_of_theorem21
        hG hsmooth hderiv hn F f a hF hf hC h21)
      hMaxwell hn

end AbelFormalization
