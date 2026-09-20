import AbelFormalization.Wilkie28WeakSelectionCompactBaireReduction
import AbelFormalization.Wilkie28SelectionComposition

/-!
# Reduction of Wilkie weak selection to compact local graph extraction

The Baire reduction supplies a compact incidence truncation with a projected
set having interior.  If a weak-family graph can be extracted locally from
each such truncation, the resulting section is exactly the weak singular
witness required by Theorem 2.8.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- The exact compact local graph-extraction property left by the Baire
reduction. -/
def Wilkie28CompactIncidenceGraphExtraction
    (C : EuclideanSetFamily) {n k : ℕ}
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k) : Prop :=
  ∀ m : ℕ,
    (interior (maxwellClosedLiftProjectionTruncation
      (wilkie28WeakSelectionIncidence F f a) m)).Nonempty →
    maxwellClosedLiftProjectionTruncation
        (wilkie28WeakSelectionIncidence F f a) m ∈ C 1 →
    ∃ (U : Set ℝ) (φ : ℝ → RealEuclidean n),
      IsOpen U ∧ U.Nonempty ∧
      wilkie28SelectedWitnessGraph U φ ∈ C (1 + n) ∧
      wilkie28SelectedWitnessGraph U φ ⊆
        charbonnelCompactTruncation
          (wilkie28WeakSelectionIncidence F f a) m

/-- A selected graph contained in the literal residual-zero incidence gives
the weak singular-witness structure, with singularity recovered from the
vanishing maximal minors. -/
def wilkie28WeakSelectedWitness_of_graph_subset_incidence
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n)
    (C : EuclideanSetFamily)
    (U : Set ℝ) (φ : ℝ → RealEuclidean n)
    (hUopen : IsOpen U) (hUnonempty : U.Nonempty)
    (hgraphMem : wilkie28SelectedWitnessGraph U φ ∈ C (1 + n))
    (hgraphSubset : wilkie28SelectedWitnessGraph U φ ⊆
      wilkie28WeakSelectionIncidence F f a) :
    Wilkie28WeakSelectedWitness C F f a := by
  have hdata : ∀ t ∈ U,
      F (φ t) = a ∧ f (φ t) = t ∧
        ∀ cols : Fin (k + 1) ↪ Fin n,
          standardJacobianColumnMinor
            (wilkie28AugmentedTuple F f) cols (φ t) = 0 := by
    intro t ht
    have hz : realEuclideanAppend (fun _ : Fin 1 ↦ t) (φ t) ∈
        wilkie28WeakSelectionIncidence F f a := by
      apply hgraphSubset
      exact ⟨t, ht, rfl⟩
    change wilkie28ExceptionalResidual F f a
      (realEuclideanAppend (fun _ : Fin 1 ↦ t) (φ t)) = 0 at hz
    exact (wilkie28ExceptionalResidual_append_eq_zero_iff
      F f a (fun _ : Fin 1 ↦ t) (φ t)).mp hz
  refine
    { U := U
      φ := φ
      U_open := hUopen
      U_nonempty := hUnonempty
      graph_mem := hgraphMem
      F_eq := fun t ht ↦ (hdata t ht).1
      f_eq := fun t ht ↦ (hdata t ht).2.1
      singular := ?_ }
  intro t ht hsurj
  have hFdiff : DifferentiableAt ℝ F (φ t) := by
    rw [differentiableAt_pi]
    intro i
    exact ((hsmooth n (fun y ↦ F y i) (hF i)).differentiable
      (by simp)).differentiableAt
  have hfdiff : DifferentiableAt ℝ f (φ t) :=
    ((hsmooth n f hf).differentiable (by simp)).differentiableAt
  have haugSurj :=
    (wilkie28AugmentedTuple_fderiv_surjective_iff
      F f (φ t) hFdiff hfdiff).mpr hsurj
  have haugMem : FunctionTupleInFamily G (wilkie28AugmentedTuple F f) :=
    wilkie28AugmentedTuple_mem F f hF hf
  obtain ⟨cols, hminor⟩ :=
    (hsmooth.fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
      (wilkie28AugmentedTuple F f) haugMem (φ t)).mp haugSurj
  exact hminor ((hdata t ht).2.2 cols)

/-- Pulling a real set back along the unique coordinate of `ℝ¹` preserves
nonempty interior. -/
theorem realEuclideanOne_coordinatePreimage_interior_nonempty
    {s : Set ℝ} (hs : (interior s).Nonempty) :
    (interior {v : RealEuclidean 1 | v 0 ∈ s}).Nonempty := by
  let E := realEuclideanOneEquivReal
  have hset : E.symm '' s = {v : RealEuclidean 1 | v 0 ∈ s} := by
    ext v
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa [E, realEuclideanOneEquivReal] using ht
    · intro hv
      refine ⟨E v, ?_, E.symm_apply_apply v⟩
      simpa [E, realEuclideanOneEquivReal] using hv
  rw [← hset]
  change (interior (E.symm.toHomeomorph '' s)).Nonempty
  rw [← E.symm.toHomeomorph.image_interior]
  exact hs.image E.symm.toHomeomorph

/-- Maxwell weak selection for the singular incidence follows from the exact
compact graph-extraction core, after the proved compact/Baire localization. -/
theorem wilkie28_weakSelection_of_compactIncidenceGraphExtraction
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n)
    (hextract : Wilkie28CompactIncidenceGraphExtraction
      (charbonnelClosure (literalZeroSetFamily G)) F f a) :
    (interior (Wilkie28MathlibOnly.exceptionalParameterSet F f a)).Nonempty →
      Nonempty (Wilkie28WeakSelectedWitness
        (charbonnelClosure (literalZeroSetFamily G)) F f a) := by
  intro hinterior
  have hsliceEq := wilkie28FlatExceptionalSlice_eq_exceptionalParameterSet
    hsmooth F f a hF hf
  have hinteriorSlice :
      (interior (wilkie28FlatExceptionalSlice F f a)).Nonempty := by
    rw [hsliceEq]
    exact realEuclideanOne_coordinatePreimage_interior_nonempty hinterior
  obtain ⟨m, _hcompact, hprojMem, hprojInterior, _hprojSubset⟩ :=
    wilkie28_exists_compact_incidence_projection_with_interior
      hG hsmooth hderiv F f a hF hf hinteriorSlice
  obtain ⟨U, φ, hUopen, hUnonempty, hgraphMem, hgraphTrunc⟩ :=
    hextract m hprojInterior hprojMem
  refine ⟨wilkie28WeakSelectedWitness_of_graph_subset_incidence
    hsmooth F f a hF hf
    (charbonnelClosure (literalZeroSetFamily G)) U φ
    hUopen hUnonempty hgraphMem ?_⟩
  exact hgraphTrunc.trans
    (charbonnelCompactTruncation_subset
      (wilkie28WeakSelectionIncidence F f a) m)

end AbelFormalization
