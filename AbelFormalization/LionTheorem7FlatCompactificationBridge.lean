import AbelFormalization.LionFlatCompactificationFiber
import AbelFormalization.LionTheorem7Induction

/-!
# Lion's Theorem 7' on the flat compactification

This file isolates the finite output of the recursive proof of Theorem 7'
that is consumed by Lemma 6.  On a full set of parameters, the components of
each fiber are bounded by the total point set of a finite family of terminal
zero-dimensional carpeted leaves.  Zero-regularity makes that terminal point
set finite; the flat compactification bridge then yields uniform finiteness
for every original fiber.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- The associated carpeted leaf representing all of `RealEuclidean n`.
Its equation tuple is empty and its carpet is Lion's standard carpet. -/
def lionWholeSpaceStandardLeaf
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G) (n : ℕ) :
    LionCarpetedLeaf G n 0 where
  U := Set.univ
  isOpen_U := isOpen_univ
  delta := lionStandardCarpet n
  isCarpet := isLionCarpetOn_univ_lionStandardCarpet n
  delta_mem := hG.lionStandardCarpet_mem n
  equations := fun _ ↦ 0
  equations_mem := fun i ↦ Fin.elim0 i
  fderiv_surjective := by
    intro x hx y
    exact ⟨0, Subsingleton.elim _ _⟩

@[simp]
theorem lionWholeSpaceStandardLeaf_carrier
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G) (n : ℕ) :
    (lionWholeSpaceStandardLeaf hG n).carrier = Set.univ := by
  ext x
  simp [lionWholeSpaceStandardLeaf, LionCarpetedLeaf.carrier]

/-- The finite, non-numerical output of Lion's Theorem 7' needed for a map
whose target has the flat compactification shape `(eta, epsilon, T)`.

The recursive Sard/Gabrielov/Rolle construction produces finitely many
zero-dimensional terminal leaves.  For every parameter in the full set, the
generic fiber has at most as many components as there are terminal points.
No numerical component bound, and no finiteness of those points, is assumed
in this structure. -/
structure LionTheorem7PrimeFlatOutput
    (G : (d : ℕ) → Set (RealEuclideanFunction d))
    {n p : ℕ} (L : LionCarpetedLeaf G n 0)
    (F : RealEuclidean n → RealEuclidean (1 + (1 + p))) where
  goodParameters : Set (ℝ × (ℝ × EuclideanSpace ℝ (Fin p)))
  goodParameters_full :
    IsLionFullFlatEuclideanParameterSet goodParameters
  TerminalIndex : Type
  terminalIndexFintype : Fintype TerminalIndex
  terminalDimension : TerminalIndex → ℕ
  terminalLeaf : ∀ i,
    LionCarpetedLeaf.ZeroDimensional G (terminalDimension i)
  genericFiber_le_terminalPoints : ∀ w ∈ goodParameters,
    ENat.card
        (ConnectedComponents
          {x | x ∈ L.carrier ∧
            F x = lionFlatCompactificationParameterTarget w}) ≤
      ENat.card (Σ i, (terminalLeaf i).carrier)

/-- The source-facing Theorem 7' conclusion required here: every
family-valued map with a target of flat-compactification shape has the
preceding finite-terminal-leaf output on the whole-space standard leaf. -/
def HasLionTheorem7PrimeWholeSpaceOutputs
    (G : (d : ℕ) → Set (RealEuclideanFunction d))
    (hG : IsGeometricFunctionFamily G) : Prop :=
  ∀ n p (F : RealEuclidean n → RealEuclidean (1 + (1 + p))),
    FunctionTupleInFamily G F →
      Nonempty
        (LionTheorem7PrimeFlatOutput G
          (lionWholeSpaceStandardLeaf hG n) F)

/-- Zero-regularity turns one genuine Theorem 7' output into the numerical
generic bound consumed by the flat-coordinate Lemma 6 bridge. -/
theorem LionTheorem7PrimeFlatOutput.hasFullGenericFlatFiberBound
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {n p : ℕ} {L : LionCarpetedLeaf G n 0}
    {F : RealEuclidean n → RealEuclidean (1 + (1 + p))}
    (output : LionTheorem7PrimeFlatOutput G L F)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G) :
    ∃ N : ℕ, ∀ w ∈ output.goodParameters,
      ENat.card
          (ConnectedComponents
            {x | x ∈ L.carrier ∧
              F x = lionFlatCompactificationParameterTarget w}) ≤
        (N : ℕ∞) := by
  letI : Fintype output.TerminalIndex := output.terminalIndexFintype
  obtain ⟨bound, _hleaf, htotal⟩ :=
    hzero.exists_sum_bound_of_zeroDimensionalLeaves hsmooth
      output.terminalDimension output.terminalLeaf
  refine ⟨∑ i, bound i, ?_⟩
  intro w hw
  exact (output.genericFiber_le_terminalPoints w hw).trans htotal

/-- Specializing Theorem 7' to the standard flat compactification of every
family tuple supplies exactly `HasLionFullGenericFlatCompactificationBoundsForFamily`.
The only map-membership input is the previously proved flat compactification
closure theorem. -/
theorem HasLionTheorem7PrimeWholeSpaceOutputs.hasLionFullGenericFlatCompactificationBoundsForFamily
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {hG : IsGeometricFunctionFamily G}
    (hT7 : HasLionTheorem7PrimeWholeSpaceOutputs G hG)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G) :
    HasLionFullGenericFlatCompactificationBoundsForFamily G := by
  intro a p g hg
  let F := lionFlatCompactificationMap (lionStandardCarpet a) g
  have hF : FunctionTupleInFamily G F := by
    exact hG.lionStandardFlatCompactificationMap_mem g hg
  obtain ⟨output⟩ := hT7 (a + (1 + (1 + p))) p F hF
  letI : Fintype output.TerminalIndex := output.terminalIndexFintype
  obtain ⟨N, hN⟩ := output.hasFullGenericFlatFiberBound hsmooth hzero
  refine ⟨N, output.goodParameters, output.goodParameters_full, ?_⟩
  intro w hw
  have hbound := hN w hw
  have hfiber :
      {x | x ∈
          (lionWholeSpaceStandardLeaf hG
            (a + (1 + (1 + p)))).carrier ∧
          F x = lionFlatCompactificationParameterTarget w} =
        F ⁻¹' {lionFlatCompactificationParameterTarget w} := by
    ext x
    simp
  rw [hfiber] at hbound
  exact hbound

/-- Direct source-facing endpoint: Theorem 7' on whole-space standard
leaves, together with the already established zero-dimensional endpoint,
implies uniform fiber finiteness. -/
theorem hasUniformFiberFiniteness_of_lionTheorem7PrimeWholeSpaceOutputs
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    (hT7 : HasLionTheorem7PrimeWholeSpaceOutputs G hG) :
    HasUniformFiberFiniteness G := by
  apply hasUniformFiberFiniteness_of_lionFullGenericFlatCompactification
    hsmooth
  exact hT7.hasLionFullGenericFlatCompactificationBoundsForFamily
    hsmooth hzero

end AbelFormalization
