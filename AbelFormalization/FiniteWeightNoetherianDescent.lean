import AbelFormalization.FiniteWeightInvariantCoordinates
import AbelFormalization.FiniteWeightIterationOrder
import AbelFormalization.FiniteWeightLocalizationClosure
import AbelFormalization.FiniteWeightRestrictedDescent
import AbelFormalization.FiniteWeightRestrictedQuotient
import AbelFormalization.FiniteWeightScalarMultiple
import AbelFormalization.MinimalPrimeDescent
import AbelFormalization.MinimalPrimeLocalization
import Mathlib.RingTheory.Localization.Finiteness

set_option autoImplicit false

/-!
# Finite-weight descent over Noetherian coefficient rings

This module carries the actual finite-product descent from Artinian
coefficients to Noetherian coefficients of bounded Krull dimension by
localizing away from the minimal primes, clearing one denominator, and
inducting after quotienting by that denominator.
-/

noncomputable section

namespace AbelFormalization

open scoped Pointwise

variable {R : Type*} [CommRing R] {n : ℕ}
variable {M : Fin n → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The dimension-zero case follows from Hopkins--Levitzki and the actual
finite-length finite-product descent theorem. -/
theorem exists_finiteWeightDescent_stabilizes_of_krullDimLE_zero
    [IsNoetherianRing R] [Ring.KrullDimLE 0 R]
    [∀ i, Module.Finite R (M i)]
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N₀ : Submodule R (∀ i, M i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀) :
    ∃ j₀ : ℕ, (finiteWeightDescentIterate J N₀ j₀).map J.toLinearMap =
        finiteWeightDescentIterate J N₀ j₀ ∧
      ∀ j, j₀ ≤ j →
        finiteWeightDescentIterate J N₀ j =
          finiteWeightDescentIterate J N₀ j₀ := by
  let _ : IsArtinianRing R :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let _ : Module.Finite R (∀ i, M i) := inferInstance
  let _ : IsArtinian R (∀ i, M i) := inferInstance
  let _ : IsNoetherian R (∀ i, M i) := inferInstance
  exact exists_finiteWeightDescent_stabilizes J htri N₀ hN₀

/-! ## Localization away from the minimal primes -/

/-- In positive Krull dimension, the iteration first stabilizes after
localizing away from all minimal primes.  Contracting the stable localized
submodule gives a finitely generated, homogeneous, `J`-invariant submodule
`K`.  One denominator `b`, which avoids every minimal prime, then gives the
sandwich

`b • K ≤ N_{j₁} ≤ K`.

The last two clauses retain the localization information used to construct
`K`: the shifted iterate has the same localization as `K`, and all later
iterates have that same localization. -/
theorem exists_finiteWeightDescent_minimalLocalization_sandwich
    (d : ℕ)
    [IsNoetherianRing R] [Ring.KrullDimLE (d + 1) R]
    [∀ i, Module.Finite R (M i)]
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N₀ : Submodule R (∀ i, M i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀) :
    ∃ (j₁ : ℕ) (K : Submodule R (∀ i, M i)) (b : R),
      (∀ p ∈ minimalPrimes R, b ∉ p) ∧
      Ring.KrullDimLE d (R ⧸ Ideal.span {b}) ∧
      K.FG ∧
      (∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K) ∧
      K.map J.toLinearMap = K ∧
      b • K ≤ finiteWeightDescentIterate J N₀ j₁ ∧
      finiteWeightDescentIterate J N₀ j₁ ≤ K ∧
      (finiteWeightDescentIterate J N₀ j₁).localized'
          (Localization (minimalPrimeAvoidanceSubmonoid R))
          (minimalPrimeAvoidanceSubmonoid R)
          (finiteWeightLocalizationMap
            (M := M) (minimalPrimeAvoidanceSubmonoid R)) =
        K.localized'
          (Localization (minimalPrimeAvoidanceSubmonoid R))
          (minimalPrimeAvoidanceSubmonoid R)
          (finiteWeightLocalizationMap
            (M := M) (minimalPrimeAvoidanceSubmonoid R)) ∧
      ∀ j, j₁ ≤ j →
        (finiteWeightDescentIterate J N₀ j).localized'
            (Localization (minimalPrimeAvoidanceSubmonoid R))
            (minimalPrimeAvoidanceSubmonoid R)
            (finiteWeightLocalizationMap
              (M := M) (minimalPrimeAvoidanceSubmonoid R)) =
          (finiteWeightDescentIterate J N₀ j₁).localized'
            (Localization (minimalPrimeAvoidanceSubmonoid R))
            (minimalPrimeAvoidanceSubmonoid R)
            (finiteWeightLocalizationMap
              (M := M) (minimalPrimeAvoidanceSubmonoid R)) := by
  let S : Submonoid R := minimalPrimeAvoidanceSubmonoid R
  let _ : IsNoetherianRing (Localization S) :=
    IsLocalization.isNoetherianRing S (Localization S) (by infer_instance)
  let _ : IsArtinianRing (Localization S) :=
    minimalPrimeAvoidanceLocalization_isArtinianRing
      (B := R) (T := Localization S)
  let _ : Module.Finite (Localization S)
      (∀ i, LocalizedModule S (M i)) := inferInstance
  let _ : IsArtinian (Localization S)
      (∀ i, LocalizedModule S (M i)) := inferInstance
  let _ : IsNoetherian (Localization S)
      (∀ i, LocalizedModule S (M i)) := inferInstance
  obtain ⟨j₁, hLinv, hLstable⟩ :=
    exists_finiteWeightDescent_stabilizes
      (R := Localization S)
      (M := fun i => LocalizedModule S (M i))
      (finiteWeightLocalizedEquiv (M := M) S J)
      (finiteWeightLocalizedEquiv_triangular (M := M) S J htri)
      (N₀.localized' (Localization S) S
        (finiteWeightLocalizationMap (M := M) S))
      (finiteWeightLocalized_homogeneous (M := M) S N₀ hN₀)
  let L : Submodule (Localization S)
      (∀ i, LocalizedModule S (M i)) :=
    finiteWeightDescentIterate
      (finiteWeightLocalizedEquiv (M := M) S J)
      (N₀.localized' (Localization S) S
        (finiteWeightLocalizationMap (M := M) S)) j₁
  change L.map
      (finiteWeightLocalizedEquiv (M := M) S J).toLinearMap = L at hLinv
  have hLhom : ∀ x ∈ L, ∀ i, Pi.single i (x i) ∈ L := by
    simpa only [L] using
      finiteWeightDescentIterate_homogeneous
        (R := Localization S)
        (M := fun i => LocalizedModule S (M i))
        (finiteWeightLocalizedEquiv (M := M) S J)
        (N₀.localized' (Localization S) S
          (finiteWeightLocalizationMap (M := M) S))
        (finiteWeightLocalized_homogeneous (M := M) S N₀ hN₀) j₁
  let K : Submodule R (∀ i, M i) :=
    finiteWeightLocalizationContraction (M := M) S L
  have hKhom : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K := by
    simpa only [K] using
      finiteWeightLocalizationContraction_homogeneous
        (M := M) S L hLhom
  have hKinv : K.map J.toLinearMap = K := by
    simpa only [K] using
      finiteWeightLocalizationContraction_invariant
        (M := M) S J L hLinv
  have hKfg : K.FG := by
    simpa only [K] using
      finiteWeightLocalizationContraction_fg (M := M) S L
  let N : Submodule R (∀ i, M i) :=
    finiteWeightDescentIterate J N₀ j₁
  have hNlocL : N.localized' (Localization S) S
      (finiteWeightLocalizationMap (M := M) S) = L := by
    simpa only [N, L] using
      localized_finiteWeightDescentIterate (M := M) S J N₀ j₁
  have hKlocL : K.localized' (Localization S) S
      (finiteWeightLocalizationMap (M := M) S) = L := by
    simpa only [K] using
      localized_finiteWeightLocalizationContraction (M := M) S L
  have hloc : N.localized' (Localization S) S
      (finiteWeightLocalizationMap (M := M) S) =
        K.localized' (Localization S) S
          (finiteWeightLocalizationMap (M := M) S) :=
    hNlocL.trans hKlocL.symm
  obtain ⟨s, hsKN, hNK⟩ :=
    exists_smul_contraction_le_and_le_contraction
      (M := M) S L N (by simpa only [K] using hloc)
  change (s : R) • K ≤ N at hsKN
  change N ≤ K at hNK
  have hb : ∀ p ∈ minimalPrimes R, (s : R) ∉ p := by
    simpa only [S, mem_minimalPrimeAvoidanceSubmonoid] using s.property
  have hdim : Ring.KrullDimLE d (R ⧸ Ideal.span {(s : R)}) :=
    Ring.KrullDimLE.quotient_span_singleton_of_avoids_minimalPrimes d hb
  have hlocalizedStable : ∀ j, j₁ ≤ j →
      (finiteWeightDescentIterate J N₀ j).localized'
          (Localization S) S
          (finiteWeightLocalizationMap (M := M) S) =
        (finiteWeightDescentIterate J N₀ j₁).localized'
          (Localization S) S
          (finiteWeightLocalizationMap (M := M) S) := by
    intro j hj
    calc
      (finiteWeightDescentIterate J N₀ j).localized'
          (Localization S) S
          (finiteWeightLocalizationMap (M := M) S) =
        finiteWeightDescentIterate
          (finiteWeightLocalizedEquiv (M := M) S J)
          (N₀.localized' (Localization S) S
            (finiteWeightLocalizationMap (M := M) S)) j :=
        localized_finiteWeightDescentIterate (M := M) S J N₀ j
      _ = finiteWeightDescentIterate
          (finiteWeightLocalizedEquiv (M := M) S J)
          (N₀.localized' (Localization S) S
            (finiteWeightLocalizationMap (M := M) S)) j₁ :=
        hLstable j hj
      _ = (finiteWeightDescentIterate J N₀ j₁).localized'
          (Localization S) S
          (finiteWeightLocalizationMap (M := M) S) :=
        (localized_finiteWeightDescentIterate (M := M) S J N₀ j₁).symm
  refine ⟨j₁, K, (s : R), hb, hdim, hKfg, hKhom, hKinv,
    ?_, ?_, ?_, ?_⟩
  · simpa only [N] using hsKN
  · simpa only [N] using hNK
  · simpa only [S, N] using hloc
  · simpa only [S] using hlocalizedStable

/-! ## The remaining quotient recursion -/

/-! The coordinate quotient is now concrete enough that invariance can be
lifted back from it.  The only induction input still left abstract below is
the existence of an invariant iterate in that quotient product. -/

/-- The quotient iteration attached to a submodule `U` between `b • K` and
`K` has an invariant iterate. -/
def FiniteWeightRestrictedDescentHasInvariantIterate
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (K : Submodule R (∀ i, M i))
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hJK : K.map J.toLinearMap = K)
    (b : R) (U : Submodule R (∀ i, M i)) : Prop :=
  ∃ j₂ : ℕ,
    (finiteWeightDescentIterate
        (finiteWeightRestrictedEquivOfInvariant J K hK hJK b)
        ((finiteWeightCoordinatePullback K U).map
          (finiteWeightRestrictedPiQuotientMap K b)) j₂).map
          (finiteWeightRestrictedEquivOfInvariant J K hK hJK b).toLinearMap =
      finiteWeightDescentIterate
        (finiteWeightRestrictedEquivOfInvariant J K hK hJK b)
        ((finiteWeightCoordinatePullback K U).map
          (finiteWeightRestrictedPiQuotientMap K b)) j₂

/-- An invariant iterate in the coordinate quotient lifts to an invariant
ambient iterate.  Kernel containment is exactly the lower sandwich
`b • K ≤ N_{j₁}`; the upper sandwich lets us identify coordinate iteration
inside `K` with ambient iteration. -/
theorem exists_finiteWeightDescent_stabilizes_of_restrictedQuotient_invariant
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (N₀ : Submodule R (∀ i, M i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀)
    (j₁ : ℕ) (K : Submodule R (∀ i, M i)) (b : R)
    (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
    (hJK : K.map J.toLinearMap = K)
    (hbKN : b • K ≤ finiteWeightDescentIterate J N₀ j₁)
    (hNK : finiteWeightDescentIterate J N₀ j₁ ≤ K)
    (hquotient : FiniteWeightRestrictedDescentHasInvariantIterate
      J K hK hJK b (finiteWeightDescentIterate J N₀ j₁)) :
    ∃ j₀ : ℕ,
      (finiteWeightDescentIterate J N₀ j₀).map J.toLinearMap =
        finiteWeightDescentIterate J N₀ j₀ ∧
      ∀ j, j₀ ≤ j →
        finiteWeightDescentIterate J N₀ j =
          finiteWeightDescentIterate J N₀ j₀ := by
  let N : Submodule R (∀ i, M i) :=
    finiteWeightDescentIterate J N₀ j₁
  let A := finiteWeightInvariantCoordinateEquiv J K hK hJK
  let P : Submodule R (∀ i, finiteWeightCoordinateSubmodule K i) :=
    finiteWeightCoordinatePullback K N
  obtain ⟨j₂, hQinv⟩ := hquotient
  have hkernel : Ideal.span {b} •
      (⊤ : Submodule R
        (∀ i, finiteWeightCoordinateSubmodule K i)) ≤ P := by
    rw [Submodule.ideal_span_singleton_smul,
      ← finiteWeightCoordinatePullback_pointwise_smul K hK b]
    exact Submodule.comap_mono (by simpa only [N] using hbKN)
  let U : Submodule R (∀ i, finiteWeightCoordinateSubmodule K i) :=
    finiteWeightDescentIterate A P j₂
  have hUinv : U.map A.toLinearMap = U := by
    simpa only [U, A, P, N] using
      (finiteWeightInvariantCoordinate_iterate_invariant_of_quotient
        J K hK hJK b P hkernel j₂ (by
          simpa only [P, N] using hQinv))
  have hcoordinateMap : U.map (finiteWeightCoordinateInclusionMap K) =
      finiteWeightDescentIterate J N j₂ := by
    simpa only [U, A, P, N] using
      (map_finiteWeightCoordinate_descentIterate_eq
        J K hK hJK (finiteWeightDescentIterate J N₀ j₁) hNK j₂)
  have hmapInclusion :
      (U.map A.toLinearMap).map (finiteWeightCoordinateInclusionMap K) =
        (U.map (finiteWeightCoordinateInclusionMap K)).map J.toLinearMap := by
    exact map_map_finiteWeightPiMap_eq
      (σ := RingHom.id R)
      (finiteWeightCoordinateInclusion K) A J
      (finiteWeightCoordinateInclusionMap_intertwines J K hK hJK) U
  have hshiftedInv :
      (finiteWeightDescentIterate J N j₂).map J.toLinearMap =
        finiteWeightDescentIterate J N j₂ := by
    calc
      (finiteWeightDescentIterate J N j₂).map J.toLinearMap =
          (U.map (finiteWeightCoordinateInclusionMap K)).map
            J.toLinearMap :=
        congrArg (fun V : Submodule R (∀ i, M i) =>
          V.map J.toLinearMap) hcoordinateMap.symm
      _ = (U.map A.toLinearMap).map
          (finiteWeightCoordinateInclusionMap K) := hmapInclusion.symm
      _ = U.map (finiteWeightCoordinateInclusionMap K) :=
        congrArg
          (fun V : Submodule R
              (∀ i, finiteWeightCoordinateSubmodule K i) =>
            V.map (finiteWeightCoordinateInclusionMap K)) hUinv
      _ = finiteWeightDescentIterate J N j₂ := hcoordinateMap
  have hfinalInv :
      (finiteWeightDescentIterate J N₀ (j₁ + j₂)).map J.toLinearMap =
        finiteWeightDescentIterate J N₀ (j₁ + j₂) := by
    rw [finiteWeightDescentIterate_add]
    simpa only [N] using hshiftedInv
  refine ⟨j₁ + j₂, hfinalInv, ?_⟩
  exact finiteWeightDescentIterate_permanent
    J N₀ hN₀ (j₁ + j₂) hfinalInv

/-- The exact outstanding induction input after localization and denominator
clearing.  It asks the dimension-`d` quotient recursion only for the
coordinate quotient produced by a finitely generated homogeneous invariant
`K` and a sandwich.  All lifting back to the original module is proved above.
-/
def FiniteWeightSuccessorQuotientRemainder
    (d : ℕ)
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (N₀ : Submodule R (∀ i, M i)) : Prop :=
  ∀ (j₁ : ℕ) (K : Submodule R (∀ i, M i)) (b : R),
    Ring.KrullDimLE d (R ⧸ Ideal.span {b}) →
    K.FG →
    ∀ (hK : ∀ x ∈ K, ∀ i, Pi.single i (x i) ∈ K)
      (hJK : K.map J.toLinearMap = K),
      b • K ≤ finiteWeightDescentIterate J N₀ j₁ →
      finiteWeightDescentIterate J N₀ j₁ ≤ K →
      FiniteWeightRestrictedDescentHasInvariantIterate
        J K hK hJK b (finiteWeightDescentIterate J N₀ j₁)

/-- Positive-dimensional stabilization follows from the completed
localization/contraction/sandwich stage and precisely the remaining quotient
recursion implication. -/
theorem exists_finiteWeightDescent_stabilizes_of_krullDimLE_succ
    (d : ℕ)
    [IsNoetherianRing R] [Ring.KrullDimLE (d + 1) R]
    [∀ i, Module.Finite R (M i)]
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N₀ : Submodule R (∀ i, M i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀)
    (hquotient : FiniteWeightSuccessorQuotientRemainder d J N₀) :
    ∃ j₀ : ℕ, (finiteWeightDescentIterate J N₀ j₀).map J.toLinearMap =
        finiteWeightDescentIterate J N₀ j₀ ∧
      ∀ j, j₀ ≤ j →
        finiteWeightDescentIterate J N₀ j =
          finiteWeightDescentIterate J N₀ j₀ := by
  obtain ⟨j₁, K, b, _hb, hdim, hKfg, hKhom, hKinv,
      hbKN, hNK, _hloc, _hlocalizedStable⟩ :=
    exists_finiteWeightDescent_minimalLocalization_sandwich
      (M := M) d J htri N₀ hN₀
  have hrestricted :=
    hquotient j₁ K b hdim hKfg hKhom hKinv hbKN hNK
  exact exists_finiteWeightDescent_stabilizes_of_restrictedQuotient_invariant
    J N₀ hN₀ j₁ K b hKhom hKinv hbKN hNK hrestricted

/-- Finite-weight descent over a Noetherian ring of bounded Krull dimension.

For dimension zero this is unconditional.  In positive dimension the only
extra input is `FiniteWeightSuccessorQuotientRemainder`, the explicitly
isolated quotient-recursion bridge described above. -/
theorem exists_finiteWeightDescent_stabilizes_of_krullDimLE_of_remainder
    (d : ℕ)
    [IsNoetherianRing R] [Ring.KrullDimLE d R]
    [∀ i, Module.Finite R (M i)]
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N₀ : Submodule R (∀ i, M i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀)
    (hquotient : match d with
      | 0 => True
      | e + 1 => FiniteWeightSuccessorQuotientRemainder e J N₀) :
    ∃ j₀ : ℕ, (finiteWeightDescentIterate J N₀ j₀).map J.toLinearMap =
        finiteWeightDescentIterate J N₀ j₀ ∧
      ∀ j, j₀ ≤ j →
        finiteWeightDescentIterate J N₀ j =
          finiteWeightDescentIterate J N₀ j₀ := by
  cases d with
  | zero =>
      exact exists_finiteWeightDescent_stabilizes_of_krullDimLE_zero
        (M := M) J htri N₀ hN₀
  | succ e =>
      exact exists_finiteWeightDescent_stabilizes_of_krullDimLE_succ
        (M := M) e J htri N₀ hN₀ hquotient

/-- Finite-weight descent stabilizes over every Noetherian coefficient ring
of bounded Krull dimension.  The successor step constructs the exact
coordinate quotient required above and invokes the induction hypothesis over
`R/(b)`. -/
theorem exists_finiteWeightDescent_stabilizes_of_krullDimLE
    (d : ℕ)
    [IsNoetherianRing R] [Ring.KrullDimLE d R]
    [∀ i, Module.Finite R (M i)]
    (J : (∀ i, M i) ≃ₗ[R] (∀ i, M i))
    (htri : ∀ i (v : M i), J (Pi.single i v) = Pi.single i v +
      finiteWeightPrefixProjection R M i.val (J (Pi.single i v)))
    (N₀ : Submodule R (∀ i, M i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀) :
    ∃ j₀ : ℕ, (finiteWeightDescentIterate J N₀ j₀).map J.toLinearMap =
        finiteWeightDescentIterate J N₀ j₀ ∧
      ∀ j, j₀ ≤ j →
        finiteWeightDescentIterate J N₀ j =
          finiteWeightDescentIterate J N₀ j₀ := by
  induction d generalizing R n M with
  | zero =>
      exact exists_finiteWeightDescent_stabilizes_of_krullDimLE_zero
        (M := M) J htri N₀ hN₀
  | succ d ih =>
      apply exists_finiteWeightDescent_stabilizes_of_krullDimLE_succ
        (M := M) d J htri N₀ hN₀
      intro j₁ K b hdim hKfg hK hJK hbKN hNK
      let _ : Ring.KrullDimLE d (R ⧸ Ideal.span {b}) := hdim
      let _ : ∀ i, Module.Finite R
          (finiteWeightCoordinateSubmodule K i) := fun i =>
        Module.Finite.of_fg (IsNoetherian.noetherian _)
      let _ : ∀ i, Module.Finite (R ⧸ Ideal.span {b})
          (finiteWeightRestrictedCoordinateQuotient K b i) := fun i =>
        inferInstance
      let P : Submodule R
          (∀ i, finiteWeightCoordinateSubmodule K i) :=
        finiteWeightCoordinatePullback K
          (finiteWeightDescentIterate J N₀ j₁)
      let q := finiteWeightRestrictedPiQuotientMap K b
      let Jq := finiteWeightRestrictedEquivOfInvariant J K hK hJK b
      let Q₀ : Submodule (R ⧸ Ideal.span {b})
          (finiteWeightRestrictedQuotient K b) := P.map q
      have hP : ∀ x ∈ P, ∀ i, Pi.single i (x i) ∈ P := by
        simpa only [P] using
          finiteWeightCoordinatePullback_homogeneous K
            (finiteWeightDescentIterate J N₀ j₁)
            (finiteWeightDescentIterate_homogeneous J N₀ hN₀ j₁)
      have hQ₀ : ∀ x ∈ Q₀, ∀ i, Pi.single i (x i) ∈ Q₀ := by
        simpa only [Q₀, q, finiteWeightRestrictedPiQuotientMap] using
          map_finiteWeightPiMap_homogeneous
            (finiteWeightRestrictedCoordinateQuotientMap K b) P hP
      have hJqtri : ∀ i
          (v : finiteWeightRestrictedCoordinateQuotient K b i),
          Jq (Pi.single i v) = Pi.single i v +
            finiteWeightPrefixProjection (R ⧸ Ideal.span {b})
              (fun i => finiteWeightRestrictedCoordinateQuotient K b i)
              i.val (Jq (Pi.single i v)) := by
        simpa only [Jq] using
          finiteWeightRestrictedEquivOfInvariant_triangular
            J htri K hK hJK b
      obtain ⟨j₂, hj₂, _⟩ := ih
        (R := R ⧸ Ideal.span {b})
        (M := fun i => finiteWeightRestrictedCoordinateQuotient K b i)
        Jq hJqtri Q₀ hQ₀
      exact ⟨j₂, hj₂⟩

end AbelFormalization
