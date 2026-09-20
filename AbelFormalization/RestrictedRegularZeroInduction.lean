import AbelFormalization.RestrictedCanonicalMorseAdjunctionStep

/-!
# Inner induction for restricted regular-zero finiteness

This module packages the manuscript's exponential-list induction.  The
level-zero assertion is kept as an explicit premise: in representative
dimension zero it is the restricted-analytic base case, while in positive
representative dimension it is supplied by the manuscript's outer induction.

The essential successor step is unconditional from `IsAbel`.  It combines
the canonical adjunction construction, the generic squared-distance Morse
theorem, and normalized-cofactor regular arcs.  The property quantifies over
all auxiliary dimensions so that the two fresh coordinates used by the
closed reciprocal curve fall under the induction hypothesis.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-- Regular-zero finiteness on the restricted tail for square systems whose
entries lie in one fixed tower level.  The tower length itself is arbitrary;
levels beyond it are stationary. -/
def RestrictedRegularZeroFiniteAtLevel
    (A : ℝ → ℝ) {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (level : ℕ) : Prop :=
  ∀ {a ell : ℕ}
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (R : ℝ)
    (_hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin ((m + p) + a) → RestrictedSource m p a → ℝ),
    (∀ k, F k ∈ T.level level) →
      (regularZeroSet (restrictedBaseOpenDomain D R)
        (constraintMap F)).Finite

/-- The level-zero assertion, stated directly for the restricted expression
base rather than through an otherwise irrelevant tower. -/
def RestrictedBaseRegularZeroFinite
    (A : ℝ → ℝ) {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D) : Prop :=
  ∀ {a : ℕ} (R : ℝ)
    (_hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin ((m + p) + a) → RestrictedSource m p a → ℝ),
    (∀ k, F k ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)) →
      (regularZeroSet (restrictedBaseOpenDomain D R)
        (constraintMap F)).Finite

/-- The direct base assertion is the same as tower-level finiteness at level
zero. -/
theorem restrictedRegularZeroFiniteAtLevel_zero_of_base
    {A : ℝ → ℝ} {m p : ℕ} {D : RestrictedBox p}
    {representative : ι → Fin m}
    {offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D}
    (hbase : RestrictedBaseRegularZeroFinite
      A D representative offset) :
    RestrictedRegularZeroFiniteAtLevel
      A D representative offset 0 := by
  intro a ell T R hDomain F hF
  apply hbase R hDomain F
  intro k
  simpa only [T.level_zero] using hF k

/-- Exponential adjunction promotes regular-zero finiteness from one tower
level to the next, uniformly in the auxiliary dimension and tower length. -/
theorem IsAbel.restrictedRegularZeroFiniteAtLevel_succ
    {A : ℝ → ℝ} (hA : IsAbel A) {level : ℕ}
    {m p : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (hlevel : RestrictedRegularZeroFiniteAtLevel
      A D representative offset level) :
    RestrictedRegularZeroFiniteAtLevel
      A D representative offset (level + 1) := by
  intro a ell T R hDomain F hF
  by_cases hlt : level < ell
  · let i : Fin ell := ⟨level, hlt⟩
    have hDomainTwo : restrictedBaseClosedDomain
        (m := m) (a := (a + 1) + 1) D R ⊆
      restrictedAbelJetDomain (a := (a + 1) + 1)
        D representative offset := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using
        (restrictedBaseClosedDomain_subset_AbelJetDomain_addAux
          (k := 2) R representative offset hDomain)
    apply hA.finite_regularZeroSet_level_succ_of_canonicalMorse
      representative offset T i R F
    · simpa only [i] using hF
    · exact hDomainTwo
    · intro G hG
      have ih := hlevel
        ((T.extendAuxAbel A representative offset 1).extendAuxAbel
          A representative offset 1)
        R hDomainTwo (fun k x ↦ G x k) hG
      have hmap : constraintMap (fun k x ↦ G x k) = G := by
        rfl
      exact hmap ▸ ih
  · have hell : ell ≤ level := Nat.le_of_not_gt hlt
    apply hlevel T R hDomain F
    intro k
    rw [← T.level_succ_eq_of_length_le hell]
    exact hF k

/-- Nat induction closes every finite tower level from the level-zero
assertion. -/
theorem IsAbel.restrictedRegularZeroFiniteAtLevel_all_of_zero
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (hzero : RestrictedRegularZeroFiniteAtLevel
      A D representative offset 0) :
    ∀ level, RestrictedRegularZeroFiniteAtLevel
      A D representative offset level := by
  intro level
  induction level with
  | zero =>
      intro a ell T R hDomain F hF
      exact hzero T R hDomain F hF
  | succ level ih =>
      exact hA.restrictedRegularZeroFiniteAtLevel_succ
        representative offset ih

/-- The manuscript's base assertion implies regular-zero finiteness at every
finite exponential level. -/
theorem IsAbel.restrictedRegularZeroFiniteAtLevel_all_of_base
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (hbase : RestrictedBaseRegularZeroFinite
      A D representative offset) :
    ∀ level, RestrictedRegularZeroFiniteAtLevel
      A D representative offset level :=
  hA.restrictedRegularZeroFiniteAtLevel_all_of_zero
    representative offset
      (restrictedRegularZeroFiniteAtLevel_zero_of_base hbase)

/-- Terminal-level form: base finiteness propagates through an arbitrary
finite exponential list. -/
theorem IsAbel.finite_regularZeroSet_terminalLevel_of_base
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (hbase : RestrictedBaseRegularZeroFinite
      A D representative offset)
    {a ell : ℕ}
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (R : ℝ)
    (hDomain : restrictedBaseClosedDomain (m := m) (a := a) D R ⊆
      restrictedAbelJetDomain (a := a) D representative offset)
    (F : Fin ((m + p) + a) → RestrictedSource m p a → ℝ)
    (hF : ∀ k, F k ∈ T.level ell) :
    (regularZeroSet (restrictedBaseOpenDomain D R)
      (constraintMap F)).Finite :=
  hA.restrictedRegularZeroFiniteAtLevel_all_of_base
    representative offset hbase ell T R hDomain F hF

/-- Manuscript-style global `P(m,q)`, quantified over every finite offset
list and every bounded box. -/
def RestrictedRegularZeroFiniteForRepresentativeCount
    (A : ℝ → ℝ) (m level : ℕ) : Prop :=
  ∀ {ι : Type} [Finite ι] {p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D),
    RestrictedRegularZeroFiniteAtLevel
      A D representative offset level

/-- Global level-zero version of the manuscript's `P(m,0)`. -/
def RestrictedBaseRegularZeroFiniteForRepresentativeCount
    (A : ℝ → ℝ) (m : ℕ) : Prop :=
  ∀ {ι : Type} [Finite ι] {p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D),
    RestrictedBaseRegularZeroFinite A D representative offset

/-- The level-zero assertion for a fixed representative count propagates
through every finite exponential-list level. -/
theorem IsAbel.restrictedRegularZeroFiniteForRepresentativeCount_all_of_base
    {A : ℝ → ℝ} (hA : IsAbel A) {m : ℕ}
    (hbase : RestrictedBaseRegularZeroFiniteForRepresentativeCount A m) :
    ∀ level, RestrictedRegularZeroFiniteForRepresentativeCount A m level := by
  intro level ι _ p D representative offset
  exact hA.restrictedRegularZeroFiniteAtLevel_all_of_base
    representative offset (hbase D representative offset) level

end AbelFormalization
