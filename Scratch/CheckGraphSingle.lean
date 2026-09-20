import AbelFormalization.RestrictedPairMergeExceptionalJetGraphLift
import AbelFormalization.RestrictedExpressionBaseFinitePolynomial
import AbelFormalization.OrdinaryHomogenization

/-!
# A common tower and polynomial denominator clearing for pair merging

The exceptional pair-merge construction supplies one exponential tower for
one graph equation or for one derivative datum.  This file concatenates any
finite collection of such towers over the same initial algebra, then applies
that construction to every graph label and every derivative order actually
used by one compressed polynomial family.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

variable {X : Type*}

private def emptyFiniteExponentialTower
    (base : Subalgebra ℝ (X → ℝ)) :
    FiniteExponentialTower base 0 where
  exponent := fun i ↦ Fin.elim0 i
  exponent_mem_level := fun i ↦ Fin.elim0 i

/-- Two towers over the same base can be concatenated after enlarging the
base of the second tower to the terminal level of the first. -/
def FiniteExponentialTower.appendSameBase
    {base : Subalgebra ℝ (X → ℝ)} {l₁ l₂ : ℕ}
    (T₁ : FiniteExponentialTower base l₁)
    (T₂ : FiniteExponentialTower base l₂) :
    FiniteExponentialTower base (l₁ + l₂) :=
  T₁.append (T₂.changeBase (T₁.base_le_level l₁))

/-- A terminal member of the first tower remains a terminal member after
same-base concatenation. -/
theorem FiniteExponentialTower.mem_appendSameBase_left
    {base : Subalgebra ℝ (X → ℝ)} {l₁ l₂ : ℕ}
    (T₁ : FiniteExponentialTower base l₁)
    (T₂ : FiniteExponentialTower base l₂)
    {f : X → ℝ} (hf : f ∈ T₁.level l₁) :
    f ∈ (T₁.appendSameBase T₂).level (l₁ + l₂) := by
  let T₂' := T₂.changeBase (T₁.base_le_level l₁)
  have hf' : f ∈ (T₁.append T₂').level l₁ := by
    rw [T₁.append_level_left T₂' l₁ le_rfl]
    exact hf
  exact (T₁.append T₂').level_mono (Nat.le_add_right l₁ l₂) hf'

/-- A terminal member of the second tower becomes a terminal member after
same-base concatenation. -/
theorem FiniteExponentialTower.mem_appendSameBase_right
    {base : Subalgebra ℝ (X → ℝ)} {l₁ l₂ : ℕ}
    (T₁ : FiniteExponentialTower base l₁)
    (T₂ : FiniteExponentialTower base l₂)
    {f : X → ℝ} (hf : f ∈ T₂.level l₂) :
    f ∈ (T₁.appendSameBase T₂).level (l₁ + l₂) := by
  let hbase : base ≤ T₁.level l₁ := T₁.base_le_level l₁
  let T₂' := T₂.changeBase hbase
  have hf' : f ∈ T₂'.level l₂ :=
    exponentialLevels_mono_base hbase T₂.exponent l₂ hf
  change f ∈ (T₁.append T₂').level (l₁ + l₂)
  rw [T₁.append_level_right T₂' l₂]
  exact hf'

/-- A finite family of functions, each lying in the terminal level of some
finite tower over one common base, lies in one explicitly concatenated finite
tower over that base. -/
theorem exists_common_finiteExponentialTower
    {κ : Type*} [Fintype κ]
    (base : Subalgebra ℝ (X → ℝ)) (f : κ → X → ℝ)
    (hf : ∀ i, ∃ l : ℕ, ∃ T : FiniteExponentialTower base l,
      f i ∈ T.level l) :
    ∃ l : ℕ, ∃ T : FiniteExponentialTower base l,
      ∀ i, f i ∈ T.level l := by
  classical
  have hfinset : ∀ s : Finset κ,
      ∃ l : ℕ, ∃ T : FiniteExponentialTower base l,
        ∀ i ∈ s, f i ∈ T.level l := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨0, emptyFiniteExponentialTower base, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨l₁, T₁, hT₁⟩ := ih
        obtain ⟨l₂, T₂, hT₂⟩ := hf i
        refine ⟨l₁ + l₂, T₁.appendSameBase T₂, ?_⟩
        intro j hj
        rw [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact T₁.mem_appendSameBase_right T₂ hT₂
        · exact T₁.mem_appendSameBase_left T₂ (hT₁ j hj)
  obtain ⟨l, T, hT⟩ := hfinset Finset.univ
  exact ⟨l, T, fun i ↦ hT i (Finset.mem_univ i)⟩

variable {ι : Type*}

/-- The largest derivative order occurring in a compressed finite jet list. -/
noncomputable def restrictedPairMergeExceptionalOrderBound
    (S : Finset (ι × ℕ)) : ℕ :=
  S.sup Prod.snd

theorem restrictedJetEnumeration_order_le_exceptionalOrderBound
    (S : Finset (ι × ℕ)) (v : Fin S.card) :
    (restrictedJetEnumeration S v).2 ≤
      restrictedPairMergeExceptionalOrderBound S := by
  classical
  apply Finset.le_sup
  exact (S.equivFin.symm v).2

/-- Ordinary pulled jets, lifted from the pair box to the enlarged graph box. -/
def restrictedPairMergeOrdinaryGraphJetGenerators
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    Set (RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) a → ℝ) :=
  functionPrecompAlgHom restrictedPairMergeExceptionalGraphDrop ''
    restrictedPairMergeOrdinaryAbelJetGenerators
      (a := a) A D representative offset i j

/-- The common lower-representative special-generator set.  It consists only
of ordinary retained jets and the standard jets represented by the added
exceptional graph coordinates. -/
def restrictedPairMergeExceptionalCommonJetGenerators
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    Set (RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) a → ℝ) :=
  restrictedPairMergeOrdinaryGraphJetGenerators
      A D representative offset i j S ∪
    restrictedPairMergeExceptionalGraphAbelJetGenerators
      (a := a) A D representative i j S

/-- Every graph-target jet is in the common enlarged base. -/
theorem restrictedPairMergeExceptionalGraphTargetJet_mem_commonBase
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    (r : ℕ) :
    restrictedAbelJet A j
        (restrictedPairMergeExceptionalGraphTargetOffset D representative i j S t :
          RestrictedBoxSpace
            ((p + 1) +
              (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) → ℝ)
        r ∈
      restrictedExpressionBase
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
        (restrictedPairMergeExceptionalCommonJetGenerators
          (a := a) A D representative offset i j S) := by
  apply specialGenerator_mem_base
  exact Or.inr ⟨(t, r), rfl⟩

/-- One graph equation has a concrete tower after enlarging its original
graph-jet base to the common lower-representative base. -/
theorem exists_tower_restrictedPairMergeExceptionalGraphEquation_commonBase
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
    let G := restrictedPairMergeExceptionalCommonJetGenerators
      (a := a) A D representative offset i j S
    ∃ l : ℕ, ∃ T : RestrictedExpressionTower
        (restrictedPairMergeExceptionalGraphBox D N) G (ell := l),
      restrictedPairMergeExceptionalRestrictedGraphEquation
        D representative offset K k i j S t ∈ T.level l := by
  dsimp only
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let G := restrictedPairMergeExceptionalCommonJetGenerators
    (a := a) A D representative offset i j S
  let base := restrictedExpressionBase
    (restrictedPairMergeExceptionalGraphBox D N) G
  obtain ⟨T₀, hT₀⟩ :=
    exists_tower_restrictedPairMergeExceptionalRestrictedGraphEquation
      A D representative offset K k i j S t
  let G₀ := restrictedPairMergeExceptionalGraphAbelJetGenerators
    (a := a) A D representative i j S
  let base₀ := restrictedExpressionBase
    (restrictedPairMergeExceptionalGraphBox D N) G₀
  have hbase : base₀ ≤ base :=
    restrictedExpressionBase_mono _ (fun _ hg ↦ Or.inr hg)
  let T := T₀.changeBase hbase
  refine ⟨_, T, ?_⟩
  exact exponentialLevels_mono_base hbase T₀.exponent _ hT₀


end AbelFormalization
