import AbelFormalization.CharbonnelClosureNullityWitnesses
import AbelFormalization.LionLemma4Counting
import AbelFormalization.LionLeafMorseSard
import AbelFormalization.LionTheorem7RolleStep

/-!
# The numerical generic-fiber conclusion of Lion's Theorem 7'

This file composes the four branches of Lion's induction.  Its two analytic
inputs are stated explicitly: the Euclidean rectangular Morse--Sard theorem
and the generic radial-parameter conclusion in Lemma 4.  The output is the
uniform natural-number component bound needed by Lion's compactification
argument.
-/

noncomputable section

open Set Function MeasureTheory
open scoped BigOperators MeasureTheory

namespace AbelFormalization

set_option autoImplicit false

open LionCarpetedLeaf

/-- A conull set of target values on which the fibers of one carpeted leaf
have a common finite bound on their number of connected components. -/
structure LionGenericFiberBound
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {n q p : ℕ} (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p) where
  goodTargets : Set (RealEuclidean p)
  goodTargets_conull : volume goodTargetsᶜ = 0
  bound : ℕ
  component_bound : ∀ t ∈ goodTargets,
    ENat.card (ConnectedComponents (L.fiber g t)) ≤ bound

/-- The low-dimensional branch needed in Theorem 7': a smooth image of a
leaf of dimension smaller than the target dimension is null. -/
def HasLionLowDimensionalImageNullity
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  ∀ {n q p : ℕ} (L : LionCarpetedLeaf G n q)
      (g : RealEuclidean n → RealEuclidean p),
    FunctionTupleInFamily G g → q ≤ n → n - q < p →
      volume (g '' L.carrier) = 0

/-- The parameter-selection conclusion of Lion's Lemma 4, isolated in the
exact form consumed by the induction. -/
def HasLionLemma4RadialSelections
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  ∀ {n q p : ℕ} (L : LionCarpetedLeaf G n q)
      (g : RealEuclidean n → RealEuclidean p),
    FunctionTupleInFamily G g → p + q < n →
      ∃ center : RealEuclidean n, ∃ height : ℝ, 0 < height ∧
        L.HasCriticalTraceRegularCoefficientSelection g center height

/-- The exact constrained critical-value nullity input consumed by the
numerical Theorem 7' induction. -/
def HasLionCriticalTargetNullity
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) : Prop :=
  ∀ {n q p : ℕ} (L : LionCarpetedLeaf G n q)
      (g : RealEuclidean n → RealEuclidean p),
    FunctionTupleInFamily G g → p + q ≤ n →
      volume (L.criticalTargetSet g) = 0

private theorem volume_compl_inter_iInter_eq_zero
    {X I : Type*} [MeasurableSpace X] [Countable I]
    (mu : Measure X) {S : Set X} {T : I → Set X}
    (hS : mu Sᶜ = 0) (hT : ∀ i, mu (T i)ᶜ = 0) :
    mu (S ∩ ⋂ i, T i)ᶜ = 0 := by
  rw [compl_inter, measure_union_null_iff]
  refine ⟨hS, ?_⟩
  rw [compl_iInter]
  exact measure_iUnion_null hT

private theorem volume_compl_inter_preimage_eq_zero
    {p : ℕ} {S : Set (RealEuclidean (p + 1))}
    {T : Set (RealEuclidean p)}
    (hS : volume Sᶜ = 0) (hT : volume Tᶜ = 0) :
    volume (S ∩ LionCarpetedLeaf.rolleValueInit ⁻¹' T)ᶜ = 0 := by
  rw [compl_inter, measure_union_null_iff]
  refine ⟨hS, ?_⟩
  rw [show (LionCarpetedLeaf.rolleValueInit ⁻¹' T)ᶜ =
      LionCarpetedLeaf.rolleValueInit ⁻¹' Tᶜ by simp]
  have heq : (LionCarpetedLeaf.rolleValueInit :
      RealEuclidean (p + 1) → RealEuclidean p) =
      realEuclideanDropLastLinearMap p := by
    funext t j
    rfl
  rw [heq]
  exact volume_dropLast_preimage_eq_zero hT

/-- Lion's Theorem 7' in the numerical form used downstream.

The proof is strong induction on `leaf dimension + target dimension`.  The
four cases are precisely the cases in Lion's paper: null image when the
target is larger, the zero-dimensional endpoint, the finite family of
Gabrielov sections, and the Rolle reduction after deleting the final target
coordinate. -/
theorem exists_lionGenericFiberBound_of_criticalTargetNullity
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    (hcritical : HasLionCriticalTargetNullity G)
    (hlow : HasLionLowDimensionalImageNullity G)
    (hselect : HasLionLemma4RadialSelections G) :
    ∀ {n q p : ℕ} (L : LionCarpetedLeaf G n q)
      (g : RealEuclidean n → RealEuclidean p),
      FunctionTupleInFamily G g → q ≤ n →
        Nonempty (LionGenericFiberBound L g) := by
  intro n q p L g hg hqn
  induction hsum : (n - q) + p using Nat.strong_induction_on
      generalizing n q p with
  | h total ih =>
      let d := n - q
      by_cases hdp : d < p
      · let good : Set (RealEuclidean p) := (g '' L.carrier)ᶜ
        refine ⟨{
          goodTargets := good
          goodTargets_conull := by
            simpa only [good, compl_compl] using hlow L g hg hqn hdp
          bound := 0
          component_bound := ?_ }⟩
        intro t ht
        have hempty : L.fiber g t = ∅ := by
          ext x
          simp only [LionCarpetedLeaf.fiber, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false]
          constructor
          · intro hx
            exact ht ⟨x, hx.1, hx.2⟩
          · intro hx
            contradiction
        rw [hempty, enatCard_connectedComponents_empty]
        exact le_rfl
      · by_cases hpd : p < d
        · have hdim : p + q < n := by
            dsimp only [d] at hpd
            omega
          obtain ⟨center, height, hheight, hselection⟩ :=
            hselect L g hg hdim
          let K : CriticalCoefficientSelection n q p →
              LionCarpetedLeaf G n (n - p) := fun selection ↦
            L.selectedCriticalSectionLeaf
              hG hsmooth hderiv g hg center hheight hdim selection
          have hchild : ∀ selection : CriticalCoefficientSelection n q p,
              Nonempty (LionGenericFiberBound (K selection) g) := by
            intro selection
            apply ih (p + p)
            · dsimp only [d] at hpd
              omega
            · exact hg
            · omega
            · omega
          let child : ∀ selection : CriticalCoefficientSelection n q p,
              LionGenericFiberBound (K selection) g := fun selection ↦
            Classical.choice (hchild selection)
          let good : Set (RealEuclidean p) :=
            L.lemma4GoodTargetSet
                hG hsmooth hderiv g hg center hheight hdim ∩
              ⋂ selection : CriticalCoefficientSelection n q p,
                (child selection).goodTargets
          refine ⟨{
            goodTargets := good
            goodTargets_conull := ?_
            bound := ∑ selection : CriticalCoefficientSelection n q p,
              (child selection).bound
            component_bound := ?_ }⟩
          · apply volume_compl_inter_iInter_eq_zero volume
            · apply L.volume_compl_lemma4GoodTargetSet_eq_zero
                hG hsmooth hderiv g hg center hheight hdim
              · exact hcritical L g hg (by omega)
              · intro selection
                let J := L.selectedCriticalCoefficientLeaf
                  hG hsmooth hderiv g hg center hheight hdim selection
                exact hcritical J g hg (by omega)
            · intro selection
              exact (child selection).goodTargets_conull
          · intro t ht
            apply L.enatCard_connectedComponents_le_sum_selectedCriticalSectionComponents
              hG hsmooth hderiv g hg center hheight hdim hselection t ht.1
            intro selection
            exact (child selection).component_bound t
              (Set.mem_iInter.mp ht.2 selection)
        · have hdeq : d = p := Nat.le_antisymm
              (Nat.le_of_not_gt hpd) (Nat.le_of_not_gt hdp)
          by_cases hpzero : p = 0
          · have hqeq : q = n := by
              dsimp only [d] at hdeq
              omega
            subst p
            subst q
            let _ : Finite L.carrier :=
              Set.finite_coe_iff.mpr
                (L.carrier_finite_of_zeroRegular hsmooth hzero)
            refine ⟨{
              goodTargets := Set.univ
              goodTargets_conull := by simp
              bound := Nat.card L.carrier
              component_bound := ?_ }⟩
            intro t _ht
            let inclusion : L.fiber g t → L.carrier := fun x ↦
              ⟨x, x.property.1⟩
            calc
              ENat.card (ConnectedComponents (L.fiber g t)) ≤
                  ENat.card (L.fiber g t) :=
                enatCard_connectedComponents_le_points
              _ ≤ ENat.card L.carrier :=
                ENat.card_le_card_of_injective (by
                  intro x y hxy
                  apply Subtype.ext
                  exact congrArg
                    (fun z : L.carrier ↦ (z : RealEuclidean n)) hxy :
                    Function.Injective inclusion)
              _ = Nat.card L.carrier := ENat.card_eq_coe_natCard _
          · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpzero
            let init := LionCarpetedLeaf.rolleTargetInit g
            let K := L.regularLeaf hG hsmooth hderiv g hg
            have hinit : FunctionTupleInFamily G init :=
              LionCarpetedLeaf.rolleTargetInit_mem g hg
            have hchild : Nonempty (LionGenericFiberBound K init) := by
              apply ih ((n - q) + k)
              · omega
              · exact hinit
              · exact hqn
              · rfl
            obtain ⟨child⟩ := hchild
            let regularTargets : Set (RealEuclidean (k + 1)) :=
              (L.criticalTargetSet g)ᶜ
            let good : Set (RealEuclidean (k + 1)) :=
              regularTargets ∩
                LionCarpetedLeaf.rolleValueInit ⁻¹' child.goodTargets
            refine ⟨{
              goodTargets := good
              goodTargets_conull := ?_
              bound := child.bound
              component_bound := ?_ }⟩
            · apply volume_compl_inter_preimage_eq_zero
                (S := regularTargets) (T := child.goodTargets)
              · dsimp only [regularTargets]
                rw [compl_compl]
                exact hcritical L g hg (by
                    dsimp only [d] at hdeq
                    omega)
              · exact child.goodTargets_conull
            · intro t ht
              have htregular : L.IsRegularTarget g t :=
                (L.not_mem_criticalTargetSet_iff_isRegularTarget g t).mp ht.1
              exact (L.enatCard_connectedComponents_fiber_le_initFiber_components
                  hG hsmooth hderiv g hg (by
                    dsimp only [d] at hdeq
                    omega) t htregular).trans
                (child.component_bound
                  (LionCarpetedLeaf.rolleValueInit t) ht.2)

/-- A sharp finite-order rectangular Morse--Sard theorem implies the exact
critical-target nullity interface used by Theorem 7'. -/
theorem hasLionCriticalTargetNullity_of_rectangularMorseSard
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hMS : ∀ {a b : ℕ}, b ≤ a →
      ∀ H : RealEuclidean a → RealEuclidean b,
        ContDiff ℝ (a - b + 1 : ℕ) H →
          volume (standardJacobianCriticalValueSet H) = 0) :
    HasLionCriticalTargetNullity G := by
  intro n q p L g hg hdim
  exact L.volume_criticalTargetSet_eq_zero_of_rectangularMorseSard
    hMS hsmooth g hg hdim

/-- The proved all-dimensional smooth rectangular Morse--Sard theorem
discharges the exact critical-target nullity interface used by Theorem 7'. -/
theorem hasLionCriticalTargetNullity_of_contDiff_top
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G) :
    HasLionCriticalTargetNullity G := by
  intro n q p L g hg hdim
  exact L.volume_criticalTargetSet_eq_zero_of_contDiff_top
    hsmooth g hg hdim

/-- Lion's numerical Theorem 7' under the traditional sharp finite-order
rectangular Morse--Sard input. -/
theorem exists_lionGenericFiberBound
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    (hMS : ∀ {a b : ℕ}, b ≤ a →
      ∀ H : RealEuclidean a → RealEuclidean b,
        ContDiff ℝ (a - b + 1 : ℕ) H →
          volume (standardJacobianCriticalValueSet H) = 0)
    (hlow : HasLionLowDimensionalImageNullity G)
    (hselect : HasLionLemma4RadialSelections G) :
    ∀ {n q p : ℕ} (L : LionCarpetedLeaf G n q)
      (g : RealEuclidean n → RealEuclidean p),
      FunctionTupleInFamily G g → q ≤ n →
        Nonempty (LionGenericFiberBound L g) :=
  exists_lionGenericFiberBound_of_criticalTargetNullity
    hG hsmooth hderiv hzero
      (hasLionCriticalTargetNullity_of_rectangularMorseSard hsmooth hMS)
      hlow hselect

/-- Lion's numerical Theorem 7' with rectangular Morse--Sard discharged by
the proved smooth theorem. -/
theorem exists_lionGenericFiberBound_of_contDiff_top
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    (hzero : IsZeroRegularFunctionFamily G)
    (hlow : HasLionLowDimensionalImageNullity G)
    (hselect : HasLionLemma4RadialSelections G) :
    ∀ {n q p : ℕ} (L : LionCarpetedLeaf G n q)
      (g : RealEuclidean n → RealEuclidean p),
      FunctionTupleInFamily G g → q ≤ n →
        Nonempty (LionGenericFiberBound L g) :=
  exists_lionGenericFiberBound_of_criticalTargetNullity
    hG hsmooth hderiv hzero
      (hasLionCriticalTargetNullity_of_contDiff_top hsmooth)
      hlow hselect

end AbelFormalization
