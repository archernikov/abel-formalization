import AbelFormalization.CharbonnelIntegerAffineWeakStageSigns
import AbelFormalization.CharbonnelLinearEquivClosure
import AbelFormalization.CharbonnelSemiClosed

/-!
# Wilkie's source-stage hierarchy for the Charbonnel closure

Wilkie's original construction does not begin with the later inductive
description syntax.  For a positive-arity weak family `S`, it first forms

* `Sᵘ`, the nonempty finite unions of members of `S`;
* `Sᵖʳ`, the projections of members of `S` from any larger arity; and
* `Sᶜˡ`, the sets `A₀ ∩ ⋂ i, closure Aᵢ` for a finite (possibly empty)
  list of members of `S`.

The stages are `S(0) = S` and
`S(i+1) = ((S(i)ᵘ)ᵖʳ)ᶜˡ`.  Their union is Wilkie's source presentation of
the Charbonnel closure.  This file records that presentation literally,
rather than replacing the final operation by unrestricted intersection or
by a single closure.

The main bridges are:

* constructor, elimination, monotonicity, and induction lemmas for stages;
* a source-stage depth for the repository's `CharbonnelDescription` syntax;
* inclusion/equality bridges between the staged hierarchy and
  `charbonnelClosure` under the precise weak-family hypotheses they use; and
* the earlier-stage integer-affine sign cuts needed in Wilkie 3.13.

No Sardian approximation theorem is assumed here.  The final section only
shows how a stagewise induction hypothesis supplies the three predecessor
cut certificates used by that constructor.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-! ## The three source operations -/

/-- The union denoted by a finite list of sets.  The empty list is assigned
the empty set; membership in `wilkieFiniteUnionExpansion` below separately
requires a nonempty list, exactly as in Wilkie's `Sᵘ`. -/
def wilkieFiniteUnionCarrier {X : Type*} : List (Set X) → Set X
  | [] => ∅
  | A :: pieces => A ∪ wilkieFiniteUnionCarrier pieces

@[simp]
theorem wilkieFiniteUnionCarrier_nil {X : Type*} :
    wilkieFiniteUnionCarrier ([] : List (Set X)) = ∅ :=
  rfl

@[simp]
theorem wilkieFiniteUnionCarrier_cons {X : Type*}
    (A : Set X) (pieces : List (Set X)) :
    wilkieFiniteUnionCarrier (A :: pieces) =
      A ∪ wilkieFiniteUnionCarrier pieces :=
  rfl

@[simp]
theorem wilkieFiniteUnionCarrier_append {X : Type*}
    (left right : List (Set X)) :
    wilkieFiniteUnionCarrier (left ++ right) =
      wilkieFiniteUnionCarrier left ∪ wilkieFiniteUnionCarrier right := by
  induction left with
  | nil => simp
  | cons A left ih =>
      simp only [List.cons_append, wilkieFiniteUnionCarrier_cons, ih]
      exact (Set.union_assoc A
        (wilkieFiniteUnionCarrier left)
        (wilkieFiniteUnionCarrier right)).symm

/-- The finite intersection of closures in Wilkie's `Sᶜˡ`.  The empty
intersection is the whole space, so the distinguished factor `A₀` is
retained when the list is empty. -/
def wilkieClosedIntersectionCarrier {X : Type*} [TopologicalSpace X] :
    List (Set X) → Set X
  | [] => Set.univ
  | A :: pieces => closure A ∩ wilkieClosedIntersectionCarrier pieces

@[simp]
theorem wilkieClosedIntersectionCarrier_nil
    {X : Type*} [TopologicalSpace X] :
    wilkieClosedIntersectionCarrier ([] : List (Set X)) = Set.univ :=
  rfl

@[simp]
theorem wilkieClosedIntersectionCarrier_cons
    {X : Type*} [TopologicalSpace X]
    (A : Set X) (pieces : List (Set X)) :
    wilkieClosedIntersectionCarrier (A :: pieces) =
      closure A ∩ wilkieClosedIntersectionCarrier pieces :=
  rfl

@[simp]
theorem wilkieClosedIntersectionCarrier_append
    {X : Type*} [TopologicalSpace X]
    (left right : List (Set X)) :
    wilkieClosedIntersectionCarrier (left ++ right) =
      wilkieClosedIntersectionCarrier left ∩
        wilkieClosedIntersectionCarrier right := by
  induction left with
  | nil => simp
  | cons A left ih =>
      simp only [List.cons_append, wilkieClosedIntersectionCarrier_cons, ih]
      exact (Set.inter_assoc (closure A)
        (wilkieClosedIntersectionCarrier left)
        (wilkieClosedIntersectionCarrier right)).symm

/-- Wilkie's `Sᵘ`: nonempty finite unions in each arity. -/
def wilkieFiniteUnionExpansion (S : EuclideanSetFamily) :
    EuclideanSetFamily :=
  fun n => {A | ∃ pieces : List (Set (RealEuclidean n)),
    pieces ≠ [] ∧
      (∀ B ∈ pieces, B ∈ S n) ∧
      wilkieFiniteUnionCarrier pieces = A}

theorem mem_wilkieFiniteUnionExpansion_iff
    {S : EuclideanSetFamily} {n : ℕ} {A : Set (RealEuclidean n)} :
    A ∈ wilkieFiniteUnionExpansion S n ↔
      ∃ pieces : List (Set (RealEuclidean n)),
        pieces ≠ [] ∧
          (∀ B ∈ pieces, B ∈ S n) ∧
          wilkieFiniteUnionCarrier pieces = A :=
  Iff.rfl

/-- Wilkie's `Sᵖʳ`: projections from an arbitrary larger finite arity.
Writing that arity as `n + k` makes the hidden block explicit. -/
def wilkieProjectionExpansion (S : EuclideanSetFamily) :
    EuclideanSetFamily :=
  fun n => {A | ∃ (k : ℕ) (B : Set (RealEuclidean (n + k))),
    B ∈ S (n + k) ∧ realEuclideanExistentialProjection B = A}

theorem mem_wilkieProjectionExpansion_iff
    {S : EuclideanSetFamily} {n : ℕ} {A : Set (RealEuclidean n)} :
    A ∈ wilkieProjectionExpansion S n ↔
      ∃ (k : ℕ) (B : Set (RealEuclidean (n + k))),
        B ∈ S (n + k) ∧ realEuclideanExistentialProjection B = A :=
  Iff.rfl

/-- Wilkie's `Sᶜˡ`, sometimes called closure at infinity: one unclosed
member intersected with finitely many closures of members of the family. -/
def wilkieClosureExpansion (S : EuclideanSetFamily) :
    EuclideanSetFamily :=
  fun n => {A | ∃ (A₀ : Set (RealEuclidean n)), A₀ ∈ S n ∧
    ∃ pieces : List (Set (RealEuclidean n)),
      (∀ B ∈ pieces, B ∈ S n) ∧
        A₀ ∩ wilkieClosedIntersectionCarrier pieces = A}

theorem mem_wilkieClosureExpansion_iff
    {S : EuclideanSetFamily} {n : ℕ} {A : Set (RealEuclidean n)} :
    A ∈ wilkieClosureExpansion S n ↔
      ∃ (A₀ : Set (RealEuclidean n)), A₀ ∈ S n ∧
        ∃ pieces : List (Set (RealEuclidean n)),
          (∀ B ∈ pieces, B ∈ S n) ∧
            A₀ ∩ wilkieClosedIntersectionCarrier pieces = A :=
  Iff.rfl

/-! ## Elementary membership and monotonicity -/

theorem mem_wilkieFiniteUnionExpansion_singleton
    {S : EuclideanSetFamily} {n : ℕ} {A : Set (RealEuclidean n)}
    (hA : A ∈ S n) :
    A ∈ wilkieFiniteUnionExpansion S n := by
  refine ⟨[A], by simp, ?_, ?_⟩
  · simpa using hA
  · simp [wilkieFiniteUnionCarrier]

theorem mem_wilkieFiniteUnionExpansion_pair
    {S : EuclideanSetFamily} {n : ℕ} {A B : Set (RealEuclidean n)}
    (hA : A ∈ S n) (hB : B ∈ S n) :
    A ∪ B ∈ wilkieFiniteUnionExpansion S n := by
  refine ⟨[A, B], by simp, ?_, ?_⟩
  · intro C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · exact hA
    · exact hB
  · simp [wilkieFiniteUnionCarrier]

theorem wilkieFiniteUnionExpansion_union
    {S : EuclideanSetFamily} {n : ℕ} {A B : Set (RealEuclidean n)}
    (hA : A ∈ wilkieFiniteUnionExpansion S n)
    (hB : B ∈ wilkieFiniteUnionExpansion S n) :
    A ∪ B ∈ wilkieFiniteUnionExpansion S n := by
  obtain ⟨left, hleftNonempty, hleft, hleftCarrier⟩ := hA
  obtain ⟨right, hrightNonempty, hright, hrightCarrier⟩ := hB
  refine ⟨left ++ right, ?_, ?_, ?_⟩
  · simpa [hleftNonempty, hrightNonempty]
  · intro C hC
    rw [List.mem_append] at hC
    exact hC.elim (hleft C) (hright C)
  · rw [wilkieFiniteUnionCarrier_append, hleftCarrier, hrightCarrier]

theorem mem_wilkieProjectionExpansion
    {S : EuclideanSetFamily} {n k : ℕ}
    {B : Set (RealEuclidean (n + k))} (hB : B ∈ S (n + k)) :
    realEuclideanExistentialProjection B ∈
      wilkieProjectionExpansion S n :=
  ⟨k, B, hB, rfl⟩

theorem mem_wilkieProjectionExpansion_of_mem
    {S : EuclideanSetFamily} {n : ℕ} {A : Set (RealEuclidean n)}
    (hA : A ∈ S n) :
    A ∈ wilkieProjectionExpansion S n := by
  refine ⟨0, A, ?_, ?_⟩
  · simpa using hA
  · simpa using realEuclideanExistentialProjection_zero A

theorem mem_wilkieClosureExpansion_of_mem
    {S : EuclideanSetFamily} {n : ℕ} {A : Set (RealEuclidean n)}
    (hA : A ∈ S n) :
    A ∈ wilkieClosureExpansion S n := by
  refine ⟨A, hA, [], ?_, ?_⟩
  · simp
  · simp [wilkieClosedIntersectionCarrier]

theorem mem_wilkieClosureExpansion_topologicalClosure
    {S : EuclideanSetFamily} {n : ℕ} {A : Set (RealEuclidean n)}
    (huniv : (Set.univ : Set (RealEuclidean n)) ∈ S n)
    (hA : A ∈ S n) :
    closure A ∈ wilkieClosureExpansion S n := by
  refine ⟨Set.univ, huniv, [A], ?_, ?_⟩
  · simpa using hA
  · simp [wilkieClosedIntersectionCarrier]

theorem wilkieFiniteUnionExpansion_mono
    {S T : EuclideanSetFamily} (hST : S ≤ T) :
    wilkieFiniteUnionExpansion S ≤ wilkieFiniteUnionExpansion T := by
  intro n A hA
  obtain ⟨pieces, hnonempty, hpieces, rfl⟩ := hA
  exact ⟨pieces, hnonempty,
    fun B hB ↦ hST n (hpieces B hB), rfl⟩

theorem wilkieProjectionExpansion_mono
    {S T : EuclideanSetFamily} (hST : S ≤ T) :
    wilkieProjectionExpansion S ≤ wilkieProjectionExpansion T := by
  intro n A hA
  obtain ⟨k, B, hB, rfl⟩ := hA
  exact ⟨k, B, hST (n + k) hB, rfl⟩

theorem wilkieClosureExpansion_mono
    {S T : EuclideanSetFamily} (hST : S ≤ T) :
    wilkieClosureExpansion S ≤ wilkieClosureExpansion T := by
  intro n A hA
  obtain ⟨A₀, hA₀, pieces, hpieces, rfl⟩ := hA
  exact ⟨A₀, hST n hA₀, pieces,
    fun B hB ↦ hST n (hpieces B hB), rfl⟩

theorem le_wilkieFiniteUnionExpansion (S : EuclideanSetFamily) :
    S ≤ wilkieFiniteUnionExpansion S := by
  intro n A hA
  exact mem_wilkieFiniteUnionExpansion_singleton hA

theorem le_wilkieProjectionExpansion (S : EuclideanSetFamily) :
    S ≤ wilkieProjectionExpansion S := by
  intro n A hA
  exact mem_wilkieProjectionExpansion_of_mem hA

theorem le_wilkieClosureExpansion (S : EuclideanSetFamily) :
    S ≤ wilkieClosureExpansion S := by
  intro n A hA
  exact mem_wilkieClosureExpansion_of_mem hA

/-! ## The stages and their union -/

/-- One complete source step `((Sᵘ)ᵖʳ)ᶜˡ`. -/
def wilkieSourceSuccessor (S : EuclideanSetFamily) : EuclideanSetFamily :=
  wilkieClosureExpansion
    (wilkieProjectionExpansion (wilkieFiniteUnionExpansion S))

/-- Wilkie's original hierarchy `S(0)=S`,
`S(i+1)=((S(i)ᵘ)ᵖʳ)ᶜˡ`. -/
def wilkieSourceStage (S : EuclideanSetFamily) : ℕ → EuclideanSetFamily
  | 0 => S
  | i + 1 => wilkieSourceSuccessor (wilkieSourceStage S i)

@[simp]
theorem wilkieSourceStage_zero (S : EuclideanSetFamily) :
    wilkieSourceStage S 0 = S :=
  rfl

@[simp]
theorem wilkieSourceStage_succ (S : EuclideanSetFamily) (i : ℕ) :
    wilkieSourceStage S (i + 1) =
      wilkieSourceSuccessor (wilkieSourceStage S i) :=
  rfl

theorem wilkieSourceSuccessor_mono
    {S T : EuclideanSetFamily} (hST : S ≤ T) :
    wilkieSourceSuccessor S ≤ wilkieSourceSuccessor T :=
  wilkieClosureExpansion_mono
    (wilkieProjectionExpansion_mono
      (wilkieFiniteUnionExpansion_mono hST))

theorem le_wilkieSourceSuccessor (S : EuclideanSetFamily) :
    S ≤ wilkieSourceSuccessor S :=
  (le_wilkieFiniteUnionExpansion S).trans
    ((le_wilkieProjectionExpansion
      (wilkieFiniteUnionExpansion S)).trans
      (le_wilkieClosureExpansion
        (wilkieProjectionExpansion (wilkieFiniteUnionExpansion S))))

theorem wilkieSourceStage_subset_succ
    (S : EuclideanSetFamily) (i : ℕ) :
    wilkieSourceStage S i ≤ wilkieSourceStage S (i + 1) := by
  rw [wilkieSourceStage_succ]
  exact le_wilkieSourceSuccessor (wilkieSourceStage S i)

theorem wilkieSourceStage_mono
    (S : EuclideanSetFamily) {i j : ℕ} (hij : i ≤ j) :
    wilkieSourceStage S i ≤ wilkieSourceStage S j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _hj ih =>
      exact ih.trans (wilkieSourceStage_subset_succ S j)

theorem wilkieSourceStage_mono_base
    {S T : EuclideanSetFamily} (hST : S ≤ T) (i : ℕ) :
    wilkieSourceStage S i ≤ wilkieSourceStage T i := by
  induction i with
  | zero => exact hST
  | succ i ih =>
      simpa only [wilkieSourceStage_succ] using
        wilkieSourceSuccessor_mono ih

/-- The union of all finite source stages. -/
def wilkieSourceHierarchy (S : EuclideanSetFamily) : EuclideanSetFamily :=
  fun n => {A | ∃ i : ℕ, A ∈ wilkieSourceStage S i n}

theorem mem_wilkieSourceHierarchy_iff
    {S : EuclideanSetFamily} {n : ℕ} {A : Set (RealEuclidean n)} :
    A ∈ wilkieSourceHierarchy S n ↔
      ∃ i : ℕ, A ∈ wilkieSourceStage S i n :=
  Iff.rfl

theorem wilkieSourceStage_le_hierarchy
    (S : EuclideanSetFamily) (i : ℕ) :
    wilkieSourceStage S i ≤ wilkieSourceHierarchy S := by
  intro n A hA
  exact ⟨i, hA⟩

theorem le_wilkieSourceHierarchy (S : EuclideanSetFamily) :
    S ≤ wilkieSourceHierarchy S := by
  simpa only [wilkieSourceStage_zero] using
    wilkieSourceStage_le_hierarchy S 0

/-! ## Induction through the literal source operations -/

/-- A reusable elimination principle for the source hierarchy.  It exposes
the three actual operations, rather than an arbitrary description tree. -/
theorem wilkieSourceStage_induction
    {S : EuclideanSetFamily}
    (P : ∀ {n : ℕ}, Set (RealEuclidean n) → Prop)
    (hbase : ∀ {n : ℕ} {A : Set (RealEuclidean n)}, A ∈ S n → P A)
    (hunion : ∀ {n : ℕ}
      (pieces : List (Set (RealEuclidean n))), pieces ≠ [] →
        (∀ A ∈ pieces, P A) → P (wilkieFiniteUnionCarrier pieces))
    (hprojection : ∀ {n k : ℕ} {A : Set (RealEuclidean (n + k))},
      P A → P (realEuclideanExistentialProjection A))
    (hclosure : ∀ {n : ℕ} (A₀ : Set (RealEuclidean n))
      (pieces : List (Set (RealEuclidean n))),
        P A₀ → (∀ A ∈ pieces, P A) →
          P (A₀ ∩ wilkieClosedIntersectionCarrier pieces)) :
    ∀ (i : ℕ) {n : ℕ} {A : Set (RealEuclidean n)},
      A ∈ wilkieSourceStage S i n → P A := by
  intro i
  induction i with
  | zero =>
      intro n A hA
      exact hbase hA
  | succ i ih =>
      intro n A hA
      obtain ⟨A₀, hA₀, closedPieces, hclosedPieces, rfl⟩ := hA
      apply hclosure A₀ closedPieces
      · obtain ⟨k, unionSet, hunionSet, rfl⟩ := hA₀
        apply hprojection
        obtain ⟨pieces, hnonempty, hpieces, rfl⟩ := hunionSet
        exact hunion pieces hnonempty
          (fun B hB ↦ ih (hpieces B hB))
      · intro closedPiece hclosedPiece
        obtain ⟨k, unionSet, hunionSet, rfl⟩ :=
          hclosedPieces closedPiece hclosedPiece
        apply hprojection
        obtain ⟨pieces, hnonempty, hpieces, rfl⟩ := hunionSet
        exact hunion pieces hnonempty
          (fun B hB ↦ ih (hpieces B hB))

theorem wilkieSourceHierarchy_induction
    {S : EuclideanSetFamily}
    (P : ∀ {n : ℕ}, Set (RealEuclidean n) → Prop)
    (hbase : ∀ {n : ℕ} {A : Set (RealEuclidean n)}, A ∈ S n → P A)
    (hunion : ∀ {n : ℕ}
      (pieces : List (Set (RealEuclidean n))), pieces ≠ [] →
        (∀ A ∈ pieces, P A) → P (wilkieFiniteUnionCarrier pieces))
    (hprojection : ∀ {n k : ℕ} {A : Set (RealEuclidean (n + k))},
      P A → P (realEuclideanExistentialProjection A))
    (hclosure : ∀ {n : ℕ} (A₀ : Set (RealEuclidean n))
      (pieces : List (Set (RealEuclidean n))),
        P A₀ → (∀ A ∈ pieces, P A) →
          P (A₀ ∩ wilkieClosedIntersectionCarrier pieces))
    {n : ℕ} {A : Set (RealEuclidean n)}
    (hA : A ∈ wilkieSourceHierarchy S n) : P A := by
  obtain ⟨i, hi⟩ := hA
  exact wilkieSourceStage_induction P hbase hunion hprojection hclosure i hi

/-! ## Weak stages and direct source constructors -/

/-- The assertion that every finite source stage is a positive-arity weak
family.  This names the exact hypothesis used when a 3.13 sign cut is made
inside an earlier stage. -/
def WilkieSourceStagesAreWeak (S : EuclideanSetFamily) : Prop :=
  ∀ i : ℕ, PositiveArityWeakSetStructure (wilkieSourceStage S i)

theorem WilkieSourceStagesAreWeak.base
    {S : EuclideanSetFamily} (hweak : WilkieSourceStagesAreWeak S) :
    PositiveArityWeakSetStructure S := by
  simpa only [wilkieSourceStage_zero] using hweak 0

/-- A finite union made from one stage lies in its successor stage. -/
theorem wilkieSourceStage_succ_of_finiteUnion
    {S : EuclideanSetFamily} {i n : ℕ}
    (pieces : List (Set (RealEuclidean n))) (hnonempty : pieces ≠ [])
    (hpieces : ∀ A ∈ pieces, A ∈ wilkieSourceStage S i n) :
    wilkieFiniteUnionCarrier pieces ∈ wilkieSourceStage S (i + 1) n := by
  have hunion : wilkieFiniteUnionCarrier pieces ∈
      wilkieFiniteUnionExpansion (wilkieSourceStage S i) n :=
    ⟨pieces, hnonempty, hpieces, rfl⟩
  exact mem_wilkieClosureExpansion_of_mem
    (mem_wilkieProjectionExpansion_of_mem hunion)

theorem wilkieSourceStage_succ_of_union
    {S : EuclideanSetFamily} {i n : ℕ}
    {A B : Set (RealEuclidean n)}
    (hA : A ∈ wilkieSourceStage S i n)
    (hB : B ∈ wilkieSourceStage S i n) :
    A ∪ B ∈ wilkieSourceStage S (i + 1) n := by
  simpa [wilkieFiniteUnionCarrier] using
    wilkieSourceStage_succ_of_finiteUnion (S := S) (i := i)
      [A, B] (by simp) (by
        intro C hC
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
        exact hC.elim (fun h ↦ h ▸ hA) (fun h ↦ h ▸ hB))

/-- A projection of a stage member lies in the successor stage. -/
theorem wilkieSourceStage_succ_of_projection
    {S : EuclideanSetFamily} {i n k : ℕ}
    {A : Set (RealEuclidean (n + k))}
    (hA : A ∈ wilkieSourceStage S i (n + k)) :
    realEuclideanExistentialProjection A ∈
      wilkieSourceStage S (i + 1) n := by
  have hunion : A ∈
      wilkieFiniteUnionExpansion (wilkieSourceStage S i) (n + k) :=
    mem_wilkieFiniteUnionExpansion_singleton hA
  exact mem_wilkieClosureExpansion_of_mem
    (mem_wilkieProjectionExpansion hunion)

/-- A closure of a stage member lies in the successor stage.  The weak-family
hypothesis is used only to put the whole ambient space in the same stage,
which is the distinguished `A₀` in `A₀ ∩ closure A`. -/
theorem wilkieSourceStage_succ_of_topologicalClosure
    {S : EuclideanSetFamily} {i n : ℕ} (hn : 0 < n)
    (hweak : PositiveArityWeakSetStructure (wilkieSourceStage S i))
    {A : Set (RealEuclidean n)}
    (hA : A ∈ wilkieSourceStage S i n) :
    closure A ∈ wilkieSourceStage S (i + 1) n := by
  have hunivStage : (Set.univ : Set (RealEuclidean n)) ∈
      wilkieSourceStage S i n :=
    hweak.ws2_polynomialSign hn (polynomialSignConstructible_univ n)
  have hunivMiddle : (Set.univ : Set (RealEuclidean n)) ∈
      wilkieProjectionExpansion
        (wilkieFiniteUnionExpansion (wilkieSourceStage S i)) n :=
    mem_wilkieProjectionExpansion_of_mem
      (mem_wilkieFiniteUnionExpansion_singleton hunivStage)
  have hAMiddle : A ∈
      wilkieProjectionExpansion
        (wilkieFiniteUnionExpansion (wilkieSourceStage S i)) n :=
    mem_wilkieProjectionExpansion_of_mem
      (mem_wilkieFiniteUnionExpansion_singleton hA)
  exact mem_wilkieClosureExpansion_topologicalClosure hunivMiddle hAMiddle

/-- Every finite integer-affine system is polynomial-sign constructible. -/
theorem IsIntegerAffineSet.polynomialSignConstructible
    {n : ℕ} {L : Set (RealEuclidean n)}
    (hL : IsIntegerAffineSet L) :
    PolynomialSignConstructible n L := by
  obtain ⟨r, coeff, constant, rfl⟩ := hL
  let P : MvPolynomial (Fin n) ℝ :=
    integerAffineSystemPolynomial coeff constant
  simpa only [Set.mem_ofPred_eq, P, eval_integerAffineSystemPolynomial,
    Finset.sum_sq_eq_zero_iff, Finset.mem_univ, true_implies] using
    (PolynomialSignConstructible.zero P)

/-- Integer-affine intersection is performed inside the same weak stage; it
does not consume a source-hierarchy step. -/
theorem wilkieSourceStage_integerAffineInter
    {S : EuclideanSetFamily} {i n : ℕ} (hn : 0 < n)
    (hweak : PositiveArityWeakSetStructure (wilkieSourceStage S i))
    {A L : Set (RealEuclidean n)}
    (hA : A ∈ wilkieSourceStage S i n)
    (hL : IsIntegerAffineSet L) :
    A ∩ L ∈ wilkieSourceStage S i n :=
  hweak.ws1_inter hn hA
    (hweak.ws2_polynomialSign hn hL.polynomialSignConstructible)

/-- The three exact/strict cells of one integer-affine row all stay in the
same source stage. -/
theorem wilkieSourceStage_integerAffineSlice_threeCuts
    {S : EuclideanSetFamily} {i n : ℕ} (hn : 0 < n)
    (hweak : PositiveArityWeakSetStructure (wilkieSourceStage S i))
    (B : Set (RealEuclidean n)) (hB : B ∈ wilkieSourceStage S i n)
    (coeff : Fin n → ℤ) (constant : ℤ) :
    B ∩ integerAffineSliceHyperplane coeff constant ∈
        wilkieSourceStage S i n ∧
      B ∩ integerAffineSlicePositiveSide coeff constant ∈
        wilkieSourceStage S i n ∧
      B ∩ integerAffineSliceNegativeSide coeff constant ∈
        wilkieSourceStage S i n := by
  refine ⟨hweak.ws1_inter hn hB
      (hweak.ws2_polynomialSign hn
        (polynomialSignConstructible_integerAffineSliceHyperplane
          coeff constant)), ?_, ?_⟩
  · exact hweak.ws1_inter hn hB
      (hweak.ws2_polynomialSign hn
        (polynomialSignConstructible_integerAffineSlicePositiveSide
          coeff constant))
  · exact hweak.ws1_inter hn hB
      (hweak.ws2_polynomialSign hn
        (polynomialSignConstructible_integerAffineSliceNegativeSide
          coeff constant))

/-! ## The union of weak stages -/

/-- An increasing union of weak source stages is itself a weak family. -/
theorem wilkieSourceHierarchy_positiveArityWeakSetStructure
    {S : EuclideanSetFamily} (hweak : WilkieSourceStagesAreWeak S) :
    PositiveArityWeakSetStructure (wilkieSourceHierarchy S) := by
  refine
    { ws1_inter := ?_
      ws2_polynomialSign := ?_
      ws3_prod := ?_
      ws4_linearEquiv := ?_ }
  · intro n hn A B hA hB
    obtain ⟨i, hi⟩ := hA
    obtain ⟨j, hj⟩ := hB
    let k := max i j
    have hi' : A ∈ wilkieSourceStage S k n :=
      (wilkieSourceStage_mono S (Nat.le_max_left i j)) n hi
    have hj' : B ∈ wilkieSourceStage S k n :=
      (wilkieSourceStage_mono S (Nat.le_max_right i j)) n hj
    exact ⟨k, (hweak k).ws1_inter hn hi' hj'⟩
  · intro n hn A hA
    exact ⟨0, (hweak 0).ws2_polynomialSign hn hA⟩
  · intro n m hn hm A B hA hB
    obtain ⟨i, hi⟩ := hA
    obtain ⟨j, hj⟩ := hB
    let k := max i j
    have hi' : A ∈ wilkieSourceStage S k n :=
      (wilkieSourceStage_mono S (Nat.le_max_left i j)) n hi
    have hj' : B ∈ wilkieSourceStage S k m :=
      (wilkieSourceStage_mono S (Nat.le_max_right i j)) m hj
    exact ⟨k, (hweak k).ws3_prod hn hm hi' hj'⟩
  · intro n hn A hA e
    obtain ⟨i, hi⟩ := hA
    exact ⟨i, (hweak i).ws4_linearEquiv hn hi e⟩

/-! ## Source-stage depth of the inductive description syntax -/

namespace CharbonnelDescription

/-- A source-hierarchy depth for a modern Charbonnel description.  An
integer-affine cut costs no stage because each stage is used as a weak family.
Union, projection, and closure each cost one complete source step. -/
def wilkieSourceStageDepth {S : EuclideanSetFamily} :
    ∀ {n : ℕ}, CharbonnelDescription S n → ℕ
  | _, .base _ _ _ => 0
  | _, .union left right =>
      max left.wilkieSourceStageDepth right.wilkieSourceStageDepth + 1
  | _, .integerAffineInter inner _ _ => inner.wilkieSourceStageDepth
  | _, .projection _ inner => inner.wilkieSourceStageDepth + 1
  | _, .topologicalClosure inner => inner.wilkieSourceStageDepth + 1

@[simp]
theorem wilkieSourceStageDepth_base
    {S : EuclideanSetFamily} {n : ℕ} (hn : 0 < n)
    (A : Set (RealEuclidean n)) (hA : A ∈ S n) :
    wilkieSourceStageDepth (.base hn A hA) = 0 :=
  rfl

@[simp]
theorem wilkieSourceStageDepth_union
    {S : EuclideanSetFamily} {n : ℕ}
    (left right : CharbonnelDescription S n) :
    wilkieSourceStageDepth (.union left right) =
      max left.wilkieSourceStageDepth right.wilkieSourceStageDepth + 1 :=
  rfl

@[simp]
theorem wilkieSourceStageDepth_integerAffineInter
    {S : EuclideanSetFamily} {n : ℕ}
    (inner : CharbonnelDescription S n)
    (L : Set (RealEuclidean n)) (hL : IsIntegerAffineSet L) :
    wilkieSourceStageDepth (.integerAffineInter inner L hL) =
      inner.wilkieSourceStageDepth :=
  rfl

@[simp]
theorem wilkieSourceStageDepth_projection
    {S : EuclideanSetFamily} {n k : ℕ} (hn : 0 < n)
    (inner : CharbonnelDescription S (n + k)) :
    wilkieSourceStageDepth (.projection hn inner) =
      inner.wilkieSourceStageDepth + 1 :=
  rfl

@[simp]
theorem wilkieSourceStageDepth_topologicalClosure
    {S : EuclideanSetFamily} {n : ℕ}
    (inner : CharbonnelDescription S n) :
    wilkieSourceStageDepth (.topologicalClosure inner) =
      inner.wilkieSourceStageDepth + 1 :=
  rfl

/-- The carrier of a description occurs at its computed source depth. -/
theorem carrier_mem_wilkieSourceStage
    {S : EuclideanSetFamily} (hweak : WilkieSourceStagesAreWeak S) :
    ∀ {n : ℕ} (description : CharbonnelDescription S n),
      description.carrier ∈
        wilkieSourceStage S description.wilkieSourceStageDepth n := by
  intro n description
  induction description with
  | base hn A hA => exact hA
  | @union n left right ihleft ihright =>
      let k := max left.wilkieSourceStageDepth right.wilkieSourceStageDepth
      have hleft : left.carrier ∈ wilkieSourceStage S k n :=
        (wilkieSourceStage_mono S
          (Nat.le_max_left left.wilkieSourceStageDepth
            right.wilkieSourceStageDepth)) n ihleft
      have hright : right.carrier ∈ wilkieSourceStage S k n :=
        (wilkieSourceStage_mono S
          (Nat.le_max_right left.wilkieSourceStageDepth
            right.wilkieSourceStageDepth)) n ihright
      exact wilkieSourceStage_succ_of_union hleft hright
  | integerAffineInter inner L hL ih =>
      exact wilkieSourceStage_integerAffineInter inner.positiveArity
        (hweak inner.wilkieSourceStageDepth) ih hL
  | @projection n k hn inner ih =>
      exact wilkieSourceStage_succ_of_projection ih
  | topologicalClosure inner ih =>
      exact wilkieSourceStage_succ_of_topologicalClosure
        inner.positiveArity (hweak inner.wilkieSourceStageDepth) ih

/-- Source depth is bounded by the existing weighted description rank.  The
inequality is strict at closure and can be non-strict at affine cuts. -/
theorem wilkieSourceStageDepth_le_rank
    {S : EuclideanSetFamily} {n : ℕ}
    (description : CharbonnelDescription S n) :
    description.wilkieSourceStageDepth ≤ description.rank := by
  induction description with
  | base => simp
  | union left right ihleft ihright =>
      simp only [wilkieSourceStageDepth_union, rank_union]
      omega
  | integerAffineInter inner L hL ih =>
      simp only [wilkieSourceStageDepth_integerAffineInter,
        rank_integerAffineInter]
      omega
  | projection hn inner ih =>
      simp only [wilkieSourceStageDepth_projection, rank_projection]
      omega
  | topologicalClosure inner ih =>
      simp only [wilkieSourceStageDepth_topologicalClosure,
        rank_topologicalClosure]
      omega

/-- A rank-`r` description carrier belongs to source stage `r`. -/
theorem carrier_mem_wilkieSourceStage_rank
    {S : EuclideanSetFamily} (hweak : WilkieSourceStagesAreWeak S)
    {n : ℕ} (description : CharbonnelDescription S n) :
    description.carrier ∈ wilkieSourceStage S description.rank n :=
  (wilkieSourceStage_mono S description.wilkieSourceStageDepth_le_rank) n
    (description.carrier_mem_wilkieSourceStage hweak)

end CharbonnelDescription

/-! ## Comparison with the maintained description closure -/

private theorem wilkieFiniteUnionCarrier_mem_charbonnelClosure
    {S : EuclideanSetFamily} {n : ℕ}
    (pieces : List (Set (RealEuclidean n))) (hnonempty : pieces ≠ [])
    (hpieces : ∀ A ∈ pieces, A ∈ charbonnelClosure S n) :
    wilkieFiniteUnionCarrier pieces ∈ charbonnelClosure S n := by
  induction pieces with
  | nil => exact (hnonempty rfl).elim
  | cons A pieces ih =>
      by_cases htail : pieces = []
      · subst pieces
        simpa [wilkieFiniteUnionCarrier] using hpieces A (by simp)
      · apply charbonnelClosure_union
        · exact hpieces A (by simp)
        · exact ih htail (fun B hB ↦ hpieces B (by simp [hB]))

private theorem wilkieClosedIntersectionCarrier_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n)
    (pieces : List (Set (RealEuclidean n)))
    (hpieces : ∀ A ∈ pieces, A ∈ charbonnelClosure S n) :
    wilkieClosedIntersectionCarrier pieces ∈ charbonnelClosure S n := by
  induction pieces with
  | nil =>
      simpa [wilkieClosedIntersectionCarrier] using
        hC.ws2_polynomialSign hn (polynomialSignConstructible_univ n)
  | cons A pieces ih =>
      exact hC.ws1_inter hn
        (charbonnelClosure_topologicalClosure (hpieces A (by simp)))
        (ih (fun B hB ↦ hpieces B (by simp [hB])))

/-- Every positive-arity source stage embeds in the maintained Charbonnel
closure as soon as that closure has its weak-family intersection clause. -/
theorem wilkieSourceStage_le_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (i : ℕ) {n : ℕ} (hn : 0 < n)
    {A : Set (RealEuclidean n)}
    (hA : A ∈ wilkieSourceStage S i n) :
    A ∈ charbonnelClosure S n := by
  let P : ∀ {d : ℕ}, Set (RealEuclidean d) → Prop :=
    fun {d} B ↦ 0 < d → B ∈ charbonnelClosure S d
  apply wilkieSourceStage_induction (S := S) P
      (fun hB hd ↦ mem_charbonnelClosure_of_mem hd hB)
      (fun pieces hnonempty hpieces hd ↦
        wilkieFiniteUnionCarrier_mem_charbonnelClosure pieces hnonempty
          (fun B hB ↦ hpieces B hB hd))
      (fun hB hd ↦ charbonnelClosure_projection hd (hB (by omega)))
      (fun B pieces hB hpieces hd ↦
        hC.ws1_inter hd (hB hd)
          (wilkieClosedIntersectionCarrier_mem_charbonnelClosure
            hC hd pieces (fun C hCmem ↦ hpieces C hCmem hd)))
      i hA hn

theorem wilkieSourceHierarchy_le_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ wilkieSourceHierarchy S n) :
    A ∈ charbonnelClosure S n := by
  obtain ⟨i, hi⟩ := hA
  exact wilkieSourceStage_le_charbonnelClosure hC i hn hi

/-- Conversely, every maintained description carrier lies in the source
hierarchy when all source stages have the weak-family clauses used by its
integer-affine constructor. -/
theorem charbonnelClosure_le_wilkieSourceHierarchy
    {S : EuclideanSetFamily} (hweak : WilkieSourceStagesAreWeak S)
    {n : ℕ} {A : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure S n) :
    A ∈ wilkieSourceHierarchy S n := by
  obtain ⟨description, hdescription⟩ := hA
  refine ⟨description.wilkieSourceStageDepth, ?_⟩
  rw [← hdescription]
  exact description.carrier_mem_wilkieSourceStage hweak

/-- On positive arities, the two formal presentations agree under their
precise weak-family hypotheses. -/
theorem wilkieSourceHierarchy_eq_charbonnelClosure
    {S : EuclideanSetFamily} (hweak : WilkieSourceStagesAreWeak S)
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) :
    wilkieSourceHierarchy S n = charbonnelClosure S n := by
  ext A
  constructor
  · exact wilkieSourceHierarchy_le_charbonnelClosure hC hn
  · exact charbonnelClosure_le_wilkieSourceHierarchy hweak

/-! ## Stagewise Sardian bridges for the 3.13 predecessor cuts -/

/-- The semantic approximation property, independent of a chosen
description of the target set. -/
def HasSardianApproximationsForSet
    (G : (d : ℕ) → Set (RealEuclideanFunction d))
    {n : ℕ} (A : Set (RealEuclidean n)) : Prop :=
  ∀ order : ℕ, 0 < order →
    Nonempty (CharbonnelSardianApproximationCertificate G order n A)

theorem CharbonnelDescription.hasSardianApproximations_iff_set
    {G : (d : ℕ) → Set (RealEuclideanFunction d)} {n : ℕ}
    (description : CharbonnelDescription (literalZeroSetFamily G) n) :
    description.HasSardianApproximations G ↔
      HasSardianApproximationsForSet G description.carrier :=
  Iff.rfl

/-- The induction assertion for one literal-zero source stage. -/
def WilkieSourceStageHasSardianApproximations
    (G : (d : ℕ) → Set (RealEuclideanFunction d)) (i : ℕ) : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ {A : Set (RealEuclidean n)},
    A ∈ wilkieSourceStage (literalZeroSetFamily G) i n →
      HasSardianApproximationsForSet G A

/-- Wilkie 3.8's literal-zero constructor is exactly the base case of the
source-stage approximation induction. -/
theorem wilkieSourceStageHasSardianApproximations_zero
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hbase : CharbonnelSardianLiteralZeroBaseInput G) :
    WilkieSourceStageHasSardianApproximations G 0 := by
  intro n hn A hA
  obtain ⟨f, hf, rfl⟩ := hA
  intro order horder
  exact hbase hn f hf order horder

/-- A stagewise Sardian induction hypothesis applies to the exact and both
strict sign cuts without changing the stage. -/
theorem WilkieSourceStageHasSardianApproximations.integerAffineSlice_threeCuts
    {G : (d : ℕ) → Set (RealEuclideanFunction d)} {i n : ℕ}
    (hstage : WilkieSourceStageHasSardianApproximations G i)
    (hweak : PositiveArityWeakSetStructure
      (wilkieSourceStage (literalZeroSetFamily G) i))
    (hn : 0 < n) (B : Set (RealEuclidean n))
    (hB : B ∈ wilkieSourceStage (literalZeroSetFamily G) i n)
    (coeff : Fin n → ℤ) (constant : ℤ) :
    HasSardianApproximationsForSet G
        (B ∩ integerAffineSliceHyperplane coeff constant) ∧
      HasSardianApproximationsForSet G
        (B ∩ integerAffineSlicePositiveSide coeff constant) ∧
      HasSardianApproximationsForSet G
        (B ∩ integerAffineSliceNegativeSide coeff constant) := by
  obtain ⟨hexact, hpositive, hnegative⟩ :=
    wilkieSourceStage_integerAffineSlice_threeCuts hn hweak B hB
      coeff constant
  exact ⟨hstage hn hexact, hstage hn hpositive, hstage hn hnegative⟩

/-- For a maintained description, the earlier-stage induction hypothesis
produces both rank-zero descriptions over that earlier weak family and the
three semantic Sardian approximation properties.  These are precisely the
predecessor objects used before the frontier-trace construction in 3.13. -/
theorem CharbonnelDescription.exists_sourceStage_integerAffineSlice_threeCuts
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hweak : WilkieSourceStagesAreWeak (literalZeroSetFamily G))
    {n : ℕ}
    (inner : CharbonnelDescription (literalZeroSetFamily G) n)
    (hstage : WilkieSourceStageHasSardianApproximations G
      inner.wilkieSourceStageDepth)
    (coeff : Fin n → ℤ) (constant : ℤ) :
    ∃ exactCut positiveCut negativeCut :
        CharbonnelDescription
          (wilkieSourceStage (literalZeroSetFamily G)
            inner.wilkieSourceStageDepth) n,
      exactCut.carrier =
          inner.carrier ∩ integerAffineSliceHyperplane coeff constant ∧
        exactCut.rank = 0 ∧
        positiveCut.carrier =
          inner.carrier ∩ integerAffineSlicePositiveSide coeff constant ∧
        positiveCut.rank = 0 ∧
        negativeCut.carrier =
          inner.carrier ∩ integerAffineSliceNegativeSide coeff constant ∧
        negativeCut.rank = 0 ∧
        HasSardianApproximationsForSet G exactCut.carrier ∧
        HasSardianApproximationsForSet G positiveCut.carrier ∧
        HasSardianApproximationsForSet G negativeCut.carrier := by
  let i := inner.wilkieSourceStageDepth
  have hinner : inner.carrier ∈
      wilkieSourceStage (literalZeroSetFamily G) i n :=
    inner.carrier_mem_wilkieSourceStage hweak
  obtain ⟨exactCut, positiveCut, negativeCut,
      hexactCarrier, hexactRank,
      hpositiveCarrier, hpositiveRank,
      hnegativeCarrier, hnegativeRank⟩ :=
    (hweak i).exists_rank_zero_integerAffineSlice_threeCuts
      inner.positiveArity inner.carrier hinner coeff constant
  obtain ⟨hexactSardian, hpositiveSardian, hnegativeSardian⟩ :=
    hstage.integerAffineSlice_threeCuts (hweak i) inner.positiveArity
      inner.carrier hinner coeff constant
  refine ⟨exactCut, positiveCut, negativeCut,
    hexactCarrier, hexactRank, hpositiveCarrier, hpositiveRank,
    hnegativeCarrier, hnegativeRank, ?_, ?_, ?_⟩
  · simpa only [hexactCarrier] using hexactSardian
  · simpa only [hpositiveCarrier] using hpositiveSardian
  · simpa only [hnegativeCarrier] using hnegativeSardian

end AbelFormalization
