import AbelFormalization.RestrictedPairMergeExpressionPullback
import AbelFormalization.RestrictedBaseFiniteSystemCompression
import AbelFormalization.RealTransferJetSubstitution
import AbelFormalization.RestrictedFixedIterateShiftGraph
import AbelFormalization.FiniteImplicitRegularZeroGraphLift
import AbelFormalization.IteratedAbelDerivativeSubstitution

/-!
# Finite graph variables for the exceptional pair-merge jets

This file makes the finite part of the exceptional-jet construction explicit.
A fixed finite base equation family uses only finitely many named Abel jets.
Among their offset labels, only labels carried by the pivot or its retained
partner need a nonlinear shift.  We enumerate those distinct offset labels,
append one `(-1,1)` box coordinate for each, and record the exact
`restrictedFixedIterateShift` graph equation.

The last section records the two jet facts currently supplied by the Abel
API: order-zero exceptional jets are standard graph jets plus a constant,
and every positive-order jet admits the exact one-step real Stirling
substitution.  No closure under an iterated substitution is assumed.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

/-! ## Finite exceptional support -/

/-- The distinct offset labels, among a finite jet support, which are carried
by one of the two representatives involved in the pair merge. -/
noncomputable def restrictedPairMergeExceptionalOffsetSupport
    {m : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) : Finset ι := by
  classical
  exact (S.image Prod.fst).filter fun q ↦
    representative q = i ∨ representative q = i.succAbove j

@[simp]
theorem mem_restrictedPairMergeExceptionalOffsetSupport_iff
    {m : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) (q : ι) :
    q ∈ restrictedPairMergeExceptionalOffsetSupport representative i j S ↔
      (∃ r, (q, r) ∈ S) ∧
        (representative q = i ∨ representative q = i.succAbove j) := by
  classical
  simp [restrictedPairMergeExceptionalOffsetSupport]

/-- Canonical duplicate-free enumeration of the exceptional offset labels. -/
noncomputable def restrictedPairMergeExceptionalOffsetEnumeration
    {m : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ι :=
  fun t ↦
    ((restrictedPairMergeExceptionalOffsetSupport representative i j S).equivFin.symm t).1

theorem restrictedPairMergeExceptionalOffsetEnumeration_mem
    {m : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    restrictedPairMergeExceptionalOffsetEnumeration representative i j S t ∈
      restrictedPairMergeExceptionalOffsetSupport representative i j S := by
  classical
  exact ((restrictedPairMergeExceptionalOffsetSupport representative i j S).equivFin.symm t).2

theorem restrictedPairMergeExceptionalOffsetEnumeration_injective
    {m : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    Function.Injective
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S) := by
  classical
  unfold restrictedPairMergeExceptionalOffsetEnumeration
  exact Subtype.val_injective.comp
    (restrictedPairMergeExceptionalOffsetSupport representative i j S).equivFin.symm.injective

/-- Finite compression of a fixed equation family, together with the finite
set which will index all exceptional graph shifts. -/
theorem exists_pairMergeFiniteEquationJetSupport
    (A : ℝ → ℝ) {m p a n : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (F : Fin n → RestrictedSource ((m + 1) + 1) p a → ℝ)
    (hF : ∀ e, F e ∈ restrictedExpressionBase D
      (restrictedAbelJetGenerators (a := a) A representative offset)) :
    ∃ S : Finset (ι × ℕ),
      ∃ Q : Fin n → MvPolynomial (PaperRankSymbols ((m + 1) + 1) a S.card)
          (RestrictedBox.analyticNearClosedBoxSubalgebra D),
      ∃ C : Finset (RestrictedBox.analyticNearClosedBoxSubalgebra D),
        (∀ e d, d ∈ (Q e).support → (Q e).coeff d ∈ C) ∧
        (∀ e, restrictedPaperPolynomialValue A D representative offset
          (restrictedJetEnumeration S) (Q e) = F e) ∧
        ∀ q, q ∈ restrictedPairMergeExceptionalOffsetSupport
            representative i j S ↔
          (∃ r, (q, r) ∈ S) ∧
            (representative q = i ∨ representative q = i.succAbove j) := by
  obtain ⟨S, Q, C, hC, hQ⟩ :=
    exists_restrictedPaperPolynomialFamilyValue_eq_of_mem_base
      A D representative offset F hF
  exact ⟨S, Q, C, hC, hQ,
    mem_restrictedPairMergeExceptionalOffsetSupport_iff representative i j S⟩

/-! ## A finite block of bounded graph coordinates -/

/-- Append `N` copies of `(-1,1)` to the pair-merge box in one block. -/
def restrictedPairMergeExceptionalGraphBox {p : ℕ}
    (D : RestrictedBox p) (N : ℕ) : RestrictedBox ((p + 1) + N) where
  lower := Fin.addCases (restrictedPairMergeBox D).lower (fun _ ↦ -1)
  upper := Fin.addCases (restrictedPairMergeBox D).upper (fun _ ↦ 1)
  lower_lt_upper := fun z ↦ Fin.addCases
    (fun q ↦ by
      simpa using (restrictedPairMergeBox D).lower_lt_upper q)
    (fun _ ↦ by norm_num) z

@[simp]
theorem restrictedPairMergeExceptionalGraphBox_lower_castAdd
    {p N : ℕ} (D : RestrictedBox p) (q : Fin (p + 1)) :
    (restrictedPairMergeExceptionalGraphBox D N).lower (Fin.castAdd N q) =
      (restrictedPairMergeBox D).lower q := by
  simp [restrictedPairMergeExceptionalGraphBox]

@[simp]
theorem restrictedPairMergeExceptionalGraphBox_upper_castAdd
    {p N : ℕ} (D : RestrictedBox p) (q : Fin (p + 1)) :
    (restrictedPairMergeExceptionalGraphBox D N).upper (Fin.castAdd N q) =
      (restrictedPairMergeBox D).upper q := by
  simp [restrictedPairMergeExceptionalGraphBox]

@[simp]
theorem restrictedPairMergeExceptionalGraphBox_lower_natAdd
    {p N : ℕ} (D : RestrictedBox p) (t : Fin N) :
    (restrictedPairMergeExceptionalGraphBox D N).lower
        (Fin.natAdd (p + 1) t) = -1 := by
  simp [restrictedPairMergeExceptionalGraphBox]

@[simp]
theorem restrictedPairMergeExceptionalGraphBox_upper_natAdd
    {p N : ℕ} (D : RestrictedBox p) (t : Fin N) :
    (restrictedPairMergeExceptionalGraphBox D N).upper
        (Fin.natAdd (p + 1) t) = 1 := by
  simp [restrictedPairMergeExceptionalGraphBox]

theorem mem_openBox_restrictedPairMergeExceptionalGraphBox_iff
    {p N : ℕ} (D : RestrictedBox p)
    (w : RestrictedBoxSpace ((p + 1) + N)) :
    w ∈ (restrictedPairMergeExceptionalGraphBox D N).openBox ↔
      (fun q ↦ w (Fin.castAdd N q)) ∈ (restrictedPairMergeBox D).openBox ∧
      ∀ t : Fin N, w (Fin.natAdd (p + 1) t) ∈ Ioo (-1) 1 := by
  rw [(restrictedPairMergeExceptionalGraphBox D N).mem_openBox,
    (restrictedPairMergeBox D).mem_openBox]
  constructor
  · intro hw
    exact ⟨fun q ↦ by simpa using hw (Fin.castAdd N q),
      fun t ↦ by simpa using hw (Fin.natAdd (p + 1) t)⟩
  · rintro ⟨hw, heta⟩ z
    refine Fin.addCases (fun q ↦ ?_) (fun t ↦ ?_) z
    · simpa using hw q
    · simpa using heta t

/-- Forget the graph-coordinate block. -/
def restrictedPairMergeExceptionalGraphDrop {m p a N : ℕ} :
    RestrictedSource (m + 1) ((p + 1) + N) a →
      RestrictedSource (m + 1) (p + 1) a :=
  fun x ↦ ((x.1.1, fun q ↦ x.1.2 (Fin.castAdd N q)), x.2)

/-- Adjoin prescribed graph-coordinate functions to a pair-merge source. -/
def restrictedPairMergeExceptionalGraphLift {m p a N : ℕ}
    (eta : Fin N → RestrictedSource (m + 1) (p + 1) a → ℝ) :
    RestrictedSource (m + 1) (p + 1) a →
      RestrictedSource (m + 1) ((p + 1) + N) a :=
  fun x ↦ ((x.1.1, Fin.addCases x.1.2 (fun t ↦ eta t x)), x.2)

@[simp]
theorem restrictedPairMergeExceptionalGraphDrop_lift
    {m p a N : ℕ}
    (eta : Fin N → RestrictedSource (m + 1) (p + 1) a → ℝ)
    (x : RestrictedSource (m + 1) (p + 1) a) :
    restrictedPairMergeExceptionalGraphDrop
        (restrictedPairMergeExceptionalGraphLift eta x) = x := by
  ext <;> simp [restrictedPairMergeExceptionalGraphDrop,
    restrictedPairMergeExceptionalGraphLift]

@[simp]
theorem restrictedPairMergeExceptionalGraphLift_box_castAdd
    {m p a N : ℕ}
    (eta : Fin N → RestrictedSource (m + 1) (p + 1) a → ℝ)
    (x : RestrictedSource (m + 1) (p + 1) a) (q : Fin (p + 1)) :
    (restrictedPairMergeExceptionalGraphLift eta x).1.2
        (Fin.castAdd N q) = x.1.2 q := by
  simp [restrictedPairMergeExceptionalGraphLift]

@[simp]
theorem restrictedPairMergeExceptionalGraphLift_box_natAdd
    {m p a N : ℕ}
    (eta : Fin N → RestrictedSource (m + 1) (p + 1) a → ℝ)
    (x : RestrictedSource (m + 1) (p + 1) a) (t : Fin N) :
    (restrictedPairMergeExceptionalGraphLift eta x).1.2
        (Fin.natAdd (p + 1) t) = eta t x := by
  simp [restrictedPairMergeExceptionalGraphLift]

/-! ## The fixed-iterate shifts attached to the finite support -/

/-- The iterate depth attached to an exceptional offset.  Pivot labels use
`K+k`; all other labels (and hence every exceptional non-pivot label) use
the retained-partner depth `K`. -/
def restrictedPairMergeExceptionalDepth {m : ℕ}
    (representative : ι → Fin ((m + 1) + 1))
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (q : ι) : ℕ :=
  if representative q = i then K + k else K

theorem restrictedPairMergeExceptionalDepth_pos
    {m : ℕ} (representative : ι → Fin ((m + 1) + 1))
    {K k : ℕ} (hK : 1 ≤ K) (i : Fin ((m + 1) + 1)) (q : ι) :
    1 ≤ restrictedPairMergeExceptionalDepth representative K k i q := by
  unfold restrictedPairMergeExceptionalDepth
  split <;> omega

/-- The source argument before applying the fixed iterate.  It is `u+xi`
for a pivot offset and `u` for a retained-partner offset. -/
def restrictedPairMergeExceptionalBaseArgument
    {m p a : ℕ} (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) (q : ι) :
    RestrictedSource (m + 1) (p + 1) a → ℝ :=
  fun x ↦ if representative q = i then
    x.1.1 j + x.1.2 (Fin.last p)
  else x.1.1 j

/-- The old coefficient, pulled back over the pair-merge box. -/
def restrictedPairMergeExceptionalOldOffset
    {p : ℕ} (D : RestrictedBox p)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (q : ι) : RestrictedBox.analyticNearClosedBoxSubalgebra
      (restrictedPairMergeBox D) :=
  D.pullbackSnoc (-1) 1 (by norm_num) (offset q)

/-- The bounded fixed-iterate shift for one exceptional offset label. -/
def restrictedPairMergeExceptionalShift
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) (q : ι) :
    RestrictedSource (m + 1) (p + 1) a → ℝ :=
  fun x ↦ restrictedFixedIterateShift
    (restrictedPairMergeExceptionalDepth representative K k i q)
    (restrictedPairMergeBox D)
    (restrictedPairMergeExceptionalOldOffset D offset q)
    (restrictedPairMergeExceptionalBaseArgument representative i j q x, x.1.2)

/-- Pointwise graph specification for one exceptional offset. -/
theorem restrictedPairMergeExceptionalShift_spec
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) (q : ι)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ (restrictedPairMergeBox D).closedBox,
      |(restrictedPairMergeExceptionalOldOffset D offset q :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (htail : B + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j q x)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox) :
    restrictedPairMergeExceptionalShift D representative offset K k i j q x ∈
        Ioo (-1) 1 ∧
      E^[restrictedPairMergeExceptionalDepth representative K k i q]
          (restrictedPairMergeExceptionalBaseArgument representative i j q x +
            restrictedPairMergeExceptionalShift D representative offset K k i j q x) -
        E^[restrictedPairMergeExceptionalDepth representative K k i q]
          (restrictedPairMergeExceptionalBaseArgument representative i j q x) =
        (restrictedPairMergeExceptionalOldOffset D offset q :
          RestrictedBoxSpace (p + 1) → ℝ) x.1.2 := by
  have hspec := restrictedFixedIterateShift_spec
    (restrictedPairMergeExceptionalDepth_pos representative (k := k) hK i q)
    (restrictedPairMergeBox D)
    (restrictedPairMergeExceptionalOldOffset D offset q)
    hB hbB htail hw
  exact ⟨hspec.1, hspec.2.1⟩

/-- The simultaneous finite family of shifts, indexed by distinct exceptional
offset labels rather than by derivative orders. -/
def restrictedPairMergeExceptionalGraphShift
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card →
      RestrictedSource (m + 1) (p + 1) a → ℝ :=
  fun t ↦ restrictedPairMergeExceptionalShift D representative offset K k i j
    (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)

/-- The pair source lifted by all finitely many exceptional graph shifts. -/
def restrictedPairMergeExceptionalFiniteGraphLift
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    RestrictedSource (m + 1) (p + 1) a →
      RestrictedSource (m + 1)
        ((p + 1) +
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) a :=
  restrictedPairMergeExceptionalGraphLift
    (restrictedPairMergeExceptionalGraphShift D representative offset K k i j S)

@[simp]
theorem restrictedPairMergeExceptionalFiniteGraphLift_graphCoordinate
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (x : RestrictedSource (m + 1) (p + 1) a)
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    (restrictedPairMergeExceptionalFiniteGraphLift D representative offset K k i j S x).1.2
        (Fin.natAdd (p + 1) t) =
      restrictedPairMergeExceptionalGraphShift D representative offset K k i j S t x := by
  simp [restrictedPairMergeExceptionalFiniteGraphLift]

/-- Simultaneous graph equations and membership in the enlarged open box.
The bounds are finite data: one bound is supplied for each distinct offset
actually used by the equation family. -/
theorem restrictedPairMergeExceptionalFiniteGraphLift_spec
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x) :
    (restrictedPairMergeExceptionalFiniteGraphLift D representative offset K k i j S x).1.2 ∈
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card).openBox ∧
      ∀ t,
        E^[restrictedPairMergeExceptionalDepth representative K k i
            (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)]
            (restrictedPairMergeExceptionalBaseArgument representative i j
                (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x +
              restrictedPairMergeExceptionalGraphShift D representative offset K k i j S t x) -
          E^[restrictedPairMergeExceptionalDepth representative K k i
            (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)]
            (restrictedPairMergeExceptionalBaseArgument representative i j
              (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x) =
          (restrictedPairMergeExceptionalOldOffset D offset
            (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
              RestrictedBoxSpace (p + 1) → ℝ) x.1.2 := by
  have hspec : ∀ t,
      restrictedPairMergeExceptionalGraphShift D representative offset K k i j S t x ∈
          Ioo (-1) 1 ∧
        E^[restrictedPairMergeExceptionalDepth representative K k i
            (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)]
            (restrictedPairMergeExceptionalBaseArgument representative i j
                (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x +
              restrictedPairMergeExceptionalGraphShift D representative offset K k i j S t x) -
          E^[restrictedPairMergeExceptionalDepth representative K k i
            (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)]
            (restrictedPairMergeExceptionalBaseArgument representative i j
              (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x) =
          (restrictedPairMergeExceptionalOldOffset D offset
            (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
              RestrictedBoxSpace (p + 1) → ℝ) x.1.2 := by
    intro t
    exact restrictedPairMergeExceptionalShift_spec D representative offset hK i j _
      (hB t) (hbB t) x (htail t) hw
  constructor
  · rw [mem_openBox_restrictedPairMergeExceptionalGraphBox_iff]
    exact ⟨by
      simpa [restrictedPairMergeExceptionalFiniteGraphLift,
        restrictedPairMergeExceptionalGraphLift] using hw,
      fun t ↦ by
        simpa using (hspec t).1⟩
  · exact fun t ↦ (hspec t).2

/-! ## Standard Abel jets on the graph box -/

/-- Projection from the enlarged graph box back to the pair-merge box. -/
def restrictedPairMergeExceptionalGraphBoxDropCLM (p N : ℕ) :
    RestrictedBoxSpace ((p + 1) + N) →L[ℝ] RestrictedBoxSpace (p + 1) :=
  ContinuousLinearMap.pi fun q ↦
    ContinuousLinearMap.proj (R := ℝ) (Fin.castAdd N q)

@[simp]
theorem restrictedPairMergeExceptionalGraphBoxDropCLM_apply
    {p N : ℕ} (w : RestrictedBoxSpace ((p + 1) + N)) (q : Fin (p + 1)) :
    restrictedPairMergeExceptionalGraphBoxDropCLM p N w q =
      w (Fin.castAdd N q) :=
  rfl

/-- Pull an analytic pair-box coefficient through the projection which
forgets all graph coordinates. -/
def RestrictedBox.pullbackPairMergeExceptionalGraph
    {p : ℕ} (D : RestrictedBox p) (N : ℕ)
    (f : RestrictedBox.analyticNearClosedBoxSubalgebra
      (restrictedPairMergeBox D)) :
    RestrictedBox.analyticNearClosedBoxSubalgebra
      (restrictedPairMergeExceptionalGraphBox D N) :=
  ⟨fun w ↦ (f : RestrictedBoxSpace (p + 1) → ℝ)
      (restrictedPairMergeExceptionalGraphBoxDropCLM p N w), by
    change (restrictedPairMergeExceptionalGraphBox D N).AnalyticNearClosedBox
      (fun w ↦ (f : RestrictedBoxSpace (p + 1) → ℝ)
        (restrictedPairMergeExceptionalGraphBoxDropCLM p N w))
    rw [(restrictedPairMergeExceptionalGraphBox D N).analyticNearClosedBox_iff]
    intro w hw
    have hwPair : restrictedPairMergeExceptionalGraphBoxDropCLM p N w ∈
        (restrictedPairMergeBox D).closedBox := by
      rw [(restrictedPairMergeBox D).mem_closedBox]
      intro q
      have hw' :=
        ((restrictedPairMergeExceptionalGraphBox D N).mem_closedBox.mp hw)
          (Fin.castAdd N q)
      simpa using hw'
    have hf := ((restrictedPairMergeBox D).analyticNearClosedBox_iff.mp f.property)
      (restrictedPairMergeExceptionalGraphBoxDropCLM p N w) hwPair
    change AnalyticAt ℝ
      ((f : RestrictedBoxSpace (p + 1) → ℝ) ∘
        restrictedPairMergeExceptionalGraphBoxDropCLM p N) w
    exact hf.compContinuousLinearMap
      (u := restrictedPairMergeExceptionalGraphBoxDropCLM p N)⟩

@[simp]
theorem RestrictedBox.pullbackPairMergeExceptionalGraph_apply
    {p : ℕ} (D : RestrictedBox p) (N : ℕ)
    (f : RestrictedBox.analyticNearClosedBoxSubalgebra
      (restrictedPairMergeBox D))
    (w : RestrictedBoxSpace ((p + 1) + N)) :
    (D.pullbackPairMergeExceptionalGraph N f :
      RestrictedBoxSpace ((p + 1) + N) → ℝ) w =
      (f : RestrictedBoxSpace (p + 1) → ℝ)
        (restrictedPairMergeExceptionalGraphBoxDropCLM p N w) :=
  rfl

/-- On the graph box, the standard Abel offset is `eta` for a partner label
and `xi+eta` for a pivot label. -/
def restrictedPairMergeExceptionalGraphTargetOffset
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    RestrictedBox.analyticNearClosedBoxSubalgebra
      (restrictedPairMergeExceptionalGraphBox D
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) := by
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let q := restrictedPairMergeExceptionalOffsetEnumeration representative i j S t
  by_cases hq : representative q = i
  · exact ⟨fun w ↦ w (Fin.castAdd N (Fin.last p)) +
        w (Fin.natAdd (p + 1) t),
      RestrictedBox.AnalyticNearClosedBox.add
        (restrictedPairMergeExceptionalGraphBox D N)
        ((restrictedPairMergeExceptionalGraphBox D N).analyticNearClosedBox_apply
          (Fin.castAdd N (Fin.last p)))
        ((restrictedPairMergeExceptionalGraphBox D N).analyticNearClosedBox_apply
          (Fin.natAdd (p + 1) t))⟩
  · exact ⟨fun w ↦ w (Fin.natAdd (p + 1) t),
      (restrictedPairMergeExceptionalGraphBox D N).analyticNearClosedBox_apply
        (Fin.natAdd (p + 1) t)⟩

/-- The standard target argument represented by one graph coordinate. -/
def restrictedPairMergeExceptionalGraphTargetArgument
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) a → ℝ :=
  restrictedAbelArgument j
    (restrictedPairMergeExceptionalGraphTargetOffset D representative i j S t :
      RestrictedBoxSpace
        ((p + 1) +
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) → ℝ)

/-- Standard target jets associated to the finitely many graph offsets. -/
def restrictedPairMergeExceptionalGraphAbelJetGenerators
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    Set (RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) a → ℝ) :=
  Set.range fun tr :
      Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card × ℕ ↦
    restrictedAbelJet A j
      (restrictedPairMergeExceptionalGraphTargetOffset D representative i j S tr.1 :
        RestrictedBoxSpace
          ((p + 1) +
            (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) → ℝ)
      tr.2

theorem restrictedPairMergeExceptionalGraphTargetJet_mem_base
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
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
        (restrictedPairMergeExceptionalGraphAbelJetGenerators
          (a := a) A D representative i j S) := by
  apply specialGenerator_mem_base
  exact ⟨(t, r), rfl⟩

/-- Along the finite graph lift, a target Abel argument is exactly the
branch-dependent base argument plus its fixed-iterate shift. -/
theorem restrictedPairMergeExceptionalGraphTargetArgument_lift
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    (x : RestrictedSource (m + 1) (p + 1) a) :
    restrictedPairMergeExceptionalGraphTargetArgument
        (a := a) D representative i j S t
        (restrictedPairMergeExceptionalFiniteGraphLift
          D representative offset K k i j S x) =
      restrictedPairMergeExceptionalBaseArgument representative i j
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x +
        restrictedPairMergeExceptionalGraphShift
          D representative offset K k i j S t x := by
  let q := restrictedPairMergeExceptionalOffsetEnumeration representative i j S t
  by_cases hq : representative q = i
  · simp [restrictedPairMergeExceptionalGraphTargetArgument,
      restrictedPairMergeExceptionalGraphTargetOffset,
      restrictedPairMergeExceptionalBaseArgument,
      restrictedPairMergeExceptionalFiniteGraphLift,
      restrictedPairMergeExceptionalGraphLift, q, hq]
    ring
  · simp [restrictedPairMergeExceptionalGraphTargetArgument,
      restrictedPairMergeExceptionalGraphTargetOffset,
      restrictedPairMergeExceptionalBaseArgument,
      restrictedPairMergeExceptionalFiniteGraphLift,
      restrictedPairMergeExceptionalGraphLift, q, hq]

/-! ## Exact exceptional-jet identities on the graph -/

/-- A uniform presentation of the pivot and partner exceptional jets. -/
def restrictedPairMergeExceptionalJet
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (q : ι) (r : ℕ) : RestrictedSource (m + 1) (p + 1) a → ℝ :=
  fun x ↦ iteratedDeriv r A
    (E^[restrictedPairMergeExceptionalDepth representative K k i q]
        (restrictedPairMergeExceptionalBaseArgument representative i j q x) +
      (restrictedPairMergeExceptionalOldOffset D offset q :
        RestrictedBoxSpace (p + 1) → ℝ) x.1.2)

theorem restrictedPairMergeExceptionalJet_eq_pivot
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (q : ι) (hq : representative q = i) (r : ℕ) :
    restrictedPairMergeExceptionalJet (a := a)
        A D representative offset K k i j q r =
      restrictedPairMergePivotJet A D offset K k j q r := by
  funext x
  simp [restrictedPairMergeExceptionalJet,
    restrictedPairMergeExceptionalDepth,
    restrictedPairMergeExceptionalBaseArgument,
    restrictedPairMergeExceptionalOldOffset,
    restrictedPairMergePivotJet, hq]

theorem restrictedPairMergeExceptionalJet_eq_partner
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (q : ι) (hq : representative q = i.succAbove j) (r : ℕ) :
    restrictedPairMergeExceptionalJet (a := a)
        A D representative offset K k i j q r =
      restrictedPairMergePartnerJet A D offset K j q r := by
  have hne : representative q ≠ i := by
    rw [hq]
    exact Fin.succAbove_ne i j
  funext x
  simp [restrictedPairMergeExceptionalJet,
    restrictedPairMergeExceptionalDepth,
    restrictedPairMergeExceptionalBaseArgument,
    restrictedPairMergeExceptionalOldOffset,
    restrictedPairMergePartnerJet, hne]

/-- Every exceptional old jet is, along its graph, the corresponding
derivative evaluated after the appropriate fixed iterate of a standard
target argument. -/
theorem restrictedPairMergeExceptionalJet_eq_iterate_targetArgument
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    (r : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ (restrictedPairMergeBox D).closedBox,
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (htail : B + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox) :
    restrictedPairMergeExceptionalJet A D representative offset K k i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) r x =
      iteratedDeriv r A
        (E^[restrictedPairMergeExceptionalDepth representative K k i
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)]
          (restrictedPairMergeExceptionalGraphTargetArgument
            (a := a) D representative i j S t
            (restrictedPairMergeExceptionalFiniteGraphLift
              D representative offset K k i j S x))) := by
  have hs := restrictedPairMergeExceptionalShift_spec
    D representative offset (k := k) hK i j
    (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)
    hB hbB x htail hw
  rw [restrictedPairMergeExceptionalGraphTargetArgument_lift]
  unfold restrictedPairMergeExceptionalJet
  apply congrArg (iteratedDeriv r A)
  simp only [restrictedPairMergeExceptionalGraphShift]
  linarith [hs.2]

/-- The graph target argument remains positive on the quantitative tail. -/
theorem restrictedPairMergeExceptionalGraphTargetArgument_lift_pos
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ (restrictedPairMergeBox D).closedBox,
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (htail : B + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox) :
    0 < restrictedPairMergeExceptionalGraphTargetArgument
      (a := a) D representative i j S t
      (restrictedPairMergeExceptionalFiniteGraphLift
        D representative offset K k i j S x) := by
  have hs := (restrictedPairMergeExceptionalShift_spec
    D representative offset (k := k) hK i j
    (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)
    hB hbB x htail hw).1
  change restrictedPairMergeExceptionalGraphShift
    D representative offset K k i j S t x ∈ Ioo (-1) 1 at hs
  rw [restrictedPairMergeExceptionalGraphTargetArgument_lift]
  linarith [hs.1]

/-- For derivative order zero, the exceptional jet is already a standard
graph Abel jet plus the fixed integer iterate depth. -/
theorem IsAbel.restrictedPairMergeExceptionalJet_zero_eq_graphJet
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ (restrictedPairMergeBox D).closedBox,
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (htail : B + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox) :
    restrictedPairMergeExceptionalJet A D representative offset K k i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) 0 x =
      restrictedAbelJet A j
          (restrictedPairMergeExceptionalGraphTargetOffset
            D representative i j S t :
            RestrictedBoxSpace
              ((p + 1) +
                (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) → ℝ)
          0
          (restrictedPairMergeExceptionalFiniteGraphLift
            D representative offset K k i j S x) +
        (restrictedPairMergeExceptionalDepth representative K k i
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) : ℝ) := by
  rw [restrictedPairMergeExceptionalJet_eq_iterate_targetArgument
    A D representative offset hK i j S t 0 hB hbB x htail hw]
  let u := restrictedPairMergeExceptionalGraphTargetArgument
    (a := a) D representative i j S t
    (restrictedPairMergeExceptionalFiniteGraphLift
      D representative offset K k i j S x)
  have hu : 0 < u := restrictedPairMergeExceptionalGraphTargetArgument_lift_pos
    D representative offset hK i j S t hB hbB x htail hw
  simpa [u, restrictedPairMergeExceptionalGraphTargetArgument,
    restrictedAbelJet] using
    hA.abel_iterate hu
      (restrictedPairMergeExceptionalDepth representative K k i
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t))

/-- Exact normalized one-step substitution for an arbitrary positive-order
derivative.  This is the function-level algebraic identity available from
`realDerivativeJetSubstitutionData`. -/
theorem IsAbel.exp_mul_iteratedDeriv_succ_E
    {A : ℝ → ℝ} (hA : IsAbel A) {u : ℝ} (hu : 0 < u) (r : ℕ) :
    Real.exp (((r + 1 : ℕ) : ℝ) * u) *
        iteratedDeriv (r + 1) A (E u) =
      realCentralStirlingJet A u (r + 1) (Fin.last r) := by
  have h := (hA.realDerivativeJetSubstitutionData hu (r + 1)).normalized_sourceJet
    (Fin.last r)
  simpa using h

/-! ## Alignment with the maintained implicit-graph API -/

/-- Package the finitely many scalar shifts as a vector-valued graph. -/
def restrictedPairMergeExceptionalVectorShift
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    RestrictedSource (m + 1) (p + 1) a →
      (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ) :=
  fun x t ↦ restrictedPairMergeExceptionalGraphShift
    D representative offset K k i j S t x

/-- The simultaneous graph system.  Each component is literally the
maintained scalar `restrictedFixedIterateShiftGraphEquation`, with its own
offset and branch-dependent iterate depth. -/
def restrictedPairMergeExceptionalVectorGraphEquation
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ)) :
    (RestrictedSource (m + 1) (p + 1) a ×
      (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)) →
      (Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ) :=
  fun z t ↦
    restrictedFixedIterateShiftGraphEquation
      (restrictedPairMergeExceptionalDepth representative K k i
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t))
      (restrictedPairMergeBox D)
      (restrictedPairMergeExceptionalOldOffset D offset
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t))
      ((restrictedPairMergeExceptionalBaseArgument representative i j
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) z.1,
        z.1.1.2), z.2 t)

/-- The simultaneous graph system vanishes exactly along the finite shift
vector on the quantitative tail. -/
theorem restrictedPairMergeExceptionalVectorGraphEquation_on_shift
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (B : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card → ℝ)
    (hB : ∀ t, 0 ≤ B t)
    (hbB : ∀ t w, w ∈ (restrictedPairMergeBox D).closedBox →
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B t)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox)
    (htail : ∀ t, B t + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x) :
    restrictedPairMergeExceptionalVectorGraphEquation
        D representative offset K k i j S
        (x, restrictedPairMergeExceptionalVectorShift
          D representative offset K k i j S x) = 0 := by
  funext t
  exact restrictedFixedIterateShiftGraphEquation_on_shift
    (restrictedPairMergeExceptionalDepth_pos representative (k := k) hK i _)
    (restrictedPairMergeBox D)
    (restrictedPairMergeExceptionalOldOffset D offset
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t))
    (hB t) (hbB t) (htail t) hw

/-! ## Tower membership of the graph equations -/

/-- The branch-dependent base argument, now viewed on the enlarged graph
source rather than along the graph parametrization. -/
def restrictedPairMergeExceptionalGraphBaseArgument
    {m p a : ℕ}
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) a → ℝ :=
  fun z ↦
    if representative
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) = i
    then z.1.1 j + z.1.2
      (Fin.castAdd
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
        (Fin.last p))
    else z.1.1 j

/-- The graph equation as a function on the enlarged restricted source. -/
def restrictedPairMergeExceptionalRestrictedGraphEquation
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) a → ℝ :=
  fun z ↦
    E^[restrictedPairMergeExceptionalDepth representative K k i
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)]
      (restrictedPairMergeExceptionalGraphBaseArgument
          (a := a) representative i j S t z +
        z.1.2 (Fin.natAdd (p + 1) t)) -
    E^[restrictedPairMergeExceptionalDepth representative K k i
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)]
      (restrictedPairMergeExceptionalGraphBaseArgument
        (a := a) representative i j S t z) -
    (restrictedPairMergeExceptionalOldOffset D offset
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
      RestrictedBoxSpace (p + 1) → ℝ)
      (restrictedPairMergeExceptionalGraphBoxDropCLM p
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card z.1.2)

theorem restrictedPairMergeExceptionalRestrictedGraphEquation_on_lift
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ (restrictedPairMergeBox D).closedBox,
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (htail : B + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox) :
    restrictedPairMergeExceptionalRestrictedGraphEquation
      D representative offset K k i j S t
      (restrictedPairMergeExceptionalFiniteGraphLift
        D representative offset K k i j S x) = 0 := by
  have hs := restrictedFixedIterateShiftGraphEquation_on_shift
    (restrictedPairMergeExceptionalDepth_pos representative (k := k) hK i
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t))
    (restrictedPairMergeBox D)
    (restrictedPairMergeExceptionalOldOffset D offset
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t))
    hB hbB htail hw
  have hbase :
      restrictedPairMergeExceptionalGraphBaseArgument
          (a := a) representative i j S t
          (restrictedPairMergeExceptionalFiniteGraphLift
            D representative offset K k i j S x) =
        restrictedPairMergeExceptionalBaseArgument representative i j
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x := by
    let q := restrictedPairMergeExceptionalOffsetEnumeration representative i j S t
    by_cases hq : representative q = i
    · simp [restrictedPairMergeExceptionalGraphBaseArgument,
        restrictedPairMergeExceptionalFiniteGraphLift,
        restrictedPairMergeExceptionalGraphLift,
        restrictedPairMergeExceptionalBaseArgument, q, hq]
    · simp [restrictedPairMergeExceptionalGraphBaseArgument,
        restrictedPairMergeExceptionalFiniteGraphLift,
        restrictedPairMergeExceptionalGraphLift,
        restrictedPairMergeExceptionalBaseArgument, q, hq]
  have hdrop :
      restrictedPairMergeExceptionalGraphBoxDropCLM p
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
          (restrictedPairMergeExceptionalFiniteGraphLift
            D representative offset K k i j S x).1.2 = x.1.2 := by
    funext q
    simp [restrictedPairMergeExceptionalFiniteGraphLift,
      restrictedPairMergeExceptionalGraphLift]
  unfold restrictedPairMergeExceptionalRestrictedGraphEquation
  rw [hbase, restrictedPairMergeExceptionalFiniteGraphLift_graphCoordinate,
    hdrop]
  exact hs

/-- The branch-dependent graph base argument is already a fixed base
expression. -/
theorem restrictedPairMergeExceptionalGraphBaseArgument_mem_base
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    restrictedPairMergeExceptionalGraphBaseArgument
        (a := a) representative i j S t ∈
      restrictedExpressionBase
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
        (restrictedPairMergeExceptionalGraphAbelJetGenerators
          (a := a) A D representative i j S) := by
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let G := restrictedPairMergeExceptionalGraphAbelJetGenerators
    (a := a) A D representative i j S
  by_cases hq : representative
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) = i
  · have hmem := (restrictedExpressionBase
      (restrictedPairMergeExceptionalGraphBox D N) G).add_mem
      (restrictedSCoordinate_mem_base
        (restrictedPairMergeExceptionalGraphBox D N) G j)
      (restrictedWCoordinate_mem_base
        (restrictedPairMergeExceptionalGraphBox D N) G
        (Fin.castAdd N (Fin.last p)))
    convert hmem using 1
    funext z
    simp [restrictedPairMergeExceptionalGraphBaseArgument,
      restrictedSCoordinate, restrictedWCoordinate, hq, N]
  · have hmem := restrictedSCoordinate_mem_base
      (restrictedPairMergeExceptionalGraphBox D N) G j
    convert hmem using 1
    funext z
    simp [restrictedPairMergeExceptionalGraphBaseArgument,
      restrictedSCoordinate, hq, N]

/-- Every added graph coordinate is a fixed base expression. -/
theorem restrictedPairMergeExceptionalGraphCoordinate_mem_base
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    restrictedWCoordinate (m := m + 1) (a := a)
        (Fin.natAdd (p + 1) t) ∈
      restrictedExpressionBase
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
        (restrictedPairMergeExceptionalGraphAbelJetGenerators
          (a := a) A D representative i j S) :=
  restrictedWCoordinate_mem_base _ _ _

/-- The old analytic coefficient remains a fixed base expression after
forgetting the graph-coordinate block. -/
theorem restrictedPairMergeExceptionalOldOffset_graphPullback_mem_base
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    (fun z : RestrictedSource (m + 1)
        ((p + 1) +
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) a ↦
      (restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ)
        (restrictedPairMergeExceptionalGraphBoxDropCLM p
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card z.1.2)) ∈
      restrictedExpressionBase
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
        (restrictedPairMergeExceptionalGraphAbelJetGenerators
          (a := a) A D representative i j S) := by
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let G := restrictedPairMergeExceptionalGraphAbelJetGenerators
    (a := a) A D representative i j S
  let b := D.pullbackPairMergeExceptionalGraph N
    (restrictedPairMergeExceptionalOldOffset D offset
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t))
  change restrictedBoxCoefficientPullback (m := m + 1) (a := a)
    (b : RestrictedBoxSpace ((p + 1) + N) → ℝ) ∈
      restrictedExpressionBase
        (restrictedPairMergeExceptionalGraphBox D N) G
  exact restrictedBoxCoefficientPullback_mem_base
    (restrictedPairMergeExceptionalGraphBox D N) G b

/-- Each finite graph equation belongs to the terminal level of an explicit
two-orbit tower.  The first orbit generates `E^[d](v+eta)` and the second
generates `E^[d]v`; the analytic coefficient is already in the base. -/
theorem exists_tower_restrictedPairMergeExceptionalRestrictedGraphEquation
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    let d := restrictedPairMergeExceptionalDepth representative K k i
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)
    ∃ T : FiniteExponentialTower
        (restrictedExpressionBase
          (restrictedPairMergeExceptionalGraphBox D
            (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
          (restrictedPairMergeExceptionalGraphAbelJetGenerators
            (a := a) A D representative i j S)) (d + d),
      restrictedPairMergeExceptionalRestrictedGraphEquation
          D representative offset K k i j S t ∈ T.level (d + d) := by
  dsimp only
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let G := restrictedPairMergeExceptionalGraphAbelJetGenerators
    (a := a) A D representative i j S
  let base := restrictedExpressionBase
    (restrictedPairMergeExceptionalGraphBox D N) G
  let d := restrictedPairMergeExceptionalDepth representative K k i
    (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)
  let v := restrictedPairMergeExceptionalGraphBaseArgument
    (p := p) (a := a) representative i j S t
  let eta := restrictedWCoordinate (m := m + 1) (a := a)
    (Fin.natAdd (p + 1) t)
  let b : RestrictedSource (m + 1) ((p + 1) + N) a → ℝ :=
    fun z ↦
      (restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ)
        (restrictedPairMergeExceptionalGraphBoxDropCLM p N z.1.2)
  have hv : v ∈ base := by
    exact restrictedPairMergeExceptionalGraphBaseArgument_mem_base
      A D representative i j S t
  have heta : eta ∈ base := by
    exact restrictedPairMergeExceptionalGraphCoordinate_mem_base
      A D representative i j S t
  have hb : b ∈ base := by
    exact restrictedPairMergeExceptionalOldOffset_graphPullback_mem_base
      A D representative offset i j S t
  have hveta : v + eta ∈ base := base.add_mem hv heta
  let T₁ := iterateETower base (v + eta) d hveta
  have hv₁ : v ∈ T₁.level d := T₁.base_mem_level hv d
  let T₂ := iterateETower (T₁.level d) v d hv₁
  let T := T₁.append T₂
  refine ⟨T, ?_⟩
  have hfirst₀ := iterateE_mem_iterateETower_terminal base (v + eta) d hveta
  have hfirstD : (fun z ↦ E^[d] ((v + eta) z)) ∈ T.level d := by
    rw [show T.level d = T₁.level d by
      exact FiniteExponentialTower.append_level_left T₁ T₂ d le_rfl]
    exact hfirst₀
  have hfirst : (fun z ↦ E^[d] ((v + eta) z)) ∈ T.level (d + d) :=
    T.level_mono (Nat.le_add_right d d) hfirstD
  have hsecond₀ := iterateE_mem_iterateETower_terminal (T₁.level d) v d hv₁
  have hsecond : (fun z ↦ E^[d] (v z)) ∈ T.level (d + d) := by
    rw [show T.level (d + d) = T₂.level d by
      exact FiniteExponentialTower.append_level_right T₁ T₂ d]
    exact hsecond₀
  have hbT : b ∈ T.level (d + d) := T.base_mem_level hb (d + d)
  have hmem := (T.level (d + d)).sub_mem
    ((T.level (d + d)).sub_mem hfirst hsecond) hbT
  change (fun z ↦
    E^[d] (v z + eta z) - E^[d] (v z) - b z) ∈ T.level (d + d)
  change (fun z ↦
    E^[d] (v z + eta z) - E^[d] (v z) - b z) ∈ T.level (d + d) at hmem
  exact hmem

/-! ## Denominator-cleared arbitrary-order exceptional jets -/

/-- The standard target argument itself is a fixed base expression. -/
theorem restrictedPairMergeExceptionalGraphTargetArgument_mem_base
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) :
    restrictedPairMergeExceptionalGraphTargetArgument
        (a := a) D representative i j S t ∈
      restrictedExpressionBase
        (restrictedPairMergeExceptionalGraphBox D
          (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
        (restrictedPairMergeExceptionalGraphAbelJetGenerators
          (a := a) A D representative i j S) := by
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let G := restrictedPairMergeExceptionalGraphAbelJetGenerators
    (a := a) A D representative i j S
  let b := restrictedPairMergeExceptionalGraphTargetOffset
    D representative i j S t
  have hs := restrictedSCoordinate_mem_base
    (restrictedPairMergeExceptionalGraphBox D N) G j
  have hb := restrictedBoxCoefficientPullback_mem_base
    (restrictedPairMergeExceptionalGraphBox D N) G b
  have hsum := (restrictedExpressionBase
    (restrictedPairMergeExceptionalGraphBox D N) G).add_mem hs hb
  convert hsum using 1
  funext z
  rfl

/-- One finite orbit tower contains both the positive common denominator and
the denominator-cleared numerator for every derivative order at the chosen
exceptional graph argument. -/
theorem exists_tower_restrictedPairMergeExceptionalDerivativeData
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    (d r : ℕ) :
    let base := restrictedExpressionBase
      (restrictedPairMergeExceptionalGraphBox D
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
      (restrictedPairMergeExceptionalGraphAbelJetGenerators
        (a := a) A D representative i j S)
    let u := restrictedPairMergeExceptionalGraphTargetArgument
      (a := a) D representative i j S t
    ∃ T : FiniteExponentialTower base d,
      (fun z ↦ iteratedAbelDerivativeDenominator d r (u z)) ∈ T.level d ∧
      (fun z ↦ iteratedAbelDerivativeNumerator A d r (u z)) ∈ T.level d := by
  dsimp only
  let N := (restrictedPairMergeExceptionalOffsetSupport representative i j S).card
  let G := restrictedPairMergeExceptionalGraphAbelJetGenerators
    (a := a) A D representative i j S
  let base := restrictedExpressionBase
    (restrictedPairMergeExceptionalGraphBox D N) G
  let u := restrictedPairMergeExceptionalGraphTargetArgument
    (a := a) D representative i j S t
  have hu : u ∈ base := by
    exact restrictedPairMergeExceptionalGraphTargetArgument_mem_base
      A D representative i j S t
  let T := iterateETower base u d hu
  have hjet : ∀ q : ℕ,
      (fun z ↦ iteratedDeriv q A (u z)) ∈ T.level d := by
    intro q
    have hq := restrictedPairMergeExceptionalGraphTargetJet_mem_base
      (a := a) A D representative i j S t q
    have hqT := T.base_mem_level hq d
    change (fun z ↦ iteratedDeriv q A (u z)) ∈ T.level d
    exact hqT
  have horbit : ∀ e < d,
      (fun z ↦ Real.exp (E^[e] (u z))) ∈ T.level d := by
    intro e he
    have hg := T.generator_mem_level_of_lt (⟨e, he⟩ : Fin d) he
    change (fun z ↦ Real.exp (E^[e] (u z))) ∈ T.level d at hg
    exact hg
  have hden := iteratedAbelDerivativeDenominator_mem_subalgebra_bounded
    (T.level d) u d (fun e he q ↦
      realExp_nat_mul_mem_subalgebra (T.level d)
        (fun z ↦ E^[e] (u z)) (horbit e he) q) r
  have hnum := iteratedAbelDerivativeNumerator_mem_subalgebra_bounded_of_exp_orbit
    (T.level d) A u hjet d horbit r
  exact ⟨T, hden, hnum⟩

/-- Denominator clearing gives the exact arbitrary-order exceptional-jet
identity along the graph.  The right side is the tower member constructed
by `exists_tower_restrictedPairMergeExceptionalDerivativeData`, and the
denominator is everywhere positive. -/
theorem IsAbel.restrictedPairMergeExceptionalJet_denominator_mul_eq_numerator
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    {K k : ℕ} (hK : 1 ≤ K)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    (r : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbB : ∀ w ∈ (restrictedPairMergeBox D).closedBox,
      |(restrictedPairMergeExceptionalOldOffset D offset
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) :
        RestrictedBoxSpace (p + 1) → ℝ) w| ≤ B)
    (x : RestrictedSource (m + 1) (p + 1) a)
    (htail : B + 2 <
      restrictedPairMergeExceptionalBaseArgument representative i j
        (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) x)
    (hw : x.1.2 ∈ (restrictedPairMergeBox D).openBox) :
    let d := restrictedPairMergeExceptionalDepth representative K k i
      (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t)
    let u := restrictedPairMergeExceptionalGraphTargetArgument
      (a := a) D representative i j S t
      (restrictedPairMergeExceptionalFiniteGraphLift
        D representative offset K k i j S x)
    iteratedAbelDerivativeDenominator d r u *
        restrictedPairMergeExceptionalJet A D representative offset K k i j
          (restrictedPairMergeExceptionalOffsetEnumeration representative i j S t) r x =
      iteratedAbelDerivativeNumerator A d r u := by
  dsimp only
  rw [restrictedPairMergeExceptionalJet_eq_iterate_targetArgument
    A D representative offset hK i j S t r hB hbB x htail hw]
  exact hA.iteratedAbelDerivative_denominator_mul
    (restrictedPairMergeExceptionalGraphTargetArgument_lift_pos
      D representative offset hK i j S t hB hbB x htail hw) _ _

theorem restrictedPairMergeExceptionalJet_denominator_pos
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Finset (ι × ℕ))
    (t : Fin (restrictedPairMergeExceptionalOffsetSupport representative i j S).card)
    (d r : ℕ)
    (z : RestrictedSource (m + 1)
      ((p + 1) +
        (restrictedPairMergeExceptionalOffsetSupport representative i j S).card) a) :
    0 < iteratedAbelDerivativeDenominator d r
      (restrictedPairMergeExceptionalGraphTargetArgument
        (a := a) D representative i j S t z) :=
  iteratedAbelDerivativeDenominator_pos d r _

end AbelFormalization
