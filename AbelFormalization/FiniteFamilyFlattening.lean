import Mathlib.Algebra.BigOperators.Fin

/-!
# Flattening finite families of variable-length traces

This module turns a finite family of variable-length operation blocks into
one chronological finite trace.  The core equivalence remembers both the
cluster and the local operation index.  Prefix offsets and boundary indices
make its arithmetic convention explicit.

The final section specializes the construction to the three phases used by
an ordered-cluster transfer: a list of individual decrements, one first
simultaneous step, and a finite list of extra retained steps.  No polynomial,
ideal, or analytic data occurs here.
-/

set_option autoImplicit false

namespace AbelFormalization
namespace FiniteFamilyFlattening

open scoped BigOperators

universe u

/-! ## General finite flattening -/

/-- The total length of a finite family of operation blocks. -/
def totalCount {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) : ℕ :=
  ∑ c, length c

/-- The number of operations in clusters strictly before `boundary`.

The boundary type has one more element than the cluster type: zero is the
initial boundary and `Fin.last clusterCount` is the terminal boundary. -/
def prefixOffset {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (boundary : Fin (clusterCount + 1)) : ℕ :=
  ∑ c : Fin boundary,
    length (Fin.castLE (Nat.le_of_lt_succ boundary.isLt) c)

@[simp]
theorem prefixOffset_zero {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) :
    prefixOffset length 0 = 0 := by
  simp [prefixOffset]

/-- Crossing cluster `c` adds exactly its local length. -/
theorem prefixOffset_succ {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) (c : Fin clusterCount) :
    prefixOffset length c.succ =
      prefixOffset length c.castSucc + length c := by
  unfold prefixOffset
  change (∑ i : Fin (c.val + 1), length (Fin.castLE _ i)) =
    (∑ i : Fin c.val, length (Fin.castLE _ i)) + length c
  rw [Fin.sum_univ_castSucc]
  congr 1

/-- Prefix offsets strictly increase across positive-length blocks. -/
theorem prefixOffset_lt_succ {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c) (c : Fin clusterCount) :
    prefixOffset length c.castSucc < prefixOffset length c.succ := by
  rw [prefixOffset_succ]
  exact Nat.lt_add_of_pos_right (hpositive c)

/-- The terminal prefix offset is the full sum of local lengths. -/
@[simp]
theorem prefixOffset_last {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) :
    prefixOffset length (Fin.last clusterCount) = totalCount length := by
  unfold prefixOffset totalCount
  apply Finset.sum_congr rfl
  intro i _
  congr 1

/-- The canonical equivalence between a global operation index and its
dependent pair of cluster and local indices. -/
def flattenEquiv {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) :
    Fin (totalCount length) ≃ Σ c, Fin (length c) :=
  finSigmaFinEquiv.symm

/-- Insert one local operation into the global chronological index. -/
def flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    Fin (totalCount length) :=
  finSigmaFinEquiv ⟨c, i⟩

@[simp]
theorem flattenEquiv_flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    flattenEquiv length (flattenIndex length c i) = ⟨c, i⟩ := by
  exact finSigmaFinEquiv.symm_apply_apply ⟨c, i⟩

/-- Look up both dependent local coordinates of a global operation. -/
def lookup {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (j : Fin (totalCount length)) : Σ c, Fin (length c) :=
  flattenEquiv length j

/-- The cluster containing a global operation. -/
def lookupCluster {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (j : Fin (totalCount length)) : Fin clusterCount :=
  (lookup length j).1

/-- The local index of a global operation inside its cluster. -/
def lookupLocal {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (j : Fin (totalCount length)) :
    Fin (length (lookupCluster length j)) :=
  (lookup length j).2

@[simp]
theorem lookup_flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    lookup length (flattenIndex length c i) = ⟨c, i⟩ := by
  exact flattenEquiv_flattenIndex length c i

@[simp]
theorem lookupCluster_flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    lookupCluster length (flattenIndex length c i) = c := by
  simp [lookupCluster]

/-- Re-inserting the coordinates obtained by lookup returns the original
global index. -/
theorem flattenIndex_lookup {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (j : Fin (totalCount length)) :
    flattenIndex length (lookupCluster length j) (lookupLocal length j) = j := by
  exact finSigmaFinEquiv.apply_symm_apply j

/-- Look up a natural-number operation index when it lies inside the finite
trace.  This is the nondependent entry point for APIs whose stage index is
`Nat`. -/
def operationAt? {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) (j : ℕ) :
    Option (Σ c, Fin (length c)) :=
  if h : j < totalCount length then some (lookup length ⟨j, h⟩) else none

@[simp]
theorem operationAt?_flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    operationAt? length (flattenIndex length c i) = some ⟨c, i⟩ := by
  simp [operationAt?, lookup]

/-- Flatten an ordinary local operation family. -/
def operationFamily {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) {A : Sort u}
    (family : ∀ c, Fin (length c) → A)
    (j : Fin (totalCount length)) : A :=
  family (lookupCluster length j) (lookupLocal length j)

@[simp]
theorem operationFamily_flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) {A : Sort u}
    (family : ∀ c, Fin (length c) → A)
    (c : Fin clusterCount) (i : Fin (length c)) :
    operationFamily length family (flattenIndex length c i) = family c i := by
  unfold operationFamily
  change family (lookup length (flattenIndex length c i)).1
      (lookup length (flattenIndex length c i)).2 = family c i
  rw [lookup_flattenIndex]

/-- Extend an ordinary flattened operation family to all natural indices by
an explicit fallback value after the finite trace. -/
def natOperationFamily {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) {A : Sort u}
    (fallback : A) (family : ∀ c, Fin (length c) → A)
    (j : ℕ) : A :=
  if h : j < totalCount length then operationFamily length family ⟨j, h⟩
  else fallback

@[simp]
theorem natOperationFamily_flattenIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) {A : Sort u}
    (fallback : A) (family : ∀ c, Fin (length c) → A)
    (c : Fin clusterCount) (i : Fin (length c)) :
    natOperationFamily length fallback family (flattenIndex length c i) =
      family c i := by
  simp [natOperationFamily]

/-- The value of a global index is its cluster offset plus its local index. -/
theorem flattenIndex_val {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    (flattenIndex length c i : ℕ) =
      prefixOffset length c.castSucc + i := by
  rw [flattenIndex, finSigmaFinEquiv_apply]
  unfold prefixOffset
  congr 2

/-- A flattened local index lies in the exact half-open interval belonging
to its cluster. -/
theorem flattenIndex_mem_block {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (length c)) :
    prefixOffset length c.castSucc ≤ (flattenIndex length c i : ℕ) ∧
      (flattenIndex length c i : ℕ) < prefixOffset length c.succ := by
  rw [flattenIndex_val, prefixOffset_succ]
  omega

/-- The end offset of a positive-length block does not exceed the total. -/
theorem prefixOffset_succ_le_total {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c) (c : Fin clusterCount) :
    prefixOffset length c.succ ≤ totalCount length := by
  let i : Fin (length c) := ⟨length c - 1, by
    have := hpositive c
    omega⟩
  have hi := (flattenIndex length c i).isLt
  rw [flattenIndex_val] at hi
  rw [prefixOffset_succ]
  dsimp [i] at hi
  omega

/-- Every boundary offset of positive-length blocks is at most the total. -/
theorem prefixOffset_le_total {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c)
    (boundary : Fin (clusterCount + 1)) :
    prefixOffset length boundary ≤ totalCount length := by
  refine Fin.cases ?_ (fun c ↦ ?_) boundary
  · simp
  · exact prefixOffset_succ_le_total length hpositive c

/-! ## Global boundaries and Nat-indexed dependent families -/

/-- Insert a local boundary into the global boundary sequence. -/
def boundaryIndex {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c)
    (c : Fin clusterCount) (i : Fin (length c + 1)) :
    Fin (totalCount length + 1) :=
  ⟨prefixOffset length c.castSucc + i, by
    have hfinish := prefixOffset_succ_le_total length hpositive c
    rw [prefixOffset_succ] at hfinish
    omega⟩

@[simp]
theorem boundaryIndex_val {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c)
    (c : Fin clusterCount) (i : Fin (length c + 1)) :
    (boundaryIndex length hpositive c i : ℕ) =
      prefixOffset length c.castSucc + i := rfl

/-- The boundary after a local operation is the successor of that operation's
global index. -/
theorem boundaryIndex_succ {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c)
    (c : Fin clusterCount) (i : Fin (length c)) :
    boundaryIndex length hpositive c i.succ =
      (flattenIndex length c i).succ := by
  apply Fin.ext
  change prefixOffset length c.castSucc + (i.val + 1) =
    (flattenIndex length c i : ℕ) + 1
  rw [flattenIndex_val]
  omega

/-- Adjacent clusters assign their shared local boundaries the same global
boundary index. -/
theorem boundaryIndex_terminal_eq_initial {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c)
    {c next : Fin clusterCount} (hnext : next.val = c.val + 1) :
    boundaryIndex length hpositive c (Fin.last (length c)) =
      boundaryIndex length hpositive next 0 := by
  apply Fin.ext
  simp only [boundaryIndex_val, Fin.val_last, Fin.val_zero, add_zero]
  rw [← prefixOffset_succ]
  congr 1
  apply Fin.ext
  exact hnext.symm

/-- The first local boundary is the first global boundary. -/
theorem boundaryIndex_first {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c) (hcount : 0 < clusterCount) :
    boundaryIndex length hpositive ⟨0, hcount⟩ 0 = 0 := by
  apply Fin.ext
  simp [boundaryIndex, prefixOffset]

/-- The index of the last cluster of a nonempty finite cluster family. -/
def lastClusterIndex {clusterCount : ℕ}
    (hcount : 0 < clusterCount) : Fin clusterCount :=
  ⟨clusterCount - 1, by omega⟩

@[simp]
theorem lastClusterIndex_val {clusterCount : ℕ}
    (hcount : 0 < clusterCount) :
    (lastClusterIndex hcount : ℕ) = clusterCount - 1 := rfl

theorem lastClusterIndex_succ {clusterCount : ℕ}
    (hcount : 0 < clusterCount) :
    (lastClusterIndex hcount).succ = Fin.last clusterCount := by
  apply Fin.ext
  simp [lastClusterIndex]
  omega

/-- The last local boundary of the last cluster is the terminal global
boundary. -/
theorem boundaryIndex_last {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (hpositive : ∀ c, 0 < length c) (hcount : 0 < clusterCount) :
    boundaryIndex length hpositive (lastClusterIndex hcount)
        (Fin.last (length (lastClusterIndex hcount))) =
      Fin.last (totalCount length) := by
  apply Fin.ext
  change prefixOffset length (lastClusterIndex hcount).castSucc +
      length (lastClusterIndex hcount) = totalCount length
  rw [← prefixOffset_succ, lastClusterIndex_succ, prefixOffset_last]

/-- Clamp a natural stage to the terminal boundary.  This extends a finite
boundary family to the all-natural-number indexing used by trace APIs. -/
def clampBoundary (total j : ℕ) : Fin (total + 1) :=
  ⟨min j total, by omega⟩

@[simp]
theorem clampBoundary_of_le {total j : ℕ} (h : j ≤ total) :
    clampBoundary total j = ⟨j, Nat.lt_succ_of_le h⟩ := by
  apply Fin.ext
  simp [clampBoundary, h]

/-- Flatten a dependent family of local operation sorts. -/
def dependentOperationFamily {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (family : ∀ c, Fin (length c) → Sort u)
    (j : Fin (totalCount length)) : Sort u :=
  family (lookupCluster length j) (lookupLocal length j)

/-- Extend a flattened dependent operation family to `ℕ` with an explicit
fallback sort outside the finite trace. -/
def natDependentOperationFamily {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ)
    (fallback : Sort u) (family : ∀ c, Fin (length c) → Sort u)
    (j : ℕ) : Sort u :=
  if h : j < totalCount length then
    dependentOperationFamily length family ⟨j, h⟩
  else fallback

/-- At every genuine global operation, the Nat-indexed dependent extension
reduces to the original local family. -/
@[simp]
theorem natDependentOperationFamily_flattenIndex
    {clusterCount : ℕ} (length : Fin clusterCount → ℕ)
    (fallback : Sort u) (family : ∀ c, Fin (length c) → Sort u)
    (c : Fin clusterCount) (i : Fin (length c)) :
    natDependentOperationFamily length fallback family
        (flattenIndex length c i) = family c i := by
  unfold natDependentOperationFamily
  simp only [Fin.isLt, ↓reduceDIte]
  unfold dependentOperationFamily
  change family (lookup length (flattenIndex length c i)).1
      (lookup length (flattenIndex length c i)).2 = family c i
  rw [lookup_flattenIndex]

/-! ## Concatenating compatible boundary families -/

/-- Local boundary families with explicit identifications at cluster seams.

Taking `A := Type u` makes the fields literal type equalities.  Data living
in those types can then be moved with the explicit transport function below;
no equality between unrelated local types is inferred by the combinator. -/
structure CompatibleBoundaryFamily {clusterCount : ℕ}
    (length : Fin clusterCount → ℕ) (A : Type*) where
  initial : A
  boundary : ∀ c, Fin (length c + 1) → A
  initial_eq_first : ∀ h : 0 < clusterCount,
    initial = boundary ⟨0, h⟩ 0
  terminal_eq_next : ∀ {c next : Fin clusterCount},
    next.val = c.val + 1 →
      boundary c (Fin.last (length c)) = boundary next 0

/-- Concatenate compatible local boundary families.  A positive global
boundary is represented by the output boundary of its preceding operation. -/
def CompatibleBoundaryFamily.concatenate
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A) :
    Fin (totalCount length + 1) → A :=
  Fin.cases family.initial fun j ↦
    family.boundary (lookupCluster length j) (lookupLocal length j).succ

@[simp]
theorem CompatibleBoundaryFamily.concatenate_zero
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A) :
    family.concatenate 0 = family.initial := rfl

/-- Concatenation preserves every positive local boundary literally. -/
theorem CompatibleBoundaryFamily.concatenate_boundaryIndex_succ
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A)
    (hpositive : ∀ c, 0 < length c)
    (c : Fin clusterCount) (i : Fin (length c)) :
    family.concatenate (boundaryIndex length hpositive c i.succ) =
      family.boundary c i.succ := by
  rw [boundaryIndex_succ]
  change family.boundary (lookup length (flattenIndex length c i)).1
      (lookup length (flattenIndex length c i)).2.succ =
    family.boundary c i.succ
  rw [lookup_flattenIndex]

/-- Concatenation preserves the terminal boundary of every positive-length
cluster. -/
theorem CompatibleBoundaryFamily.concatenate_boundaryIndex_terminal
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A)
    (hpositive : ∀ c, 0 < length c) (c : Fin clusterCount) :
    family.concatenate
        (boundaryIndex length hpositive c (Fin.last (length c))) =
      family.boundary c (Fin.last (length c)) := by
  let i : Fin (length c) := ⟨length c - 1, by
    have := hpositive c
    omega⟩
  have hi : i.succ = Fin.last (length c) := by
    apply Fin.ext
    have hc := hpositive c
    simp [i]
    omega
  rw [← hi, family.concatenate_boundaryIndex_succ]

/-- At a cluster seam, the concatenated boundary is the next cluster's
explicitly identified initial boundary. -/
theorem CompatibleBoundaryFamily.concatenate_seam
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A)
    (hpositive : ∀ c, 0 < length c)
    {c next : Fin clusterCount} (hnext : next.val = c.val + 1) :
    family.concatenate
        (boundaryIndex length hpositive c (Fin.last (length c))) =
      family.boundary next 0 := by
  rw [family.concatenate_boundaryIndex_terminal]
  exact family.terminal_eq_next hnext

/-- Concatenation preserves the first local boundary through the supplied
initial identification. -/
theorem CompatibleBoundaryFamily.concatenate_first
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A)
    (hpositive : ∀ c, 0 < length c) (hcount : 0 < clusterCount) :
    family.concatenate
        (boundaryIndex length hpositive ⟨0, hcount⟩ 0) =
      family.boundary ⟨0, hcount⟩ 0 := by
  rw [boundaryIndex_first, family.concatenate_zero,
    family.initial_eq_first hcount]

/-- Concatenation preserves the last local boundary at the global endpoint. -/
theorem CompatibleBoundaryFamily.concatenate_last
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A)
    (hpositive : ∀ c, 0 < length c) (hcount : 0 < clusterCount) :
    family.concatenate (Fin.last (totalCount length)) =
      family.boundary (lastClusterIndex hcount)
        (Fin.last (length (lastClusterIndex hcount))) := by
  rw [← boundaryIndex_last length hpositive hcount]
  exact family.concatenate_boundaryIndex_terminal hpositive _

/-- The Nat-indexed boundary family obtained by clamping after the finite
terminal stage. -/
def CompatibleBoundaryFamily.natFamily
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A) (j : ℕ) : A :=
  family.concatenate (clampBoundary (totalCount length) j)

@[simp]
theorem CompatibleBoundaryFamily.natFamily_zero
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A) :
    family.natFamily 0 = family.initial := by
  simp [CompatibleBoundaryFamily.natFamily, clampBoundary]

@[simp]
theorem CompatibleBoundaryFamily.natFamily_total
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A) :
    family.natFamily (totalCount length) =
      family.concatenate (Fin.last (totalCount length)) := by
  unfold CompatibleBoundaryFamily.natFamily
  congr 1
  apply Fin.ext
  simp [clampBoundary]

/-- At the successor of a flattened operation, the Nat-indexed family is
the corresponding local output boundary. -/
theorem CompatibleBoundaryFamily.natFamily_succ_flattenIndex
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ} {A : Type*}
    (family : CompatibleBoundaryFamily length A)
    (hpositive : ∀ c, 0 < length c)
    (c : Fin clusterCount) (i : Fin (length c)) :
    family.natFamily ((flattenIndex length c i : ℕ) + 1) =
      family.boundary c i.succ := by
  unfold CompatibleBoundaryFamily.natFamily
  have hle : (flattenIndex length c i : ℕ) + 1 ≤ totalCount length :=
    (flattenIndex length c i).isLt
  rw [clampBoundary_of_le hle]
  change family.concatenate (flattenIndex length c i).succ = _
  rw [← boundaryIndex_succ length hpositive]
  exact family.concatenate_boundaryIndex_succ hpositive c i

/-- Explicitly transport dependent data from a local output boundary to the
corresponding Nat-indexed global boundary. -/
def CompatibleBoundaryFamily.transportAfter
    {clusterCount : ℕ} {length : Fin clusterCount → ℕ}
    (family : CompatibleBoundaryFamily length (Type u))
    (hpositive : ∀ c, 0 < length c)
    (c : Fin clusterCount) (i : Fin (length c))
    (x : family.boundary c i.succ) :
    family.natFamily ((flattenIndex length c i : ℕ) + 1) :=
  Eq.mp (family.natFamily_succ_flattenIndex hpositive c i).symm x

/-! ## Ordered-cluster transfer phases -/

/-- The three kinds of transfer operation belonging to one ordered cluster. -/
inductive ClusterTransferOperation
    (individualCount extraRetainedCount : ℕ) where
  | individual : Fin individualCount →
      ClusterTransferOperation individualCount extraRetainedCount
  | firstSimultaneous :
      ClusterTransferOperation individualCount extraRetainedCount
  | extraRetained : Fin extraRetainedCount →
      ClusterTransferOperation individualCount extraRetainedCount

/-- Split a cluster transfer operation into its three finite summands. -/
def clusterTransferOperationSumEquiv
    (individualCount extraRetainedCount : ℕ) :
    ClusterTransferOperation individualCount extraRetainedCount ≃
      Fin individualCount ⊕ (Fin 1 ⊕ Fin extraRetainedCount) where
  toFun
    | .individual i => Sum.inl i
    | .firstSimultaneous => Sum.inr (Sum.inl 0)
    | .extraRetained i => Sum.inr (Sum.inr i)
  invFun
    | Sum.inl i => .individual i
    | Sum.inr (Sum.inl _) => .firstSimultaneous
    | Sum.inr (Sum.inr i) => .extraRetained i
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with i | i
    · rfl
    · rcases i with i | i
      · rcases i with ⟨i, hi⟩
        have : i = 0 := by omega
        subst i
        rfl
      · rfl

/-- Chronological local numbering: individual operations, the first
simultaneous operation, then the extra retained operations. -/
def clusterTransferOperationFinEquiv
    (individualCount extraRetainedCount : ℕ) :
    ClusterTransferOperation individualCount extraRetainedCount ≃
      Fin (individualCount + 1 + extraRetainedCount) :=
  (clusterTransferOperationSumEquiv individualCount extraRetainedCount).trans
    ((Equiv.sumCongr (Equiv.refl (Fin individualCount)) finSumFinEquiv).trans
      (finSumFinEquiv.trans
        (finCongr (Nat.add_assoc individualCount 1 extraRetainedCount).symm)))

@[simp]
theorem clusterTransferOperationFinEquiv_individual
    {individualCount extraRetainedCount : ℕ} (i : Fin individualCount) :
    (clusterTransferOperationFinEquiv individualCount extraRetainedCount
        (.individual i) : ℕ) = i := by
  simp [clusterTransferOperationFinEquiv, clusterTransferOperationSumEquiv,
    finSumFinEquiv_apply_left]

@[simp]
theorem clusterTransferOperationFinEquiv_firstSimultaneous
    (individualCount extraRetainedCount : ℕ) :
    (clusterTransferOperationFinEquiv individualCount extraRetainedCount
        .firstSimultaneous : ℕ) = individualCount := by
  simp [clusterTransferOperationFinEquiv, clusterTransferOperationSumEquiv,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

@[simp]
theorem clusterTransferOperationFinEquiv_extraRetained
    {individualCount extraRetainedCount : ℕ} (i : Fin extraRetainedCount) :
    (clusterTransferOperationFinEquiv individualCount extraRetainedCount
        (.extraRetained i) : ℕ) = individualCount + 1 + i := by
  simp [clusterTransferOperationFinEquiv, clusterTransferOperationSumEquiv,
    finSumFinEquiv_apply_right]
  omega

/-- The operation count of one cluster's three transfer phases. -/
abbrev clusterTransferLength {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount) : ℕ :=
  individualCount c + 1 + extraRetainedCount c

theorem clusterTransferLength_pos {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount) :
    0 < clusterTransferLength individualCount extraRetainedCount c := by
  unfold clusterTransferLength
  omega

/-- The total number of transfer operations in all ordered clusters. -/
abbrev totalClusterTransferCount {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ) : ℕ :=
  totalCount (clusterTransferLength individualCount extraRetainedCount)

/-- Enumerate all three-phase operations across all ordered clusters. -/
def orderedClusterTransferEquiv {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ) :
    Fin (totalClusterTransferCount individualCount extraRetainedCount) ≃
      Σ c, ClusterTransferOperation
        (individualCount c) (extraRetainedCount c) :=
  (flattenEquiv
      (clusterTransferLength individualCount extraRetainedCount)).trans
    (Equiv.sigmaCongrRight fun c ↦
      (clusterTransferOperationFinEquiv
        (individualCount c) (extraRetainedCount c)).symm)

/-- Insert a named local transfer operation into the global trace. -/
def clusterTransferIndex {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount)
    (operation : ClusterTransferOperation
      (individualCount c) (extraRetainedCount c)) :
    Fin (totalClusterTransferCount individualCount extraRetainedCount) :=
  flattenIndex (clusterTransferLength individualCount extraRetainedCount) c
    (clusterTransferOperationFinEquiv
      (individualCount c) (extraRetainedCount c) operation)

@[simp]
theorem orderedClusterTransferEquiv_clusterTransferIndex
    {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount)
    (operation : ClusterTransferOperation
      (individualCount c) (extraRetainedCount c)) :
    orderedClusterTransferEquiv individualCount extraRetainedCount
        (clusterTransferIndex individualCount extraRetainedCount c operation) =
      ⟨c, operation⟩ := by
  unfold orderedClusterTransferEquiv clusterTransferIndex
  rw [Equiv.trans_apply, flattenEquiv_flattenIndex]
  change (⟨c, (clusterTransferOperationFinEquiv
        (individualCount c) (extraRetainedCount c)).symm
          (clusterTransferOperationFinEquiv
            (individualCount c) (extraRetainedCount c) operation)⟩ :
      Σ c, ClusterTransferOperation
        (individualCount c) (extraRetainedCount c)) =
    (⟨c, operation⟩ : Σ c, ClusterTransferOperation
      (individualCount c) (extraRetainedCount c))
  rw [Equiv.symm_apply_apply]

@[simp]
theorem clusterTransferIndex_individual_val
    {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (individualCount c)) :
    (clusterTransferIndex individualCount extraRetainedCount c
        (.individual i) : ℕ) =
      prefixOffset
          (clusterTransferLength individualCount extraRetainedCount)
          c.castSucc + i := by
  calc
    (clusterTransferIndex individualCount extraRetainedCount c
        (.individual i) : ℕ) =
        prefixOffset
            (clusterTransferLength individualCount extraRetainedCount)
            c.castSucc +
          (clusterTransferOperationFinEquiv
            (individualCount c) (extraRetainedCount c)
            (.individual i) : ℕ) := by
      exact flattenIndex_val
        (clusterTransferLength individualCount extraRetainedCount) c _
    _ = _ := by simp

@[simp]
theorem clusterTransferIndex_firstSimultaneous_val
    {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount) :
    (clusterTransferIndex individualCount extraRetainedCount c
        .firstSimultaneous : ℕ) =
      prefixOffset
          (clusterTransferLength individualCount extraRetainedCount)
          c.castSucc + individualCount c := by
  calc
    (clusterTransferIndex individualCount extraRetainedCount c
        .firstSimultaneous : ℕ) =
        prefixOffset
            (clusterTransferLength individualCount extraRetainedCount)
            c.castSucc +
          (clusterTransferOperationFinEquiv
            (individualCount c) (extraRetainedCount c)
            .firstSimultaneous : ℕ) := by
      exact flattenIndex_val
        (clusterTransferLength individualCount extraRetainedCount) c _
    _ = _ := by simp

@[simp]
theorem clusterTransferIndex_extraRetained_val
    {clusterCount : ℕ}
    (individualCount extraRetainedCount : Fin clusterCount → ℕ)
    (c : Fin clusterCount) (i : Fin (extraRetainedCount c)) :
    (clusterTransferIndex individualCount extraRetainedCount c
        (.extraRetained i) : ℕ) =
      prefixOffset
          (clusterTransferLength individualCount extraRetainedCount)
          c.castSucc + individualCount c + 1 + i := by
  calc
    (clusterTransferIndex individualCount extraRetainedCount c
        (.extraRetained i) : ℕ) =
        prefixOffset
            (clusterTransferLength individualCount extraRetainedCount)
            c.castSucc +
          (clusterTransferOperationFinEquiv
            (individualCount c) (extraRetainedCount c)
            (.extraRetained i) : ℕ) := by
      exact flattenIndex_val
        (clusterTransferLength individualCount extraRetainedCount) c _
    _ = _ := by
      simp
      omega

/-- Total transfer count when the individual phases are actual operation
lists rather than bare lengths. -/
def totalClusterTransferCountOfLists
    {clusterCount : ℕ} {Block : Fin clusterCount → Type u}
    (individualSteps : ∀ c, List (Block c))
    (extraRetainedCount : Fin clusterCount → ℕ) : ℕ :=
  totalClusterTransferCount (fun c ↦ (individualSteps c).length)
    extraRetainedCount

/-- Enumerate variable-length individual operation lists together with the
first simultaneous and extra retained operations of every cluster. -/
def orderedClusterTransferEquivOfLists
    {clusterCount : ℕ} {Block : Fin clusterCount → Type u}
    (individualSteps : ∀ c, List (Block c))
    (extraRetainedCount : Fin clusterCount → ℕ) :
    Fin (totalClusterTransferCountOfLists
      individualSteps extraRetainedCount) ≃
      Σ c, ClusterTransferOperation
        (individualSteps c).length (extraRetainedCount c) :=
  orderedClusterTransferEquiv (fun c ↦ (individualSteps c).length)
    extraRetainedCount

/-- Read the selected block stored at an individual-operation index. -/
def individualStepAt
    {clusterCount : ℕ} {Block : Fin clusterCount → Type u}
    (individualSteps : ∀ c, List (Block c)) (c : Fin clusterCount)
    (i : Fin (individualSteps c).length) : Block c :=
  (individualSteps c).get i

end FiniteFamilyFlattening
end AbelFormalization
