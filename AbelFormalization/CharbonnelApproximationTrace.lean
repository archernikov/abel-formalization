import AbelFormalization.CharbonnelApproximationModuli

/-!
# Trace descent for Charbonnel approximations

This file formalizes the recursive mechanism in Wilkie's Lemma 3.3.  At a
successor parameter depth, the last positive parameter is sent to zero and
the approximating set is replaced by the zero trace of the closure of its
positive-last-coordinate part.  The first error parameter is halved, exactly
as in Wilkie's proof, so that taking a limit preserves a strict error bound.

The two set-family facts imported by the paper from Charbonnel's Theorems 2.1
and 2.2 are kept in the explicit interface
`CharbonnelApproximationTraceTameness`: closure preserves membership and empty
interior, and the positive zero trace preserves membership and empty interior.
These facts are not consequences of topology for arbitrary sets.  No
complement closure is assumed here.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AbelFormalization

set_option autoImplicit false

/-! ## Halving the first approximation parameter -/

/-- Replace the first coordinate of a positive parameter vector by half of
it, leaving every later coordinate unchanged. -/
def charbonnelHalveFirstParameter {k : ℕ}
    (ε : RealEuclidean (k + 1)) : RealEuclidean (k + 1) :=
  Fin.cases (ε 0 / 2) (fun i ↦ ε i.succ)

@[simp]
theorem charbonnelHalveFirstParameter_zero {k : ℕ}
    (ε : RealEuclidean (k + 1)) :
    charbonnelHalveFirstParameter ε 0 = ε 0 / 2 := by
  simp [charbonnelHalveFirstParameter]

@[simp]
theorem charbonnelHalveFirstParameter_succ {k : ℕ}
    (ε : RealEuclidean (k + 1)) (i : Fin k) :
    charbonnelHalveFirstParameter ε i.succ = ε i.succ := by
  simp [charbonnelHalveFirstParameter]

theorem charbonnelHalveFirstParameter_pos {k : ℕ}
    {ε : RealEuclidean (k + 1)} (hε : ∀ i, 0 < ε i) :
    ∀ i, 0 < charbonnelHalveFirstParameter ε i := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using half_pos (hε 0)
  · simpa using hε j.succ

@[simp]
theorem charbonnelHalveFirstParameter_init {k : ℕ}
    (ε : RealEuclidean ((k + 1) + 1)) :
    Fin.init (charbonnelHalveFirstParameter ε) =
      charbonnelHalveFirstParameter (Fin.init ε) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;>
    simp [charbonnelHalveFirstParameter, Fin.init]

@[simp]
theorem charbonnelHalveFirstParameter_last {k : ℕ}
    (ε : RealEuclidean ((k + 1) + 1)) :
    charbonnelHalveFirstParameter ε (Fin.last (k + 1)) =
      ε (Fin.last (k + 1)) := by
  have hi : Fin.last (k + 1) = (Fin.last k).succ := Fin.ext rfl
  rw [hi]
  exact charbonnelHalveFirstParameter_succ ε (Fin.last k)

namespace CharbonnelModulus

/-- Wilkie's reduced modulus after replacing the first error parameter by
half of itself. -/
def halveFirst : {k : ℕ} → CharbonnelModulus k → CharbonnelModulus k
  | 0, .base bound hbound => .base bound hbound
  | k + 1, .step initial lastBound hlast =>
      .step (halveFirst initial)
        (fun ε ↦ lastBound (charbonnelHalveFirstParameter ε))
        (fun ε hε ↦ hlast _ (charbonnelHalveFirstParameter_pos hε))

/-- Every bounded modulus vector has positive coordinates. -/
theorem IsBounded.coord_pos : ∀ {k : ℕ}
    {modulus : CharbonnelModulus k}
    {ε : RealEuclidean (k + 1)},
    modulus.IsBounded ε → ∀ i, 0 < ε i := by
  intro k
  induction k with
  | zero =>
      intro modulus ε hε i
      cases modulus with
      | base bound hbound =>
          exact Fin.cases hε.1 (fun i ↦ Fin.elim0 i) i
  | succ k ih =>
      intro modulus ε hε i
      cases modulus with
      | step initial lastBound hlast =>
          refine Fin.lastCases hε.2.1 (fun j ↦ ?_) i
          exact ih hε.1 j

/-- Boundedness for the reduced modulus means that halving the first
coordinate produces a vector bounded by the original modulus. -/
theorem halveFirst_isBounded : ∀ {k : ℕ}
    (modulus : CharbonnelModulus k)
    (ε : RealEuclidean (k + 1)),
    (halveFirst modulus).IsBounded ε →
      modulus.IsBounded (charbonnelHalveFirstParameter ε) := by
  intro k
  induction k with
  | zero =>
      intro modulus ε hε
      cases modulus with
      | base bound hbound =>
          constructor
          · exact half_pos hε.1
          · exact (half_lt_self hε.1).trans hε.2
  | succ k ih =>
      intro modulus ε hε
      cases modulus with
      | step initial lastBound hlast =>
          constructor
          · simpa using ih initial (Fin.init ε) hε.1
          · constructor
            · simpa using hε.2.1
            · simpa using hε.2.2

end CharbonnelModulus

/-! ## The positive zero trace -/

/-- Append one scalar as the final coordinate of a finite real vector. -/
def charbonnelAppendLastCoordinate {d : ℕ}
    (x : RealEuclidean d) (t : ℝ) : RealEuclidean (d + 1) :=
  realEuclideanAppend x (fun _ : Fin 1 ↦ t)

@[simp]
theorem charbonnelAppendLastCoordinate_castAdd {d : ℕ}
    (x : RealEuclidean d) (t : ℝ) (i : Fin d) :
    charbonnelAppendLastCoordinate x t (Fin.castAdd 1 i) = x i := by
  simp [charbonnelAppendLastCoordinate]

@[simp]
theorem charbonnelAppendLastCoordinate_castSucc {d : ℕ}
    (x : RealEuclidean d) (t : ℝ) (i : Fin d) :
    charbonnelAppendLastCoordinate x t i.castSucc = x i := by
  have hi : i.castSucc = Fin.castAdd 1 i := Fin.ext rfl
  rw [hi]
  exact charbonnelAppendLastCoordinate_castAdd x t i

@[simp]
theorem charbonnelAppendLastCoordinate_last {d : ℕ}
    (x : RealEuclidean d) (t : ℝ) :
    charbonnelAppendLastCoordinate x t (Fin.last d) = t := by
  have hi : Fin.last d = Fin.natAdd d (0 : Fin 1) := Fin.ext rfl
  rw [hi]
  simp [charbonnelAppendLastCoordinate]

/-- Reassociate a visible block, a stored-parameter block, and one final
coordinate in the flat Euclidean representation. -/
theorem charbonnelAppendLastCoordinate_append {n k : ℕ}
    (x : RealEuclidean n) (u : RealEuclidean k) (t : ℝ) :
    charbonnelAppendLastCoordinate (realEuclideanAppend x u) t =
      realEuclideanAppend x
        (realEuclideanAppend u (fun _ : Fin 1 ↦ t)) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun c ↦ ?_) i
  · refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) j
    · rw [charbonnelAppendLastCoordinate_castAdd,
        realEuclideanAppend_castAdd]
      have hi : Fin.castAdd 1 (Fin.castAdd k a) =
          Fin.castAdd (k + 1) a := Fin.ext rfl
      rw [hi, realEuclideanAppend_castAdd]
    · rw [charbonnelAppendLastCoordinate_castAdd,
        realEuclideanAppend_natAdd]
      have hi : Fin.castAdd 1 (Fin.natAdd n b) =
          Fin.natAdd n (Fin.castAdd 1 b) := Fin.ext rfl
      rw [hi, realEuclideanAppend_natAdd, realEuclideanAppend_castAdd]
  · have hc : c = (0 : Fin 1) := Subsingleton.elim _ _
    subst c
    have hlastIndex : Fin.natAdd (n + k) (0 : Fin 1) =
        Fin.last (n + k) := Fin.ext rfl
    rw [hlastIndex, charbonnelAppendLastCoordinate_last]
    have hi : Fin.last (n + k) =
        Fin.natAdd n (Fin.natAdd k (0 : Fin 1)) := Fin.ext rfl
    rw [hi, realEuclideanAppend_natAdd, realEuclideanAppend_natAdd]

@[simp]
theorem charbonnelAppendLastCoordinate_append_parameter {n k : ℕ}
    (x : RealEuclidean n) (u : RealEuclidean k) (t : ℝ) (b : Fin k) :
    charbonnelAppendLastCoordinate (realEuclideanAppend x u) t
        (Fin.natAdd n b.castSucc) = u b := by
  have hi : Fin.natAdd n b.castSucc = (Fin.natAdd n b).castSucc := Fin.ext rfl
  rw [hi, charbonnelAppendLastCoordinate_castSucc,
    realEuclideanAppend_natAdd]

/-- Restrict a set to points whose final coordinate is positive. -/
def charbonnelPositiveLastPart {d : ℕ}
    (S : Set (RealEuclidean (d + 1))) : Set (RealEuclidean (d + 1)) :=
  S ∩ {v | 0 < v (Fin.last d)}

/-- Set the last positive parameter equal to zero after first taking the
closure.  Restricting to the positive part makes the hypothesis of
Charbonnel's Theorem 2.2 explicit. -/
def charbonnelPositiveZeroTrace {d : ℕ}
    (S : Set (RealEuclidean (d + 1))) : Set (RealEuclidean d) :=
  {x | charbonnelAppendLastCoordinate x 0 ∈
    closure (charbonnelPositiveLastPart S)}

/-- Append a final approximation parameter. -/
def charbonnelAppendLastParameter {k : ℕ}
    (ε : RealEuclidean (k + 1)) (η : ℝ) :
    RealEuclidean ((k + 1) + 1) :=
  realEuclideanAppend ε (fun _ : Fin 1 ↦ η)

@[simp]
theorem charbonnelAppendLastParameter_init {k : ℕ}
    (ε : RealEuclidean (k + 1)) (η : ℝ) :
    Fin.init (charbonnelAppendLastParameter ε η) = ε := by
  funext i
  have hi : i.castSucc = Fin.castAdd 1 i := Fin.ext rfl
  rw [show Fin.init (charbonnelAppendLastParameter ε η) i =
      charbonnelAppendLastParameter ε η i.castSucc by rfl, hi]
  simp [charbonnelAppendLastParameter]

@[simp]
theorem charbonnelAppendLastParameter_last {k : ℕ}
    (ε : RealEuclidean (k + 1)) (η : ℝ) :
    charbonnelAppendLastParameter ε η (Fin.last (k + 1)) = η := by
  have hi : Fin.last (k + 1) = Fin.natAdd (k + 1) (0 : Fin 1) := Fin.ext rfl
  rw [hi]
  simp [charbonnelAppendLastParameter]

@[simp]
theorem charbonnelAppendLastParameter_zero {k : ℕ}
    (ε : RealEuclidean (k + 1)) (η : ℝ) :
    charbonnelAppendLastParameter ε η 0 = ε 0 := by
  have hi : (0 : Fin ((k + 1) + 1)) =
      Fin.castAdd 1 (0 : Fin (k + 1)) := Fin.ext rfl
  rw [hi]
  simp [charbonnelAppendLastParameter]

@[simp]
theorem charbonnelParameterTail_appendLastParameter {k : ℕ}
    (ε : RealEuclidean (k + 1)) (η : ℝ) :
    CharbonnelModulus.parameterTail
        (charbonnelAppendLastParameter ε η) =
      realEuclideanAppend (CharbonnelModulus.parameterTail ε)
        (fun _ : Fin 1 ↦ η) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · have hi : (Fin.castAdd 1 j).succ = Fin.castAdd 1 j.succ := Fin.ext rfl
    rw [show CharbonnelModulus.parameterTail
        (charbonnelAppendLastParameter ε η) (Fin.castAdd 1 j) =
        charbonnelAppendLastParameter ε η (Fin.castAdd 1 j).succ by rfl,
      hi]
    simp [CharbonnelModulus.parameterTail,
      charbonnelAppendLastParameter, realEuclideanAppend]
  · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    have hi : (Fin.natAdd k (0 : Fin 1)).succ =
        Fin.natAdd (k + 1) (0 : Fin 1) := Fin.ext rfl
    rw [show CharbonnelModulus.parameterTail
        (charbonnelAppendLastParameter ε η) (Fin.natAdd k (0 : Fin 1)) =
        charbonnelAppendLastParameter ε η
          (Fin.natAdd k (0 : Fin 1)).succ by rfl,
      hi]
    simp [CharbonnelModulus.parameterTail,
      charbonnelAppendLastParameter, realEuclideanAppend]

/-! ## The topological approximation descent -/

/-- At depth zero, approximation from above puts the target in the closure of
the approximating set. -/
theorem CharbonnelModulus.ApproximatesFromAboveOnBoundedSets.subset_closure_zero
    {n : ℕ} {modulus : CharbonnelModulus 0}
    {A S : Set (RealEuclidean n)}
    (h : ApproximatesFromAboveOnBoundedSets modulus A S) :
    A ⊆ closure S := by
  intro x hx
  cases modulus with
  | base bound hbound =>
      rw [Metric.mem_closure_iff]
      intro δ hδ
      let c : ℝ := min bound (min δ (‖x‖ + 1)⁻¹)
      let e : ℝ := c / 2
      have hnorm_one : 0 < ‖x‖ + 1 := by positivity
      have hc : 0 < c := by
        exact lt_min hbound (lt_min hδ (inv_pos.mpr hnorm_one))
      have he : 0 < e := half_pos hc
      have hec : e < c := half_lt_self hc
      have hebound : e < bound :=
        hec.trans_le (min_le_left _ _)
      have heδ : e < δ :=
        hec.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have heinv : e < (‖x‖ + 1)⁻¹ :=
        hec.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have hnorm_inv : ‖x‖ < e⁻¹ := by
        have hlarge : ‖x‖ + 1 < e⁻¹ :=
          (lt_inv_comm₀ he hnorm_one).mp heinv
        linarith
      let ε : RealEuclidean 1 := fun _ ↦ e
      have hε : (CharbonnelModulus.base bound hbound).IsBounded ε := by
        exact ⟨he, hebound⟩
      obtain ⟨y, hxy, hyS⟩ := h ε hε x hx (by simpa [ε] using hnorm_inv)
      exact ⟨y, by simpa [CharbonnelModulus.parameterTail] using hyS,
        hxy.trans heδ⟩

/-- The successor step in Wilkie's Lemma 3.3.  Sending the final positive
parameter to zero replaces `S` by its positive zero trace; compactness of the
closed error ball supplies a limit for the varying visible points. -/
theorem CharbonnelModulus.ApproximatesFromAboveOnBoundedSets.descend_positiveZeroTrace
    {n k : ℕ} {initial : CharbonnelModulus k}
    {lastBound : RealEuclidean (k + 1) → ℝ}
    {hlast : ∀ ε : RealEuclidean (k + 1),
      (∀ i, 0 < ε i) → 0 < lastBound ε}
    {A : Set (RealEuclidean n)}
    {S : Set (RealEuclidean (n + (k + 1)))}
    (h : ApproximatesFromAboveOnBoundedSets
      (.step initial lastBound hlast) A S) :
    ApproximatesFromAboveOnBoundedSets (initial.halveFirst) A
      (charbonnelPositiveZeroTrace S) := by
  intro ε hε x hx hnorm
  let halfParams := charbonnelHalveFirstParameter ε
  have hhalfParamsBounded : initial.IsBounded halfParams :=
    CharbonnelModulus.halveFirst_isBounded initial ε hε
  have hεpos : ∀ i, 0 < ε i := hε.coord_pos
  have hhalfParamsPos : ∀ i, 0 < halfParams i :=
    charbonnelHalveFirstParameter_pos hεpos
  have hlastPos : 0 < lastBound halfParams :=
    hlast halfParams hhalfParamsPos
  let δ : ℕ → ℝ := fun m ↦ 1 / (m + 1 : ℝ)
  let η : ℕ → ℝ := fun m ↦ min (δ m) (lastBound halfParams) / 2
  have hδpos : ∀ m, 0 < δ m := by
    intro m
    positivity
  have hηpos : ∀ m, 0 < η m := by
    intro m
    exact half_pos (lt_min (hδpos m) hlastPos)
  have hηlast : ∀ m, η m < lastBound halfParams := by
    intro m
    exact (half_lt_self (lt_min (hδpos m) hlastPos)).trans_le
      (min_le_right _ _)
  have hextendedBounded : ∀ m,
      (CharbonnelModulus.step initial lastBound hlast).IsBounded
        (charbonnelAppendLastParameter halfParams (η m)) := by
    intro m
    exact ⟨by simpa using hhalfParamsBounded, by simpa using hηpos m,
      by simpa using hηlast m⟩
  have hhalfInv : ‖x‖ < (ε 0 / 2)⁻¹ := by
    have hinvPos : 0 < (ε 0)⁻¹ := inv_pos.mpr (hεpos 0)
    have hinvEq : (ε 0 / 2)⁻¹ = 2 * (ε 0)⁻¹ := by
      rw [inv_div, div_eq_mul_inv]
    rw [hinvEq]
    nlinarith
  have hpoint : ∀ m, ∃ y : RealEuclidean n,
      dist x y < ε 0 / 2 ∧
        realEuclideanAppend y
          (CharbonnelModulus.parameterTail
            (charbonnelAppendLastParameter halfParams (η m))) ∈ S := by
    intro m
    obtain ⟨y, hxy, hyS⟩ :=
      h (charbonnelAppendLastParameter halfParams (η m))
        (hextendedBounded m) x hx (by
          simpa [halfParams] using hhalfInv)
    exact ⟨y, by simpa [halfParams] using hxy, hyS⟩
  choose y hxy hyS using hpoint
  have hyball : ∀ m, y m ∈ Metric.closedBall x (ε 0 / 2) := by
    intro m
    exact Metric.mem_closedBall'.mpr (hxy m).le
  obtain ⟨y₀, hy₀ball, φ, hφ, hy₀⟩ :=
    (isCompact_closedBall x (ε 0 / 2)).tendsto_subseq hyball
  have hηle : ∀ m, η m ≤ δ m / 2 := by
    intro m
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hηtendsto : Tendsto η atTop (nhds 0) := by
    apply squeeze_zero (fun m ↦ (hηpos m).le) hηle
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  let z : ℕ → RealEuclidean (n + (k + 1)) := fun m ↦
    charbonnelAppendLastCoordinate
      (realEuclideanAppend (y m) (CharbonnelModulus.parameterTail ε)) (η m)
  let z₀ : RealEuclidean (n + (k + 1)) :=
    charbonnelAppendLastCoordinate
      (realEuclideanAppend y₀ (CharbonnelModulus.parameterTail ε)) 0
  have hzmem : ∀ m, z m ∈ charbonnelPositiveLastPart S := by
    intro m
    constructor
    · have hyS' := hyS m
      rw [charbonnelParameterTail_appendLastParameter] at hyS'
      have htail : CharbonnelModulus.parameterTail halfParams =
          CharbonnelModulus.parameterTail ε := by
        funext i
        simp [CharbonnelModulus.parameterTail, halfParams]
      rw [htail] at hyS'
      rw [show z m = realEuclideanAppend (y m)
          (realEuclideanAppend (CharbonnelModulus.parameterTail ε)
            (fun _ : Fin 1 ↦ η m)) by
        simp only [z]
        exact charbonnelAppendLastCoordinate_append _ _ _]
      exact hyS'
    · simpa [z] using hηpos m
  have hz₀ : Tendsto (z ∘ φ) atTop (nhds z₀) := by
    rw [tendsto_pi_nhds]
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · convert hηtendsto.comp hφ.tendsto_atTop using 1
      · funext m
        simp [z, Function.comp_apply]
      · simp [z₀]
    · refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) j
      · have hsource :
            (fun m ↦ (z ∘ φ) m (Fin.castAdd k a).castSucc) =
              fun m ↦ y (φ m) a := by
            funext m
            simp [z, Function.comp_apply]
        have htarget : z₀ (Fin.castAdd k a).castSucc = y₀ a := by
          simp [z₀]
        rw [hsource, htarget]
        exact tendsto_pi_nhds.mp hy₀ a
      · have hsource :
            (fun m ↦ (z ∘ φ) m (Fin.natAdd n b).castSucc) =
              fun _ ↦ CharbonnelModulus.parameterTail ε b := by
            funext m
            simp [z, Function.comp_apply]
        have htarget : z₀ (Fin.natAdd n b).castSucc =
            CharbonnelModulus.parameterTail ε b := by
          simp [z₀]
        rw [hsource, htarget]
        exact tendsto_const_nhds
  have hz₀closure : z₀ ∈ closure (charbonnelPositiveLastPart S) :=
    isClosed_closure.mem_of_tendsto hz₀
      (Eventually.of_forall fun m ↦ subset_closure (hzmem (φ m)))
  refine ⟨y₀, ?_, ?_⟩
  · have hhalf : ε 0 / 2 < ε 0 := half_lt_self (hεpos 0)
    exact (Metric.mem_closedBall'.mp hy₀ball).trans_lt hhalf
  · exact hz₀closure

/-! ## The explicit Charbonnel 2.1/2.2 interface -/

/-- The exact set-family input used by the trace recursion.  The two
empty-interior clauses are the content imported by Wilkie from Charbonnel's
Theorems 2.1 and 2.2; neither is valid for arbitrary subsets of Euclidean
space. -/
structure CharbonnelApproximationTraceTameness
    (C : EuclideanSetFamily) : Prop where
  closure_mem : ∀ {d : ℕ}, 0 < d →
    ∀ {S : Set (RealEuclidean d)}, S ∈ C d → closure S ∈ C d
  closure_interior_eq_empty : ∀ {d : ℕ}, 0 < d →
    ∀ {S : Set (RealEuclidean d)}, S ∈ C d →
      interior S = ∅ → interior (closure S) = ∅
  positiveZeroTrace_mem : ∀ {d : ℕ}, 0 < d →
    ∀ {S : Set (RealEuclidean (d + 1))}, S ∈ C (d + 1) →
      charbonnelPositiveZeroTrace S ∈ C d
  positiveZeroTrace_interior_eq_empty : ∀ {d : ℕ}, 0 < d →
    ∀ {S : Set (RealEuclidean (d + 1))}, S ∈ C (d + 1) →
      interior S = ∅ → interior (charbonnelPositiveZeroTrace S) = ∅

/-- Minimal recursion theorem underlying Wilkie's Lemma 3.3.  Membership of
the target is not used by the proof; the source-shaped wrapper below retains
that hypothesis. -/
theorem exists_closed_emptyInterior_boundaryCarrier_of_approximatesFromAbove
    {C : EuclideanSetFamily}
    (hC : CharbonnelApproximationTraceTameness C)
    {n k : ℕ} (hn : 0 < n)
    (A : Set (RealEuclidean n))
    {S : Set (RealEuclidean (n + k))}
    (hS : S ∈ C (n + k))
    (hSempty : interior S = ∅)
    (modulus : CharbonnelModulus k)
    (happrox : CharbonnelModulus.ApproximatesFromAboveOnBoundedSets
      modulus (frontier A) S) :
    ∃ B : Set (RealEuclidean n),
      IsClosed B ∧ B ∈ C n ∧ interior B = ∅ ∧ frontier A ⊆ B := by
  induction k with
  | zero =>
      refine ⟨closure S, isClosed_closure, hC.closure_mem hn hS,
        hC.closure_interior_eq_empty hn hS hSempty, ?_⟩
      exact happrox.subset_closure_zero
  | succ k ih =>
      cases modulus with
      | step initial lastBound hlast =>
          let T : Set (RealEuclidean (n + k)) :=
            charbonnelPositiveZeroTrace S
          have hT : T ∈ C (n + k) := by
            exact hC.positiveZeroTrace_mem (by omega) hS
          have hTempty : interior T = ∅ := by
            exact hC.positiveZeroTrace_interior_eq_empty (by omega) hS hSempty
          have hTapprox :
              CharbonnelModulus.ApproximatesFromAboveOnBoundedSets
                initial.halveFirst (frontier A) T := by
            exact happrox.descend_positiveZeroTrace
          exact ih hT hTempty initial.halveFirst hTapprox

/-- Source-shaped form of Wilkie's Lemma 3.3. -/
theorem wilkie_lemma_3_3
    {C : EuclideanSetFamily}
    (hC : CharbonnelApproximationTraceTameness C)
    {n k : ℕ} (hn : 0 < n)
    {A : Set (RealEuclidean n)} (_hA : A ∈ C n)
    {S : Set (RealEuclidean (n + k))} (hS : S ∈ C (n + k))
    (hSempty : interior S = ∅)
    (modulus : CharbonnelModulus k)
    (happrox : CharbonnelModulus.ApproximatesFromAboveOnBoundedSets
      modulus (frontier A) S) :
    ∃ B : Set (RealEuclidean n),
      IsClosed B ∧ B ∈ C n ∧ interior B = ∅ ∧ frontier A ⊆ B := by
  exact exists_closed_emptyInterior_boundaryCarrier_of_approximatesFromAbove
    hC hn A hS hSempty modulus happrox

end AbelFormalization
