import AbelFormalization.CharbonnelApproximationModuli
import AbelFormalization.ClosedZeroSetCharbonnelBridge
import AbelFormalization.LionRegularCodimensionOne

/-!
# Finite Sardian constituent families

This file records the finite syntax immediately preceding the empty-interior
argument in the Wilkie--Karpinski--Macintyre complement proof.  The source
notion is an `ℓ`-Sardian constituent

`{(x, ε) ∈ ℝⁿ × ℝ₊ᵖ | ∃ y ∈ ℝ^(p-1), F(x,y) = ε}`,

where the coordinate functions of `F` belong to the chosen function family
and are `C^ℓ`.  We index the definition by the hidden arity `q = p - 1`, so
the positive parameter block has arity `q + 1`.  A Sardian set is a finite
union of constituents with one common `ℓ` and one common parameter depth.
Its list length is a separate finite index; it is not the source's
differentiability budget or parameter complexity.

The terminology follows Karpinski--Macintyre, Section 4.4, and the equivalent
smooth `M(S)`-constituent formulation in Berarducci--Servi, Definition 3.5.6:

* https://theory.cs.uni-bonn.de/ftp/reports/cs-reports/1997/85173-CS.pdf
* https://ricerca.sns.it/retrieve/e3aacdfd-ef33-4c98-e053-3705fe0acb7e/Servi_Tamara.pdf

Only finite syntax, unused-parameter padding, common modulus refinement, and
zero-set/description carriers are proved.  In particular, this file does not
assert that these carriers have empty interior or that the Charbonnel closure
is closed under complements.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-! ## Positive parameter blocks -/

/-- Positivity on a finite selection of the final `p` parameter coordinates. -/
def charbonnelParameterPositiveOn (n p : ℕ) (indices : Finset (Fin p)) :
    Set (RealEuclidean (n + p)) :=
  {v | ∀ i ∈ indices, 0 < realEuclideanTakeRight v i}

@[simp]
theorem mem_charbonnelParameterPositiveOn_iff
    {n p : ℕ} {indices : Finset (Fin p)}
    {v : RealEuclidean (n + p)} :
    v ∈ charbonnelParameterPositiveOn n p indices ↔
      ∀ i ∈ indices, 0 < realEuclideanTakeRight v i :=
  Iff.rfl

/-- Positivity of every coordinate in the final parameter block. -/
def charbonnelPositiveParameterCarrier (n p : ℕ) :
    Set (RealEuclidean (n + p)) :=
  charbonnelParameterPositiveOn n p Finset.univ

@[simp]
theorem mem_charbonnelPositiveParameterCarrier_iff
    {n p : ℕ} {v : RealEuclidean (n + p)} :
    v ∈ charbonnelPositiveParameterCarrier n p ↔
      ∀ i, 0 < realEuclideanTakeRight v i := by
  simp [charbonnelPositiveParameterCarrier]

/-- A finite conjunction of parameter-coordinate positivity conditions is a
polynomial-sign set. -/
theorem charbonnelParameterPositiveOn_polynomialSignConstructible
    (n p : ℕ) (indices : Finset (Fin p)) :
    PolynomialSignConstructible (n + p)
      (charbonnelParameterPositiveOn n p indices) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa [charbonnelParameterPositiveOn] using
        (polynomialSignConstructible_univ (n + p))
  | @insert i indices hi ih =>
      have hcoordinate : PolynomialSignConstructible (n + p)
          {v : RealEuclidean (n + p) |
            0 < v (Fin.natAdd n i)} := by
        simpa using
          (PolynomialSignConstructible.pos
            (MvPolynomial.X (Fin.natAdd n i)))
      rw [show charbonnelParameterPositiveOn n p (insert i indices) =
          {v : RealEuclidean (n + p) | 0 < v (Fin.natAdd n i)} ∩
            charbonnelParameterPositiveOn n p indices by
        ext v
        simp [charbonnelParameterPositiveOn, realEuclideanTakeRight]]
      exact .inter hcoordinate ih

/-- Hence every selected positive-parameter condition is projected-zero for
a geometric function family. -/
theorem charbonnelParameterPositiveOn_isProjectedZeroSet
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (n p : ℕ) (indices : Finset (Fin p)) :
    IsProjectedZeroSet G (charbonnelParameterPositiveOn n p indices) :=
  (charbonnelParameterPositiveOn_polynomialSignConstructible n p indices).isProjectedZeroSet hG

/-! ## Exact Sardian constituent syntax -/

/-- An `order`-Sardian constituent over `G` with visible arity `n`, hidden
arity `q`, and therefore positive-parameter depth `q + 1`.

The componentwise fields are the finite-coordinate rendering of the source's
map `F : ℝ^(n+q) → ℝ^(q+1)`. -/
structure CharbonnelSardianConstituent
    (G : (d : ℕ) → Set (RealEuclideanFunction d))
    (order n q : ℕ) where
  visible_pos : 0 < n
  equation : Fin (q + 1) → RealEuclideanFunction (n + q)
  equation_mem : ∀ i, equation i ∈ G (n + q)
  equation_contDiff : ∀ i, ContDiff ℝ order (equation i)

namespace CharbonnelSardianConstituent

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n q : ℕ}

/-- The equation relation before imposing positivity of the parameter block. -/
def relationCarrier (constituent :
    CharbonnelSardianConstituent G order n q) :
    Set (RealEuclidean (n + (q + 1))) :=
  {v | ∃ y : RealEuclidean q, ∀ i,
    constituent.equation i
        (realEuclideanAppend (realEuclideanTakeLeft v) y) =
      realEuclideanTakeRight v i}

/-- The exact carrier of a Sardian constituent. -/
def carrier (constituent : CharbonnelSardianConstituent G order n q) :
    Set (RealEuclidean (n + (q + 1))) :=
  constituent.relationCarrier ∩
    charbonnelPositiveParameterCarrier n (q + 1)

@[simp]
theorem mem_relationCarrier_iff
    (constituent : CharbonnelSardianConstituent G order n q)
    {v : RealEuclidean (n + (q + 1))} :
    v ∈ constituent.relationCarrier ↔
      ∃ y : RealEuclidean q, ∀ i,
        constituent.equation i
            (realEuclideanAppend (realEuclideanTakeLeft v) y) =
          realEuclideanTakeRight v i :=
  Iff.rfl

@[simp]
theorem mem_carrier_iff
    (constituent : CharbonnelSardianConstituent G order n q)
    {v : RealEuclidean (n + (q + 1))} :
    v ∈ constituent.carrier ↔
      (∃ y : RealEuclidean q, ∀ i,
        constituent.equation i
            (realEuclideanAppend (realEuclideanTakeLeft v) y) =
          realEuclideanTakeRight v i) ∧
      ∀ i, 0 < realEuclideanTakeRight v i := by
  simp [carrier]

/-- From coordinates `((x,ε),y)`, retain `(x,y)`. -/
def relationInputLinearMap (n q : ℕ) :
    RealEuclidean ((n + (q + 1)) + q) →ₗ[ℝ]
      RealEuclidean (n + q) where
  toFun v := realEuclideanAppend
    (realEuclideanTakeLeft (realEuclideanTakeLeft v))
    (realEuclideanTakeRight v)
  map_add' := by
    intro v w
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

@[simp]
theorem relationInputLinearMap_append
    (v : RealEuclidean (n + (q + 1))) (y : RealEuclidean q) :
    relationInputLinearMap n q (realEuclideanAppend v y) =
      realEuclideanAppend (realEuclideanTakeLeft v) y := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
    simp [relationInputLinearMap, realEuclideanAppend,
      realEuclideanTakeLeft, realEuclideanTakeRight]

/-- One equation residual on the space `((x,ε),y)`. -/
def relationResidualTerm
    (constituent : CharbonnelSardianConstituent G order n q)
    (i : Fin (q + 1)) :
    RealEuclideanFunction ((n + (q + 1)) + q) :=
  fun v ↦
    constituent.equation i (relationInputLinearMap n q v) -
      v (Fin.castAdd q (Fin.natAdd n i))

/-- The sum of squares of all constituent equation residuals. -/
def relationResidual
    (constituent : CharbonnelSardianConstituent G order n q) :
    RealEuclideanFunction ((n + (q + 1)) + q) :=
  fun v ↦ ∑ i ∈ Finset.univ, constituent.relationResidualTerm i v ^ 2

@[simp]
theorem relationResidualTerm_append
    (constituent : CharbonnelSardianConstituent G order n q)
    (i : Fin (q + 1))
    (v : RealEuclidean (n + (q + 1))) (y : RealEuclidean q) :
    constituent.relationResidualTerm i (realEuclideanAppend v y) =
      constituent.equation i
          (realEuclideanAppend (realEuclideanTakeLeft v) y) -
        realEuclideanTakeRight v i := by
  simp [relationResidualTerm, realEuclideanTakeRight]

@[simp]
theorem relationResidual_append_eq_zero_iff
    (constituent : CharbonnelSardianConstituent G order n q)
    (v : RealEuclidean (n + (q + 1))) (y : RealEuclidean q) :
    constituent.relationResidual (realEuclideanAppend v y) = 0 ↔
      ∀ i, constituent.equation i
          (realEuclideanAppend (realEuclideanTakeLeft v) y) =
        realEuclideanTakeRight v i := by
  rw [relationResidual]
  simp only [relationResidualTerm_append]
  rw [Finset.sum_sq_eq_zero_iff]
  simp only [Finset.mem_univ, forall_const, sub_eq_zero]

/-- The residual belongs to a geometric function family by affine pullback,
subtraction, squaring, and finite addition. -/
theorem relationResidual_mem
    (hG : IsGeometricFunctionFamily G)
    (constituent : CharbonnelSardianConstituent G order n q) :
    constituent.relationResidual ∈ G ((n + (q + 1)) + q) := by
  let L := relationInputLinearMap n q
  have hterm : ∀ i : Fin (q + 1),
      constituent.relationResidualTerm i ∈
        G ((n + (q + 1)) + q) := by
    intro i
    let pulledEquation : RealEuclideanFunction ((n + (q + 1)) + q) :=
      constituent.equation i ∘ L
    have hequation : pulledEquation ∈ G ((n + (q + 1)) + q) := by
      exact hG.affine_comp (constituent.equation_mem i) L.toAffineMap
    let coordinate : Fin ((n + (q + 1)) + q) :=
      Fin.castAdd q (Fin.natAdd n i)
    let coordinateFunction :
        RealEuclideanFunction ((n + (q + 1)) + q) :=
      fun v ↦ v coordinate
    have hcoordinate : coordinateFunction ∈
        G ((n + (q + 1)) + q) := by
      simpa [coordinate] using hG.polynomial (MvPolynomial.X coordinate)
    have hsub := hG.sub_mem hequation hcoordinate
    have hterm_eq : constituent.relationResidualTerm i =
        pulledEquation - coordinateFunction := by
      funext v
      rfl
    rw [hterm_eq]
    exact hsub
  have hsquares : ∀ i ∈ (Finset.univ : Finset (Fin (q + 1))),
      (fun v ↦ constituent.relationResidualTerm i v ^ 2) ∈
        G ((n + (q + 1)) + q) := by
    intro i _hi
    exact hG.sq_mem (hterm i)
  have hsum := hG.finset_sum_mem
    (Finset.univ : Finset (Fin (q + 1)))
    (fun i ↦ fun v ↦ constituent.relationResidualTerm i v ^ 2)
    hsquares
  have hresidual_eq : constituent.relationResidual =
      ∑ i ∈ (Finset.univ : Finset (Fin (q + 1))),
        (fun v : RealEuclidean ((n + (q + 1)) + q) ↦
          constituent.relationResidualTerm i v ^ 2) := by
    funext v
    simp only [relationResidual, Finset.sum_apply]
  rw [hresidual_eq]
  exact hsum

/-- The equation relation is the projection of the literal residual zero set. -/
theorem relationCarrier_isProjectedZeroSet
    (hG : IsGeometricFunctionFamily G)
    (constituent : CharbonnelSardianConstituent G order n q) :
    IsProjectedZeroSet G constituent.relationCarrier := by
  refine ⟨q, constituent.relationResidual,
    constituent.relationResidual_mem hG, ?_⟩
  ext v
  simp [relationCarrier]

/-- The exact positive Sardian carrier is projected-zero.  Positivity is
encoded by the project's polynomial-sign witness equations. -/
theorem carrier_isProjectedZeroSet
    (hG : IsGeometricFunctionFamily G)
    (constituent : CharbonnelSardianConstituent G order n q) :
    IsProjectedZeroSet G constituent.carrier := by
  change IsProjectedZeroSet G
    (constituent.relationCarrier ∩
      charbonnelParameterPositiveOn n (q + 1) Finset.univ)
  exact (constituent.relationCarrier_isProjectedZeroSet hG).inter hG
    (charbonnelParameterPositiveOn_isProjectedZeroSet hG n (q + 1)
      Finset.univ)

/-- A constituent carrier has a rank-one description over literal zero sets. -/
theorem exists_rank_one_description
    (hG : IsGeometricFunctionFamily G)
    (constituent : CharbonnelSardianConstituent G order n q) :
    ∃ description :
        CharbonnelDescription (literalZeroSetFamily G) (n + (q + 1)),
      description.carrier = constituent.carrier ∧ description.rank = 1 :=
  (constituent.carrier_isProjectedZeroSet hG).exists_rank_one_literalZero_description
    (by omega)

end CharbonnelSardianConstituent

/-! ## Finite unions at one source depth and order -/

/-- A finite Sardian set: all constituents share the same differentiability
budget and the same parameter depth. -/
structure CharbonnelSardianSet
    (G : (d : ℕ) → Set (RealEuclideanFunction d))
    (order n q : ℕ) where
  visible_pos : 0 < n
  constituents : List (CharbonnelSardianConstituent G order n q)

namespace CharbonnelSardianSet

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n q : ℕ}

/-- The finite union denoted by a Sardian-set syntax object. -/
def carrier (s : CharbonnelSardianSet G order n q) :
    Set (RealEuclidean (n + (q + 1))) :=
  {v | ∃ constituent ∈ s.constituents, v ∈ constituent.carrier}

/-- The finite constituent index used by the syntax object. -/
abbrev ConstituentIndex (s : CharbonnelSardianSet G order n q) :=
  Fin s.constituents.length

/-- Retrieve a constituent by its finite syntax index. -/
def indexedConstituent (s : CharbonnelSardianSet G order n q)
    (i : s.ConstituentIndex) :
    CharbonnelSardianConstituent G order n q :=
  s.constituents.get i

@[simp]
theorem mem_carrier_iff
    (s : CharbonnelSardianSet G order n q)
    {v : RealEuclidean (n + (q + 1))} :
    v ∈ s.carrier ↔
      ∃ constituent ∈ s.constituents, v ∈ constituent.carrier :=
  Iff.rfl

theorem mem_carrier_iff_exists_index
    (s : CharbonnelSardianSet G order n q)
    {v : RealEuclidean (n + (q + 1))} :
    v ∈ s.carrier ↔
      ∃ i : s.ConstituentIndex, v ∈ (s.indexedConstituent i).carrier := by
  rw [mem_carrier_iff, List.exists_mem_iff_get]
  rfl

/-- Concatenation is finite union at the syntax level. -/
def union (left right : CharbonnelSardianSet G order n q) :
    CharbonnelSardianSet G order n q :=
  ⟨left.visible_pos, left.constituents ++ right.constituents⟩

@[simp]
theorem carrier_union
    (left right : CharbonnelSardianSet G order n q) :
    (left.union right).carrier = left.carrier ∪ right.carrier := by
  ext v
  simp only [carrier, union, List.mem_append, Set.mem_setOf_eq,
    Set.mem_union]
  constructor
  · rintro ⟨constituent, hleft | hright, hv⟩
    · exact Or.inl ⟨constituent, hleft, hv⟩
    · exact Or.inr ⟨constituent, hright, hv⟩
  · rintro (⟨constituent, hleft, hv⟩ | ⟨constituent, hright, hv⟩)
    · exact ⟨constituent, Or.inl hleft, hv⟩
    · exact ⟨constituent, Or.inr hright, hv⟩

/-- A finite union of constituent carriers is still projected-zero. -/
theorem carrier_isProjectedZeroSet
    (hG : IsGeometricFunctionFamily G)
    (s : CharbonnelSardianSet G order n q) :
    IsProjectedZeroSet G s.carrier := by
  change IsProjectedZeroSet G
    {v | ∃ constituent ∈ s.constituents, v ∈ constituent.carrier}
  induction s.constituents with
  | nil =>
      simpa [carrier] using
        (isProjectedZeroSet_empty (G := G) hG :
          IsProjectedZeroSet G
            (∅ : Set (RealEuclidean (n + (q + 1)))))
  | cons constituent constituents ih =>
      have hconstituent := constituent.carrier_isProjectedZeroSet hG
      have hunion := hconstituent.union hG ih
      rw [show
        {v | ∃ piece ∈ constituent :: constituents, v ∈ piece.carrier} =
          constituent.carrier ∪
            {v | ∃ piece ∈ constituents, v ∈ piece.carrier} by
        ext v
        simp only [List.mem_cons, Set.mem_setOf_eq, Set.mem_union]
        constructor
        · rintro ⟨piece, rfl | hpiece, hv⟩
          · exact Or.inl hv
          · exact Or.inr ⟨piece, hpiece, hv⟩
        · rintro (hv | ⟨piece, hpiece, hv⟩)
          · exact ⟨constituent, Or.inl rfl, hv⟩
          · exact ⟨piece, Or.inr hpiece, hv⟩]
      exact hunion

/-- Consequently a finite Sardian carrier has a rank-one literal-zero
Charbonnel description. -/
theorem exists_rank_one_description
    (hG : IsGeometricFunctionFamily G)
    (s : CharbonnelSardianSet G order n q) :
    ∃ description :
        CharbonnelDescription (literalZeroSetFamily G) (n + (q + 1)),
      description.carrier = s.carrier ∧ description.rank = 1 :=
  (s.carrier_isProjectedZeroSet hG).exists_rank_one_literalZero_description
    (by omega)

end CharbonnelSardianSet

/-! ## Unused positive-parameter padding -/

/-- Retain the visible block and the first `q + 1` parameters from a block
of common depth `K + 1`. -/
def charbonnelParameterPrefixLinearMap
    (n q K : ℕ) (hqK : q ≤ K) :
    RealEuclidean (n + (K + 1)) →ₗ[ℝ]
      RealEuclidean (n + (q + 1)) where
  toFun v := realEuclideanAppend (realEuclideanTakeLeft v)
    (fun i ↦ realEuclideanTakeRight v
      (Fin.castLE (Nat.succ_le_succ hqK) i))
  map_add' := by
    intro v w
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

@[simp]
theorem charbonnelParameterPrefixLinearMap_append
    {n q K : ℕ} (hqK : q ≤ K)
    (x : RealEuclidean n) (ε : RealEuclidean (K + 1)) :
    charbonnelParameterPrefixLinearMap n q K hqK
        (realEuclideanAppend x ε) =
      realEuclideanAppend x
        (fun i ↦ ε (Fin.castLE (Nat.succ_le_succ hqK) i)) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
    simp [charbonnelParameterPrefixLinearMap, realEuclideanAppend,
      realEuclideanTakeLeft, realEuclideanTakeRight]

/-- Indices of the newly appended parameter coordinates. -/
def charbonnelTrailingParameterIndices (q K : ℕ) :
    Finset (Fin (K + 1)) :=
  Finset.univ.filter (fun i ↦ q + 1 ≤ i.val)

/-- Extend a carrier of hidden arity `q` to common hidden arity `K` by
ignoring the new trailing parameters while requiring them to be positive. -/
def charbonnelParameterPad
    {n q K : ℕ} (hqK : q ≤ K)
    (A : Set (RealEuclidean (n + (q + 1)))) :
    Set (RealEuclidean (n + (K + 1))) :=
  (charbonnelParameterPrefixLinearMap n q K hqK) ⁻¹' A ∩
    charbonnelParameterPositiveOn n (K + 1)
      (charbonnelTrailingParameterIndices q K)

@[simp]
theorem mem_charbonnelParameterPad_iff
    {n q K : ℕ} (hqK : q ≤ K)
    {A : Set (RealEuclidean (n + (q + 1)))}
    {v : RealEuclidean (n + (K + 1))} :
    v ∈ charbonnelParameterPad hqK A ↔
      charbonnelParameterPrefixLinearMap n q K hqK v ∈ A ∧
        ∀ i, q + 1 ≤ i.val → 0 < realEuclideanTakeRight v i := by
  simp [charbonnelParameterPad, charbonnelTrailingParameterIndices,
    charbonnelParameterPositiveOn]

/-- Section form of unused-parameter padding. -/
@[simp]
theorem mem_charbonnelParameterPad_append_iff
    {n q K : ℕ} (hqK : q ≤ K)
    {A : Set (RealEuclidean (n + (q + 1)))}
    (x : RealEuclidean n) (ε : RealEuclidean (K + 1)) :
    realEuclideanAppend x ε ∈ charbonnelParameterPad hqK A ↔
      realEuclideanAppend x
          (fun i ↦ ε (Fin.castLE (Nat.succ_le_succ hqK) i)) ∈ A ∧
        ∀ i, q + 1 ≤ i.val → 0 < ε i := by
  rw [mem_charbonnelParameterPad_iff,
    charbonnelParameterPrefixLinearMap_append]
  simp only [realEuclideanTakeRight_append]

theorem charbonnelParameterPad_union
    {n q K : ℕ} (hqK : q ≤ K)
    (A B : Set (RealEuclidean (n + (q + 1)))) :
    charbonnelParameterPad hqK (A ∪ B) =
      charbonnelParameterPad hqK A ∪ charbonnelParameterPad hqK B := by
  ext v
  simp only [mem_charbonnelParameterPad_iff, Set.mem_union]
  tauto

theorem charbonnelParameterPad_inter
    {n q K : ℕ} (hqK : q ≤ K)
    (A B : Set (RealEuclidean (n + (q + 1)))) :
    charbonnelParameterPad hqK (A ∩ B) =
      charbonnelParameterPad hqK A ∩ charbonnelParameterPad hqK B := by
  ext v
  simp only [mem_charbonnelParameterPad_iff, Set.mem_inter_iff]
  tauto

/-- The chosen common hidden arity for two independently constructed
constituent families. -/
def charbonnelCommonHiddenArity (q r : ℕ) : ℕ :=
  max q r

/-- Pad the left carrier to the common maximum parameter depth. -/
def charbonnelPadLeftToCommon
    {n q r : ℕ} (A : Set (RealEuclidean (n + (q + 1)))) :
    Set (RealEuclidean (n + (charbonnelCommonHiddenArity q r + 1))) :=
  charbonnelParameterPad (Nat.le_max_left q r) A

/-- Pad the right carrier to the same common maximum parameter depth. -/
def charbonnelPadRightToCommon
    {n q r : ℕ} (B : Set (RealEuclidean (n + (r + 1)))) :
    Set (RealEuclidean (n + (charbonnelCommonHiddenArity q r + 1))) :=
  charbonnelParameterPad (Nat.le_max_right q r) B

/-- Padding preserves the projected-zero carrier property. -/
theorem charbonnelParameterPad_isProjectedZeroSet
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    {n q K : ℕ} (hqK : q ≤ K)
    {A : Set (RealEuclidean (n + (q + 1)))}
    (hA : IsProjectedZeroSet G A) :
    IsProjectedZeroSet G (charbonnelParameterPad hqK A) := by
  exact (hA.linear_preimage hG
    (charbonnelParameterPrefixLinearMap n q K hqK)).inter hG
      (charbonnelParameterPositiveOn_isProjectedZeroSet hG n (K + 1)
        (charbonnelTrailingParameterIndices q K))

/-- One constituent together with evidence that it fits a chosen common
parameter depth. -/
structure CharbonnelPaddedSardianConstituent
    (G : (d : ℕ) → Set (RealEuclideanFunction d))
    (order n K : ℕ) where
  hiddenArity : ℕ
  hiddenArity_le : hiddenArity ≤ K
  constituent : CharbonnelSardianConstituent G order n hiddenArity

namespace CharbonnelPaddedSardianConstituent

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n K : ℕ}

/-- Regard a constituent of any smaller depth as a constituent at the chosen
common depth. -/
def ofConstituent {q : ℕ} (hqK : q ≤ K)
    (constituent : CharbonnelSardianConstituent G order n q) :
    CharbonnelPaddedSardianConstituent G order n K :=
  ⟨q, hqK, constituent⟩

/-- Carrier after adjoining the unused positive trailing parameters. -/
def carrier (piece : CharbonnelPaddedSardianConstituent G order n K) :
    Set (RealEuclidean (n + (K + 1))) :=
  charbonnelParameterPad piece.hiddenArity_le piece.constituent.carrier

@[simp]
theorem carrier_ofConstituent {q : ℕ} (hqK : q ≤ K)
    (constituent : CharbonnelSardianConstituent G order n q) :
    (ofConstituent hqK constituent).carrier =
      charbonnelParameterPad hqK constituent.carrier :=
  rfl

theorem carrier_isProjectedZeroSet
    (hG : IsGeometricFunctionFamily G)
    (piece : CharbonnelPaddedSardianConstituent G order n K) :
    IsProjectedZeroSet G piece.carrier :=
  charbonnelParameterPad_isProjectedZeroSet hG piece.hiddenArity_le
    (piece.constituent.carrier_isProjectedZeroSet hG)

end CharbonnelPaddedSardianConstituent

/-- A finite collection of constituents padded to one common parameter depth
and carrying one common differentiability budget. -/
structure CharbonnelFiniteSardianFamily
    (G : (d : ℕ) → Set (RealEuclideanFunction d))
    (order n K : ℕ) where
  visible_pos : 0 < n
  constituents : List (CharbonnelPaddedSardianConstituent G order n K)

namespace CharbonnelFiniteSardianFamily

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)}
variable {order n K : ℕ}

/-- Pad every constituent of one exact-depth Sardian set to a chosen common
depth. -/
def ofSardianSet {q : ℕ} (hqK : q ≤ K)
    (s : CharbonnelSardianSet G order n q) :
    CharbonnelFiniteSardianFamily G order n K :=
  ⟨s.visible_pos, s.constituents.map
    (fun constituent ↦
      CharbonnelPaddedSardianConstituent.ofConstituent hqK constituent)⟩

def carrier (family : CharbonnelFiniteSardianFamily G order n K) :
    Set (RealEuclidean (n + (K + 1))) :=
  {v | ∃ constituent ∈ family.constituents, v ∈ constituent.carrier}

@[simp]
theorem carrier_ofSardianSet {q : ℕ} (hqK : q ≤ K)
    (s : CharbonnelSardianSet G order n q) :
    (ofSardianSet hqK s).carrier =
      charbonnelParameterPad hqK s.carrier := by
  ext v
  change
    (∃ piece ∈ s.constituents.map
        (fun constituent ↦
          CharbonnelPaddedSardianConstituent.ofConstituent hqK constituent),
      v ∈ piece.carrier) ↔
      v ∈ charbonnelParameterPad hqK s.carrier
  constructor
  · rintro ⟨piece, hpiece, hv⟩
    rcases List.mem_map.mp hpiece with ⟨constituent, hconstituent, rfl⟩
    rw [CharbonnelPaddedSardianConstituent.carrier_ofConstituent,
      mem_charbonnelParameterPad_iff] at hv
    rw [mem_charbonnelParameterPad_iff]
    exact
      ⟨(CharbonnelSardianSet.mem_carrier_iff s).mpr
        ⟨constituent, hconstituent, hv.1⟩, hv.2⟩
  · rw [mem_charbonnelParameterPad_iff]
    rintro ⟨hv, htrailing⟩
    rcases (CharbonnelSardianSet.mem_carrier_iff s).mp hv with
      ⟨constituent, hconstituent, hcarrier⟩
    refine
      ⟨CharbonnelPaddedSardianConstituent.ofConstituent hqK constituent,
        List.mem_map.mpr ⟨constituent, hconstituent, rfl⟩, ?_⟩
    rw [CharbonnelPaddedSardianConstituent.carrier_ofConstituent,
      mem_charbonnelParameterPad_iff]
    exact ⟨hcarrier, htrailing⟩

abbrev ConstituentIndex
    (family : CharbonnelFiniteSardianFamily G order n K) :=
  Fin family.constituents.length

def indexedConstituent
    (family : CharbonnelFiniteSardianFamily G order n K)
    (i : family.ConstituentIndex) :
    CharbonnelPaddedSardianConstituent G order n K :=
  family.constituents.get i

theorem mem_carrier_iff_exists_index
    (family : CharbonnelFiniteSardianFamily G order n K)
    {v : RealEuclidean (n + (K + 1))} :
    v ∈ family.carrier ↔
      ∃ i : family.ConstituentIndex,
        v ∈ (family.indexedConstituent i).carrier := by
  change
    (∃ constituent ∈ family.constituents, v ∈ constituent.carrier) ↔
      ∃ i : Fin family.constituents.length,
        v ∈ (family.constituents.get i).carrier
  exact List.exists_mem_iff_get

theorem carrier_isProjectedZeroSet
    (hG : IsGeometricFunctionFamily G)
    (family : CharbonnelFiniteSardianFamily G order n K) :
    IsProjectedZeroSet G family.carrier := by
  change IsProjectedZeroSet G
    {v | ∃ constituent ∈ family.constituents, v ∈ constituent.carrier}
  induction family.constituents with
  | nil =>
      simpa [carrier] using
        (isProjectedZeroSet_empty (G := G) hG :
          IsProjectedZeroSet G
            (∅ : Set (RealEuclidean (n + (K + 1)))))
  | cons constituent constituents ih =>
      have hconstituent := constituent.carrier_isProjectedZeroSet hG
      have hunion := hconstituent.union hG ih
      rw [show
        {v | ∃ piece ∈ constituent :: constituents, v ∈ piece.carrier} =
          constituent.carrier ∪
            {v | ∃ piece ∈ constituents, v ∈ piece.carrier} by
        ext v
        simp only [List.mem_cons, Set.mem_setOf_eq, Set.mem_union]
        constructor
        · rintro ⟨piece, rfl | hpiece, hv⟩
          · exact Or.inl hv
          · exact Or.inr ⟨piece, hpiece, hv⟩
        · rintro (hv | ⟨piece, hpiece, hv⟩)
          · exact ⟨constituent, Or.inl rfl, hv⟩
          · exact ⟨piece, Or.inr hpiece, hv⟩]
      exact hunion

theorem exists_rank_one_description
    (hG : IsGeometricFunctionFamily G)
    (family : CharbonnelFiniteSardianFamily G order n K) :
    ∃ description :
        CharbonnelDescription (literalZeroSetFamily G) (n + (K + 1)),
      description.carrier = family.carrier ∧ description.rank = 1 :=
  (family.carrier_isProjectedZeroSet hG).exists_rank_one_literalZero_description
    (by omega)

end CharbonnelFiniteSardianFamily

/-! ## Finite common refinements and finite approximation unions -/

namespace CharbonnelModulus

/-- Iterated infimum of a finite list, with an explicit fallback modulus for
the empty list. -/
def finiteInfimum {k : ℕ} (fallback : CharbonnelModulus k) :
    List (CharbonnelModulus k) → CharbonnelModulus k
  | [] => fallback
  | μ :: moduli => infimum μ (finiteInfimum fallback moduli)

theorem finiteInfimum_refines_fallback {k : ℕ}
    (fallback : CharbonnelModulus k)
    (moduli : List (CharbonnelModulus k)) :
    (finiteInfimum fallback moduli).Refines fallback := by
  induction moduli with
  | nil => exact refines_refl fallback
  | cons μ moduli ih =>
      exact (infimum_refines_right μ (finiteInfimum fallback moduli)).trans ih

theorem finiteInfimum_refines_of_mem {k : ℕ}
    (fallback : CharbonnelModulus k)
    {μ : CharbonnelModulus k}
    {moduli : List (CharbonnelModulus k)}
    (hμ : μ ∈ moduli) :
    (finiteInfimum fallback moduli).Refines μ := by
  induction moduli with
  | nil => simp at hμ
  | cons ν moduli ih =>
      rw [List.mem_cons] at hμ
      rcases hμ with rfl | hμ
      · exact infimum_refines_left μ (finiteInfimum fallback moduli)
      · exact
          (infimum_refines_right ν (finiteInfimum fallback moduli)).trans
            (ih hμ)

/-- Nonempty finite infimum, indexed without an externally chosen fallback.
The first indexed modulus supplies the fallback for the list fold. -/
def finiteInfimumFin {k r : ℕ}
    (moduli : Fin (r + 1) → CharbonnelModulus k) :
    CharbonnelModulus k :=
  finiteInfimum (moduli 0) (List.ofFn moduli)

/-- The nonempty finite infimum refines every member of the family. -/
theorem finiteInfimumFin_refines {k r : ℕ}
    (moduli : Fin (r + 1) → CharbonnelModulus k)
    (i : Fin (r + 1)) :
    (finiteInfimumFin moduli).Refines (moduli i) := by
  unfold finiteInfimumFin
  apply finiteInfimum_refines_of_mem (moduli 0)
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Every nonempty finite family of same-depth moduli has a common semantic
refinement. -/
theorem exists_common_refinement_fin {k r : ℕ}
    (moduli : Fin (r + 1) → CharbonnelModulus k) :
    ∃ ξ : CharbonnelModulus k, ∀ i, ξ.Refines (moduli i) :=
  ⟨finiteInfimumFin moduli, finiteInfimumFin_refines moduli⟩

theorem isBounded_finiteInfimum_iff {k : ℕ}
    (fallback : CharbonnelModulus k)
    (moduli : List (CharbonnelModulus k))
    (ε : RealEuclidean (k + 1)) :
    (finiteInfimum fallback moduli).IsBounded ε ↔
      fallback.IsBounded ε ∧ ∀ μ ∈ moduli, μ.IsBounded ε := by
  induction moduli with
  | nil => simp [finiteInfimum]
  | cons μ moduli ih =>
      rw [finiteInfimum, isBounded_infimum_iff, ih]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

/-- The empty carrier is a two-sided approximation of the empty target. -/
theorem isTwoSidedApproximation_empty {n k : ℕ}
    (μ : CharbonnelModulus k) :
    IsTwoSidedApproximation μ
      (∅ : Set (RealEuclidean (n + k)))
      (∅ : Set (RealEuclidean n)) := by
  constructor
  · intro ε hε x hx
    exact hx.elim
  · intro ε hε x hx hxnorm
    exact hx.elim

end CharbonnelModulus

/-- One modulated two-sided approximation piece. -/
structure CharbonnelApproximationPiece (n k : ℕ) where
  modulus : CharbonnelModulus k
  approximant : Set (RealEuclidean (n + k))
  target : Set (RealEuclidean n)
  isTwoSided :
    CharbonnelModulus.IsTwoSidedApproximation modulus approximant target

namespace CharbonnelApproximationPiece

variable {n k : ℕ}

def approximantUnion (pieces : List (CharbonnelApproximationPiece n k)) :
    Set (RealEuclidean (n + k)) :=
  {x | ∃ piece ∈ pieces, x ∈ piece.approximant}

def targetUnion (pieces : List (CharbonnelApproximationPiece n k)) :
    Set (RealEuclidean n) :=
  {x | ∃ piece ∈ pieces, x ∈ piece.target}

/-- A common modulus propagates through a finite union. -/
theorem isTwoSidedApproximation_unions
    (μ : CharbonnelModulus k)
    (pieces : List (CharbonnelApproximationPiece n k))
    (hpieces : ∀ piece ∈ pieces,
      CharbonnelModulus.IsTwoSidedApproximation μ
        piece.approximant piece.target) :
    CharbonnelModulus.IsTwoSidedApproximation μ
      (approximantUnion pieces) (targetUnion pieces) := by
  induction pieces with
  | nil =>
      simpa [approximantUnion, targetUnion] using
        (CharbonnelModulus.isTwoSidedApproximation_empty (n := n) μ)
  | cons piece pieces ih =>
      have hpiece := hpieces piece (by simp)
      have htail := ih (by
        intro other hother
        exact hpieces other (by simp [hother]))
      rw [show approximantUnion (piece :: pieces) =
          piece.approximant ∪ approximantUnion pieces by
        ext x
        simp only [approximantUnion, List.mem_cons, Set.mem_setOf_eq,
          Set.mem_union]
        constructor
        · rintro ⟨other, rfl | hother, hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨other, hother, hx⟩
        · rintro (hx | ⟨other, hother, hx⟩)
          · exact ⟨piece, Or.inl rfl, hx⟩
          · exact ⟨other, Or.inr hother, hx⟩]
      rw [show targetUnion (piece :: pieces) =
          piece.target ∪ targetUnion pieces by
        ext x
        simp only [targetUnion, List.mem_cons, Set.mem_setOf_eq,
          Set.mem_union]
        constructor
        · rintro ⟨other, rfl | hother, hx⟩
          · exact Or.inl hx
          · exact Or.inr ⟨other, hother, hx⟩
        · rintro (hx | ⟨other, hother, hx⟩)
          · exact ⟨piece, Or.inl rfl, hx⟩
          · exact ⟨other, Or.inr hother, hx⟩]
      exact hpiece.union htail

/-- One finite infimum refines every modulus occurring in the list. -/
def commonModulus (fallback : CharbonnelModulus k)
    (pieces : List (CharbonnelApproximationPiece n k)) :
    CharbonnelModulus k :=
  CharbonnelModulus.finiteInfimum fallback
    (pieces.map (fun piece ↦ piece.modulus))

theorem commonModulus_refines
    (fallback : CharbonnelModulus k)
    {pieces : List (CharbonnelApproximationPiece n k)}
    {piece : CharbonnelApproximationPiece n k}
    (hpiece : piece ∈ pieces) :
    (commonModulus fallback pieces).Refines piece.modulus := by
  unfold commonModulus
  exact CharbonnelModulus.finiteInfimum_refines_of_mem fallback
    (List.mem_map.mpr ⟨piece, hpiece, rfl⟩)

theorem commonModulus_isTwoSided
    (fallback : CharbonnelModulus k)
    {pieces : List (CharbonnelApproximationPiece n k)}
    {piece : CharbonnelApproximationPiece n k}
    (hpiece : piece ∈ pieces) :
    CharbonnelModulus.IsTwoSidedApproximation
      (commonModulus fallback pieces) piece.approximant piece.target :=
  piece.isTwoSided.mono_modulus
    (commonModulus_refines fallback hpiece)

/-- A finite list of independently modulated approximations admits one
common refined modulus, and its two finite unions are a two-sided
approximation under that modulus. -/
theorem commonModulus_isTwoSidedApproximation_unions
    (fallback : CharbonnelModulus k)
    (pieces : List (CharbonnelApproximationPiece n k)) :
    CharbonnelModulus.IsTwoSidedApproximation
      (commonModulus fallback pieces)
      (approximantUnion pieces) (targetUnion pieces) := by
  apply isTwoSidedApproximation_unions
  intro piece hpiece
  exact commonModulus_isTwoSided fallback hpiece

end CharbonnelApproximationPiece

end AbelFormalization
