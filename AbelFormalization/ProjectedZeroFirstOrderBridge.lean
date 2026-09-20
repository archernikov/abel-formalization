import AbelFormalization.ProjectedZeroMatrixSections
import AbelFormalization.UnaryPieceDecomposition
import Mathlib.Topology.Order.IntermediateValue

/-!
# First-order projection rules for projected zero sets

This file proves the quantifier rules that follow formally from the
projected-zero presentation.  Existential quantification only enlarges the
witness block.  Universal quantification follows as soon as the projected-zero
class is closed under complements.

The complement hypothesis below is an interface: this file does not assume or
postulate a complement theorem.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Reassociating flat coordinate blocks -/

/-- The linear reassociation `(x,(y,z)) ↦ ((x,y),z)` of three flat coordinate
blocks. -/
def realEuclideanAssociateLeftLinearMap (n m q : ℕ) :
    RealEuclidean (n + (m + q)) →ₗ[ℝ]
      RealEuclidean ((n + m) + q) where
  toFun v := Fin.addCases
    (fun ij ↦ Fin.addCases
      (fun i ↦ v (Fin.castAdd (m + q) i))
      (fun j ↦ v (Fin.natAdd n (Fin.castAdd q j))) ij)
    (fun k ↦ v (Fin.natAdd n (Fin.natAdd m k)))
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases ?_ ?_ k
    · intro ij
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) ij <;> simp
    · intro i
      simp
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases ?_ ?_ k
    · intro ij
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) ij <;> simp
    · intro i
      simp

@[simp]
theorem realEuclideanAssociateLeftLinearMap_append
    {n m q : ℕ} (x : RealEuclidean n) (y : RealEuclidean m)
    (z : RealEuclidean q) :
    realEuclideanAssociateLeftLinearMap n m q
        (realEuclideanAppend x (realEuclideanAppend y z)) =
      realEuclideanAppend (realEuclideanAppend x y) z := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro ij
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) ij <;>
      simp [realEuclideanAssociateLeftLinearMap]
  · intro i
    simp [realEuclideanAssociateLeftLinearMap]

/-! ## Existential and universal coordinate projection -/

/-- Project away the final block of `m` coordinates.  This is the semantic
operation performed by a finite block of existential quantifiers. -/
def realEuclideanExistentialProjection {n m : ℕ}
    (s : Set (RealEuclidean (n + m))) : Set (RealEuclidean n) :=
  {x | ∃ y : RealEuclidean m, realEuclideanAppend x y ∈ s}

/-- Projected zero sets are closed under existential quantification: the new
quantified variables are simply prepended to the old witness block. -/
theorem IsProjectedZeroSet.existentialProjection
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n m : ℕ}
    {s : Set (RealEuclidean (n + m))}
    (hs : IsProjectedZeroSet G s) :
    IsProjectedZeroSet G (realEuclideanExistentialProjection s) := by
  obtain ⟨q, f, hf, rfl⟩ := hs
  let L := realEuclideanAssociateLeftLinearMap n m q
  let F : RealEuclideanFunction (n + (m + q)) := f ∘ L
  have hF : F ∈ G (n + (m + q)) :=
    hG.affine_comp hf L.toAffineMap
  refine ⟨m + q, F, hF, ?_⟩
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, z, hz⟩
    refine ⟨realEuclideanAppend y z, ?_⟩
    simpa [F, L, Function.comp_apply] using hz
  · rintro ⟨yz, hyz⟩
    let y : RealEuclidean m := realEuclideanTakeLeft yz
    let z : RealEuclidean q := realEuclideanTakeRight yz
    have hyz' : yz = realEuclideanAppend y z := by
      funext k
      refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
        simp [y, z, realEuclideanTakeLeft, realEuclideanTakeRight]
    rw [hyz'] at hyz
    refine ⟨y, z, ?_⟩
    simpa [F, L, Function.comp_apply] using hyz

/-- Closure under complements for all arities.  A complement theorem for a
particular geometric family should produce a proof of this proposition. -/
def HasProjectedZeroComplements
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ (n : ℕ) (s : Set (RealEuclidean n)),
    IsProjectedZeroSet G s → IsProjectedZeroSet G sᶜ

/-- Project away a final coordinate block using universal quantification. -/
def realEuclideanUniversalProjection {n m : ℕ}
    (s : Set (RealEuclidean (n + m))) : Set (RealEuclidean n) :=
  {x | ∀ y : RealEuclidean m, realEuclideanAppend x y ∈ s}

/-- Complement closure turns the elementary existential projection rule into
the universal-quantifier rule by `∀y, P y ↔ ¬ ∃y, ¬ P y`. -/
theorem IsProjectedZeroSet.universalProjection
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hcompl : HasProjectedZeroComplements G)
    {n m : ℕ} {s : Set (RealEuclidean (n + m))}
    (hs : IsProjectedZeroSet G s) :
    IsProjectedZeroSet G (realEuclideanUniversalProjection s) := by
  have hscompl : IsProjectedZeroSet G sᶜ := hcompl (n + m) s hs
  have hproj : IsProjectedZeroSet G
      (realEuclideanExistentialProjection sᶜ) :=
    hscompl.existentialProjection hG
  have hresult : IsProjectedZeroSet G
      (realEuclideanExistentialProjection sᶜ)ᶜ :=
    hcompl n (realEuclideanExistentialProjection sᶜ) hproj
  convert hresult using 1
  ext x
  simp [realEuclideanUniversalProjection,
    realEuclideanExistentialProjection]

/-! ## Finite components on the real line -/

private theorem unaryPieceDecomposable_Icc_total (a b : ℝ) :
    UnaryPieceDecomposable (Icc a b) := by
  by_cases hab : a ≤ b
  · exact unaryPieceDecomposable_Icc hab
  · simpa [not_le.mp hab] using unaryPieceDecomposable_empty

private theorem unaryPieceDecomposable_Ico_total (a b : ℝ) :
    UnaryPieceDecomposable (Ico a b) := by
  by_cases hab : a < b
  · exact unaryPieceDecomposable_Ico hab
  · simpa [not_lt.mp hab] using unaryPieceDecomposable_empty

private theorem unaryPieceDecomposable_Ioc_total (a b : ℝ) :
    UnaryPieceDecomposable (Ioc a b) := by
  by_cases hab : a < b
  · exact unaryPieceDecomposable_Ioc hab
  · simpa [not_lt.mp hab] using unaryPieceDecomposable_empty

/-- Every preconnected subset of the real line has the project's exact finite
point/open-interval decomposition.  Mathlib classifies such a set as one of
the nine interval shapes (or the empty set); closed endpoints become point
pieces. -/
theorem IsPreconnected.unaryPieceDecomposable
    {s : Set ℝ} (hs : IsPreconnected s) : UnaryPieceDecomposable s := by
  have h := hs.mem_intervals
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · rw [h]
    exact unaryPieceDecomposable_Icc_total _ _
  · rw [h]
    exact unaryPieceDecomposable_Ico_total _ _
  · rw [h]
    exact unaryPieceDecomposable_Ioc_total _ _
  · rw [h]
    exact unaryPieceDecomposable_Ioo _ _
  · rw [h]
    exact unaryPieceDecomposable_Ici _
  · rw [h]
    exact unaryPieceDecomposable_Ioi _
  · rw [h]
    exact unaryPieceDecomposable_Iic _
  · rw [h]
    exact unaryPieceDecomposable_Iio _
  · rw [h]
    exact unaryPieceDecomposable_univ
  · rw [h]
    exact unaryPieceDecomposable_empty

/-- A chosen point representing a connected component. -/
noncomputable def connectedComponentRepresentative
    (s : Set ℝ) (c : ConnectedComponents s) : s :=
  Classical.choose (ConnectedComponents.surjective_coe c)

@[simp]
theorem connectedComponentRepresentative_mk
    (s : Set ℝ) (c : ConnectedComponents s) :
    (connectedComponentRepresentative s c : ConnectedComponents s) = c :=
  Classical.choose_spec (ConnectedComponents.surjective_coe c)

/-- The image in `ℝ` of a connected component of the subtype `s`. -/
def realConnectedComponentCarrier
    (s : Set ℝ) (c : ConnectedComponents s) : Set ℝ :=
  Subtype.val '' connectedComponent (connectedComponentRepresentative s c)

theorem isConnected_realConnectedComponentCarrier
    (s : Set ℝ) (c : ConnectedComponents s) :
    IsConnected (realConnectedComponentCarrier s c) := by
  exact isConnected_connectedComponent.image Subtype.val
    continuous_subtype_val.continuousOn

/-- The carriers of the connected components of the subtype `s` cover `s`. -/
theorem iUnion_realConnectedComponentCarrier (s : Set ℝ) :
    ⋃ c : ConnectedComponents s, realConnectedComponentCarrier s c = s := by
  ext x
  simp only [Set.mem_iUnion, realConnectedComponentCarrier, Set.mem_image]
  constructor
  · rintro ⟨c, p, hp, rfl⟩
    exact p.2
  · intro hx
    let p : s := ⟨x, hx⟩
    let c : ConnectedComponents s := (p : ConnectedComponents s)
    refine ⟨c, p, ?_, rfl⟩
    rw [← ConnectedComponents.coe_eq_coe']
    exact (connectedComponentRepresentative_mk s c).symm

/-- A finite union of unary-piece decomposable sets, indexed by any finite
type, is unary-piece decomposable. -/
theorem unaryPieceDecomposable_iUnion_finite
    {ι : Type*} [Finite ι] (s : ι → Set ℝ)
    (hs : ∀ i, UnaryPieceDecomposable (s i)) :
    UnaryPieceDecomposable (⋃ i, s i) := by
  let _ := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  rw [show (⋃ i, s i) = ⋃ j : Fin (Fintype.card ι), s (e j) by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, by simpa using hi⟩
    · rintro ⟨j, hj⟩
      exact ⟨e j, hj⟩]
  exact unaryPieceDecomposable_iUnion_fin
    (fun j ↦ s (e j)) (fun j ↦ hs (e j))

/-- A real set with finitely many connected components has the exact finite
point/open-interval decomposition used by `OMinimal`. -/
theorem unaryPieceDecomposable_of_finite_connectedComponents
    (s : Set ℝ) [Finite (ConnectedComponents s)] :
    UnaryPieceDecomposable s := by
  rw [← iUnion_realConnectedComponentCarrier s]
  apply unaryPieceDecomposable_iUnion_finite
  intro c
  exact IsPreconnected.unaryPieceDecomposable
    (isConnected_realConnectedComponentCarrier s c).isPreconnected

/-- An explicit extended-cardinal bound makes the connected-component type
finite and hence gives a unary-piece decomposition. -/
theorem unaryPieceDecomposable_of_enatCard_connectedComponents_le
    (s : Set ℝ) (N : ℕ)
    (hcard : ENat.card (ConnectedComponents s) ≤ N) :
    UnaryPieceDecomposable s := by
  let _ : Finite (ConnectedComponents s) :=
    ENat.card_lt_top.mp (hcard.trans_lt (by simp))
  exact unaryPieceDecomposable_of_finite_connectedComponents s

/-! ## The W5-to-unary endpoint -/

/-- The image of a subset of `ℝ¹` under its unique coordinate. -/
def realEuclideanOneCoordinateImage
    (s : Set (RealEuclidean 1)) : Set ℝ :=
  {x | ∃ v ∈ s, v 0 = x}

/-- The coordinate map from a subtype of `ℝ¹` to its scalar image. -/
def realEuclideanOneToCoordinateImage
    (s : Set (RealEuclidean 1)) :
    s → realEuclideanOneCoordinateImage s :=
  fun v ↦ ⟨v.1 0, v.1, v.2, rfl⟩

theorem continuous_realEuclideanOneToCoordinateImage
    (s : Set (RealEuclidean 1)) :
    Continuous (realEuclideanOneToCoordinateImage s) := by
  apply Continuous.subtype_mk
  exact (continuous_apply 0).comp continuous_subtype_val

theorem surjective_realEuclideanOneToCoordinateImage
    (s : Set (RealEuclidean 1)) :
    Function.Surjective (realEuclideanOneToCoordinateImage s) := by
  rintro ⟨x, v, hv, hvx⟩
  refine ⟨⟨v, hv⟩, ?_⟩
  apply Subtype.ext
  exact hvx

/-- The one-dimensional instance of W5 already forces the scalar coordinate
image of a projected zero set to have a unary-piece decomposition. -/
theorem IsProjectedZeroSet.coordinateImage_unaryPieceDecomposable
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    {s : Set (RealEuclidean 1)} (hs : IsProjectedZeroSet G s) :
    UnaryPieceDecomposable (realEuclideanOneCoordinateImage s) := by
  obtain ⟨N, hN⟩ := hs.exists_matrixSection_component_bound hG hUFF
  have hsCard : ENat.card (ConnectedComponents s) ≤ N := by
    have hsection :
        {x : RealEuclidean 1 |
          flatSquareMatrixMulVec (0 : FlatSquareMatrix 1) x = 0} =
          Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      funext i
      simp [flatSquareMatrixMulVec, flatSquareMatrixEntry]
    have h := hN (0 : FlatSquareMatrix 1) (0 : RealEuclidean 1)
    rw [hsection, Set.inter_univ] at h
    exact h
  have hcoordCard :
      ENat.card (ConnectedComponents (realEuclideanOneCoordinateImage s)) ≤ N :=
    (enatCard_connectedComponents_le_of_continuous_surjective
      (continuous_realEuclideanOneToCoordinateImage s)
      (surjective_realEuclideanOneToCoordinateImage s)).trans hsCard
  exact unaryPieceDecomposable_of_enatCard_connectedComponents_le
    (realEuclideanOneCoordinateImage s) N hcoordCard

/-- Final elementary reduct from unary projected-zero membership and uniform
fiber finiteness to the project's exact o-minimality statement.  The premise
`hdef` is precisely the remaining first-order/complement bridge. -/
theorem oMinimal_of_unary_definable_isProjectedZeroSet
    (A : ℝ → ℝ)
    (G : (n : ℕ) → Set (RealEuclideanFunction n))
    (hG : IsGeometricFunctionFamily G)
    (hUFF : HasUniformFiberFiniteness G)
    (hdef : ∀ s : Set ℝ, UnaryDefinable A s →
      IsProjectedZeroSet G {v : RealEuclidean 1 | v 0 ∈ s}) :
    OMinimal A := by
  intro s hs
  have hpieces :=
    (hdef s hs).coordinateImage_unaryPieceDecomposable hG hUFF
  have himage : realEuclideanOneCoordinateImage
      {v : RealEuclidean 1 | v 0 ∈ s} = s := by
    ext x
    simp only [realEuclideanOneCoordinateImage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      exact ⟨fun _ ↦ x, hx, rfl⟩
  rw [himage] at hpieces
  exact hpieces

/-- Abel-family specialization of the final elementary reduct. -/
theorem oMinimal_of_abel_unary_definable_isProjectedZeroSet
    (A : ℝ → ℝ)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A))
    (hdef : ∀ s : Set ℝ, UnaryDefinable A s →
      IsProjectedZeroSet (abelGeometricFamily A)
        {v : RealEuclidean 1 | v 0 ∈ s}) :
    OMinimal A :=
  oMinimal_of_unary_definable_isProjectedZeroSet A
    (abelGeometricFamily A)
    (isGeometricFunctionFamily_abelGeometricFamily A) hUFF hdef

end AbelFormalization
