import AbelFormalization.Definability
import AbelFormalization.ProjectedZeroFirstOrderBridge
import AbelFormalization.ProjectedZeroPolynomialSigns

/-!
# Abel first-order definability from projected zero sets

This file closes the internal first-order part of the projected-zero argument.
It compiles every nested Abel term to a projected-zero graph, proves the
equality and strict-order atoms, and then inducts on mathlib's bounded-formula
syntax.  Implication uses Boolean closure, and the `all` constructor uses the
universal projection theorem from `ProjectedZeroFirstOrderBridge`.

Consequently complement closure is the only first-order closure hypothesis:
every unary Abel-definable set is projected zero.  Combined with uniform
fiber finiteness, this gives the project's exact o-minimality statement.
-/

noncomputable section

open Set Function
open FirstOrder FirstOrder.Language

namespace AbelFormalization

set_option autoImplicit false

/-! ## Linear pullbacks -/

/-- Apply a linear map to the visible block and leave a projected-zero witness
block unchanged. -/
def realEuclideanVisibleLinearMap {m n : ℕ}
    (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n) (q : ℕ) :
    RealEuclidean (m + q) →ₗ[ℝ] RealEuclidean (n + q) where
  toFun v := realEuclideanAppend (L (realEuclideanTakeLeft v))
    (realEuclideanTakeRight v)
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · have hleft : realEuclideanTakeLeft (v + w) =
          realEuclideanTakeLeft v + realEuclideanTakeLeft w := by
        funext j
        rfl
      rw [hleft, L.map_add]
      simp
    · simp [realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
    · have hleft : realEuclideanTakeLeft (c • v) =
          c • realEuclideanTakeLeft v := by
        funext j
        rfl
      rw [hleft, L.map_smul]
      simp
    · simp [realEuclideanTakeRight]

@[simp]
theorem realEuclideanVisibleLinearMap_append {m n q : ℕ}
    (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n)
    (x : RealEuclidean m) (z : RealEuclidean q) :
    realEuclideanVisibleLinearMap L q (realEuclideanAppend x z) =
      realEuclideanAppend (L x) z := by
  simp [realEuclideanVisibleLinearMap]

/-- Projected zero sets are closed under arbitrary linear pullback of their
visible coordinates. -/
theorem IsProjectedZeroSet.linear_preimage
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    {m n : ℕ} {s : Set (RealEuclidean n)}
    (hs : IsProjectedZeroSet G s)
    (L : RealEuclidean m →ₗ[ℝ] RealEuclidean n) :
    IsProjectedZeroSet G (L ⁻¹' s) := by
  obtain ⟨q, f, hf, rfl⟩ := hs
  let V := realEuclideanVisibleLinearMap L q
  let F : RealEuclideanFunction (m + q) := f ∘ V
  have hF : F ∈ G (m + q) := hG.affine_comp hf V.toAffineMap
  refine ⟨q, F, hF, ?_⟩
  ext x
  simp [F, V, Function.comp_apply]

/-! ## Flattening term graphs -/

/-- From coordinates `(x,y,u,v)`, retain `(x,u)`. -/
def realEuclideanBinaryGraphLeftLinearMap (d : ℕ) :
    RealEuclidean ((d + 1) + 2) →ₗ[ℝ] RealEuclidean (d + 1) where
  toFun w := realEuclideanAppend
    (realEuclideanTakeLeft
      (realEuclideanTakeLeft (n := d + 1) (m := 2) w))
    (fun _ : Fin 1 ↦
      realEuclideanTakeRight (n := d + 1) (m := 2) w 0)
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [realEuclideanTakeLeft, realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [realEuclideanTakeLeft, realEuclideanTakeRight]

/-- From coordinates `(x,y,u,v)`, retain `(x,v)`. -/
def realEuclideanBinaryGraphRightLinearMap (d : ℕ) :
    RealEuclidean ((d + 1) + 2) →ₗ[ℝ] RealEuclidean (d + 1) where
  toFun w := realEuclideanAppend
    (realEuclideanTakeLeft
      (realEuclideanTakeLeft (n := d + 1) (m := 2) w))
    (fun _ : Fin 1 ↦
      realEuclideanTakeRight (n := d + 1) (m := 2) w 1)
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [realEuclideanTakeLeft, realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [realEuclideanTakeLeft, realEuclideanTakeRight]

/-- From coordinates `(x,y,u,v)`, retain `(u,v,y)`. -/
def realEuclideanBinaryGraphOperationLinearMap (d : ℕ) :
    RealEuclidean ((d + 1) + 2) →ₗ[ℝ] RealEuclidean (2 + 1) where
  toFun w := realEuclideanAppend
    (realEuclideanTakeRight (n := d + 1) (m := 2) w)
    (realEuclideanTakeRight
      (realEuclideanTakeLeft (n := d + 1) (m := 2) w))
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [realEuclideanTakeLeft, realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [realEuclideanTakeLeft, realEuclideanTakeRight]

/-- Compose a binary scalar graph with two already compiled scalar graphs.
The two intermediate scalar values are appended as existential coordinates. -/
theorem IsProjectedZeroSet.binaryGraph_comp
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    {d : ℕ} {f g : RealEuclideanFunction d}
    {op : RealEuclideanFunction 2}
    (hf : IsProjectedZeroSet G (realEuclideanGraph f))
    (hg : IsProjectedZeroSet G (realEuclideanGraph g))
    (hop : IsProjectedZeroSet G (realEuclideanGraph op)) :
    IsProjectedZeroSet G
      (realEuclideanGraph (fun x ↦ op ![f x, g x])) := by
  let L := realEuclideanBinaryGraphLeftLinearMap d
  let R := realEuclideanBinaryGraphRightLinearMap d
  let O := realEuclideanBinaryGraphOperationLinearMap d
  have hf' := hf.linear_preimage hG L
  have hg' := hg.linear_preimage hG R
  have hop' := hop.linear_preimage hG O
  have hall := (hf'.inter hG hg').inter hG hop'
  have hproj := hall.existentialProjection hG
  convert hproj using 1
  ext xy
  let x := realEuclideanTakeLeft (n := d) (m := 1) xy
  let y := realEuclideanTakeRight (n := d) (m := 1) xy 0
  simp only [realEuclideanGraph, realEuclideanExistentialProjection,
    Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
  simp only [L, R, O, realEuclideanBinaryGraphLeftLinearMap,
    realEuclideanBinaryGraphRightLinearMap,
    realEuclideanBinaryGraphOperationLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append,
    realEuclideanDropLastLinearMap_append_one,
    realEuclideanAppend_last_one]
  change op ![f x, g x] = y ↔
    ∃ uv : RealEuclidean 2,
      (f x = uv 0 ∧ g x = uv 1) ∧ op uv = y
  constructor
  · intro h
    refine ⟨![f x, g x], ⟨⟨rfl, rfl⟩, ?_⟩⟩
    simpa using h
  · rintro ⟨uv, ⟨⟨hu, hv⟩, hopuv⟩⟩
    have huv : uv = ![f x, g x] := by
      funext i
      fin_cases i
      · exact hu.symm
      · exact hv.symm
    rwa [← huv]

/-- From coordinates `(x,u,v)`, retain `(x,u)`. -/
def realEuclideanBinaryAtomLeftLinearMap (d : ℕ) :
    RealEuclidean (d + 2) →ₗ[ℝ] RealEuclidean (d + 1) where
  toFun w := realEuclideanAppend (realEuclideanTakeLeft w)
    (fun _ : Fin 1 ↦ realEuclideanTakeRight w 0)
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [realEuclideanTakeLeft, realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [realEuclideanTakeLeft, realEuclideanTakeRight]

/-- From coordinates `(x,u,v)`, retain `(x,v)`. -/
def realEuclideanBinaryAtomRightLinearMap (d : ℕ) :
    RealEuclidean (d + 2) →ₗ[ℝ] RealEuclidean (d + 1) where
  toFun w := realEuclideanAppend (realEuclideanTakeLeft w)
    (fun _ : Fin 1 ↦ realEuclideanTakeRight w 1)
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [realEuclideanTakeLeft, realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [realEuclideanTakeLeft, realEuclideanTakeRight]

/-- From coordinates `(x,u,v)`, retain the value pair `(u,v)`. -/
def realEuclideanBinaryAtomPairLinearMap (d : ℕ) :
    RealEuclidean (d + 2) →ₗ[ℝ] RealEuclidean 2 where
  toFun := realEuclideanTakeRight
  map_add' := by
    intro v w
    funext k
    simp [realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext k
    simp [realEuclideanTakeRight]

/-- Pull a binary predicate back along two functions whose graphs are
projected zero sets.  The two function values are existential witnesses. -/
theorem IsProjectedZeroSet.binaryGraph_atom
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    {d : ℕ} {f g : RealEuclideanFunction d}
    {p : Set (RealEuclidean 2)}
    (hf : IsProjectedZeroSet G (realEuclideanGraph f))
    (hg : IsProjectedZeroSet G (realEuclideanGraph g))
    (hp : IsProjectedZeroSet G p) :
    IsProjectedZeroSet G {x | ![f x, g x] ∈ p} := by
  let L := realEuclideanBinaryAtomLeftLinearMap d
  let R := realEuclideanBinaryAtomRightLinearMap d
  let P := realEuclideanBinaryAtomPairLinearMap d
  have hf' := hf.linear_preimage hG L
  have hg' := hg.linear_preimage hG R
  have hp' := hp.linear_preimage hG P
  have hall := (hf'.inter hG hg').inter hG hp'
  have hproj := hall.existentialProjection hG
  convert hproj using 1
  ext x
  simp only [realEuclideanExistentialProjection, realEuclideanGraph,
    Set.mem_ofPred_eq,
    Set.mem_inter_iff, Set.mem_preimage]
  simp only [L, R, P, realEuclideanBinaryAtomLeftLinearMap,
    realEuclideanBinaryAtomRightLinearMap,
    realEuclideanBinaryAtomPairLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk,
    realEuclideanTakeLeft_append, realEuclideanTakeRight_append,
    realEuclideanDropLastLinearMap_append_one,
    realEuclideanAppend_last_one]
  change ![f x, g x] ∈ p ↔
    ∃ uv : RealEuclidean 2,
      (f x = uv 0 ∧ g x = uv 1) ∧ uv ∈ p
  constructor
  · intro h
    exact ⟨![f x, g x], ⟨⟨rfl, rfl⟩, h⟩⟩
  · rintro ⟨uv, ⟨⟨hu, hv⟩, huv⟩⟩
    have heq : uv = ![f x, g x] := by
      funext i
      fin_cases i
      · exact hu.symm
      · exact hv.symm
    rwa [← heq]

/-- Equality of the two coordinates of a pair is a polynomial zero set. -/
theorem isProjectedZeroSet_pair_eq
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) :
    IsProjectedZeroSet G
      {z : RealEuclidean 2 | z 0 = z 1} := by
  let P : MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.X 0 - MvPolynomial.X 1
  have h := isProjectedZeroSet_polynomial_zero hG P
  simpa [P, sub_eq_zero] using h

/-- Strict order on the two coordinates of a pair is a polynomial positive
set. -/
theorem isProjectedZeroSet_pair_lt
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) :
    IsProjectedZeroSet G
      {z : RealEuclidean 2 | z 0 < z 1} := by
  let P : MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.X 1 - MvPolynomial.X 0
  have h := isProjectedZeroSet_polynomial_pos hG P
  simpa [P, sub_pos] using h

/-- Evaluation of an Abel term as a function of one flat finite coordinate
block. -/
def abelTermRealization (A : ℝ → ℝ) {d : ℕ}
    (t : abelLanguage[[(Set.univ : Set ℝ)]].Term (Fin d)) :
    RealEuclideanFunction d := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  exact fun v ↦ t.realize v

/-- Every (possibly nested) Abel term has a projected-zero graph.  Function
nodes are flattened by existentially adjoining the values of their immediate
subterms. -/
theorem abelTermRealization_graph_isProjectedZeroSet
    (A : ℝ → ℝ) {d : ℕ}
    (t : abelLanguage[[(Set.univ : Set ℝ)]].Term (Fin d)) :
    IsProjectedZeroSet (abelGeometricFamily A)
      (realEuclideanGraph (abelTermRealization A t)) := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  let hG := isGeometricFunctionFamily_abelGeometricFamily A
  induction t with
  | var i =>
      apply hG.isProjectedZeroSet_graph
      simpa [abelTermRealization] using
        hG.polynomial (MvPolynomial.X i)
  | @func k f ts ih =>
      cases f with
      | inl f =>
          cases f with
          | add =>
              have hx0 : (fun z : RealEuclidean 2 ↦ z 0) ∈
                  abelGeometricFamily A 2 := by
                simpa using hG.polynomial (MvPolynomial.X (0 : Fin 2))
              have hx1 : (fun z : RealEuclidean 2 ↦ z 1) ∈
                  abelGeometricFamily A 2 := by
                simpa using hG.polynomial (MvPolynomial.X (1 : Fin 2))
              have hop : IsProjectedZeroSet (abelGeometricFamily A)
                  (realEuclideanGraph
                    (fun z : RealEuclidean 2 ↦ z 0 + z 1)) := by
                apply hG.isProjectedZeroSet_graph
                convert hG.add hx0 hx1 using 1
                funext z
                rfl
              have hcomp := IsProjectedZeroSet.binaryGraph_comp hG
                (ih 0) (ih 1) hop
              convert hcomp using 1
              ext v
              simp [Set.mem_ofPred_eq, abelTermRealization,
                realEuclideanGraph, Term.realize]
              with_unfolding_all rfl
          | mul =>
              have hx0 : (fun z : RealEuclidean 2 ↦ z 0) ∈
                  abelGeometricFamily A 2 := by
                simpa using hG.polynomial (MvPolynomial.X (0 : Fin 2))
              have hx1 : (fun z : RealEuclidean 2 ↦ z 1) ∈
                  abelGeometricFamily A 2 := by
                simpa using hG.polynomial (MvPolynomial.X (1 : Fin 2))
              have hop : IsProjectedZeroSet (abelGeometricFamily A)
                  (realEuclideanGraph
                    (fun z : RealEuclidean 2 ↦ z 0 * z 1)) := by
                apply hG.isProjectedZeroSet_graph
                convert hG.mul hx0 hx1 using 1
                funext z
                rfl
              have hcomp := IsProjectedZeroSet.binaryGraph_comp hG
                (ih 0) (ih 1) hop
              convert hcomp using 1
              ext v
              simp [Set.mem_ofPred_eq, abelTermRealization,
                realEuclideanGraph, Term.realize]
              with_unfolding_all rfl
          | c0 =>
              let ℓ : RealEuclidean 2 →ᵃ[ℝ] ℝ := AffineMap.proj 0
              have hopMem : (fun z : RealEuclidean 2 ↦ C0 A (z 0)) ∈
                  abelGeometricFamily A 2 := by
                convert Cr_comp_affine_mem_abelGeometricFamily A 0 ℓ using 1
                funext z
                simp [ℓ, Cr_zero]
              have hop : IsProjectedZeroSet (abelGeometricFamily A)
                  (realEuclideanGraph
                    (fun z : RealEuclidean 2 ↦ C0 A (z 0))) :=
                hG.isProjectedZeroSet_graph hopMem
              have hcomp := IsProjectedZeroSet.binaryGraph_comp hG
                (ih 0) (ih 0) hop
              convert hcomp using 1
              ext v
              simp [Set.mem_ofPred_eq, abelTermRealization,
                realEuclideanGraph, Term.realize]
              with_unfolding_all rfl
      | inr f =>
          cases k with
          | zero =>
              have hgraph := hG.isProjectedZeroSet_graph
                (hG.const_mem (n := d) (f : ℝ))
              convert hgraph using 1
              ext v
              simp [Set.mem_ofPred_eq, abelTermRealization,
                realEuclideanGraph, Term.realize]
              with_unfolding_all rfl
          | succ k =>
              nomatch f

/-- Evaluate a term whose variables are split into free and bound blocks on
the corresponding flat Euclidean coordinate block. -/
def abelBoundedTermRealization (A : ℝ → ℝ) {n l : ℕ}
    (t : abelLanguage[[(Set.univ : Set ℝ)]].Term (Fin n ⊕ Fin l)) :
    RealEuclideanFunction (n + l) := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  exact fun v ↦ t.realize
    (Sum.elim (realEuclideanTakeLeft v) (realEuclideanTakeRight v))

/-- Flattening the free/bound variable split preserves term evaluation. -/
theorem abelTermRealization_relabel_finSumFinEquiv
    (A : ℝ → ℝ) {n l : ℕ}
    (t : abelLanguage[[(Set.univ : Set ℝ)]].Term (Fin n ⊕ Fin l)) :
    abelTermRealization A (t.relabel finSumFinEquiv) =
      abelBoundedTermRealization A t := by
  funext v
  simp only [abelTermRealization, abelBoundedTermRealization,
    Term.realize_relabel]
  congr 1
  funext i
  rcases i with i | i
  · simp [Function.comp_apply, realEuclideanTakeLeft]
  · simp [Function.comp_apply, realEuclideanTakeRight]

/-- Every Abel term in a split free/bound context has a projected-zero graph
after the two variable blocks are flattened. -/
theorem abelBoundedTermRealization_graph_isProjectedZeroSet
    (A : ℝ → ℝ) {n l : ℕ}
    (t : abelLanguage[[(Set.univ : Set ℝ)]].Term (Fin n ⊕ Fin l)) :
    IsProjectedZeroSet (abelGeometricFamily A)
      (realEuclideanGraph (abelBoundedTermRealization A t)) := by
  rw [← abelTermRealization_relabel_finSumFinEquiv A t]
  exact abelTermRealization_graph_isProjectedZeroSet A
    (t.relabel finSumFinEquiv)

/-! ## Flattened semantics -/

/-- The realization set of a bounded formula, with the free coordinates first
and the in-scope bound coordinates second. -/
def abelBoundedFormulaRealizationSet
    (A : ℝ → ℝ) {n l : ℕ}
    (φ : abelLanguage[[(Set.univ : Set ℝ)]].BoundedFormula (Fin n) l) :
    Set (RealEuclidean (n + l)) := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  exact {v | φ.Realize (realEuclideanTakeLeft v) (realEuclideanTakeRight v)}

/-- The inverse reassociation `((x,y),z) ↦ (x,(y,z))` of three flat coordinate
blocks. -/
def realEuclideanAssociateRightLinearMap (n m q : ℕ) :
    RealEuclidean ((n + m) + q) →ₗ[ℝ]
      RealEuclidean (n + (m + q)) where
  toFun v := Fin.addCases
    (fun i ↦ v (Fin.castAdd q (Fin.castAdd m i)))
    (fun jk ↦ Fin.addCases
      (fun j ↦ v (Fin.castAdd q (Fin.natAdd n j)))
      (fun k ↦ v (Fin.natAdd (n + m) k)) jk)
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp
    · intro jk
      refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) jk <;> simp
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp
    · intro jk
      refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) jk <;> simp

@[simp]
theorem realEuclideanAssociateRightLinearMap_append
    {n m q : ℕ} (x : RealEuclidean n) (y : RealEuclidean m)
    (z : RealEuclidean q) :
    realEuclideanAssociateRightLinearMap n m q
        (realEuclideanAppend (realEuclideanAppend x y) z) =
      realEuclideanAppend x (realEuclideanAppend y z) := by
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp [realEuclideanAssociateRightLinearMap]
  · intro jk
    refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) jk <;>
      simp [realEuclideanAssociateRightLinearMap]

theorem realEuclideanAssociateRightLinearMap_leftInverse
    (n m q : ℕ) :
    Function.LeftInverse (realEuclideanAssociateRightLinearMap n m q)
      (realEuclideanAssociateLeftLinearMap n m q) := by
  intro v
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp [realEuclideanAssociateLeftLinearMap,
      realEuclideanAssociateRightLinearMap]
  · intro jk
    refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) jk <;>
      simp [realEuclideanAssociateLeftLinearMap,
        realEuclideanAssociateRightLinearMap]

theorem realEuclideanAssociateRightLinearMap_rightInverse
    (n m q : ℕ) :
    Function.RightInverse (realEuclideanAssociateRightLinearMap n m q)
      (realEuclideanAssociateLeftLinearMap n m q) := by
  intro v
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro ij
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) ij <;>
      simp [realEuclideanAssociateLeftLinearMap,
        realEuclideanAssociateRightLinearMap]
  · intro i
    simp [realEuclideanAssociateLeftLinearMap,
      realEuclideanAssociateRightLinearMap]

/-- The linear equivalence reassociating three flat coordinate blocks. -/
def realEuclideanAssociateLeftLinearEquiv (n m q : ℕ) :
    RealEuclidean (n + (m + q)) ≃ₗ[ℝ]
      RealEuclidean ((n + m) + q) where
  toLinearMap := realEuclideanAssociateLeftLinearMap n m q
  invFun := realEuclideanAssociateRightLinearMap n m q
  left_inv := realEuclideanAssociateRightLinearMap_leftInverse n m q
  right_inv := realEuclideanAssociateRightLinearMap_rightInverse n m q

@[simp]
theorem realEuclideanAppend_takeLeft_takeRight {n m : ℕ}
    (v : RealEuclidean (n + m)) :
    realEuclideanAppend (realEuclideanTakeLeft v)
      (realEuclideanTakeRight v) = v := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun k ↦ ?_) i <;>
    simp [realEuclideanTakeLeft, realEuclideanTakeRight]

/-- Rebracket a flat vector and append one scalar to its bound-variable block.
This is the coordinate operation appearing in `BoundedFormula.realize_all`. -/
def realEuclideanSnocBound {n l : ℕ}
    (v : RealEuclidean (n + l)) (a : ℝ) :
    RealEuclidean (n + (l + 1)) :=
  realEuclideanAppend (realEuclideanTakeLeft v)
    (realEuclideanAppend (realEuclideanTakeRight v)
      (fun _ : Fin 1 ↦ a))

@[simp]
theorem realEuclideanTakeLeft_snocBound {n l : ℕ}
    (v : RealEuclidean (n + l)) (a : ℝ) :
    realEuclideanTakeLeft (realEuclideanSnocBound v a) =
      realEuclideanTakeLeft v := by
  simp [realEuclideanSnocBound]

@[simp]
theorem realEuclideanTakeRight_snocBound {n l : ℕ}
    (v : RealEuclidean (n + l)) (a : ℝ) :
    realEuclideanTakeRight (realEuclideanSnocBound v a) =
      Fin.snoc (realEuclideanTakeRight v) a := by
  have hright : realEuclideanTakeRight (realEuclideanSnocBound v a) =
      realEuclideanAppend (realEuclideanTakeRight v)
        (fun _ : Fin 1 ↦ a) := by
    simp [realEuclideanSnocBound]
  rw [hright, Fin.snoc_eq_append]
  change Fin.append (realEuclideanTakeRight v) (fun _ : Fin 1 ↦ a) =
    Fin.append (realEuclideanTakeRight v) (Fin.cons a Fin.elim0)
  congr 1
  funext i
  exact Fin.eq_zero i ▸ rfl

/-- Universal projection in the precise bracketing used by bounded-formula
semantics. -/
def realEuclideanUniversalBoundProjection {n l : ℕ}
    (s : Set (RealEuclidean (n + (l + 1)))) :
    Set (RealEuclidean (n + l)) :=
  {v | ∀ a : ℝ, realEuclideanSnocBound v a ∈ s}

/-- The existing universal-projection theorem, transported across associativity
of the free and bound coordinate blocks. -/
theorem IsProjectedZeroSet.universalBoundProjection
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hcompl : HasProjectedZeroComplements G)
    {n l : ℕ} {s : Set (RealEuclidean (n + (l + 1)))}
    (hs : IsProjectedZeroSet G s) :
    IsProjectedZeroSet G (realEuclideanUniversalBoundProjection s) := by
  let e := realEuclideanAssociateLeftLinearEquiv n l 1
  have himage : IsProjectedZeroSet G (e '' s) :=
    hs.linearEquiv_image hG e
  have hproj := himage.universalProjection hG hcompl
  convert hproj using 1
  ext v
  simp only [realEuclideanUniversalBoundProjection,
    realEuclideanUniversalProjection, Set.mem_ofPred_eq]
  constructor
  · intro h z
    refine ⟨realEuclideanSnocBound v (z 0), h (z 0), ?_⟩
    change realEuclideanAssociateLeftLinearMap n l 1
        (realEuclideanSnocBound v (z 0)) = realEuclideanAppend v z
    rw [show realEuclideanSnocBound v (z 0) =
        realEuclideanAppend (realEuclideanTakeLeft v)
          (realEuclideanAppend (realEuclideanTakeRight v) z) by
      apply congrArg (realEuclideanAppend (realEuclideanTakeLeft v))
      apply congrArg (realEuclideanAppend (realEuclideanTakeRight v))
      funext i
      exact Fin.eq_zero i ▸ rfl]
    rw [realEuclideanAssociateLeftLinearMap_append,
      realEuclideanAppend_takeLeft_takeRight]
  · intro h a
    obtain ⟨w, hw, hew⟩ := h (fun _ : Fin 1 ↦ a)
    have hwEq : w = realEuclideanSnocBound v a := by
      apply e.injective
      rw [hew]
      change realEuclideanAppend v (fun _ : Fin 1 ↦ a) =
        realEuclideanAssociateLeftLinearMap n l 1
          (realEuclideanSnocBound v a)
      rw [show realEuclideanSnocBound v a =
          realEuclideanAppend (realEuclideanTakeLeft v)
            (realEuclideanAppend (realEuclideanTakeRight v)
              (fun _ : Fin 1 ↦ a)) by rfl,
        realEuclideanAssociateLeftLinearMap_append,
        realEuclideanAppend_takeLeft_takeRight]
    rwa [← hwEq]

/-! ## Atomic semantics -/

/-- A package of projected-zero semantics for the two atomic constructors of
mathlib's first-order formulas in every finite context. -/
structure HasProjectedZeroAbelAtomicSemantics (A : ℝ → ℝ) : Prop where
  equal :
    ∀ {n l : ℕ}
      (t₁ t₂ : abelLanguage[[(Set.univ : Set ℝ)]].Term
        (Fin n ⊕ Fin l)),
      IsProjectedZeroSet (abelGeometricFamily A)
        (abelBoundedFormulaRealizationSet A
          (.equal t₁ t₂))
  rel :
    ∀ {n l k : ℕ}
      (R : abelLanguage[[(Set.univ : Set ℝ)]].Relations k)
      (ts : Fin k → abelLanguage[[(Set.univ : Set ℝ)]].Term
        (Fin n ⊕ Fin l)),
      IsProjectedZeroSet (abelGeometricFamily A)
        (abelBoundedFormulaRealizationSet A
          (.rel R ts))

/-- The atomic semantics premise is automatic for the Abel language.  Nested
terms are compiled to graphs, while equality and strict order are pulled back
from their polynomial predicates on a pair of term values. -/
theorem hasProjectedZeroAbelAtomicSemantics (A : ℝ → ℝ) :
    HasProjectedZeroAbelAtomicSemantics A := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  let hG := isGeometricFunctionFamily_abelGeometricFamily A
  constructor
  · intro n l t₁ t₂
    have ht₁ := abelBoundedTermRealization_graph_isProjectedZeroSet A t₁
    have ht₂ := abelBoundedTermRealization_graph_isProjectedZeroSet A t₂
    have h := IsProjectedZeroSet.binaryGraph_atom hG ht₁ ht₂
      (isProjectedZeroSet_pair_eq hG)
    convert h using 1
    ext v
    simp only [abelBoundedFormulaRealizationSet, Set.mem_ofPred_eq,
      BoundedFormula.Realize, abelBoundedTermRealization,
      Matrix.cons_val_zero, Matrix.cons_val_one]
  · intro n l k R ts
    cases R with
    | inl R =>
        cases R with
        | lt =>
            have ht₀ :=
              abelBoundedTermRealization_graph_isProjectedZeroSet A (ts 0)
            have ht₁ :=
              abelBoundedTermRealization_graph_isProjectedZeroSet A (ts 1)
            have h := IsProjectedZeroSet.binaryGraph_atom hG ht₀ ht₁
              (isProjectedZeroSet_pair_lt hG)
            convert h using 1
            ext v
            simp only [abelBoundedFormulaRealizationSet, Set.mem_ofPred_eq,
              BoundedFormula.Realize, abelBoundedTermRealization,
              Matrix.cons_val_zero, Matrix.cons_val_one]
            with_unfolding_all rfl
    | inr R =>
        nomatch R

/-! ## Formula induction -/

/-- Every bounded Abel formula has projected-zero semantics once its atomic
term graphs do.  All Boolean and quantifier steps are discharged here. -/
theorem hasProjectedZero_abelformula_semantics
    {A : ℝ → ℝ}
    (hcompl : HasProjectedZeroComplements (abelGeometricFamily A))
    (hatomic : HasProjectedZeroAbelAtomicSemantics A)
    {n l : ℕ}
    (φ : abelLanguage[[(Set.univ : Set ℝ)]].BoundedFormula (Fin n) l) :
    IsProjectedZeroSet (abelGeometricFamily A)
      (abelBoundedFormulaRealizationSet A φ) := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  let hG := isGeometricFunctionFamily_abelGeometricFamily A
  induction φ with
  | @falsum l =>
      simpa [abelBoundedFormulaRealizationSet, BoundedFormula.Realize] using
        (isProjectedZeroSet_empty hG :
          IsProjectedZeroSet (abelGeometricFamily A)
            (∅ : Set (RealEuclidean (n + l))))
  | @equal l t₁ t₂ =>
      exact hatomic.equal t₁ t₂
  | @rel l k R ts =>
      exact hatomic.rel R ts
  | @imp l φ ψ ihφ ihψ =>
      have hnot : IsProjectedZeroSet (abelGeometricFamily A)
          (abelBoundedFormulaRealizationSet A φ)ᶜ :=
        hcompl (n + l) (abelBoundedFormulaRealizationSet A φ) ihφ
      have hor := hnot.union hG ihψ
      convert hor using 1
      ext v
      simp only [abelBoundedFormulaRealizationSet, Set.mem_union,
        Set.mem_compl_iff, Set.mem_ofPred_eq,
        BoundedFormula.realize_imp]
      constructor
      · intro h
        by_cases hp : φ.Realize (realEuclideanTakeLeft v)
            (realEuclideanTakeRight v)
        · exact Or.inr (h hp)
        · exact Or.inl hp
      · rintro (hp | hq) hφ
        · exact (hp hφ).elim
        · exact hq
  | @all l φ ih =>
      have hproj := ih.universalBoundProjection hG hcompl
      convert hproj using 1
      ext v
      simp only [abelBoundedFormulaRealizationSet,
        realEuclideanUniversalBoundProjection, Set.mem_ofPred_eq,
        BoundedFormula.realize_all]
      constructor
      · intro h a
        simpa using h a
      · intro h a
        simpa using h a

/-! ## Definability and o-minimality endpoints -/

/-- Every unary set definable with arbitrary real parameters in the Abel
structure is a projected zero set in its canonical `RealEuclidean 1`
coordinate representation. -/
theorem unaryDefinable_isProjectedZeroSet_of_atomic
    {A : ℝ → ℝ}
    (hcompl : HasProjectedZeroComplements (abelGeometricFamily A))
    (hatomic : HasProjectedZeroAbelAtomicSemantics A)
    {s : Set ℝ} (hs : UnaryDefinable A s) :
    IsProjectedZeroSet (abelGeometricFamily A)
      {v : RealEuclidean 1 | v 0 ∈ s} := by
  let _ : abelLanguage.Structure ℝ := abelStructure A
  change (Set.univ : Set ℝ).Definable abelLanguage
      {v : Fin 1 → ℝ | v 0 ∈ s} at hs
  rcases hs with ⟨φ, hφ⟩
  have hsem := hasProjectedZero_abelformula_semantics hcompl hatomic φ
  rw [hφ]
  convert hsem using 1
  ext v
  simp only [Set.mem_ofPred_eq, abelBoundedFormulaRealizationSet]
  have hleft : realEuclideanTakeLeft (n := 1) (m := 0) v = v := by
      funext i
      simp [realEuclideanTakeLeft]
  rw [hleft]
  simp only [Formula.Realize]
  rw [show (@default (Fin 0 → ℝ) Unique.instInhabited) =
      realEuclideanTakeRight (n := 1) (m := 0) v from
    Subsingleton.elim _ _]

/-- Every unary set definable with arbitrary real parameters in the Abel
structure is projected zero once the Abel geometric family is closed under
complements.  No analytic property of `A` is needed for this syntactic
statement. -/
theorem unaryDefinable_isProjectedZeroSet
    {A : ℝ → ℝ}
    (hcompl : HasProjectedZeroComplements (abelGeometricFamily A))
    {s : Set ℝ} (hs : UnaryDefinable A s) :
    IsProjectedZeroSet (abelGeometricFamily A)
      {v : RealEuclidean 1 | v 0 ∈ s} :=
  unaryDefinable_isProjectedZeroSet_of_atomic hcompl
    (hasProjectedZeroAbelAtomicSemantics A) hs

/-- The specialization requested for Abel solutions.  The proof is inherited
from the stronger syntax theorem, which does not use the Abel equation. -/
theorem IsAbel.unaryDefinable_isProjectedZeroSet
    {A : ℝ → ℝ} (_hA : IsAbel A)
    (hcompl : HasProjectedZeroComplements (abelGeometricFamily A))
    {s : Set ℝ} (hs : UnaryDefinable A s) :
    IsProjectedZeroSet (abelGeometricFamily A)
      {v : RealEuclidean 1 | v 0 ∈ s} :=
  AbelFormalization.unaryDefinable_isProjectedZeroSet hcompl hs

/-- Strongest direct Lion-style endpoint: atomic term-graph compilation,
projected-zero complement closure, and uniform fiber finiteness imply the
project's exact o-minimality statement. -/
theorem oMinimal_of_abel_atomic_projectedZero_and_uniformFiberFiniteness
    {A : ℝ → ℝ}
    (hcompl : HasProjectedZeroComplements (abelGeometricFamily A))
    (hatomic : HasProjectedZeroAbelAtomicSemantics A)
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A)) :
    OMinimal A := by
  exact oMinimal_of_abel_unary_definable_isProjectedZeroSet A hUFF
    (fun _ hs ↦ unaryDefinable_isProjectedZeroSet_of_atomic
      hcompl hatomic hs)

/-- Complement closure and Lion-style uniform fiber finiteness for the Abel
geometric family imply o-minimality of the Abel expansion.  This is stronger
than the Abel-specialized formulation: the implication is purely geometric
and syntactic and therefore holds for every function `A`. -/
theorem oMinimal_of_abel_projectedZeroComplements_and_uniformFiberFiniteness
    {A : ℝ → ℝ}
    (hcompl : HasProjectedZeroComplements (abelGeometricFamily A))
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A)) :
    OMinimal A := by
  exact oMinimal_of_abel_unary_definable_isProjectedZeroSet A hUFF
    (fun _ hs ↦ unaryDefinable_isProjectedZeroSet hcompl hs)

/-- Abel-solution corollary of the strongest geometric criterion. -/
theorem IsAbel.oMinimal_of_projectedZeroComplements_and_uniformFiberFiniteness
    {A : ℝ → ℝ} (_hA : IsAbel A)
    (hcompl : HasProjectedZeroComplements (abelGeometricFamily A))
    (hUFF : HasUniformFiberFiniteness (abelGeometricFamily A)) :
    OMinimal A :=
  oMinimal_of_abel_projectedZeroComplements_and_uniformFiberFiniteness
    hcompl hUFF

end AbelFormalization
