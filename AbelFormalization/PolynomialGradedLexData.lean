import AbelFormalization.ArtinianHomogeneousLayerCover
import AbelFormalization.FiniteWeightIteration
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.Order.PiLex

set_option autoImplicit false

/-!
# A concrete joint grading of a shifted free polynomial module

This file supplies the coefficient-level grading data needed by the finite
lexicographic descent argument.  It deliberately works over an arbitrary
commutative coefficient ring.  Positivity of the ordinary variable degrees
is used only for the finite-support and finite-window results.

The finite window groups all ordinary degrees having the same
lexicographic multidegree before it orders those multidegrees.  Its final
linear equivalence therefore has the literal target

`(i : Fin weightCount) -> orderedWeightPiece i`,

which is the product shape used by `exists_finiteWeightDescent_stabilizes`.
-/

noncomputable section

namespace AbelFormalization

/-! ## Coefficient fibres for a finite free polynomial module -/

variable {B : Type*} [CommRing B] {n r : ℕ}

/-- A coordinate monomial of the finite free polynomial module. -/
abbrev PolynomialModuleTerm (n r : ℕ) := Fin r × (Fin n →₀ ℕ)

section CoefficientFibres

variable {ι : Type*}

/-- The coordinate vector consisting of one coordinate monomial with
coefficient one. -/
def artinianPolynomialModuleTermVector
    (t : PolynomialModuleTerm n r) :
    artinianFreePolynomialModule B n r :=
  artinianPolynomialModuleCoeffEquiv.symm (Finsupp.single t 1)

@[simp]
theorem artinianPolynomialModuleTermVector_coeff
    (t : PolynomialModuleTerm n r) (k : Fin r) (d : Fin n →₀ ℕ) :
    (artinianPolynomialModuleTermVector (B := B) t k).coeff d =
      if t = (k, d) then 1 else 0 := by
  change artinianPolynomialModuleCoeffEquiv
      (artinianPolynomialModuleTermVector (B := B) t) (k, d) = _
  rw [artinianPolynomialModuleTermVector,
    LinearEquiv.apply_symm_apply, Finsupp.single_apply]

theorem artinianPolynomialModuleTermVector_ne_zero [Nontrivial B]
    (t : PolynomialModuleTerm n r) :
    artinianPolynomialModuleTermVector (B := B) t ≠ 0 := by
  rcases t with ⟨k, d⟩
  intro hzero
  have hcoeff := congrArg (fun P => (P k).coeff d) hzero
  rw [artinianPolynomialModuleTermVector_coeff, ite_eq_left rfl,
    Pi.zero_apply, MvPolynomial.coeff_zero] at hcoeff
  exact one_ne_zero hcoeff

/-- The set of coordinate monomials in one fibre of a grading key. -/
def artinianPolynomialModuleFiberTerms
    (key : PolynomialModuleTerm n r → ι) (i : ι) :
    Set (PolynomialModuleTerm n r) :=
  {t | key t = i}

/-- The coefficient submodule in one fibre of a grading key. -/
def artinianPolynomialModuleFiberPiece
    (key : PolynomialModuleTerm n r → ι) (i : ι) :
    Submodule B (artinianFreePolynomialModule B n r) :=
  artinianPolynomialModuleSupported (artinianPolynomialModuleFiberTerms key i)

/-- The coordinate term vector belongs to the fibre selected by its key. -/
theorem artinianPolynomialModuleTermVector_mem_fiber
    (key : PolynomialModuleTerm n r → ι)
    (t : PolynomialModuleTerm n r) (i : ι) (hi : key t = i) :
    artinianPolynomialModuleTermVector (B := B) t ∈
      artinianPolynomialModuleFiberPiece (B := B) key i := by
  classical
  apply (mem_artinianPolynomialModuleSupported _ _).mpr
  intro k d hcoeff
  rw [artinianPolynomialModuleTermVector_coeff] at hcoeff
  by_cases ht : t = (k, d)
  · change key (k, d) = i
    simpa [← ht] using hi
  · rw [ite_eq_right ht] at hcoeff
    exact (hcoeff rfl).elim

/-- Coefficient projection to one fibre of an arbitrary grading key. -/
def artinianPolynomialModuleFiberComponent [DecidableEq ι]
    (key : PolynomialModuleTerm n r → ι) (i : ι) :
    artinianFreePolynomialModule B n r →ₗ[B]
      artinianFreePolynomialModule B n r :=
  { toFun := fun P => artinianPolynomialModuleCoeffEquiv.symm
      ((artinianPolynomialModuleCoeffEquiv P).filter (fun t => key t = i))
    map_add' := by
      intro P Q
      simp only [map_add, Finsupp.filter_add]
    map_smul' := by
      intro c P
      simp only [map_smul, Finsupp.filter_smul, RingHom.id_apply] }

@[simp]
theorem artinianPolynomialModuleFiberComponent_coeff [DecidableEq ι]
    (key : PolynomialModuleTerm n r → ι) (i : ι)
    (P : artinianFreePolynomialModule B n r)
    (k : Fin r) (d : Fin n →₀ ℕ) :
    (artinianPolynomialModuleFiberComponent key i P k).coeff d =
      if key (k, d) = i then (P k).coeff d else 0 := by
  change artinianPolynomialModuleCoeffEquiv
      (artinianPolynomialModuleFiberComponent key i P) (k, d) = _
  change artinianPolynomialModuleCoeffEquiv
      (artinianPolynomialModuleCoeffEquiv.symm
        ((artinianPolynomialModuleCoeffEquiv P).filter (fun t => key t = i)))
      (k, d) = _
  rw [LinearEquiv.apply_symm_apply, Finsupp.filter_apply]
  rfl

/-- A fibre projection lands in the corresponding coefficient fibre. -/
theorem artinianPolynomialModuleFiberComponent_mem [DecidableEq ι]
    (key : PolynomialModuleTerm n r → ι) (i : ι)
    (P : artinianFreePolynomialModule B n r) :
    artinianPolynomialModuleFiberComponent key i P ∈
      artinianPolynomialModuleFiberPiece (B := B) key i := by
  classical
  apply (mem_artinianPolynomialModuleSupported _ _).mpr
  intro k d hcoeff
  change key (k, d) = i
  by_contra hkey
  exact hcoeff (by
    rw [artinianPolynomialModuleFiberComponent_coeff, ite_eq_right hkey])

/-- Projection fixes a vector already supported in its fibre. -/
theorem artinianPolynomialModuleFiberComponent_eq_self [DecidableEq ι]
    (key : PolynomialModuleTerm n r → ι) (i : ι)
    {P : artinianFreePolynomialModule B n r}
    (hP : P ∈ artinianPolynomialModuleFiberPiece (B := B) key i) :
    artinianPolynomialModuleFiberComponent key i P = P := by
  classical
  funext k
  apply MvPolynomial.ext
  intro d
  rw [artinianPolynomialModuleFiberComponent_coeff]
  by_cases hkey : key (k, d) = i
  · exact ite_eq_left hkey
  · rw [ite_eq_right hkey]
    by_contra hcoeff
    exact hkey ((mem_artinianPolynomialModuleSupported _ _).mp hP k d
      (Ne.symm hcoeff))

/-- Projection to one fibre kills a vector supported in another fibre. -/
theorem artinianPolynomialModuleFiberComponent_eq_zero_of_mem
    [DecidableEq ι]
    (key : PolynomialModuleTerm n r → ι) {i j : ι}
    (hij : i ≠ j) {P : artinianFreePolynomialModule B n r}
    (hP : P ∈ artinianPolynomialModuleFiberPiece (B := B) key j) :
    artinianPolynomialModuleFiberComponent key i P = 0 := by
  classical
  funext k
  apply MvPolynomial.ext
  intro d
  rw [artinianPolynomialModuleFiberComponent_coeff, Pi.zero_apply,
    MvPolynomial.coeff_zero]
  by_cases hkey : key (k, d) = i
  · rw [ite_eq_left hkey]
    by_contra hcoeff
    have hj := (mem_artinianPolynomialModuleSupported _ _).mp hP k d hcoeff
    exact hij (hkey.symm.trans hj)
  · exact ite_eq_right hkey

/-- If a fibre index is absent from the image of the coefficient support,
its projection is zero. -/
theorem artinianPolynomialModuleFiberComponent_eq_zero_of_notMem
    [DecidableEq ι]
    (key : PolynomialModuleTerm n r → ι) (i : ι)
    (P : artinianFreePolynomialModule B n r)
    (hi : i ∉ Finset.image key (artinianPolynomialModuleCoeffEquiv P).support) :
    artinianPolynomialModuleFiberComponent key i P = 0 := by
  classical
  funext k
  apply MvPolynomial.ext
  intro d
  rw [artinianPolynomialModuleFiberComponent_coeff, Pi.zero_apply,
    MvPolynomial.coeff_zero]
  by_cases hkey : key (k, d) = i
  · rw [ite_eq_left hkey]
    by_cases hzero : (P k).coeff d = 0
    · exact hzero
    · exfalso
      apply hi
      apply Finset.mem_image.mpr
      refine ⟨(k, d), ?_, hkey⟩
      rw [Finsupp.mem_support_iff]
      simpa only [artinianPolynomialModuleCoeffEquiv_apply] using hzero
  · exact ite_eq_right hkey

/-- Only finitely many coefficient-fibre projections of a fixed vector are
nonzero. -/
theorem artinianPolynomialModuleFiberComponent_finiteSupport
    [DecidableEq ι]
    (key : PolynomialModuleTerm n r → ι)
    (P : artinianFreePolynomialModule B n r) :
    (fun i => artinianPolynomialModuleFiberComponent key i P).HasFiniteSupport := by
  classical
  refine ((artinianPolynomialModuleCoeffEquiv P).support.finite_toSet.image key).subset ?_
  intro i hi
  by_contra himage
  apply hi
  apply artinianPolynomialModuleFiberComponent_eq_zero_of_notMem key i P
  intro hfinset
  apply himage
  rcases Finset.mem_image.mp hfinset with ⟨t, ht, hkey⟩
  exact ⟨t, by simpa using ht, hkey⟩

/-- A vector is the finite sum of all of its coefficient-fibre
projections. -/
theorem sum_artinianPolynomialModuleFiberComponent
    [DecidableEq ι]
    (key : PolynomialModuleTerm n r → ι)
    (P : artinianFreePolynomialModule B n r) :
    (finsum fun i => artinianPolynomialModuleFiberComponent key i P) = P := by
  classical
  rw [finsum_eq_sum_of_support_subset
    (fun i => artinianPolynomialModuleFiberComponent key i P)
    (s := Finset.image key
      (artinianPolynomialModuleCoeffEquiv P).support)
    (by
      intro i hi
      by_contra himage
      exact hi
        (artinianPolynomialModuleFiberComponent_eq_zero_of_notMem
          key i P himage))]
  funext k
  apply MvPolynomial.ext
  intro d
  simp only [Finset.sum_apply, MvPolynomial.coeff_sum,
    artinianPolynomialModuleFiberComponent_coeff]
  rw [Finset.sum_eq_single (key (k, d))]
  · rw [ite_eq_left rfl]
  · intro i _ hi
    rw [ite_eq_right hi.symm]
  · intro hi
    rw [ite_eq_left rfl]
    by_contra hcoeff
    apply hi
    apply Finset.mem_image.mpr
    refine ⟨(k, d), ?_, rfl⟩
    rw [Finsupp.mem_support_iff]
    simpa only [artinianPolynomialModuleCoeffEquiv_apply] using hcoeff

/-- The explicit finite-support direct-sum coordinate map associated to a
coefficient grading key. -/
def artinianPolynomialModuleFiberDecompose' [DecidableEq ι]
    (key : PolynomialModuleTerm n r → ι)
    (P : artinianFreePolynomialModule B n r) :
    DirectSum ι (fun i =>
      ↥(artinianPolynomialModuleFiberPiece (B := B) key i)) :=
  DirectSum.mk (fun i =>
      ↥(artinianPolynomialModuleFiberPiece (B := B) key i))
    (Finset.image key (artinianPolynomialModuleCoeffEquiv P).support)
    (fun i => ⟨artinianPolynomialModuleFiberComponent key i P,
      artinianPolynomialModuleFiberComponent_mem key i P⟩)

@[simp]
theorem artinianPolynomialModuleFiberDecompose'_apply [DecidableEq ι]
    (key : PolynomialModuleTerm n r → ι)
    (P : artinianFreePolynomialModule B n r) (i : ι) :
    (artinianPolynomialModuleFiberDecompose' key P i :
      artinianFreePolynomialModule B n r) =
      artinianPolynomialModuleFiberComponent key i P := by
  rw [artinianPolynomialModuleFiberDecompose']
  by_cases hi : i ∈ Finset.image key (artinianPolynomialModuleCoeffEquiv P).support
  · simp only [DirectSum.mk_apply_of_mem hi, Subtype.coe_mk]
  · rw [DirectSum.mk_apply_of_notMem hi, Submodule.coe_zero,
      artinianPolynomialModuleFiberComponent_eq_zero_of_notMem key i P hi]

/-- Fibre projection recovers a coordinate of an arbitrary direct sum of
fibre pieces. -/
theorem artinianPolynomialModuleFiberComponent_directSum [DecidableEq ι]
    (key : PolynomialModuleTerm n r → ι)
    (x : DirectSum ι (fun i =>
      ↥(artinianPolynomialModuleFiberPiece (B := B) key i)))
    (i : ι) :
    artinianPolynomialModuleFiberComponent key i
        (DirectSum.coeLinearMap
          (fun i => artinianPolynomialModuleFiberPiece (B := B) key i) x) =
      x i := by
  classical
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  convert! @Finset.sum_eq_single ι (artinianFreePolynomialModule B n r) _
    (DFinsupp.support x) _ i _ _
  · exact (artinianPolynomialModuleFiberComponent_eq_self
      key i (x i).prop).symm
  · intro j _ hji
    exact artinianPolynomialModuleFiberComponent_eq_zero_of_mem key hji.symm (x j).prop
  · rw [DFinsupp.notMem_support_iff]
    intro hi
    rw [hi, Submodule.coe_zero, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The actual coefficient-linear direct-sum decomposition associated to an
arbitrary grading key. -/
@[instance_reducible]
def artinianPolynomialModuleFiberDecomposition [DecidableEq ι]
    (key : PolynomialModuleTerm n r → ι) :
    DirectSum.Decomposition
      (fun i => artinianPolynomialModuleFiberPiece (B := B) key i) where
  decompose' := artinianPolynomialModuleFiberDecompose' key
  left_inv P := by
    classical
    conv_rhs => rw [← sum_artinianPolynomialModuleFiberComponent key P]
    rw [← DirectSum.sum_support_of
      (artinianPolynomialModuleFiberDecompose' key P)]
    simp only [DirectSum.coeAddMonoidHom_of, map_sum,
      finsum_eq_sum _
        (artinianPolynomialModuleFiberComponent_finiteSupport key P)]
    apply Finset.sum_congr _ (fun i _ => by
      rw [artinianPolynomialModuleFiberDecompose'_apply])
    ext i
    simp only [DFinsupp.mem_support_toFun, ne_eq, Set.Finite.mem_toFinset,
      Function.mem_support, not_iff_not]
    conv_lhs => rw [← Subtype.coe_inj]
    rw [artinianPolynomialModuleFiberDecompose'_apply, Submodule.coe_zero]
  right_inv x := by
    apply DFinsupp.ext
    intro i
    rw [← Subtype.coe_inj,
      artinianPolynomialModuleFiberDecompose'_apply]
    exact artinianPolynomialModuleFiberComponent_directSum key x i

end CoefficientFibres

/-! ## The concrete ordinary/lexicographic grading -/

/-- Lexicographically ordered integral multidegrees of height `h`. -/
abbrev PolynomialLexWeight (h : ℕ) := Lex (Fin h → ℤ)

/-- A joint shifted ordinary degree and lexicographic multidegree. -/
abbrev PolynomialGradedLexDegree (h : ℕ) := ℤ × PolynomialLexWeight h

/-- The combinatorial data of a grading on a finite shifted free polynomial
module.  Positivity is intentionally not stored: the direct-sum grading is
valid without it, while the finite-window API takes positivity exactly where
it is required. -/
structure PolynomialGradedLexData (n r h : ℕ) where
  ordinaryDegree : Fin n → ℕ
  multiDegree : Fin n → Fin h → ℤ
  ordinaryShift : Fin r → ℤ
  multiShift : Fin r → Fin h → ℤ

namespace PolynomialGradedLexData

variable {h : ℕ} (G : PolynomialGradedLexData n r h)

/-- Shifted ordinary degree of a coordinate monomial. -/
def termOrdinaryDegree (t : PolynomialModuleTerm n r) : ℤ :=
  artinianPolynomialTermDegree G.ordinaryDegree G.ordinaryShift t

/-- Shifted lexicographic multidegree of a coordinate monomial. -/
def termWeight (t : PolynomialModuleTerm n r) : PolynomialLexWeight h :=
  toLex (Finsupp.weight G.multiDegree t.2 + G.multiShift t.1)

/-- Joint ordinary and lexicographic degree of a coordinate monomial. -/
def termJointDegree (t : PolynomialModuleTerm n r) :
    PolynomialGradedLexDegree h :=
  (G.termOrdinaryDegree t, G.termWeight t)

@[simp]
theorem termJointDegree_fst (t : PolynomialModuleTerm n r) :
    (G.termJointDegree t).1 = G.termOrdinaryDegree t := rfl

@[simp]
theorem termJointDegree_snd (t : PolynomialModuleTerm n r) :
    (G.termJointDegree t).2 = G.termWeight t := rfl

/-- Adding one variable exponent adds its ordinary degree. -/
theorem termOrdinaryDegree_add_single (i : Fin n) (k : Fin r)
    (d : Fin n →₀ ℕ) :
    G.termOrdinaryDegree (k, Finsupp.single i 1 + d) =
      (G.ordinaryDegree i : ℤ) + G.termOrdinaryDegree (k, d) := by
  simp [termOrdinaryDegree, artinianPolynomialTermDegree, map_add,
    Finsupp.weight_single, add_assoc]

/-- Adding one variable exponent adds its lexicographic multidegree. -/
theorem termWeight_add_single (i : Fin n) (k : Fin r)
    (d : Fin n →₀ ℕ) :
    G.termWeight (k, Finsupp.single i 1 + d) =
      toLex (G.multiDegree i) + G.termWeight (k, d) := by
  simp [termWeight, map_add, Finsupp.weight_single, add_assoc]

/-- Terms of one joint degree. -/
abbrev jointTerms (degree : ℤ) (weight : PolynomialLexWeight h) :
    Set (PolynomialModuleTerm n r) :=
  artinianPolynomialModuleFiberTerms G.termJointDegree (degree, weight)

/-- One actual joint ordinary/lexicographic coefficient submodule. -/
abbrev jointPiece (B : Type*) [CommRing B]
    (degree : ℤ) (weight : PolynomialLexWeight h) :
    Submodule B (artinianFreePolynomialModule B n r) :=
  artinianPolynomialModuleFiberPiece G.termJointDegree (degree, weight)

/-- Projection to one joint ordinary/lexicographic degree. -/
abbrev jointComponent (B : Type*) [CommRing B]
    (degree : ℤ) (weight : PolynomialLexWeight h) :
    artinianFreePolynomialModule B n r →ₗ[B]
      artinianFreePolynomialModule B n r :=
  artinianPolynomialModuleFiberComponent G.termJointDegree (degree, weight)

@[simp]
theorem jointComponent_coeff
    (degree : ℤ) (weight : PolynomialLexWeight h)
    (P : artinianFreePolynomialModule B n r)
    (k : Fin r) (d : Fin n →₀ ℕ) :
    (G.jointComponent B degree weight P k).coeff d =
      if G.termJointDegree (k, d) = (degree, weight)
      then (P k).coeff d else 0 :=
  artinianPolynomialModuleFiberComponent_coeff
    G.termJointDegree (degree, weight) P k d

/-- Joint components are an actual coefficient-linear direct-sum
decomposition of the full shifted free module. -/
@[instance_reducible]
def jointDecomposition (B : Type*) [CommRing B] :
    DirectSum.Decomposition
      (fun q : PolynomialGradedLexDegree h => G.jointPiece B q.1 q.2) :=
  artinianPolynomialModuleFiberDecomposition G.termJointDegree

/-- The canonical coefficient-linear equivalence furnished by the joint
decomposition. -/
noncomputable def jointDecomposeLinearEquiv (B : Type*) [CommRing B] :
    artinianFreePolynomialModule B n r ≃ₗ[B]
      DirectSum (PolynomialGradedLexDegree h)
        (fun q => ↥(G.jointPiece B q.1 q.2)) := by
  letI := G.jointDecomposition B
  exact DirectSum.decomposeLinearEquiv
    (fun q : PolynomialGradedLexDegree h => G.jointPiece B q.1 q.2)

@[simp]
theorem jointDecomposeLinearEquiv_apply
    (P : artinianFreePolynomialModule B n r)
    (q : PolynomialGradedLexDegree h) :
    (G.jointDecomposeLinearEquiv B P q :
      artinianFreePolynomialModule B n r) =
      G.jointComponent B q.1 q.2 P := by
  letI := G.jointDecomposition B
  exact artinianPolynomialModuleFiberDecompose'_apply
    G.termJointDegree P q

/-- A joint piece lies in its ordinary-degree piece. -/
theorem jointPiece_le_ordinaryPiece
    (degree : ℤ) (weight : PolynomialLexWeight h) :
    G.jointPiece B degree weight ≤
      artinianPolynomialModulePiece (B := B)
        G.ordinaryDegree G.ordinaryShift degree := by
  intro P hP
  apply (mem_artinianPolynomialModuleSupported _ _).mpr
  intro k d hcoeff
  have hjoint := (mem_artinianPolynomialModuleSupported _ _).mp hP k d hcoeff
  change G.termJointDegree (k, d) = (degree, weight) at hjoint
  change G.termOrdinaryDegree (k, d) = degree
  exact congrArg Prod.fst hjoint

/-- Multiplication by `X i`, coordinatewise on the free module, is linear
over the coefficient ring. -/
def XLinear (B : Type*) [CommRing B] (i : Fin n) :
    artinianFreePolynomialModule B n r →ₗ[B]
      artinianFreePolynomialModule B n r where
  toFun P := fun k => MvPolynomial.X i * P k
  map_add' P Q := by
    funext k
    simp only [Pi.add_apply, mul_add]
  map_smul' c P := by
    funext k
    simp only [Pi.smul_apply, RingHom.id_apply,
      MvPolynomial.smul_eq_C_mul]
    ac_rfl

/-- Multiplication by a variable sends a joint piece to the joint piece
obtained by adding that variable's two degrees. -/
theorem X_smul_jointPiece_le (i : Fin n)
    (degree : ℤ) (weight : PolynomialLexWeight h) :
    (G.jointPiece B degree weight).map
        (XLinear (n := n) (r := r) B i) ≤
      G.jointPiece B
        ((G.ordinaryDegree i : ℤ) + degree)
        (toLex (G.multiDegree i) + weight) := by
  rintro _ ⟨P, hP, rfl⟩
  apply (mem_artinianPolynomialModuleSupported _ _).mpr
  intro k d hcoeff
  change (MvPolynomial.X i * P k).coeff d ≠ 0 at hcoeff
  have hd : d ∈ (MvPolynomial.X i * P k).support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  rw [MvPolynomial.support_X_mul] at hd
  rcases Finset.mem_map.mp hd with ⟨d₀, hd₀, rfl⟩
  have hPcoeff : (P k).coeff d₀ ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd₀
  have hjoint :=
    (mem_artinianPolynomialModuleSupported _ _).mp hP k d₀ hPcoeff
  change G.termJointDegree (k, d₀) = (degree, weight) at hjoint
  apply Prod.ext
  · rw [addLeftEmbedding_apply, termJointDegree_fst,
      G.termOrdinaryDegree_add_single]
    exact congrArg
      (fun q : ℤ => (G.ordinaryDegree i : ℤ) + q)
      (congrArg Prod.fst hjoint)
  · rw [addLeftEmbedding_apply, termJointDegree_snd,
      G.termWeight_add_single]
    exact congrArg
      (fun q : PolynomialLexWeight h => toLex (G.multiDegree i) + q)
      (congrArg Prod.snd hjoint)

/-! ## Finite weights in each ordinary degree -/

/-- The finite set of all coordinate monomials of one ordinary degree.
Positivity is precisely the hypothesis needed for this definition. -/
def ordinaryTermFinset (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (degree : ℤ) : Finset (PolynomialModuleTerm n r) :=
  (artinianPolynomialDegreeTerms_finite G.ordinaryDegree hpositive
    G.ordinaryShift degree).toFinset

@[simp]
theorem mem_ordinaryTermFinset (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (degree : ℤ) (t : PolynomialModuleTerm n r) :
    t ∈ G.ordinaryTermFinset hpositive degree ↔
      G.termOrdinaryDegree t = degree := by
  simp only [ordinaryTermFinset, Set.Finite.mem_toFinset,
    artinianPolynomialDegreeTerms, Set.mem_setOf_eq, termOrdinaryDegree]

/-- A finite, coefficient-ring-independent set containing every
multidegree that can occur in one ordinary slice. -/
def ordinaryWeightSupport (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (degree : ℤ) : Finset (PolynomialLexWeight h) :=
  (G.ordinaryTermFinset hpositive degree).image G.termWeight

theorem mem_ordinaryWeightSupport
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (degree : ℤ) (weight : PolynomialLexWeight h) :
    weight ∈ G.ordinaryWeightSupport hpositive degree ↔
      ∃ t : PolynomialModuleTerm n r,
        G.termOrdinaryDegree t = degree ∧ G.termWeight t = weight := by
  simp only [ordinaryWeightSupport, Finset.mem_image,
    G.mem_ordinaryTermFinset]

/-- In each ordinary slice, the existing ordinary coefficient projection is
the finite sum of the joint lexicographic projections. -/
theorem sum_jointComponent_eq_ordinaryComponent
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (degree : ℤ) (P : artinianFreePolynomialModule B n r) :
    (∑ weight ∈ G.ordinaryWeightSupport hpositive degree,
        G.jointComponent B degree weight P) =
      artinianPolynomialModuleComponent
        G.ordinaryDegree G.ordinaryShift degree P := by
  classical
  funext k
  apply MvPolynomial.ext
  intro d
  simp only [Finset.sum_apply, MvPolynomial.coeff_sum,
    G.jointComponent_coeff,
    artinianPolynomialModuleComponent_coeff]
  by_cases hdegree : G.termOrdinaryDegree (k, d) = degree
  · have hweight : G.termWeight (k, d) ∈
        G.ordinaryWeightSupport hpositive degree :=
      (G.mem_ordinaryWeightSupport hpositive degree
        (G.termWeight (k, d))).mpr ⟨(k, d), hdegree, rfl⟩
    have hjoint : G.termJointDegree (k, d) =
        (degree, G.termWeight (k, d)) := by
      apply Prod.ext
      · exact hdegree
      · rfl
    have hordinary :
        artinianPolynomialTermDegree G.ordinaryDegree
          G.ordinaryShift (k, d) = degree := by
      simpa only [termOrdinaryDegree] using hdegree
    rw [Finset.sum_eq_single (G.termWeight (k, d))]
    · rw [ite_eq_left hjoint, ite_eq_left hordinary]
    · intro weight _ hne
      rw [ite_eq_right]
      intro hjoint
      apply hne
      exact (congrArg Prod.snd hjoint).symm
    · exact fun hnot => (hnot hweight).elim
  · have hordinary : ¬
        artinianPolynomialTermDegree G.ordinaryDegree
          G.ordinaryShift (k, d) = degree := by
      simpa only [termOrdinaryDegree] using hdegree
    rw [ite_eq_right hordinary]
    apply Finset.sum_eq_zero
    intro weight _
    rw [ite_eq_right]
    intro hjoint
    exact hdegree (congrArg Prod.fst hjoint)

/-- A nonzero joint piece must occur in the finite combinatorial support of
its ordinary slice.  This direction is valid even for the zero ring. -/
theorem jointPiece_ne_bot_imp_mem_ordinaryWeightSupport
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (degree : ℤ) (weight : PolynomialLexWeight h)
    (hpiece : G.jointPiece B degree weight ≠ ⊥) :
    weight ∈ G.ordinaryWeightSupport hpositive degree := by
  obtain ⟨P, hP, hP0⟩ := (Submodule.ne_bot_iff _).mp hpiece
  by_contra hweight
  apply hP0
  funext k
  apply MvPolynomial.ext
  intro d
  by_contra hcoeff
  have hjoint :=
    (mem_artinianPolynomialModuleSupported _ _).mp hP k d hcoeff
  change G.termJointDegree (k, d) = (degree, weight) at hjoint
  apply hweight
  apply (G.mem_ordinaryWeightSupport hpositive degree weight).mpr
  refine ⟨(k, d), ?_, ?_⟩
  · exact congrArg Prod.fst hjoint
  · exact congrArg Prod.snd hjoint

/-- Over a nonzero coefficient ring, every combinatorially possible weight
gives a nonzero joint piece.  The `Nontrivial` assumption is necessary for
this converse. -/
theorem mem_ordinaryWeightSupport_imp_jointPiece_ne_bot [Nontrivial B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (degree : ℤ) (weight : PolynomialLexWeight h)
    (hweight : weight ∈ G.ordinaryWeightSupport hpositive degree) :
    G.jointPiece B degree weight ≠ ⊥ := by
  obtain ⟨t, htdegree, htweight⟩ :=
    (G.mem_ordinaryWeightSupport hpositive degree weight).mp hweight
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨artinianPolynomialModuleTermVector (B := B) t, ?_,
    artinianPolynomialModuleTermVector_ne_zero (B := B) t⟩
  apply artinianPolynomialModuleTermVector_mem_fiber G.termJointDegree
    t (degree, weight)
  exact Prod.ext htdegree htweight

theorem jointPiece_ne_bot_iff_mem_ordinaryWeightSupport [Nontrivial B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (degree : ℤ) (weight : PolynomialLexWeight h) :
    G.jointPiece B degree weight ≠ ⊥ ↔
      weight ∈ G.ordinaryWeightSupport hpositive degree :=
  ⟨G.jointPiece_ne_bot_imp_mem_ordinaryWeightSupport
      hpositive degree weight,
    G.mem_ordinaryWeightSupport_imp_jointPiece_ne_bot
      hpositive degree weight⟩

/-- The set of nonzero joint weight spaces in a fixed ordinary degree is
finite over every commutative coefficient ring. -/
theorem finite_jointPiece_weights
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (degree : ℤ) :
    {weight : PolynomialLexWeight h |
      G.jointPiece B degree weight ≠ ⊥}.Finite :=
  (G.ordinaryWeightSupport hpositive degree).finite_toSet.subset
    (fun weight hweight =>
      G.jointPiece_ne_bot_imp_mem_ordinaryWeightSupport
        hpositive degree weight hweight)

/-! ## A uniform lower bound and finite degree/weight windows -/

/-- A choice-free lower bound for all shifts.  The absolute-value sum also
works when the free rank is zero. -/
def ordinaryLowerBound : ℤ :=
  -∑ k : Fin r, |G.ordinaryShift k|

theorem ordinaryLowerBound_le_shift (k : Fin r) :
    G.ordinaryLowerBound ≤ G.ordinaryShift k := by
  have habs : |G.ordinaryShift k| ≤ ∑ j : Fin r, |G.ordinaryShift j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (G.ordinaryShift j))
      (Finset.mem_univ k)
  exact (neg_le_neg habs).trans (neg_abs_le (G.ordinaryShift k))

theorem ordinaryLowerBound_le_term (t : PolynomialModuleTerm n r) :
    G.ordinaryLowerBound ≤ G.termOrdinaryDegree t := by
  change G.ordinaryLowerBound ≤
    (Finsupp.weight G.ordinaryDegree t.2 : ℤ) + G.ordinaryShift t.1
  exact (G.ordinaryLowerBound_le_shift t.1).trans
    (le_add_of_nonneg_left
      (Int.natCast_nonneg (Finsupp.weight G.ordinaryDegree t.2)))

/-- The finite interval containing every ordinary degree at most `D` that
can occur in the shifted free module. -/
def degreeWindow (D : ℤ) : Finset ℤ :=
  Finset.Icc G.ordinaryLowerBound D

@[simp]
theorem mem_degreeWindow (D degree : ℤ) :
    degree ∈ G.degreeWindow D ↔
      G.ordinaryLowerBound ≤ degree ∧ degree ≤ D := by
  simp [degreeWindow]

/-- All coordinate monomials whose ordinary degree lies in the bounded
degree window. -/
def windowTermFinset (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) : Finset (PolynomialModuleTerm n r) :=
  (G.degreeWindow D).biUnion (G.ordinaryTermFinset hpositive)

theorem mem_windowTermFinset_iff_mem_degreeWindow
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) (t : PolynomialModuleTerm n r) :
    t ∈ G.windowTermFinset hpositive D ↔
      G.termOrdinaryDegree t ∈ G.degreeWindow D := by
  simp only [windowTermFinset, Finset.mem_biUnion,
    G.mem_ordinaryTermFinset]
  constructor
  · rintro ⟨degree, hdegree, ht⟩
    simpa [ht] using hdegree
  · intro ht
    exact ⟨G.termOrdinaryDegree t, ht, rfl⟩

/-- Because `ordinaryLowerBound` bounds every term, membership in the
window is equivalent simply to having ordinary degree at most `D`. -/
theorem mem_windowTermFinset_iff_le
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) (t : PolynomialModuleTerm n r) :
    t ∈ G.windowTermFinset hpositive D ↔
      G.termOrdinaryDegree t ≤ D := by
  rw [G.mem_windowTermFinset_iff_mem_degreeWindow,
    G.mem_degreeWindow]
  exact and_iff_right (G.ordinaryLowerBound_le_term t)

/-- The finite lexicographic weight window obtained after grouping all
ordinary degrees at most `D` by their multidegree. -/
def weightWindow (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) : Finset (PolynomialLexWeight h) :=
  (G.windowTermFinset hpositive D).image G.termWeight

theorem mem_weightWindow
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) (weight : PolynomialLexWeight h) :
    weight ∈ G.weightWindow hpositive D ↔
      ∃ t : PolynomialModuleTerm n r,
        G.termOrdinaryDegree t ≤ D ∧ G.termWeight t = weight := by
  simp only [weightWindow, Finset.mem_image,
    G.mem_windowTermFinset_iff_le]

/-- The window is exactly the union of the finite weight supports of the
ordinary degrees in its degree interval. -/
theorem weightWindow_eq_biUnion_ordinaryWeightSupport
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ) :
    G.weightWindow hpositive D =
      (G.degreeWindow D).biUnion
        (G.ordinaryWeightSupport hpositive) := by
  ext weight
  simp only [G.mem_weightWindow, Finset.mem_biUnion,
    G.mem_ordinaryWeightSupport]
  constructor
  · rintro ⟨t, htD, htweight⟩
    refine ⟨G.termOrdinaryDegree t, ?_, t, rfl, htweight⟩
    exact (G.mem_degreeWindow D (G.termOrdinaryDegree t)).mpr
      ⟨G.ordinaryLowerBound_le_term t, htD⟩
  · rintro ⟨degree, hdegree, t, htdegree, htweight⟩
    refine ⟨t, ?_, htweight⟩
    rw [htdegree]
    exact ((G.mem_degreeWindow D degree).mp hdegree).2

/-- The number of grouped lexicographic weights in the bounded window. -/
abbrev weightCount (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) : ℕ :=
  (G.weightWindow hpositive D).card

/-- The increasing enumeration of the finite weight window. -/
def weightOrderIso (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) :
    Fin (G.weightCount hpositive D) ≃o
      {weight // weight ∈ G.weightWindow hpositive D} :=
  (G.weightWindow hpositive D).orderIsoOfFin rfl

/-- The weight in position `i` of the increasing enumeration. -/
def weightAt (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) (i : Fin (G.weightCount hpositive D)) :
    PolynomialLexWeight h :=
  (G.weightOrderIso hpositive D i).1

@[simp]
theorem weightAt_mem (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) (i : Fin (G.weightCount hpositive D)) :
    G.weightAt hpositive D i ∈ G.weightWindow hpositive D :=
  (G.weightOrderIso hpositive D i).2

/-- The finite enumeration preserves and reflects strict lexicographic
order. -/
theorem weightAt_lt_iff (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) (i j : Fin (G.weightCount hpositive D)) :
    G.weightAt hpositive D i < G.weightAt hpositive D j ↔ i < j := by
  change G.weightOrderIso hpositive D i <
      G.weightOrderIso hpositive D j ↔ i < j
  exact (G.weightOrderIso hpositive D).lt_iff_lt

theorem exists_weightAt_eq
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) {weight : PolynomialLexWeight h}
    (hweight : weight ∈ G.weightWindow hpositive D) :
    ∃ i : Fin (G.weightCount hpositive D),
      G.weightAt hpositive D i = weight := by
  obtain ⟨i, hi⟩ :=
    (G.weightOrderIso hpositive D).surjective ⟨weight, hweight⟩
  exact ⟨i, congrArg Subtype.val hi⟩

/-! ## The window module and its grouped weight product -/

/-- The coefficient term set in the bounded ordinary-degree window. -/
def windowTermSet (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) : Set (PolynomialModuleTerm n r) :=
  ↑(G.windowTermFinset hpositive D)

/-- The finite submodule supported in ordinary degrees at most `D`. -/
def windowModule (B : Type*) [CommRing B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ) :
    Submodule B (artinianFreePolynomialModule B n r) :=
  artinianPolynomialModuleSupported (G.windowTermSet hpositive D)

/-- The terms of a fixed lexicographic weight in the whole ordinary-degree
window.  All ordinary degrees with this weight are grouped together. -/
def windowWeightTerms (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) (weight : PolynomialLexWeight h) :
    Set (PolynomialModuleTerm n r) :=
  {t | t ∈ G.windowTermSet hpositive D ∧ G.termWeight t = weight}

/-- The aggregate of all joint pieces in the window with a fixed
lexicographic weight. -/
def windowWeightPiece (B : Type*) [CommRing B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) (weight : PolynomialLexWeight h) :
    Submodule B (artinianFreePolynomialModule B n r) :=
  artinianPolynomialModuleSupported
    (G.windowWeightTerms hpositive D weight)

/-- The grouped weight-term set is the union, over the finite degree
window, of the corresponding joint term sets. -/
theorem windowWeightTerms_eq_iUnion_jointTerms
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) (weight : PolynomialLexWeight h) :
    G.windowWeightTerms hpositive D weight =
      ⋃ degree : {degree // degree ∈ G.degreeWindow D},
        G.jointTerms degree.1 weight := by
  ext t
  simp only [windowWeightTerms, windowTermSet, Set.mem_setOf_eq,
    Set.mem_iUnion, jointTerms, artinianPolynomialModuleFiberTerms]
  constructor
  · rintro ⟨ht, htweight⟩
    have hdegree :=
      (G.mem_windowTermFinset_iff_mem_degreeWindow hpositive D t).mp ht
    refine ⟨⟨G.termOrdinaryDegree t, hdegree⟩, ?_⟩
    exact Prod.ext rfl htweight
  · rintro ⟨degree, ht⟩
    refine ⟨?_, congrArg Prod.snd ht⟩
    apply (G.mem_windowTermFinset_iff_mem_degreeWindow hpositive D t).mpr
    have htdegree : G.termOrdinaryDegree t = degree.1 :=
      congrArg Prod.fst ht
    rw [htdegree]
    exact degree.2

theorem windowWeightPiece_le_windowModule
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) (weight : PolynomialLexWeight h) :
    G.windowWeightPiece B hpositive D weight ≤
      G.windowModule B hpositive D := by
  intro P hP
  apply (mem_artinianPolynomialModuleSupported _ _).mpr
  intro k d hcoeff
  exact ((mem_artinianPolynomialModuleSupported _ _).mp hP k d hcoeff).1

/-- The whole ordinary-degree window is a finite coefficient module. -/
theorem windowModule_moduleFinite
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ) :
    Module.Finite B (G.windowModule B hpositive D) := by
  let _ : Fintype (G.windowTermSet hpositive D) :=
    (G.windowTermFinset hpositive D).finite_toSet.fintype
  exact Module.Finite.equiv
    (artinianPolynomialModuleSupportedEquiv
      (B := B) (G.windowTermSet hpositive D)).symm

/-- Every aggregate weight piece in the window is a finite coefficient
module. -/
theorem windowWeightPiece_moduleFinite
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) (weight : PolynomialLexWeight h) :
    Module.Finite B (G.windowWeightPiece B hpositive D weight) := by
  have hfinite : (G.windowWeightTerms hpositive D weight).Finite :=
    (G.windowTermFinset hpositive D).finite_toSet.subset (fun _ ht => ht.1)
  let _ : Fintype (G.windowWeightTerms hpositive D weight) := hfinite.fintype
  exact Module.Finite.equiv
    (artinianPolynomialModuleSupportedEquiv
      (B := B) (G.windowWeightTerms hpositive D weight)).symm

/-- Terms in the finite ordinary-degree window, as a finite type. -/
abbrev WindowTerm (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) :=
  {t // t ∈ G.windowTermSet hpositive D}

/-- Weights in the finite weight window, as a finite linearly ordered type. -/
abbrev WindowWeight (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) :=
  {weight // weight ∈ G.weightWindow hpositive D}

/-- The weight map from window terms to the finite weight window. -/
def windowTermWeight (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) :
    G.WindowTerm hpositive D → G.WindowWeight hpositive D :=
  fun t => ⟨G.termWeight t.1, by
    apply (G.mem_weightWindow hpositive D (G.termWeight t.1)).mpr
    exact ⟨t.1,
      (G.mem_windowTermFinset_iff_le hpositive D t.1).mp t.2, rfl⟩⟩

/-- A fibre of `windowTermWeight` is canonically the term subtype defining
the corresponding grouped weight piece. -/
def windowWeightFiberEquiv
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    (D : ℤ) (weight : G.WindowWeight hpositive D) :
    {t : G.WindowTerm hpositive D |
        G.windowTermWeight hpositive D t = weight} ≃
      G.windowWeightTerms hpositive D weight.1 where
  toFun t := ⟨t.1.1, t.1.2, congrArg Subtype.val t.2⟩
  invFun t :=
    ⟨⟨t.1, t.2.1⟩, Subtype.ext t.2.2⟩
  left_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv t := by
    apply Subtype.ext
    rfl

/-- Canonical coefficient-linear splitting of the bounded window into the
product of its grouped lexicographic weight pieces. -/
def windowWeightProductEquiv
    (B : Type*) [CommRing B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ) :
    G.windowModule B hpositive D ≃ₗ[B]
      ((weight : G.WindowWeight hpositive D) →
        G.windowWeightPiece B hpositive D weight.1) :=
  (artinianPolynomialModuleSupportedEquiv
      (B := B) (G.windowTermSet hpositive D)).trans
    ((Finsupp.domLCongr
        (Equiv.sigmaFiberEquiv
          (G.windowTermWeight hpositive D)).symm).trans
      ((Finsupp.sigmaFinsuppLEquivPiFinsupp B).trans
        (LinearEquiv.piCongrRight (fun weight =>
          (Finsupp.domLCongr
            (G.windowWeightFiberEquiv hpositive D weight)).trans
          (artinianPolynomialModuleSupportedEquiv
            (B := B)
            (G.windowWeightTerms hpositive D weight.1)).symm))))

/-- The actual component family indexed by `Fin weightCount`, in increasing
lexicographic order. -/
abbrev orderedWeightPiece
    (B : Type*) [CommRing B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (i : Fin (G.weightCount hpositive D)) :=
  G.windowWeightPiece B hpositive D (G.weightAt hpositive D i)

/-- The canonical equivalence from the bounded ordinary-degree window to
the literal finite product required by the finite-weight stabilization
theorem. -/
def windowOrderedWeightProductEquiv
    (B : Type*) [CommRing B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ) :
    G.windowModule B hpositive D ≃ₗ[B]
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :=
  (G.windowWeightProductEquiv B hpositive D).trans
    (LinearEquiv.piCongrLeft B
      (fun weight : G.WindowWeight hpositive D =>
        G.windowWeightPiece B hpositive D weight.1)
      (G.weightOrderIso hpositive D).toEquiv).symm

/-- Every coordinate in the ordered finite product is a finite coefficient
module. -/
theorem orderedWeightPiece_moduleFinite
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (i : Fin (G.weightCount hpositive D)) :
    Module.Finite B (G.orderedWeightPiece B hpositive D i) :=
  G.windowWeightPiece_moduleFinite hpositive D
    (G.weightAt hpositive D i)

/-- The ordered product itself is a finite coefficient module. -/
theorem windowOrderedWeightProduct_moduleFinite
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ) :
    Module.Finite B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) := by
  letI (i : Fin (G.weightCount hpositive D)) :
      Module.Finite B (G.orderedWeightPiece B hpositive D i) :=
    G.orderedWeightPiece_moduleFinite hpositive D i
  infer_instance

/-- Direct specialization of the verified finite-weight stabilization
theorem to the ordered grouped pieces of this polynomial window.  Later
modules only have to construct the transported triangular equivalence and
the transported homogeneous submodule. -/
theorem exists_windowOrderedWeightDescent_stabilizes
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    [IsArtinian B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i)]
    [IsNoetherian B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i)]
    (J :
      ((i : Fin (G.weightCount hpositive D)) →
          G.orderedWeightPiece B hpositive D i) ≃ₗ[B]
        ((i : Fin (G.weightCount hpositive D)) →
          G.orderedWeightPiece B hpositive D i))
    (htri : ∀ i (v : G.orderedWeightPiece B hpositive D i),
      J (Pi.single i v) = Pi.single i v +
        finiteWeightPrefixProjection B
          (n := G.weightCount hpositive D)
          (fun i : Fin (G.weightCount hpositive D) =>
            G.orderedWeightPiece B hpositive D i) i.val
          (J (Pi.single i v)))
    (N₀ : Submodule B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀) :
    ∃ j₀ : ℕ,
      (finiteWeightDescentIterate J N₀ j₀).map J.toLinearMap =
          finiteWeightDescentIterate J N₀ j₀ ∧
        ∀ j, j₀ ≤ j →
          finiteWeightDescentIterate J N₀ j =
            finiteWeightDescentIterate J N₀ j₀ :=
  exists_finiteWeightDescent_stabilizes J htri N₀ hN₀

/-- Over an Artinian coefficient ring, finiteness of the concrete weight
pieces supplies all finite-length hypotheses needed by the stabilization
theorem. -/
theorem exists_windowOrderedWeightDescent_stabilizes_of_isArtinianRing
    [IsArtinianRing B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J :
      ((i : Fin (G.weightCount hpositive D)) →
          G.orderedWeightPiece B hpositive D i) ≃ₗ[B]
        ((i : Fin (G.weightCount hpositive D)) →
          G.orderedWeightPiece B hpositive D i))
    (htri : ∀ i (v : G.orderedWeightPiece B hpositive D i),
      J (Pi.single i v) = Pi.single i v +
        finiteWeightPrefixProjection B
          (n := G.weightCount hpositive D)
          (fun i : Fin (G.weightCount hpositive D) =>
            G.orderedWeightPiece B hpositive D i) i.val
          (J (Pi.single i v)))
    (N₀ : Submodule B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i))
    (hN₀ : ∀ x ∈ N₀, ∀ i, Pi.single i (x i) ∈ N₀) :
    ∃ j₀ : ℕ,
      (finiteWeightDescentIterate J N₀ j₀).map J.toLinearMap =
          finiteWeightDescentIterate J N₀ j₀ ∧
        ∀ j, j₀ ≤ j →
          finiteWeightDescentIterate J N₀ j =
            finiteWeightDescentIterate J N₀ j₀ := by
  letI : Module.Finite B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :=
    G.windowOrderedWeightProduct_moduleFinite hpositive D
  letI : IsArtinian B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) := inferInstance
  letI : IsNoetherian B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :=
    isNoetherian_of_finite_isArtinian
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i)
  exact G.exists_windowOrderedWeightDescent_stabilizes
    hpositive D J htri N₀ hN₀

end PolynomialGradedLexData

end AbelFormalization
