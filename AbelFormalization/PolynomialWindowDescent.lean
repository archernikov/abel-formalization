import AbelFormalization.ArtinianBoundedGeneratorLifting
import AbelFormalization.PolynomialGradedLexData

set_option autoImplicit false

/-!
# Explicit polynomial-window coordinates

This file gives the bounded ordinary-degree window a coordinate equivalence
whose components are literally the grouped lexicographic weight projections.
That explicit formula is the bridge between polynomial weighted initial
formation and the finite-product stabilization theorem.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n r h : ℕ}
variable (G : PolynomialGradedLexData n r h)

/-- Projection of a bounded polynomial window to one grouped weight piece. -/
def PolynomialGradedLexData.windowWeightComponent
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (weight : PolynomialLexWeight h) :
    G.windowModule B hpositive D →ₗ[B]
      G.windowWeightPiece B hpositive D weight :=
  LinearMap.codRestrict _
    ((artinianPolynomialModuleFiberComponent G.termWeight weight).domRestrict
      (G.windowModule B hpositive D)) (by
        intro P
        apply (mem_artinianPolynomialModuleSupported _ _).mpr
        intro k d hcoeff
        change ((artinianPolynomialModuleFiberComponent G.termWeight weight
          (P : artinianFreePolynomialModule B n r)) k).coeff d ≠ 0 at hcoeff
        rw [artinianPolynomialModuleFiberComponent_coeff] at hcoeff
        by_cases hweight : G.termWeight (k, d) = weight
        · refine ⟨?_, hweight⟩
          exact (mem_artinianPolynomialModuleSupported _ _).mp P.2 k d
            (by simpa [hweight] using hcoeff)
        · exact (hcoeff (by simp [hweight])).elim)

@[simp]
theorem PolynomialGradedLexData.windowWeightComponent_coe
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (weight : PolynomialLexWeight h)
    (P : G.windowModule B hpositive D) :
    (G.windowWeightComponent hpositive D weight P :
      artinianFreePolynomialModule B n r) =
      artinianPolynomialModuleFiberComponent G.termWeight weight P := rfl

/-- The explicit ordered coordinate map of the bounded window. -/
def PolynomialGradedLexData.windowOrderedWeightDecompose
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ) :
    G.windowModule B hpositive D →ₗ[B]
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :=
  LinearMap.pi (fun i =>
    G.windowWeightComponent hpositive D (G.weightAt hpositive D i))

@[simp]
theorem PolynomialGradedLexData.windowOrderedWeightDecompose_apply
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (P : G.windowModule B hpositive D)
    (i : Fin (G.weightCount hpositive D)) :
    G.windowOrderedWeightDecompose hpositive D P i =
      G.windowWeightComponent hpositive D (G.weightAt hpositive D i) P := rfl

/-- Sum the ordered grouped weight coordinates back into the bounded
polynomial window. -/
def PolynomialGradedLexData.windowOrderedWeightCompose
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ) :
    ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) →ₗ[B]
      G.windowModule B hpositive D where
  toFun x := ⟨∑ i, (x i : artinianFreePolynomialModule B n r), by
    apply Submodule.sum_mem
    intro i hi
    exact G.windowWeightPiece_le_windowModule hpositive D
      (G.weightAt hpositive D i) (x i).2⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Pi.add_apply]
    exact Finset.sum_add_distrib
  map_smul' c x := by
    apply Subtype.ext
    simp only [RingHom.id_apply, Pi.smul_apply]
    exact Finset.smul_sum.symm

@[simp]
theorem PolynomialGradedLexData.windowOrderedWeightCompose_coe
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (x : (i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :
    (G.windowOrderedWeightCompose hpositive D x :
      artinianFreePolynomialModule B n r) =
      ∑ i, (x i : artinianFreePolynomialModule B n r) := rfl

private theorem PolynomialGradedLexData.weightAt_injective
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ) :
    Function.Injective (G.weightAt hpositive D) := by
  intro i j hij
  apply (G.weightOrderIso hpositive D).injective
  exact Subtype.ext hij

theorem PolynomialGradedLexData.windowWeightPiece_le_fiberPiece
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (weight : PolynomialLexWeight h) :
    G.windowWeightPiece B hpositive D weight ≤
      artinianPolynomialModuleFiberPiece (B := B) G.termWeight weight := by
  intro P hP
  apply (mem_artinianPolynomialModuleSupported _ _).mpr
  intro k d hcoeff
  exact ((mem_artinianPolynomialModuleSupported _ _).mp hP k d hcoeff).2

/-- Every shifted ordinary-degree piece at degree at most `D` lies in the
bounded window. -/
theorem PolynomialGradedLexData.ordinaryPiece_le_windowModule
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D degree : ℤ)
    (hdegree : degree ≤ D) :
    artinianPolynomialModulePiece (B := B)
        G.ordinaryDegree G.ordinaryShift degree ≤
      G.windowModule B hpositive D := by
  intro P hP
  apply (mem_artinianPolynomialModuleSupported _ _).mpr
  intro k d hcoeff
  apply (G.mem_windowTermFinset_iff_le hpositive D (k, d)).mpr
  have hterm := (mem_artinianPolynomialModuleSupported _ _).mp hP k d hcoeff
  change G.termOrdinaryDegree (k, d) = degree at hterm
  rw [hterm]
  exact hdegree

/-- Terms in the bounded window whose lexicographic weight is strictly
less than `weight`. -/
def PolynomialGradedLexData.windowStrictLowerPiece
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (weight : PolynomialLexWeight h) :
    Submodule B (artinianFreePolynomialModule B n r) :=
  artinianPolynomialModuleSupported
    {t | t ∈ G.windowTermSet hpositive D ∧ G.termWeight t < weight}

theorem PolynomialGradedLexData.windowStrictLowerPiece_le_windowModule
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (weight : PolynomialLexWeight h) :
    G.windowStrictLowerPiece (B := B) hpositive D weight ≤
      G.windowModule B hpositive D := by
  intro P hP
  apply (mem_artinianPolynomialModuleSupported _ _).mpr
  intro k d hcoeff
  exact ((mem_artinianPolynomialModuleSupported _ _).mp hP k d hcoeff).1

theorem PolynomialGradedLexData.windowOrderedWeightCompose_decompose
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (P : G.windowModule B hpositive D) :
    G.windowOrderedWeightCompose hpositive D
        (G.windowOrderedWeightDecompose hpositive D P) = P := by
  classical
  apply Subtype.ext
  funext k
  apply MvPolynomial.ext
  intro d
  rw [G.windowOrderedWeightCompose_coe]
  simp only [Finset.sum_apply, MvPolynomial.coeff_sum,
    G.windowOrderedWeightDecompose_apply,
    G.windowWeightComponent_coe,
    artinianPolynomialModuleFiberComponent_coeff]
  by_cases hcoeff : ((P : artinianFreePolynomialModule B n r) k).coeff d = 0
  · simp [hcoeff]
  · have hterm : (k, d) ∈ G.windowTermSet hpositive D :=
      (mem_artinianPolynomialModuleSupported _ _).mp P.2 k d hcoeff
    have hweight : G.termWeight (k, d) ∈ G.weightWindow hpositive D := by
      apply (G.mem_weightWindow hpositive D (G.termWeight (k, d))).mpr
      exact ⟨(k, d),
        (G.mem_windowTermFinset_iff_le hpositive D (k, d)).mp hterm, rfl⟩
    let i₀ : Fin (G.weightCount hpositive D) :=
      (G.weightOrderIso hpositive D).symm ⟨G.termWeight (k, d), hweight⟩
    have hi₀ : G.weightAt hpositive D i₀ = G.termWeight (k, d) := by
      exact congrArg Subtype.val
        ((G.weightOrderIso hpositive D).apply_symm_apply
          ⟨G.termWeight (k, d), hweight⟩)
    rw [Finset.sum_eq_single i₀]
    · simp [hi₀]
    · intro j hj hji
      rw [ite_eq_right]
      intro hjweight
      apply hji
      apply G.weightAt_injective hpositive D
      exact hjweight.symm.trans hi₀.symm
    · intro hi₀
      exact (hi₀ (Finset.mem_univ i₀)).elim

theorem PolynomialGradedLexData.windowOrderedWeightDecompose_compose
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (x : (i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :
    G.windowOrderedWeightDecompose hpositive D
        (G.windowOrderedWeightCompose hpositive D x) = x := by
  classical
  funext i
  apply Subtype.ext
  change artinianPolynomialModuleFiberComponent G.termWeight
    (G.weightAt hpositive D i)
      (∑ j, (x j : artinianFreePolynomialModule B n r)) =
        (x i : artinianFreePolynomialModule B n r)
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · exact artinianPolynomialModuleFiberComponent_eq_self G.termWeight
      (G.weightAt hpositive D i)
      (G.windowWeightPiece_le_fiberPiece hpositive D
        (G.weightAt hpositive D i) (x i).2)
  · intro j hj hji
    apply artinianPolynomialModuleFiberComponent_eq_zero_of_mem
      G.termWeight
    · intro hweight
      apply hji
      exact G.weightAt_injective hpositive D hweight.symm
    · exact G.windowWeightPiece_le_fiberPiece hpositive D
        (G.weightAt hpositive D j) (x j).2
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- The bounded polynomial window as the literal ordered product of its
grouped lexicographic weight pieces. -/
def PolynomialGradedLexData.windowOrderedWeightLinearEquiv
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ) :
    G.windowModule B hpositive D ≃ₗ[B]
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) where
  toLinearMap := G.windowOrderedWeightDecompose hpositive D
  invFun := G.windowOrderedWeightCompose hpositive D
  left_inv := G.windowOrderedWeightCompose_decompose hpositive D
  right_inv := G.windowOrderedWeightDecompose_compose hpositive D

@[simp]
theorem PolynomialGradedLexData.windowOrderedWeightLinearEquiv_apply
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (P : G.windowModule B hpositive D) :
    G.windowOrderedWeightLinearEquiv hpositive D P =
      G.windowOrderedWeightDecompose hpositive D P := rfl

@[simp]
theorem PolynomialGradedLexData.windowOrderedWeightLinearEquiv_symm_apply
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (x : (i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :
    (G.windowOrderedWeightLinearEquiv hpositive D).symm x =
      G.windowOrderedWeightCompose hpositive D x := rfl

@[simp]
theorem PolynomialGradedLexData.windowOrderedWeightLinearEquiv_symm_single_coe
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (i : Fin (G.weightCount hpositive D))
    (v : G.orderedWeightPiece B hpositive D i) :
    ((G.windowOrderedWeightLinearEquiv hpositive D).symm
        (Pi.single i v) : artinianFreePolynomialModule B n r) = v := by
  classical
  let q : G.windowModule B hpositive D :=
    ⟨(v : artinianFreePolynomialModule B n r),
      G.windowWeightPiece_le_windowModule hpositive D
        (G.weightAt hpositive D i) v.2⟩
  have hq : G.windowOrderedWeightLinearEquiv hpositive D q =
      Pi.single i v := by
    funext j
    apply Subtype.ext
    by_cases hji : j = i
    · subst j
      rw [Pi.single_eq_same]
      change artinianPolynomialModuleFiberComponent G.termWeight
        (G.weightAt hpositive D i) (v : artinianFreePolynomialModule B n r) = v
      exact artinianPolynomialModuleFiberComponent_eq_self G.termWeight
        (G.weightAt hpositive D i)
        (G.windowWeightPiece_le_fiberPiece hpositive D
          (G.weightAt hpositive D i) v.2)
    · rw [Pi.single_eq_of_ne hji]
      change artinianPolynomialModuleFiberComponent G.termWeight
        (G.weightAt hpositive D j) (v : artinianFreePolynomialModule B n r) = 0
      apply artinianPolynomialModuleFiberComponent_eq_zero_of_mem
        G.termWeight
      · intro hweight
        apply hji
        exact G.weightAt_injective hpositive D hweight
      · exact G.windowWeightPiece_le_fiberPiece hpositive D
          (G.weightAt hpositive D i) v.2
  have heq : (G.windowOrderedWeightLinearEquiv hpositive D).symm
      (Pi.single i v) = q := by
    apply (G.windowOrderedWeightLinearEquiv hpositive D).injective
    rw [(G.windowOrderedWeightLinearEquiv hpositive D).apply_symm_apply, hq]
  exact congrArg Subtype.val heq

/-- A strictly lower polynomial weight vector becomes exactly a coordinate
prefix under the explicit ordered-window equivalence. -/
theorem PolynomialGradedLexData.windowOrderedWeightLinearEquiv_eq_prefix_of_mem_lower
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (i : Fin (G.weightCount hpositive D))
    {P : artinianFreePolynomialModule B n r}
    (hP : P ∈ G.windowStrictLowerPiece (B := B) hpositive D
      (G.weightAt hpositive D i)) :
    G.windowOrderedWeightLinearEquiv hpositive D
        ⟨P, G.windowStrictLowerPiece_le_windowModule hpositive D
          (G.weightAt hpositive D i) hP⟩ =
      finiteWeightPrefixProjection B
        (fun j : Fin (G.weightCount hpositive D) =>
          G.orderedWeightPiece B hpositive D j) i.val
      (G.windowOrderedWeightLinearEquiv hpositive D
          ⟨P, G.windowStrictLowerPiece_le_windowModule hpositive D
            (G.weightAt hpositive D i) hP⟩) := by
  classical
  symm
  apply (finiteWeightPrefixProjection_eq_self_iff i.val _).mpr
  intro j hji
  apply Subtype.ext
  change artinianPolynomialModuleFiberComponent G.termWeight
    (G.weightAt hpositive D j) P = 0
  funext k
  apply MvPolynomial.ext
  intro d
  rw [artinianPolynomialModuleFiberComponent_coeff,
    Pi.zero_apply, AddMonoidAlgebra.coeff_zero]
  by_cases hweight : G.termWeight (k, d) = G.weightAt hpositive D j
  · rw [ite_eq_left hweight]
    by_contra hcoeff
    have hlower :=
      ((mem_artinianPolynomialModuleSupported _ _).mp hP k d hcoeff).2
    rw [hweight, G.weightAt_lt_iff hpositive D] at hlower
    exact (not_lt_of_ge hji) hlower
  · exact ite_eq_right hweight

/-! ## Restriction and conjugation of the triangular automorphism -/

/-- Restriction of a coefficient-linear automorphism that preserves the
bounded ordinary-degree window. -/
def PolynomialGradedLexData.windowRestriction
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r)
    (hJ : (G.windowModule B hpositive D).map J.toLinearMap =
      G.windowModule B hpositive D) :
    G.windowModule B hpositive D ≃ₗ[B]
      G.windowModule B hpositive D :=
  J.ofSubmodules (G.windowModule B hpositive D)
    (G.windowModule B hpositive D) hJ

@[simp]
theorem PolynomialGradedLexData.windowRestriction_coe
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r)
    (hJ : (G.windowModule B hpositive D).map J.toLinearMap =
      G.windowModule B hpositive D)
    (P : G.windowModule B hpositive D) :
    (G.windowRestriction hpositive D J hJ P :
      artinianFreePolynomialModule B n r) = J P :=
  LinearEquiv.ofSubmodules_apply J hJ P

/-- Conjugate a window-preserving automorphism into the ordered finite
weight product. -/
def PolynomialGradedLexData.windowOrderedWeightConjugate
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r)
    (hJ : (G.windowModule B hpositive D).map J.toLinearMap =
      G.windowModule B hpositive D) :
    ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) ≃ₗ[B]
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :=
  (G.windowOrderedWeightLinearEquiv hpositive D).symm.trans
    ((G.windowRestriction hpositive D J hJ).trans
      (G.windowOrderedWeightLinearEquiv hpositive D))

/-- Polynomial form of strict lexicographic unipotent triangularity on a
bounded ordinary-degree window. -/
def PolynomialGradedLexData.IsWindowWeightTriangular
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r) : Prop :=
  ∀ (weight : PolynomialLexWeight h)
    (P : artinianFreePolynomialModule B n r),
    P ∈ G.windowWeightPiece B hpositive D weight →
      J P - P ∈ G.windowStrictLowerPiece (B := B) hpositive D weight

/-- Strict polynomial triangularity becomes the literal prefix identity
required by `exists_finiteWeightDescent_stabilizes`. -/
theorem PolynomialGradedLexData.windowOrderedWeightConjugate_triangular
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r)
    (hJ : (G.windowModule B hpositive D).map J.toLinearMap =
      G.windowModule B hpositive D)
    (htri : G.IsWindowWeightTriangular hpositive D J) :
    ∀ i (v : G.orderedWeightPiece B hpositive D i),
      G.windowOrderedWeightConjugate hpositive D J hJ (Pi.single i v) =
        Pi.single i v +
          finiteWeightPrefixProjection B
            (fun j : Fin (G.weightCount hpositive D) =>
              G.orderedWeightPiece B hpositive D j) i.val
            (G.windowOrderedWeightConjugate hpositive D J hJ
              (Pi.single i v)) := by
  classical
  intro i v
  let E := G.windowOrderedWeightLinearEquiv (B := B) hpositive D
  let p : G.windowModule B hpositive D :=
    ⟨(v : artinianFreePolynomialModule B n r),
      G.windowWeightPiece_le_windowModule hpositive D
        (G.weightAt hpositive D i) v.2⟩
  have hsingle : E.symm (Pi.single i v) = p := by
    apply Subtype.ext
    exact G.windowOrderedWeightLinearEquiv_symm_single_coe hpositive D i v
  let q₀ : artinianFreePolynomialModule B n r := J v - v
  have hq₀ : q₀ ∈ G.windowStrictLowerPiece (B := B) hpositive D
      (G.weightAt hpositive D i) :=
    htri (G.weightAt hpositive D i) v v.2
  let q : G.windowModule B hpositive D :=
    ⟨q₀, G.windowStrictLowerPiece_le_windowModule hpositive D
      (G.weightAt hpositive D i) hq₀⟩
  have hJp : G.windowRestriction hpositive D J hJ p = p + q := by
    apply Subtype.ext
    rw [G.windowRestriction_coe]
    change J (v : artinianFreePolynomialModule B n r) =
      (v : artinianFreePolynomialModule B n r) + (J v - v)
    abel
  have hEp : E p = Pi.single i v := by
    calc
      E p = E (E.symm (Pi.single i v)) := congrArg E hsingle.symm
      _ = Pi.single i v := E.apply_symm_apply _
  have hconj : G.windowOrderedWeightConjugate hpositive D J hJ
      (Pi.single i v) = Pi.single i v + E q := by
    change E (G.windowRestriction hpositive D J hJ
      (E.symm (Pi.single i v))) = _
    rw [hsingle, hJp, map_add, hEp]
  have hlower : E q =
      finiteWeightPrefixProjection B
        (fun j : Fin (G.weightCount hpositive D) =>
          G.orderedWeightPiece B hpositive D j) i.val (E q) :=
    G.windowOrderedWeightLinearEquiv_eq_prefix_of_mem_lower
      hpositive D i hq₀
  rw [hconj, map_add,
    finiteWeightPrefixProjection_single,
    ite_eq_right (lt_irrefl i.val), ← hlower]
  simp

/-! ## Joint homogeneity and its two marginal gradings -/

/-- Weight homogeneity stated through the actual coefficient projections. -/
def PolynomialGradedLexData.IsPolynomialModuleWeightHomogeneous
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r)) : Prop :=
  ∀ (P : artinianFreePolynomialModule B n r), P ∈ N →
    ∀ weight : PolynomialLexWeight h,
      artinianPolynomialModuleFiberComponent G.termWeight weight P ∈ N

/-- The finite set of shifted ordinary degrees actually occurring in a
polynomial-module vector. -/
def PolynomialGradedLexData.ordinaryDegreeSupport
    (P : artinianFreePolynomialModule B n r) : Finset ℤ :=
  (artinianPolynomialModuleCoeffEquiv P).support.image G.termOrdinaryDegree

/-- Summing the joint components over the ordinary degrees occurring in
`P` gives its full component at one lexicographic weight. -/
theorem PolynomialGradedLexData.sum_jointComponent_eq_weightComponent
    (P : artinianFreePolynomialModule B n r)
    (weight : PolynomialLexWeight h) :
    (∑ degree ∈ G.ordinaryDegreeSupport P,
        G.jointComponent B degree weight P) =
      artinianPolynomialModuleFiberComponent G.termWeight weight P := by
  classical
  funext k
  apply MvPolynomial.ext
  intro d
  simp only [Finset.sum_apply, MvPolynomial.coeff_sum,
    G.jointComponent_coeff,
    artinianPolynomialModuleFiberComponent_coeff]
  by_cases hweight : G.termWeight (k, d) = weight
  · rw [ite_eq_left hweight]
    by_cases hcoeff : (P k).coeff d = 0
    · simp [hcoeff]
    · have hdegree : G.termOrdinaryDegree (k, d) ∈
          G.ordinaryDegreeSupport P := by
        apply Finset.mem_image.mpr
        refine ⟨(k, d), ?_, rfl⟩
        rw [Finsupp.mem_support_iff]
        simpa only [artinianPolynomialModuleCoeffEquiv_apply] using hcoeff
      rw [Finset.sum_eq_single (G.termOrdinaryDegree (k, d))]
      · rw [ite_eq_left]
        exact Prod.ext rfl hweight
      · intro degree hdegree' hne
        rw [ite_eq_right]
        intro hjoint
        apply hne
        exact (congrArg Prod.fst hjoint).symm
      · intro hnot
        exact (hnot hdegree).elim
  · rw [ite_eq_right hweight]
    apply Finset.sum_eq_zero
    intro degree hdegree
    rw [ite_eq_right]
    intro hjoint
    exact hweight (congrArg Prod.snd hjoint)

/-- Closure of a polynomial submodule under every joint ordinary/weight
coefficient projection. -/
def PolynomialGradedLexData.IsPolynomialModuleJointHomogeneous
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r)) : Prop :=
  ∀ (P : artinianFreePolynomialModule B n r), P ∈ N →
    ∀ (degree : ℤ) (weight : PolynomialLexWeight h),
      G.jointComponent B degree weight P ∈ N

/-- Joint homogeneity implies the ordinary homogeneity used by the uniform
Artinian generator theorem. -/
theorem PolynomialGradedLexData.IsPolynomialModuleJointHomogeneous.ordinary
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    {N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r)}
    (hN : G.IsPolynomialModuleJointHomogeneous N) :
    IsArtinianPolynomialSubmoduleHomogeneous
      G.ordinaryDegree G.ordinaryShift N := by
  intro P hP degree
  rw [← G.sum_jointComponent_eq_ordinaryComponent hpositive degree P]
  apply Submodule.sum_mem
  intro weight hweight
  exact hN P hP degree weight

/-- Joint homogeneity also implies homogeneity for the grouped
lexicographic-weight projections used in the bounded window. -/
theorem PolynomialGradedLexData.IsPolynomialModuleJointHomogeneous.weight
    {N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r)}
    (hN : G.IsPolynomialModuleJointHomogeneous N) :
    G.IsPolynomialModuleWeightHomogeneous N := by
  intro P hP weight
  rw [← G.sum_jointComponent_eq_weightComponent P weight]
  apply Submodule.sum_mem
  intro degree hdegree
  exact hN P hP degree weight

/-! ## Bounded parts of polynomial submodules -/

/-- The coefficient-linear bounded-window part of a polynomial submodule. -/
def PolynomialGradedLexData.polynomialWindowPart
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r)) :
    Submodule B (G.windowModule B hpositive D) :=
  (N.restrictScalars B).comap (G.windowModule B hpositive D).subtype

/-- The bounded part transported to the literal ordered product. -/
def PolynomialGradedLexData.polynomialWindowOrderedWeightPart
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r)) :
    Submodule B
      ((i : Fin (G.weightCount hpositive D)) →
        G.orderedWeightPiece B hpositive D i) :=
  (G.polynomialWindowPart hpositive D N).map
    (G.windowOrderedWeightLinearEquiv hpositive D).toLinearMap

/-- Weight homogeneity of the polynomial submodule becomes literal
coordinate homogeneity of its transported bounded part. -/
theorem PolynomialGradedLexData.polynomialWindowOrderedWeightPart_homogeneous
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (hN : G.IsPolynomialModuleWeightHomogeneous N) :
    ∀ x ∈ G.polynomialWindowOrderedWeightPart hpositive D N,
      ∀ i, Pi.single i (x i) ∈
        G.polynomialWindowOrderedWeightPart hpositive D N := by
  classical
  rintro x ⟨P, hP, rfl⟩ i
  let E := G.windowOrderedWeightLinearEquiv (B := B) hpositive D
  refine ⟨E.symm (Pi.single i (E P i)), ?_, E.apply_symm_apply _⟩
  change ((E.symm (Pi.single i (E P i)) : G.windowModule B hpositive D) :
    artinianFreePolynomialModule B n r) ∈ N
  rw [G.windowOrderedWeightLinearEquiv_symm_single_coe]
  change (G.windowWeightComponent hpositive D
    (G.weightAt hpositive D i) P :
      artinianFreePolynomialModule B n r) ∈ N
  rw [G.windowWeightComponent_coe]
  apply hN (P : artinianFreePolynomialModule B n r)
  exact hP

/-- The actual polynomial vectors that lie both in `N` and in the bounded
ordinary-degree window. -/
def PolynomialGradedLexData.polynomialWindowCarrier
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r)) :
    Set (artinianFreePolynomialModule B n r) :=
  {P | P ∈ N ∧ P ∈ G.windowModule B hpositive D}

/-- The bounded window determines `N` when its vectors generate `N` over
the polynomial ring. -/
def PolynomialGradedLexData.IsGeneratedInPolynomialWindow
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r)) : Prop :=
  Submodule.span (MvPolynomial (Fin n) B)
    (G.polynomialWindowCarrier hpositive D N) = N

theorem PolynomialGradedLexData.isGeneratedInPolynomialWindow_of_generators
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (H : Finset (artinianFreePolynomialModule B n r))
    (hH : ∀ P ∈ H, P ∈ N ∧
      ∃ degree : ℤ, degree ≤ D ∧
        P ∈ artinianPolynomialModulePiece (B := B)
          G.ordinaryDegree G.ordinaryShift degree)
    (hspan : Submodule.span (MvPolynomial (Fin n) B) (H : Set _) = N) :
    G.IsGeneratedInPolynomialWindow hpositive D N := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro P hP
    exact hP.1
  · calc
      N = Submodule.span (MvPolynomial (Fin n) B) (H : Set _) := hspan.symm
      _ ≤ Submodule.span (MvPolynomial (Fin n) B)
          (G.polynomialWindowCarrier hpositive D N) := by
        apply Submodule.span_mono
        intro P hP
        obtain ⟨hPN, degree, hdegree, hPdegree⟩ := hH P hP
        exact ⟨hPN, G.ordinaryPiece_le_windowModule hpositive D degree
          hdegree hPdegree⟩

/-- Two boundedly generated polynomial submodules are equal as soon as
their coefficient-linear bounded parts are equal. -/
theorem PolynomialGradedLexData.eq_of_polynomialWindowPart_eq
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (N N' : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (hN : G.IsGeneratedInPolynomialWindow hpositive D N)
    (hN' : G.IsGeneratedInPolynomialWindow hpositive D N')
    (hpart : G.polynomialWindowPart hpositive D N =
      G.polynomialWindowPart hpositive D N') : N = N' := by
  have hcarrier : G.polynomialWindowCarrier hpositive D N =
      G.polynomialWindowCarrier hpositive D N' := by
    ext P
    constructor
    · rintro ⟨hPN, hPW⟩
      refine ⟨?_, hPW⟩
      let p : G.windowModule B hpositive D := ⟨P, hPW⟩
      have hp : p ∈ G.polynomialWindowPart hpositive D N := hPN
      rw [hpart] at hp
      exact hp
    · rintro ⟨hPN', hPW⟩
      refine ⟨?_, hPW⟩
      let p : G.windowModule B hpositive D := ⟨P, hPW⟩
      have hp : p ∈ G.polynomialWindowPart hpositive D N' := hPN'
      rw [← hpart] at hp
      exact hp
  rw [← hN, ← hN', hcarrier]

/-- Module 186's Artinian-local uniform generator bound, repackaged as
determination by one finite ordinary-degree window. -/
theorem PolynomialGradedLexData.exists_uniform_generatedInPolynomialWindow
    [IsNoetherianRing B] [IsArtinianRing B]
    (m : MonomialOrder (Fin n))
    (I : Ideal B) [I.IsMaximal]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i)
    {e : ℕ} (he : I ^ e = ⊥)
    (hilbertLength : ℤ → ℕ) :
    ∃ D : ℕ,
      ∀ N : Submodule (MvPolynomial (Fin n) B)
          (artinianFreePolynomialModule B n r),
        ∀ _hN : IsArtinianPolynomialSubmoduleHomogeneous
          G.ordinaryDegree G.ordinaryShift N,
        (∀ degree,
          (Module.length B
            (artinianPolynomialSubmoduleDegree N
              G.ordinaryDegree G.ordinaryShift degree)).toNat =
                hilbertLength degree) →
        G.IsGeneratedInPolynomialWindow hpositive (D : ℤ) N := by
  obtain ⟨D, hD⟩ :=
    exists_uniform_finite_homogeneous_artinianPolynomialSubmodule_generators
      m I G.ordinaryDegree hpositive G.ordinaryShift he hilbertLength
  refine ⟨D, ?_⟩
  intro N hN hlength
  obtain ⟨H, hH, hspan⟩ := hD N hN hlength
  exact G.isGeneratedInPolynomialWindow_of_generators hpositive (D : ℤ)
    N H hH hspan

/-- The Artinian finite-product stabilization theorem, now fed by an actual
bounded polynomial submodule and an actual polynomial triangular map. -/
theorem PolynomialGradedLexData.exists_polynomialWindowOrderedWeightDescent_stabilizes
    [IsArtinianRing B]
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (J : artinianFreePolynomialModule B n r ≃ₗ[B]
      artinianFreePolynomialModule B n r)
    (hJ : (G.windowModule B hpositive D).map J.toLinearMap =
      G.windowModule B hpositive D)
    (htri : G.IsWindowWeightTriangular hpositive D J)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (hN : G.IsPolynomialModuleWeightHomogeneous N) :
    ∃ j₀ : ℕ,
      (finiteWeightDescentIterate
          (G.windowOrderedWeightConjugate hpositive D J hJ)
          (G.polynomialWindowOrderedWeightPart hpositive D N) j₀).map
          (G.windowOrderedWeightConjugate hpositive D J hJ).toLinearMap =
        finiteWeightDescentIterate
          (G.windowOrderedWeightConjugate hpositive D J hJ)
          (G.polynomialWindowOrderedWeightPart hpositive D N) j₀ ∧
      ∀ j, j₀ ≤ j →
        finiteWeightDescentIterate
          (G.windowOrderedWeightConjugate hpositive D J hJ)
          (G.polynomialWindowOrderedWeightPart hpositive D N) j =
        finiteWeightDescentIterate
          (G.windowOrderedWeightConjugate hpositive D J hJ)
          (G.polynomialWindowOrderedWeightPart hpositive D N) j₀ := by
  exact G.exists_windowOrderedWeightDescent_stabilizes_of_isArtinianRing
    hpositive D (G.windowOrderedWeightConjugate hpositive D J hJ)
    (G.windowOrderedWeightConjugate_triangular hpositive D J hJ htri)
    (G.polynomialWindowOrderedWeightPart hpositive D N)
    (G.polynomialWindowOrderedWeightPart_homogeneous hpositive D N hN)

end AbelFormalization
