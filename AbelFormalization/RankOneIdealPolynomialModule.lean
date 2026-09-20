import AbelFormalization.PolynomialWindowDescent
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Submodule.RestrictScalars

set_option autoImplicit false

/-!
# Rank-one ideals as free polynomial submodules

The rank-one free polynomial module is literally

`Fin 1 → MvPolynomial (Fin n) B`.

This file records the concrete linear equivalence with the polynomial ring,
uses it to transport ideals to polynomial submodules, and relates that
transport to coefficient restriction and bounded polynomial windows.
-/

noncomputable section

namespace AbelFormalization

variable {B : Type*} [CommRing B] {n h : ℕ}

/-- Put a polynomial in the unique coordinate of the rank-one free
polynomial module. -/
def rankOnePolynomialModuleEquiv :
    MvPolynomial (Fin n) B ≃ₗ[MvPolynomial (Fin n) B]
      artinianFreePolynomialModule B n 1 where
  toFun := fun P _ => P
  invFun := fun P => P 0
  left_inv := fun _ => rfl
  right_inv := by
    intro P
    funext i
    exact congrArg P (Subsingleton.elim 0 i)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

@[simp]
theorem rankOnePolynomialModuleEquiv_apply
    (P : MvPolynomial (Fin n) B) (i : Fin 1) :
    rankOnePolynomialModuleEquiv P i = P :=
  rfl

@[simp]
theorem rankOnePolynomialModuleEquiv_symm_apply
    (P : artinianFreePolynomialModule B n 1) :
    rankOnePolynomialModuleEquiv.symm P = P 0 :=
  rfl

/-- The same equivalence after restricting scalars from the polynomial ring
to its coefficient ring. -/
def rankOnePolynomialModuleCoeffEquiv :
    MvPolynomial (Fin n) B ≃ₗ[B]
      artinianFreePolynomialModule B n 1 :=
  rankOnePolynomialModuleEquiv.restrictScalars B

@[simp]
theorem rankOnePolynomialModuleCoeffEquiv_apply
    (P : MvPolynomial (Fin n) B) (i : Fin 1) :
    rankOnePolynomialModuleCoeffEquiv P i = P :=
  rfl

@[simp]
theorem rankOnePolynomialModuleCoeffEquiv_symm_apply
    (P : artinianFreePolynomialModule B n 1) :
    rankOnePolynomialModuleCoeffEquiv.symm P = P 0 :=
  rfl

/-- An ideal of the polynomial ring, regarded as a polynomial submodule of
the rank-one free polynomial module. -/
def rankOnePolynomialIdealSubmodule
    (I : Ideal (MvPolynomial (Fin n) B)) :
    Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n 1) :=
  Submodule.map rankOnePolynomialModuleEquiv.toLinearMap I

/-- Membership in the transported ideal is membership of the unique
coordinate in the original ideal. -/
@[simp]
theorem mem_rankOnePolynomialIdealSubmodule_iff
    (I : Ideal (MvPolynomial (Fin n) B))
    (P : artinianFreePolynomialModule B n 1) :
    P ∈ rankOnePolynomialIdealSubmodule I ↔ P 0 ∈ I := by
  rw [rankOnePolynomialIdealSubmodule, Submodule.mem_map_equiv]
  rfl

/-- The canonical rank-one vector of `P` belongs to the transported ideal
exactly when `P` belongs to the ideal. -/
@[simp]
theorem rankOnePolynomialModuleEquiv_mem_idealSubmodule_iff
    (I : Ideal (MvPolynomial (Fin n) B))
    (P : MvPolynomial (Fin n) B) :
    rankOnePolynomialModuleEquiv P ∈
        rankOnePolynomialIdealSubmodule I ↔
      P ∈ I := by
  rw [mem_rankOnePolynomialIdealSubmodule_iff,
    rankOnePolynomialModuleEquiv_apply]

/-- Mapping the transported submodule back through the inverse equivalence
recovers the ideal. -/
@[simp]
theorem map_rankOnePolynomialIdealSubmodule_symm
    (I : Ideal (MvPolynomial (Fin n) B)) :
    (rankOnePolynomialIdealSubmodule I).map
        rankOnePolynomialModuleEquiv.symm.toLinearMap = I := by
  ext P
  simp

/-- Transport to the rank-one polynomial module reflects inclusion. -/
theorem rankOnePolynomialIdealSubmodule_le_iff
    (I J : Ideal (MvPolynomial (Fin n) B)) :
    rankOnePolynomialIdealSubmodule I ≤
        rankOnePolynomialIdealSubmodule J ↔
      I ≤ J := by
  constructor
  · intro h P hP
    have hmap : rankOnePolynomialModuleEquiv P ∈
        rankOnePolynomialIdealSubmodule I := by
      simpa using hP
    have := h hmap
    simpa using this
  · intro h P hP
    rw [mem_rankOnePolynomialIdealSubmodule_iff] at hP ⊢
    exact h hP

/-- Transport from ideals to rank-one polynomial submodules is injective. -/
theorem rankOnePolynomialIdealSubmodule_injective :
    Function.Injective
      (rankOnePolynomialIdealSubmodule (B := B) (n := n)) := by
  intro I J hIJ
  apply le_antisymm
  · exact (rankOnePolynomialIdealSubmodule_le_iff I J).mp hIJ.le
  · exact (rankOnePolynomialIdealSubmodule_le_iff J I).mp hIJ.ge

@[simp]
theorem rankOnePolynomialIdealSubmodule_bot :
    rankOnePolynomialIdealSubmodule
        (⊥ : Ideal (MvPolynomial (Fin n) B)) = ⊥ := by
  ext P
  rw [mem_rankOnePolynomialIdealSubmodule_iff]
  constructor
  · intro hP
    rw [Submodule.mem_bot] at hP ⊢
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact hP
  · intro hP
    rw [Submodule.mem_bot] at hP ⊢
    simpa only [hP, Pi.zero_apply]

@[simp]
theorem rankOnePolynomialIdealSubmodule_top :
    rankOnePolynomialIdealSubmodule
        (⊤ : Ideal (MvPolynomial (Fin n) B)) = ⊤ := by
  ext P
  simp

/-- Restricting the transported polynomial submodule to coefficient scalars
is the same as first restricting the ideal and then applying the
coefficient-linear rank-one equivalence. -/
theorem rankOnePolynomialIdealSubmodule_restrictScalars
    (I : Ideal (MvPolynomial (Fin n) B)) :
    (rankOnePolynomialIdealSubmodule I).restrictScalars B =
      (I.restrictScalars B).map
        rankOnePolynomialModuleCoeffEquiv.toLinearMap := by
  change
    (Submodule.map rankOnePolynomialModuleEquiv.toLinearMap I).restrictScalars B = _
  rw [Submodule.restrictScalars_map]
  rfl

/-! ## Bounded-window compatibility -/

variable (G : PolynomialGradedLexData n 1 h)

/-- The coefficient-linear submodule of polynomials whose canonical
rank-one vector belongs to the bounded window. -/
def PolynomialGradedLexData.rankOnePolynomialWindowPreimage
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ) :
    Submodule B (MvPolynomial (Fin n) B) :=
  (G.windowModule B hpositive D).comap
    rankOnePolynomialModuleCoeffEquiv.toLinearMap

@[simp]
theorem PolynomialGradedLexData.mem_rankOnePolynomialWindowPreimage_iff
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (P : MvPolynomial (Fin n) B) :
    P ∈ G.rankOnePolynomialWindowPreimage hpositive D ↔
      rankOnePolynomialModuleCoeffEquiv P ∈
        G.windowModule B hpositive D :=
  Iff.rfl

/-- Concrete coefficient-support description of the pulled-back rank-one
window. -/
theorem PolynomialGradedLexData.mem_rankOnePolynomialWindowPreimage_iff_coeff
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (P : MvPolynomial (Fin n) B) :
    P ∈ G.rankOnePolynomialWindowPreimage hpositive D ↔
      ∀ d : Fin n →₀ ℕ, P.coeff d ≠ 0 →
        ((0 : Fin 1), d) ∈ G.windowTermSet hpositive D := by
  rw [G.mem_rankOnePolynomialWindowPreimage_iff]
  change rankOnePolynomialModuleCoeffEquiv P ∈
      artinianPolynomialModuleSupported (G.windowTermSet hpositive D) ↔ _
  rw [mem_artinianPolynomialModuleSupported]
  constructor
  · intro hP d hd
    exact hP 0 d (by simpa using hd)
  · intro hP i d hd
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact hP d (by simpa using hd)

/-- Membership in the bounded part of a transported ideal is detected in
the unique rank-one coordinate. -/
@[simp]
theorem PolynomialGradedLexData.mem_polynomialWindowPart_rankOneIdeal_iff
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (P : G.windowModule B hpositive D) :
    P ∈ G.polynomialWindowPart hpositive D
        (rankOnePolynomialIdealSubmodule I) ↔
      ((P : artinianFreePolynomialModule B n 1) 0) ∈ I := by
  change (P : artinianFreePolynomialModule B n 1) ∈
      rankOnePolynomialIdealSubmodule I ↔ _
  exact mem_rankOnePolynomialIdealSubmodule_iff I P

/-- The image in the ambient rank-one module of the bounded part is the
intersection of the bounded window with the coefficient restriction of the
transported ideal. -/
theorem PolynomialGradedLexData.map_polynomialWindowPart_rankOneIdeal
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B)) :
    (G.polynomialWindowPart hpositive D
        (rankOnePolynomialIdealSubmodule I)).map
        (G.windowModule B hpositive D).subtype =
      G.windowModule B hpositive D ⊓
        (rankOnePolynomialIdealSubmodule I).restrictScalars B := by
  simpa only [PolynomialGradedLexData.polynomialWindowPart] using
    (Submodule.map_comap_subtype
      (p := G.windowModule B hpositive D)
      (p' := (rankOnePolynomialIdealSubmodule I).restrictScalars B))

/-- Under the coefficient-linear rank-one equivalence, intersecting an
ideal with the pulled-back bounded window becomes the intersection of the
transported ideal with the actual bounded window. -/
theorem PolynomialGradedLexData.map_rankOneIdeal_inf_windowPreimage
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B)) :
    ((I.restrictScalars B) ⊓
        G.rankOnePolynomialWindowPreimage hpositive D).map
        rankOnePolynomialModuleCoeffEquiv.toLinearMap =
      (rankOnePolynomialIdealSubmodule I).restrictScalars B ⊓
        G.windowModule B hpositive D := by
  rw [Submodule.map_inf _ rankOnePolynomialModuleCoeffEquiv.injective,
    ← rankOnePolynomialIdealSubmodule_restrictScalars I]
  change _ ⊓
      ((G.windowModule B hpositive D).comap
        rankOnePolynomialModuleCoeffEquiv.toLinearMap).map
          rankOnePolynomialModuleCoeffEquiv.toLinearMap = _
  rw [Submodule.map_comap_eq_of_surjective
    rankOnePolynomialModuleCoeffEquiv.surjective]

/-- Membership in the polynomial-window carrier of a transported ideal is
the conjunction of ideal membership in the unique coordinate and bounded
window membership. -/
@[simp]
theorem PolynomialGradedLexData.mem_polynomialWindowCarrier_rankOneIdeal_iff
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (P : artinianFreePolynomialModule B n 1) :
    P ∈ G.polynomialWindowCarrier hpositive D
        (rankOnePolynomialIdealSubmodule I) ↔
      P 0 ∈ I ∧ P ∈ G.windowModule B hpositive D := by
  simp only [PolynomialGradedLexData.polynomialWindowCarrier,
    Set.mem_setOf_eq, mem_rankOnePolynomialIdealSubmodule_iff]

/-- Membership in the transported bounded part after ordered-weight
decomposition can still be read by returning to its unique polynomial
coordinate. -/
@[simp]
theorem PolynomialGradedLexData.mem_polynomialWindowOrderedWeightPart_rankOneIdeal_iff
    (hpositive : ∀ i, 0 < G.ordinaryDegree i) (D : ℤ)
    (I : Ideal (MvPolynomial (Fin n) B))
    (x : (i : Fin (G.weightCount hpositive D)) →
      G.orderedWeightPiece B hpositive D i) :
    x ∈ G.polynomialWindowOrderedWeightPart hpositive D
        (rankOnePolynomialIdealSubmodule I) ↔
      ((((G.windowOrderedWeightLinearEquiv (B := B) hpositive D).symm x :
          G.windowModule B hpositive D) :
        artinianFreePolynomialModule B n 1) 0) ∈ I := by
  rw [PolynomialGradedLexData.polynomialWindowOrderedWeightPart,
    Submodule.mem_map_equiv]
  exact G.mem_polynomialWindowPart_rankOneIdeal_iff hpositive D I _

end AbelFormalization
