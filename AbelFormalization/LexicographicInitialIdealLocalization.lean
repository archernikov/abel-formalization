import AbelFormalization.LexicographicInitialIdeals
import Mathlib.RingTheory.MvPolynomial.Localization

set_option autoImplicit false

/-!
# Lexicographic initial ideals and coefficient localization

The first lemmas isolate the element-level fact used in both directions of
base change: mapping a least-weight component either kills it, or leaves it
the least-weight component of the mapped polynomial.
-/

noncomputable section

namespace AbelFormalization

variable {R T ι : Type*} [CommRing R] [CommRing T] {h : ℕ}

/-- Coefficient maps commute with a fixed weighted homogeneous component. -/
theorem mvPolynomial_map_weightedHomogeneousComponent
    (f : R →+* T) (weight : ι → Lex (Fin h → ℤ))
    (degree : Lex (Fin h → ℤ)) (p : MvPolynomial ι R) :
    MvPolynomial.map f
        (MvPolynomial.weightedHomogeneousComponent weight degree p) =
      MvPolynomial.weightedHomogeneousComponent weight degree
        (MvPolynomial.map f p) := by
  classical
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_map,
    MvPolynomial.coeff_weightedHomogeneousComponent]
  split <;> simp_all

/-- Under an arbitrary coefficient map, the source initial form either dies
or maps to the actual initial form of the image. -/
theorem lexicographicInitialForm_map_eq_zero_or_eq
    (f : R →+* T) (weight : ι → Fin h → ℤ)
    (p : MvPolynomial ι R) :
    MvPolynomial.map f (lexicographicInitialForm weight p) = 0 ∨
      MvPolynomial.map f (lexicographicInitialForm weight p) =
        lexicographicInitialForm weight (MvPolynomial.map f p) := by
  classical
  by_cases hz : MvPolynomial.map f
      (lexicographicInitialForm weight p) = 0
  · exact Or.inl hz
  right
  have hcomponent :
      MvPolynomial.map f (lexicographicInitialForm weight p) =
        MvPolynomial.weightedHomogeneousComponent
          (fun i ↦ toLex (weight i))
          (lexicographicMinimumWeight weight p)
          (MvPolynomial.map f p) := by
    exact mvPolynomial_map_weightedHomogeneousComponent f
      (fun i ↦ toLex (weight i))
      (lexicographicMinimumWeight weight p) p
  have hcomponent_ne :
      MvPolynomial.weightedHomogeneousComponent
          (fun i ↦ toLex (weight i))
          (lexicographicMinimumWeight weight p)
          (MvPolynomial.map f p) ≠ 0 := by
    rwa [← hcomponent]
  have hbound : ∀ d ∈ (MvPolynomial.map f p).support,
      lexicographicMinimumWeight weight p ≤
        Finsupp.weight (fun i ↦ toLex (weight i)) d := by
    intro d hd
    exact lexicographicMinimumWeight_le weight p
      (MvPolynomial.support_map_subset f p hd)
  have hminimum :
      lexicographicMinimumWeight weight (MvPolynomial.map f p) =
        lexicographicMinimumWeight weight p :=
    lexicographicMinimumWeight_eq_of_component_ne_zero
      weight (MvPolynomial.map f p)
      (lexicographicMinimumWeight weight p) hbound hcomponent_ne
  calc
    MvPolynomial.map f (lexicographicInitialForm weight p) =
        MvPolynomial.weightedHomogeneousComponent
          (fun i ↦ toLex (weight i))
          (lexicographicMinimumWeight weight p)
          (MvPolynomial.map f p) := hcomponent
    _ = MvPolynomial.weightedHomogeneousComponent
          (fun i ↦ toLex (weight i))
          (lexicographicMinimumWeight weight (MvPolynomial.map f p))
          (MvPolynomial.map f p) := by rw [hminimum]
    _ = lexicographicInitialForm weight (MvPolynomial.map f p) := rfl

/-- Consequently every mapped source initial form belongs to the initial
ideal after coefficient base change. -/
theorem map_lexicographicInitialForm_mem_lexicographicInitialIdeal_map
    (f : R →+* T) (weight : ι → Fin h → ℤ)
    (I : Ideal (MvPolynomial ι R)) {p : MvPolynomial ι R}
    (hp : p ∈ I) :
    MvPolynomial.map f (lexicographicInitialForm weight p) ∈
      lexicographicInitialIdeal weight (I.map (MvPolynomial.map f)) := by
  rcases lexicographicInitialForm_map_eq_zero_or_eq f weight p with hz | heq
  · rw [hz]
    exact Ideal.zero_mem _
  · rw [heq]
    exact lexicographicInitialForm_mem_initialIdeal weight _
      (Ideal.mem_map_of_mem (MvPolynomial.map f) hp)

/-- The easy inclusion: coefficient base change of an initial ideal is
contained in the initial ideal of the base-changed ideal. -/
theorem lexicographicInitialIdeal_map_le
    (f : R →+* T) (weight : ι → Fin h → ℤ)
    (I : Ideal (MvPolynomial ι R)) :
    (lexicographicInitialIdeal weight I).map (MvPolynomial.map f) ≤
      lexicographicInitialIdeal weight (I.map (MvPolynomial.map f)) := by
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  rintro _ ⟨p, hp, rfl⟩
  exact map_lexicographicInitialForm_mem_lexicographicInitialIdeal_map
    f weight I hp

end AbelFormalization
