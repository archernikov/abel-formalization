import AbelFormalization.RankOneIdealWindowRecurrence

set_option autoImplicit false

/-!
# Base change for the lexicographic initial-ideal iteration

This module isolates the formal recursion shared by product decompositions,
coefficient localizations, and principal quotients.  Once the coefficient
map commutes with both the polynomial automorphism and full initial-ideal
formation, it commutes with every iterate.
-/

noncomputable section

namespace AbelFormalization

variable {R S : Type*} [CommRing R] [CommRing S]
variable {n h : ℕ}

/-- Every lexicographic initial-ideal iterate commutes with a coefficient-ring
map, provided the two operations defining one step commute with that map. -/
theorem lexicographicInitialIdealIteration_map
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) R ≃+* MvPolynomial (Fin n) R)
    (J' : MvPolynomial (Fin n) S ≃+* MvPolynomial (Fin n) S)
    (f : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) S)
    (hJ : f.comp J.toRingHom = J'.toRingHom.comp f)
    (hinitial : ∀ I : Ideal (MvPolynomial (Fin n) R),
      (lexicographicInitialIdeal multiDegree I).map f =
        lexicographicInitialIdeal multiDegree (I.map f))
    (Q : Ideal (MvPolynomial (Fin n) R)) :
    ∀ j : ℕ,
      (lexicographicInitialIdealIteration multiDegree J Q j).map f =
        lexicographicInitialIdealIteration multiDegree J' (Q.map f) j := by
  intro j
  induction j with
  | zero =>
      simp only [lexicographicInitialIdealIteration_zero]
      exact hinitial Q
  | succ j ih =>
      rw [lexicographicInitialIdealIteration_succ,
        lexicographicInitialIdealIteration_succ]
      calc
        (lexicographicInitialIdeal multiDegree
            ((lexicographicInitialIdealIteration multiDegree J Q j).map
              J.toRingHom)).map f =
          lexicographicInitialIdeal multiDegree
            (((lexicographicInitialIdealIteration multiDegree J Q j).map
              J.toRingHom).map f) :=
            hinitial _
        _ = lexicographicInitialIdeal multiDegree
            (((lexicographicInitialIdealIteration multiDegree J Q j).map f).map
              J'.toRingHom) := by
            rw [Ideal.map_map, Ideal.map_map, hJ]
        _ = lexicographicInitialIdeal multiDegree
            ((lexicographicInitialIdealIteration multiDegree J'
              (Q.map f) j).map J'.toRingHom) := by rw [ih]

/-- Pointwise coefficient-map naturality is enough to instantiate the
ring-homomorphism hypothesis above. -/
theorem lexicographicInitialIdealIteration_map_of_apply
    (multiDegree : Fin n → Fin h → ℤ)
    (J : MvPolynomial (Fin n) R ≃+* MvPolynomial (Fin n) R)
    (J' : MvPolynomial (Fin n) S ≃+* MvPolynomial (Fin n) S)
    (f : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) S)
    (hJ : ∀ P, f (J P) = J' (f P))
    (hinitial : ∀ I : Ideal (MvPolynomial (Fin n) R),
      (lexicographicInitialIdeal multiDegree I).map f =
        lexicographicInitialIdeal multiDegree (I.map f))
    (Q : Ideal (MvPolynomial (Fin n) R)) (j : ℕ) :
    (lexicographicInitialIdealIteration multiDegree J Q j).map f =
      lexicographicInitialIdealIteration multiDegree J' (Q.map f) j := by
  apply lexicographicInitialIdealIteration_map multiDegree J J' f
  · apply DFunLike.ext _ _
    intro P
    exact hJ P
  · exact hinitial

end AbelFormalization
