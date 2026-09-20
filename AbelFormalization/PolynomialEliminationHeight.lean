import AbelFormalization.IdealHeight

/-!
# Height under elimination of the auxiliary polynomial variables

The outer literal polynomial variable represents the inverse-minor symbol.
Contracting it and then a finite tuple of auxiliary variables has exactly
the height cost used by the analytic elimination lemma.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

/-- The arbitrary-ideal contraction bound in the literal one-variable
polynomial convention, without a saturation hypothesis. -/
theorem polynomial_height_le_comap_C_add_one (J : Ideal (Polynomial R)) :
    J.height ≤ (J.comap Polynomial.C).height + 1 := by
  let e := MvPolynomial.uniqueAlgEquiv R Unit
  have he : e.toRingHom.comp MvPolynomial.C = Polynomial.C := by
    apply RingHom.ext
    intro r
    exact e.commutes r
  calc
    J.height = (J.comap e.toRingHom).height := (e.toRingEquiv.height_comap J).symm
    _ ≤ ((J.comap e.toRingHom).comap MvPolynomial.C).height + Nat.card Unit :=
      mvPolynomial_height_le_comap_add_card _
    _ = (J.comap Polynomial.C).height + 1 := by
      rw [Ideal.comap_comap, he]
      simp

/-- Contraction eliminates the outer inverse symbol and the chosen finite
tuple of auxiliary polynomial symbols, retaining the entire base ring. -/
def polynomialEliminationContraction (a : ℕ)
    (Q : Ideal (Polynomial (MvPolynomial (Fin a) R))) : Ideal R :=
  (Q.comap Polynomial.C).comap MvPolynomial.C

omit [IsNoetherianRing R] in
@[simp]
theorem polynomialEliminationContraction_mem_iff (a : ℕ)
    (Q : Ideal (Polynomial (MvPolynomial (Fin a) R))) (r : R) :
    r ∈ polynomialEliminationContraction a Q ↔
      Polynomial.C (MvPolynomial.C r) ∈ Q := Iff.rfl

/-- Eliminating the `a` auxiliary symbols and the inverse-minor symbol costs
at most `a+1` in ideal height. -/
theorem polynomial_height_le_eliminationContraction_add (a : ℕ)
    (Q : Ideal (Polynomial (MvPolynomial (Fin a) R))) :
    Q.height ≤ (polynomialEliminationContraction a Q).height + (a + 1 : ℕ) := by
  calc
    Q.height ≤ (Q.comap Polynomial.C).height + 1 :=
      polynomial_height_le_comap_C_add_one Q
    _ ≤ ((Q.comap Polynomial.C).comap MvPolynomial.C).height + a + 1 :=
      add_le_add (mvPolynomial_height_le_comap_add a (Q.comap Polynomial.C)) le_rfl
    _ = (polynomialEliminationContraction a Q).height + (a + 1 : ℕ) := by
      simp only [polynomialEliminationContraction, Nat.cast_add, Nat.cast_one, add_assoc]

/-- A height bound before elimination gives the precise retained height
bound, including when the ideal or its contraction is the unit ideal. -/
theorem polynomialEliminationContraction_height_ge (a r : ℕ)
    (Q : Ideal (Polynomial (MvPolynomial (Fin a) R)))
    (hQ : ((r + a + 1 : ℕ) : ℕ∞) ≤ Q.height) :
    (r : ℕ∞) ≤ (polynomialEliminationContraction a Q).height := by
  apply (ENat.add_le_add_iff_right (show ((a + 1 : ℕ) : ℕ∞) ≠ ⊤ by simp)).mp
  calc
    (r : ℕ∞) + (a + 1 : ℕ) = ((r + a + 1 : ℕ) : ℕ∞) := by
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]
    _ ≤ Q.height := hQ
    _ ≤ (polynomialEliminationContraction a Q).height + (a + 1 : ℕ) :=
      polynomial_height_le_eliminationContraction_add a Q

end AbelFormalization
