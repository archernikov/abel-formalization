import AbelFormalization.AugmentedJacobianHeight
import AbelFormalization.PolynomialEliminationLayout

/-!
# The actual retained ideal in Jacobian elimination

The inverse relation and all original equations are ordinary polynomials in
one flat symbol type. The ideal is contracted to the exact retained ring,
and the height bound follows from the augmented determinant argument and
the proved finite-variable contraction bound.
-/

noncomputable section

set_option autoImplicit false

namespace AbelFormalization

variable {B ι γ : Type*} [CommRing B]
variable {n : ℕ}

/-- A flat polynomial tuple with the inverse relation first. -/
def mvPolynomialUnitAugmentedTuple
    (f : Fin n → MvPolynomial ι B) (d : MvPolynomial ι B) :
    Fin (n + 1) → MvPolynomial (Option ι) B :=
  Fin.cons (α := fun _ : Fin (n + 1) => MvPolynomial (Option ι) B)
    (MvPolynomial.X none * MvPolynomial.rename some d - 1)
    (fun i => MvPolynomial.rename some (f i))

def mvPolynomialUnitAugmentedIdeal
    (f : Fin n → MvPolynomial ι B) (d : MvPolynomial ι B) :
    Ideal (MvPolynomial (Option ι) B) :=
  Ideal.span (Set.range (mvPolynomialUnitAugmentedTuple f d))

@[simp]
theorem optionEquivLeft_rename_some (P : MvPolynomial ι B) :
    MvPolynomial.optionEquivLeft B ι (MvPolynomial.rename some P) = Polynomial.C P := by
  have h : (MvPolynomial.optionEquivLeft B ι).toRingHom.comp
      (MvPolynomial.rename (R := B) (fun i : ι => some i)).toRingHom = Polynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp
    · intro i
      simp
  exact RingHom.congr_fun h P

theorem optionEquivLeft_mvPolynomialUnitAugmentedTuple
    (f : Fin n → MvPolynomial ι B) (d : MvPolynomial ι B)
    (i : Fin (n + 1)) :
    MvPolynomial.optionEquivLeft B ι (mvPolynomialUnitAugmentedTuple f d i) =
      polynomialUnitAugmentedTuple f d i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [mvPolynomialUnitAugmentedTuple, polynomialUnitAugmentedTuple]
  · simp [mvPolynomialUnitAugmentedTuple, polynomialUnitAugmentedTuple]

/-- The explicit flat generators map to precisely the literal augmented
polynomial ideal, with no localization or additional equation. -/
theorem mvPolynomialUnitAugmentedIdeal_map_optionEquivLeft
    (f : Fin n → MvPolynomial ι B) (d : MvPolynomial ι B) :
    (mvPolynomialUnitAugmentedIdeal f d).map
      (MvPolynomial.optionEquivLeft B ι).toRingHom =
        polynomialUnitAugmentedIdeal f d := by
  unfold mvPolynomialUnitAugmentedIdeal polynomialUnitAugmentedIdeal
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact optionEquivLeft_mvPolynomialUnitAugmentedTuple f d i

/-- An actual inverse assignment annihilates every explicit augmented
generator. This works over any commutative coefficient ring. -/
theorem mvPolynomialUnitAugmentedTuple_eval_zero
    (f : Fin n → MvPolynomial ι B) (d : MvPolynomial ι B)
    (x : ι → B) (z : B) (hf : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hd : z * MvPolynomial.eval x d = 1) (i : Fin (n + 1)) :
    MvPolynomial.eval (fun o : Option ι => o.elim z x)
      (mvPolynomialUnitAugmentedTuple f d i) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [mvPolynomialUnitAugmentedTuple, MvPolynomial.eval_rename, Function.comp_def, hd]
  · simp [mvPolynomialUnitAugmentedTuple, MvPolynomial.eval_rename, Function.comp_def, hf]

/-- The entire augmented ideal vanishes under an actual inverse assignment,
because the evaluation kernel contains all its generators. -/
theorem mvPolynomialUnitAugmentedIdeal_le_ker_eval
    (f : Fin n → MvPolynomial ι B) (d : MvPolynomial ι B)
    (x : ι → B) (z : B) (hf : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hd : z * MvPolynomial.eval x d = 1) :
    mvPolynomialUnitAugmentedIdeal f d ≤
      RingHom.ker (MvPolynomial.eval (fun o : Option ι => o.elim z x)) := by
  apply Ideal.span_le.mpr
  rintro P ⟨i, rfl⟩
  exact mvPolynomialUnitAugmentedTuple_eval_zero f d x z hf hd i

variable {K : Type*} [Field K] [CharZero K] [Algebra K B]

private theorem flatJacobian_height_map_of_bijective {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Bijective f)
    (I : Ideal R) :
    (I.map f).height = I.height := (RingEquiv.ofBijective f hf).height_map I

/-- The actual flat ideal has the required augmented Jacobian height. -/
theorem mvPolynomialUnitAugmentedIdeal_height [Fintype γ]
    (f : Fin n → MvPolynomial ι B)
    (D : γ → Derivation K (MvPolynomial ι B) (MvPolynomial ι B)) :
    ((n + 1 : ℕ) : ℕ∞) ≤
      (mvPolynomialUnitAugmentedIdeal f (derivationJacobianDenominator f D)).height := by
  have h := polynomialUnitAugmentedIdeal_height f D
  rw [← mvPolynomialUnitAugmentedIdeal_map_optionEquivLeft] at h
  rwa [flatJacobian_height_map_of_bijective
    (R := MvPolynomial (Option ι) B) (S := Polynomial (MvPolynomial ι B))
    (MvPolynomial.optionEquivLeft B ι).toRingHom
    (MvPolynomial.optionEquivLeft B ι).bijective] at h

variable {Keep : Type*} [Finite Keep] [IsNoetherianRing B]

/-- The retained ideal obtained by eliminating the auxiliary symbols and
the inverse-minor symbol from the actual augmented Jacobian ideal. -/
def jacobianEliminationIdeal [Fintype γ] (a : ℕ)
    (f : Fin n → MvPolynomial (Fin a ⊕ Keep) B)
    (D : γ → Derivation K (MvPolynomial (Fin a ⊕ Keep) B)
      (MvPolynomial (Fin a ⊕ Keep) B)) : Ideal (MvPolynomial Keep B) :=
  (mvPolynomialUnitAugmentedIdeal f (derivationJacobianDenominator f D)).comap
    (polynomialEliminationRetainedFlat B Keep (Fin a))

/-- For `r+a` equations, contraction retains height at least `r`. This is
the complete algebraic height step of elimination at regular zeros. -/
theorem jacobianEliminationIdeal_height [Fintype γ] (a r : ℕ)
    (f : Fin (r + a) → MvPolynomial (Fin a ⊕ Keep) B)
    (D : γ → Derivation K (MvPolynomial (Fin a ⊕ Keep) B)
      (MvPolynomial (Fin a ⊕ Keep) B)) :
    (r : ℕ∞) ≤ (jacobianEliminationIdeal a f D).height := by
  apply polynomialEliminationLayout_retained_height_ge a r
  exact mvPolynomialUnitAugmentedIdeal_height f D

end AbelFormalization
