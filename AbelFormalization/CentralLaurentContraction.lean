import AbelFormalization.WeightedGroupEvaluation
import AbelFormalization.GroupLaurentWeightedIdeal
import AbelFormalization.FiniteLaurentLocalization

/-!
# The actual Laurent contraction in the central-ideal construction

The source variables are the independent q symbols and the remaining
polynomial symbols. The initial ideal uses the
original least lexicographic order. Its actual Laurent extension is rescaled
and contracted to the literal weight-zero polynomial subring. The resulting
ideal has height at least the original ideal. The final Stirling automorphism
is a separate subsequent operation.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

variable {R ι : Type*} [CommRing R] {h : ℕ}

/-- Translation of any family of independent polynomial coordinates,
with its actual opposite translation as inverse. -/
def polynomialCoordinateTranslation {σ : Type*} (c : σ → R) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (c i)))
    (MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (c i)))
    (by ext i; simp)
    (by ext i; simp)

@[simp]
theorem polynomialCoordinateTranslation_X {σ : Type*} (c : σ → R) (i : σ) :
    polynomialCoordinateTranslation c (MvPolynomial.X i) =
      MvPolynomial.X i + MvPolynomial.C (c i) := by
  exact MvPolynomial.aeval_X _ i

@[simp]
theorem polynomialCoordinateTranslation_C {σ : Type*} (c : σ → R) (a : R) :
    polynomialCoordinateTranslation c (MvPolynomial.C a) = MvPolynomial.C a := by
  exact MvPolynomial.aeval_C _ a

/-- The paper's weights: q has negative standard weight. The shear
parameter is the negative of the weight of the retained polynomial symbols. -/
def centralLaurentWeight (ω : ι → Fin h → ℤ) : (Fin h ⊕ ι) → Fin h → ℤ :=
  Sum.elim (fun i => -finiteLaurentExponentHom h (Finsupp.single i 1))
    (fun i => -ω i)

/-- The actual inclusion that inverts q and retains every other symbol. -/
def centralLaurentPolynomialMap (R : Type*) [CommRing R] (ι : Type*) (h : ℕ) :
    MvPolynomial (Fin h ⊕ ι) R →+*
      AddMonoidAlgebra (MvPolynomial ι R) (Fin h → ℤ) :=
  (finiteLaurentPolynomialHom (MvPolynomial ι R) h).comp
    (MvPolynomial.sumAlgEquiv R (Fin h) ι).toRingHom

/-- Perform the actual Laurent rescaling on that actual inclusion. -/
def centralLaurentRescaledMap (ω : ι → Fin h → ℤ) :
    MvPolynomial (Fin h ⊕ ι) R →+*
      AddMonoidAlgebra (MvPolynomial ι R) (Fin h → ℤ) :=
  (groupLaurentWeightRescaling ω).toRingHom.comp
    (centralLaurentPolynomialMap R ι h)

@[simp]
theorem finiteLaurentPolynomialHom_C (A : Type*) [CommRing A] (h : ℕ) (a : A) :
    finiteLaurentPolynomialHom A h (MvPolynomial.C a) =
      AddMonoidAlgebra.single 0 a := by
  simpa only [MvPolynomial.C_apply, map_zero] using
    finiteLaurentPolynomialHom_monomial A h 0 a

/-- On each symbol this composite is precisely evaluation at a group
monomial with degree opposite to the original paper weight. -/
theorem centralLaurentRescaledMap_eq_evaluation (ω : ι → Fin h → ℤ) :
    centralLaurentRescaledMap (R := R) ω =
      weightedGroupEvaluation MvPolynomial.C
        (Sum.elim (fun _ : Fin h => (1 : MvPolynomial ι R)) MvPolynomial.X)
        (fun i => -centralLaurentWeight ω i) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change groupLaurentWeightRescaling ω
      (finiteLaurentPolynomialHom (MvPolynomial ι R) h
        (MvPolynomial.sumAlgEquiv R (Fin h) ι (MvPolynomial.C r))) = _
    rw [MvPolynomial.sumAlgEquiv_C_inl, finiteLaurentPolynomialHom_C,
      weightedGroupEvaluation_C]
    exact groupLaurentWeightRescaling_single_C ω r
  · intro i
    cases i with
    | inl i =>
        change groupLaurentWeightRescaling ω
          (finiteLaurentPolynomialHom (MvPolynomial ι R) h
            (MvPolynomial.sumAlgEquiv R (Fin h) ι (MvPolynomial.X (Sum.inl i)))) = _
        rw [MvPolynomial.sumAlgEquiv_X_inl, finiteLaurentPolynomialHom_X,
          groupLaurentWeightRescaling_single_one, weightedGroupEvaluation_X]
        simp [centralLaurentWeight]
    | inr i =>
        change groupLaurentWeightRescaling ω
          (finiteLaurentPolynomialHom (MvPolynomial ι R) h
            (MvPolynomial.sumAlgEquiv R (Fin h) ι (MvPolynomial.X (Sum.inr i)))) = _
        rw [MvPolynomial.sumAlgEquiv_X_inr, finiteLaurentPolynomialHom_C,
          groupLaurentWeightRescaling_single_X, weightedGroupEvaluation_X]
        simp [centralLaurentWeight]

/-- This homogeneity follows from the actual initial generators; it is
not an input assumption on the original ideal or its Laurent extension. -/
theorem centralLaurent_rescaled_initial_isHomogeneous (ω : ι → Fin h → ℤ)
    (I : Ideal (MvPolynomial (Fin h ⊕ ι) R)) :
    ((lexicographicInitialIdeal (centralLaurentWeight ω) I).map
      (centralLaurentRescaledMap ω)).IsHomogeneous
      (AddMonoidAlgebra.grade (MvPolynomial ι R)) := by
  rw [centralLaurentRescaledMap_eq_evaluation]
  exact weightedGroupEvaluation_neg_lexicographicInitial_isHomogeneous _ _ _ I

/-- The exact contraction along U_i ↦ q^(-ω_i) v_i of the actual localized
initial ideal, before the final Stirling change of polynomial coordinates. -/
def centralLaurentContraction (ω : ι → Fin h → ℤ)
    (I : Ideal (MvPolynomial (Fin h ⊕ ι) R)) : Ideal (MvPolynomial ι R) :=
  groupLaurentRescaledContraction ω
    ((lexicographicInitialIdeal (centralLaurentWeight ω) I).map
      (centralLaurentPolynomialMap R ι h))

theorem centralLaurentContraction_eq (ω : ι → Fin h → ℤ)
    (I : Ideal (MvPolynomial (Fin h ⊕ ι) R)) :
    centralLaurentContraction ω I =
      ((lexicographicInitialIdeal (centralLaurentWeight ω) I).map
        (centralLaurentRescaledMap ω)).comap
          (groupAlgebraC (MvPolynomial ι R) (Fin h → ℤ)) := by
  rw [centralLaurentContraction, groupLaurentRescaledContraction_eq, Ideal.map_map]
  rfl

/-- The actual rescaled ideal is extended from that exact contraction. -/
theorem centralLaurent_initial_eq_map_contraction (ω : ι → Fin h → ℤ)
    (I : Ideal (MvPolynomial (Fin h ⊕ ι) R)) :
    (lexicographicInitialIdeal (centralLaurentWeight ω) I).map
        (centralLaurentRescaledMap ω) =
      (centralLaurentContraction ω I).map
        (groupAlgebraC (MvPolynomial ι R) (Fin h → ℤ)) := by
  classical
  rw [centralLaurentContraction_eq]
  exact groupAlgebra_homogeneousIdeal_eq_map_comap _
    (centralLaurent_rescaled_initial_isHomogeneous ω I)

private theorem central_algEquiv_height_map {A B : Type*}
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (I : Ideal A) :
    (I.map e.toRingHom).height = I.height := e.toRingEquiv.height_map I

/-- The actual polynomial-to-Laurent inclusion cannot lower ideal height.
The localization instance is the proved explicit finite exponent embedding. -/
theorem centralLaurentPolynomialMap_height_le
    (I : Ideal (MvPolynomial (Fin h ⊕ ι) R)) :
    I.height ≤ (I.map (centralLaurentPolynomialMap R ι h)).height := by
  let J := I.map (MvPolynomial.sumAlgEquiv R (Fin h) ι).toRingHom
  have hJ : J.height = I.height := by
    have he := central_algEquiv_height_map (R := R)
      (A := MvPolynomial (Fin h ⊕ ι) R)
      (B := MvPolynomial (Fin h) (MvPolynomial ι R))
      (MvPolynomial.sumAlgEquiv R (Fin h) ι) I
    exact he
  rw [centralLaurentPolynomialMap, ← Ideal.map_map]
  change I.height ≤ (J.map (finiteLaurentPolynomialHom (MvPolynomial ι R) h)).height
  rw [← hJ]
  calc
    J.height ≤ ((J.map (algebraMap (MvPolynomial (Fin h) (MvPolynomial ι R))
        (AddMonoidAlgebra (MvPolynomial ι R) (Fin h → ℤ)))).comap
      (algebraMap (MvPolynomial (Fin h) (MvPolynomial ι R))
        (AddMonoidAlgebra (MvPolynomial ι R) (Fin h → ℤ)))).height :=
      Ideal.height_mono Ideal.le_comap_map
    _ = _ := idealHeight_localization_under
      (laurentVariableSubmonoid (Fin h) (MvPolynomial ι R)) _

/-- The central Laurent contraction has at least the original height,
including unit ideals and coefficient rings with zero divisors. -/
theorem centralLaurentContraction_height_le [IsNoetherianRing R] [Finite ι]
    (ω : ι → Fin h → ℤ) (I : Ideal (MvPolynomial (Fin h ⊕ ι) R)) :
    I.height ≤ (centralLaurentContraction ω I).height := by
  let K := lexicographicInitialIdeal (centralLaurentWeight ω) I
  have he : (K.map (centralLaurentRescaledMap ω)).height =
      (K.map (centralLaurentPolynomialMap R ι h)).height := by
    rw [centralLaurentRescaledMap, ← Ideal.map_map]
    have hm := central_algEquiv_height_map (R := R)
      (A := AddMonoidAlgebra (MvPolynomial ι R) (Fin h → ℤ))
      (B := AddMonoidAlgebra (MvPolynomial ι R) (Fin h → ℤ))
      (groupLaurentWeightRescaling ω) (K.map (centralLaurentPolynomialMap R ι h))
    exact hm
  have hc : (centralLaurentContraction ω I).height =
      (K.map (centralLaurentRescaledMap ω)).height := by
    calc
      (centralLaurentContraction ω I).height =
          ((centralLaurentContraction ω I).map
            (groupAlgebraC (MvPolynomial ι R) (Fin h → ℤ))).height :=
        (multivariateLaurent_height_map_C (MvPolynomial ι R) h _).symm
      _ = _ := congrArg Ideal.height (centralLaurent_initial_eq_map_contraction ω I).symm
  calc
    I.height ≤ K.height := lexicographicInitialIdeal_height _ I
    _ ≤ (K.map (centralLaurentPolynomialMap R ι h)).height :=
      centralLaurentPolynomialMap_height_le K
    _ = (K.map (centralLaurentRescaledMap ω)).height := he.symm
    _ = (centralLaurentContraction ω I).height := hc.symm

/-- Include the literal preliminary substitution x_i ↦ q_i - 1, fixing
all retained symbols, before the actual Laurent contraction. -/
def centralShiftedLaurentContraction (ω : ι → Fin h → ℤ)
    (I : Ideal (MvPolynomial (Fin h ⊕ ι) R)) : Ideal (MvPolynomial ι R) :=
  centralLaurentContraction ω
    (I.map (polynomialCoordinateTranslation
      (Sum.elim (fun _ : Fin h => (-1 : R)) (fun _ : ι => 0))).toRingHom)

theorem centralShiftedLaurentContraction_height_le [IsNoetherianRing R] [Finite ι]
    (ω : ι → Fin h → ℤ) (I : Ideal (MvPolynomial (Fin h ⊕ ι) R)) :
    I.height ≤ (centralShiftedLaurentContraction ω I).height := by
  have ht := central_algEquiv_height_map (R := R)
    (A := MvPolynomial (Fin h ⊕ ι) R) (B := MvPolynomial (Fin h ⊕ ι) R)
    (polynomialCoordinateTranslation
      (Sum.elim (fun _ : Fin h => (-1 : R)) (fun _ : ι => 0))) I
  exact ht.symm.trans_le (centralLaurentContraction_height_le ω _)

end AbelFormalization
