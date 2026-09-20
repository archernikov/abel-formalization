import AbelFormalization.CentralLaurentLocalization

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-!
# Height under ordinary homogeneous dehomogenization

An ordinary homogeneous ideal in `B[H, t]` is localized at `H` and the
remaining variables are rescaled by `H`.  The resulting Laurent ideal is
homogeneous, hence extended from its degree-zero coefficient contraction.
Evaluation of every Laurent monomial at one identifies that contraction with
the original ideal specialized at `H = 1`.
-/

noncomputable section

namespace AbelFormalization

variable {B ι : Type*} [CommRing B]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- Keep the semiring structure used by ideals coherent with the reduct of
the canonical commutative-ring structure on the Laurent target. -/
local instance (priority := 2000) ordinaryLaurentSemiring
    (B ι : Type*) [CommRing B] :
    Semiring (AddMonoidAlgebra (MvPolynomial ι B) (Fin 1 → ℤ)) :=
  (inferInstance : CommRing
    (AddMonoidAlgebra (MvPolynomial ι B) (Fin 1 → ℤ))).toSemiring

private theorem ordinary_algEquiv_height_map
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (e : A ≃ₐ[R] A) (I : Ideal A) :
    (I.map e.toRingHom).height = I.height :=
  e.toRingEquiv.height_map I

/-- Set the distinguished variable to one and retain all other variables. -/
def ordinaryDehomogenizationHom :
    MvPolynomial (Fin 1 ⊕ ι) B →+* MvPolynomial ι B :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun _ : Fin 1 ↦ 1) MvPolynomial.X)

@[simp]
theorem ordinaryDehomogenizationHom_C (b : B) :
    ordinaryDehomogenizationHom (ι := ι) (MvPolynomial.C b) =
      MvPolynomial.C b := by
  simp [ordinaryDehomogenizationHom]

@[simp]
theorem ordinaryDehomogenizationHom_X_left (j : Fin 1) :
    ordinaryDehomogenizationHom (B := B) (ι := ι)
      (MvPolynomial.X (Sum.inl j)) = 1 := by
  simp [ordinaryDehomogenizationHom]

@[simp]
theorem ordinaryDehomogenizationHom_X_right (i : ι) :
    ordinaryDehomogenizationHom (B := B) (ι := ι)
      (MvPolynomial.X (Sum.inr i)) = MvPolynomial.X i := by
  simp [ordinaryDehomogenizationHom]

/-- The constant ordinary rescaling weight on retained variables. -/
def ordinaryLaurentRescalingWeight : ι → Fin 1 → ℤ :=
  fun _ _ ↦ 1

/-- Every source variable receives Laurent degree one. -/
def ordinaryLaurentTotalWeight : (Fin 1 ⊕ ι) → Fin 1 → ℤ :=
  fun _ _ ↦ 1

theorem centralLaurentWeight_one_neg :
    (fun i ↦ -centralLaurentWeight
      (ordinaryLaurentRescalingWeight (ι := ι)) i) =
        ordinaryLaurentTotalWeight (ι := ι) := by
  funext i j
  rcases i with i | i
  · have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [centralLaurentWeight, ordinaryLaurentTotalWeight,
      finiteLaurentExponentHom_apply]
  · simp [centralLaurentWeight, ordinaryLaurentRescalingWeight,
      ordinaryLaurentTotalWeight]

/-- Evaluate every group monomial at one. -/
def finiteLaurentEvalOne (A : Type*) [CommRing A] (h : ℕ) :
    AddMonoidAlgebra A (Fin h → ℤ) →+* A :=
  (AddMonoidAlgebra.lift A A (Fin h → ℤ)
    (1 : Multiplicative (Fin h → ℤ) →* A)).toRingHom

@[simp]
theorem finiteLaurentEvalOne_single
    (A : Type*) [CommRing A] (h : ℕ) (g : Fin h → ℤ) (a : A) :
    finiteLaurentEvalOne A h (AddMonoidAlgebra.single g a) = a := by
  simp [finiteLaurentEvalOne]

theorem finiteLaurentEvalOne_comp_C
    (A : Type*) [CommRing A] (h : ℕ) :
    (finiteLaurentEvalOne A h).comp (groupAlgebraC A (Fin h → ℤ)) =
      RingHom.id A := by
  ext a
  simp [groupAlgebraC_apply]

/-- Evaluation of the rescaled localization at Laurent degree one is
exactly ordinary dehomogenization. -/
theorem finiteLaurentEvalOne_comp_ordinaryRescaledMap :
    (finiteLaurentEvalOne (MvPolynomial ι B) 1).comp
      (centralLaurentRescaledMap
        (ordinaryLaurentRescalingWeight (ι := ι))) =
      ordinaryDehomogenizationHom (B := B) (ι := ι) := by
  rw [centralLaurentRescaledMap_eq_evaluation,
    centralLaurentWeight_one_neg]
  apply MvPolynomial.ringHom_ext
  · intro b
    simp
  · rintro (j | i)
    · simp
    · simp

/-- Scalar total-degree homogeneity implies homogeneity for the equivalent
one-coordinate vector grading. -/
theorem isWeightedHomogeneous_ordinaryLaurentTotalWeight
    {f : MvPolynomial (Fin 1 ⊕ ι) B} {n : ℕ}
    (hf : f.IsWeightedHomogeneous (fun _ ↦ (1 : ℕ)) n) :
    f.IsWeightedHomogeneous (ordinaryLaurentTotalWeight (ι := ι))
      (fun _ ↦ (n : ℤ)) := by
  intro d hd
  funext j
  have hn := congrArg (fun m : ℕ ↦ (m : ℤ)) (hf hd)
  simpa [Finsupp.weight_apply, Finsupp.sum,
    ordinaryLaurentTotalWeight] using hn

/-- Localizing the distinguished variable and rescaling the retained
variables turns an ordinary homogeneous ideal into a homogeneous Laurent
ideal. -/
theorem ordinaryRescaledMap_isHomogeneous
    (C : Ideal (MvPolynomial (Fin 1 ⊕ ι) B))
    (hC : C.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun _ ↦ (1 : ℕ)))) :
    (C.map (centralLaurentRescaledMap
      (ordinaryLaurentRescalingWeight (ι := ι)))).IsHomogeneous
        (AddMonoidAlgebra.grade (MvPolynomial ι B)) := by
  classical
  obtain ⟨S, hS⟩ :=
    (Ideal.IsHomogeneous.iff_exists
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun _ : Fin 1 ⊕ ι ↦ (1 : ℕ))) C).mp hC
  rw [centralLaurentRescaledMap_eq_evaluation,
    centralLaurentWeight_one_neg, hS]
  apply weightedGroupEvaluation_span_isHomogeneous
  rintro f ⟨g, _, rfl⟩
  obtain ⟨n, hn⟩ := g.property
  exact ⟨fun _ ↦ (n : ℤ),
    isWeightedHomogeneous_ordinaryLaurentTotalWeight hn⟩

/-- The degree-zero coefficient contraction of the rescaled Laurent ideal is
literally the ideal obtained by setting `H = 1`. -/
theorem ordinaryRescaledMap_comap_C_eq_dehomogenization
    (C : Ideal (MvPolynomial (Fin 1 ⊕ ι) B))
    (hC : C.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun _ ↦ (1 : ℕ)))) :
    (C.map (centralLaurentRescaledMap
      (ordinaryLaurentRescalingWeight (ι := ι)))).comap
        (groupAlgebraC (MvPolynomial ι B) (Fin 1 → ℤ)) =
      C.map (ordinaryDehomogenizationHom (B := B) (ι := ι)) := by
  let K := C.map (centralLaurentRescaledMap
    (ordinaryLaurentRescalingWeight (ι := ι)))
  let D := K.comap (groupAlgebraC (MvPolynomial ι B) (Fin 1 → ℤ))
  have hK : K.IsHomogeneous
      (AddMonoidAlgebra.grade (MvPolynomial ι B)) :=
    ordinaryRescaledMap_isHomogeneous C hC
  have hKC : K = D.map
      (groupAlgebraC (MvPolynomial ι B) (Fin 1 → ℤ)) :=
    groupAlgebra_homogeneousIdeal_eq_map_comap K hK
  change D = C.map (ordinaryDehomogenizationHom (B := B) (ι := ι))
  calc
    D = (D.map (groupAlgebraC (MvPolynomial ι B) (Fin 1 → ℤ))).map
        (finiteLaurentEvalOne (MvPolynomial ι B) 1) := by
      rw [Ideal.map_map, finiteLaurentEvalOne_comp_C]
      simp
    _ = K.map (finiteLaurentEvalOne (MvPolynomial ι B) 1) := by rw [← hKC]
    _ = C.map (ordinaryDehomogenizationHom (B := B) (ι := ι)) := by
      rw [Ideal.map_map, finiteLaurentEvalOne_comp_ordinaryRescaledMap]

/-- Ordinary homogeneous dehomogenization at `H = 1` cannot lower ideal
height.  No saturation assumption is needed. -/
theorem ordinaryHomogeneous_height_le_dehomogenization
    [IsNoetherianRing B] [Finite ι]
    (C : Ideal (MvPolynomial (Fin 1 ⊕ ι) B))
    (hC : C.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun _ ↦ (1 : ℕ)))) :
    C.height ≤
      (C.map (ordinaryDehomogenizationHom (B := B) (ι := ι))).height := by
  let K := C.map (centralLaurentRescaledMap
    (ordinaryLaurentRescalingWeight (ι := ι)))
  let D := K.comap (groupAlgebraC (MvPolynomial ι B) (Fin 1 → ℤ))
  have hK : K.IsHomogeneous
      (AddMonoidAlgebra.grade (MvPolynomial ι B)) :=
    ordinaryRescaledMap_isHomogeneous C hC
  have hrescale :
      (C.map (centralLaurentPolynomialMap B ι 1)).height = K.height := by
    dsimp [K]
    rw [centralLaurentRescaledMap, ← Ideal.map_map]
    exact (ordinary_algEquiv_height_map
      (R := B)
      (groupLaurentWeightRescaling
        (ordinaryLaurentRescalingWeight (ι := ι)))
      (C.map (centralLaurentPolynomialMap B ι 1))).symm
  calc
    C.height ≤ (C.map (centralLaurentPolynomialMap B ι 1)).height :=
      centralLaurentPolynomialMap_height_le C
    _ = K.height := hrescale
    _ = D.height :=
      multivariateLaurent_homogeneousIdeal_height
        (R := MvPolynomial ι B) 1 K hK
    _ = (C.map (ordinaryDehomogenizationHom (B := B) (ι := ι))).height := by
      dsimp [D, K]
      exact congrArg Ideal.height
        (ordinaryRescaledMap_comap_C_eq_dehomogenization C hC)

/-- After dehomogenization, regroup the time variables over the retained
coefficient ring and contract them away. -/
def ordinaryDehomogenizedTimeContraction
    (Time Keep : Type*)
    (C : Ideal (MvPolynomial (Fin 1 ⊕ (Time ⊕ Keep)) B)) :
    Ideal (MvPolynomial Keep B) :=
  (((C.map
      (ordinaryDehomogenizationHom (B := B) (ι := Time ⊕ Keep))).map
        (MvPolynomial.sumAlgEquiv B Time Keep).toRingHom).comap
          (MvPolynomial.C :
            MvPolynomial Keep B →+* MvPolynomial Time (MvPolynomial Keep B)))

/-- Setting `H = 1` and then contracting the time variables loses at most
their cardinality in height.  This is the combined height estimate used in
the cluster-contraction step of the manuscript. -/
theorem ordinaryHomogeneous_height_sub_card_le_timeContraction
    {Time Keep : Type*}
    [IsNoetherianRing B] [Finite Time] [Finite Keep]
    (C : Ideal (MvPolynomial (Fin 1 ⊕ (Time ⊕ Keep)) B))
    (hC : C.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun _ ↦ (1 : ℕ)))) :
    C.height - Nat.card Time ≤
      (ordinaryDehomogenizedTimeContraction Time Keep C).height := by
  let J := C.map
    (ordinaryDehomogenizationHom (B := B) (ι := Time ⊕ Keep))
  let J' := J.map (MvPolynomial.sumAlgEquiv B Time Keep).toRingHom
  have hdehom : C.height ≤ J.height :=
    ordinaryHomogeneous_height_le_dehomogenization C hC
  have hgroup : J'.height = J.height :=
    (MvPolynomial.sumAlgEquiv B Time Keep).toRingEquiv.height_map J
  have hcontract : J'.height - Nat.card Time ≤
      (J'.comap (MvPolynomial.C :
        MvPolynomial Keep B →+* MvPolynomial Time (MvPolynomial Keep B))).height :=
    mvPolynomial_height_sub_card_le_comap J'
  calc
    C.height - Nat.card Time ≤ J.height - Nat.card Time :=
      tsub_le_tsub_right hdehom _
    _ = J'.height - Nat.card Time := by rw [hgroup]
    _ ≤ (ordinaryDehomogenizedTimeContraction Time Keep C).height := by
      exact hcontract

/-- The finite-indexed form gives the exact numerical loss appearing in the
paper. -/
theorem ordinaryHomogeneous_height_sub_fin_le_timeContraction
    {Keep : Type*}
    [IsNoetherianRing B] [Finite Keep]
    (h : ℕ)
    (C : Ideal (MvPolynomial (Fin 1 ⊕ (Fin h ⊕ Keep)) B))
    (hC : C.IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule B
        (fun _ ↦ (1 : ℕ)))) :
    C.height - h ≤
      (ordinaryDehomogenizedTimeContraction (Fin h) Keep C).height := by
  simpa using
    (ordinaryHomogeneous_height_sub_card_le_timeContraction C hC)

end AbelFormalization
