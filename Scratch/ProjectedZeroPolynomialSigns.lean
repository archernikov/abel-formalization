import AbelFormalization.ProjectedZeroFamily

/-!
# Polynomial sign sets as projected zero sets

This file formalizes the elementary existential encodings used for the
semialgebraic axiom of the manuscript's projected-zero family.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

@[simp]
theorem realEuclideanDropLastLinearMap_append_one
    {n : ℕ} (x : RealEuclidean n) (z : RealEuclidean 1) :
    realEuclideanDropLastLinearMap n (realEuclideanAppend x z) = x := by
  funext i
  change realEuclideanAppend x z (Fin.castAdd 1 i) = x i
  exact realEuclideanAppend_castAdd x z i

@[simp]
theorem realEuclideanAppend_last_one
    {n : ℕ} (x : RealEuclidean n) (z : RealEuclidean 1) :
    realEuclideanAppend x z (Fin.last n) = z 0 := by
  have hlast : Fin.last n = Fin.natAdd n (0 : Fin 1) := by ext; simp
  rw [hlast]
  exact realEuclideanAppend_natAdd x z (0 : Fin 1)

/-- The equation `P(x) u² - 1 = 0` existentially represents `P(x) > 0`. -/
def polynomialPositiveWitnessEquation {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) : RealEuclideanFunction (n + 1) :=
  fun v ↦
    MvPolynomial.eval (realEuclideanDropLastLinearMap n v) P *
      v (Fin.last n) ^ 2 - 1

@[simp]
theorem polynomialPositiveWitnessEquation_append
    {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : RealEuclidean n) (z : RealEuclidean 1) :
    polynomialPositiveWitnessEquation P (realEuclideanAppend x z) =
      MvPolynomial.eval x P * (z 0) ^ 2 - 1 := by
  simp [polynomialPositiveWitnessEquation]

theorem IsGeometricFunctionFamily.polynomialPositiveWitnessEquation_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    polynomialPositiveWitnessEquation P ∈ G (n + 1) := by
  let L := realEuclideanDropLastLinearMap n
  let p : RealEuclideanFunction (n + 1) :=
    fun v ↦ MvPolynomial.eval (L v) P
  let u : RealEuclideanFunction (n + 1) := fun v ↦ v (Fin.last n)
  have hp : p ∈ G (n + 1) := by
    exact hG.affine_comp (hG.polynomial P) L.toAffineMap
  have hu : u ∈ G (n + 1) := by
    simpa [u] using hG.polynomial (MvPolynomial.X (Fin.last n))
  have hmem := hG.sub_mem (hG.mul hp (hG.sq_mem hu)) hG.one_mem
  change (fun v ↦ p v * u v ^ 2 - 1) ∈ G (n + 1)
  rw [show (fun v ↦ p v * u v ^ 2 - 1) =
      p * (fun v ↦ u v ^ 2) - 1 by
    funext v
    rfl]
  exact hmem

theorem isProjectedZeroSet_polynomial_zero
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    IsProjectedZeroSet G {x | MvPolynomial.eval x P = 0} :=
  isProjectedZeroSet_zeroSet (hG.polynomial P)

theorem isProjectedZeroSet_polynomial_pos
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    IsProjectedZeroSet G {x | 0 < MvPolynomial.eval x P} := by
  refine ⟨1, polynomialPositiveWitnessEquation P,
    hG.polynomialPositiveWitnessEquation_mem P, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hp
    let u : ℝ := (Real.sqrt (MvPolynomial.eval x P))⁻¹
    refine ⟨fun _ ↦ u, ?_⟩
    rw [polynomialPositiveWitnessEquation_append]
    rw [← Real.sq_sqrt hp.le]
    dsimp only [u]
    field_simp
    norm_num
  · rintro ⟨z, hz⟩
    rw [polynomialPositiveWitnessEquation_append, sub_eq_zero] at hz
    have hu : z 0 ≠ 0 := by
      intro hu
      simp [hu] at hz
    have hu2 : 0 < (z 0) ^ 2 := sq_pos_of_ne_zero hu
    have hprod : 0 < MvPolynomial.eval x P * (z 0) ^ 2 := by
      rw [hz]
      norm_num
    rcases mul_pos_iff.mp hprod with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hu2.le hneg.2).elim

theorem isProjectedZeroSet_polynomial_neg
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) :
    IsProjectedZeroSet G {x | MvPolynomial.eval x P < 0} := by
  have h := isProjectedZeroSet_polynomial_pos hG (-P)
  simpa using h

/-- Finite unions and intersections of polynomial zero/positive/negative sign
conditions. This is the disjunctive-normal-form presentation of real
semialgebraic sets used in the manuscript's elementary encoding. -/
inductive PolynomialSignConstructible (n : ℕ) :
    Set (RealEuclidean n) → Prop
  | zero (P : MvPolynomial (Fin n) ℝ) :
      PolynomialSignConstructible n {x | MvPolynomial.eval x P = 0}
  | pos (P : MvPolynomial (Fin n) ℝ) :
      PolynomialSignConstructible n {x | 0 < MvPolynomial.eval x P}
  | neg (P : MvPolynomial (Fin n) ℝ) :
      PolynomialSignConstructible n {x | MvPolynomial.eval x P < 0}
  | inter {s t} : PolynomialSignConstructible n s →
      PolynomialSignConstructible n t →
        PolynomialSignConstructible n (s ∩ t)
  | union {s t} : PolynomialSignConstructible n s →
      PolynomialSignConstructible n t →
        PolynomialSignConstructible n (s ∪ t)

theorem polynomialSignConstructible_empty (n : ℕ) :
    PolynomialSignConstructible n (∅ : Set (RealEuclidean n)) := by
  have h := PolynomialSignConstructible.zero
    (n := n) (1 : MvPolynomial (Fin n) ℝ)
  simpa using h

theorem polynomialSignConstructible_univ (n : ℕ) :
    PolynomialSignConstructible n (Set.univ : Set (RealEuclidean n)) := by
  have h := PolynomialSignConstructible.zero
    (n := n) (0 : MvPolynomial (Fin n) ℝ)
  simpa using h

/-- Polynomial sign normal forms are closed under complement by trichotomy of
real polynomial values and De Morgan's laws. -/
theorem PolynomialSignConstructible.compl
    {n : ℕ} {s : Set (RealEuclidean n)}
    (hs : PolynomialSignConstructible n s) :
    PolynomialSignConstructible n sᶜ := by
  induction hs with
  | zero P =>
      rw [show {x | MvPolynomial.eval x P = 0}ᶜ =
          {x | 0 < MvPolynomial.eval x P} ∪
            {x | MvPolynomial.eval x P < 0} by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · intro hne
          rcases lt_or_gt_of_ne hne with hneg | hpos
          · exact Or.inr hneg
          · exact Or.inl hpos
        · rintro (hpos | hneg)
          · exact ne_of_gt hpos
          · exact ne_of_lt hneg]
      exact .union (.pos P) (.neg P)
  | pos P =>
      rw [show {x | 0 < MvPolynomial.eval x P}ᶜ =
          {x | MvPolynomial.eval x P = 0} ∪
            {x | MvPolynomial.eval x P < 0} by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · intro hnpos
          rcases eq_or_lt_of_le (not_lt.mp hnpos) with hzero | hneg
          · exact Or.inl hzero
          · exact Or.inr hneg
        · rintro (hzero | hneg)
          · simp [hzero]
          · exact not_lt_of_ge hneg.le]
      exact .union (.zero P) (.neg P)
  | neg P =>
      rw [show {x | MvPolynomial.eval x P < 0}ᶜ =
          {x | MvPolynomial.eval x P = 0} ∪
            {x | 0 < MvPolynomial.eval x P} by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
        constructor
        · intro hnneg
          rcases eq_or_lt_of_le (not_lt.mp hnneg) with hzero | hpos
          · exact Or.inl hzero.symm
          · exact Or.inr hpos
        · rintro (hzero | hpos)
          · simp [hzero]
          · exact not_lt_of_ge hpos.le]
      exact .union (.zero P) (.pos P)
  | inter hs ht ihs iht =>
      rw [compl_inter]
      exact .union ihs iht
  | union hs ht ihs iht =>
      rw [compl_union]
      exact .inter ihs iht

theorem PolynomialSignConstructible.isProjectedZeroSet
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    {s : Set (RealEuclidean n)} (hs : PolynomialSignConstructible n s) :
    IsProjectedZeroSet G s := by
  induction hs with
  | zero P => exact isProjectedZeroSet_polynomial_zero hG P
  | pos P => exact isProjectedZeroSet_polynomial_pos hG P
  | neg P => exact isProjectedZeroSet_polynomial_neg hG P
  | inter _ _ ihs iht => exact ihs.inter hG iht
  | union _ _ ihs iht => exact ihs.union hG iht

end AbelFormalization
