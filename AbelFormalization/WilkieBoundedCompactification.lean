import AbelFormalization.CharbonnelWeakStructure
import AbelFormalization.CharbonnelLinearEquivClosure
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Wilkie's bounded-coordinate compactification

Section 4 of Wilkie's proof is carried out in the bounded cube.  The scalar
map is `t ↦ t / √(1 + t²)`, applied coordinatewise.  This file records its
semialgebraic graph without assuming complement closure, and proves that
images and inverse images under the coordinatewise map remain in the
Charbonnel closure using only WS1--WS4 and existential projection.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Wilkie's scalar homeomorphism from `ℝ` to `(-1,1)`. -/
def wilkieBoundedCoordinate (t : ℝ) : ℝ :=
  (Real.sqrt (1 + t ^ 2))⁻¹ * t

/-- Coordinatewise bounded-coordinate map. -/
def wilkieBoundedMap (n : ℕ) (x : RealEuclidean n) : RealEuclidean n :=
  fun i ↦ wilkieBoundedCoordinate (x i)

/-- The open coordinate cube used in Wilkie's Section 4. -/
def wilkieOpenCube (n : ℕ) : Set (RealEuclidean n) :=
  {x | ∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1}

theorem wilkieBoundedCoordinate_sq_relation (t : ℝ) :
    wilkieBoundedCoordinate t ^ 2 * (1 + t ^ 2) = t ^ 2 := by
  have hd : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hdsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [wilkieBoundedCoordinate, inv_mul_eq_div, div_pow]
  field_simp
  nlinarith

theorem wilkieBoundedCoordinate_mul_nonneg (t : ℝ) :
    0 ≤ t * wilkieBoundedCoordinate t := by
  rw [wilkieBoundedCoordinate]
  have hinv : 0 ≤ (Real.sqrt (1 + t ^ 2))⁻¹ := by positivity
  nlinarith [sq_nonneg t]

/-- The polynomial equation and sign condition characterize Wilkie's scalar
bounded-coordinate map. -/
theorem wilkieBoundedCoordinate_eq_iff {t u : ℝ} :
    u = wilkieBoundedCoordinate t ↔
      u ^ 2 * (1 + t ^ 2) = t ^ 2 ∧ 0 ≤ t * u := by
  constructor
  · rintro rfl
    exact ⟨wilkieBoundedCoordinate_sq_relation t,
      wilkieBoundedCoordinate_mul_nonneg t⟩
  · rintro ⟨hsq, hsign⟩
    let d := Real.sqrt (1 + t ^ 2)
    have hd : 0 < d := Real.sqrt_pos.2 (by positivity)
    have hdsq : d ^ 2 = 1 + t ^ 2 := by
      dsimp [d]
      exact Real.sq_sqrt (by positivity)
    have hsquares : (u * d) ^ 2 = t ^ 2 := by
      rw [mul_pow, hdsq]
      exact hsq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with hpos | hneg
    · rw [wilkieBoundedCoordinate]
      have hdEq : Real.sqrt (1 + t ^ 2) = d := rfl
      rw [hdEq, ← div_eq_inv_mul]
      exact (eq_div_iff hd.ne').2 hpos
    · have hu : u = 0 := by
        rcases lt_trichotomy u 0 with huNeg | huZero | huPos
        · have hud : u * d < 0 := mul_neg_of_neg_of_pos huNeg hd
          have htPos : 0 < t := by linarith [hneg, hud]
          exact (not_le_of_gt (mul_neg_of_pos_of_neg htPos huNeg) hsign).elim
        · exact huZero
        · have hud : 0 < u * d := mul_pos huPos hd
          have htNeg : t < 0 := by linarith [hneg, hud]
          exact (not_le_of_gt (mul_neg_of_neg_of_pos htNeg huPos) hsign).elim
      have ht : t = 0 := by simpa [hu] using hneg
      simp [hu, ht, wilkieBoundedCoordinate]

theorem wilkieBoundedCoordinate_mem_Ioo (t : ℝ) :
    wilkieBoundedCoordinate t ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hd : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
  have habs : |t| < Real.sqrt (1 + t ^ 2) := by
    rw [Real.lt_sqrt (abs_nonneg t)]
    nlinarith [sq_abs t]
  have hb := (abs_lt.mp habs)
  constructor
  · rw [wilkieBoundedCoordinate, inv_mul_eq_div]
    exact (lt_div_iff₀ hd).2 (by linarith [hb.1])
  · rw [wilkieBoundedCoordinate, inv_mul_eq_div]
    exact (div_lt_one hd).2 (by linarith [hb.2])

theorem wilkieBoundedMap_mem_openCube (n : ℕ) (x : RealEuclidean n) :
    wilkieBoundedMap n x ∈ wilkieOpenCube n := by
  intro i
  exact wilkieBoundedCoordinate_mem_Ioo (x i)

def wilkieBoundedImage {n : ℕ} (A : Set (RealEuclidean n)) :
    Set (RealEuclidean n) :=
  wilkieBoundedMap n '' A

/-! ## The coordinatewise homeomorphism -/

/-- The scalar map as a homeomorphism onto `(-1,1)`. -/
theorem wilkieUnitBall_eq_Ioo :
    Metric.ball (0 : ℝ) 1 = Set.Ioo (-1 : ℝ) 1 := by
  simpa using (Real.ball_zero_eq_Ioo (1 : ℝ))

def wilkieBoundedCoordinateHomeomorph :
    ℝ ≃ₜ {u : ℝ // u ∈ Set.Ioo (-1 : ℝ) 1} :=
  (Homeomorph.unitBall (E := ℝ)).trans
    (Homeomorph.setCongr wilkieUnitBall_eq_Ioo)

@[simp]
theorem wilkieBoundedCoordinateHomeomorph_coe_apply (t : ℝ) :
    ((wilkieBoundedCoordinateHomeomorph t :
      {u : ℝ // u ∈ Set.Ioo (-1 : ℝ) 1}) : ℝ) =
        wilkieBoundedCoordinate t := by
  rw [wilkieBoundedCoordinateHomeomorph, Homeomorph.trans_apply]
  change ((Set.equivOfEq wilkieUnitBall_eq_Ioo)
    (Homeomorph.unitBall (E := ℝ) t)).1 = _
  have heq := Set.equivOfEq_apply wilkieUnitBall_eq_Ioo
    (Homeomorph.unitBall (E := ℝ) t)
  have hval := congrArg Subtype.val heq
  rw [hval, Homeomorph.unitBall_apply_coe,
    OpenPartialHomeomorph.univUnitBall_apply]
  simp [wilkieBoundedCoordinate, Real.norm_eq_abs, sq_abs, smul_eq_mul]

/-- Pointwise subtype packaging identifies a product of scalar intervals
with the subtype of the coordinate cube. -/
def wilkiePiIooHomeomorph (n : ℕ) :
    ((i : Fin n) → {u : ℝ // u ∈ Set.Ioo (-1 : ℝ) 1}) ≃ₜ
      (wilkieOpenCube n) where
  toFun u := ⟨fun i ↦ u i, fun i ↦ (u i).property⟩
  invFun x i := ⟨x.1 i, x.2 i⟩
  left_inv u := by
    funext i
    exact Subtype.ext rfl
  right_inv x := by
    exact Subtype.ext (by rfl)
  continuous_toFun :=
    (continuous_pi fun i ↦
      continuous_subtype_val.comp (continuous_apply i)).subtype_mk _
  continuous_invFun := by
    exact continuous_pi fun i ↦
      ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

/-- Wilkie's coordinatewise homeomorphism from `ℝⁿ` to the bounded cube. -/
def wilkieBoundedHomeomorph (n : ℕ) :
    RealEuclidean n ≃ₜ (wilkieOpenCube n) :=
  (Homeomorph.piCongrRight
    (fun _ : Fin n ↦ wilkieBoundedCoordinateHomeomorph)).trans
      (wilkiePiIooHomeomorph n)

@[simp]
theorem wilkieBoundedHomeomorph_coe_apply
    (n : ℕ) (x : RealEuclidean n) :
    ((wilkieBoundedHomeomorph n x : wilkieOpenCube n) :
      RealEuclidean n) = wilkieBoundedMap n x := by
  funext i
  simp [wilkieBoundedHomeomorph, wilkiePiIooHomeomorph,
    wilkieBoundedMap]

theorem wilkieBoundedMap_injective (n : ℕ) :
    Function.Injective (wilkieBoundedMap n) := by
  intro x y hxy
  apply (wilkieBoundedHomeomorph n).injective
  apply Subtype.ext
  simpa only [wilkieBoundedHomeomorph_coe_apply] using hxy

theorem wilkieBoundedMap_surjOn_openCube (n : ℕ) :
    Set.SurjOn (wilkieBoundedMap n) Set.univ (wilkieOpenCube n) := by
  intro u hu
  let us : wilkieOpenCube n := ⟨u, hu⟩
  refine ⟨(wilkieBoundedHomeomorph n).symm us, Set.mem_univ _, ?_⟩
  have happly := congrArg Subtype.val
    ((wilkieBoundedHomeomorph n).apply_symm_apply us)
  simpa only [wilkieBoundedHomeomorph_coe_apply] using happly

theorem continuous_wilkieBoundedMap (n : ℕ) :
    Continuous (wilkieBoundedMap n) := by
  have h := continuous_subtype_val.comp (wilkieBoundedHomeomorph n).continuous
  change Continuous
    (fun x ↦ ((wilkieBoundedHomeomorph n x : wilkieOpenCube n) :
      RealEuclidean n)) at h
  simpa only [wilkieBoundedHomeomorph_coe_apply] using h

theorem isClosed_preimage_val_wilkieBoundedImage
    {n : ℕ} {A : Set (RealEuclidean n)} (hA : IsClosed A) :
    IsClosed (Subtype.val ⁻¹' wilkieBoundedImage A :
      Set (wilkieOpenCube n)) := by
  have heq :
      (Subtype.val ⁻¹' wilkieBoundedImage A :
          Set (wilkieOpenCube n)) =
        wilkieBoundedHomeomorph n '' A := by
    ext u
    constructor
    · rintro ⟨x, hx, hxu⟩
      refine ⟨x, hx, ?_⟩
      apply Subtype.ext
      simpa only [wilkieBoundedHomeomorph_coe_apply] using hxu
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, (wilkieBoundedHomeomorph_coe_apply n x).symm⟩
  rw [heq]
  exact (wilkieBoundedHomeomorph n).isClosed_image.mpr hA

/-! ## A polynomial-sign presentation of the graph -/

def wilkieBoundedEquationPolynomial (n : ℕ) (i : Fin n) :
    MvPolynomial (Fin (n + n)) ℝ :=
  let X := MvPolynomial.X (Fin.castAdd n i)
  let U := MvPolynomial.X (Fin.natAdd n i)
  U ^ 2 * (1 + X ^ 2) - X ^ 2

def wilkieBoundedSignPolynomial (n : ℕ) (i : Fin n) :
    MvPolynomial (Fin (n + n)) ℝ :=
  MvPolynomial.X (Fin.castAdd n i) *
    MvPolynomial.X (Fin.natAdd n i)

def wilkieBoundedCoordinateConstraint (n : ℕ) (i : Fin n) :
    Set (RealEuclidean (n + n)) :=
  {w | MvPolynomial.eval w (wilkieBoundedEquationPolynomial n i) = 0} ∩
    ({w | MvPolynomial.eval w (wilkieBoundedSignPolynomial n i) = 0} ∪
      {w | 0 < MvPolynomial.eval w (wilkieBoundedSignPolynomial n i)})

def wilkieBoundedIncidence (n : ℕ) : Set (RealEuclidean (n + n)) :=
  ⋂ i, wilkieBoundedCoordinateConstraint n i

theorem polynomialSignConstructible_wilkieBoundedCoordinateConstraint
    (n : ℕ) (i : Fin n) :
    PolynomialSignConstructible (n + n)
      (wilkieBoundedCoordinateConstraint n i) := by
  exact .inter (.zero _) (.union (.zero _) (.pos _))

theorem polynomialSignConstructible_iInter_fin
    {d n : ℕ} (A : Fin n → Set (RealEuclidean d))
    (hA : ∀ i, PolynomialSignConstructible d (A i)) :
    PolynomialSignConstructible d (⋂ i, A i) := by
  induction n with
  | zero =>
      simpa using polynomialSignConstructible_univ d
  | succ n ih =>
      rw [show (⋂ i : Fin (n + 1), A i) =
          A 0 ∩ ⋂ j : Fin n, A j.succ by
        ext x
        simp only [Set.mem_iInter, Set.mem_inter_iff]
        constructor
        · intro hx
          exact ⟨hx 0, fun j ↦ hx j.succ⟩
        · rintro ⟨hzero, hsucc⟩ i
          exact Fin.cases hzero (fun j ↦ hsucc j) i]
      exact .inter (hA 0) (ih (fun j ↦ A j.succ) (fun j ↦ hA j.succ))

theorem polynomialSignConstructible_wilkieBoundedIncidence (n : ℕ) :
    PolynomialSignConstructible (n + n) (wilkieBoundedIncidence n) :=
  polynomialSignConstructible_iInter_fin _
    (polynomialSignConstructible_wilkieBoundedCoordinateConstraint n)

@[simp]
theorem realEuclideanAppend_mem_wilkieBoundedCoordinateConstraint_iff
    {n : ℕ} (x u : RealEuclidean n) (i : Fin n) :
    realEuclideanAppend x u ∈ wilkieBoundedCoordinateConstraint n i ↔
      u i = wilkieBoundedCoordinate (x i) := by
  rw [wilkieBoundedCoordinate_eq_iff]
  simp only [wilkieBoundedCoordinateConstraint, Set.mem_inter_iff,
    Set.mem_union, Set.mem_ofPred_eq,
    wilkieBoundedEquationPolynomial, wilkieBoundedSignPolynomial,
    map_sub, map_mul, map_add, map_pow, map_one, MvPolynomial.eval_X,
    realEuclideanAppend_castAdd]
  rw [realEuclideanAppend_natAdd]
  constructor
  · rintro ⟨heq, hzero | hpos⟩
    · exact ⟨sub_eq_zero.mp heq, le_of_eq hzero.symm⟩
    · exact ⟨sub_eq_zero.mp heq, hpos.le⟩
  · rintro ⟨heq, hnonneg⟩
    refine ⟨sub_eq_zero.mpr heq, ?_⟩
    rcases hnonneg.eq_or_lt with hzero | hpos
    · exact Or.inl hzero.symm
    · exact Or.inr hpos

@[simp]
theorem realEuclideanAppend_mem_wilkieBoundedIncidence_iff
    {n : ℕ} (x u : RealEuclidean n) :
    realEuclideanAppend x u ∈ wilkieBoundedIncidence n ↔
      u = wilkieBoundedMap n x := by
  simp only [wilkieBoundedIncidence, Set.mem_iInter,
    realEuclideanAppend_mem_wilkieBoundedCoordinateConstraint_iff]
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrFun h i

theorem wilkieBoundedIncidence_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (n : ℕ) (hn : 0 < n) :
    wilkieBoundedIncidence n ∈ charbonnelClosure S (n + n) :=
  hC.ws2_polynomialSign (by omega)
    (polynomialSignConstructible_wilkieBoundedIncidence n)

/-! ## Inverse images stay in the generated weak structure -/

def wilkieBoundedPreimage {n : ℕ} (A : Set (RealEuclidean n)) :
    Set (RealEuclidean n) :=
  {x | wilkieBoundedMap n x ∈ A}

def wilkieBoundedPreimageIncidence {n : ℕ}
    (A : Set (RealEuclidean n)) : Set (RealEuclidean (n + n)) :=
  wilkieBoundedIncidence n ∩
    realEuclideanSetProduct Set.univ A

theorem realEuclideanExistentialProjection_wilkieBoundedPreimageIncidence
    {n : ℕ} (A : Set (RealEuclidean n)) :
    realEuclideanExistentialProjection
        (wilkieBoundedPreimageIncidence A) =
      wilkieBoundedPreimage A := by
  ext x
  simp only [realEuclideanExistentialProjection, Set.mem_ofPred_eq,
    wilkieBoundedPreimageIncidence, Set.mem_inter_iff,
    realEuclideanAppend_mem_wilkieBoundedIncidence_iff,
    realEuclideanSetProduct, realEuclideanTakeRight_append,
    Set.mem_univ, true_and,
    wilkieBoundedPreimage]
  constructor
  · rintro ⟨u, hu, hA⟩
    simpa [hu] using hA
  · intro hA
    exact ⟨wilkieBoundedMap n x, rfl, hA⟩

theorem wilkieBoundedPreimage_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure S n) :
    wilkieBoundedPreimage A ∈ charbonnelClosure S n := by
  have hUniv : (Set.univ : Set (RealEuclidean n)) ∈
      charbonnelClosure S n :=
    hC.ws2_polynomialSign hn (polynomialSignConstructible_univ n)
  have hProduct : realEuclideanSetProduct
      (Set.univ : Set (RealEuclidean n)) A ∈
        charbonnelClosure S (n + n) :=
    hC.ws3_prod hn hn hUniv hA
  have hIncidence : wilkieBoundedIncidence n ∈
      charbonnelClosure S (n + n) :=
    wilkieBoundedIncidence_mem_charbonnelClosure hC n hn
  have hBoth : wilkieBoundedPreimageIncidence A ∈
      charbonnelClosure S (n + n) :=
    hC.ws1_inter (by omega) hIncidence hProduct
  rw [← realEuclideanExistentialProjection_wilkieBoundedPreimageIncidence A]
  exact charbonnelClosure_projection hn hBoth

/-! ## Images stay in the generated weak structure -/

/-- The same graph with the bounded coordinate block first, so existential
projection produces the image rather than the inverse image. -/
def wilkieBoundedReverseIncidence (n : ℕ) :
    Set (RealEuclidean (n + n)) :=
  realEuclideanCoordinateReindex (@finAddFlip n n) ''
    wilkieBoundedIncidence n

@[simp]
theorem realEuclideanAppend_mem_wilkieBoundedReverseIncidence_iff
    {n : ℕ} (u x : RealEuclidean n) :
    realEuclideanAppend u x ∈ wilkieBoundedReverseIncidence n ↔
      u = wilkieBoundedMap n x := by
  constructor
  · rintro ⟨w, hw, hswap⟩
    have hwCanonical :
        w = realEuclideanAppend x u := by
      apply (realEuclideanCoordinateReindex (@finAddFlip n n)).injective
      rw [hswap]
      exact (realEuclideanCoordinateReindex_finAddFlip_append u x).symm
    rw [hwCanonical] at hw
    exact
      (realEuclideanAppend_mem_wilkieBoundedIncidence_iff x u).mp hw
  · intro hu
    refine ⟨realEuclideanAppend x u,
      (realEuclideanAppend_mem_wilkieBoundedIncidence_iff x u).mpr hu,
      ?_⟩
    exact realEuclideanCoordinateReindex_finAddFlip_append u x

theorem wilkieBoundedReverseIncidence_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    (n : ℕ) (hn : 0 < n) :
    wilkieBoundedReverseIncidence n ∈ charbonnelClosure S (n + n) := by
  exact hC.ws4_linearEquiv (by omega)
    (wilkieBoundedIncidence_mem_charbonnelClosure hC n hn)
    (realEuclideanCoordinateReindex (@finAddFlip n n))

def wilkieBoundedImageIncidence {n : ℕ}
    (A : Set (RealEuclidean n)) : Set (RealEuclidean (n + n)) :=
  wilkieBoundedReverseIncidence n ∩
    realEuclideanSetProduct Set.univ A

theorem realEuclideanExistentialProjection_wilkieBoundedImageIncidence
    {n : ℕ} (A : Set (RealEuclidean n)) :
    realEuclideanExistentialProjection (wilkieBoundedImageIncidence A) =
      wilkieBoundedImage A := by
  ext u
  simp only [realEuclideanExistentialProjection, Set.mem_ofPred_eq,
    wilkieBoundedImageIncidence, Set.mem_inter_iff,
    realEuclideanAppend_mem_wilkieBoundedReverseIncidence_iff,
    realEuclideanSetProduct, realEuclideanTakeRight_append,
    Set.mem_univ, true_and, wilkieBoundedImage, Set.mem_image]
  constructor
  · rintro ⟨x, hmap, hx⟩
    exact ⟨x, hx, hmap.symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, rfl, hx⟩

theorem wilkieBoundedImage_mem_charbonnelClosure
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hA : A ∈ charbonnelClosure S n) :
    wilkieBoundedImage A ∈ charbonnelClosure S n := by
  have hUniv : (Set.univ : Set (RealEuclidean n)) ∈
      charbonnelClosure S n :=
    hC.ws2_polynomialSign hn (polynomialSignConstructible_univ n)
  have hProduct : realEuclideanSetProduct
      (Set.univ : Set (RealEuclidean n)) A ∈
        charbonnelClosure S (n + n) :=
    hC.ws3_prod hn hn hUniv hA
  have hIncidence : wilkieBoundedReverseIncidence n ∈
      charbonnelClosure S (n + n) :=
    wilkieBoundedReverseIncidence_mem_charbonnelClosure hC n hn
  have hBoth : wilkieBoundedImageIncidence A ∈
      charbonnelClosure S (n + n) :=
    hC.ws1_inter (by omega) hIncidence hProduct
  rw [← realEuclideanExistentialProjection_wilkieBoundedImageIncidence A]
  exact charbonnelClosure_projection hn hBoth

/-! ## Compatibility with visible-coordinate projection -/

@[simp]
theorem wilkieBoundedMap_append {n q : ℕ}
    (x : RealEuclidean n) (y : RealEuclidean q) :
    wilkieBoundedMap (n + q) (realEuclideanAppend x y) =
      realEuclideanAppend (wilkieBoundedMap n x)
        (wilkieBoundedMap q y) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
    simp [wilkieBoundedMap]

theorem realEuclideanExistentialProjection_wilkieBoundedImage
    {n q : ℕ} (B : Set (RealEuclidean (n + q))) :
    realEuclideanExistentialProjection (wilkieBoundedImage B) =
      wilkieBoundedImage (realEuclideanExistentialProjection B) := by
  ext u
  constructor
  · rintro ⟨v, w, hwB, hmap⟩
    let x : RealEuclidean n := realEuclideanTakeLeft w
    let y : RealEuclidean q := realEuclideanTakeRight w
    have hw : w = realEuclideanAppend x y := by
      exact (realEuclideanAppend_takeLeft_takeRight w).symm
    have hmap' :
        realEuclideanAppend (wilkieBoundedMap n x)
            (wilkieBoundedMap q y) =
          realEuclideanAppend u v := by
      rw [← wilkieBoundedMap_append, ← hw]
      exact hmap
    have hu : wilkieBoundedMap n x = u := by
      have := congrArg (realEuclideanTakeLeft (n := n) (m := q)) hmap'
      simpa using this
    refine ⟨x, ?_, hu⟩
    exact ⟨y, by simpa [hw] using hwB⟩
  · rintro ⟨x, ⟨y, hxyB⟩, hxu⟩
    refine ⟨wilkieBoundedMap q y, realEuclideanAppend x y, hxyB, ?_⟩
    rw [wilkieBoundedMap_append, hxu]

theorem wilkieBoundedPreimage_openCube_sdiff_image
    {n : ℕ} (A : Set (RealEuclidean n)) :
    wilkieBoundedPreimage (wilkieOpenCube n \ wilkieBoundedImage A) =
      Aᶜ := by
  ext x
  constructor
  · rintro ⟨_hxCube, hxNotImage⟩ hxA
    exact hxNotImage ⟨x, hxA, rfl⟩
  · intro hxNotA
    refine ⟨wilkieBoundedMap_mem_openCube n x, ?_⟩
    rintro ⟨y, hyA, hyx⟩
    have hyEq : y = x :=
      wilkieBoundedMap_injective n hyx
    exact hxNotA (hyEq ▸ hyA)

/-- Once bounded cell decomposition has put the complement of the bounded
image in the family, the semialgebraic inverse-image construction returns the
ordinary complement in the original coordinates. -/
theorem compl_mem_charbonnelClosure_of_openCube_sdiff_boundedImage_mem
    {S : EuclideanSetFamily}
    (hC : PositiveArityWeakSetStructure (charbonnelClosure S))
    {n : ℕ} (hn : 0 < n) {A : Set (RealEuclidean n)}
    (hboundedComplement :
      wilkieOpenCube n \ wilkieBoundedImage A ∈
        charbonnelClosure S n) :
    Aᶜ ∈ charbonnelClosure S n := by
  have hpreimage := wilkieBoundedPreimage_mem_charbonnelClosure
    hC hn hboundedComplement
  rwa [wilkieBoundedPreimage_openCube_sdiff_image A] at hpreimage

end AbelFormalization
