import AbelFormalization.ClosedZeroSetCharbonnelBridge
import AbelFormalization.SmoothFamilyRectangularRankLocus
import AbelFormalization.Wilkie28ExceptionalMathlibOnly
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Wilkie 2.8 exceptional values as a rank-one Charbonnel member

The singular witnesses are cut out by the equations `F x = a`, `f x = b`,
and all maximal minors of the augmented map `(F,f)` being zero.  One
sum-of-squares function in the geometric derivative-closed family expresses
all these equations on the coordinate space `(b,x)`.  Its zero set projects
onto the unary exceptional-value set.
-/

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- The flat augmented tuple `(F,f)`. -/
def wilkie28AugmentedTuple {n k : ℕ}
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) :
    RealEuclidean n → RealEuclidean (k + 1) :=
  fun x ↦ realEuclideanAppend (F x) (fun _ : Fin 1 ↦ f x)

theorem wilkie28AugmentedTuple_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n) :
    FunctionTupleInFamily G (wilkie28AugmentedTuple F f) := by
  intro i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa only [wilkie28AugmentedTuple, realEuclideanAppend_castAdd] using hF j
  · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    simpa only [wilkie28AugmentedTuple, realEuclideanAppend_natAdd] using hf

/-- In flat coordinates, the augmented derivative has the original derivative
and the scalar derivative as its two blocks. -/
theorem wilkie28AugmentedTuple_fderiv
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (x v : RealEuclidean n)
    (hFdiff : DifferentiableAt ℝ F x)
    (hfdiff : DifferentiableAt ℝ f x) :
    fderiv ℝ (wilkie28AugmentedTuple F f) x v =
      realEuclideanAppend (fderiv ℝ F x v)
        (fun _ : Fin 1 ↦ fderiv ℝ f x v) := by
  let g := wilkie28AugmentedTuple F f
  have hFcoords : ∀ i : Fin k,
      DifferentiableAt ℝ (fun y ↦ F y i) x :=
    differentiableAt_pi.mp hFdiff
  have hgcoords : ∀ i : Fin (k + 1),
      DifferentiableAt ℝ (fun y ↦ g y i) x := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa only [g, wilkie28AugmentedTuple,
        realEuclideanAppend_castAdd] using hFcoords j
    · simpa only [g, wilkie28AugmentedTuple,
        realEuclideanAppend_natAdd] using hfdiff
  have hFderiv : fderiv ℝ F x =
      constraintFDeriv (fun i y ↦ F y i) x := by
    change fderiv ℝ (fun y i ↦ F y i) x =
      ContinuousLinearMap.pi (fun i ↦ fderiv ℝ (fun y ↦ F y i) x)
    exact fderiv_pi hFcoords
  have hgderiv : fderiv ℝ g x =
      constraintFDeriv (fun i y ↦ g y i) x := by
    change fderiv ℝ (fun y i ↦ g y i) x =
      ContinuousLinearMap.pi (fun i ↦ fderiv ℝ (fun y ↦ g y i) x)
    exact fderiv_pi hgcoords
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · have hleft := congrFun (congrArg (fun L : RealEuclidean n →L[ℝ]
        RealEuclidean (k + 1) ↦ L v) hgderiv) (Fin.castAdd 1 j)
    have hFleft := congrFun (congrArg (fun L : RealEuclidean n →L[ℝ]
        RealEuclidean k ↦ L v) hFderiv) j
    simp only [realEuclideanAppend_castAdd]
    calc
      fderiv ℝ (wilkie28AugmentedTuple F f) x v (Fin.castAdd 1 j) =
          fderiv ℝ (fun y ↦ F y j) x v := by
        simpa only [g, wilkie28AugmentedTuple,
          realEuclideanAppend_castAdd, constraintFDeriv,
          ContinuousLinearMap.pi_apply] using hleft
      _ = fderiv ℝ F x v j := by
        simpa only [constraintFDeriv,
          ContinuousLinearMap.pi_apply] using hFleft.symm
  · have hright := congrFun (congrArg (fun L : RealEuclidean n →L[ℝ]
        RealEuclidean (k + 1) ↦ L v) hgderiv) (Fin.natAdd k j)
    simpa only [g, wilkie28AugmentedTuple,
      realEuclideanAppend_natAdd, constraintFDeriv,
      ContinuousLinearMap.pi_apply] using hright

/-- Surjectivity of the flat derivative is equivalent to surjectivity of the
product-valued derivative in Wilkie's exceptional-set definition. -/
theorem wilkie28AugmentedTuple_fderiv_surjective_iff
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (x : RealEuclidean n)
    (hFdiff : DifferentiableAt ℝ F x)
    (hfdiff : DifferentiableAt ℝ f x) :
    Function.Surjective (fderiv ℝ (wilkie28AugmentedTuple F f) x) ↔
      Function.Surjective
        (fun v : RealEuclidean n ↦
          (fderiv ℝ F x v, fderiv ℝ f x v)) := by
  have hflat : ∀ v : RealEuclidean n,
      fderiv ℝ (wilkie28AugmentedTuple F f) x v =
        realEuclideanAppend (fderiv ℝ F x v)
          (fun _ : Fin 1 ↦ fderiv ℝ f x v) := by
    intro v
    exact wilkie28AugmentedTuple_fderiv F f x v hFdiff hfdiff
  constructor
  · intro hsurj
    rintro ⟨y, z⟩
    obtain ⟨v, hv⟩ := hsurj
      (realEuclideanAppend y (fun _ : Fin 1 ↦ z))
    refine ⟨v, ?_⟩
    apply Prod.ext
    · funext i
      have hi := congrFun hv (Fin.castAdd 1 i)
      simpa only [hflat v, realEuclideanAppend_castAdd] using hi
    · have hi := congrFun hv (Fin.natAdd k (0 : Fin 1))
      simpa only [hflat v, realEuclideanAppend_natAdd] using hi
  · intro hsurj
    intro target
    obtain ⟨v, hv⟩ := hsurj
      (realEuclideanTakeLeft target,
        realEuclideanTakeRight target (0 : Fin 1))
    refine ⟨v, ?_⟩
    have hvF : fderiv ℝ F x v = realEuclideanTakeLeft target :=
      congrArg Prod.fst hv
    have hvf : fderiv ℝ f x v =
        realEuclideanTakeRight target (0 : Fin 1) :=
      congrArg Prod.snd hv
    rw [hflat v, hvF]
    have hright : (fun _ : Fin 1 ↦ fderiv ℝ f x v) =
        realEuclideanTakeRight target := by
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      exact hvf
    rw [hright]
    exact realEuclideanAppend_takeLeft_takeRight target

/-- The unary set of singular values for the augmented tuple. -/
def wilkie28FlatExceptionalSlice {n k : ℕ}
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k) :
    Set (RealEuclidean 1) :=
  {b | ∃ x : RealEuclidean n,
    F x = a ∧ f x = b 0 ∧
      ∀ cols : Fin (k + 1) ↪ Fin n,
        standardJacobianColumnMinor
          (wilkie28AugmentedTuple F f) cols x = 0}

/-- A single finite sum of squares simultaneously imposes the fiber value,
the unary function value, and all maximal augmented Jacobian minors. -/
def wilkie28ExceptionalResidual {n k : ℕ}
    (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k) :
    RealEuclideanFunction (1 + n) :=
  fun w ↦
    (∑ i : Fin k, (F (realEuclideanTakeRight w) i - a i) ^ 2) +
      (f (realEuclideanTakeRight w) - realEuclideanTakeLeft w 0) ^ 2 +
      (∑ cols : Fin (k + 1) ↪ Fin n,
        standardJacobianColumnMinor (wilkie28AugmentedTuple F f)
          cols (realEuclideanTakeRight w) ^ 2)

theorem wilkie28ExceptionalResidual_append_eq_zero_iff
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (b : RealEuclidean 1) (x : RealEuclidean n) :
    wilkie28ExceptionalResidual F f a (realEuclideanAppend b x) = 0 ↔
      F x = a ∧ f x = b 0 ∧
        ∀ cols : Fin (k + 1) ↪ Fin n,
          standardJacobianColumnMinor
            (wilkie28AugmentedTuple F f) cols x = 0 := by
  classical
  simp only [wilkie28ExceptionalResidual,
    realEuclideanTakeRight_append, realEuclideanTakeLeft_append]
  let A : ℝ := ∑ i : Fin k, (F x i - a i) ^ 2
  let B : ℝ := (f x - b 0) ^ 2
  let M : ℝ := ∑ cols : Fin (k + 1) ↪ Fin n,
    standardJacobianColumnMinor (wilkie28AugmentedTuple F f) cols x ^ 2
  have hA_nonneg : 0 ≤ A := Finset.sum_nonneg
    (fun i _ ↦ sq_nonneg (F x i - a i))
  have hB_nonneg : 0 ≤ B := sq_nonneg (f x - b 0)
  have hM_nonneg : 0 ≤ M := Finset.sum_nonneg
    (fun cols _ ↦ sq_nonneg
      (standardJacobianColumnMinor (wilkie28AugmentedTuple F f) cols x))
  change A + B + M = 0 ↔
    F x = a ∧ f x = b 0 ∧
      ∀ cols : Fin (k + 1) ↪ Fin n,
        standardJacobianColumnMinor (wilkie28AugmentedTuple F f) cols x = 0
  constructor
  · intro hzero
    have hAz : A = 0 := by nlinarith
    have hBz : B = 0 := by nlinarith
    have hMz : M = 0 := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · funext i
      have hi := ((Finset.sum_sq_eq_zero_iff Finset.univ
        (fun j : Fin k ↦ F x j - a j)).mp hAz) i
        (Finset.mem_univ i)
      exact sub_eq_zero.mp hi
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hBz)
    · intro cols
      have hc := ((Finset.sum_sq_eq_zero_iff Finset.univ
        (fun c : Fin (k + 1) ↪ Fin n ↦
          standardJacobianColumnMinor (wilkie28AugmentedTuple F f) c x)).mp hMz) cols
        (Finset.mem_univ cols)
      exact hc
  · rintro ⟨hF, hf, hminor⟩
    have hAz : A = 0 := by
      apply (Finset.sum_sq_eq_zero_iff Finset.univ
        (fun i : Fin k ↦ F x i - a i)).mpr
      intro i _
      exact sub_eq_zero.mpr (congrFun hF i)
    have hBz : B = 0 := by
      simp [B, hf]
    have hMz : M = 0 := by
      apply (Finset.sum_sq_eq_zero_iff Finset.univ
        (fun cols : Fin (k + 1) ↪ Fin n ↦
          standardJacobianColumnMinor (wilkie28AugmentedTuple F f) cols x)).mpr
      intro cols _
      exact hminor cols
    simp only [hAz, hBz, hMz, add_zero]

/-- All three blocks of the residual remain in the geometric family. -/
theorem wilkie28ExceptionalResidual_mem
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n) :
    wilkie28ExceptionalResidual F f a ∈ G (1 + n) := by
  classical
  let R := realEuclideanTakeRightLinearMap 1 n
  let g := wilkie28AugmentedTuple F f
  have hg : FunctionTupleInFamily G g :=
    wilkie28AugmentedTuple_mem F f hF hf
  have hrow : ∀ i : Fin k,
      (fun w : RealEuclidean (1 + n) ↦
        F (realEuclideanTakeRight w) i - a i) ∈ G (1 + n) := by
    intro i
    have hpulled := hG.affine_comp (hF i) R.toAffineMap
    have hsub := hG.sub_mem hpulled (hG.const_mem (n := 1 + n) (a i))
    convert hsub using 1
    funext w
    rfl
  have hvalue : (fun w : RealEuclidean (1 + n) ↦
      f (realEuclideanTakeRight w) - realEuclideanTakeLeft w 0) ∈
      G (1 + n) := by
    let j : Fin (1 + n) := Fin.castAdd n (0 : Fin 1)
    have hcoordinate : (fun w : RealEuclidean (1 + n) ↦ w j) ∈
        G (1 + n) := by
      simpa [j] using hG.polynomial (MvPolynomial.X j)
    have hpulled := hG.affine_comp hf R.toAffineMap
    have hsub := hG.sub_mem hpulled hcoordinate
    convert hsub using 1
    funext w
    rfl
  have hminor : ∀ cols : Fin (k + 1) ↪ Fin n,
      (fun w : RealEuclidean (1 + n) ↦
        standardJacobianColumnMinor g cols (realEuclideanTakeRight w)) ∈
      G (1 + n) := by
    intro cols
    have hm := hG.standardJacobianColumnMinor_mem hderiv g hg cols
    convert hG.affine_comp hm R.toAffineMap using 1
    funext w
    rfl
  have hrowsum : (fun w : RealEuclidean (1 + n) ↦
      ∑ i : Fin k, (F (realEuclideanTakeRight w) i - a i) ^ 2) ∈
      G (1 + n) := by
    have hsum := hG.finset_sum_mem (Finset.univ : Finset (Fin k))
      (fun i ↦ fun w : RealEuclidean (1 + n) ↦
        (F (realEuclideanTakeRight w) i - a i) ^ 2)
      (by intro i _; exact hG.sq_mem (hrow i))
    convert hsum using 1
    funext w
    simp only [Finset.sum_apply]
  have hminorsum : (fun w : RealEuclidean (1 + n) ↦
      ∑ cols : Fin (k + 1) ↪ Fin n,
        standardJacobianColumnMinor g cols
          (realEuclideanTakeRight w) ^ 2) ∈ G (1 + n) := by
    have hsum := hG.finset_sum_mem
      (Finset.univ : Finset (Fin (k + 1) ↪ Fin n))
      (fun cols ↦ fun w : RealEuclidean (1 + n) ↦
        standardJacobianColumnMinor g cols
          (realEuclideanTakeRight w) ^ 2)
      (by intro cols _; exact hG.sq_mem (hminor cols))
    convert hsum using 1
    funext w
    simp only [Finset.sum_apply]
  have htotal := hG.add (hG.add hrowsum (hG.sq_mem hvalue)) hminorsum
  convert htotal using 1
  funext w
  rfl

theorem wilkie28FlatExceptionalSlice_isProjectedZeroSet
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n) :
    IsProjectedZeroSet G (wilkie28FlatExceptionalSlice F f a) := by
  refine ⟨n, wilkie28ExceptionalResidual F f a,
    wilkie28ExceptionalResidual_mem hG hderiv F f a hF hf, ?_⟩
  ext b
  simp only [wilkie28FlatExceptionalSlice, Set.mem_setOf_eq]
  exact exists_congr (fun x ↦
    (wilkie28ExceptionalResidual_append_eq_zero_iff F f a b x).symm)

/-- The actual Wilkie product-valued exceptional set coincides with the
flat minor description in its unique unary coordinate. -/
theorem wilkie28FlatExceptionalSlice_eq_exceptionalParameterSet
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n) :
    wilkie28FlatExceptionalSlice F f a =
      {b : RealEuclidean 1 |
        b 0 ∈ Wilkie28MathlibOnly.exceptionalParameterSet F f a} := by
  let g := wilkie28AugmentedTuple F f
  have hg : FunctionTupleInFamily G g :=
    wilkie28AugmentedTuple_mem F f hF hf
  ext b
  simp only [wilkie28FlatExceptionalSlice,
    Wilkie28MathlibOnly.exceptionalParameterSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hFx, hfx, hminor⟩
    refine ⟨x, hFx, hfx, ?_⟩
    intro hsurj
    have hFdiff : DifferentiableAt ℝ F x := by
      rw [differentiableAt_pi]
      intro i
      exact ((hsmooth n (fun y ↦ F y i) (hF i)).differentiable
        (by simp)).differentiableAt
    have hfdiff : DifferentiableAt ℝ f x :=
      ((hsmooth n f hf).differentiable (by simp)).differentiableAt
    have hgSurj :=
      (wilkie28AugmentedTuple_fderiv_surjective_iff F f x hFdiff hfdiff).mpr hsurj
    obtain ⟨cols, hc⟩ :=
      (hsmooth.fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
        g hg x).mp hgSurj
    exact hc (hminor cols)
  · rintro ⟨x, hFx, hfx, hsingular⟩
    refine ⟨x, hFx, hfx, ?_⟩
    intro cols
    by_contra hc
    have hgSurj :=
      (hsmooth.fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero
        g hg x).mpr ⟨cols, hc⟩
    have hFdiff : DifferentiableAt ℝ F x := by
      rw [differentiableAt_pi]
      intro i
      exact ((hsmooth n (fun y ↦ F y i) (hF i)).differentiable
        (by simp)).differentiableAt
    have hfdiff : DifferentiableAt ℝ f x :=
      ((hsmooth n f hf).differentiable (by simp)).differentiableAt
    exact hsingular
      ((wilkie28AugmentedTuple_fderiv_surjective_iff F f x hFdiff hfdiff).mp hgSurj)

/-- A base node for the residual zero set followed by one projection node
describes the original Wilkie exceptional unary set with rank one. -/
theorem wilkie28_exceptionalParameterSet_rank_one_literalZero_description
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n) :
    ∃ description : CharbonnelDescription (literalZeroSetFamily G) 1,
      description.carrier =
        {b : RealEuclidean 1 |
          b 0 ∈ Wilkie28MathlibOnly.exceptionalParameterSet F f a} ∧
      description.rank = 1 := by
  rw [← wilkie28FlatExceptionalSlice_eq_exceptionalParameterSet hsmooth F f a hF hf]
  have hprojected := wilkie28FlatExceptionalSlice_isProjectedZeroSet
    hG hderiv F f a hF hf
  exact hprojected.exists_rank_one_literalZero_description (by omega)

/-- The Wilkie 2.8 WS5 membership input in Charbonnel's expanded weak
family over literal zero-set generators. -/
theorem wilkie28_exceptionalParameterSet_mem_literalZeroCharbonnel
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hderiv : IsCoordinateDerivativeClosedFunctionFamily G)
    {n k : ℕ} (F : RealEuclidean n → RealEuclidean k)
    (f : RealEuclideanFunction n) (a : RealEuclidean k)
    (hF : FunctionTupleInFamily G F) (hf : f ∈ G n) :
    {b : RealEuclidean 1 |
      b 0 ∈ Wilkie28MathlibOnly.exceptionalParameterSet F f a} ∈
      charbonnelClosure (literalZeroSetFamily G) 1 := by
  obtain ⟨description, hcarrier, _⟩ :=
    wilkie28_exceptionalParameterSet_rank_one_literalZero_description
      hG hsmooth hderiv F f a hF hf
  exact ⟨description, hcarrier⟩

end AbelFormalization
