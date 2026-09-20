import AbelFormalization.LionLemma4RegularMinorCover
import AbelFormalization.SmoothFamilyJacobianRankStrata

noncomputable section

open Set Function
open scoped BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-- If every vector in `K` is the first component of a vector in `ker D`,
and no nonzero vertical vector belongs to `ker D`, then `K` has dimension at
most `ker D`. -/
theorem finrank_le_finrank_ker_of_primal_lifts
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (D : (X × Y) →L[ℝ] Z) (K : Submodule ℝ X)
    (hvertical : ∀ y, D (0, y) = 0 → y = 0)
    (hlift : ∀ x ∈ K, ∃ y, D (x, y) = 0) :
    Module.finrank ℝ K ≤ Module.finrank ℝ D.ker := by
  let P : D.ker →ₗ[ℝ] X :=
    (LinearMap.fst ℝ X Y).comp D.ker.subtype
  have hPinj : Function.Injective P := by
    intro u v huv
    apply Subtype.ext
    apply Prod.ext
    · exact huv
    · apply sub_eq_zero.mp
      apply hvertical (u.1.2 - v.1.2)
      have hu : D u.1 = 0 := u.2
      have hv : D v.1 = 0 := v.2
      have hfst : u.1.1 = v.1.1 := huv
      rw [show (0, u.1.2 - v.1.2) = u.1 - v.1 by
        ext <;> simp [hfst], map_sub, hu, hv, sub_zero]
  have hKle : K ≤ LinearMap.range P := by
    intro x hx
    obtain ⟨y, hy⟩ := hlift x hx
    refine ⟨⟨(x, y), hy⟩, rfl⟩
  calc
    Module.finrank ℝ K ≤ Module.finrank ℝ (LinearMap.range P) :=
      Submodule.finrank_mono hKle
    _ = Module.finrank ℝ D.ker :=
      LinearMap.finrank_range_of_inj hPinj

/-- A finite family of scalar covectors, selected with repetition allowed. -/
def selectedCovectorMap
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (B : I → E →L[ℝ] ℝ) (selection : Fin k → I) :
    E →L[ℝ] RealEuclidean k :=
  ContinuousLinearMap.pi fun j ↦ B (selection j)

/-- Append two continuous linear maps in the same `Fin.addCases` ordering as
`LionCarpetedLeaf.definingTupleAppend`. -/
def coordinateAppendContinuousLinearMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q k : ℕ} (A : E →L[ℝ] RealEuclidean q)
    (B : E →L[ℝ] RealEuclidean k) :
    E →L[ℝ] RealEuclidean (q + k) :=
  ContinuousLinearMap.pi fun i ↦
    Fin.addCases
      (fun j ↦ (ContinuousLinearMap.proj j).comp A)
      (fun j ↦ (ContinuousLinearMap.proj j).comp B) i

@[simp]
theorem coordinateAppendContinuousLinearMap_apply_castAdd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q k : ℕ} (A : E →L[ℝ] RealEuclidean q)
    (B : E →L[ℝ] RealEuclidean k) (v : E) (i : Fin q) :
    coordinateAppendContinuousLinearMap A B v (Fin.castAdd k i) = A v i := by
  simp [coordinateAppendContinuousLinearMap]

@[simp]
theorem coordinateAppendContinuousLinearMap_apply_natAdd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q k : ℕ} (A : E →L[ℝ] RealEuclidean q)
    (B : E →L[ℝ] RealEuclidean k) (v : E) (i : Fin k) :
    coordinateAppendContinuousLinearMap A B v (Fin.natAdd q i) = B v i := by
  simp [coordinateAppendContinuousLinearMap]

/-- If the first block is onto, an appended coordinate map is onto once its
second block is onto along the kernel of the first. -/
theorem coordinateAppendContinuousLinearMap_surjective_of_restrictKer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q k : ℕ} (A : E →L[ℝ] RealEuclidean q)
    (B : E →L[ℝ] RealEuclidean k)
    (hA : Function.Surjective A)
    (hB : Function.Surjective (B.comp A.ker.subtypeL)) :
    Function.Surjective (coordinateAppendContinuousLinearMap A B) := by
  intro target
  let left : RealEuclidean q := fun i ↦ target (Fin.castAdd k i)
  let right : RealEuclidean k := fun i ↦ target (Fin.natAdd q i)
  obtain ⟨v, hv⟩ := hA left
  obtain ⟨w, hw⟩ := hB (right - B v)
  refine ⟨v + (w : E), ?_⟩
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · rw [coordinateAppendContinuousLinearMap_apply_castAdd, map_add]
    rw [hv]
    have hwA := congrFun w.property j
    simp only [Pi.zero_apply] at hwA
    change (left + A (w : E)) j = target (Fin.castAdd k j)
    calc
      (left + A (w : E)) j = left j + A (w : E) j := rfl
      _ = left j + 0 := congrArg (left j + ·) hwA
      _ = target (Fin.castAdd k j) := by simp [left]
  · rw [coordinateAppendContinuousLinearMap_apply_natAdd, map_add]
    have hw' : B (w : E) = right - B v := by
      simpa [ContinuousLinearMap.comp_apply] using hw
    rw [hw']
    simp [right]

/-- A dimension bound on the common kernel of a surjective first block and
a finite family of covectors selects enough actual covectors to give full
appended rank. -/
theorem exists_selectedCovectorMap_append_surjective_of_commonKernel_finrank_le
    {n q p : ℕ} {I : Type*} [Fintype I]
    (A : RealEuclidean n →L[ℝ] RealEuclidean q)
    (B : I → RealEuclidean n →L[ℝ] ℝ)
    (hA : Function.Surjective A)
    (hcommon : Module.finrank ℝ
      (A.prod (ContinuousLinearMap.pi B)).ker ≤ p)
    (hdim : p + q ≤ n) :
    ∃ selection : Fin (n - p - q) → I,
      Function.Surjective
        (coordinateAppendContinuousLinearMap A
          (selectedCovectorMap B selection)) := by
  classical
  let C : RealEuclidean n →L[ℝ]
      (RealEuclidean q × (I → ℝ)) :=
    A.prod (ContinuousLinearMap.pi B)
  let K : Submodule ℝ (RealEuclidean n) := A.ker
  have hKdim : Module.finrank ℝ K = n - q := by
    have hrankNullity := A.toLinearMap.finrank_range_add_finrank_ker
    have hArange : A.range = ⊤ := LinearMap.range_eq_top.mpr hA
    rw [hArange, finrank_top, Module.finrank_pi,
      Fintype.card_fin, Module.finrank_pi, Fintype.card_fin] at hrankNullity
    simpa only [K] using (show Module.finrank ℝ A.ker = n - q by omega)
  let m := Fintype.card I
  let eI : Fin m ≃ I := (Fintype.equivFin I).symm
  let eK : RealEuclidean (n - q) ≃L[ℝ] K :=
    ContinuousLinearEquiv.ofFinrankEq (by
      simpa only [Module.finrank_pi, Fintype.card_fin] using hKdim.symm)
  let EK : RealEuclidean (n - q) →ₗ[ℝ] RealEuclidean n :=
    K.subtype.comp eK.toLinearMap
  let M : Matrix (Fin m) (Fin (n - q)) ℝ :=
    fun i j ↦ B (eI i) (EK (Pi.single j 1))
  have hM_apply (z : RealEuclidean (n - q)) (i : Fin m) :
      M.mulVec z i = B (eI i) (EK z) := by
    let basis : Module.Basis (Fin (n - q)) ℝ
        (RealEuclidean (n - q)) := Pi.basisFun ℝ (Fin (n - q))
    have hz : (∑ j, z j • basis j) = z := by
      simpa only [basis, Pi.basisFun_repr] using basis.sum_repr z
    calc
      M.mulVec z i = ∑ j, B (eI i) (EK (basis j)) * z j := by
        simp only [M, Matrix.mulVec, dotProduct, basis, Pi.basisFun_apply]
      _ = B (eI i) (EK (∑ j, z j • basis j)) := by
        rw [map_sum, map_sum]
        simp only [map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = B (eI i) (EK z) := by rw [hz]
  let T : RealEuclidean (n - q) →ₗ[ℝ] RealEuclidean m := M.mulVecLin
  let J : T.ker →ₗ[ℝ] C.ker :=
    { toFun := fun z ↦ ⟨EK z.1, by
        change (A (EK z.1), (ContinuousLinearMap.pi B) (EK z.1)) = 0
        apply Prod.ext
        · exact (eK z.1).2
        · funext i
          have hz := congrFun z.2 (eI.symm i)
          change B i (EK z.1) = 0
          rw [← eI.apply_symm_apply i, ← hM_apply z.1 (eI.symm i)]
          simpa only [T, Matrix.mulVecLin_apply, Pi.zero_apply] using hz⟩
      map_add' := by
        intro u v
        apply Subtype.ext
        exact map_add EK u.1 v.1
      map_smul' := by
        intro c u
        apply Subtype.ext
        exact map_smul EK c u.1 }
  have hJinj : Function.Injective J := by
    intro u v huv
    apply Subtype.ext
    apply eK.injective
    apply Subtype.ext
    exact congrArg (fun w : C.ker ↦ w.1) huv
  have hkerT : Module.finrank ℝ T.ker ≤ p := by
    calc
      Module.finrank ℝ T.ker ≤ Module.finrank ℝ C.ker :=
        J.finrank_le_finrank_of_injective hJinj
      _ ≤ p := by simpa only [C] using hcommon
  have hrank : n - p - q ≤ M.rank := by
    have hrankNullity := T.finrank_range_add_finrank_ker
    have hrange : Module.finrank ℝ T.range = M.rank := by
      rfl
    rw [hrange, Module.finrank_pi, Fintype.card_fin] at hrankNullity
    omega
  obtain ⟨rows, cols, hminor⟩ :=
    (matrix_le_rank_iff_exists_square_minor_ne_zero M).mp hrank
  let selection : Fin (n - p - q) → I := fun j ↦ eI (rows j)
  let Bsel : RealEuclidean n →L[ℝ] RealEuclidean (n - p - q) :=
    selectedCovectorMap B selection
  let N : Matrix (Fin (n - p - q)) (Fin (n - q)) ℝ :=
    M.submatrix rows id
  have hNsurj : Function.Surjective N.mulVecLin :=
    (matrix_mulVecLin_surjective_iff_exists_column_minor_ne_zero N).mpr
      ⟨cols, by
        have heq : N.submatrix id cols = M.submatrix rows cols := by
          ext i j
          rfl
        rw [heq]
        exact hminor⟩
  have hBsel : Function.Surjective (Bsel.comp A.ker.subtypeL) := by
    intro target
    obtain ⟨z, hz⟩ := hNsurj target
    refine ⟨eK z, ?_⟩
    funext j
    have hzj := congrFun hz j
    change B (selection j) ((eK z : K) : RealEuclidean n) = target j
    calc
      B (selection j) ((eK z : K) : RealEuclidean n) =
          M.mulVec z (rows j) := by
            symm
            change M.mulVec z (rows j) =
              B (eI (rows j)) ((eK z : K) : RealEuclidean n)
            have hEK : EK z = ((eK z : K) : RealEuclidean n) := rfl
            rw [← hEK]
            exact hM_apply z (rows j)
      _ = N.mulVec z j := by rfl
      _ = target j := hzj
  refine ⟨selection, ?_⟩
  exact coordinateAppendContinuousLinearMap_surjective_of_restrictKer
    A Bsel hA hBsel

end AbelFormalization
