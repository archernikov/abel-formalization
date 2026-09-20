import AbelFormalization.SmoothGeometricFamily

/-!
# Projections of zero sets from a geometric family

This file packages the projected-zero class used in the smooth-family
criterion and proves its elementary lattice closure directly from the
geometric-family axioms.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Concatenate two finite real coordinate vectors. -/
def realEuclideanAppend {n q : ℕ}
    (x : RealEuclidean n) (z : RealEuclidean q) :
    RealEuclidean (n + q) :=
  Fin.addCases x z

@[simp]
theorem realEuclideanAppend_castAdd {n q : ℕ}
    (x : RealEuclidean n) (z : RealEuclidean q) (i : Fin n) :
    realEuclideanAppend x z (Fin.castAdd q i) = x i := by
  simp [realEuclideanAppend]

@[simp]
theorem realEuclideanAppend_natAdd {n q : ℕ}
    (x : RealEuclidean n) (z : RealEuclidean q) (j : Fin q) :
    realEuclideanAppend x z (Fin.natAdd n j) = z j := by
  simp [realEuclideanAppend]

@[simp]
theorem realEuclideanAppend_zero {n : ℕ}
    (x : RealEuclidean n) (z : RealEuclidean 0) :
    realEuclideanAppend x z = x := by
  funext i
  let j : Fin n := ⟨i.val, by omega⟩
  have hi : i = Fin.castAdd 0 j := Fin.ext rfl
  rw [hi]
  change Fin.addCases x z (Fin.castAdd 0 j) = x j
  exact Fin.addCases_left j

/-- From coordinates `(x,z,u)`, retain `(x,z)`. -/
def realEuclideanVisibleLeftWitnessLinearMap (n q r : ℕ) :
    RealEuclidean (n + (q + r)) →ₗ[ℝ] RealEuclidean (n + q) where
  toFun v := Fin.addCases
    (fun i ↦ v (Fin.castAdd (q + r) i))
    (fun j ↦ v (Fin.natAdd n (Fin.castAdd r j)))
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;> simp
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;> simp

/-- From coordinates `(x,z,u)`, retain `(x,u)`. -/
def realEuclideanVisibleRightWitnessLinearMap (n q r : ℕ) :
    RealEuclidean (n + (q + r)) →ₗ[ℝ] RealEuclidean (n + r) where
  toFun v := Fin.addCases
    (fun i ↦ v (Fin.castAdd (q + r) i))
    (fun k ↦ v (Fin.natAdd n (Fin.natAdd q k)))
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;> simp
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;> simp

@[simp]
theorem realEuclideanVisibleLeftWitnessLinearMap_append
    {n q r : ℕ} (x : RealEuclidean n) (z : RealEuclidean q)
    (u : RealEuclidean r) :
    realEuclideanVisibleLeftWitnessLinearMap n q r
        (realEuclideanAppend x (realEuclideanAppend z u)) =
      realEuclideanAppend x z := by
  funext k
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
    simp [realEuclideanVisibleLeftWitnessLinearMap]

@[simp]
theorem realEuclideanVisibleRightWitnessLinearMap_append
    {n q r : ℕ} (x : RealEuclidean n) (z : RealEuclidean q)
    (u : RealEuclidean r) :
    realEuclideanVisibleRightWitnessLinearMap n q r
        (realEuclideanAppend x (realEuclideanAppend z u)) =
      realEuclideanAppend x u := by
  funext k
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
    simp [realEuclideanVisibleRightWitnessLinearMap]

/-- A set is a coordinate projection of the zero set of one member of `G`. -/
def IsProjectedZeroSet
    (G : (n : ℕ) → Set (RealEuclideanFunction n))
    {n : ℕ} (s : Set (RealEuclidean n)) : Prop :=
  ∃ (q : ℕ) (f : RealEuclideanFunction (n + q)), f ∈ G (n + q) ∧
    s = {x | ∃ z : RealEuclidean q, f (realEuclideanAppend x z) = 0}

theorem isProjectedZeroSet_empty
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ} :
    IsProjectedZeroSet G (∅ : Set (RealEuclidean n)) := by
  refine ⟨0, (1 : RealEuclideanFunction (n + 0)), hG.one_mem, ?_⟩
  ext x
  simp

theorem isProjectedZeroSet_univ
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ} :
    IsProjectedZeroSet G (Set.univ : Set (RealEuclidean n)) := by
  refine ⟨0, (0 : RealEuclideanFunction (n + 0)), hG.zero_mem, ?_⟩
  ext x
  simp

theorem IsProjectedZeroSet.inter
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    {s t : Set (RealEuclidean n)}
    (hs : IsProjectedZeroSet G s) (ht : IsProjectedZeroSet G t) :
    IsProjectedZeroSet G (s ∩ t) := by
  obtain ⟨q, f, hf, rfl⟩ := hs
  obtain ⟨r, g, hg, rfl⟩ := ht
  let L := realEuclideanVisibleLeftWitnessLinearMap n q r
  let R := realEuclideanVisibleRightWitnessLinearMap n q r
  let F : RealEuclideanFunction (n + (q + r)) := f ∘ L
  let H : RealEuclideanFunction (n + (q + r)) := g ∘ R
  have hF : F ∈ G (n + (q + r)) := by
    exact hG.affine_comp hf L.toAffineMap
  have hH : H ∈ G (n + (q + r)) := by
    exact hG.affine_comp hg R.toAffineMap
  refine ⟨q + r, fun v ↦ F v ^ 2 + H v ^ 2,
    hG.add (hG.sq_mem hF) (hG.sq_mem hH), ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨z, hz⟩, ⟨u, hu⟩⟩
    refine ⟨realEuclideanAppend z u, ?_⟩
    simp [F, H, L, R, hz, hu]
  · rintro ⟨zu, hzu⟩
    let z : RealEuclidean q := fun j ↦ zu (Fin.castAdd r j)
    let u : RealEuclidean r := fun k ↦ zu (Fin.natAdd q k)
    have hzu' : zu = realEuclideanAppend z u := by
      funext k
      refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) k <;> simp [z, u]
    rw [hzu'] at hzu
    have hzero : F (realEuclideanAppend x (realEuclideanAppend z u)) = 0 ∧
        H (realEuclideanAppend x (realEuclideanAppend z u)) = 0 :=
      sq_add_sq_eq_zero.mp hzu
    refine ⟨⟨z, ?_⟩, ⟨u, ?_⟩⟩
    · simpa [F, L, Function.comp_apply] using hzero.1
    · simpa [H, R, Function.comp_apply] using hzero.2

theorem IsProjectedZeroSet.union
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    {s t : Set (RealEuclidean n)}
    (hs : IsProjectedZeroSet G s) (ht : IsProjectedZeroSet G t) :
    IsProjectedZeroSet G (s ∪ t) := by
  obtain ⟨q, f, hf, rfl⟩ := hs
  obtain ⟨r, g, hg, rfl⟩ := ht
  let L := realEuclideanVisibleLeftWitnessLinearMap n q r
  let R := realEuclideanVisibleRightWitnessLinearMap n q r
  let F : RealEuclideanFunction (n + (q + r)) := f ∘ L
  let H : RealEuclideanFunction (n + (q + r)) := g ∘ R
  have hF : F ∈ G (n + (q + r)) := by
    exact hG.affine_comp hf L.toAffineMap
  have hH : H ∈ G (n + (q + r)) := by
    exact hG.affine_comp hg R.toAffineMap
  refine ⟨q + r, fun v ↦ F v * H v, hG.mul hF hH, ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨z, hz⟩ | ⟨u, hu⟩)
    · refine ⟨realEuclideanAppend z 0, ?_⟩
      simp [F, H, L, R, hz]
    · refine ⟨realEuclideanAppend 0 u, ?_⟩
      simp [F, H, L, R, hu]
  · rintro ⟨zu, hzu⟩
    let z : RealEuclidean q := fun j ↦ zu (Fin.castAdd r j)
    let u : RealEuclidean r := fun k ↦ zu (Fin.natAdd q k)
    have hzu' : zu = realEuclideanAppend z u := by
      funext k
      refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) k <;> simp [z, u]
    rw [hzu'] at hzu
    rcases mul_eq_zero.mp hzu with hzero | hzero
    · exact Or.inl ⟨z, by simpa [F, L, Function.comp_apply] using hzero⟩
    · exact Or.inr ⟨u, by simpa [H, R, Function.comp_apply] using hzero⟩

/-! ## Products in flat coordinates -/

/-- The first block of a concatenated finite coordinate vector. -/
def realEuclideanTakeLeft {n m : ℕ}
    (v : RealEuclidean (n + m)) : RealEuclidean n :=
  fun i ↦ v (Fin.castAdd m i)

/-- The second block of a concatenated finite coordinate vector. -/
def realEuclideanTakeRight {n m : ℕ}
    (v : RealEuclidean (n + m)) : RealEuclidean m :=
  fun j ↦ v (Fin.natAdd n j)

@[simp]
theorem realEuclideanTakeLeft_append {n m : ℕ}
    (x : RealEuclidean n) (y : RealEuclidean m) :
    realEuclideanTakeLeft (realEuclideanAppend x y) = x := by
  funext i
  simp [realEuclideanTakeLeft]

@[simp]
theorem realEuclideanTakeRight_append {n m : ℕ}
    (x : RealEuclidean n) (y : RealEuclidean m) :
    realEuclideanTakeRight (realEuclideanAppend x y) = y := by
  funext j
  simp [realEuclideanTakeRight]

/-- Cartesian product of two sets, represented on one flat coordinate space. -/
def realEuclideanSetProduct {n m : ℕ}
    (s : Set (RealEuclidean n)) (t : Set (RealEuclidean m)) :
    Set (RealEuclidean (n + m)) :=
  {v | realEuclideanTakeLeft v ∈ s ∧ realEuclideanTakeRight v ∈ t}

/-- From flat coordinates `(x,y,z,u)`, retain `(x,z)`. -/
def realEuclideanProductLeftWitnessLinearMap (n m q r : ℕ) :
    RealEuclidean ((n + m) + (q + r)) →ₗ[ℝ]
      RealEuclidean (n + q) where
  toFun v := Fin.addCases
    (fun i ↦ v (Fin.castAdd (q + r) (Fin.castAdd m i)))
    (fun j ↦ v (Fin.natAdd (n + m) (Fin.castAdd r j)))
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;> simp
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;> simp

/-- From flat coordinates `(x,y,z,u)`, retain `(y,u)`. -/
def realEuclideanProductRightWitnessLinearMap (n m q r : ℕ) :
    RealEuclidean ((n + m) + (q + r)) →ₗ[ℝ]
      RealEuclidean (m + r) where
  toFun v := Fin.addCases
    (fun j ↦ v (Fin.castAdd (q + r) (Fin.natAdd n j)))
    (fun k ↦ v (Fin.natAdd (n + m) (Fin.natAdd q k)))
  map_add' := by
    intro v w
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;> simp
  map_smul' := by
    intro c v
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;> simp

@[simp]
theorem realEuclideanProductLeftWitnessLinearMap_append
    {n m q r : ℕ} (v : RealEuclidean (n + m))
    (z : RealEuclidean q) (u : RealEuclidean r) :
    realEuclideanProductLeftWitnessLinearMap n m q r
        (realEuclideanAppend v (realEuclideanAppend z u)) =
      realEuclideanAppend (realEuclideanTakeLeft v) z := by
  funext k
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
    simp [realEuclideanProductLeftWitnessLinearMap, realEuclideanTakeLeft]

@[simp]
theorem realEuclideanProductRightWitnessLinearMap_append
    {n m q r : ℕ} (v : RealEuclidean (n + m))
    (z : RealEuclidean q) (u : RealEuclidean r) :
    realEuclideanProductRightWitnessLinearMap n m q r
        (realEuclideanAppend v (realEuclideanAppend z u)) =
      realEuclideanAppend (realEuclideanTakeRight v) u := by
  funext k
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
    simp [realEuclideanProductRightWitnessLinearMap, realEuclideanTakeRight]

/-- Projected zero sets are closed under Cartesian products, after the
canonical flattening of visible and witness coordinates. -/
theorem IsProjectedZeroSet.prod
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n m : ℕ}
    {s : Set (RealEuclidean n)} {t : Set (RealEuclidean m)}
    (hs : IsProjectedZeroSet G s) (ht : IsProjectedZeroSet G t) :
    IsProjectedZeroSet G (realEuclideanSetProduct s t) := by
  obtain ⟨q, f, hf, rfl⟩ := hs
  obtain ⟨r, g, hg, rfl⟩ := ht
  let L := realEuclideanProductLeftWitnessLinearMap n m q r
  let R := realEuclideanProductRightWitnessLinearMap n m q r
  let F : RealEuclideanFunction ((n + m) + (q + r)) := f ∘ L
  let H : RealEuclideanFunction ((n + m) + (q + r)) := g ∘ R
  have hF : F ∈ G ((n + m) + (q + r)) :=
    hG.affine_comp hf L.toAffineMap
  have hH : H ∈ G ((n + m) + (q + r)) :=
    hG.affine_comp hg R.toAffineMap
  refine ⟨q + r, fun w ↦ F w ^ 2 + H w ^ 2,
    hG.add (hG.sq_mem hF) (hG.sq_mem hH), ?_⟩
  ext v
  simp only [realEuclideanSetProduct, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨z, hz⟩, ⟨u, hu⟩⟩
    refine ⟨realEuclideanAppend z u, ?_⟩
    simp [F, H, L, R, hz, hu]
  · rintro ⟨zu, hzu⟩
    let z : RealEuclidean q := fun j ↦ zu (Fin.castAdd r j)
    let u : RealEuclidean r := fun k ↦ zu (Fin.natAdd q k)
    have hzu' : zu = realEuclideanAppend z u := by
      funext k
      refine Fin.addCases (fun j ↦ ?_) (fun i ↦ ?_) k <;> simp [z, u]
    rw [hzu'] at hzu
    have hzero :
        F (realEuclideanAppend v (realEuclideanAppend z u)) = 0 ∧
          H (realEuclideanAppend v (realEuclideanAppend z u)) = 0 :=
      sq_add_sq_eq_zero.mp hzu
    refine ⟨⟨z, ?_⟩, ⟨u, ?_⟩⟩
    · simpa [F, L, Function.comp_apply] using hzero.1
    · simpa [H, R, Function.comp_apply] using hzero.2

/-! ## Invertible linear changes of visible coordinates -/

/-- Apply a linear map to the visible block and leave the witness block fixed. -/
def realEuclideanVisibleBlockLinearMap {n : ℕ}
    (e : RealEuclidean n →ₗ[ℝ] RealEuclidean n) (q : ℕ) :
    RealEuclidean (n + q) →ₗ[ℝ] RealEuclidean (n + q) where
  toFun v := realEuclideanAppend
    (e (realEuclideanTakeLeft v)) (realEuclideanTakeRight v)
  map_add' := by
    intro v w
    have hleft : realEuclideanTakeLeft (v + w) =
        realEuclideanTakeLeft v + realEuclideanTakeLeft w := by
      funext i
      rfl
    have hright : realEuclideanTakeRight (v + w) =
        realEuclideanTakeRight v + realEuclideanTakeRight w := by
      funext j
      rfl
    rw [hleft, hright, e.map_add]
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [realEuclideanAppend]
  map_smul' := by
    intro c v
    have hleft : realEuclideanTakeLeft (c • v) =
        c • realEuclideanTakeLeft v := by
      funext i
      rfl
    have hright : realEuclideanTakeRight (c • v) =
        c • realEuclideanTakeRight v := by
      funext j
      rfl
    rw [hleft, hright, e.map_smul]
    funext k
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k <;>
      simp [realEuclideanAppend]

@[simp]
theorem realEuclideanVisibleBlockLinearMap_append
    {n q : ℕ} (e : RealEuclidean n →ₗ[ℝ] RealEuclidean n)
    (x : RealEuclidean n) (z : RealEuclidean q) :
    realEuclideanVisibleBlockLinearMap e q (realEuclideanAppend x z) =
      realEuclideanAppend (e x) z := by
  simp [realEuclideanVisibleBlockLinearMap]

/-- Projected zero sets are preserved by every invertible linear change of
visible coordinates; coordinate permutations are a special case. -/
theorem IsProjectedZeroSet.linearEquiv_image
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G) {n : ℕ}
    {s : Set (RealEuclidean n)} (hs : IsProjectedZeroSet G s)
    (e : RealEuclidean n ≃ₗ[ℝ] RealEuclidean n) :
    IsProjectedZeroSet G (e '' s) := by
  obtain ⟨q, f, hf, rfl⟩ := hs
  let L := realEuclideanVisibleBlockLinearMap e.symm.toLinearMap q
  let F : RealEuclideanFunction (n + q) := f ∘ L
  have hF : F ∈ G (n + q) := hG.affine_comp hf L.toAffineMap
  refine ⟨q, F, hF, ?_⟩
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨z, hz⟩, rfl⟩
    refine ⟨z, ?_⟩
    simpa [F, L, Function.comp_apply] using hz
  · rintro ⟨z, hz⟩
    refine ⟨e.symm y, ⟨z, ?_⟩, e.apply_symm_apply y⟩
    simpa [F, L, Function.comp_apply] using hz

/-! ## Closed lifts and graphs -/

/-- A zero set of one family member is a projected zero set (with no added
witness coordinates). -/
theorem isProjectedZeroSet_zeroSet
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {n : ℕ} {f : RealEuclideanFunction n} (hf : f ∈ G n) :
    IsProjectedZeroSet G {x | f x = 0} := by
  refine ⟨0, f, ?_, ?_⟩
  · simpa using hf
  · ext x
    simp

/-- The precise closed-lift property needed for projected zero sets. -/
def HasClosedProjectedZeroLift
    (G : (n : ℕ) → Set (RealEuclideanFunction n))
    {n : ℕ} (s : Set (RealEuclidean n)) : Prop :=
  ∃ (q : ℕ) (B : Set (RealEuclidean (n + q))),
    IsClosed B ∧ IsProjectedZeroSet G B ∧
      s = {x | ∃ z : RealEuclidean q, realEuclideanAppend x z ∈ B}

/-- Global smoothness makes the defining zero set into the required closed
lift of every projected zero set. -/
theorem IsProjectedZeroSet.hasClosedLift
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {n : ℕ} {s : Set (RealEuclidean n)}
    (hs : IsProjectedZeroSet G s) :
    HasClosedProjectedZeroLift G s := by
  obtain ⟨q, f, hf, rfl⟩ := hs
  let B : Set (RealEuclidean (n + q)) := {v | f v = 0}
  refine ⟨q, B, ?_, isProjectedZeroSet_zeroSet hf, ?_⟩
  · exact isClosed_singleton.preimage (hsmooth (n + q) f hf).continuous
  · rfl

/-- Drop the last coordinate of a finite real coordinate vector. -/
def realEuclideanDropLastLinearMap (n : ℕ) :
    RealEuclidean (n + 1) →ₗ[ℝ] RealEuclidean n where
  toFun v i := v i.castSucc
  map_add' := by
    intro x y
    funext i
    rfl
  map_smul' := by
    intro c x
    funext i
    rfl

/-- The flat-coordinate graph of a scalar function. -/
def realEuclideanGraph {n : ℕ} (f : RealEuclideanFunction n) :
    Set (RealEuclidean (n + 1)) :=
  {v | f (realEuclideanDropLastLinearMap n v) = v (Fin.last n)}

/-- The graph of every family member is itself a projected zero set.  This is
the graph clause used in the all-orders differentiable-closure condition. -/
theorem IsGeometricFunctionFamily.isProjectedZeroSet_graph
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    {n : ℕ} {f : RealEuclideanFunction n} (hf : f ∈ G n) :
    IsProjectedZeroSet G (realEuclideanGraph f) := by
  let L := realEuclideanDropLastLinearMap n
  let F : RealEuclideanFunction (n + 1) := f ∘ L
  let Y : RealEuclideanFunction (n + 1) := fun v ↦ v (Fin.last n)
  have hF : F ∈ G (n + 1) := hG.affine_comp hf L.toAffineMap
  have hY : Y ∈ G (n + 1) := by
    simpa [Y] using hG.polynomial (MvPolynomial.X (Fin.last n))
  have hsub : F - Y ∈ G (n + 1) := hG.sub_mem hF hY
  rw [show realEuclideanGraph f = {v | (F - Y) v = 0} by
    ext v
    change (f (realEuclideanDropLastLinearMap n v) = v (Fin.last n)) ↔
      f (realEuclideanDropLastLinearMap n v) - v (Fin.last n) = 0
    exact sub_eq_zero.symm]
  exact isProjectedZeroSet_zeroSet hsub

end AbelFormalization
