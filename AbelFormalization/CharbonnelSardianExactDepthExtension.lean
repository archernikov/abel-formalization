import AbelFormalization.CharbonnelSardianConstituents

/-!
# Replace unused-parameter padding by an exact-depth constituent

An old constituent with `q` hidden coordinates can be represented at every
depth `K ≥ q`: each trailing positive parameter is made equal to one new
hidden coordinate.  Its exact Sardian carrier is precisely the pre-existing
`charbonnelParameterPad` carrier.  This permits the same final equation slot
to be used when a finite family contains constituents of differing depths.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

/-- Retain the visible coordinates and the first `q` hidden coordinates. -/
def sardianExactDepthInputPrefix (n q K : ℕ) (hqK : q ≤ K) :
    RealEuclidean (n + K) →ₗ[ℝ] RealEuclidean (n + q) where
  toFun v := realEuclideanAppend (realEuclideanTakeLeft v)
    (fun i ↦ realEuclideanTakeRight v (Fin.castLE hqK i))
  map_add' := by
    intro v w
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  map_smul' := by
    intro c v
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]

@[simp]
theorem sardianExactDepthInputPrefix_append
    {n q K : ℕ} (hqK : q ≤ K)
    (x : RealEuclidean n) (y : RealEuclidean K) :
    sardianExactDepthInputPrefix n q K hqK
        (realEuclideanAppend x y) =
      realEuclideanAppend x (fun i ↦ y (Fin.castLE hqK i)) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
    simp [sardianExactDepthInputPrefix, realEuclideanAppend,
      realEuclideanTakeLeft, realEuclideanTakeRight]

/-- The new equations are the old equations on the prefix input, followed
by a coordinate equation for each added positive parameter. -/
def sardianExactDepthEquation
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    {order n q K : ℕ} (hqK : q ≤ K)
    (old : CharbonnelSardianConstituent G order n q)
    (i : Fin (K + 1)) : RealEuclideanFunction (n + K) :=
  if hi : i.val < q + 1 then
    fun v ↦ old.equation ⟨i.val, hi⟩
      (sardianExactDepthInputPrefix n q K hqK v)
  else
    fun v ↦ realEuclideanTakeRight v
      (⟨i.val - 1, by omega⟩ : Fin K)

theorem sardianExactDepthEquation_mem
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    {order n q K : ℕ} (hqK : q ≤ K)
    (old : CharbonnelSardianConstituent G order n q)
    (i : Fin (K + 1)) :
    sardianExactDepthEquation hqK old i ∈ G (n + K) := by
  by_cases hi : i.val < q + 1
  · have hpull := hG.affine_comp
      (old.equation_mem (⟨i.val, hi⟩ : Fin (q + 1)))
      (sardianExactDepthInputPrefix n q K hqK).toAffineMap
    change (fun v : RealEuclidean (n + K) ↦
      old.equation (⟨i.val, hi⟩ : Fin (q + 1))
        (sardianExactDepthInputPrefix n q K hqK v)) ∈ G (n + K) at hpull
    simpa only [sardianExactDepthEquation, dif_pos hi] using hpull
  · have hcoordinate := hG.polynomial
      (MvPolynomial.X (Fin.natAdd n
        (⟨i.val - 1, by omega⟩ : Fin K)))
    simpa [sardianExactDepthEquation, hi,
      realEuclideanTakeRight] using hcoordinate

/-- An exact-depth constituent whose new hidden coordinates reproduce the
old syntax's unused positive trailing parameters. -/
def sardianConstituentExactDepthExtension
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q K : ℕ} (hqK : q ≤ K)
    (old : CharbonnelSardianConstituent G order n q) :
    CharbonnelSardianConstituent G order n K := by
  let equations : Fin (K + 1) → RealEuclideanFunction (n + K) :=
    sardianExactDepthEquation hqK old
  have hequations : ∀ i, equations i ∈ G (n + K) :=
    fun i ↦ sardianExactDepthEquation_mem hG hqK old i
  exact {
    visible_pos := old.visible_pos
    equation := equations
    equation_mem := hequations
    equation_contDiff := fun i ↦
      (hsmooth (n + K) (equations i) (hequations i)).of_le
        (by simp)
  }

theorem sardianConstituentExactDepthExtension_equation_prefix
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q K : ℕ} (hqK : q ≤ K)
    (old : CharbonnelSardianConstituent G order n q)
    (i : Fin (q + 1)) (v : RealEuclidean (n + K)) :
    (sardianConstituentExactDepthExtension
      hG hsmooth hqK old).equation
        (Fin.castLE (Nat.succ_le_succ hqK) i) v =
      old.equation i (sardianExactDepthInputPrefix n q K hqK v) := by
  have hi : (Fin.castLE (Nat.succ_le_succ hqK) i).val < q + 1 := i.isLt
  simp only [sardianConstituentExactDepthExtension,
    sardianExactDepthEquation, dif_pos hi]
  rfl

theorem sardianConstituentExactDepthExtension_equation_trailing
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q K : ℕ} (hqK : q ≤ K)
    (old : CharbonnelSardianConstituent G order n q)
    (i : Fin (K + 1)) (hi : q + 1 ≤ i.val)
    (v : RealEuclidean (n + K)) :
    (sardianConstituentExactDepthExtension
      hG hsmooth hqK old).equation i v =
      realEuclideanTakeRight v
        (⟨i.val - 1, by omega⟩ : Fin K) := by
  have hnot : ¬ i.val < q + 1 := by omega
  simp only [sardianConstituentExactDepthExtension,
    sardianExactDepthEquation, dif_neg hnot]

/-- Fill the added hidden coordinates with the trailing parameter values. -/
def sardianExactDepthHiddenWitness
    {q K : ℕ} (hqK : q ≤ K)
    (y : RealEuclidean q) (ε : RealEuclidean (K + 1)) :
    RealEuclidean K :=
  fun j ↦ if hj : j.val < q then y ⟨j.val, hj⟩
    else ε ⟨j.val + 1, by omega⟩

@[simp]
theorem sardianExactDepthHiddenWitness_prefix
    {q K : ℕ} (hqK : q ≤ K)
    (y : RealEuclidean q) (ε : RealEuclidean (K + 1))
    (i : Fin q) :
    sardianExactDepthHiddenWitness hqK y ε (Fin.castLE hqK i) = y i := by
  have hi : (Fin.castLE hqK i).val < q := i.isLt
  simp only [sardianExactDepthHiddenWitness, dif_pos hi]
  rfl

theorem sardianExactDepthHiddenWitness_trailing
    {q K : ℕ} (hqK : q ≤ K)
    (y : RealEuclidean q) (ε : RealEuclidean (K + 1))
    (i : Fin (K + 1)) (hi : q + 1 ≤ i.val) :
    sardianExactDepthHiddenWitness hqK y ε
        (⟨i.val - 1, by omega⟩ : Fin K) = ε i := by
  have hnot : ¬ i.val - 1 < q := by omega
  simp only [sardianExactDepthHiddenWitness, dif_neg hnot]
  congr 1
  apply Fin.ext
  dsimp
  omega

/-- Exact-depth extension realizes the existing padded carrier, including
the old prefix positivity and positivity of every trailing parameter. -/
theorem mem_sardianConstituentExactDepthExtension_append_iff_pad
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q K : ℕ} (hqK : q ≤ K)
    (old : CharbonnelSardianConstituent G order n q)
    (x : RealEuclidean n) (ε : RealEuclidean (K + 1)) :
    realEuclideanAppend x ε ∈
        (sardianConstituentExactDepthExtension
          hG hsmooth hqK old).carrier ↔
      realEuclideanAppend x ε ∈
        charbonnelParameterPad hqK old.carrier := by
  rw [(sardianConstituentExactDepthExtension
    hG hsmooth hqK old).mem_carrier_iff,
    mem_charbonnelParameterPad_append_iff hqK,
    old.mem_carrier_iff]
  simp only [realEuclideanTakeLeft_append,
    realEuclideanTakeRight_append]
  constructor
  · rintro ⟨⟨yK, hyK⟩, hpositive⟩
    let yq : RealEuclidean q := fun i ↦ yK (Fin.castLE hqK i)
    refine ⟨⟨⟨yq, ?_⟩, ?_⟩, ?_⟩
    · intro i
      have hi := hyK (Fin.castLE (Nat.succ_le_succ hqK) i)
      rw [sardianConstituentExactDepthExtension_equation_prefix
        hG hsmooth hqK old i,
        sardianExactDepthInputPrefix_append] at hi
      exact hi
    · intro i
      exact hpositive (Fin.castLE (Nat.succ_le_succ hqK) i)
    · intro i _
      exact hpositive i
  · rintro ⟨⟨⟨yq, hyq⟩, hprefixPositive⟩, htrailingPositive⟩
    have hpositive : ∀ i : Fin (K + 1), 0 < ε i := by
      intro i
      by_cases hi : i.val < q + 1
      · let j : Fin (q + 1) := ⟨i.val, hi⟩
        have hj : Fin.castLE (Nat.succ_le_succ hqK) j = i := by
          apply Fin.ext
          rfl
        simpa only [hj] using hprefixPositive j
      · exact htrailingPositive i (by omega)
    let yK := sardianExactDepthHiddenWitness hqK yq ε
    refine ⟨⟨yK, ?_⟩, hpositive⟩
    intro i
    by_cases hi : i.val < q + 1
    · let j : Fin (q + 1) := ⟨i.val, hi⟩
      have hj : Fin.castLE (Nat.succ_le_succ hqK) j = i := by
        apply Fin.ext
        rfl
      have hinput :
          sardianExactDepthInputPrefix n q K hqK
              (realEuclideanAppend x yK) =
            realEuclideanAppend x yq := by
        rw [sardianExactDepthInputPrefix_append]
        congr 1
        funext t
        exact sardianExactDepthHiddenWitness_prefix hqK yq ε t
      rw [← hj, sardianConstituentExactDepthExtension_equation_prefix
        hG hsmooth hqK old j, hinput]
      exact hyq j
    · have htrail : q + 1 ≤ i.val := by omega
      rw [sardianConstituentExactDepthExtension_equation_trailing
        hG hsmooth hqK old i htrail]
      simp only [realEuclideanTakeRight_append]
      exact sardianExactDepthHiddenWitness_trailing hqK yq ε i htrail

theorem sardianConstituentExactDepthExtension_carrier_eq_pad
    {G : (d : ℕ) → Set (RealEuclideanFunction d)}
    (hG : IsGeometricFunctionFamily G)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    {order n q K : ℕ} (hqK : q ≤ K)
    (old : CharbonnelSardianConstituent G order n q) :
    (sardianConstituentExactDepthExtension
      hG hsmooth hqK old).carrier =
        charbonnelParameterPad hqK old.carrier := by
  ext v
  let x : RealEuclidean n := realEuclideanTakeLeft v
  let ε : RealEuclidean (K + 1) := realEuclideanTakeRight v
  have hv : v = realEuclideanAppend x ε := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
      simp [x, ε, realEuclideanAppend, realEuclideanTakeLeft,
        realEuclideanTakeRight]
  rw [hv]
  exact mem_sardianConstituentExactDepthExtension_append_iff_pad
    hG hsmooth hqK old x ε

end AbelFormalization
