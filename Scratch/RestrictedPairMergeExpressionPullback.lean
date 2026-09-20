import AbelFormalization.RestrictedPairMergeCoordinates
import AbelFormalization.ExponentialTowerPullback

/-!
# Expression pullback along the unbounded pair merge

The two nonlinear coordinate functions in `restrictedPairMergeSourceMap` are
finite iterates of `E x = exp x - 1`.  This file first packages one finite
`E`-orbit as an exponential tower, then concatenates towers.  The resulting
coordinate tower contains the pullback of every fixed generator.  Pulled-back
special generators are retained explicitly; this isolates the remaining Abel
jet transport problem from the purely exponential algebra.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## A finite tower generating one orbit of `E` -/

variable {X : Type*}

/-- Exponents whose successive exponentials generate the first `n` iterates
of `E` applied pointwise to `f`. -/
def iterateEExponents (f : X → ℝ) (n : ℕ) : Fin n → X → ℝ :=
  fun i x ↦ E^[i.val] (f x)

private theorem iterateE_mem_exponentialLevels
    (base : Subalgebra ℝ (X → ℝ)) (f : X → ℝ) (hf : f ∈ base)
    (n r : ℕ) (hr : r ≤ n) :
    (fun x ↦ E^[r] (f x)) ∈
      exponentialLevels base (iterateEExponents f n) r := by
  induction r with
  | zero =>
      change f ∈ base
      exact hf
  | succ r ih =>
      have hrn : r < n := Nat.lt_of_succ_le hr
      have hprev : (fun x ↦ E^[r] (f x)) ∈
          exponentialLevels base (iterateEExponents f n) r :=
        ih (Nat.le_of_lt hrn)
      have hstep : exponentialGenerator (iterateEExponents f n)
            ⟨r, hrn⟩ ∈
          exponentialLevels base (iterateEExponents f n) (r + 1) := by
        rw [exponentialLevels]
        apply (show Algebra.adjoin ℝ
            (exponentialStepGenerators (iterateEExponents f n) r) ≤
              exponentialLevels base (iterateEExponents f n) r ⊔
                Algebra.adjoin ℝ
                  (exponentialStepGenerators (iterateEExponents f n) r) from
            le_sup_right)
        apply Algebra.subset_adjoin
        exact ⟨hrn, rfl⟩
      have hone : (1 : X → ℝ) ∈
          exponentialLevels base (iterateEExponents f n) (r + 1) :=
        (exponentialLevels base (iterateEExponents f n) (r + 1)).one_mem
      have hsub := (exponentialLevels base
        (iterateEExponents f n) (r + 1)).sub_mem hstep hone
      convert hsub using 1
      funext x
      simp only [Pi.sub_apply, Pi.one_apply, exponentialGenerator,
        iterateEExponents, Function.iterate_succ_apply', E]

/-- The finite exponential tower which generates `f, E f, ..., E^[n] f`. -/
def iterateETower (base : Subalgebra ℝ (X → ℝ))
    (f : X → ℝ) (n : ℕ) (hf : f ∈ base) :
    FiniteExponentialTower base n where
  exponent := iterateEExponents f n
  exponent_mem_level i :=
    iterateE_mem_exponentialLevels base f hf n i.val (Nat.le_of_lt i.isLt)

/-- The terminal level of `iterateETower` contains the `n`th iterate. -/
theorem iterateE_mem_iterateETower_terminal
    (base : Subalgebra ℝ (X → ℝ)) (f : X → ℝ) (n : ℕ) (hf : f ∈ base) :
    (fun x ↦ E^[n] (f x)) ∈ (iterateETower base f n hf).level n :=
  iterateE_mem_exponentialLevels base f hf n n le_rfl

/-! ## Concatenating finite exponential towers -/

/-- Concatenate two exponent lists. -/
def appendExponents {l₁ l₂ : ℕ}
    (e₁ : Fin l₁ → X → ℝ) (e₂ : Fin l₂ → X → ℝ) :
    Fin (l₁ + l₂) → X → ℝ :=
  Fin.addCases e₁ e₂

private theorem exponentialStepGenerators_append_left
    {l₁ l₂ : ℕ} (e₁ : Fin l₁ → X → ℝ) (e₂ : Fin l₂ → X → ℝ)
    {r : ℕ} (hr : r < l₁) :
    exponentialStepGenerators (appendExponents e₁ e₂) r =
      exponentialStepGenerators e₁ r := by
  ext f
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨hr, ?_⟩
    have hi : (⟨r, h⟩ : Fin (l₁ + l₂)) = Fin.castAdd l₂ ⟨r, hr⟩ :=
      Fin.ext rfl
    rw [hi]
    funext x
    change Real.exp (Fin.addCases e₁ e₂ (Fin.castAdd l₂ ⟨r, hr⟩) x) =
      Real.exp (e₁ ⟨r, hr⟩ x)
    rw [Fin.addCases_left]
  · rintro ⟨h, rfl⟩
    have hsum : r < l₁ + l₂ := lt_of_lt_of_le h (Nat.le_add_right l₁ l₂)
    refine ⟨hsum, ?_⟩
    have hi : (⟨r, hsum⟩ : Fin (l₁ + l₂)) = Fin.castAdd l₂ ⟨r, h⟩ :=
      Fin.ext rfl
    rw [hi]
    funext x
    change Real.exp (e₁ ⟨r, h⟩ x) =
      Real.exp (Fin.addCases e₁ e₂ (Fin.castAdd l₂ ⟨r, h⟩) x)
    rw [Fin.addCases_left]

private theorem exponentialStepGenerators_append_right
    {l₁ l₂ : ℕ} (e₁ : Fin l₁ → X → ℝ) (e₂ : Fin l₂ → X → ℝ)
    (r : ℕ) :
    exponentialStepGenerators (appendExponents e₁ e₂) (l₁ + r) =
      exponentialStepGenerators e₂ r := by
  ext f
  constructor
  · rintro ⟨h, rfl⟩
    have hr : r < l₂ := by omega
    refine ⟨hr, ?_⟩
    have hi : (⟨l₁ + r, h⟩ : Fin (l₁ + l₂)) = Fin.natAdd l₁ ⟨r, hr⟩ :=
      Fin.ext rfl
    rw [hi]
    funext x
    change Real.exp (Fin.addCases e₁ e₂ (Fin.natAdd l₁ ⟨r, hr⟩) x) =
      Real.exp (e₂ ⟨r, hr⟩ x)
    rw [Fin.addCases_right]
  · rintro ⟨hr, rfl⟩
    have hsum : l₁ + r < l₁ + l₂ := Nat.add_lt_add_left hr l₁
    refine ⟨hsum, ?_⟩
    have hi : (⟨l₁ + r, hsum⟩ : Fin (l₁ + l₂)) =
        Fin.natAdd l₁ ⟨r, hr⟩ := Fin.ext rfl
    rw [hi]
    funext x
    change Real.exp (e₂ ⟨r, hr⟩ x) =
      Real.exp (Fin.addCases e₁ e₂ (Fin.natAdd l₁ ⟨r, hr⟩) x)
    rw [Fin.addCases_right]

private theorem exponentialLevels_append_left
    (base : Subalgebra ℝ (X → ℝ)) {l₁ l₂ : ℕ}
    (e₁ : Fin l₁ → X → ℝ) (e₂ : Fin l₂ → X → ℝ)
    (r : ℕ) (hr : r ≤ l₁) :
    exponentialLevels base (appendExponents e₁ e₂) r =
      exponentialLevels base e₁ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have hrlt : r < l₁ := Nat.lt_of_succ_le hr
      rw [exponentialLevels, exponentialLevels,
        ih (Nat.le_of_lt hrlt),
        exponentialStepGenerators_append_left e₁ e₂ hrlt]

private theorem exponentialLevels_append_right
    (base : Subalgebra ℝ (X → ℝ)) {l₁ l₂ : ℕ}
    (e₁ : Fin l₁ → X → ℝ) (e₂ : Fin l₂ → X → ℝ)
    (r : ℕ) :
    exponentialLevels base (appendExponents e₁ e₂) (l₁ + r) =
      exponentialLevels (exponentialLevels base e₁ l₁) e₂ r := by
  induction r with
  | zero =>
      rw [Nat.add_zero]
      change exponentialLevels base (appendExponents e₁ e₂) l₁ =
        exponentialLevels base e₁ l₁
      exact exponentialLevels_append_left base e₁ e₂ l₁ le_rfl
  | succ r ih =>
      rw [Nat.add_succ, exponentialLevels, exponentialLevels, ih,
        exponentialStepGenerators_append_right e₁ e₂ r]

/-- Append a tower over `base` to a tower whose base is the first terminal
level. -/
def FiniteExponentialTower.append
    {base : Subalgebra ℝ (X → ℝ)} {l₁ l₂ : ℕ}
    (T₁ : FiniteExponentialTower base l₁)
    (T₂ : FiniteExponentialTower (T₁.level l₁) l₂) :
    FiniteExponentialTower base (l₁ + l₂) where
  exponent := appendExponents T₁.exponent T₂.exponent
  exponent_mem_level i := by
    refine Fin.addCases (fun i₁ ↦ ?_) (fun i₂ ↦ ?_) i
    · simp only [appendExponents, Fin.addCases_left]
      rw [show (Fin.castAdd l₂ i₁).val = i₁.val from rfl]
      rw [exponentialLevels_append_left base T₁.exponent T₂.exponent
        i₁.val (Nat.le_of_lt i₁.isLt)]
      exact T₁.exponent_mem i₁
    · simp only [appendExponents, Fin.addCases_right]
      rw [show (Fin.natAdd l₁ i₂).val = l₁ + i₂.val from rfl]
      rw [exponentialLevels_append_right base T₁.exponent T₂.exponent i₂.val]
      exact T₂.exponent_mem i₂

/-- The first tower's levels are unchanged in the concatenation. -/
theorem FiniteExponentialTower.append_level_left
    {base : Subalgebra ℝ (X → ℝ)} {l₁ l₂ : ℕ}
    (T₁ : FiniteExponentialTower base l₁)
    (T₂ : FiniteExponentialTower (T₁.level l₁) l₂)
    (r : ℕ) (hr : r ≤ l₁) :
    (T₁.append T₂).level r = T₁.level r :=
  exponentialLevels_append_left base T₁.exponent T₂.exponent r hr

/-- After the first terminal level, concatenated levels are the levels of the
second tower. -/
theorem FiniteExponentialTower.append_level_right
    {base : Subalgebra ℝ (X → ℝ)} {l₁ l₂ : ℕ}
    (T₁ : FiniteExponentialTower base l₁)
    (T₂ : FiniteExponentialTower (T₁.level l₁) l₂)
    (r : ℕ) :
    (T₁.append T₂).level (l₁ + r) = T₂.level r :=
  exponentialLevels_append_right base T₁.exponent T₂.exponent r

end AbelFormalization

namespace AbelFormalization

/-! ## The coordinate tower for the pair merge -/

/-- The natural enlarged box for the new bounded difference coordinate. -/
def restrictedPairMergeBox {p : ℕ} (D : RestrictedBox p) :
    RestrictedBox (p + 1) :=
  D.snoc (-1) 1 (by norm_num)

/-- Keep exact pullbacks of the old special generators.  The theorems below
show that no additional special generators are needed for the old fixed
coordinates. -/
def restrictedPairMergePulledSpecialGenerators
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)) :
    Set (RestrictedSource (m + 1) (p + 1) a → ℝ) :=
  functionPrecompAlgHom (restrictedPairMergeSourceMap K k i j) '' S

/-- The retained pair coordinate `u`. -/
def restrictedPairMergeU {m p a : ℕ} (j : Fin (m + 1)) :
    RestrictedSource (m + 1) (p + 1) a → ℝ :=
  restrictedSCoordinate (p := p + 1) (a := a) j

/-- The second orbit starts at `u + xi`. -/
def restrictedPairMergeUXi {m p a : ℕ} (j : Fin (m + 1)) :
    RestrictedSource (m + 1) (p + 1) a → ℝ :=
  restrictedPairMergeU j +
    restrictedWCoordinate (m := m + 1) (a := a) (Fin.last p)

private theorem restrictedPairMergeU_mem_base
    {m p a : ℕ} {D : RestrictedBox p} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)) :
    restrictedPairMergeU (p := p) (a := a) j ∈
      restrictedExpressionBase (restrictedPairMergeBox D)
        (restrictedPairMergePulledSpecialGenerators K k i j S) :=
  restrictedSCoordinate_mem_base _ _ j

private theorem restrictedPairMergeUXi_mem_base
    {m p a : ℕ} {D : RestrictedBox p} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)) :
    restrictedPairMergeUXi (p := p) (a := a) j ∈
      restrictedExpressionBase (restrictedPairMergeBox D)
        (restrictedPairMergePulledSpecialGenerators K k i j S) := by
  apply (restrictedExpressionBase (restrictedPairMergeBox D)
    (restrictedPairMergePulledSpecialGenerators K k i j S)).add_mem
  · exact restrictedPairMergeU_mem_base K k i j S
  · exact restrictedWCoordinate_mem_base _ _ (Fin.last p)

/-- The first coordinate orbit `u, E u, ..., E^[K] u`. -/
def restrictedPairMergeFirstCoordinateTower
    {m p a : ℕ} (D : RestrictedBox p) (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)) :
    RestrictedExpressionTower (restrictedPairMergeBox D)
      (restrictedPairMergePulledSpecialGenerators K k i j S) (ell := K) :=
  iterateETower
    (restrictedExpressionBase (restrictedPairMergeBox D)
      (restrictedPairMergePulledSpecialGenerators K k i j S))
    (restrictedPairMergeU j) K
    (restrictedPairMergeU_mem_base K k i j S)

/-- The second coordinate orbit `u+xi, E(u+xi), ...` starts over the terminal
level of the first orbit. -/
def restrictedPairMergeSecondCoordinateTower
    {m p a : ℕ} (D : RestrictedBox p) (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)) :
    FiniteExponentialTower
      ((restrictedPairMergeFirstCoordinateTower D K k i j S).level K)
      (K + k) :=
  iterateETower
    ((restrictedPairMergeFirstCoordinateTower D K k i j S).level K)
    (restrictedPairMergeUXi j) (K + k)
    ((restrictedPairMergeFirstCoordinateTower D K k i j S).base_mem_level
      (restrictedPairMergeUXi_mem_base K k i j S) K)

/-- A fixed finite restricted-expression tower generating both nonlinear
coordinate functions of the pair merge. -/
def restrictedPairMergeCoordinateTower
    {m p a : ℕ} (D : RestrictedBox p) (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)) :
    RestrictedExpressionTower (restrictedPairMergeBox D)
      (restrictedPairMergePulledSpecialGenerators K k i j S)
      (ell := K + (K + k)) :=
  (restrictedPairMergeFirstCoordinateTower D K k i j S).append
    (restrictedPairMergeSecondCoordinateTower D K k i j S)

/-- The terminal coordinate level contains `E^[K] u`. -/
theorem restrictedPairMerge_firstOrbit_mem_coordinateTower_terminal
    {m p a : ℕ} (D : RestrictedBox p) (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)) :
    (fun x : RestrictedSource (m + 1) (p + 1) a ↦
        E^[K] (x.1.1 j)) ∈
      (restrictedPairMergeCoordinateTower D K k i j S).level
        (K + (K + k)) := by
  let T₁ := restrictedPairMergeFirstCoordinateTower D K k i j S
  let T₂ := restrictedPairMergeSecondCoordinateTower D K k i j S
  have hfirst : (fun x : RestrictedSource (m + 1) (p + 1) a ↦
      E^[K] (x.1.1 j)) ∈ T₁.level K := by
    exact iterateE_mem_iterateETower_terminal
      (restrictedExpressionBase (restrictedPairMergeBox D)
        (restrictedPairMergePulledSpecialGenerators K k i j S))
      (restrictedPairMergeU j) K
      (restrictedPairMergeU_mem_base K k i j S)
  have hsecond : (fun x : RestrictedSource (m + 1) (p + 1) a ↦
      E^[K] (x.1.1 j)) ∈ T₂.level (K + k) :=
    T₂.base_mem_level hfirst (K + k)
  change (fun x : RestrictedSource (m + 1) (p + 1) a ↦
      E^[K] (x.1.1 j)) ∈ (T₁.append T₂).level (K + (K + k))
  rw [T₁.append_level_right T₂ (K + k)]
  exact hsecond

/-- The terminal coordinate level contains `E^[K+k] (u+xi)`. -/
theorem restrictedPairMerge_secondOrbit_mem_coordinateTower_terminal
    {m p a : ℕ} (D : RestrictedBox p) (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)) :
    (fun x : RestrictedSource (m + 1) (p + 1) a ↦
        E^[K + k] (x.1.1 j + x.1.2 (Fin.last p))) ∈
      (restrictedPairMergeCoordinateTower D K k i j S).level
        (K + (K + k)) := by
  let T₁ := restrictedPairMergeFirstCoordinateTower D K k i j S
  let T₂ := restrictedPairMergeSecondCoordinateTower D K k i j S
  have hsecond : (fun x : RestrictedSource (m + 1) (p + 1) a ↦
      E^[K + k] (x.1.1 j + x.1.2 (Fin.last p))) ∈
      T₂.level (K + k) := by
    exact iterateE_mem_iterateETower_terminal
      (T₁.level K) (restrictedPairMergeUXi j) (K + k)
      (T₁.base_mem_level
        (restrictedPairMergeUXi_mem_base K k i j S) K)
  change (fun x : RestrictedSource (m + 1) (p + 1) a ↦
      E^[K + k] (x.1.1 j + x.1.2 (Fin.last p))) ∈
        (T₁.append T₂).level (K + (K + k))
  rw [T₁.append_level_right T₂ (K + k)]
  exact hsecond

end AbelFormalization

namespace AbelFormalization

/-! ## Pullback of the old base -/

@[simp]
theorem precomp_restrictedSCoordinate_pairMerge_pivot
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j)
        (restrictedSCoordinate (p := p) (a := a) i) =
      (fun x : RestrictedSource (m + 1) (p + 1) a ↦
        E^[K + k] (x.1.1 j + x.1.2 (Fin.last p))) := by
  funext x
  exact restrictedPairMergeSourceMap_pivot K k i j x

@[simp]
theorem precomp_restrictedSCoordinate_pairMerge_partner
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j)
        (restrictedSCoordinate (p := p) (a := a) (i.succAbove j)) =
      (fun x : RestrictedSource (m + 1) (p + 1) a ↦
        E^[K] (x.1.1 j)) := by
  funext x
  exact restrictedPairMergeSourceMap_partner K k i j x

@[simp]
theorem precomp_restrictedSCoordinate_pairMerge_other
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j r : Fin (m + 1)) (hr : r ≠ j) :
    functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j)
        (restrictedSCoordinate (p := p) (a := a) (i.succAbove r)) =
      restrictedSCoordinate (p := p + 1) (a := a) r := by
  funext x
  exact restrictedPairMergeSourceMap_other K k i j r hr x

@[simp]
theorem precomp_restrictedAuxCoordinate_pairMerge
    {m p a : ℕ} (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) (r : Fin a) :
    functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j)
        (restrictedAuxCoordinate (m := (m + 1) + 1) (p := p) r) =
      restrictedAuxCoordinate (m := m + 1) (p := p + 1) r := by
  funext x
  exact restrictedPairMergeSourceMap_aux K k i j x r

@[simp]
theorem precomp_restrictedBoxCoefficientPullback_pairMerge
    {m p a : ℕ} (D : RestrictedBox p) (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (f : RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j)
        (restrictedBoxCoefficientPullback (m := (m + 1) + 1) (a := a)
          (f : RestrictedBoxSpace p → ℝ)) =
      restrictedBoxCoefficientPullback (m := m + 1) (a := a)
        (D.pullbackSnoc (-1) 1 (by norm_num) f :
          RestrictedBoxSpace (p + 1) → ℝ) := by
  funext x
  change (f : RestrictedBoxSpace p → ℝ)
      (restrictedPairMergeSourceMap K k i j x).1.2 =
    (f : RestrictedBoxSpace p → ℝ) (restrictedBoxInitCLM p x.1.2)
  apply congrArg (f : RestrictedBoxSpace p → ℝ)
  funext r
  exact restrictedPairMergeSourceMap_box K k i j x r

/-- Every pulled-back fixed generator is generated by the explicit two-orbit
coordinate tower. -/
theorem image_restrictedFixedGenerators_pairMerge_subset_coordinateTerminal
    {m p a : ℕ} (D : RestrictedBox p) (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)) :
    functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j) ''
        restrictedFixedGenerators (m := (m + 1) + 1) (a := a) D ⊆
      (restrictedPairMergeCoordinateTower D K k i j S).level
        (K + (K + k)) := by
  rintro g ⟨f, hf, rfl⟩
  rcases hf with (hf | hf)
  · rcases hf with (⟨r, rfl⟩ | ⟨r, rfl⟩)
    · by_cases hri : r = i
      · subst r
        rw [precomp_restrictedSCoordinate_pairMerge_pivot]
        exact restrictedPairMerge_secondOrbit_mem_coordinateTower_terminal
          D K k i j S
      · obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hri
        by_cases hrj : r = j
        · subst r
          rw [precomp_restrictedSCoordinate_pairMerge_partner]
          exact restrictedPairMerge_firstOrbit_mem_coordinateTower_terminal
            D K k i j S
        · rw [precomp_restrictedSCoordinate_pairMerge_other K k i j r hrj]
          exact (restrictedPairMergeCoordinateTower D K k i j S).base_mem_level
            (restrictedSCoordinate_mem_base
              (restrictedPairMergeBox D)
              (restrictedPairMergePulledSpecialGenerators K k i j S) r)
            (K + (K + k))
    · rw [precomp_restrictedAuxCoordinate_pairMerge]
      exact (restrictedPairMergeCoordinateTower D K k i j S).base_mem_level
        (restrictedAuxCoordinate_mem_base
          (restrictedPairMergeBox D)
          (restrictedPairMergePulledSpecialGenerators K k i j S) r)
        (K + (K + k))
  · rcases hf with ⟨f, rfl⟩
    rw [precomp_restrictedBoxCoefficientPullback_pairMerge D K k i j]
    exact (restrictedPairMergeCoordinateTower D K k i j S).base_mem_level
      (restrictedBoxCoefficientPullback_mem_base
        (restrictedPairMergeBox D)
        (restrictedPairMergePulledSpecialGenerators K k i j S)
        (D.pullbackSnoc (-1) 1 (by norm_num) f))
      (K + (K + k))

/-- Pullback of the whole old restricted base lies in the terminal level of
the explicit coordinate tower. -/
theorem map_restrictedExpressionBase_pairMerge_le_coordinateTerminal
    {m p a : ℕ} (D : RestrictedBox p) (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)) :
    (restrictedExpressionBase D S).map
        (functionPrecompAlgHom
          (restrictedPairMergeSourceMap (p := p) (a := a) K k i j)) ≤
      (restrictedPairMergeCoordinateTower D K k i j S).level
        (K + (K + k)) := by
  rw [restrictedExpressionBase, AlgHom.map_adjoin]
  apply Algebra.adjoin_le
  rintro g ⟨f, hf, rfl⟩
  rcases hf with hf | hf
  · exact image_restrictedFixedGenerators_pairMerge_subset_coordinateTerminal
      D K k i j S ⟨f, hf, rfl⟩
  · exact (restrictedPairMergeCoordinateTower D K k i j S).base_mem_level
      (specialGenerator_mem_base (restrictedPairMergeBox D)
        (show functionPrecompAlgHom
            (restrictedPairMergeSourceMap (p := p) (a := a) K k i j) f ∈
          restrictedPairMergePulledSpecialGenerators K k i j S from
          ⟨f, hf, rfl⟩))
      (K + (K + k))

/-- Pointwise membership form for an old base expression. -/
theorem precomp_mem_coordinateTower_terminal_of_mem_restrictedExpressionBase
    {m p a : ℕ} (D : RestrictedBox p) (K k : ℕ)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ))
    {f : RestrictedSource ((m + 1) + 1) p a → ℝ}
    (hf : f ∈ restrictedExpressionBase D S) :
    functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j) f ∈
      (restrictedPairMergeCoordinateTower D K k i j S).level
        (K + (K + k)) := by
  apply map_restrictedExpressionBase_pairMerge_le_coordinateTerminal
    D K k i j S
  rw [Subalgebra.mem_map]
  exact ⟨f, hf, rfl⟩

end AbelFormalization

namespace AbelFormalization

/-! ## Pullback of an arbitrary old tower -/

/-- Pull the old exponent list through the pair merge, using the terminal
coordinate level as its enlarged base. -/
def restrictedPairMergeOldTowerAfterCoordinates
    {m p a ell : ℕ} (D : RestrictedBox p)
    {S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell))
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    FiniteExponentialTower
      ((restrictedPairMergeCoordinateTower D K k i j S).level
        (K + (K + k))) ell :=
  T.pullbackChangeBase
    (restrictedPairMergeSourceMap K k i j)
    ((restrictedPairMergeCoordinateTower D K k i j S).level
      (K + (K + k)))
    (map_restrictedExpressionBase_pairMerge_le_coordinateTerminal
      D K k i j S)

/-- The fixed enlarged restricted-expression tower: first generate both
coordinate iterates, then replay the pulled-back exponent list of `T`. -/
def restrictedPairMergeExpressionTower
    {m p a ell : ℕ} (D : RestrictedBox p)
    {S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell))
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    RestrictedExpressionTower (restrictedPairMergeBox D)
      (restrictedPairMergePulledSpecialGenerators K k i j S)
      (ell := (K + (K + k)) + ell) :=
  (restrictedPairMergeCoordinateTower D K k i j S).append
    (restrictedPairMergeOldTowerAfterCoordinates D T K k i j)

/-- Every old level-`q` expression, precomposed by the pair merge, belongs to
the enlarged tower at level `K + (K+k) + q`. -/
theorem RestrictedExpressionTower.precomp_mem_pairMerge_level
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell))
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    {q : ℕ} {f : RestrictedSource ((m + 1) + 1) p a → ℝ}
    (hf : f ∈ T.level q) :
    functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j) f ∈
      (restrictedPairMergeExpressionTower D T K k i j).level
        ((K + (K + k)) + q) := by
  let C := restrictedPairMergeCoordinateTower D K k i j S
  let U := restrictedPairMergeOldTowerAfterCoordinates D T K k i j
  have hu : functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j) f ∈
      U.level q := by
    exact T.precomp_mem_pullbackChangeBase_level
      (restrictedPairMergeSourceMap K k i j)
      (C.level (K + (K + k)))
      (map_restrictedExpressionBase_pairMerge_le_coordinateTerminal
        D K k i j S) hf
  change functionPrecompAlgHom
      (restrictedPairMergeSourceMap (p := p) (a := a) K k i j) f ∈
    (C.append U).level ((K + (K + k)) + q)
  rw [C.append_level_right U q]
  exact hu

/-- The reindexed square equation family from the maintained coordinate
module belongs componentwise to one fixed enlarged level. -/
theorem RestrictedExpressionTower.restrictedPairMergedEquationFamily_mem_level
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource ((m + 1) + 1) p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell))
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (q : ℕ)
    (F : Fin (((((m + 1) + 1) + p) + a)) →
      RestrictedSource ((m + 1) + 1) p a → ℝ)
    (hF : ∀ r, F r ∈ T.level q) :
    ∀ r, restrictedPairMergedEquationFamily K k i j F r ∈
      (restrictedPairMergeExpressionTower D T K k i j).level
        ((K + (K + k)) + q) := by
  intro r
  exact T.precomp_mem_pairMerge_level K k i j
    (hF ((restrictedReclassificationEquationIndexEquiv (m + 1) p a).symm r))

/-! ## Abel specialization and the exact remaining interface -/

variable {ι : Type*}

/-- Exact pulled-back Abel jets used by the theorem above. -/
def restrictedPairMergePulledAbelJetGenerators
    {A : ℝ → ℝ} {m p a : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    Set (RestrictedSource (m + 1) (p + 1) a → ℝ) :=
  restrictedPairMergePulledSpecialGenerators K k i j
    (restrictedAbelJetGenerators (a := a) A representative offset)

/-- Abel-specialized form: the algebraic and exponential part of pair merge
is complete once the exact pulled-back Abel jets are accepted as the target
special-generator family. -/
theorem RestrictedExpressionTower.precomp_mem_pairMerge_Abel_level
    {A : ℝ → ℝ} {m p a ell : ℕ} {D : RestrictedBox p}
    {representative : ι → Fin ((m + 1) + 1)}
    {offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D}
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell))
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    {q : ℕ} {f : RestrictedSource ((m + 1) + 1) p a → ℝ}
    (hf : f ∈ T.level q) :
    functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j) f ∈
      (restrictedPairMergeExpressionTower D T K k i j).level
        ((K + (K + k)) + q) :=
  T.precomp_mem_pairMerge_level K k i j hf

end AbelFormalization

namespace AbelFormalization

/-! ## Splitting the pulled Abel jets -/

/-- Old offset labels carried by a representative other than the two merged
slots. -/
abbrev RestrictedPairMergeOrdinaryOffsetIndex {m : ℕ}
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :=
  {q : RestrictedRetainedOffsetIndex representative i //
    restrictedReclassifiedRepresentative representative i q ≠ j}

/-- Old labels carried by the retained partner slot `i.succAbove j`. -/
abbrev RestrictedPairMergePartnerOffsetIndex {m : ℕ}
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :=
  {q : RestrictedRetainedOffsetIndex representative i //
    restrictedReclassifiedRepresentative representative i q = j}

/-- Target representative assignment for the ordinary, unwarped labels. -/
def restrictedPairMergeOrdinaryRepresentative {m : ℕ}
    (representative : ι → Fin ((m + 1) + 1))
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    RestrictedPairMergeOrdinaryOffsetIndex representative i j → Fin (m + 1) :=
  fun q ↦ restrictedReclassifiedRepresentative representative i q.1

/-- Ordinary offsets only forget the newly appended bounded coordinate. -/
def restrictedPairMergeOrdinaryOffset {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    RestrictedPairMergeOrdinaryOffsetIndex representative i j →
      RestrictedBox.analyticNearClosedBoxSubalgebra
        (restrictedPairMergeBox D) :=
  fun q ↦ D.pullbackSnoc (-1) 1 (by norm_num) (offset q.1.1)

/-- An ordinary old Abel jet is literally a standard Abel jet after pair
merge. -/
theorem precomp_restrictedAbelJet_pairMerge_ordinary
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (q : RestrictedPairMergeOrdinaryOffsetIndex representative i j)
    (r : ℕ) :
    functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j)
        (restrictedAbelJet A (representative q.1.1)
          (offset q.1.1 : RestrictedBoxSpace p → ℝ) r) =
      restrictedAbelJet A
        (restrictedPairMergeOrdinaryRepresentative representative i j q)
        (restrictedPairMergeOrdinaryOffset D representative offset i j q :
          RestrictedBoxSpace (p + 1) → ℝ) r := by
  funext x
  apply congrArg (iteratedDeriv r A)
  change
    (restrictedPairMergeSourceMap K k i j x).1.1 (representative q.1.1) +
        (offset q.1.1 : RestrictedBoxSpace p → ℝ)
          (restrictedPairMergeSourceMap K k i j x).1.2 =
      x.1.1 (restrictedReclassifiedRepresentative representative i q.1) +
        (offset q.1.1 : RestrictedBoxSpace p → ℝ)
          (restrictedBoxInitCLM p x.1.2)
  rw [← succAbove_restrictedReclassifiedRepresentative representative i q.1,
    restrictedPairMergeSourceMap_other K k i j
      (restrictedReclassifiedRepresentative representative i q.1) q.2]
  congr 1
  apply congrArg (offset q.1.1 : RestrictedBoxSpace p → ℝ)
  funext s
  exact restrictedPairMergeSourceMap_box K k i j x s

/-- The transformed pivot jet, displayed without hiding it as a pullback. -/
def restrictedPairMergePivotJet
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (j : Fin (m + 1))
    (q : ι) (r : ℕ) : RestrictedSource (m + 1) (p + 1) a → ℝ :=
  fun x ↦ iteratedDeriv r A
    (E^[K + k] (x.1.1 j + x.1.2 (Fin.last p)) +
      (offset q : RestrictedBoxSpace p → ℝ)
        (restrictedBoxInitCLM p x.1.2))

/-- The transformed retained-partner jet, displayed without hiding it as a
pullback. -/
def restrictedPairMergePartnerJet
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K : ℕ) (j : Fin (m + 1))
    (q : ι) (r : ℕ) : RestrictedSource (m + 1) (p + 1) a → ℝ :=
  fun x ↦ iteratedDeriv r A
    (E^[K] (x.1.1 j) +
      (offset q : RestrictedBoxSpace p → ℝ)
        (restrictedBoxInitCLM p x.1.2))

/-- Exact pivot-jet pullback formula. -/
theorem precomp_restrictedAbelJet_pairMerge_pivot
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (q : RestrictedPivotOffsetIndex representative i) (r : ℕ) :
    functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j)
        (restrictedAbelJet A (representative q.1)
          (offset q.1 : RestrictedBoxSpace p → ℝ) r) =
      restrictedPairMergePivotJet A D offset K k j q.1 r := by
  funext x
  apply congrArg (iteratedDeriv r A)
  change
    (restrictedPairMergeSourceMap K k i j x).1.1 (representative q.1) +
        (offset q.1 : RestrictedBoxSpace p → ℝ)
          (restrictedPairMergeSourceMap K k i j x).1.2 = _
  rw [q.2, restrictedPairMergeSourceMap_pivot]
  congr 1
  apply congrArg (offset q.1 : RestrictedBoxSpace p → ℝ)
  funext s
  exact restrictedPairMergeSourceMap_box K k i j x s

/-- Exact partner-jet pullback formula. -/
theorem precomp_restrictedAbelJet_pairMerge_partner
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1))
    (q : RestrictedPairMergePartnerOffsetIndex representative i j)
    (r : ℕ) :
    functionPrecompAlgHom
        (restrictedPairMergeSourceMap (p := p) (a := a) K k i j)
        (restrictedAbelJet A (representative q.1.1)
          (offset q.1.1 : RestrictedBoxSpace p → ℝ) r) =
      restrictedPairMergePartnerJet A D offset K j q.1.1 r := by
  funext x
  apply congrArg (iteratedDeriv r A)
  change
    (restrictedPairMergeSourceMap K k i j x).1.1 (representative q.1.1) +
        (offset q.1.1 : RestrictedBoxSpace p → ℝ)
          (restrictedPairMergeSourceMap K k i j x).1.2 = _
  rw [← succAbove_restrictedReclassifiedRepresentative representative i q.1,
    q.2, restrictedPairMergeSourceMap_partner]
  congr 1
  apply congrArg (offset q.1.1 : RestrictedBoxSpace p → ℝ)
  funext s
  exact restrictedPairMergeSourceMap_box K k i j x s

end AbelFormalization

namespace AbelFormalization

/-- Standard target Abel jets carried by representatives untouched by the
pair merge. -/
def restrictedPairMergeOrdinaryAbelJetGenerators
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    Set (RestrictedSource (m + 1) (p + 1) a → ℝ) :=
  restrictedAbelJetGenerators (a := a) A
    (restrictedPairMergeOrdinaryRepresentative representative i j)
    (restrictedPairMergeOrdinaryOffset D representative offset i j)

/-- Exceptional transformed jets from the deleted pivot slot. -/
def restrictedPairMergePivotJetGenerators
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    Set (RestrictedSource (m + 1) (p + 1) a → ℝ) :=
  Set.range fun qr : RestrictedPivotOffsetIndex representative i × ℕ ↦
    restrictedPairMergePivotJet A D offset K k j qr.1.1 qr.2

/-- Exceptional transformed jets from the retained partner slot. -/
def restrictedPairMergePartnerJetGenerators
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    Set (RestrictedSource (m + 1) (p + 1) a → ℝ) :=
  Set.range fun qr :
      RestrictedPairMergePartnerOffsetIndex representative i j × ℕ ↦
    restrictedPairMergePartnerJet A D offset K j qr.1.1.1 qr.2

/-- Exact classification of pulled Abel jets: ordinary labels become standard
target jets; only labels on the two merged representatives remain in the two
displayed exceptional families. -/
theorem restrictedPairMergePulledAbelJetGenerators_eq_split
    (A : ℝ → ℝ) {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin ((m + 1) + 1))
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (K k : ℕ) (i : Fin ((m + 1) + 1)) (j : Fin (m + 1)) :
    restrictedPairMergePulledAbelJetGenerators (A := A) (a := a)
        representative offset K k i j =
      (restrictedPairMergeOrdinaryAbelJetGenerators (a := a)
          A D representative offset i j ∪
        restrictedPairMergePivotJetGenerators (a := a)
          A D representative offset K k i j) ∪
      restrictedPairMergePartnerJetGenerators (a := a)
        A D representative offset K i j := by
  ext f
  constructor
  · rintro ⟨g, ⟨⟨q, r⟩, rfl⟩, rfl⟩
    by_cases hqi : representative q = i
    · refine Or.inl (Or.inr ?_)
      let qp : RestrictedPivotOffsetIndex representative i := ⟨q, hqi⟩
      refine ⟨(qp, r), ?_⟩
      exact (precomp_restrictedAbelJet_pairMerge_pivot
        A D representative offset K k i j qp r).symm
    · let qr : RestrictedRetainedOffsetIndex representative i := ⟨q, hqi⟩
      by_cases hqj :
          restrictedReclassifiedRepresentative representative i qr = j
      · refine Or.inr ?_
        let qp : RestrictedPairMergePartnerOffsetIndex representative i j :=
          ⟨qr, hqj⟩
        refine ⟨(qp, r), ?_⟩
        exact (precomp_restrictedAbelJet_pairMerge_partner
          A D representative offset K k i j qp r).symm
      · refine Or.inl (Or.inl ?_)
        let qo : RestrictedPairMergeOrdinaryOffsetIndex representative i j :=
          ⟨qr, hqj⟩
        refine ⟨(qo, r), ?_⟩
        exact (precomp_restrictedAbelJet_pairMerge_ordinary
          A D representative offset K k i j qo r).symm
  · rintro ((⟨⟨q, r⟩, rfl⟩ | ⟨⟨q, r⟩, rfl⟩) |
      ⟨⟨q, r⟩, rfl⟩)
    · refine ⟨restrictedAbelJet A (representative q.1.1)
          (offset q.1.1 : RestrictedBoxSpace p → ℝ) r,
        ⟨(q.1.1, r), rfl⟩, ?_⟩
      exact precomp_restrictedAbelJet_pairMerge_ordinary
        A D representative offset K k i j q r
    · refine ⟨restrictedAbelJet A (representative q.1)
          (offset q.1 : RestrictedBoxSpace p → ℝ) r,
        ⟨(q.1, r), rfl⟩, ?_⟩
      exact precomp_restrictedAbelJet_pairMerge_pivot
        A D representative offset K k i j q r
    · refine ⟨restrictedAbelJet A (representative q.1.1)
          (offset q.1.1 : RestrictedBoxSpace p → ℝ) r,
        ⟨(q.1.1, r), rfl⟩, ?_⟩
      exact precomp_restrictedAbelJet_pairMerge_partner
        A D representative offset K k i j q r

end AbelFormalization
