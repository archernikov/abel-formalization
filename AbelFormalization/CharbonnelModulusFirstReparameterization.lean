import AbelFormalization.CharbonnelApproximationTrace

/-!
# Reparameterizing the first coordinate of a nested modulus

Wilkie's projection proof evaluates an old approximation twice: once at the
new error `epsilon_0`, and once at a smaller boundary-separation scale
`h(epsilon_0)`, while retaining the remaining parameters.  This file gives
the recursive modulus construction which makes both evaluations bounded.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Replace the first coordinate of a parameter vector by `phi` of that
coordinate, leaving every later coordinate unchanged. -/
def charbonnelReparameterizeFirst {k : ℕ} (phi : ℝ → ℝ)
    (epsilon : RealEuclidean (k + 1)) : RealEuclidean (k + 1) :=
  Fin.cases (phi (epsilon 0)) (fun i ↦ epsilon i.succ)

@[simp]
theorem charbonnelReparameterizeFirst_zero {k : ℕ} (phi : ℝ → ℝ)
    (epsilon : RealEuclidean (k + 1)) :
    charbonnelReparameterizeFirst phi epsilon 0 = phi (epsilon 0) := by
  simp [charbonnelReparameterizeFirst]

@[simp]
theorem charbonnelReparameterizeFirst_succ {k : ℕ} (phi : ℝ → ℝ)
    (epsilon : RealEuclidean (k + 1)) (i : Fin k) :
    charbonnelReparameterizeFirst phi epsilon i.succ = epsilon i.succ := by
  simp [charbonnelReparameterizeFirst]

theorem charbonnelReparameterizeFirst_pos {k : ℕ} (phi : ℝ → ℝ)
    (hphi : ∀ x : ℝ, 0 < x → 0 < phi x)
    {epsilon : RealEuclidean (k + 1)} (hepsilon : ∀ i, 0 < epsilon i) :
    ∀ i, 0 < charbonnelReparameterizeFirst phi epsilon i := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using hphi (epsilon 0) (hepsilon 0)
  · simpa using hepsilon j.succ

@[simp]
theorem charbonnelReparameterizeFirst_init {k : ℕ} (phi : ℝ → ℝ)
    (epsilon : RealEuclidean ((k + 1) + 1)) :
    Fin.init (charbonnelReparameterizeFirst phi epsilon) =
      charbonnelReparameterizeFirst phi (Fin.init epsilon) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;>
    simp [charbonnelReparameterizeFirst, Fin.init]

@[simp]
theorem charbonnelReparameterizeFirst_last {k : ℕ} (phi : ℝ → ℝ)
    (epsilon : RealEuclidean ((k + 1) + 1)) :
    charbonnelReparameterizeFirst phi epsilon (Fin.last (k + 1)) =
      epsilon (Fin.last (k + 1)) := by
  have hi : Fin.last (k + 1) = (Fin.last k).succ := Fin.ext rfl
  rw [hi]
  exact charbonnelReparameterizeFirst_succ phi epsilon (Fin.last k)

namespace CharbonnelModulus

/-- The bound on the first approximation-error coordinate. -/
def initialErrorBound : {k : ℕ} → CharbonnelModulus k → ℝ
  | 0, .base bound _ => bound
  | _ + 1, .step initial _ _ => initialErrorBound initial

theorem initialErrorBound_pos : ∀ {k : ℕ} (mu : CharbonnelModulus k),
    0 < mu.initialErrorBound := by
  intro k mu
  induction mu with
  | base bound hbound => simpa only [initialErrorBound] using hbound
  | step initial lastBound hlast ih =>
      simpa only [initialErrorBound] using ih

/-- Pull an old nested modulus back along a positive reparameterization of
its first coordinate.  The new first-coordinate bound is supplied
explicitly; later bounds are the old bounds evaluated at the transformed
prefix. -/
def pullbackFirst (phi : ℝ → ℝ)
    (hphi : ∀ x : ℝ, 0 < x → 0 < phi x)
    (newBound : ℝ) (hnewBound : 0 < newBound) :
    {k : ℕ} → CharbonnelModulus k → CharbonnelModulus k
  | 0, .base _ _ => .base newBound hnewBound
  | k + 1, .step initial lastBound hlast =>
      .step (pullbackFirst phi hphi newBound hnewBound initial)
        (fun epsilon ↦
          lastBound (charbonnelReparameterizeFirst phi epsilon))
        (fun epsilon hepsilon ↦
          hlast _ (charbonnelReparameterizeFirst_pos phi hphi hepsilon))

@[simp]
theorem initialErrorBound_pullbackFirst
    (phi : ℝ → ℝ) (hphi : ∀ x : ℝ, 0 < x → 0 < phi x)
    (newBound : ℝ) (hnewBound : 0 < newBound) :
    ∀ {k : ℕ} (old : CharbonnelModulus k),
      (pullbackFirst phi hphi newBound hnewBound old).initialErrorBound =
        newBound := by
  intro k old
  induction old with
  | base bound hbound => rfl
  | step initial lastBound hlast ih =>
      simpa only [pullbackFirst, initialErrorBound] using ih

/-- A bounded vector's first coordinate lies below the initial error bound
of its modulus. -/
theorem IsBounded.error_lt_initialErrorBound : ∀ {k : ℕ}
    {mu : CharbonnelModulus k} {epsilon : RealEuclidean (k + 1)},
    mu.IsBounded epsilon → epsilon 0 < mu.initialErrorBound := by
  intro k
  induction k with
  | zero =>
      intro mu epsilon hepsilon
      cases mu with
      | base bound hbound => exact hepsilon.2
  | succ k ih =>
      intro mu epsilon hepsilon
      cases mu with
      | step initial lastBound hlast =>
          have hzero : Fin.init epsilon 0 = epsilon 0 := rfl
          simpa only [initialErrorBound, hzero] using ih hepsilon.1

/-- Boundedness in the pullback modulus gives old boundedness after replacing
the first coordinate, provided that transformed coordinate lies below the
old initial bound. -/
theorem pullbackFirst_isBounded
    (phi : ℝ → ℝ) (hphi : ∀ x : ℝ, 0 < x → 0 < phi x)
    (newBound : ℝ) (hnewBound : 0 < newBound) :
    ∀ {k : ℕ} (old : CharbonnelModulus k)
      (epsilon : RealEuclidean (k + 1)),
      (pullbackFirst phi hphi newBound hnewBound old).IsBounded epsilon →
      phi (epsilon 0) < old.initialErrorBound →
        old.IsBounded (charbonnelReparameterizeFirst phi epsilon) := by
  intro k
  induction k with
  | zero =>
      intro old epsilon hepsilon hfirst
      cases old with
      | base bound hbound =>
          exact ⟨hphi _ hepsilon.1, hfirst⟩
  | succ k ih =>
      intro old epsilon hepsilon hfirst
      cases old with
      | step initial lastBound hlast =>
          refine ⟨?_, ?_, ?_⟩
          · rw [charbonnelReparameterizeFirst_init]
            apply ih initial (Fin.init epsilon) hepsilon.1
            have hzero : Fin.init epsilon 0 = epsilon 0 := rfl
            simpa only [initialErrorBound, hzero] using hfirst
          · simpa only [charbonnelReparameterizeFirst_last] using
              hepsilon.2.1
          · simpa only [pullbackFirst,
              charbonnelReparameterizeFirst_init,
              charbonnelReparameterizeFirst_last] using hepsilon.2.2

/-- Tighten a modulus so that both the original parameter vector and the
same vector with first coordinate `phi(epsilon_0)` are bounded for the old
modulus. -/
def commonWithFirstPullback
    (phi : ℝ → ℝ) (hphi : ∀ x : ℝ, 0 < x → 0 < phi x)
    (newBound : ℝ) (hnewBound : 0 < newBound)
    {k : ℕ} (old : CharbonnelModulus k) : CharbonnelModulus k :=
  infimum old (pullbackFirst phi hphi newBound hnewBound old)

theorem isBounded_commonWithFirstPullback
    (phi : ℝ → ℝ) (hphi : ∀ x : ℝ, 0 < x → 0 < phi x)
    (newBound : ℝ) (hnewBound : 0 < newBound)
    {k : ℕ} (old : CharbonnelModulus k)
    (hcontrol : ∀ x : ℝ, 0 < x → x < newBound →
      phi x < old.initialErrorBound)
    (epsilon : RealEuclidean (k + 1))
    (hepsilon :
      (commonWithFirstPullback phi hphi newBound hnewBound old).IsBounded
        epsilon) :
    old.IsBounded epsilon ∧
      old.IsBounded (charbonnelReparameterizeFirst phi epsilon) := by
  have hparts := (isBounded_infimum_iff old
    (pullbackFirst phi hphi newBound hnewBound old) epsilon).mp hepsilon
  refine ⟨hparts.1, ?_⟩
  apply pullbackFirst_isBounded phi hphi newBound hnewBound old epsilon
    hparts.2
  apply hcontrol (epsilon 0)
  · exact hparts.2.coord_pos 0
  · have hlt := hparts.2.error_lt_initialErrorBound
    simpa only [initialErrorBound_pullbackFirst] using hlt

end CharbonnelModulus

end AbelFormalization
