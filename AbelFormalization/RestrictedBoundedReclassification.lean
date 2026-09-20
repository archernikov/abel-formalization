import AbelFormalization.RestrictedExpressionTower
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Scratch infrastructure for bounded-representative reclassification

This file appends one bounded interval to a restricted box and gives the
linear change of source coordinates which moves a chosen `s` coordinate into
that new final box coordinate.
-/

noncomputable section

open Set

namespace AbelFormalization

set_option autoImplicit false

namespace RestrictedBox

/-- Append one nondegenerate interval as the final coordinate of a restricted
box. -/
def snoc {p : ℕ} (D : RestrictedBox p) (l u : ℝ) (hlu : l < u) :
    RestrictedBox (p + 1) where
  lower := Fin.snoc D.lower l
  upper := Fin.snoc D.upper u
  lower_lt_upper := fun i ↦ by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using hlu
    · simpa using D.lower_lt_upper j

@[simp]
theorem mem_openBox_snoc {p : ℕ} (D : RestrictedBox p)
    {l u : ℝ} (hlu : l < u) {w : RestrictedBoxSpace (p + 1)} :
    w ∈ (D.snoc l u hlu).openBox ↔
      (fun j : Fin p ↦ w j.castSucc) ∈ D.openBox ∧
        l < w (Fin.last p) ∧ w (Fin.last p) < u := by
  constructor
  · intro hw
    rw [(D.snoc l u hlu).mem_openBox] at hw
    constructor
    · rw [D.mem_openBox]
      intro j
      simpa [snoc] using hw j.castSucc
    · simpa [snoc] using hw (Fin.last p)
  · rintro ⟨hw, hlast⟩
    rw [D.mem_openBox] at hw
    rw [(D.snoc l u hlu).mem_openBox]
    intro j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simpa [snoc] using hlast
    · simpa [snoc] using hw k

@[simp]
theorem mem_closedBox_snoc {p : ℕ} (D : RestrictedBox p)
    {l u : ℝ} (hlu : l < u) {w : RestrictedBoxSpace (p + 1)} :
    w ∈ (D.snoc l u hlu).closedBox ↔
      (fun j : Fin p ↦ w j.castSucc) ∈ D.closedBox ∧
        l ≤ w (Fin.last p) ∧ w (Fin.last p) ≤ u := by
  constructor
  · intro hw
    rw [(D.snoc l u hlu).mem_closedBox] at hw
    constructor
    · rw [D.mem_closedBox]
      intro j
      simpa [snoc] using hw j.castSucc
    · simpa [snoc] using hw (Fin.last p)
  · rintro ⟨hw, hlast⟩
    rw [D.mem_closedBox] at hw
    rw [(D.snoc l u hlu).mem_closedBox]
    intro j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simpa [snoc] using hlast
    · simpa [snoc] using hw k

end RestrictedBox

/-- The linear source reclassification which turns the chosen `s` coordinate
into the final bounded coordinate.  It is oriented from the reclassified
source to the original source, as needed for precomposition. -/
def restrictedSourceReclassifyAtLinearEquiv {m p a : ℕ}
    (i : Fin (m + 1)) :
    RestrictedSource m (p + 1) a ≃ₗ[ℝ] RestrictedSource (m + 1) p a where
  toFun x :=
    ((Fin.insertNth i (x.1.2 (Fin.last p)) x.1.1,
        fun j ↦ x.1.2 j.castSucc),
      x.2)
  invFun x :=
    (((fun j ↦ x.1.1 (i.succAbove j)),
        Fin.snoc x.1.2 (x.1.1 i)),
      x.2)
  left_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · funext j
        simp
      · funext j
        refine Fin.lastCases ?_ (fun k ↦ ?_) j <;> simp
    · rfl
  right_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · funext j
        refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j <;> simp
      · funext j
        simp
    · rfl
  map_add' x y := by
    apply Prod.ext
    · apply Prod.ext
      · funext j
        refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j <;> simp
      · funext j
        rfl
    · funext k
      rfl
  map_smul' c x := by
    apply Prod.ext
    · apply Prod.ext
      · funext j
        refine Fin.succAboveCases i ?_ (fun k ↦ ?_) j <;> simp
      · funext j
        rfl
    · funext k
      rfl

/-- Continuous-linear form of `restrictedSourceReclassifyAtLinearEquiv`.
All source spaces here are finite-dimensional real normed spaces. -/
def restrictedSourceReclassifyAt {m p a : ℕ} (i : Fin (m + 1)) :
    RestrictedSource m (p + 1) a ≃L[ℝ] RestrictedSource (m + 1) p a :=
  (restrictedSourceReclassifyAtLinearEquiv i).toContinuousLinearEquiv

@[simp]
theorem restrictedSourceReclassifyAt_apply_pivot {m p a : ℕ}
    (i : Fin (m + 1)) (x : RestrictedSource m (p + 1) a) :
    (restrictedSourceReclassifyAt i x).1.1 i =
      x.1.2 (Fin.last p) := by
  simp [restrictedSourceReclassifyAt,
    restrictedSourceReclassifyAtLinearEquiv]

@[simp]
theorem restrictedSourceReclassifyAt_apply_succAbove {m p a : ℕ}
    (i : Fin (m + 1)) (x : RestrictedSource m (p + 1) a) (j : Fin m) :
    (restrictedSourceReclassifyAt i x).1.1 (i.succAbove j) = x.1.1 j := by
  simp [restrictedSourceReclassifyAt,
    restrictedSourceReclassifyAtLinearEquiv]

@[simp]
theorem restrictedSourceReclassifyAt_apply_w {m p a : ℕ}
    (i : Fin (m + 1)) (x : RestrictedSource m (p + 1) a) (j : Fin p) :
    (restrictedSourceReclassifyAt i x).1.2 j = x.1.2 j.castSucc := by
  rfl

@[simp]
theorem restrictedSourceReclassifyAt_apply_aux {m p a : ℕ}
    (i : Fin (m + 1)) (x : RestrictedSource m (p + 1) a) (k : Fin a) :
    (restrictedSourceReclassifyAt i x).2 k = x.2 k := by
  rfl

end AbelFormalization
