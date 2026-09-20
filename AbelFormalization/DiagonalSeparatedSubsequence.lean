import AbelFormalization.RestrictedAllUnboundedBranchDichotomy
import Mathlib.Data.Nat.Nth

/-!
# A diagonal subsequence through decreasing infinite separation sets

The quantitative descent chooses its required separation rank only after a
finite preprocessing subsequence has been fixed.  To avoid interchanging
those two choices, this file first diagonalizes through all separation ranks.
For an antitone family of infinite subsets `Γ N` of the naturals, it builds a
strictly increasing `φ` with `φ n ∈ Γ n`.  Consequently every fixed `Γ N`
contains the tail of `φ`.
-/

noncomputable section
set_option autoImplicit false

open Filter Set
open scoped Topology

namespace AbelFormalization

/-- Recursively choose the next point in `Γ (n + 1)` above the point already
chosen at stage `n`. -/
def diagonalSubsequenceOfInfiniteSets
    (Γ : ℕ → Set ℕ) (hinfinite : ∀ N, (Γ N).Infinite) : ℕ → ℕ
  | 0 => Classical.choose (hinfinite 0).nonempty
  | n + 1 => Classical.choose
      ((hinfinite (n + 1)).exists_gt
        (diagonalSubsequenceOfInfiniteSets Γ hinfinite n))

theorem diagonalSubsequenceOfInfiniteSets_mem
    (Γ : ℕ → Set ℕ) (hinfinite : ∀ N, (Γ N).Infinite) (n : ℕ) :
    diagonalSubsequenceOfInfiniteSets Γ hinfinite n ∈ Γ n := by
  cases n with
  | zero =>
      exact Classical.choose_spec (hinfinite 0).nonempty
  | succ n =>
      exact (Classical.choose_spec
        ((hinfinite (n + 1)).exists_gt
          (diagonalSubsequenceOfInfiniteSets Γ hinfinite n))).1

theorem diagonalSubsequenceOfInfiniteSets_lt_succ
    (Γ : ℕ → Set ℕ) (hinfinite : ∀ N, (Γ N).Infinite) (n : ℕ) :
    diagonalSubsequenceOfInfiniteSets Γ hinfinite n <
      diagonalSubsequenceOfInfiniteSets Γ hinfinite (n + 1) := by
  exact (Classical.choose_spec
    ((hinfinite (n + 1)).exists_gt
      (diagonalSubsequenceOfInfiniteSets Γ hinfinite n))).2

theorem diagonalSubsequenceOfInfiniteSets_strictMono
    (Γ : ℕ → Set ℕ) (hinfinite : ∀ N, (Γ N).Infinite) :
    StrictMono (diagonalSubsequenceOfInfiniteSets Γ hinfinite) :=
  strictMono_nat_of_lt_succ
    (diagonalSubsequenceOfInfiniteSets_lt_succ Γ hinfinite)

/-- Antitonicity turns diagonal membership into eventual membership at every
fixed rank. -/
theorem eventually_diagonalSubsequenceOfInfiniteSets_mem
    (Γ : ℕ → Set ℕ) (hinfinite : ∀ N, (Γ N).Infinite)
    (hanti : Antitone Γ) (N : ℕ) :
    ∀ᶠ n in atTop,
      diagonalSubsequenceOfInfiniteSets Γ hinfinite n ∈ Γ N := by
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hanti hn (diagonalSubsequenceOfInfiniteSets_mem Γ hinfinite n)

/-- Increasing the rank makes the all-unbounded separation condition
stronger. -/
theorem IsAbel.restrictedAllUnboundedSeparationSet_antitone
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i))) :
    Antitone (restrictedAllUnboundedSeparationSet x data) := by
  intro N M hNM n hn
  intro c i hi j hj hij
  have hcast : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have harg :
      data.orderedClusterMinTime c n - (M : ℝ) ≤
        data.orderedClusterMinTime c n - (N : ℝ) := by
    linarith
  have hinverse :
      inverse A (data.orderedClusterMinTime c n - (M : ℝ)) ≤
        inverse A (data.orderedClusterMinTime c n - (N : ℝ)) :=
    hA.inverse_strictMono.monotone harg
  have hreciprocal :
      (inverse A (data.orderedClusterMinTime c n - (N : ℝ)))⁻¹ ≤
        (inverse A (data.orderedClusterMinTime c n - (M : ℝ)))⁻¹ :=
    (inv_le_inv₀
      (hA.inverse_pos
        (data.orderedClusterMinTime c n - (N : ℝ)))
      (hA.inverse_pos
        (data.orderedClusterMinTime c n - (M : ℝ)))).2 hinverse
  exact hreciprocal.trans (hn c i hi j hj hij)

/-- The canonical diagonal sequence for the separation sets of a normalized
all-unbounded setup. -/
def IsAbel.diagonalSeparatedSubsequence
    {A : ℝ → ℝ} (_hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite) : ℕ → ℕ :=
  diagonalSubsequenceOfInfiniteSets
    (restrictedAllUnboundedSeparationSet x data) hinfinite

theorem IsAbel.diagonalSeparatedSubsequence_strictMono
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite) :
    StrictMono (hA.diagonalSeparatedSubsequence x data hinfinite) :=
  diagonalSubsequenceOfInfiniteSets_strictMono _ hinfinite

theorem IsAbel.diagonalSeparatedSubsequence_eventually_mem
    {A : ℝ → ℝ} (hA : IsAbel A) {m p a : ℕ}
    (x : ℕ → RestrictedSource m p a)
    (data : RepresentativeClusterSubsequence
      (fun n i ↦ A ((x n).1.1 i)))
    (hinfinite : ∀ N,
      (restrictedAllUnboundedSeparationSet x data N).Infinite)
    (N : ℕ) :
    ∀ᶠ n in atTop,
      hA.diagonalSeparatedSubsequence x data hinfinite n ∈
        restrictedAllUnboundedSeparationSet x data N :=
  eventually_diagonalSubsequenceOfInfiniteSets_mem _ hinfinite
    (hA.restrictedAllUnboundedSeparationSet_antitone x data) N

end AbelFormalization
