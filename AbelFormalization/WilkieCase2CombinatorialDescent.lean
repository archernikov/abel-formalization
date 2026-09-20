import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

/-!
# Wilkie Corollary 2.9, Case 2: the finite-exception descent

This mathlib-only module isolates the combinatorial induction in
Case 2 of Wilkie's proof.  If the visible image is infinite, at least one
visible coordinate has infinite image.  Consequently that coordinate has a
value attained on the fiber outside any finite set of exceptional values.
The attained-value clause matters: choosing only a value in the projection
of the open ball would not ensure that the sliced fiber is nonempty.

`case2_induction` packages the descent from `m + 1` visible coordinates to
`m`.  Its `sliceRel` premise is where a concrete application must record
coordinate insertion, a nonempty bounded regular sliced fiber, ball-slice
geometry, and transport of a selected minor back to the original fiber.
Those analytic and coordinate-transport statements are not inferred from
finite exceptional sets.  In the intended application, `hfinite` is Case 1,
`hterminal` supplies a hidden-column nonzero minor at zero visible arity,
and `hlift` transports a sliced certificate.  A final vertical-minor fork
turns that certificate into Corollary 2.9's alternative.

The only nontrivial source input represented here is the finiteness of each
exceptional unary set, supplied in the paper by Theorem 2.8.  This file
asserts no family membership or smooth selection theorem.
-/

namespace AbelFormalization

set_option autoImplicit false

universe u

/-- An infinite set of finite real tuples has an infinite image in at least
one coordinate.  This also covers `n = 0`: an infinite set of empty tuples
cannot exist. -/
theorem exists_infinite_coordinate_image
    {n : ℕ} {S : Set (Fin n → ℝ)} (hS : S.Infinite) :
    ∃ i : Fin n, ((fun v : Fin n → ℝ ↦ v i) '' S).Infinite := by
  classical
  by_contra hnone
  have hcoord (i : Fin n) :
      ((fun v : Fin n → ℝ ↦ v i) '' S).Finite := by
    by_contra hi
    exact hnone ⟨i, hi⟩
  have hproduct :
      {v : Fin n → ℝ |
        ∀ i, v i ∈ (fun w : Fin n → ℝ ↦ w i) '' S}.Finite :=
    Set.Finite.pi' hcoord
  apply hS
  exact hproduct.subset (by
    intro v hv i
    exact ⟨v, hv, rfl⟩)

/-- An infinite visible image contains a fiber point whose chosen visible
coordinate avoids the corresponding finite exceptional set.  The point
witness makes the later fixed-coordinate slice nonempty. -/
theorem exists_fiber_point_with_good_visible_coordinate
    {E : Type u} {n : ℕ} {X : Set E}
    (π : E → Fin n → ℝ)
    (hvisible : (π '' X).Infinite)
    (bad : Fin n → Set ℝ)
    (hbad : ∀ i, (bad i).Finite) :
    ∃ i : Fin n, ∃ x ∈ X, (π x) i ∉ bad i := by
  obtain ⟨i, hi⟩ :=
    exists_infinite_coordinate_image hvisible
  obtain ⟨b, hbImage, hbGood⟩ :=
    hi.exists_notMem_finite (hbad i)
  obtain ⟨v, hvImage, rfl⟩ := hbImage
  obtain ⟨x, hx, rfl⟩ := hvImage
  exact ⟨i, x, hx, hbGood⟩

/-- The Case 2 induction with its geometric slice construction kept as a
relation.  A state of arity `m` represents the original fiber after fixing
some visible coordinates.  `sliceRel` should retain all data needed to lift
either a Case 1 fixed-minor interval or the zero-arity hidden-minor seed.

The infinite branch always chooses `b` from the actual visible image, then
avoids the finite Theorem 2.8 exceptional set.  Thus `hslice` can require a
nonempty regular slice without adding an unsupported choice premise. -/
theorem case2_induction
    {State : ℕ → Type u}
    (visible : ∀ m, State m → Set (Fin m → ℝ))
    (bad : ∀ m, State (m + 1) → Fin (m + 1) → Set ℝ)
    (sliceRel : ∀ m, State (m + 1) → Fin (m + 1) → ℝ →
      State m → Prop)
    (outcome : ∀ m, State m → Prop)
    (hterminal : ∀ s : State 0, outcome 0 s)
    (hfinite : ∀ m (s : State (m + 1)),
      (visible (m + 1) s).Finite → outcome (m + 1) s)
    (hbad : ∀ m (s : State (m + 1)) (i : Fin (m + 1)),
      (bad m s i).Finite)
    (hslice : ∀ m (s : State (m + 1)) (i : Fin (m + 1)) (b : ℝ),
      b ∈ (fun v : Fin (m + 1) → ℝ ↦ v i) ''
        visible (m + 1) s →
      b ∉ bad m s i →
      ∃ s' : State m, sliceRel m s i b s')
    (hlift : ∀ m (s : State (m + 1)) (i : Fin (m + 1))
      (b : ℝ) (s' : State m),
      sliceRel m s i b s' → outcome m s' →
      outcome (m + 1) s) :
    ∀ m (s : State m), outcome m s := by
  intro m
  induction m with
  | zero =>
      intro s
      exact hterminal s
  | succ m ih =>
      intro s
      by_cases hfin : (visible (m + 1) s).Finite
      · exact hfinite m s hfin
      · have hinf : (visible (m + 1) s).Infinite := hfin
        obtain ⟨i, hi⟩ :=
          exists_infinite_coordinate_image hinf
        obtain ⟨b, hbImage, hbGood⟩ :=
          hi.exists_notMem_finite (hbad m s i)
        obtain ⟨s', hs'⟩ :=
          hslice m s i b hbImage hbGood
        exact hlift m s i b s' hs' (ih s')

end AbelFormalization
