import AbelFormalization.RestrictedBoundedReclassificationDomain
import AbelFormalization.RegularConstraintFiber
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Tactic.Omega

/-!
# Scratch: regular zeros under bounded-coordinate reclassification

This file isolates the two harmless coordinate changes in the bounded branch:
the source continuous linear equivalence and the reassociation of the finite
equation index.  The main generic lemma says that regular-zero sets commute
with continuous-linear equivalences on both sides of the equation map.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Generic transport of regular zeros -/

/-- Composing an equation map on the left and right with continuous linear
equivalences transports its regular-zero set by source preimage.  No
differentiability assumption is needed because the `fderiv` composition
formulas for equivalences also hold at nondifferentiability points. -/
theorem regularZeroSet_comp_continuousLinearEquiv_eq_preimage
    {E E' F F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (e : E' ≃L[ℝ] E) (q : F ≃L[ℝ] F')
    (Omega : Set E) (f : E → F) :
    regularZeroSet (e ⁻¹' Omega) (q ∘ f ∘ e) =
      e ⁻¹' regularZeroSet Omega f := by
  ext x
  simp only [regularZeroSet, Set.mem_setOf_eq, Set.mem_preimage]
  have hderiv :
      fderiv ℝ (q ∘ f ∘ e) x =
        (q : F →L[ℝ] F').comp
          ((fderiv ℝ f (e x)).comp (e : E' →L[ℝ] E)) := by
    rw [q.comp_fderiv, e.comp_right_fderiv]
  constructor
  · rintro ⟨hxOmega, hxzero, hxsurj⟩
    refine ⟨hxOmega, ?_, ?_⟩
    · apply q.injective
      simpa only [Function.comp_apply, map_zero] using hxzero
    · rw [hderiv] at hxsurj
      change Function.Surjective
        (fun y : E' ↦ q (fderiv ℝ f (e x) (e y))) at hxsurj
      intro y
      obtain ⟨z, hz⟩ := hxsurj (q y)
      exact ⟨e z, q.injective hz⟩
  · rintro ⟨hxOmega, hxzero, hxsurj⟩
    refine ⟨hxOmega, ?_, ?_⟩
    · simpa only [Function.comp_apply, map_zero] using congrArg q hxzero
    · rw [hderiv]
      change Function.Surjective
        (fun y : E' ↦ q (fderiv ℝ f (e x) (e y)))
      intro y'
      obtain ⟨y, hy⟩ := q.surjective y'
      obtain ⟨z, hz⟩ := hxsurj y
      refine ⟨e.symm z, ?_⟩
      simpa only [e.apply_symm_apply, hz] using hy

/-- The corresponding finiteness statement is an equivalence.  The reverse
direction uses surjectivity of the source equivalence, which is the direction
needed after applying the lower-representative-count induction hypothesis. -/
theorem finite_regularZeroSet_comp_continuousLinearEquiv_iff
    {E E' F F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (e : E' ≃L[ℝ] E) (q : F ≃L[ℝ] F')
    (Omega : Set E) (f : E → F) :
    (regularZeroSet (e ⁻¹' Omega) (q ∘ f ∘ e)).Finite ↔
      (regularZeroSet Omega f).Finite := by
  rw [regularZeroSet_comp_continuousLinearEquiv_eq_preimage]
  constructor
  · intro h
    exact Set.Finite.of_preimage h e.surjective
  · intro h
    exact Set.Finite.preimage e.injective.injOn h

/-! ## The finite equation-coordinate equivalence -/

/-- The two square-system equation counts in the old and reclassified source
are equal; only the association of addition differs. -/
theorem restrictedEquationCount_reclassify_eq (m p a : ℕ) :
    ((m + 1 + p) + a) = ((m + (p + 1)) + a) := by
  omega

/-- Reindex old equations as equations for the reclassified source. -/
def restrictedEquationIndexReclassifyEquiv (m p a : ℕ) :
    Fin ((m + 1 + p) + a) ≃ Fin ((m + (p + 1)) + a) :=
  finCongr (restrictedEquationCount_reclassify_eq m p a)

/-- The equation-coordinate reindexing as a continuous linear equivalence
between the two finite products of copies of `ℝ`. -/
def restrictedEquationReclassifyEquiv (m p a : ℕ) :
    (Fin ((m + 1 + p) + a) → ℝ) ≃L[ℝ]
      (Fin ((m + (p + 1)) + a) → ℝ) :=
  ContinuousLinearEquiv.piCongrLeft ℝ
    (fun _ : Fin ((m + (p + 1)) + a) ↦ ℝ)
    (restrictedEquationIndexReclassifyEquiv m p a)

/-- At an index transported from the old system, the equation reindexing is
literally evaluation at the old index. -/
@[simp]
theorem restrictedEquationReclassifyEquiv_apply_index
    (m p a : ℕ) (v : Fin ((m + 1 + p) + a) → ℝ)
    (k : Fin ((m + 1 + p) + a)) :
    restrictedEquationReclassifyEquiv m p a v
        (restrictedEquationIndexReclassifyEquiv m p a k) = v k := by
  change
    Equiv.piCongrLeft
        (fun _ : Fin ((m + (p + 1)) + a) ↦ ℝ)
        (restrictedEquationIndexReclassifyEquiv m p a) v
        (restrictedEquationIndexReclassifyEquiv m p a k) = v k
  exact Equiv.piCongrLeft_apply_apply
    (fun _ : Fin ((m + (p + 1)) + a) ↦ ℝ)
    (restrictedEquationIndexReclassifyEquiv m p a) v k

/-! ## Reclassified equation tuples -/

/-- Reclassify a square tuple of equations: first precompose every old
equation with the source equivalence, then transport the equation index to
the reassociated `Fin` type expected by the new source. -/
def restrictedConstraintTupleReclassifyAt
    {m p a : ℕ} (i : Fin (m + 1))
    (F : Fin ((m + 1 + p) + a) →
      RestrictedSource (m + 1) p a → ℝ) :
    Fin ((m + (p + 1)) + a) →
      RestrictedSource m (p + 1) a → ℝ :=
  fun j x ↦
    restrictedEquationReclassifyEquiv m p a
      (constraintMap F (restrictedSourceReclassifyAt i x)) j

/-- The equation tuple at a transported old index is exactly the pullback of
that old scalar equation. -/
@[simp]
theorem restrictedConstraintTupleReclassifyAt_apply_index
    {m p a : ℕ} (i : Fin (m + 1))
    (F : Fin ((m + 1 + p) + a) →
      RestrictedSource (m + 1) p a → ℝ)
    (k : Fin ((m + 1 + p) + a)) :
    restrictedConstraintTupleReclassifyAt i F
        (restrictedEquationIndexReclassifyEquiv m p a k) =
      functionPrecompAlgHom (restrictedSourceReclassifyAt i) (F k) := by
  funext x
  simp [restrictedConstraintTupleReclassifyAt, constraintMap]

/-- A convenient pointwise package for transporting tower-level membership
of every old equation to every equation in the reclassified tuple. -/
theorem restrictedConstraintTupleReclassifyAt_mem_set
    {m p a : ℕ} (i : Fin (m + 1))
    (F : Fin ((m + 1 + p) + a) →
      RestrictedSource (m + 1) p a → ℝ)
    (S : Set (RestrictedSource m (p + 1) a → ℝ))
    (hF : ∀ k,
      functionPrecompAlgHom (restrictedSourceReclassifyAt i) (F k) ∈ S) :
    ∀ j, restrictedConstraintTupleReclassifyAt i F j ∈ S := by
  intro j
  obtain ⟨k, rfl⟩ :=
    (restrictedEquationIndexReclassifyEquiv m p a).surjective j
  simpa using hF k

/-- The simultaneous map of the reclassified tuple is precisely the old
simultaneous map conjugated by the source and equation equivalences. -/
theorem constraintMap_restrictedConstraintTupleReclassifyAt
    {m p a : ℕ} (i : Fin (m + 1))
    (F : Fin ((m + 1 + p) + a) →
      RestrictedSource (m + 1) p a → ℝ) :
    constraintMap (restrictedConstraintTupleReclassifyAt i F) =
      restrictedEquationReclassifyEquiv m p a ∘
        constraintMap F ∘ restrictedSourceReclassifyAt i := by
  funext x j
  rfl

/-- Exact regular-zero-set transport for a reclassified square tuple. -/
theorem regularZeroSet_restrictedConstraintTupleReclassifyAt
    {m p a : ℕ} (i : Fin (m + 1))
    (F : Fin ((m + 1 + p) + a) →
      RestrictedSource (m + 1) p a → ℝ)
    (Omega : Set (RestrictedSource (m + 1) p a)) :
    regularZeroSet
        (restrictedSourceReclassifyAt i ⁻¹' Omega)
        (constraintMap (restrictedConstraintTupleReclassifyAt i F)) =
      restrictedSourceReclassifyAt i ⁻¹'
        regularZeroSet Omega (constraintMap F) := by
  rw [constraintMap_restrictedConstraintTupleReclassifyAt]
  exact regularZeroSet_comp_continuousLinearEquiv_eq_preimage
    (restrictedSourceReclassifyAt i)
    (restrictedEquationReclassifyEquiv m p a) Omega (constraintMap F)

/-- Finiteness of regular zeros is equivalent before and after
reclassification. -/
theorem finite_regularZeroSet_restrictedConstraintTupleReclassifyAt_iff
    {m p a : ℕ} (i : Fin (m + 1))
    (F : Fin ((m + 1 + p) + a) →
      RestrictedSource (m + 1) p a → ℝ)
    (Omega : Set (RestrictedSource (m + 1) p a)) :
    (regularZeroSet
        (restrictedSourceReclassifyAt i ⁻¹' Omega)
        (constraintMap (restrictedConstraintTupleReclassifyAt i F))).Finite ↔
      (regularZeroSet Omega (constraintMap F)).Finite := by
  rw [constraintMap_restrictedConstraintTupleReclassifyAt]
  exact finite_regularZeroSet_comp_continuousLinearEquiv_iff
    (restrictedSourceReclassifyAt i)
    (restrictedEquationReclassifyEquiv m p a) Omega (constraintMap F)

/-- The domain-specialized form used by the bounded slice of the outer
representative-count induction. -/
theorem finite_regularZeroSet_reclassifyAt_slice_iff
    {m p a : ℕ} (D : RestrictedBox p) (R M : ℝ) (hRM : R < M)
    (i : Fin (m + 1))
    (F : Fin ((m + 1 + p) + a) →
      RestrictedSource (m + 1) p a → ℝ) :
    (regularZeroSet
        (restrictedBaseOpenDomain (D.snoc R M hRM) R)
        (constraintMap (restrictedConstraintTupleReclassifyAt i F))).Finite ↔
      (regularZeroSet
        (restrictedBaseOpenDomain D R ∩ {x | x.1.1 i < M})
        (constraintMap F)).Finite := by
  rw [← preimage_restrictedBaseOpenDomain_slice_reclassifyAt
    D R M hRM i]
  exact finite_regularZeroSet_restrictedConstraintTupleReclassifyAt_iff
    i F (restrictedBaseOpenDomain D R ∩ {x | x.1.1 i < M})

end AbelFormalization
