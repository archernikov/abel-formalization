import AbelFormalization.RestrictedAuxExtension

/-!
# Replacing the last exponential generator by a fresh variable

An expression in the successor level of a restricted exponential tower is a
polynomial in the newly adjoined exponential generator.  This file realizes
that polynomial on the restricted source with one additional unrestricted
coordinate and proves the exact substitution identity on the graph of the
generator.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Append one unrestricted auxiliary coordinate to a restricted source. -/
def restrictedSourceAppendAuxOne {m p a : ℕ}
    (x : RestrictedSource m p a) (y : ℝ) :
    RestrictedSource m p (a + 1) :=
  (x.1, Fin.append x.2 (fun _ : Fin 1 ↦ y))

@[simp]
theorem restrictedSourceAppendAuxOne_fst {m p a : ℕ}
    (x : RestrictedSource m p a) (y : ℝ) :
    (restrictedSourceAppendAuxOne x y).1 = x.1 :=
  rfl

@[simp]
theorem restrictedSourceAppendAuxOne_oldAux {m p a : ℕ}
    (x : RestrictedSource m p a) (y : ℝ) (i : Fin a) :
    (restrictedSourceAppendAuxOne x y).2 (Fin.castAdd 1 i) = x.2 i := by
  exact Fin.append_left x.2 (fun _ : Fin 1 ↦ y) i

@[simp]
theorem restrictedSourceAppendAuxOne_last {m p a : ℕ}
    (x : RestrictedSource m p a) (y : ℝ) :
    (restrictedSourceAppendAuxOne x y).2 (Fin.last a) = y := by
  have hlast : Fin.last a = Fin.natAdd a (0 : Fin 1) := by
    ext
    rfl
  rw [hlast]
  exact Fin.append_right x.2 (fun _ : Fin 1 ↦ y) 0

@[simp]
theorem restrictedSourceDropAux_appendAuxOne {m p a : ℕ}
    (x : RestrictedSource m p a) (y : ℝ) :
    restrictedSourceDropAux 1 (restrictedSourceAppendAuxOne x y) = x := by
  apply Prod.ext
  · rfl
  · funext i
    exact restrictedSourceAppendAuxOne_oldAux x y i

/-- Evaluate a polynomial over level `i` after replacing the `i`th
exponential generator by the final fresh auxiliary coordinate. -/
def restrictedLastAuxPolynomialLift
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (i : Fin ell)
    (P : Polynomial (T.level i.val)) :
    RestrictedSource m p (a + 1) → ℝ :=
  fun x ↦ graphPolynomialLift (T.level i.val) P
    (restrictedSourceDropAux 1 x, x.2 (Fin.last a))

/-- The polynomial lift belongs to the old tower level on the enlarged
source.  Its coefficients are pulled back from level `i`, while its variable
is the new unrestricted auxiliary coordinate. -/
theorem RestrictedExpressionTower.restrictedLastAuxPolynomialLift_mem
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (i : Fin ell)
    (P : Polynomial (T.level i.val)) :
    restrictedLastAuxPolynomialLift T i P ∈ (T.extendAux 1).level i.val := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      have hadd := ((T.extendAux 1).level i.val).add_mem hP hQ
      have heq : restrictedLastAuxPolynomialLift T i (P + Q) =
          restrictedLastAuxPolynomialLift T i P +
            restrictedLastAuxPolynomialLift T i Q := by
        funext x
        exact Polynomial.eval₂_add _ _
      rw [heq]
      exact hadd
  | monomial n b =>
      have hb : functionPrecompAlgHom (restrictedSourceDropAux 1)
          (b : RestrictedSource m p a → ℝ) ∈
          (T.extendAux 1).level i.val :=
        T.precomp_mem_extendAux_level 1 b.property
      have hyBase : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) ∈
          restrictedExpressionBase D
            (restrictedSpecialGeneratorsExtendAux 1 S) :=
        restrictedAuxCoordinate_mem_base D _ (Fin.last a)
      have hy : restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) ∈
          (T.extendAux 1).level i.val :=
        (T.extendAux 1).base_mem_level hyBase i.val
      have hmul := ((T.extendAux 1).level i.val).mul_mem hb
        (((T.extendAux 1).level i.val).pow_mem hy n)
      have heq :
          restrictedLastAuxPolynomialLift T i ((Polynomial.monomial n) b) =
            functionPrecompAlgHom (restrictedSourceDropAux 1)
                (b : RestrictedSource m p a → ℝ) *
              restrictedAuxCoordinate (m := m) (p := p) (Fin.last a) ^ n := by
        funext x
        simp [restrictedLastAuxPolynomialLift, graphPolynomialLift,
          Polynomial.eval₂_monomial, restrictedAuxCoordinate]
      rw [heq]
      exact hmul

/-- Appending a scalar and then evaluating the restricted lift agrees with
the abstract product-space polynomial lift. -/
theorem restrictedLastAuxPolynomialLift_appendAuxOne
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (i : Fin ell)
    (P : Polynomial (T.level i.val))
    (x : RestrictedSource m p a) (y : ℝ) :
    restrictedLastAuxPolynomialLift T i P
        (restrictedSourceAppendAuxOne x y) =
      graphPolynomialLift (T.level i.val) P (x, y) := by
  simp [restrictedLastAuxPolynomialLift]

/-- Exact substitution of the original exponential generator into the fresh
coordinate recovers polynomial evaluation in the original function ring. -/
theorem restrictedLastAuxPolynomialLift_on_generator
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (i : Fin ell)
    (P : Polynomial (T.level i.val)) (x : RestrictedSource m p a) :
    restrictedLastAuxPolynomialLift T i P
        (restrictedSourceAppendAuxOne x (T.generator i x)) =
      (Polynomial.aeval (T.generator i) P : RestrictedSource m p a → ℝ) x := by
  rw [restrictedLastAuxPolynomialLift_appendAuxOne,
    graphPolynomialLift_on_graph]

/-- Every expression in successor level `i+1` has a lift in level `i` after
adding one unrestricted coordinate, and substitution of the `i`th generator
into that coordinate recovers the original expression pointwise. -/
theorem RestrictedExpressionTower.exists_restrictedLastGeneratorLift_of_mem_level_succ
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (i : Fin ell)
    (f : RestrictedSource m p a → ℝ) (hf : f ∈ T.level (i.val + 1)) :
    ∃ F : RestrictedSource m p (a + 1) → ℝ,
      F ∈ (T.extendAux 1).level i.val ∧
        ∀ x, F (restrictedSourceAppendAuxOne x (T.generator i x)) = f x := by
  obtain ⟨P, _, hP⟩ := T.exists_graphPolynomialLift_of_mem_level_succ i f hf
  refine ⟨restrictedLastAuxPolynomialLift T i P,
    T.restrictedLastAuxPolynomialLift_mem i P, ?_⟩
  intro x
  rw [restrictedLastAuxPolynomialLift_appendAuxOne]
  exact hP x

end AbelFormalization
