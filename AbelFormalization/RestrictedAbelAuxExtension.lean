import AbelFormalization.DirectionalJacobian

/-!
# Auxiliary extension of shifted Abel-jet towers

Shifted Abel jets depend only on the representative and bounded-box
coordinates.  Pulling them back after adding auxiliary variables therefore
gives exactly the same Abel-jet generator family on the enlarged source.
This identifies the generic auxiliary extension with an Abel tower to which
the differentiation theorems apply directly.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

variable {ι : Type*}

theorem precomp_restrictedAbelJet_dropAux
    (A : ℝ → ℝ) {m p a : ℕ} (k : ℕ) (i : Fin m)
    (b : RestrictedBoxSpace p → ℝ) (r : ℕ) :
    functionPrecompAlgHom (restrictedSourceDropAux k)
        (restrictedAbelJet A (a := a) i b r) =
      restrictedAbelJet A (a := a + k) i b r := by
  rfl

/-- Pullback of all Abel-jet generators after adding auxiliaries is exactly
the Abel-jet generator set on the enlarged source. -/
theorem restrictedSpecialGeneratorsExtendAux_restrictedAbelJetGenerators
    (A : ℝ → ℝ) {m p a : ℕ} {D : RestrictedBox p} (k : ℕ)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D) :
    restrictedSpecialGeneratorsExtendAux k
        (restrictedAbelJetGenerators (a := a) A representative offset) =
      restrictedAbelJetGenerators (a := a + k) A representative offset := by
  ext f
  constructor
  · rintro ⟨g, ⟨kr, rfl⟩, rfl⟩
    exact ⟨kr, (precomp_restrictedAbelJet_dropAux A k
      (representative kr.1)
      (offset kr.1 : RestrictedBoxSpace p → ℝ) kr.2).symm⟩
  · rintro ⟨kr, rfl⟩
    refine ⟨restrictedAbelJet A (a := a) (representative kr.1)
      (offset kr.1 : RestrictedBoxSpace p → ℝ) kr.2, ⟨kr, rfl⟩, ?_⟩
    exact precomp_restrictedAbelJet_dropAux A k
      (representative kr.1)
      (offset kr.1 : RestrictedBoxSpace p → ℝ) kr.2

/-- Transport a finite exponential tower across equality of its base
subalgebra. -/
def FiniteExponentialTower.castBase
    {X : Type*} {base base' : Subalgebra ℝ (X → ℝ)} {ell : ℕ}
    (h : base = base') (T : FiniteExponentialTower base ell) :
    FiniteExponentialTower base' ell :=
  h ▸ T

@[simp]
theorem FiniteExponentialTower.castBase_exponent
    {X : Type*} {base base' : Subalgebra ℝ (X → ℝ)} {ell : ℕ}
    (h : base = base') (T : FiniteExponentialTower base ell) (i : Fin ell) :
    (T.castBase h).exponent i = T.exponent i := by
  subst base'
  rfl

@[simp]
theorem FiniteExponentialTower.castBase_level
    {X : Type*} {base base' : Subalgebra ℝ (X → ℝ)} {ell : ℕ}
    (h : base = base') (T : FiniteExponentialTower base ell) (j : ℕ) :
    (T.castBase h).level j = T.level j := by
  subst base'
  rfl

/-- The generic auxiliary extension of an Abel tower is definitionally an
Abel tower over the enlarged source after rewriting its generator set. -/
def RestrictedExpressionTower.extendAuxAbel
    (A : ℝ → ℝ) {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell)) (k : ℕ) :
    RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a + k) A representative offset)
      (ell := ell) where
  exponent := (T.extendAux k).exponent
  exponent_mem_level i := by
    rw [← restrictedSpecialGeneratorsExtendAux_restrictedAbelJetGenerators
      A k representative offset]
    exact (T.extendAux k).exponent_mem_level i

@[simp]
theorem RestrictedExpressionTower.extendAuxAbel_exponent_apply
    (A : ℝ → ℝ) {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell)) (k : ℕ) (i : Fin ell)
    (x : RestrictedSource m p (a + k)) :
    (T.extendAuxAbel A representative offset k).exponent i x =
      T.exponent i (restrictedSourceDropAux k x) := by
  rfl

@[simp]
theorem RestrictedExpressionTower.extendAuxAbel_generator_apply
    (A : ℝ → ℝ) {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell)) (k : ℕ) (i : Fin ell)
    (x : RestrictedSource m p (a + k)) :
    (T.extendAuxAbel A representative offset k).generator i x =
      T.generator i (restrictedSourceDropAux k x) := by
  rfl

/-- The levels of the Abel-typed auxiliary extension coincide with those of
the generic auxiliary extension. -/
theorem RestrictedExpressionTower.extendAuxAbel_level_eq_extendAux
    (A : ℝ → ℝ) {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell)) (k j : ℕ) :
    (T.extendAuxAbel A representative offset k).level j =
      (T.extendAux k).level j := by
  let exponent : Fin ell → RestrictedSource m p (a + k) → ℝ :=
    (T.extendAux k).exponent
  change exponentialLevels
      (restrictedExpressionBase D
        (restrictedAbelJetGenerators (a := a + k) A representative offset))
      exponent j =
    exponentialLevels
      (restrictedExpressionBase D
        (restrictedSpecialGeneratorsExtendAux k
          (restrictedAbelJetGenerators (a := a) A representative offset)))
      exponent j
  have hbase :
      restrictedExpressionBase D
          (restrictedSpecialGeneratorsExtendAux k
            (restrictedAbelJetGenerators (a := a) A representative offset)) =
        restrictedExpressionBase D
          (restrictedAbelJetGenerators (a := a + k) A representative offset) :=
    congrArg (restrictedExpressionBase D)
      (restrictedSpecialGeneratorsExtendAux_restrictedAbelJetGenerators
        A k representative offset)
  exact congrArg (fun B ↦ exponentialLevels B exponent j) hbase.symm

/-- Every level of an auxiliary-extended Abel tower retains the full
directional derivative closure on the enlarged positive-argument domain. -/
theorem IsAbel.extendAuxAbel_directionallyClosedOn_level
    {A : ℝ → ℝ} (hA : IsAbel A)
    {m p a ell : ℕ} {D : RestrictedBox p}
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (T : RestrictedExpressionTower D
      (restrictedAbelJetGenerators (a := a) A representative offset)
      (ell := ell)) (k : ℕ)
    (v : RestrictedSource m p (a + k)) (j : ℕ) :
    DirectionallyClosedOn
      ((T.extendAuxAbel A representative offset k).level j)
      (restrictedAbelJetDomain (a := a + k) D representative offset) v :=
  hA.restrictedAbelTower_directionallyClosedOn_level
    representative offset (T.extendAuxAbel A representative offset k) v j

end AbelFormalization
