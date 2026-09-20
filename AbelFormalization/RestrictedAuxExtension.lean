import AbelFormalization.ExponentialTowerPullback

/-!
# Adding unrestricted auxiliary variables

The restricted expression language permits arbitrarily many unrestricted
auxiliary coordinates.  This file embeds an expression base and an entire
finite exponential tower after adjoining a finite block of fresh auxiliary
variables.  Old functions are pulled back by forgetting the new block; all
new coordinates are available in the enlarged base.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Forget the last `k` unrestricted auxiliary coordinates. -/
def restrictedSourceDropAux {m p a : ℕ} (k : ℕ) :
    RestrictedSource m p (a + k) → RestrictedSource m p a :=
  fun x ↦ (x.1, fun i ↦ x.2 (Fin.castAdd k i))

@[simp]
theorem restrictedSourceDropAux_fst {m p a : ℕ} (k : ℕ)
    (x : RestrictedSource m p (a + k)) :
    (restrictedSourceDropAux k x).1 = x.1 :=
  rfl

@[simp]
theorem restrictedSourceDropAux_aux {m p a : ℕ} (k : ℕ)
    (x : RestrictedSource m p (a + k)) (i : Fin a) :
    (restrictedSourceDropAux k x).2 i = x.2 (Fin.castAdd k i) :=
  rfl

/-- Pull a set of special generators back after forgetting the fresh
auxiliary block. -/
def restrictedSpecialGeneratorsExtendAux {m p a : ℕ} (k : ℕ)
    (S : Set (RestrictedSource m p a → ℝ)) :
    Set (RestrictedSource m p (a + k) → ℝ) :=
  functionPrecompAlgHom (restrictedSourceDropAux k) '' S

theorem precomp_restrictedSCoordinate_dropAux {m p a : ℕ} (k : ℕ)
    (i : Fin m) :
    functionPrecompAlgHom (restrictedSourceDropAux k)
        (restrictedSCoordinate (p := p) (a := a) i) =
      restrictedSCoordinate (p := p) (a := a + k) i :=
  rfl

theorem precomp_restrictedWCoordinate_dropAux {m p a : ℕ} (k : ℕ)
    (i : Fin p) :
    functionPrecompAlgHom (restrictedSourceDropAux k)
        (restrictedWCoordinate (m := m) (a := a) i) =
      restrictedWCoordinate (m := m) (a := a + k) i :=
  rfl

theorem precomp_restrictedAuxCoordinate_dropAux {m p a : ℕ} (k : ℕ)
    (i : Fin a) :
    functionPrecompAlgHom (restrictedSourceDropAux k)
        (restrictedAuxCoordinate (m := m) (p := p) i) =
      restrictedAuxCoordinate (m := m) (p := p) (Fin.castAdd k i) :=
  rfl

theorem precomp_restrictedBoxCoefficientPullback_dropAux
    {m p a : ℕ} (k : ℕ) (f : RestrictedBoxSpace p → ℝ) :
    functionPrecompAlgHom (restrictedSourceDropAux k)
        (restrictedBoxCoefficientPullback (m := m) (a := a) f) =
      restrictedBoxCoefficientPullback (m := m) (a := a + k) f :=
  rfl

/-- Every fixed generator remains a fixed generator after auxiliary
extension. -/
theorem image_restrictedFixedGenerators_dropAux_subset
    {m p a : ℕ} (D : RestrictedBox p) (k : ℕ) :
    functionPrecompAlgHom (restrictedSourceDropAux k) ''
        restrictedFixedGenerators (m := m) (a := a) D ⊆
      restrictedFixedGenerators (m := m) (a := a + k) D := by
  rintro g ⟨f, hf, rfl⟩
  rcases hf with (hf | hf)
  · rcases hf with (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact Or.inl (Or.inl ⟨i, rfl⟩)
    · exact Or.inl (Or.inr ⟨Fin.castAdd k i, rfl⟩)
  · rcases hf with ⟨f, rfl⟩
    exact Or.inr ⟨f, rfl⟩

/-- Pullback of the old restricted expression base lies in the enlarged
base with the pulled-back special generators. -/
theorem map_restrictedExpressionBase_dropAux_le
    {m p a : ℕ} (D : RestrictedBox p) (k : ℕ)
    (S : Set (RestrictedSource m p a → ℝ)) :
    (restrictedExpressionBase D S).map
        (functionPrecompAlgHom (restrictedSourceDropAux k)) ≤
      restrictedExpressionBase D (restrictedSpecialGeneratorsExtendAux k S) := by
  rw [restrictedExpressionBase, AlgHom.map_adjoin]
  apply Algebra.adjoin_mono
  rintro g ⟨f, hf, rfl⟩
  rcases hf with hf | hf
  · exact Or.inl (image_restrictedFixedGenerators_dropAux_subset D k
      ⟨f, hf, rfl⟩)
  · exact Or.inr ⟨f, hf, rfl⟩

/-- Every old special generator, pulled back to the enlarged source, is in
the enlarged expression base. -/
theorem precomp_specialGenerator_mem_extendedBase
    {m p a : ℕ} (D : RestrictedBox p) (k : ℕ)
    {S : Set (RestrictedSource m p a → ℝ)}
    {f : RestrictedSource m p a → ℝ} (hf : f ∈ S) :
    functionPrecompAlgHom (restrictedSourceDropAux k) f ∈
      restrictedExpressionBase D (restrictedSpecialGeneratorsExtendAux k S) := by
  apply specialGenerator_mem_base D
  exact ⟨f, hf, rfl⟩

/-- The `j`th fresh auxiliary coordinate belongs to the enlarged base. -/
theorem freshAuxCoordinate_mem_extendedBase
    {m p a : ℕ} (D : RestrictedBox p) (k : ℕ) (j : Fin k)
    (S : Set (RestrictedSource m p a → ℝ)) :
    restrictedAuxCoordinate (m := m) (p := p) (Fin.natAdd a j) ∈
      restrictedExpressionBase D (restrictedSpecialGeneratorsExtendAux k S) :=
  restrictedAuxCoordinate_mem_base D _ (Fin.natAdd a j)

/-- Extend a restricted expression tower by a fresh block of unrestricted
auxiliary coordinates. -/
def RestrictedExpressionTower.extendAux
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (k : ℕ) :
    RestrictedExpressionTower D
      (restrictedSpecialGeneratorsExtendAux k S) (ell := ell) :=
  T.pullbackChangeBase (restrictedSourceDropAux k)
    (restrictedExpressionBase D (restrictedSpecialGeneratorsExtendAux k S))
    (map_restrictedExpressionBase_dropAux_le D k S)

/-- A function in an old tower level remains in the same level after adding
fresh unrestricted auxiliary coordinates. -/
theorem RestrictedExpressionTower.precomp_mem_extendAux_level
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (k : ℕ)
    {j : ℕ} {f : RestrictedSource m p a → ℝ} (hf : f ∈ T.level j) :
    functionPrecompAlgHom (restrictedSourceDropAux k) f ∈
      (T.extendAux k).level j :=
  T.precomp_mem_pullbackChangeBase_level
    (restrictedSourceDropAux k)
    (restrictedExpressionBase D (restrictedSpecialGeneratorsExtendAux k S))
    (map_restrictedExpressionBase_dropAux_le D k S) hf

@[simp]
theorem RestrictedExpressionTower.extendAux_exponent_apply
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (k : ℕ)
    (i : Fin ell) (x : RestrictedSource m p (a + k)) :
    (T.extendAux k).exponent i x =
      T.exponent i (restrictedSourceDropAux k x) :=
  rfl

@[simp]
theorem RestrictedExpressionTower.extendAux_generator_apply
    {m p a ell : ℕ} {D : RestrictedBox p}
    {S : Set (RestrictedSource m p a → ℝ)}
    (T : RestrictedExpressionTower D S (ell := ell)) (k : ℕ)
    (i : Fin ell) (x : RestrictedSource m p (a + k)) :
    (T.extendAux k).generator i x =
      T.generator i (restrictedSourceDropAux k x) :=
  rfl

end AbelFormalization
