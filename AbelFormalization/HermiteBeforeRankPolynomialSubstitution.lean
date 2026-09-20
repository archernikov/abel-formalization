import AbelFormalization.PaperRankFlatHermiteReindexing

/-!
# Hermite substitution before paper-rank elimination

This module turns a finite family of retained jet variables into explicit
Hermite polynomials before the rank-elimination step.  All representative
blocks are placed on the coefficient side of the split-cluster construction.
Currying therefore leaves an empty outer polynomial layer, which is removed
with `MvPolynomial.isEmptyAlgEquiv`.

The resulting flat Hermite operation ring is reindexed as a retained
paper-rank ring with `m * (D + 1)` central slots.  The substitution is then
extended across the auxiliary `Fin a` variables.  The final evaluation
theorems record the induced valuation on the original retained coordinates.
-/

noncomputable section
set_option autoImplicit false

namespace AbelFormalization

universe u

/-- Put every block on the coefficient side of a cluster split. -/
def paperRankAllCoefficientBlockEquiv (m : ℕ) :
    Fin m ≃ Fin 0 ⊕ Fin m :=
  (Equiv.emptySum (Fin 0) (Fin m)).symm

@[simp]
theorem paperRankAllCoefficientBlockEquiv_apply (m : ℕ) (i : Fin m) :
    paperRankAllCoefficientBlockEquiv m i = Sum.inr i :=
  rfl

/-- Curry a split Hermite polynomial with no active blocks and remove the
empty outer polynomial layer. -/
def emptyActiveSplitCurryHom
    (R : Type u) [CommSemiring R] (m D : ℕ) :
    MvPolynomial
        (SplitClusterBlockSymbol (Fin 0) (Fin m)
          (fun _ ↦ D) (fun _ ↦ D)) R →ₐ[R]
      MvPolynomial (ClusterOperationSymbol (Fin m) (fun _ ↦ D)) R :=
  let C := MvPolynomial (ClusterOperationSymbol (Fin m) (fun _ ↦ D)) R
  let ActiveSymbol := ClusterOperationSymbol (Fin 0) (fun _ ↦ D)
  ((MvPolynomial.isEmptyAlgEquiv C ActiveSymbol).toAlgHom.restrictScalars R).comp
    (splitClusterCurryAlgEquiv R (Fin 0) (Fin m)
      (fun _ ↦ D) (fun _ ↦ D)).toAlgHom

/-- Curry a Hermite blockification with no active blocks and then remove the
empty outer polynomial layer. -/
def paperRankAllCoefficientCurryHom
    (R : Type u) [CommSemiring R]
    {m b D : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ D) (fun _ ↦ D)) R) :
    MvPolynomial (PaperRankRetainedSymbols m b) R →ₐ[R]
      MvPolynomial (ClusterOperationSymbol (Fin m) (fun _ ↦ D)) R :=
  let C := MvPolynomial (ClusterOperationSymbol (Fin m) (fun _ ↦ D)) R
  let ActiveSymbol := ClusterOperationSymbol (Fin 0) (fun _ ↦ D)
  ((MvPolynomial.isEmptyAlgEquiv C ActiveSymbol).toAlgHom.restrictScalars R).comp
    (paperRankClusterCurryHom R (Fin 0) (Fin m)
      (fun _ ↦ D) (fun _ ↦ D)
      (paperRankAllCoefficientBlockEquiv m) jetPolynomial)

/-- Hermite-before-rank substitution on the retained variables: perform the
all-coefficient Hermite blockification, then express the resulting flat
operation polynomial in the full retained paper-rank coordinate ring. -/
def hermiteBeforeRankRetainedHom
    (R : Type u) [CommSemiring R]
    {m b D : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ D) (fun _ ↦ D)) R) :
    MvPolynomial (PaperRankRetainedSymbols m b) R →ₐ[R]
      MvPolynomial (PaperRankRetainedSymbols m (m * (D + 1))) R :=
  (paperRankRetainedFlatHermiteAlgEquiv R m D).symm.toAlgHom.comp
    (paperRankAllCoefficientCurryHom R jetPolynomial)

@[simp]
theorem paperRankAllCoefficientCurryHom_apply_X_free
    (R : Type u) [CommSemiring R]
    {m b D : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ D) (fun _ ↦ D)) R)
    (i : Fin m) :
    paperRankAllCoefficientCurryHom R jetPolynomial
        (MvPolynomial.X (Sum.inl i)) =
      MvPolynomial.X (Sum.inl i) := by
  simp [paperRankAllCoefficientCurryHom, paperRankClusterCurryHom,
    splitClusterCurryAlgEquiv, paperRankClusterBlockificationHom,
    paperRankAllCoefficientBlockEquiv, splitClusterBlockSymbolEquiv]

@[simp]
theorem paperRankAllCoefficientCurryHom_apply_X_jet
    (R : Type u) [CommSemiring R]
    {m b D : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ D) (fun _ ↦ D)) R)
    (j : Fin b) :
    paperRankAllCoefficientCurryHom R jetPolynomial
        (MvPolynomial.X (Sum.inr j)) =
      emptyActiveSplitCurryHom R m D (jetPolynomial j) := by
  simp [paperRankAllCoefficientCurryHom, emptyActiveSplitCurryHom,
    paperRankClusterCurryHom, paperRankClusterBlockificationHom]

@[simp]
theorem hermiteBeforeRankRetainedHom_apply_X_free
    (R : Type u) [CommSemiring R]
    {m b D : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ D) (fun _ ↦ D)) R)
    (i : Fin m) :
    hermiteBeforeRankRetainedHom R jetPolynomial
        (MvPolynomial.X (Sum.inl i)) =
      MvPolynomial.X (Sum.inl i) := by
  apply (paperRankRetainedFlatHermiteAlgEquiv R m D).injective
  simp [hermiteBeforeRankRetainedHom]

@[simp]
theorem hermiteBeforeRankRetainedHom_apply_X_jet
    (R : Type u) [CommSemiring R]
    {m b D : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ D) (fun _ ↦ D)) R)
    (j : Fin b) :
    hermiteBeforeRankRetainedHom R jetPolynomial
        (MvPolynomial.X (Sum.inr j)) =
      (paperRankRetainedFlatHermiteAlgEquiv R m D).symm
        (emptyActiveSplitCurryHom R m D (jetPolynomial j)) := by
  simp [hermiteBeforeRankRetainedHom]

/-- Extend a substitution on retained variables across an untouched auxiliary
variable family. -/
def extendRetainedPolynomialHom
    (R : Type u) [CommSemiring R]
    (Aux Old New : Type*)
    (f : MvPolynomial Old R →ₐ[R] MvPolynomial New R) :
    MvPolynomial (Aux ⊕ Old) R →ₐ[R] MvPolynomial (Aux ⊕ New) R :=
  MvPolynomial.aeval <| Sum.elim
    (fun i => MvPolynomial.X (Sum.inl i))
    (fun z => MvPolynomial.rename Sum.inr (f (MvPolynomial.X z)))

@[simp]
theorem extendRetainedPolynomialHom_apply_X_aux
    (R : Type u) [CommSemiring R]
    (Aux Old New : Type*)
    (f : MvPolynomial Old R →ₐ[R] MvPolynomial New R)
    (i : Aux) :
    extendRetainedPolynomialHom R Aux Old New f
        (MvPolynomial.X (Sum.inl i)) =
      MvPolynomial.X (Sum.inl i) := by
  simp [extendRetainedPolynomialHom]

@[simp]
theorem extendRetainedPolynomialHom_apply_X_retained
    (R : Type u) [CommSemiring R]
    (Aux Old New : Type*)
    (f : MvPolynomial Old R →ₐ[R] MvPolynomial New R)
    (z : Old) :
    extendRetainedPolynomialHom R Aux Old New f
        (MvPolynomial.X (Sum.inr z)) =
      MvPolynomial.rename Sum.inr (f (MvPolynomial.X z)) := by
  simp [extendRetainedPolynomialHom]

/-- Hermite-before-rank substitution on all paper-rank variables, leaving
the auxiliary `y` variables unchanged. -/
def hermiteBeforeRankPolynomialHom
    (R : Type u) [CommSemiring R]
    {a m b D : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ D) (fun _ ↦ D)) R) :
    MvPolynomial (PaperRankSymbols m a b) R →ₐ[R]
      MvPolynomial (PaperRankSymbols m a (m * (D + 1))) R :=
  extendRetainedPolynomialHom R (Fin a)
    (PaperRankRetainedSymbols m b)
    (PaperRankRetainedSymbols m (m * (D + 1)))
    (hermiteBeforeRankRetainedHom R jetPolynomial)

@[simp]
theorem hermiteBeforeRankPolynomialHom_apply_X_aux
    (R : Type u) [CommSemiring R]
    {a m b D : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ D) (fun _ ↦ D)) R)
    (i : Fin a) :
    hermiteBeforeRankPolynomialHom (a := a) R jetPolynomial
        (MvPolynomial.X (Sum.inl i)) =
      MvPolynomial.X (Sum.inl i) := by
  simp [hermiteBeforeRankPolynomialHom]

@[simp]
theorem hermiteBeforeRankPolynomialHom_apply_X_free
    (R : Type u) [CommSemiring R]
    {a m b D : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ D) (fun _ ↦ D)) R)
    (i : Fin m) :
    hermiteBeforeRankPolynomialHom (a := a) R jetPolynomial
        (MvPolynomial.X (Sum.inr (Sum.inl i))) =
      MvPolynomial.X (Sum.inr (Sum.inl i)) := by
  simp [hermiteBeforeRankPolynomialHom]

@[simp]
theorem hermiteBeforeRankPolynomialHom_apply_X_jet
    (R : Type u) [CommSemiring R]
    {a m b D : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ D) (fun _ ↦ D)) R)
    (j : Fin b) :
    hermiteBeforeRankPolynomialHom (a := a) R jetPolynomial
        (MvPolynomial.X (Sum.inr (Sum.inr j))) =
      MvPolynomial.rename
        (Sum.inr : PaperRankRetainedSymbols m (m * (D + 1)) →
          PaperRankSymbols m a (m * (D + 1)))
        ((paperRankRetainedFlatHermiteAlgEquiv R m D).symm
          (emptyActiveSplitCurryHom R m D (jetPolynomial j))) := by
  simp [hermiteBeforeRankPolynomialHom]

/-- Evaluation after extending a retained-variable substitution is evaluation
of the original polynomial at the induced old retained-variable values. -/
theorem eval₂Hom_extendRetainedPolynomialHom
    {R : Type u} {S : Type*} [CommSemiring R] [CommSemiring S]
    (c : R →+* S)
    (Aux Old New : Type*)
    (f : MvPolynomial Old R →ₐ[R] MvPolynomial New R)
    (auxValue : Aux → S) (newValue : New → S)
    (P : MvPolynomial (Aux ⊕ Old) R) :
    MvPolynomial.eval₂Hom c (Sum.elim auxValue newValue)
        (extendRetainedPolynomialHom R Aux Old New f P) =
      MvPolynomial.eval₂Hom c
        (Sum.elim auxValue
          (fun z => MvPolynomial.eval₂Hom c newValue
            (f (MvPolynomial.X z)))) P := by
  let lhs : MvPolynomial (Aux ⊕ Old) R →+* S :=
    (MvPolynomial.eval₂Hom c (Sum.elim auxValue newValue)).comp
      (extendRetainedPolynomialHom R Aux Old New f).toRingHom
  let rhs : MvPolynomial (Aux ⊕ Old) R →+* S :=
    MvPolynomial.eval₂Hom c
      (Sum.elim auxValue
        (fun z => MvPolynomial.eval₂Hom c newValue
          (f (MvPolynomial.X z))))
  change lhs P = rhs P
  apply DFunLike.congr_fun _ P
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [lhs, rhs, extendRetainedPolynomialHom]
  · rintro (i | z)
    · simp [lhs, rhs, extendRetainedPolynomialHom]
    · simp [lhs, rhs, extendRetainedPolynomialHom]
      rw [MvPolynomial.eval₂_rename]
      rfl

/-- Evaluation compatibility for the complete Hermite-before-rank
substitution on `PaperRankSymbols`. -/
theorem eval₂Hom_hermiteBeforeRankPolynomialHom
    {R : Type u} {S : Type*} [CommSemiring R] [CommSemiring S]
    (c : R →+* S)
    {a m b D : ℕ}
    (jetPolynomial : Fin b → MvPolynomial
      (SplitClusterBlockSymbol (Fin 0) (Fin m)
        (fun _ ↦ D) (fun _ ↦ D)) R)
    (auxValue : Fin a → S)
    (newValue : PaperRankRetainedSymbols m (m * (D + 1)) → S)
    (P : MvPolynomial (PaperRankSymbols m a b) R) :
    MvPolynomial.eval₂Hom c (Sum.elim auxValue newValue)
        (hermiteBeforeRankPolynomialHom R jetPolynomial P) =
      MvPolynomial.eval₂Hom c
        (Sum.elim auxValue
          (fun z => MvPolynomial.eval₂Hom c newValue
            (hermiteBeforeRankRetainedHom R jetPolynomial
              (MvPolynomial.X z)))) P := by
  exact eval₂Hom_extendRetainedPolynomialHom c
    (Fin a) (PaperRankRetainedSymbols m b)
    (PaperRankRetainedSymbols m (m * (D + 1)))
    (hermiteBeforeRankRetainedHom R jetPolynomial)
    auxValue newValue P

end AbelFormalization

