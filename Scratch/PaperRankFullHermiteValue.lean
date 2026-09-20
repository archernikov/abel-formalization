import AbelFormalization.HermiteBeforeRankPolynomialSubstitution
import AbelFormalization.CommonStripHermiteRealAnalytic
import AbelFormalization.RestrictedHermiteJetBlockification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace AbelFormalization

open Set
open scoped Topology

variable {ι : Type*}

/-- The retained `s` and complete Hermite coefficient assignment in the flat
coordinate order used by rank elimination. -/
def paperRankFullHermiteRetainedValue
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) :
    PaperRankRetainedSymbols m
      (m * (paperRankHermitePositiveDerivativeCount S + 1)) → ℝ :=
  fun z =>
    paperRankHermiteCoefficientBlockValue D representative offset S
      (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
      B (fun _ => F) sw
      (paperRankRetainedFlatHermiteEquiv m
        (paperRankHermitePositiveDerivativeCount S) z)

/-- The smooth-coordinate part of the complete Hermite assignment. -/
def paperRankFullHermiteSmoothValue
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    (B : ℝ) (F : ℂ → ℂ) :
    PaperRankParameterSpace m p →
      PaperRankRealSpace
        (m * (paperRankHermitePositiveDerivativeCount S + 1)) :=
  fun sw j => paperRankFullHermiteRetainedValue D representative offset S B F sw
    (Sum.inr j)

@[simp] theorem paperRankFullHermiteRetainedValue_free
    {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ)) (B : ℝ) (F : ℂ → ℂ)
    (sw : PaperRankParameterSpace m p) (i : Fin m) :
    paperRankFullHermiteRetainedValue D representative offset S B F sw
      (Sum.inl i) = sw.1 i := by
  rfl

@[simp] theorem paperRankRetainedArgument_fullHermiteSmoothValue
    {m p a : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ)) (B : ℝ) (F : ℂ → ℂ)
    (x : PaperRankSource m p a) :
    paperRankRetainedArgument
      (paperRankFullHermiteSmoothValue D representative offset S B F) x =
      paperRankFullHermiteRetainedValue D representative offset S B F x.1 := by
  funext z
  rcases z with i | j <;> rfl

private theorem eval₂Hom_isEmptyAlgEquiv
    {R T σ : Type*} [CommSemiring R] [CommSemiring T] [IsEmpty σ]
    (c : R →+* T) (value : σ → T) (P : MvPolynomial σ R) :
    c (MvPolynomial.isEmptyAlgEquiv R σ P) =
      MvPolynomial.eval₂Hom c value P := by
  let lhs : MvPolynomial σ R →+* T :=
    c.comp (MvPolynomial.isEmptyAlgEquiv R σ).toRingHom
  let rhs : MvPolynomial σ R →+* T := MvPolynomial.eval₂Hom c value
  change lhs P = rhs P
  apply DFunLike.congr_fun _ P
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [lhs, rhs]
  · intro z
    exact isEmptyElim z

/-- The retained Hermite-before-rank substitution evaluates to the original
selected Abel jets. -/
theorem eval₂Hom_hermiteBeforeRankRetainedHom_fullHermiteValue
    {A : ℝ → ℝ} {m p : ℕ} (D : RestrictedBox p)
    (representative : ι → Fin m)
    (offset : ι → RestrictedBox.analyticNearClosedBoxSubalgebra D)
    (S : Finset (ι × ℕ))
    {B X K K0 : ℝ} {F : ℂ → ℂ}
    (H : AbelHermiteFamilySpec A B (paperRankHermiteNodeMultiplicity S)
      X K K0 (fun _ => F))
    (hB : 0 < B) (sw : PaperRankParameterSpace m p)
    (hs : ∀ i, X < sw.1 i)
    (hoffset : ∀ j : Fin S.card,
      |(offset (restrictedJetEnumeration S j).1 :
        RestrictedBoxSpace p → ℝ) sw.2| ≤ B)
    (P : MvPolynomial (PaperRankRetainedSymbols m S.card)
      (RestrictedBox.analyticNearClosedBoxSubalgebra D)) :
    MvPolynomial.eval₂Hom
        (subalgebraPointEval D.analyticNearClosedBoxSubalgebra sw.2)
        (paperRankFullHermiteRetainedValue D representative offset S B F sw)
        (hermiteBeforeRankRetainedHom
          D.analyticNearClosedBoxSubalgebra
          (paperRankHermiteJetPolynomial D representative offset S
            (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)) P) =
      MvPolynomial.eval₂Hom
        (subalgebraPointEval D.analyticNearClosedBoxSubalgebra sw.2)
        (Sum.elim sw.1
          (restrictedSelectedAbelJets A representative offset
            (restrictedJetEnumeration S) sw)) P := by
  let c := subalgebraPointEval D.analyticNearClosedBoxSubalgebra sw.2
  let coeffValue := paperRankHermiteCoefficientBlockValue D representative offset S
    (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m) B (fun _ => F) sw
  have hold := eval₂Hom_paperRankHermiteClusterCurryHom
    D representative offset S (Fin 0) (Fin m)
    (paperRankAllCoefficientBlockEquiv m) H hB sw hs hoffset P
  let activeValue := paperRankHermiteActiveValue D representative offset S
    (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m) B (fun _ => F) sw
  let jetPolynomial := paperRankHermiteJetPolynomial D representative offset S
    (Fin 0) (Fin m) (paperRankAllCoefficientBlockEquiv m)
  let curried := paperRankClusterCurryHom
    D.analyticNearClosedBoxSubalgebra (Fin 0) (Fin m)
    (paperRankHermiteBlockDerivativeCount S (Fin 0))
    (paperRankHermiteBlockDerivativeCount S (Fin m))
    (paperRankAllCoefficientBlockEquiv m) jetPolynomial P
  have hvalue :
      (paperRankFullHermiteRetainedValue D representative offset S B F sw) ∘
        (paperRankRetainedFlatHermiteEquiv m
          (paperRankHermitePositiveDerivativeCount S)).symm = coeffValue := by
    funext z
    dsimp [paperRankFullHermiteRetainedValue, coeffValue, Function.comp_def]
    rw [Equiv.apply_symm_apply]
  calc
    MvPolynomial.eval₂Hom c
        (paperRankFullHermiteRetainedValue D representative offset S B F sw)
        (hermiteBeforeRankRetainedHom
          D.analyticNearClosedBoxSubalgebra jetPolynomial P) =
      MvPolynomial.eval₂Hom c coeffValue
        (paperRankAllCoefficientCurryHom
          D.analyticNearClosedBoxSubalgebra jetPolynomial P) := by
            rw [show hermiteBeforeRankRetainedHom
                D.analyticNearClosedBoxSubalgebra jetPolynomial P =
              (paperRankRetainedFlatHermiteAlgEquiv
                D.analyticNearClosedBoxSubalgebra m
                (paperRankHermitePositiveDerivativeCount S)).symm
                (paperRankAllCoefficientCurryHom
                  D.analyticNearClosedBoxSubalgebra jetPolynomial P) by rfl]
            rw [show (paperRankRetainedFlatHermiteAlgEquiv
                D.analyticNearClosedBoxSubalgebra m
                (paperRankHermitePositiveDerivativeCount S)).symm
                (paperRankAllCoefficientCurryHom
                  D.analyticNearClosedBoxSubalgebra jetPolynomial P) =
              MvPolynomial.rename
                (paperRankRetainedFlatHermiteEquiv m
                  (paperRankHermitePositiveDerivativeCount S)).symm
                (paperRankAllCoefficientCurryHom
                  D.analyticNearClosedBoxSubalgebra jetPolynomial P) by rfl]
            change MvPolynomial.eval₂ c
                (paperRankFullHermiteRetainedValue
                  D representative offset S B F sw)
                (MvPolynomial.rename
                  (paperRankRetainedFlatHermiteEquiv m
                    (paperRankHermitePositiveDerivativeCount S)).symm
                  (paperRankAllCoefficientCurryHom
                    D.analyticNearClosedBoxSubalgebra jetPolynomial P)) =
              MvPolynomial.eval₂ c coeffValue
                (paperRankAllCoefficientCurryHom
                  D.analyticNearClosedBoxSubalgebra jetPolynomial P)
            rw [MvPolynomial.eval₂_rename]
            rw [hvalue]
    _ = MvPolynomial.eval₂Hom
        (MvPolynomial.eval₂Hom c coeffValue) activeValue curried := by
          exact eval₂Hom_isEmptyAlgEquiv
            (MvPolynomial.eval₂Hom c coeffValue) activeValue curried
    _ = _ := by
      simpa [c, coeffValue, activeValue, jetPolynomial, curried] using hold.symm

end AbelFormalization
