import AbelFormalization.ArtinianInducedLayerDegreeIdentification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Uniform generators for the Artinian layer pullback

The canonical degree-slice identification removes the final abstract input
from the residue-field generator theorem.  Thus one degree bound, selected
only from the Artinian coefficient filtration and the common length function,
works for every homogeneous polynomial submodule with that length function.
-/

noncomputable section

namespace AbelFormalization

/-- The Artinian layer pullback has uniformly bounded homogeneous generators;
the degree-slice identification is now constructed internally. -/
theorem exists_uniform_finite_homogeneous_artinianLayerPullback_generators'
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    [IsArtinianRing B]
    (m : MonomialOrder (Fin n))
    (I : Ideal B) [I.IsMaximal]
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ) {e : ℕ} (he : I ^ e = ⊥)
    (hilbertLength : ℤ → ℕ) :
    letI : Field (B ⧸ I) := Ideal.Quotient.field I
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    letI := artinianPolynomialAmbientLayerSumResidueModule
      (n := n) (r := r) I e
    ∃ D : ℕ,
      ∀ N : Submodule (MvPolynomial (Fin n) B)
          (artinianFreePolynomialModule B n r),
        letI (i : Fin e) :=
          artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
        letI := artinianPolynomialInducedLayerSumResidueModule
          (n := n) (r := r) I N e
        ∀ _hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N,
        (∀ degree,
          (Module.length B
            (artinianPolynomialSubmoduleDegree
              N weight shift degree)).toNat = hilbertLength degree) →
        ∃ G : Finset
            (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
              MvPolynomial (Fin n) (B ⧸ I)),
          (∀ P ∈ G,
            P ∈ artinianPolynomialInducedLayerSumGradedPullback
                (n := n) (r := r) I N e ∧
              ∃ degree : ℤ, degree ≤ (D : ℤ) ∧
                P ∈ weightedPolynomialModulePiece weight
                  (artinianPolynomialAmbientLayerSumGradedGeneratorShift
                    I e shift)
                  degree) ∧
          Submodule.span (MvPolynomial (Fin n) (B ⧸ I)) (G : Set _) =
            artinianPolynomialInducedLayerSumGradedPullback
              (n := n) (r := r) I N e := by
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  obtain ⟨D, hD⟩ :=
    exists_uniform_finite_homogeneous_artinianLayerPullback_generators
      m I weight hweight shift he hilbertLength
  refine ⟨D, ?_⟩
  intro N
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  intro hN hlength
  exact hD N hN
    (artinianPolynomialInducedLayerDegreeIdentification I N hN e)
    hlength

end AbelFormalization
