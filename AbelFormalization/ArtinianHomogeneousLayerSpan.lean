import AbelFormalization.ArtinianHomogeneousLayerCover

set_option autoImplicit false

/-!
# Constant generators span the Artinian polynomial filtration

The finite coefficient generators chosen in
`ArtinianHomogeneousLayerCover` generate each coefficient ideal power.  After
extension to the polynomial ring, their constant coordinate vectors generate
the entire corresponding ideal-power numerator of the free polynomial module.
-/

noncomputable section

namespace AbelFormalization

section ConstantSpan

variable {B : Type*} [CommRing B] {n r : ℕ}

/-- The underlying values of the chosen finite cover generators generate the
coefficient ideal power itself. -/
theorem artinianIdealPower_eq_span_coverGenerator_values
    [IsNoetherianRing B] (I : Ideal B) (i : ℕ) :
    I ^ i = Ideal.span (Set.range (fun s :
        Fin (artinianIdealPowerFiniteFreeCover I i).rank =>
      (artinianIdealPowerCoverGenerator I i s : B))) := by
  apply le_antisymm
  · intro x hx
    let x' : {y : B // y ∈ I ^ i} := ⟨x, hx⟩
    have hx' : x' ∈ Submodule.span B
        (Set.range (artinianIdealPowerCoverGenerator I i)) := by
      rw [artinianIdealPowerCoverGenerator_span_eq_top]
      exact Submodule.mem_top
    change (x' : B) ∈ Ideal.span (Set.range (fun s :
      Fin (artinianIdealPowerFiniteFreeCover I i).rank =>
        (artinianIdealPowerCoverGenerator I i s : B)))
    refine Submodule.span_induction
      (R := B) (M := {y : B // y ∈ I ^ i})
      (s := Set.range (artinianIdealPowerCoverGenerator I i)) (x := x')
      (p := fun y _ => (y : B) ∈ Ideal.span (Set.range (fun s :
        Fin (artinianIdealPowerFiniteFreeCover I i).rank =>
          (artinianIdealPowerCoverGenerator I i s : B))))
      ?_ ?_ ?_ ?_ hx'
    · intro y hy
      obtain ⟨s, rfl⟩ := hy
      exact Ideal.subset_span (Set.mem_range_self s)
    · exact (Ideal.span _).zero_mem
    · intro y z hy hz hy' hz'
      exact (Ideal.span _).add_mem hy' hz'
    · intro a y hy hy'
      change a * (y : B) ∈ Ideal.span _
      exact (Ideal.span _).mul_mem_left a hy'
  · apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    exact (artinianIdealPowerCoverGenerator I i s).property

/-- Constant coordinate vectors made from the chosen coefficient generators
span the full polynomial ideal-power numerator. -/
theorem artinianPolynomialIdealPowerSubmodule_eq_span_constants
    [IsNoetherianRing B] (I : Ideal B) (i : ℕ) :
    artinianPolynomialIdealPowerSubmodule (n := n) (r := r) I i =
      Submodule.span (MvPolynomial (Fin n) B)
        (Set.range (fun ks :
            Fin r × Fin (artinianIdealPowerFiniteFreeCover I i).rank =>
          artinianPolynomialIdealPowerConstantGenerator
            (n := n) (r := r) I i ks.1 ks.2)) := by
  classical
  let T : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r) :=
    Submodule.span (MvPolynomial (Fin n) B)
      (Set.range (fun ks :
          Fin r × Fin (artinianIdealPowerFiniteFreeCover I i).rank =>
        artinianPolynomialIdealPowerConstantGenerator
          (n := n) (r := r) I i ks.1 ks.2))
  apply le_antisymm
  · rw [artinianPolynomialIdealPowerSubmodule_eq_pi]
    intro P hP
    rw [← Finset.univ_sum_single P]
    apply Submodule.sum_mem
    intro k hk
    have hPk := (Submodule.mem_pi.mp hP) k (Set.mem_univ k)
    change P k ∈ artinianPolynomialCoefficientIdeal (n := n) I ^ i at hPk
    rw [artinianPolynomialCoefficientIdeal, ← Ideal.map_pow,
      artinianIdealPower_eq_span_coverGenerator_values, Ideal.map_span] at hPk
    change Pi.single k (P k) ∈ T
    refine Submodule.span_induction
      (p := fun p _ => Pi.single k p ∈ T) ?_ ?_ ?_ ?_ hPk
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := hp
      obtain ⟨s, rfl⟩ := ha
      exact Submodule.subset_span ⟨(k, s), rfl⟩
    · simpa using T.zero_mem
    · intro p q hp hq hp' hq'
      have hadd :
          (Pi.single k (p + q) : artinianFreePolynomialModule B n r) =
            Pi.single k p + Pi.single k q := by
        funext l
        by_cases hl : l = k <;> simp [Pi.single_apply, hl]
      rw [hadd]
      exact T.add_mem hp' hq'
    · intro a p hp hp'
      simpa only [Pi.single_smul'] using T.smul_mem a hp'
  · apply Submodule.span_le.mpr
    rintro _ ⟨ks, rfl⟩
    exact artinianPolynomialIdealPowerConstantGenerator_mem
      (n := n) (r := r) I i ks.1 ks.2

end ConstantSpan

end AbelFormalization
