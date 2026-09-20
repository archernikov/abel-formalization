import AbelFormalization.WeightedDeformationGenerators

/-!
# Actual lifts of homogeneous initial forms

A homogeneous element of the full initial ideal is lifted by selecting one
coefficient of an actual inverse-rescaled Laurent preimage. Polynomiality of
the deformation gives a lower bound on all weights of that coefficient.
No assumption that the coefficient ring is a domain is needed.
-/

noncomputable section

namespace AbelFormalization

variable {R ι : Type*} [CommRing R]

/-- A homogeneous element of the full initial ideal has an actual lift in I
with no monomial below its specified weight. This also includes g=0. -/
theorem exists_component_lift_weightedInitialIdeal
    (ω : ι → ℤ) (I : Ideal (MvPolynomial ι R))
    {α : ℤ} {g : MvPolynomial ι R}
    (hg : g ∈ weightedInitialIdeal ω I) (hhom : g.IsWeightedHomogeneous ω α) :
    ∃ f ∈ I, (∀ d ∈ f.support, α ≤ Finsupp.weight ω d) ∧
      MvPolynomial.weightedHomogeneousComponent ω α f = g := by
  classical
  have hg' : g ∈ (weightedDeformationIdeal ω I).map (Polynomial.evalRingHom 0) := by
    change g ∈ weightedDeformationSpecialization ω I
    rwa [weightedDeformationSpecialization_eq_initialIdeal]
  obtain ⟨p, hp, hpg⟩ := (Ideal.mem_map_iff_of_surjective (Polynomial.evalRingHom 0)
    (Polynomial.eval_surjective 0)).mp hg'
  change p.eval 0 = g at hpg
  have hp0 : p.coeff 0 = g := p.coeff_zero_eq_eval_zero.trans hpg
  have hpL0 : p.toLaurent.coeff (0 : ℤ) = g :=
    (polynomial_toLaurent_coeff_nat p 0).trans hp0
  let e := laurentWeightRescaling (R := R) ω
  change p.toLaurent ∈ (I.map LaurentPolynomial.C).map e.toRingHom at hp
  obtain ⟨F, hFI, hFp⟩ :=
    (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hp
  have hFp' : laurentWeightRescaling ω F = p.toLaurent := hFp
  have hcoeffI : ∀ n : ℤ, F.coeff n ∈ I :=
    (laurentPolynomial_mem_map_C_iff I F).mp hFI
  have hcoeff (d : ι →₀ ℕ) :
      g.coeff d = (F.coeff (-Finsupp.weight ω d)).coeff d := by
    have he := congrArg (fun L : LaurentPolynomial (MvPolynomial ι R) =>
      (L.coeff 0).coeff d) hFp'
    simpa only [laurentWeightRescaling_coeff, zero_sub, hpL0] using he.symm
  let f := F.coeff (-α)
  refine ⟨f, hcoeffI (-α), ?_, ?_⟩
  · intro d hd
    have hfd : (F.coeff (-α)).coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have hb := laurentWeightRescaling_exponent_nonneg_of_toLaurent ω F p hFp' (-α) d hfd
    omega
  · apply MvPolynomial.ext
    intro d
    rw [MvPolynomial.coeff_weightedHomogeneousComponent]
    by_cases hw : Finsupp.weight ω d = α
    · rw [ite_eq_left hw]
      simpa only [f, hw] using (hcoeff d).symm
    · rw [ite_eq_right hw]
      symm
      by_contra hgd
      exact hw (hhom hgd)

/-- Every nonzero homogeneous element of the full initial ideal is itself
the initial form of an actual member of I, at exactly its given weight. -/
theorem exists_lift_weightedInitialIdeal_homogeneous
    (ω : ι → ℤ) (I : Ideal (MvPolynomial ι R))
    {α : ℤ} {g : MvPolynomial ι R}
    (hg : g ∈ weightedInitialIdeal ω I)
    (hhom : g.IsWeightedHomogeneous ω α) (hne : g ≠ 0) :
    ∃ f ∈ I, f ≠ 0 ∧ minimumSupportWeight ω f = α ∧
      MvPolynomial.weightedHomogeneousComponent ω α f = g := by
  classical
  obtain ⟨f, hfI, hbound, hproj⟩ :=
    exists_component_lift_weightedInitialIdeal ω I hg hhom
  have hf : f ≠ 0 := by
    intro hf0
    rw [hf0, map_zero] at hproj
    exact hne hproj.symm
  refine ⟨f, hfI, hf, le_antisymm ?_ ?_, hproj⟩
  · obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hne
    have hweight : Finsupp.weight ω d = α := hhom hd
    have hfd : f.coeff d ≠ 0 := by
      have he := congrArg (fun q : MvPolynomial ι R => q.coeff d) hproj
      rw [MvPolynomial.coeff_weightedHomogeneousComponent, ite_eq_left hweight] at he
      exact he.symm ▸ hd
    exact (minimumSupportWeight_le ω f (MvPolynomial.mem_support_iff.mpr hfd)).trans_eq hweight
  · obtain ⟨d, hd, hweight⟩ := exists_support_weight_eq_minimum ω hf
    exact (hbound d hd).trans_eq hweight

/-- The same lifting conclusion written with the lift's own minimum-weight
component, convenient for composing successive initial operations. -/
theorem exists_initial_form_lift_weightedInitialIdeal
    (ω : ι → ℤ) (I : Ideal (MvPolynomial ι R))
    {α : ℤ} {g : MvPolynomial ι R}
    (hg : g ∈ weightedInitialIdeal ω I)
    (hhom : g.IsWeightedHomogeneous ω α) (hne : g ≠ 0) :
    ∃ f ∈ I, f ≠ 0 ∧ minimumSupportWeight ω f = α ∧
      MvPolynomial.weightedHomogeneousComponent ω (minimumSupportWeight ω f) f = g := by
  obtain ⟨f, hfI, hf, hmin, hproj⟩ :=
    exists_lift_weightedInitialIdeal_homogeneous ω I hg hhom hne
  exact ⟨f, hfI, hf, hmin, by simpa only [hmin] using hproj⟩

end AbelFormalization
