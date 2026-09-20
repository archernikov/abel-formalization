import AbelFormalization.WeightedDeformationGenerators

/-!
# Homogeneous components of the full weighted initial ideal

The least-weight generators make the full initial ideal homogeneous. Two
independent weight projections commute, including over coefficient rings
with zero divisors. These facts allow successive weight refinements without
treating arbitrary members of a homogeneous ideal as homogeneous elements.
-/

noncomputable section

namespace AbelFormalization

section Components

variable {R ι M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]

/-- Two weight projections are commuting filters on the coefficient support. -/
theorem weightedHomogeneousComponents_commute (ω : ι → M) (ν : ι → N)
    (α : M) (β : N) (f : MvPolynomial ι R) :
    MvPolynomial.weightedHomogeneousComponent ω α
        (MvPolynomial.weightedHomogeneousComponent ν β f) =
      MvPolynomial.weightedHomogeneousComponent ν β
        (MvPolynomial.weightedHomogeneousComponent ω α f) := by
  classical
  ext d
  simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
  split_ifs <;> rfl

/-- Projecting for one grading preserves homogeneity for another grading. -/
theorem weightedHomogeneousComponent_preserves_homogeneity
    (ω : ι → M) (ν : ι → N) (α : M) {β : N} {f : MvPolynomial ι R}
    (hf : f.IsWeightedHomogeneous ν β) :
    (MvPolynomial.weightedHomogeneousComponent ω α f).IsWeightedHomogeneous ν β := by
  classical
  intro d hd
  rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hd
  split_ifs at hd with hweight
  · exact hf hd
  · exact (hd rfl).elim

/-- A finite sum indexed by the weights actually occurring in the support. -/
theorem sum_weightedHomogeneousComponent_support [DecidableEq M] (ω : ι → M)
    (f : MvPolynomial ι R) :
    (∑ α ∈ f.support.image (Finsupp.weight ω),
      MvPolynomial.weightedHomogeneousComponent ω α f) = f := by
  classical
  ext d
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (Finsupp.weight ω d)]
  · simp
  · intro α hα hne
    simp [Ne.symm hne]
  · intro hd
    simp only [ite_true]
    by_contra hcoeff
    exact hd (Finset.mem_image.mpr ⟨d, MvPolynomial.mem_support_iff.mpr hcoeff, rfl⟩)

end Components

section InitialIdeal

variable {R ι : Type*} [CommRing R]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The full initial ideal is homogeneous for the weight used to form it. -/
theorem weightedInitialIdeal_isHomogeneous (ω : ι → ℤ)
    (I : Ideal (MvPolynomial ι R)) :
    (weightedInitialIdeal ω I).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule R ω) := by
  classical
  apply Ideal.homogeneous_span
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨minimumSupportWeight ω f,
    MvPolynomial.weightedHomogeneousComponent_mem ω f (minimumSupportWeight ω f)⟩

/-- Every weight component of every member belongs to the full initial ideal. -/
theorem weightedInitialIdeal_component_mem (ω : ι → ℤ)
    (I : Ideal (MvPolynomial ι R)) {g : MvPolynomial ι R}
    (hg : g ∈ weightedInitialIdeal ω I) (α : ℤ) :
    MvPolynomial.weightedHomogeneousComponent ω α g ∈ weightedInitialIdeal ω I :=
  MvPolynomial.weightedHomogeneousComponent_mem_of_mem R ω
    (weightedInitialIdeal_isHomogeneous ω I) hg α

/-- A nonzero homogeneous polynomial has exactly its homogeneous weight
as its minimum support weight. -/
theorem minimumSupportWeight_of_homogeneous (ω : ι → ℤ)
    {α : ℤ} {f : MvPolynomial ι R} (hf : f.IsWeightedHomogeneous ω α)
    (hne : f ≠ 0) : minimumSupportWeight ω f = α := by
  obtain ⟨d, hd, hmin⟩ := exists_support_weight_eq_minimum ω hne
  exact hmin.symm.trans (hf (MvPolynomial.mem_support_iff.mp hd))

/-- Initial formation fixes ideals already homogeneous for that weight. -/
theorem weightedInitialIdeal_eq_of_homogeneous (ω : ι → ℤ)
    (I : Ideal (MvPolynomial ι R))
    (hI : I.IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule R ω)) :
    weightedInitialIdeal ω I = I := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem R ω hI hf _
  · intro f hf
    rw [← sum_weightedHomogeneousComponent_support ω f]
    apply Ideal.sum_mem
    intro α hα
    let g := MvPolynomial.weightedHomogeneousComponent ω α f
    have hg : g ∈ I :=
      MvPolynomial.weightedHomogeneousComponent_mem_of_mem R ω hI hf α
    by_cases hzero : g = 0
    · change g ∈ weightedInitialIdeal ω I
      rw [hzero]
      exact (weightedInitialIdeal ω I).zero_mem
    · have hhom : g.IsWeightedHomogeneous ω α :=
        MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous α f
      have hmin := minimumSupportWeight_of_homogeneous ω hhom hzero
      have heq : MvPolynomial.weightedHomogeneousComponent ω
          (minimumSupportWeight ω g) g = g := by
        rw [hmin]
        exact hhom.weightedHomogeneousComponent_same
      have hmem : MvPolynomial.weightedHomogeneousComponent ω
          (minimumSupportWeight ω g) g ∈ weightedInitialIdeal ω I :=
        Ideal.subset_span ⟨g, hg, rfl⟩
      change g ∈ weightedInitialIdeal ω I
      rwa [heq] at hmem

end InitialIdeal

end AbelFormalization
