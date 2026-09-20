import AbelFormalization.LionCarpetedLeaf
import AbelFormalization.RegularConstraintFiber

/-!
# Component maxima on fibers of a carpeted leaf

The first step of Lion's Lemma 4 chooses a maximum of the carpet on every
connected component of a regular fiber.  Positive compact superlevels are
exactly the properness input needed for that choice.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-- Points which maximize a function on their own connected component. -/
def componentMaximizers {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) : Set X :=
  {x | IsMaxOn f (connectedComponent x) x}

/-- A positive continuous function with compact positive superlevels attains
a maximum on every connected component. -/
theorem exists_componentMaximizer_of_compact_positive_superlevel
    {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f)
    (hpos : ∀ x, 0 < f x)
    (hcompact : ∀ r : ℝ, 0 < r → IsCompact {x | r ≤ f x})
    (x : X) :
    ∃ y ∈ connectedComponent x, y ∈ componentMaximizers f := by
  let S : Set X := connectedComponent x ∩ {y | f x ≤ f y}
  have hScompact : IsCompact S :=
    (hcompact (f x) (hpos x)).inter_left isClosed_connectedComponent
  have hxS : x ∈ S := by
    refine ⟨mem_connectedComponent, ?_⟩
    show f x ≤ f x
    exact le_rfl
  obtain ⟨y, hyS, hymax⟩ :=
    hScompact.exists_isMaxOn ⟨x, hxS⟩
      (hf.continuousOn.mono inter_subset_right)
  refine ⟨y, hyS.1, ?_⟩
  have hcomponents : connectedComponent x = connectedComponent y :=
    connectedComponent_eq hyS.1
  change IsMaxOn f (connectedComponent y) y
  rw [← hcomponents]
  intro z hz
  by_cases hzsuper : f x ≤ f z
  · exact hymax ⟨hz, hzsuper⟩
  · exact (le_of_not_ge hzsuper).trans (hymax hxS)

/-- A componentwise maximum on a regular constraint locus is a constrained
local maximum.  This is the differential-topological bridge used to put the
carpet maximum from Lion's Lemma 4 in the critical locus. -/
theorem componentMaximizer_isLocalMaxOn_of_surjectiveConstraint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : ℕ} {M : Set E} (H : Fin r → E → ℝ) (ρ : E → ℝ)
    (x : M)
    (hmax : x ∈ componentMaximizers (fun y : M ↦ ρ (y : E)))
    (hH : ∀ i, HasStrictFDerivAt (H i) (fderiv ℝ (H i) x) x)
    (hsurj : (constraintFDeriv H x).range = ⊤)
    (hlocalConstraint : ∃ V ∈ nhds (x : E),
      V ∩ {y | ∀ i, H i y = H i x} ⊆ M) :
    IsLocalMaxOn ρ {y | ∀ i, H i y = H i x} (x : E) := by
  obtain ⟨U, hU, hcomponent⟩ :=
    localConstraintFiber_of_surjectiveDerivative
      H x hH hsurj hlocalConstraint
  change IsMaxOn (fun y : M ↦ ρ (y : E))
    (connectedComponent x) x at hmax
  rw [IsLocalMaxOn]
  filter_upwards [mem_nhdsWithin_of_mem_nhds hU,
    self_mem_nhdsWithin] with y hyU hyfiber
  obtain ⟨hyM, hycomponent⟩ := hcomponent y hyU hyfiber
  exact hmax hycomponent

namespace LionCarpetedLeaf

variable {G : (d : ℕ) → Set (RealEuclideanFunction d)} {n q p : ℕ}

/-- The `t`-fiber of `g` inside a carpeted leaf. -/
def fiber (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (t : RealEuclidean p) : Set (RealEuclidean n) :=
  {x | x ∈ L.carrier ∧ g x = t}

@[simp]
theorem mem_fiber_iff (L : LionCarpetedLeaf G n q)
    (g : RealEuclidean n → RealEuclidean p)
    (t : RealEuclidean p) (x : RealEuclidean n) :
    x ∈ L.fiber g t ↔ x ∈ L.U ∧ L.equations x = 0 ∧ g x = t := by
  simp only [fiber, carrier, Set.mem_ofPred_eq]
  aesop

/-- The old carpet remains a carpet after restricting to a leaf fiber. -/
theorem isLionCarpetOn_fiber
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (t : RealEuclidean p) :
    IsLionCarpetOn (L.fiber g t) L.delta := by
  have hfcont : Continuous L.equations :=
    (L.equations_contDiff hsmooth).continuous
  have hgcont : Continuous g := by
    apply continuous_pi
    intro j
    exact (hsmooth n (fun x ↦ g x j) (hg j)).continuous
  refine ⟨fun x hx ↦ L.isCarpet.pos x hx.1.1, ?_⟩
  intro eta heta
  let K : Set (RealEuclidean n) := {x | x ∈ L.U ∧ eta ≤ L.delta x}
  have hK : IsCompact K := L.isCarpet.isCompact_superlevel eta heta
  have hfclosed : IsClosed (L.equations ⁻¹' {(0 : RealEuclidean q)}) :=
    isClosed_singleton.preimage hfcont
  have hgclosed : IsClosed (g ⁻¹' {t}) :=
    isClosed_singleton.preimage hgcont
  have heq :
      {x | x ∈ L.fiber g t ∧ eta ≤ L.delta x} =
        (K ∩ L.equations ⁻¹' {(0 : RealEuclidean q)}) ∩
          g ⁻¹' {t} := by
    ext x
    simp only [K, fiber, carrier, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff]
    aesop
  rw [heq]
  exact (hK.inter_right hfclosed).inter_right hgclosed

/-- Every connected component of a leaf fiber contains a maximum of the
carpet restricted to that fiber. -/
theorem exists_carpetMaximizer_in_connectedComponent
    (L : LionCarpetedLeaf G n q)
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (g : RealEuclidean n → RealEuclidean p)
    (hg : FunctionTupleInFamily G g)
    (t : RealEuclidean p) (x : L.fiber g t) :
    ∃ y ∈ connectedComponent x,
      y ∈ componentMaximizers (fun z : L.fiber g t ↦ L.delta z) := by
  let M := L.fiber g t
  have hcarpet : IsLionCarpetOn M L.delta :=
    L.isLionCarpetOn_fiber hsmooth g hg t
  apply exists_componentMaximizer_of_compact_positive_superlevel
    (fun z : M ↦ L.delta z)
  · exact (L.carpet_contDiff hsmooth).continuous.comp continuous_subtype_val
  · intro z
    exact hcarpet.pos z z.property
  · intro eta heta
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have himage :
        ((↑) : M → RealEuclidean n) ''
            {z : M | eta ≤ L.delta z} =
          {z | z ∈ M ∧ eta ≤ L.delta z} := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.property, hw⟩
      · rintro ⟨hzM, hz⟩
        exact ⟨⟨z, hzM⟩, hz, rfl⟩
    rw [himage]
    exact hcarpet.isCompact_superlevel eta heta

end LionCarpetedLeaf

end AbelFormalization
