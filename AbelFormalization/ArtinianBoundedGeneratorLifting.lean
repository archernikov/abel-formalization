import AbelFormalization.ArtinianUniformLayerPullbackGenerators

set_option autoImplicit false

/-!
# Lifting bounded generators through an Artinian coefficient filtration

The graded pullback used by the residue-field argument maps canonically and
surjectively onto the simultaneous induced coefficient layers.  This file
constructs that map without choosing a global section of the coefficient
quotient and records its compatibility with homogeneous components.
-/

noncomputable section

namespace AbelFormalization

/-! ## Changing scalars back across a pushed-forward quotient layer -/

/-- If a set spans an annihilated quotient layer after its scalar action is
pushed through a surjective ring map, then the same set already spans the
layer over the original scalar ring.  Surjectivity is used one scalar at a
time; no section of the ring map is retained. -/
theorem submoduleLayer_span_eq_top_of_pushforward_span_eq_top
    {A C W : Type*} [CommRing A] [CommRing C]
    [AddCommGroup W] [Module A W]
    (q : A →+* C) (hq : Function.Surjective q)
    (F G : Submodule A W) (hker : RingHom.ker q • F ≤ G)
    (S : Set (submoduleLayer F G)) :
    letI := submoduleLayerPushforwardModule q hq F G hker
    Submodule.span C S = ⊤ → Submodule.span A S = ⊤ := by
  let _ := submoduleLayerPushforwardModule q hq F G hker
  intro hspan
  apply (Submodule.eq_top_iff').mpr
  intro x
  have hx : x ∈ Submodule.span C S := by
    rw [hspan]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
      exact Submodule.subset_span hx
  | zero =>
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
      obtain ⟨a, rfl⟩ := hq c
      rw [submoduleLayerPushforward_smul_eq_original q hq F G hker]
      exact Submodule.smul_mem _ a hx

/-- The canonical map from the graded pullback to the simultaneous induced
layers.  The pullback condition says that the fixed ambient cover lands in
the range of the injective induced-layer embedding, whose inverse therefore
recovers a unique induced-layer tuple. -/
def artinianPolynomialGradedPullbackToInducedLayerSum
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e →ₗ[MvPolynomial (Fin n) (B ⧸ I)]
      artinianPolynomialInducedLayerSum (n := n) (r := r) I N e := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let q := artinianPolynomialAmbientLayerSumGradedCover
    (n := n) (r := r) I e
  let f := artinianPolynomialInducedLayerSumMap
    (n := n) (r := r) I N e
  let hf : Function.Injective f :=
    artinianPolynomialInducedLayerSumMap_injective
      (n := n) (r := r) I N e
  exact (LinearEquiv.ofInjective f hf).symm.toLinearMap.comp
    ((q.domRestrict
      (artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)).codRestrict
      (LinearMap.range f) (fun x => x.property))

@[simp]
theorem artinianPolynomialInducedLayerSumMap_gradedPullbackToInducedLayerSum
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ)
    (x : artinianPolynomialInducedLayerSumGradedPullback
      (n := n) (r := r) I N e) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialInducedLayerSumMap (n := n) (r := r) I N e
        (artinianPolynomialGradedPullbackToInducedLayerSum I N e x) =
      artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e x := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let f := artinianPolynomialInducedLayerSumMap
    (n := n) (r := r) I N e
  let hf : Function.Injective f :=
    artinianPolynomialInducedLayerSumMap_injective
      (n := n) (r := r) I N e
  change f ((LinearEquiv.ofInjective f hf).symm
      ⟨artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e x, x.property⟩) =
    artinianPolynomialAmbientLayerSumGradedCover
      (n := n) (r := r) I e x
  exact LinearEquiv.ofInjective_symm_apply (f := f) (h := hf)
    ⟨artinianPolynomialAmbientLayerSumGradedCover
      (n := n) (r := r) I e x, x.property⟩

theorem artinianPolynomialGradedPullbackToInducedLayerSum_surjective
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Function.Surjective
      (artinianPolynomialGradedPullbackToInducedLayerSum
        (n := n) (r := r) I N e) := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  intro y
  obtain ⟨x, hx⟩ :=
    artinianPolynomialAmbientLayerSumGradedCover_surjective
      (n := n) (r := r) I e
      (artinianPolynomialInducedLayerSumMap
        (n := n) (r := r) I N e y)
  have hxPullback :
      x ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e := by
    rw [mem_artinianPolynomialInducedLayerSumGradedPullback_iff, hx]
    exact LinearMap.mem_range_self _ y
  refine ⟨⟨x, hxPullback⟩, ?_⟩
  apply artinianPolynomialInducedLayerSumMap_injective
    (n := n) (r := r) I N e
  rw [artinianPolynomialInducedLayerSumMap_gradedPullbackToInducedLayerSum]
  exact hx

/-- The canonical pullback-to-layer map intertwines the component on the
free graded cover with the pointwise component on the induced layers. -/
theorem artinianPolynomialGradedPullbackToInducedLayerSum_component
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ)
    (x : artinianPolynomialInducedLayerSumGradedPullback
      (n := n) (r := r) I N e) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialGradedPullbackToInducedLayerSum I N e
        ⟨artinianPolynomialModuleComponent (B := B ⧸ I) weight
            (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
            degree x,
          by
            exact
              artinianPolynomialInducedLayerSumGradedPullback_homogeneous
                (n := n) (r := r) I N hN e x x.property degree⟩ =
      artinianPolynomialInducedLayerSumComponent I N hN e degree
        (artinianPolynomialGradedPullbackToInducedLayerSum I N e x) := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  apply artinianPolynomialInducedLayerSumMap_injective
    (n := n) (r := r) I N e
  rw [artinianPolynomialInducedLayerSumMap_gradedPullbackToInducedLayerSum]
  change
    artinianPolynomialAmbientLayerSumGradedCover
        (n := n) (r := r) I e
        (artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree x) =
      artinianPolynomialInducedLayerSumMap (n := n) (r := r) I N e
        (artinianPolynomialInducedLayerSumComponent I N hN e degree
          (artinianPolynomialGradedPullbackToInducedLayerSum I N e x))
  rw [← artinianPolynomialAmbientLayerSumGradedCover_component,
    artinianPolynomialInducedLayerSumMap_component,
    artinianPolynomialInducedLayerSumMap_gradedPullbackToInducedLayerSum]

/-- A homogeneous pullback vector maps to a tuple fixed by the component of
the same shifted degree. -/
theorem artinianPolynomialGradedPullbackToInducedLayerSum_component_eq_self
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ) (degree : ℤ)
    (x : artinianPolynomialInducedLayerSumGradedPullback
      (n := n) (r := r) I N e)
    (hx : artinianPolynomialModuleComponent (B := B ⧸ I) weight
        (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
        degree x = x) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    artinianPolynomialInducedLayerSumComponent I N hN e degree
        (artinianPolynomialGradedPullbackToInducedLayerSum I N e x) =
      artinianPolynomialGradedPullbackToInducedLayerSum I N e x := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let hxComponent :
      artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree x ∈
        artinianPolynomialInducedLayerSumGradedPullback
          (n := n) (r := r) I N e :=
    artinianPolynomialInducedLayerSumGradedPullback_homogeneous
      (n := n) (r := r) I N hN e x x.property degree
  have hsource :
      (⟨artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          degree x, hxComponent⟩ :
        artinianPolynomialInducedLayerSumGradedPullback
          (n := n) (r := r) I N e) = x := by
    apply Subtype.ext
    exact hx
  rw [← artinianPolynomialGradedPullbackToInducedLayerSum_component
    (n := n) (r := r) I N hN e degree x]
  exact congrArg
    (artinianPolynomialGradedPullbackToInducedLayerSum I N e) hsource

/-! ## Homogeneous representatives of individual induced-layer classes -/

/-- A chosen numerator representative of one induced-layer class.  The
choice is made only after the class is specified. -/
def artinianPolynomialInducedLayerRepresentative
    {B : Type*} [CommRing B] {n r : ℕ}
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (i : ℕ)
    (x : artinianPolynomialInducedLayer (n := n) (r := r) I N i) :
    ↥(N ⊓ artinianPolynomialIdealPowerSubmodule
      (n := n) (r := r) I i) :=
  Classical.choose
    (Submodule.mkQ_surjective
      ((N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I (i + 1)).comap
        (N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I i).subtype) x)

@[simp]
theorem artinianPolynomialInducedLayerRepresentative_mk
    {B : Type*} [CommRing B] {n r : ℕ}
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (i : ℕ)
    (x : artinianPolynomialInducedLayer (n := n) (r := r) I N i) :
    Submodule.Quotient.mk
        (artinianPolynomialInducedLayerRepresentative I N i x) = x :=
  Classical.choose_spec
    (Submodule.mkQ_surjective
      ((N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I (i + 1)).comap
        (N ⊓ artinianPolynomialIdealPowerSubmodule
          (n := n) (r := r) I i).subtype) x)

/-- Projecting a chosen numerator representative produces a homogeneous
representative of the selected component of the layer class. -/
def artinianPolynomialHomogeneousInducedLayerRepresentative
    {B : Type*} [CommRing B] {n r : ℕ}
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (i : ℕ) (degree : ℤ)
    (x : artinianPolynomialInducedLayer (n := n) (r := r) I N i) :
    ↥(N ⊓ artinianPolynomialIdealPowerSubmodule
      (n := n) (r := r) I i) :=
  artinianPolynomialInducedNumeratorComponent I N hN i degree
    (artinianPolynomialInducedLayerRepresentative I N i x)

theorem artinianPolynomialHomogeneousInducedLayerRepresentative_mk
    {B : Type*} [CommRing B] {n r : ℕ}
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (i : ℕ) (degree : ℤ)
    (x : artinianPolynomialInducedLayer (n := n) (r := r) I N i) :
    Submodule.Quotient.mk
        (artinianPolynomialHomogeneousInducedLayerRepresentative
          I N hN i degree x) =
      artinianPolynomialInducedLayerComponent I N hN i degree x := by
  rw [artinianPolynomialHomogeneousInducedLayerRepresentative,
    ← artinianPolynomialInducedLayerComponent_mk,
    artinianPolynomialInducedLayerRepresentative_mk]

theorem artinianPolynomialHomogeneousInducedLayerRepresentative_mem_piece
    {B : Type*} [CommRing B] {n r : ℕ}
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (i : ℕ) (degree : ℤ)
    (x : artinianPolynomialInducedLayer (n := n) (r := r) I N i) :
    (artinianPolynomialHomogeneousInducedLayerRepresentative
        I N hN i degree x : artinianFreePolynomialModule B n r) ∈
      artinianPolynomialModulePiece (B := B) weight shift degree := by
  exact artinianPolynomialModuleComponent_mem_piece weight shift degree _

/-! ## Spanning the induced layers by images of pullback generators -/

/-- A finite set spanning the pullback in the ambient free module spans the
top submodule after its elements are regarded as elements of the pullback
subtype. -/
theorem artinianPolynomialGradedPullback_generator_span_eq_top
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ)
    (G : Finset
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)))
    (hG : ∀ P ∈ G,
      P ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)
    (hspan :
      Submodule.span (MvPolynomial (Fin n) (B ⧸ I)) (G : Set _) =
        artinianPolynomialInducedLayerSumGradedPullback
          (n := n) (r := r) I N e) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Submodule.span (MvPolynomial (Fin n) (B ⧸ I))
        (Set.range fun P : ↥G =>
          (⟨P.1, hG P.1 P.2⟩ :
            artinianPolynomialInducedLayerSumGradedPullback
              (n := n) (r := r) I N e)) = ⊤ := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  apply (Submodule.span_range_subtype_eq_top_iff
    (artinianPolynomialInducedLayerSumGradedPullback
      (n := n) (r := r) I N e)
    (fun P : ↥G => hG P.1 P.2)).mpr
  have hrange :
      Set.range (fun P : ↥G =>
        (P.1 : Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
          MvPolynomial (Fin n) (B ⧸ I))) = (G : Set _) := by
    ext P
    constructor
    · rintro ⟨Q, rfl⟩
      exact Q.2
    · intro hP
      exact ⟨⟨P, hP⟩, rfl⟩
  rw [hrange]
  exact hspan

/-- The images of a finite spanning set of the pullback span the complete
simultaneous induced-layer sum. -/
theorem artinianPolynomialGradedPullback_generator_image_span_eq_top
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ)
    (G : Finset
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)))
    (hG : ∀ P ∈ G,
      P ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)
    (hspan :
      Submodule.span (MvPolynomial (Fin n) (B ⧸ I)) (G : Set _) =
        artinianPolynomialInducedLayerSumGradedPullback
          (n := n) (r := r) I N e) :
    letI (i : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
    letI (i : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
    Submodule.span (MvPolynomial (Fin n) (B ⧸ I))
        (Set.range fun P : ↥G =>
          artinianPolynomialGradedPullbackToInducedLayerSum I N e
            ⟨P.1, hG P.1 P.2⟩) = ⊤ := by
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let s := fun P : ↥G =>
    (⟨P.1, hG P.1 P.2⟩ :
      artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)
  let f := artinianPolynomialGradedPullbackToInducedLayerSum
    (n := n) (r := r) I N e
  change Submodule.span (MvPolynomial (Fin n) (B ⧸ I))
    (Set.range (f ∘ s)) = ⊤
  rw [Set.range_comp, ← Submodule.map_span,
    artinianPolynomialGradedPullback_generator_span_eq_top
      (n := n) (r := r) I N e G hG hspan,
    Submodule.map_top,
    LinearMap.range_eq_top.mpr
      (artinianPolynomialGradedPullbackToInducedLayerSum_surjective
        (n := n) (r := r) I N e)]

/-- In each filtration degree, the corresponding coordinates of the images
of the pullback generators span that complete induced layer. -/
theorem artinianPolynomialGradedPullback_generator_coordinate_span_eq_top
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    (e : ℕ)
    (G : Finset
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)))
    (hG : ∀ P ∈ G,
      P ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)
    (hspan :
      Submodule.span (MvPolynomial (Fin n) (B ⧸ I)) (G : Set _) =
        artinianPolynomialInducedLayerSumGradedPullback
          (n := n) (r := r) I N e)
    (i : Fin e) :
    letI (j : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N j.1
    letI (j : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
    Submodule.span (MvPolynomial (Fin n) (B ⧸ I))
        (Set.range fun P : ↥G =>
          artinianPolynomialGradedPullbackToInducedLayerSum I N e
            ⟨P.1, hG P.1 P.2⟩ i) = ⊤ := by
  let _ (j : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N j.1
  let _ (j : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
  let s := fun P : ↥G =>
    artinianPolynomialGradedPullbackToInducedLayerSum I N e
      ⟨P.1, hG P.1 P.2⟩
  let f : artinianPolynomialInducedLayerSum (n := n) (r := r) I N e
      →ₗ[MvPolynomial (Fin n) (B ⧸ I)]
        artinianPolynomialInducedLayer (n := n) (r := r) I N i.1 :=
    LinearMap.proj i
  change Submodule.span (MvPolynomial (Fin n) (B ⧸ I))
    (Set.range (f ∘ s)) = ⊤
  rw [Set.range_comp, ← Submodule.map_span,
    artinianPolynomialGradedPullback_generator_image_span_eq_top
      (n := n) (r := r) I N e G hG hspan,
    Submodule.map_top,
    LinearMap.range_eq_top.mpr (LinearMap.proj_surjective i)]

/-! ## Compatible homogeneous representatives of a finite pullback family -/

/-- For a pullback generator equipped with a selected degree, take the
homogeneous representative of each coordinate of its induced-layer image. -/
def artinianPolynomialHomogeneousPullbackGeneratorRepresentative
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ)
    (G : Finset
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)))
    (hG : ∀ P ∈ G,
      P ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)
    (degree : ↥G → ℤ) (P : ↥G) (i : Fin e) :
    ↥(N ⊓ artinianPolynomialIdealPowerSubmodule
      (n := n) (r := r) I i.1) := by
  let _ (j : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N j.1
  let _ (j : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
  exact artinianPolynomialHomogeneousInducedLayerRepresentative
    I N hN i.1 (degree P)
      (artinianPolynomialGradedPullbackToInducedLayerSum I N e
        ⟨P.1, hG P.1 P.2⟩ i)

/-- Every compatible representative lies in the original polynomial
submodule. -/
theorem artinianPolynomialHomogeneousPullbackGeneratorRepresentative_mem
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ)
    (G : Finset
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)))
    (hG : ∀ P ∈ G,
      P ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)
    (degree : ↥G → ℤ) (P : ↥G) (i : Fin e) :
    (artinianPolynomialHomogeneousPullbackGeneratorRepresentative
        I N hN e G hG degree P i :
      artinianFreePolynomialModule B n r) ∈ N :=
  (artinianPolynomialHomogeneousPullbackGeneratorRepresentative
    I N hN e G hG degree P i).property.1

/-- Every compatible representative is supported in its selected shifted
degree over the original coefficient ring. -/
theorem artinianPolynomialHomogeneousPullbackGeneratorRepresentative_mem_piece
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ)
    (G : Finset
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)))
    (hG : ∀ P ∈ G,
      P ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)
    (degree : ↥G → ℤ) (P : ↥G) (i : Fin e) :
    (artinianPolynomialHomogeneousPullbackGeneratorRepresentative
        I N hN e G hG degree P i :
      artinianFreePolynomialModule B n r) ∈
      artinianPolynomialModulePiece (B := B) weight shift (degree P) := by
  let _ (j : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N j.1
  let _ (j : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
  exact artinianPolynomialHomogeneousInducedLayerRepresentative_mem_piece
    I N hN i.1 (degree P)
      (artinianPolynomialGradedPullbackToInducedLayerSum I N e
        ⟨P.1, hG P.1 P.2⟩ i)

/-- If every selected pullback generator is fixed by its chosen component,
then the chosen representative of each coordinate represents exactly that
coordinate in the induced quotient layer. -/
theorem artinianPolynomialHomogeneousPullbackGeneratorRepresentative_mk
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ)
    (G : Finset
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)))
    (hG : ∀ P ∈ G,
      P ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)
    (degree : ↥G → ℤ)
    (hdegree : ∀ P : ↥G,
      artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          (degree P) P.1 = P.1)
    (P : ↥G) (i : Fin e) :
    letI (j : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N j.1
    letI (j : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
    Submodule.Quotient.mk
        (artinianPolynomialHomogeneousPullbackGeneratorRepresentative
          I N hN e G hG degree P i) =
      artinianPolynomialGradedPullbackToInducedLayerSum I N e
        ⟨P.1, hG P.1 P.2⟩ i := by
  let _ (j : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N j.1
  let _ (j : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
  rw [artinianPolynomialHomogeneousPullbackGeneratorRepresentative,
    artinianPolynomialHomogeneousInducedLayerRepresentative_mk]
  have htuple :=
    artinianPolynomialGradedPullbackToInducedLayerSum_component_eq_self
      (n := n) (r := r) I N hN e (degree P)
        ⟨P.1, hG P.1 P.2⟩ (hdegree P)
  exact congrFun htuple i

/-- The finite family of all homogeneous representatives, one for every
pullback generator and every Artinian filtration layer. -/
def artinianPolynomialHomogeneousPullbackGeneratorRepresentatives
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ)
    (G : Finset
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)))
    (hG : ∀ P ∈ G,
      P ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)
    (degree : ↥G → ℤ) :
    Finset (artinianFreePolynomialModule B n r) := by
  classical
  exact Finset.univ.image fun u : ↥G × Fin e =>
    (artinianPolynomialHomogeneousPullbackGeneratorRepresentative
      I N hN e G hG degree u.1 u.2 :
        artinianFreePolynomialModule B n r)

/-- All representatives lie in the original submodule and inherit the
selected degree bounds. -/
theorem artinianPolynomialHomogeneousPullbackGeneratorRepresentatives_mem
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ)
    (G : Finset
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)))
    (hG : ∀ P ∈ G,
      P ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)
    (degree : ↥G → ℤ) (D : ℕ)
    (hdegree_le : ∀ P : ↥G, degree P ≤ (D : ℤ)) :
    ∀ Q ∈ artinianPolynomialHomogeneousPullbackGeneratorRepresentatives
        I N hN e G hG degree,
      Q ∈ N ∧ ∃ d : ℤ, d ≤ (D : ℤ) ∧
        Q ∈ artinianPolynomialModulePiece (B := B) weight shift d := by
  classical
  intro Q hQ
  rw [artinianPolynomialHomogeneousPullbackGeneratorRepresentatives,
    Finset.mem_image] at hQ
  obtain ⟨⟨P, i⟩, _, rfl⟩ := hQ
  refine ⟨artinianPolynomialHomogeneousPullbackGeneratorRepresentative_mem
      I N hN e G hG degree P i,
    degree P, hdegree_le P, ?_⟩
  exact artinianPolynomialHomogeneousPullbackGeneratorRepresentative_mem_piece
    I N hN e G hG degree P i

/-- The finite representative family surjects onto every successive induced
coefficient-ideal quotient. -/
theorem artinianPolynomialHomogeneousPullbackGeneratorRepresentatives_surject
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    (e : ℕ)
    (G : Finset
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)))
    (hG : ∀ P ∈ G,
      P ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)
    (hspan :
      Submodule.span (MvPolynomial (Fin n) (B ⧸ I)) (G : Set _) =
        artinianPolynomialInducedLayerSumGradedPullback
          (n := n) (r := r) I N e)
    (degree : ↥G → ℤ)
    (hdegree : ∀ P : ↥G,
      artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          (degree P) P.1 = P.1)
    (i : Fin e) :
    letI (j : Fin e) :=
      artinianPolynomialInducedLayerModule (n := n) (r := r) I N j.1
    letI (j : Fin e) :=
      artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
    let A := N ⊓ artinianPolynomialIdealPowerSubmodule
      (n := n) (r := r) I i.1
    let A' := N ⊓ artinianPolynomialIdealPowerSubmodule
      (n := n) (r := r) I (i.1 + 1)
    let H := artinianPolynomialHomogeneousPullbackGeneratorRepresentatives
      I N hN e G hG degree
    ((Submodule.span (MvPolynomial (Fin n) B) (H : Set _)).comap
        A.subtype).map ((A'.comap A.subtype).mkQ) = ⊤ := by
  classical
  let _ (j : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N j.1
  let _ (j : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I j.1
  let A := N ⊓ artinianPolynomialIdealPowerSubmodule
    (n := n) (r := r) I i.1
  let A' := N ⊓ artinianPolynomialIdealPowerSubmodule
    (n := n) (r := r) I (i.1 + 1)
  let H := artinianPolynomialHomogeneousPullbackGeneratorRepresentatives
    I N hN e G hG degree
  let L := Submodule.span (MvPolynomial (Fin n) B)
    (↑H : Set (artinianFreePolynomialModule B n r))
  let Q := (L.comap A.subtype).map ((A'.comap A.subtype).mkQ)
  have hcoordinates :
      Submodule.span (MvPolynomial (Fin n) (B ⧸ I))
          (Set.range fun P : ↥G =>
            artinianPolynomialGradedPullbackToInducedLayerSum I N e
              ⟨P.1, hG P.1 P.2⟩ i) = ⊤ :=
    artinianPolynomialGradedPullback_generator_coordinate_span_eq_top
      (n := n) (r := r) I N e G hG hspan i
  have hsubset :
      Set.range (fun P : ↥G =>
        artinianPolynomialGradedPullbackToInducedLayerSum I N e
          ⟨P.1, hG P.1 P.2⟩ i) ⊆
        (↑Q : Set (artinianPolynomialInducedLayer
          (n := n) (r := r) I N i.1)) := by
    rintro y ⟨P, rfl⟩
    let R : A :=
      artinianPolynomialHomogeneousPullbackGeneratorRepresentative
        I N hN e G hG degree P i
    have hRH : (R : artinianFreePolynomialModule B n r) ∈ H := by
      apply Finset.mem_image.mpr
      exact ⟨(P, i), Finset.mem_univ _, rfl⟩
    have hRL : R ∈ L.comap A.subtype := by
      change (R : artinianFreePolynomialModule B n r) ∈ L
      exact Submodule.subset_span hRH
    refine ⟨R, hRL, ?_⟩
    exact artinianPolynomialHomogeneousPullbackGeneratorRepresentative_mk
      I N hN e G hG degree hdegree P i
  have hspanResidue :
      Submodule.span (MvPolynomial (Fin n) (B ⧸ I))
        (↑Q : Set (artinianPolynomialInducedLayer
          (n := n) (r := r) I N i.1)) = ⊤ := by
    apply top_unique
    rw [← hcoordinates]
    exact Submodule.span_mono hsubset
  have hspanOriginal :
      Submodule.span (MvPolynomial (Fin n) B)
        (↑Q : Set (artinianPolynomialInducedLayer
          (n := n) (r := r) I N i.1)) = ⊤ :=
    submoduleLayer_span_eq_top_of_pushforward_span_eq_top
      (artinianPolynomialResidueMap (n := n) I)
      (artinianPolynomialResidueMap_surjective (n := n) I)
      A A' (artinianPolynomialInducedLayer_annihilation
        (n := n) (r := r) I N i.1)
      (↑Q : Set (artinianPolynomialInducedLayer
        (n := n) (r := r) I N i.1)) hspanResidue
  simpa only [Submodule.span_eq] using hspanOriginal

/-- Compatible representatives of a spanning pullback family generate the
original polynomial submodule through the finite ideal-power filtration. -/
theorem artinianPolynomialHomogeneousPullbackGeneratorRepresentatives_span
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    (I : Ideal B)
    (N : Submodule (MvPolynomial (Fin n) B)
      (artinianFreePolynomialModule B n r))
    {weight : Fin n → ℕ} {shift : Fin r → ℤ}
    (hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N)
    {e : ℕ} (he : I ^ e = ⊥)
    (G : Finset
      (Fin (artinianPolynomialAmbientLayerGradedCoverRank I e r) →
        MvPolynomial (Fin n) (B ⧸ I)))
    (hG : ∀ P ∈ G,
      P ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e)
    (hspan :
      Submodule.span (MvPolynomial (Fin n) (B ⧸ I)) (G : Set _) =
        artinianPolynomialInducedLayerSumGradedPullback
          (n := n) (r := r) I N e)
    (degree : ↥G → ℤ)
    (hdegree : ∀ P : ↥G,
      artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          (degree P) P.1 = P.1) :
    Submodule.span (MvPolynomial (Fin n) B)
        (artinianPolynomialHomogeneousPullbackGeneratorRepresentatives
          I N hN e G hG degree : Set _) = N := by
  classical
  apply span_eq_of_surjects_on_artinianPolynomialIdealPowerFiltration
    I N he
      (artinianPolynomialHomogeneousPullbackGeneratorRepresentatives
        I N hN e G hG degree)
  · intro Q hQ
    rw [artinianPolynomialHomogeneousPullbackGeneratorRepresentatives,
      Finset.mem_image] at hQ
    obtain ⟨⟨P, i⟩, _, rfl⟩ := hQ
    exact artinianPolynomialHomogeneousPullbackGeneratorRepresentative_mem
      I N hN e G hG degree P i
  · intro i hi
    exact
      artinianPolynomialHomogeneousPullbackGeneratorRepresentatives_surject
        I N hN e G hG hspan degree hdegree ⟨i, hi⟩

/-! ## Uniform bounded generation over an Artinian local coefficient ring -/

/-- Homogeneous polynomial submodules with one fixed degree-length function
have a common bound on the shifted degrees of finite homogeneous generating
sets over the original Artinian coefficient ring. -/
theorem exists_uniform_finite_homogeneous_artinianPolynomialSubmodule_generators
    {B : Type*} [CommRing B] {n r : ℕ} [IsNoetherianRing B]
    [IsArtinianRing B]
    (m : MonomialOrder (Fin n))
    (I : Ideal B) [I.IsMaximal]
    (weight : Fin n → ℕ) (hweight : ∀ i, 0 < weight i)
    (shift : Fin r → ℤ) {e : ℕ} (he : I ^ e = ⊥)
    (hilbertLength : ℤ → ℕ) :
    ∃ D : ℕ,
      ∀ N : Submodule (MvPolynomial (Fin n) B)
          (artinianFreePolynomialModule B n r),
        ∀ _hN : IsArtinianPolynomialSubmoduleHomogeneous weight shift N,
        (∀ degree,
          (Module.length B
            (artinianPolynomialSubmoduleDegree
              N weight shift degree)).toNat = hilbertLength degree) →
        ∃ H : Finset (artinianFreePolynomialModule B n r),
          (∀ P ∈ H, P ∈ N ∧
            ∃ degree : ℤ, degree ≤ (D : ℤ) ∧
              P ∈ artinianPolynomialModulePiece
                (B := B) weight shift degree) ∧
          Submodule.span (MvPolynomial (Fin n) B) (H : Set _) = N := by
  classical
  let _ : Field (B ⧸ I) := Ideal.Quotient.field I
  let _ (i : Fin e) :=
    artinianPolynomialAmbientLayerModule (n := n) (r := r) I i.1
  let _ := artinianPolynomialAmbientLayerSumResidueModule
    (n := n) (r := r) I e
  obtain ⟨D, hD⟩ :=
    exists_uniform_finite_homogeneous_artinianLayerPullback_generators'
      m I weight hweight shift he hilbertLength
  refine ⟨D, ?_⟩
  intro N hN hlength
  let _ (i : Fin e) :=
    artinianPolynomialInducedLayerModule (n := n) (r := r) I N i.1
  let _ := artinianPolynomialInducedLayerSumResidueModule
    (n := n) (r := r) I N e
  obtain ⟨G, hGdata, hGspan⟩ := hD N hN hlength
  have hG : ∀ P ∈ G,
      P ∈ artinianPolynomialInducedLayerSumGradedPullback
        (n := n) (r := r) I N e := by
    intro P hP
    exact (hGdata P hP).1
  let degree : ↥G → ℤ := fun P =>
    Classical.choose (hGdata P.1 P.2).2
  have hdegree_spec (P : ↥G) :
      degree P ≤ (D : ℤ) ∧
        P.1 ∈ weightedPolynomialModulePiece weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          (degree P) :=
    Classical.choose_spec (hGdata P.1 P.2).2
  have hdegree : ∀ P : ↥G,
      artinianPolynomialModuleComponent (B := B ⧸ I) weight
          (artinianPolynomialAmbientLayerSumGradedGeneratorShift I e shift)
          (degree P) P.1 = P.1 := by
    intro P
    rw [artinianPolynomialModuleComponent_eq_weightedPolynomialModuleComponent]
    exact weightedPolynomialModuleComponent_eq_self _ _ _ (hdegree_spec P).2
  let H := artinianPolynomialHomogeneousPullbackGeneratorRepresentatives
    I N hN e G hG degree
  refine ⟨H, ?_, ?_⟩
  · exact
      artinianPolynomialHomogeneousPullbackGeneratorRepresentatives_mem
        I N hN e G hG degree D (fun P => (hdegree_spec P).1)
  · exact
      artinianPolynomialHomogeneousPullbackGeneratorRepresentatives_span
        I N hN he G hG hGspan degree hdegree

end AbelFormalization
