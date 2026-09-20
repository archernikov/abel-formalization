import AbelFormalization.LionUniformRegularFiberEncoding

/-!
# Khovanskii upper numbers and the fixed-map Gabrielov reduction

This file records the source-faithful quantifiers in the uniform-preimage
step used by Khovanskii and Lion.

For a square map `F`, `HasUpperNumberOfPreimagesAt F u N` says that one
neighborhood of `u` has at most `N` preimages over every regular target
value.  This is the predicate whose least witness is Khovanskii's *upper
number of preimages* (u.n.p.).  It deliberately counts the whole fiber only
when the target value is regular.

`HasUniformRegularFiberBound F` is the fixed-map conclusion needed by
`HasUniformSquareRegularFiberBound`: one natural number bounds the
nondegenerate part of every fiber of `F`, including fibers whose target value
is not regular.

Khovanskii's Lemma 2 passes from a local upper number to the nondegenerate
preimages over the center.  Its proof uses local inversion and the existence
of nearby regular values.  Gabrielov's theorem, together with the analytic
compactification/properness hypotheses, supplies a bound uniform in the
center.  Both inputs are represented below as explicit propositions.  No
implication from pointwise finiteness to either uniform proposition is
asserted.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Regular values and nondegenerate preimages -/

/-- The nondegenerate preimages of `u` under a square map `F`. -/
def nondegeneratePreimage {n : ℕ}
    (F : RealEuclidean n → RealEuclidean n) (u : RealEuclidean n) :
    Set (RealEuclidean n) :=
  {x | F x = u ∧ Function.Surjective (fderiv ℝ F x)}

@[simp]
theorem mem_nondegeneratePreimage_iff {n : ℕ}
    (F : RealEuclidean n → RealEuclidean n)
    (u x : RealEuclidean n) :
    x ∈ nondegeneratePreimage F u ↔
      F x = u ∧ Function.Surjective (fderiv ℝ F x) :=
  Iff.rfl

/-- A target value is regular when every point of its full preimage is
nondegenerate.  The empty fiber is therefore regular. -/
def IsRegularTargetValue {n : ℕ}
    (F : RealEuclidean n → RealEuclidean n)
    (u : RealEuclidean n) : Prop :=
  ∀ x, F x = u → Function.Surjective (fderiv ℝ F x)

/-- Over a regular target value, the nondegenerate preimage is the full
preimage. -/
theorem nondegeneratePreimage_eq_preimage_of_isRegularTargetValue
    {n : ℕ} (F : RealEuclidean n → RealEuclidean n)
    (u : RealEuclidean n) (hu : IsRegularTargetValue F u) :
    nondegeneratePreimage F u = F ⁻¹' {u} := by
  ext x
  simp only [mem_nondegeneratePreimage_iff, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · exact fun hx ↦ hx.1
  · intro hx
    exact ⟨hx, hu x hx⟩

/-- Equivalently, a target is regular exactly when its nondegenerate and full
preimages agree. -/
theorem isRegularTargetValue_iff_nondegeneratePreimage_eq_preimage
    {n : ℕ} (F : RealEuclidean n → RealEuclidean n)
    (u : RealEuclidean n) :
    IsRegularTargetValue F u ↔
      nondegeneratePreimage F u = F ⁻¹' {u} := by
  constructor
  · exact nondegeneratePreimage_eq_preimage_of_isRegularTargetValue F u
  · intro h x hx
    have hmem : x ∈ nondegeneratePreimage F u := by
      rw [h]
      simpa only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (mem_nondegeneratePreimage_iff F u x).mp hmem |>.2

/-- For a globally `C¹` square map, the manuscript's neighborhood-based
smooth regular fiber is exactly its set of nondegenerate preimages. -/
theorem smoothRegularFiber_eq_nondegeneratePreimage
    {n : ℕ} (F : RealEuclidean n → RealEuclidean n)
    (hF : ContDiff ℝ 1 F) (u : RealEuclidean n) :
    smoothRegularFiber F u = nondegeneratePreimage F u := by
  ext x
  rw [mem_smoothRegularFiber_iff_of_contDiff_square F hF u x]
  exact mem_nondegeneratePreimage_iff F u x |>.symm

/-- Hence, over a regular target value, the smooth regular fiber is the full
fiber. -/
theorem smoothRegularFiber_eq_preimage_of_isRegularTargetValue
    {n : ℕ} (F : RealEuclidean n → RealEuclidean n)
    (hF : ContDiff ℝ 1 F) (u : RealEuclidean n)
    (hu : IsRegularTargetValue F u) :
    smoothRegularFiber F u = F ⁻¹' {u} := by
  rw [smoothRegularFiber_eq_nondegeneratePreimage F hF u,
    nondegeneratePreimage_eq_preimage_of_isRegularTargetValue F u hu]

/-! ## Khovanskii's local upper number -/

/-- `N` is an upper number of preimages for `F` at `u`: some neighborhood of
`u` has full fibers of cardinal at most `N` at every regular target value.

Khovanskii defines the u.n.p. as the least such natural number.  The witness
predicate is the useful formal interface and avoids choosing that least
number. -/
def HasUpperNumberOfPreimagesAt {n : ℕ}
    (F : RealEuclidean n → RealEuclidean n)
    (u : RealEuclidean n) (N : ℕ) : Prop :=
  ∃ V : Set (RealEuclidean n), IsOpen V ∧ u ∈ V ∧
    ∀ v ∈ V, IsRegularTargetValue F v →
      ENat.card (F ⁻¹' {v}) ≤ N

/-- A larger natural number is still an upper number of preimages. -/
theorem HasUpperNumberOfPreimagesAt.mono
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    {u : RealEuclidean n} {N N' : ℕ}
    (hupper : HasUpperNumberOfPreimagesAt F u N) (hNN' : N ≤ N') :
    HasUpperNumberOfPreimagesAt F u N' := by
  obtain ⟨V, hVopen, huV, hV⟩ := hupper
  refine ⟨V, hVopen, huV, fun v hvV hvregular ↦ ?_⟩
  exact (hV v hvV hvregular).trans
    (ENat.natCast_le_natCast.mpr hNN')

/-- The same witnessing neighborhood proves Khovanskii's elementary local
persistence statement: every center in that neighborhood has upper number
at most `N`. -/
theorem HasUpperNumberOfPreimagesAt.exists_open_upperNumbers
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    {u : RealEuclidean n} {N : ℕ}
    (hupper : HasUpperNumberOfPreimagesAt F u N) :
    ∃ V : Set (RealEuclidean n), IsOpen V ∧ u ∈ V ∧
      ∀ v ∈ V, HasUpperNumberOfPreimagesAt F v N := by
  obtain ⟨V, hVopen, huV, hV⟩ := hupper
  exact ⟨V, hVopen, huV, fun v hvV ↦ ⟨V, hVopen, hvV, hV⟩⟩

/-- At a regular center, a local upper number directly bounds the full fiber
at that center. -/
theorem HasUpperNumberOfPreimagesAt.enatCard_preimage_le
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    {u : RealEuclidean n} {N : ℕ}
    (hupper : HasUpperNumberOfPreimagesAt F u N)
    (hregular : IsRegularTargetValue F u) :
    ENat.card (F ⁻¹' {u}) ≤ N := by
  obtain ⟨V, _, huV, hV⟩ := hupper
  exact hV u huV hregular

/-- The local implication used in Khovanskii's Lemma 2(2): an upper number at
the center also bounds the nondegenerate preimages over the center itself.

For smooth finite-dimensional maps this is proved using local inversion and
nearby regular values.  It is named as a premise here because that Sard/local
inversion argument is not part of the current formalized API. -/
def UpperNumbersControlNondegeneratePreimages {n : ℕ}
    (F : RealEuclidean n → RealEuclidean n) : Prop :=
  ∀ u N, HasUpperNumberOfPreimagesAt F u N →
    ENat.card (nondegeneratePreimage F u) ≤ N

/-- The uniform local-u.n.p. conclusion supplied in the analytic setting by
the Gabrielov/compactification and properness argument.  The same `N` works
at every center; this proposition is not derived from finite individual
fibers. -/
def HasGabrielovUniformUpperNumberProperty {n : ℕ}
    (F : RealEuclidean n → RealEuclidean n) : Prop :=
  ∃ N : ℕ, ∀ u, HasUpperNumberOfPreimagesAt F u N

/-- Asking for the same local upper number at every center is equivalent to
one global cardinal bound over all regular target values.  This equivalence
is purely logical; it does not establish the existence of either bound. -/
theorem hasGabrielovUniformUpperNumberProperty_iff
    {n : ℕ} (F : RealEuclidean n → RealEuclidean n) :
    HasGabrielovUniformUpperNumberProperty F ↔
      ∃ N : ℕ, ∀ u, IsRegularTargetValue F u →
        ENat.card (F ⁻¹' {u}) ≤ N := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun u hu ↦ (hN u).enatCard_preimage_le hu⟩
  · rintro ⟨N, hN⟩
    refine ⟨N, fun u ↦ ?_⟩
    exact ⟨Set.univ, isOpen_univ, Set.mem_univ u,
      fun v _ hv ↦ hN v hv⟩

/-- A uniform bound on nondegenerate preimages directly gives the same
uniform local upper number: take the whole target space as the neighborhood
and use that a regular target has no degenerate preimages. -/
theorem hasGabrielovUniformUpperNumberProperty_of_uniformNondegeneratePreimageBound
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hbound : ∃ N : ℕ, ∀ u,
      ENat.card (nondegeneratePreimage F u) ≤ N) :
    HasGabrielovUniformUpperNumberProperty F := by
  obtain ⟨N, hN⟩ := hbound
  refine ⟨N, fun u ↦ ?_⟩
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ u, ?_⟩
  intro v _ hv
  rw [← nondegeneratePreimage_eq_preimage_of_isRegularTargetValue F v hv]
  exact hN v

/-- Uniform local upper numbers give a uniform bound on nondegenerate
preimages once the center-control implication of Khovanskii's Lemma 2 is
available. -/
theorem uniformNondegeneratePreimageBound_of_gabrielovUpperNumbers
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hcenter : UpperNumbersControlNondegeneratePreimages F)
    (hupper : HasGabrielovUniformUpperNumberProperty F) :
    ∃ N : ℕ, ∀ u,
      ENat.card (nondegeneratePreimage F u) ≤ N := by
  obtain ⟨N, hN⟩ := hupper
  exact ⟨N, fun u ↦ hcenter u N (hN u)⟩

/-! ## The fixed square-map uniformity property -/

/-- One bound for all smooth regular fibers of one fixed square map. -/
def HasUniformRegularFiberBound {n : ℕ}
    (F : RealEuclidean n → RealEuclidean n) : Prop :=
  ∃ N : ℕ, ∀ u, ENat.card (smoothRegularFiber F u) ≤ N

/-- For a globally `C¹` square map, the fixed regular-fiber property is
exactly the corresponding uniform bound on nondegenerate preimages. -/
theorem hasUniformRegularFiberBound_iff_uniformNondegeneratePreimageBound
    {n : ℕ} (F : RealEuclidean n → RealEuclidean n)
    (hF : ContDiff ℝ 1 F) :
    HasUniformRegularFiberBound F ↔
      ∃ N : ℕ, ∀ u,
        ENat.card (nondegeneratePreimage F u) ≤ N := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun u ↦ ?_⟩
    rw [← smoothRegularFiber_eq_nondegeneratePreimage F hF u]
    exact hN u
  · rintro ⟨N, hN⟩
    refine ⟨N, fun u ↦ ?_⟩
    rw [smoothRegularFiber_eq_nondegeneratePreimage F hF u]
    exact hN u

/-- This is the exact formal reduction from the two source-level inputs to a
fixed-map uniform regular-fiber bound.  Establishing `hupper` from analytic
compactification/properness is the Gabrielov step; it is not inferred from
pointwise finiteness. -/
theorem hasUniformRegularFiberBound_of_gabrielovUpperNumbers
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : ContDiff ℝ 1 F)
    (hcenter : UpperNumbersControlNondegeneratePreimages F)
    (hupper : HasGabrielovUniformUpperNumberProperty F) :
    HasUniformRegularFiberBound F := by
  rw [hasUniformRegularFiberBound_iff_uniformNondegeneratePreimageBound F hF]
  exact uniformNondegeneratePreimageBound_of_gabrielovUpperNumbers
    hcenter hupper

/-- Conversely, a fixed-map uniform regular-fiber bound gives uniform upper
numbers for a globally `C¹` map.  This direction uses no compactness. -/
theorem HasUniformRegularFiberBound.hasGabrielovUniformUpperNumberProperty
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hbound : HasUniformRegularFiberBound F)
    (hF : ContDiff ℝ 1 F) :
    HasGabrielovUniformUpperNumberProperty F := by
  apply hasGabrielovUniformUpperNumberProperty_of_uniformNondegeneratePreimageBound
  exact (hasUniformRegularFiberBound_iff_uniformNondegeneratePreimageBound
    F hF).mp hbound

/-- The family-level property already used by the component encoding is
definitionally the assertion that every square tuple in the family has the
fixed-map property above. -/
theorem hasUniformSquareRegularFiberBound_iff_fixed
    {G : (n : ℕ) → Set (RealEuclideanFunction n)} :
    HasUniformSquareRegularFiberBound G ↔
      ∀ n (F : RealEuclidean n → RealEuclidean n),
        FunctionTupleInFamily G F → HasUniformRegularFiberBound F :=
  Iff.rfl

/-! ## The pointwise hypothesis remains pointwise -/

/-- Pointwise finiteness of the smooth regular fibers of one fixed map. -/
def HasPointwiseFiniteRegularFibers {n : ℕ}
    (F : RealEuclidean n → RealEuclidean n) : Prop :=
  ∀ u, (smoothRegularFiber F u).Finite

/-- `0`-regularity supplies the pointwise property for each square family
tuple.  The conclusion retains the order `∀ u, finite`; no uniform natural
number is produced. -/
theorem IsZeroRegularFunctionFamily.hasPointwiseFiniteRegularFibers
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hzero : IsZeroRegularFunctionFamily G)
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hF : FunctionTupleInFamily G F) :
    HasPointwiseFiniteRegularFibers F :=
  hzero n F hF

/-- A uniform fixed-map bound implies pointwise finiteness. -/
theorem HasUniformRegularFiberBound.hasPointwiseFiniteRegularFibers
    {n : ℕ} {F : RealEuclidean n → RealEuclidean n}
    (hbound : HasUniformRegularFiberBound F) :
    HasPointwiseFiniteRegularFibers F := by
  obtain ⟨N, hN⟩ := hbound
  intro u
  rw [← Set.finite_coe_iff]
  exact ENat.card_lt_top.mp ((hN u).trans_lt (by simp))

end AbelFormalization
