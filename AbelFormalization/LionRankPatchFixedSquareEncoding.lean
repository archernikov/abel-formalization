import AbelFormalization.LionFixedMinorConstantRankComponentEncoding
import AbelFormalization.LionUniformFiberNarrowing
import AbelFormalization.SmoothFamilyRankStratumFiberReduction
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite rank-patch fixed-square encodings

For an arbitrary rectangular smooth map, the derivative ranks and the choices
of a nonzero square Jacobian minor form a finite family.  This file makes that
finite cover explicit and separates two issues which are easy to conflate:

* component encodings for each rank/minor patch, and
* merging the regular fibers of finitely many fixed square maps into the
  regular fiber of one fixed square map.

The first item already suffices for uniform fiber finiteness once every fixed
square family map has a uniform regular-fiber bound: one simply sums the
finitely many bounds.  Thus a literal one-map merger is stronger than the
cardinal conclusion needed in Lion's argument.  A final constructor records
the exact additional injection required to obtain the older one-map
`FixedSquareRegularFiberComponentEncoding` interface.
-/

noncomputable section

open Set Function
open scoped ContDiff BigOperators

namespace AbelFormalization

set_option autoImplicit false

/-! ## The finite rank/minor cover -/

/-- All possible exact ranks and selected square minors for a map
`ℝᵃ → ℝᵇ`.  Empty embedding types automatically remove impossible ranks. -/
abbrev RankMinorPatchIndex (a b : ℕ) :=
  Σ k : Fin (a + 1),
    (Fin (k : ℕ) ↪ Fin b) × (Fin (k : ℕ) ↪ Fin a)

/-- The part of one full fiber having the selected exact rank and nonzero
selected minor. -/
def rankMinorFiberPatch {a b : ℕ}
    (g : RealEuclidean a → RealEuclidean b) (t : RealEuclidean b)
    (i : RankMinorPatchIndex a b) : Set (g ⁻¹' {t}) :=
  {x |
    Module.finrank ℝ
        (LinearMap.range
          (fderiv ℝ g (x : RealEuclidean a)).toLinearMap) = (i.1 : ℕ) ∧
      standardJacobianMinor g i.2.1 i.2.2
        (x : RealEuclidean a) ≠ 0}

/-- On a selected nonzero `k`-minor, exact rank `k` is precisely the
vanishing of every successor minor.  This exhibits the residual patch as one
reciprocal nonvanishing condition together with a finite system of zero
conditions; regularity of that enlarged system is not automatic. -/
theorem mem_rankMinorFiberPatch_iff_successorMinors
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : ContDiff ℝ 1 g) (t : RealEuclidean b)
    (i : RankMinorPatchIndex a b) (x : g ⁻¹' {t}) :
    x ∈ rankMinorFiberPatch g t i ↔
      standardJacobianMinor g i.2.1 i.2.2
          (x : RealEuclidean a) ≠ 0 ∧
        ∀ rows : Fin ((i.1 : ℕ) + 1) ↪ Fin b,
          ∀ cols : Fin ((i.1 : ℕ) + 1) ↪ Fin a,
            standardJacobianMinor g rows cols
              (x : RealEuclidean a) = 0 := by
  have hrank := finrank_range_fderiv_eq_iff_standardJacobianMinors
    (k := (i.1 : ℕ))
    ((hg.differentiable one_ne_zero).differentiableAt :
      DifferentiableAt ℝ g (x : RealEuclidean a))
  constructor
  · rintro ⟨hxrank, hminor⟩
    exact ⟨hminor, (hrank.mp hxrank).2⟩
  · rintro ⟨hminor, hsuccessor⟩
    refine ⟨hrank.mpr ⟨?_, hsuccessor⟩, hminor⟩
    exact ⟨i.2.1, i.2.2, hminor⟩

/-- The finitely many exact-rank/nonzero-minor patches cover every fiber of a
`C¹` rectangular map. -/
theorem iUnion_rankMinorFiberPatch_eq_univ
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b)
    (hg : ContDiff ℝ 1 g) (t : RealEuclidean b) :
    ⋃ i : RankMinorPatchIndex a b,
      rankMinorFiberPatch g t i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let r := Module.finrank ℝ
    (LinearMap.range
      (fderiv ℝ g (x : RealEuclidean a)).toLinearMap)
  have hr : r ≤ a := by
    have hr' := LinearMap.finrank_range_le
      (fderiv ℝ g (x : RealEuclidean a)).toLinearMap
    simpa only [r, Module.finrank_fin_fun] using hr'
  let k : Fin (a + 1) := ⟨r, Nat.lt_succ_of_le hr⟩
  have hrank : Module.finrank ℝ
      (LinearMap.range
        (fderiv ℝ g (x : RealEuclidean a)).toLinearMap) = (k : ℕ) := rfl
  obtain ⟨rows, cols, hminor⟩ :=
    ((finrank_range_fderiv_eq_iff_standardJacobianMinors
      ((hg.differentiable one_ne_zero).differentiableAt)).mp hrank).1
  rw [Set.mem_iUnion]
  exact ⟨⟨k, rows, cols⟩, hrank, hminor⟩

/-! ## A finite atlas of fixed square maps -/

/-- A finite collection of fixed square family maps whose regular fibers,
taken as a dependent sum, encode every connected component of every fiber of
`g`.  Each dimension and square map is fixed before `t` varies. -/
structure FiniteFixedSquareRegularFiberComponentEncoding
    (G : (n : ℕ) → Set (RealEuclideanFunction n))
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b) where
  Patch : Type
  patchFintype : Fintype Patch
  dimension : Patch → ℕ
  squareMap : ∀ i, RealEuclidean (dimension i) → RealEuclidean (dimension i)
  fiberTarget : ∀ i, RealEuclidean b → RealEuclidean (dimension i)
  squareMap_mem : ∀ i, FunctionTupleInFamily G (squareMap i)
  encode : ∀ t, ConnectedComponents (g ⁻¹' {t}) →
    Σ i, smoothRegularFiber (squareMap i) (fiberTarget i t)
  encode_injective : ∀ t, Function.Injective (encode t)

attribute [instance]
  FiniteFixedSquareRegularFiberComponentEncoding.patchFintype

/-- One ordinary fixed-square encoding is a singleton finite atlas. -/
def FixedSquareRegularFiberComponentEncoding.toFinite
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (encoding : FixedSquareRegularFiberComponentEncoding G g) :
    FiniteFixedSquareRegularFiberComponentEncoding G g where
  Patch := PUnit
  patchFintype := inferInstance
  dimension _ := encoding.dimension
  squareMap _ := encoding.squareMap
  fiberTarget _ := encoding.fiberTarget
  squareMap_mem _ := encoding.squareMap_mem
  encode t c := ⟨PUnit.unit, encoding.encode t c⟩
  encode_injective t := by
    intro c d h
    have h' : encoding.encode t c = encoding.encode t d := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact encoding.encode_injective t h'

/-- A finite atlas transfers uniform regular-fiber bounds to one uniform
component bound.  No construction merging the square maps is needed for this
cardinal conclusion. -/
theorem FiniteFixedSquareRegularFiberComponentEncoding.exists_uniform_component_bound
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (encoding : FiniteFixedSquareRegularFiberComponentEncoding G g)
    (hregular : HasUniformSquareRegularFiberBound G) :
    ∃ N : ℕ, ∀ t,
      ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ N := by
  choose bound hbound using fun i ↦
    hregular (encoding.dimension i) (encoding.squareMap i)
      (encoding.squareMap_mem i)
  refine ⟨∑ i, bound i, fun t ↦ ?_⟩
  have hfinite : ∀ i,
      Finite (smoothRegularFiber (encoding.squareMap i)
        (encoding.fiberTarget i t)) := by
    intro i
    exact ENat.card_lt_top.mp
      ((hbound i (encoding.fiberTarget i t)).trans_lt (by simp))
  let _ (i : encoding.Patch) :
      Finite (smoothRegularFiber (encoding.squareMap i)
        (encoding.fiberTarget i t)) := hfinite i
  calc
    ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤
        ENat.card (Σ i, smoothRegularFiber (encoding.squareMap i)
          (encoding.fiberTarget i t)) :=
      ENat.card_le_card_of_injective (encoding.encode_injective t)
    _ = Nat.card (Σ i, smoothRegularFiber (encoding.squareMap i)
          (encoding.fiberTarget i t)) :=
      ENat.card_eq_coe_natCard _
    _ = ∑ i, Nat.card (smoothRegularFiber (encoding.squareMap i)
          (encoding.fiberTarget i t)) := by
      norm_cast
      exact Nat.card_sigma
    _ ≤ ∑ i, bound i := by
      norm_cast
      apply Finset.sum_le_sum
      intro i _hi
      have hi := hbound i (encoding.fiberTarget i t)
      rw [ENat.card_eq_coe_natCard] at hi
      exact_mod_cast hi

/-! ## Assembly from the actual rank/minor cover -/

/-- Patchwise fixed-square data for the canonical finite rank/minor cover.
The injection is required only on the connected components of the indicated
patch; maps and dimensions stay fixed while the original target varies. -/
structure RankMinorPatchFixedSquareEncoding
    (G : (n : ℕ) → Set (RealEuclideanFunction n))
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b) where
  dimension : RankMinorPatchIndex a b → ℕ
  squareMap : ∀ i, RealEuclidean (dimension i) → RealEuclidean (dimension i)
  fiberTarget : ∀ i, RealEuclidean b → RealEuclidean (dimension i)
  squareMap_mem : ∀ i, FunctionTupleInFamily G (squareMap i)
  encodePatch : ∀ i t,
    ConnectedComponents (rankMinorFiberPatch g t i) →
      smoothRegularFiber (squareMap i) (fiberTarget i t)
  encodePatch_injective : ∀ i t, Function.Injective (encodePatch i t)

/-- The canonical rank/minor cover and patchwise encoders assemble into a
finite fixed-square atlas for the full fibers. -/
noncomputable def RankMinorPatchFixedSquareEncoding.toFinite
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g)
    (encoding : RankMinorPatchFixedSquareEncoding G g) :
    FiniteFixedSquareRegularFiberComponentEncoding G g := by
  classical
  let Patch := RankMinorPatchIndex a b
  let cover (t : RealEuclidean b) : Patch → Set (g ⁻¹' {t}) :=
    fun i ↦ rankMinorFiberPatch g t i
  have hsurj : ∀ t, Function.Surjective
      (connectedComponentsCoverMap (cover t)) := by
    intro t
    exact connectedComponentsCoverMap_surjective (cover t)
      (iUnion_rankMinorFiberPatch_eq_univ g hg t)
  let choosePatch (t : RealEuclidean b) :
      ConnectedComponents (g ⁻¹' {t}) →
        Σ i, ConnectedComponents (rankMinorFiberPatch g t i) :=
    Function.surjInv (hsurj t)
  have hchoosePatch : ∀ t, Function.Injective (choosePatch t) := by
    intro t
    exact Function.injective_surjInv (hsurj t)
  let encodeSigma (t : RealEuclidean b) :
      (Σ i, ConnectedComponents (rankMinorFiberPatch g t i)) →
        Σ i, smoothRegularFiber (encoding.squareMap i)
          (encoding.fiberTarget i t) :=
    fun p ↦ ⟨p.1, encoding.encodePatch p.1 t p.2⟩
  have hencodeSigma : ∀ t, Function.Injective (encodeSigma t) := by
    intro t p q hpq
    rcases p with ⟨i, p⟩
    rcases q with ⟨j, q⟩
    change (⟨i, encoding.encodePatch i t p⟩ :
        Σ r, smoothRegularFiber (encoding.squareMap r)
          (encoding.fiberTarget r t)) =
      ⟨j, encoding.encodePatch j t q⟩ at hpq
    have hij : i = j := (Sigma.mk.inj_iff.mp hpq).1
    subst j
    have hvalue : encoding.encodePatch i t p =
        encoding.encodePatch i t q :=
      eq_of_heq (Sigma.mk.inj_iff.mp hpq).2
    have hp : p = q := encoding.encodePatch_injective i t hvalue
    subst q
    rfl
  exact
    { Patch := Patch
      patchFintype := inferInstance
      dimension := encoding.dimension
      squareMap := encoding.squareMap
      fiberTarget := encoding.fiberTarget
      squareMap_mem := encoding.squareMap_mem
      encode := fun t ↦ encodeSigma t ∘ choosePatch t
      encode_injective := fun t ↦
        (hencodeSigma t).comp (hchoosePatch t) }

/-- Consequently, patchwise encodings for the canonical finite rank/minor
cover are sufficient for a uniform component bound. -/
theorem RankMinorPatchFixedSquareEncoding.exists_uniform_component_bound
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g)
    (encoding : RankMinorPatchFixedSquareEncoding G g)
    (hregular : HasUniformSquareRegularFiberBound G) :
    ∃ N : ℕ, ∀ t,
      ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ N :=
  (encoding.toFinite hg).exists_uniform_component_bound hregular

/-! ## Family-level consequences -/

/-- Every family tuple admits a finite atlas of fixed square regular-fiber
encoders. -/
def HasFiniteFixedSquareRegularFiberComponentEncodingsForFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ a b (g : RealEuclidean a → RealEuclidean b),
    FunctionTupleInFamily G g →
      Nonempty (FiniteFixedSquareRegularFiberComponentEncoding G g)

/-- The former one-square-map hypothesis implies the finite-atlas hypothesis
by using a singleton atlas. -/
theorem HasFixedSquareRegularFiberComponentEncodingsForFamily.hasFiniteEncodings
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hencoding : HasFixedSquareRegularFiberComponentEncodingsForFamily G) :
    HasFiniteFixedSquareRegularFiberComponentEncodingsForFamily G := by
  intro a b g hg
  obtain ⟨encoding⟩ := hencoding a b g hg
  exact ⟨encoding.toFinite⟩

/-- Finite fixed-square atlases are sufficient for uniform fiber finiteness.
This weakens the one-square-map hypothesis in
`HasFixedSquareRegularFiberComponentEncodingsForFamily`. -/
theorem HasFiniteFixedSquareRegularFiberComponentEncodingsForFamily.hasUniformFiberFiniteness
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hencoding :
      HasFiniteFixedSquareRegularFiberComponentEncodingsForFamily G)
    (hregular : HasUniformSquareRegularFiberBound G) :
    HasUniformFiberFiniteness G := by
  intro a b g hg
  obtain ⟨encoding⟩ := hencoding a b g hg
  exact encoding.exists_uniform_component_bound hregular

/-- Every family tuple admits patchwise encoders for its canonical finite
rank/minor cover. -/
def HasRankMinorPatchFixedSquareEncodingsForFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ a b (g : RealEuclidean a → RealEuclidean b),
    FunctionTupleInFamily G g →
      Nonempty (RankMinorPatchFixedSquareEncoding G g)

/-- Canonical rank/minor patch encoders supply finite atlases for every family
tuple. -/
theorem HasRankMinorPatchFixedSquareEncodingsForFamily.hasFiniteEncodings
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hpatch : HasRankMinorPatchFixedSquareEncodingsForFamily G) :
    HasFiniteFixedSquareRegularFiberComponentEncodingsForFamily G := by
  intro a b g hg
  obtain ⟨encoding⟩ := hpatch a b g hg
  have hgDiff : ContDiff ℝ 1 g := by
    rw [contDiff_pi]
    intro i
    exact (hsmooth a (fun x ↦ g x i) (hg i)).of_le (by norm_num)
  exact ⟨encoding.toFinite hgDiff⟩

/-- Exact finite-patch reduction of Lion's uniform-fiber conclusion.  Once
the patchwise encoders exist, Gabrielov's uniform bound for each fixed square
map may be summed over the finite rank/minor index. -/
theorem hasUniformFiberFiniteness_of_rankMinorPatchEncodings
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hregular : HasUniformSquareRegularFiberBound G)
    (hpatch : HasRankMinorPatchFixedSquareEncodingsForFamily G) :
    HasUniformFiberFiniteness G :=
  (hpatch.hasFiniteEncodings hsmooth).hasUniformFiberFiniteness hregular

/-- Gabrielov upper numbers plus patchwise fixed-square encoders give the
uniform fiber theorem directly; no literal merger of the finitely many square
maps is required. -/
theorem hasUniformFiberFiniteness_of_gabrielovUpperNumbers_of_rankMinorPatchEncodings
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hupper : ∀ n (F : RealEuclidean n → RealEuclidean n),
      FunctionTupleInFamily G F →
        HasGabrielovUniformUpperNumberProperty F)
    (hpatch : HasRankMinorPatchFixedSquareEncodingsForFamily G) :
    HasUniformFiberFiniteness G := by
  apply hasUniformFiberFiniteness_of_rankMinorPatchEncodings hsmooth
  · exact hasUniformSquareRegularFiberBound_of_gabrielovUpperNumbers
      hsmooth hupper
  · exact hpatch

/-! ## Exact interface for a literal one-map merger -/

/-- Extra data which embeds all regular fibers in a finite atlas into one
regular fiber of one fixed square family map.  This is precisely the datum
needed to recover the literal one-map encoding interface; it is not needed to
obtain the uniform cardinal bound above. -/
structure FiniteFixedSquareRegularFiberComponentEncoding.OneMapMerger
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (encoding : FiniteFixedSquareRegularFiberComponentEncoding G g) where
  dimension : ℕ
  squareMap : RealEuclidean dimension → RealEuclidean dimension
  fiberTarget : RealEuclidean b → RealEuclidean dimension
  squareMap_mem : FunctionTupleInFamily G squareMap
  merge : ∀ t,
    (Σ i, smoothRegularFiber (encoding.squareMap i)
      (encoding.fiberTarget i t)) →
      smoothRegularFiber squareMap (fiberTarget t)
  merge_injective : ∀ t, Function.Injective (merge t)

/-- A finite atlas plus a one-map merger gives the original
`FixedSquareRegularFiberComponentEncoding`. -/
def FiniteFixedSquareRegularFiberComponentEncoding.toFixedSquare
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (encoding : FiniteFixedSquareRegularFiberComponentEncoding G g)
    (merger : encoding.OneMapMerger) :
    FixedSquareRegularFiberComponentEncoding G g where
  dimension := merger.dimension
  squareMap := merger.squareMap
  fiberTarget := merger.fiberTarget
  squareMap_mem := merger.squareMap_mem
  encode t := merger.merge t ∘ encoding.encode t
  encode_injective t :=
    (merger.merge_injective t).comp (encoding.encode_injective t)

/-- Rank/minor patch encodings produce one literal fixed-square encoding as
soon as the finite atlas admits the explicit merger above. -/
def RankMinorPatchFixedSquareEncoding.toFixedSquare
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hg : ContDiff ℝ 1 g)
    (encoding : RankMinorPatchFixedSquareEncoding G g)
    (merger : (encoding.toFinite hg).OneMapMerger) :
    FixedSquareRegularFiberComponentEncoding G g :=
  (encoding.toFinite hg).toFixedSquare merger

end AbelFormalization
