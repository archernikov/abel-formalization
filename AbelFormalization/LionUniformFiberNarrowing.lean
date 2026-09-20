import AbelFormalization.LionUpperNumbersCenterControl

/-!
# The remaining Lion--Gabrielov uniform-fiber interface

`LionUpperNumbersCenterControl` turns Gabrielov's uniform upper-number property
for every fixed square tuple into `HasUniformSquareRegularFiberBound`.  The
remaining geometric bridge to arbitrary rectangular maps is the construction,
for each such map, of the fixed-square component encoding already defined in
`LionUniformRegularFiberEncoding`.

The property below records only that construction.  It contains no numerical
bound and does not follow from pointwise finiteness of regular fibers.  The
theorem then composes the two existing reductions without changing their
quantifier order.
-/

noncomputable section

namespace AbelFormalization

set_option autoImplicit false

/-- Every family tuple has a fixed square regular-fiber encoding of all of its
fiber-component types.  The square map may depend on the tuple, but it is fixed
before the original fiber target varies. -/
def HasFixedSquareRegularFiberComponentEncodingsForFamily
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ a b (g : RealEuclidean a → RealEuclidean b),
    FunctionTupleInFamily G g →
      Nonempty (FixedSquareRegularFiberComponentEncoding G g)

/-- Fixed-square encodings transfer a uniform regular-fiber bound to uniform
connected-component bounds for all family maps. -/
theorem HasFixedSquareRegularFiberComponentEncodingsForFamily.hasUniformFiberFiniteness
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hencoding : HasFixedSquareRegularFiberComponentEncodingsForFamily G)
    (hregular : HasUniformSquareRegularFiberBound G) :
    HasUniformFiberFiniteness G := by
  intro a b g hg
  obtain ⟨encoding⟩ := hencoding a b g hg
  exact
    FixedSquareRegularFiberComponentEncoding.exists_uniform_component_bound
      hregular encoding

/-- Exact remaining Lion--Gabrielov composition: Gabrielov bounds the regular
fibers of each fixed square family tuple, and the fixed-square encodings
transfer those bounds to all fibers of all rectangular family tuples. -/
theorem hasUniformFiberFiniteness_of_gabrielovUpperNumbers_of_fixedSquareEncodings
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hsmooth : IsEverywhereSmoothFunctionFamily G)
    (hupper : ∀ n (F : RealEuclidean n → RealEuclidean n),
      FunctionTupleInFamily G F →
        HasGabrielovUniformUpperNumberProperty F)
    (hencoding : HasFixedSquareRegularFiberComponentEncodingsForFamily G) :
    HasUniformFiberFiniteness G := by
  have hregular : HasUniformSquareRegularFiberBound G :=
    hasUniformSquareRegularFiberBound_of_gabrielovUpperNumbers hsmooth hupper
  exact
    HasFixedSquareRegularFiberComponentEncodingsForFamily.hasUniformFiberFiniteness
      hencoding hregular

end AbelFormalization
