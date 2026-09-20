import AbelFormalization.LiftedComponentFiniteness
import AbelFormalization.ParametricSubmersionLinear
import AbelFormalization.SmoothGeometricFamily
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The fixed-square-map reduction in Lion's uniform-finiteness argument

This file isolates the cardinal and topological part of the uniform-in-target
argument.  If one fixed square family map has a regular point encoding every
connected component of every fiber of `g`, a uniform bound for the regular
fibers of that square map gives a uniform bound for the fibers of `g`.

The word *fixed* is essential: the dimension and the square map cannot depend
on the target of `g`.  The target of the square map is allowed to vary.  In the
Lagrange-multiplier application it records both the original fiber value and
an auxiliary squared-distance center.

The analytic assertion that turns pointwise `0`-regularity into a uniform
bound for all regular fibers of a fixed square map is named below as
`HasUniformSquareRegularFiberBound`.  No proof of that assertion from
`IsZeroRegularFunctionFamily` is claimed here.  Such a proof is the remaining
Gabrielov--Lion finiteness step; merely adjoining the target and auxiliary
parameters to one map does not supply its uniform cardinal bound.
-/

noncomputable section

open Set Function

namespace AbelFormalization

set_option autoImplicit false

/-! ## Extended-cardinal versions of the lifted-component argument -/

/-- If an auxiliary type meets every connected component through a base map,
then the connected-component quotient injects into the auxiliary type.  This
is the cardinal form of `finite_connectedComponents_of_finite_lifts`, without
any finiteness assumption on the auxiliary type. -/
theorem enatCard_connectedComponents_le_lifts
    {X Y : Type*} [TopologicalSpace X]
    (base : Y → X)
    (hmeet : ∀ x : X, ∃ y : Y, base y ∈ connectedComponent x) :
    ENat.card (ConnectedComponents X) ≤ ENat.card Y := by
  obtain ⟨pick, hpick⟩ :=
    exists_injective_connectedComponents_to_lifts base hmeet
  exact ENat.card_le_card_of_injective hpick

/-- Choosing a proper componentwise minimizer and then lifting that minimizer
gives a cardinal injection from connected components to the lift type. -/
theorem enatCard_connectedComponents_le_lifted_componentMinimizers
    {X Y : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f)
    (hcompact : ∀ r : ℝ, IsCompact {x | f x ≤ r})
    (base : Y → X)
    (hlift : ∀ x : X, x ∈ componentMinimizers f →
      ∃ y : Y, base y = x) :
    ENat.card (ConnectedComponents X) ≤ ENat.card Y := by
  apply enatCard_connectedComponents_le_lifts base
  intro x
  obtain ⟨y, hycomponent, hymin⟩ :=
    exists_componentMinimizer_of_compact_sublevel f hf hcompact x
  obtain ⟨z, hz⟩ := hlift y hymin
  refine ⟨z, ?_⟩
  simpa only [hz] using hycomponent

/-- A numerical bound on the lift type transfers to the connected-component
quotient. -/
theorem enatCard_connectedComponents_le_of_lifted_componentMinimizers_bound
    {X Y : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f)
    (hcompact : ∀ r : ℝ, IsCompact {x | f x ≤ r})
    (base : Y → X)
    (hlift : ∀ x : X, x ∈ componentMinimizers f →
      ∃ y : Y, base y = x)
    (N : ℕ) (hY : ENat.card Y ≤ N) :
    ENat.card (ConnectedComponents X) ≤ N :=
  (enatCard_connectedComponents_le_lifted_componentMinimizers
    f hf hcompact base hlift).trans hY

/-! ## Recording an auxiliary parameter in the target -/

section ParameterRecording

variable {X P Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Adjoin the parameter itself to the output of a parameterized map.  A
fiber of this map freezes the parameter while retaining the original
equations in the first output block. -/
def parameterRecordingMap (f : X × P → Y) : X × P → Y × P :=
  fun p ↦ (f p, p.2)

@[simp]
theorem mem_preimage_parameterRecordingMap_singleton
    (f : X × P → Y) (q : X × P) (y : Y) (p : P) :
    q ∈ parameterRecordingMap f ⁻¹' {(y, p)} ↔
      f q = y ∧ q.2 = p := by
  simp [parameterRecordingMap, Prod.ext_iff]

/-- The block derivative of `parameterRecordingMap`. -/
def parameterRecordingCLM (L : (X × P) →L[ℝ] Y) :
    (X × P) →L[ℝ] (Y × P) :=
  L.prod (ContinuousLinearMap.snd ℝ X P)

@[simp]
theorem parameterRecordingCLM_apply
    (L : (X × P) →L[ℝ] Y) (q : X × P) :
    parameterRecordingCLM L q = (L q, q.2) :=
  rfl

/-- The parameter-recording block map is surjective whenever the derivative
in the first variable is surjective.  This is the elementary triangular
linear-algebra calculation behind the universal-center construction. -/
theorem surjective_parameterRecordingCLM_of_surjective_fstPartial
    (L : (X × P) →L[ℝ] Y)
    (hpartial : Function.Surjective (fstPartial L)) :
    Function.Surjective (parameterRecordingCLM L) := by
  rintro ⟨y, p⟩
  obtain ⟨x, hx⟩ := hpartial (y - L (0, p))
  refine ⟨(x, p), ?_⟩
  apply Prod.ext
  · simp only [parameterRecordingCLM_apply]
    rw [show (x, p) = (x, 0) + (0, p) by ext <;> simp, map_add]
    change fstPartial L x + L (0, p) = y
    rw [hx, sub_add_cancel]
  · simp only [parameterRecordingCLM_apply]

/-- Fréchet differentiation commutes with recording the parameter. -/
theorem hasFDerivAt_parameterRecordingMap
    {f : X × P → Y} {L : (X × P) →L[ℝ] Y} {q : X × P}
    (hf : HasFDerivAt f L q) :
    HasFDerivAt (parameterRecordingMap f) (parameterRecordingCLM L) q := by
  change HasFDerivAt (fun p : X × P ↦ (f p, p.2))
    (L.prod (ContinuousLinearMap.snd ℝ X P)) q
  exact hf.prodMk (ContinuousLinearMap.snd ℝ X P).hasFDerivAt

/-- Formula for the derivative of the parameter-recording map. -/
theorem fderiv_parameterRecordingMap
    {f : X × P → Y} {q : X × P}
    (hf : DifferentiableAt ℝ f q) :
    fderiv ℝ (parameterRecordingMap f) q =
      parameterRecordingCLM (fderiv ℝ f q) :=
  (hasFDerivAt_parameterRecordingMap hf.hasFDerivAt).fderiv

/-- Surjectivity of the fixed-parameter derivative implies surjectivity of
the derivative after the parameter is appended to the output. -/
theorem surjective_fderiv_parameterRecordingMap_of_surjective_fstPartial
    {f : X × P → Y} {q : X × P}
    (hf : DifferentiableAt ℝ f q)
    (hpartial : Function.Surjective (fstPartial (fderiv ℝ f q))) :
    Function.Surjective (fderiv ℝ (parameterRecordingMap f) q) := by
  rw [fderiv_parameterRecordingMap hf]
  exact surjective_parameterRecordingCLM_of_surjective_fstPartial
    (fderiv ℝ f q) hpartial

end ParameterRecording

/-! ## The remaining analytic property and the fixed-map encoding -/

/-- The Gabrielov-type uniform regular-fiber property needed by the fixed-map
reduction.  For each fixed square tuple in the family, one natural number
bounds all of its smooth regular fibers as the target varies.

This is stronger than the quantifier pattern in
`IsZeroRegularFunctionFamily`, which says only that each individual regular
fiber is finite. -/
def HasUniformSquareRegularFiberBound
    (G : (n : ℕ) → Set (RealEuclideanFunction n)) : Prop :=
  ∀ n (F : RealEuclidean n → RealEuclidean n),
    FunctionTupleInFamily G F → ∃ N : ℕ, ∀ u,
      ENat.card (smoothRegularFiber F u) ≤ N

/-- Data exhibiting one fixed square family map whose regular fibers encode
the connected components of every fiber of `g`.  `fiberTarget t` may include
the original target `t` and any auxiliary parameter selected for that fiber;
`squareMap` itself remains independent of `t`.

For the intended Morse--Lagrange construction, `encode t` chooses one lifted
componentwise distance minimizer.  Its primal coordinate determines the
component, which proves injectivity. -/
structure FixedSquareRegularFiberComponentEncoding
    (G : (n : ℕ) → Set (RealEuclideanFunction n))
    {a b : ℕ} (g : RealEuclidean a → RealEuclidean b) where
  dimension : ℕ
  squareMap : RealEuclidean dimension → RealEuclidean dimension
  fiberTarget : RealEuclidean b → RealEuclidean dimension
  squareMap_mem : FunctionTupleInFamily G squareMap
  encode : ∀ t, ConnectedComponents (g ⁻¹' {t}) →
    smoothRegularFiber squareMap (fiberTarget t)
  encode_injective : ∀ t, Function.Injective (encode t)

/-- A fixed-square regular-fiber encoding gives the pointwise cardinal
comparison used in the uniform argument. -/
theorem FixedSquareRegularFiberComponentEncoding.enatCard_le_regularFiber
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (encoding : FixedSquareRegularFiberComponentEncoding G g)
    (t : RealEuclidean b) :
    ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤
      ENat.card
        (smoothRegularFiber encoding.squareMap (encoding.fiberTarget t)) := by
  exact ENat.card_le_card_of_injective (encoding.encode_injective t)

/-- `0`-regularity applied to the fixed square map gives only targetwise
finiteness of the encoded connected-component types.  This lemma deliberately
does not produce one natural-number bound valid for all `t`. -/
theorem FixedSquareRegularFiberComponentEncoding.finite_connectedComponents
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hzero : IsZeroRegularFunctionFamily G)
    (encoding : FixedSquareRegularFiberComponentEncoding G g)
    (t : RealEuclidean b) :
    Finite (ConnectedComponents (g ⁻¹' {t})) := by
  letI : Finite
      (smoothRegularFiber encoding.squareMap (encoding.fiberTarget t)) :=
    Set.finite_coe_iff.mpr
      (hzero encoding.dimension encoding.squareMap encoding.squareMap_mem
        (encoding.fiberTarget t))
  exact Finite.of_injective (encoding.encode t)
    (encoding.encode_injective t)

/-- Once the genuine uniform regular-fiber bound is available, a fixed-square
encoding transfers it to a bound independent of the original fiber target. -/
theorem FixedSquareRegularFiberComponentEncoding.exists_uniform_component_bound
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    {a b : ℕ} {g : RealEuclidean a → RealEuclidean b}
    (hregular : HasUniformSquareRegularFiberBound G)
    (encoding : FixedSquareRegularFiberComponentEncoding G g) :
    ∃ N : ℕ, ∀ t,
      ENat.card (ConnectedComponents (g ⁻¹' {t})) ≤ N := by
  obtain ⟨N, hN⟩ := hregular encoding.dimension encoding.squareMap
    encoding.squareMap_mem
  refine ⟨N, fun t => ?_⟩
  exact (encoding.enatCard_le_regularFiber t).trans
    (hN (encoding.fiberTarget t))

/-- A uniform regular-fiber bound in particular implies Lion's pointwise
`0`-regular condition.  The converse is precisely the nontrivial direction
that is not formalized in this file. -/
theorem HasUniformSquareRegularFiberBound.isZeroRegularFunctionFamily
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hregular : HasUniformSquareRegularFiberBound G) :
    IsZeroRegularFunctionFamily G := by
  intro n F hF t
  obtain ⟨N, hN⟩ := hregular n F hF
  rw [← Set.finite_coe_iff]
  exact ENat.card_lt_top.mp ((hN t).trans_lt (by simp))

end AbelFormalization
