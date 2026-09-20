# Case 2 reachable-stage source premises

The current `Scratch/Case2RecursiveAssemblyDraft.lean` assumes WS5 membership and smooth singular-witness selection for **every** map of every visible arity. That is stronger than the source: Wilkie starts with one map whose coordinates lie in the weak function family and then repeatedly pulls that map back along affine visible-coordinate insertions. The source inputs should be required only for those descendants. A mere corollary of the current universal theorem cannot narrow these hypotheses; its recursion must first be refactored to carry a reachable-stage witness.

## Noncircular reachable class

```lean
abbrev WilkieCase2StageMap (m q : ℕ) :=
  ((Fin m → ℝ) × (Fin q → ℝ)) → RealEuclidean q

inductive WilkieCase2Reachable {n q : ℕ}
    (F₀ : WilkieCase2StageMap n q) :
    (m : ℕ) → WilkieCase2StageMap m q → Prop where
  | original : WilkieCase2Reachable F₀ n F₀
  | visibleSlice {m : ℕ} {G : WilkieCase2StageMap (m + 1) q}
      (hG : WilkieCase2Reachable F₀ (m + 1) G)
      (i : Fin (m + 1)) (b : ℝ) :
      WilkieCase2Reachable F₀ m
        (G ∘ wilkieCase2VisibleInsert i b)
```

The constructors mention neither the exceptional set nor regularity, boundedness, an attained point, or the final result. They permit **arbitrary** fixed values `b`, which avoids defining reachability in terms of the good-value choice being proved. The recursive proof passes `hReach.visibleSlice i b` to the lower stage after choosing its good attained value. Each reachable map is an affine pullback of the original map; geometric-family `affine_comp` can prove coordinate membership by induction on this relation. The coordinate function `x ↦ x.1 i` is polynomial after flattening, so its membership is independent of the original map.

## Predicate-parametric recursive theorem

Refactor `wilkieCase2_recursive_fixedMinorAlternative` to take a stage predicate `P` and its affine-slice closure. Keep the target `a₀` fixed through the recursion:

```lean
theorem wilkieCase2_recursive_fixedMinorAlternative_of_predicate
    {C : EuclideanSetFamily}
    (hC : PositiveArityOMinimalWeakSetStructure C)
    {q : ℕ} (hq : 0 < q) (a₀ : RealEuclidean q)
    (P : ∀ m : ℕ, WilkieCase2StageMap m q → Prop)
    (hPslice : ∀ m (G : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)) (b : ℝ),
      P (m + 1) G → P m (G ∘ wilkieCase2VisibleInsert i b))
    (hBmem : ∀ m (G : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      P (m + 1) G →
      {v : RealEuclidean 1 |
        v 0 ∈ Wilkie28MathlibOnly.exceptionalParameterSet
          G (fun x ↦ x.1 i) a₀} ∈ C 1)
    (hselection : ∀ m (G : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      P (m + 1) G → ContDiff ℝ 1 G →
      (∀ y, G y = a₀ → Function.Surjective (fderiv ℝ G y)) →
      Wilkie28MathlibOnly.SmoothSingularWitnessSelection
        G (fun x ↦ x.1 i) a₀) :
    ∀ m (G : WilkieCase2StageMap m q)
      (U : Set (RealEuclidean m)),
      P m G → ContDiff ℝ 1 G → IsOpen U → Convex ℝ U →
      (∀ y, G y = a₀ → Function.Surjective (fderiv ℝ G y)) →
      Bornology.IsBounded (wilkieCase2VisibleCylinderFiber G a₀ U) →
      (wilkieCase2VisibleCylinderFiber G a₀ U).Nonempty →
      wilkieCase2RecursiveAlternative G a₀ U
```

The existing induction needs only three source-line changes: add `hP` to the stage hypotheses, use `hBmem m G i hP` and `hselection m G i hP hG hregular` in the infinite branch, and pass `hPslice m G i b hP` to the lower induction hypothesis. The terminal, finite-image, cylinder geometry, fixed-minor lifts, and final vertical fork are unchanged. Thus the predicate theorem is a genuine recursion, not an attempted derivation of universal `hBmem` from a restricted one.

## Original-map corollary

For a fixed original `F₀ : WilkieCase2StageMap n q` and target `a₀`, assume the two source inputs only when `G` is reachable from `F₀`:

```lean
theorem wilkieCase2_originalMap_fixedMinorAlternative
    {C : EuclideanSetFamily} {n q : ℕ}
    (hq : 0 < q) (F₀ : WilkieCase2StageMap n q)
    (a₀ : RealEuclidean q)
    (U : Set (RealEuclidean n))
    (hC : PositiveArityOMinimalWeakSetStructure C)
    (hBmemReachable : ∀ m (G : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      WilkieCase2Reachable F₀ (m + 1) G →
      {v : RealEuclidean 1 |
        v 0 ∈ Wilkie28MathlibOnly.exceptionalParameterSet
          G (fun x ↦ x.1 i) a₀} ∈ C 1)
    (hselectionReachable : ∀ m (G : WilkieCase2StageMap (m + 1) q)
        (i : Fin (m + 1)),
      WilkieCase2Reachable F₀ (m + 1) G → ContDiff ℝ 1 G →
      (∀ y, G y = a₀ → Function.Surjective (fderiv ℝ G y)) →
      Wilkie28MathlibOnly.SmoothSingularWitnessSelection
        G (fun x ↦ x.1 i) a₀)
    (hF₀ : ContDiff ℝ 1 F₀)
    (hUopen : IsOpen U) (hUconvex : Convex ℝ U)
    (hregular : ∀ y, F₀ y = a₀ →
      Function.Surjective (fderiv ℝ F₀ y))
    (hbounded : Bornology.IsBounded
      (wilkieCase2VisibleCylinderFiber F₀ a₀ U))
    (hnonempty : (wilkieCase2VisibleCylinderFiber F₀ a₀ U).Nonempty) :
    wilkieCase2RecursiveAlternative F₀ a₀ U
```

Its proof instantiates the predicate theorem with `P m G := WilkieCase2Reachable F₀ m G`, uses the `visibleSlice` constructor for `hPslice`, and supplies the initial witness by `original`. After this corollary, `wilkieCase2RecursiveAlternative_finalFork` yields Corollary 2.9's projection-or-fixed-minor interval for the original visible ball.

## Global regularity check

The recursion's global regularity hypothesis is source-correct. Theorem 2.8 excludes values `b` for which **any** point of the full fiber `F⁻¹ {a₀}` with visible pivot `b` makes `(F,pivot)` singular. Therefore a good `b` makes the augmented derivative surjective at every point of the full slice, including points outside the sliced visible domain. The affine insertion range then makes `a₀` a regular value of the globally defined sliced map. Wilkie states this explicitly on printed p. 405. By contrast, the inherited boundedness holds only for the restricted cylinder; it is transported from the standing bounded `wilkieFiberOver F a₀ U` through coordinate deletion. The current private helper `wilkieCase2VisibleInsert_globalRegular_of_good` uses the global exceptional-set condition and proves exactly this stronger regularity property.
