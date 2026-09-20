# Wilkie 2.8–2.9 fixed-minor audit (source-only)

Source: Wilkie, *A theorem of the complement and some new o-minimal structures*, Selecta Math. 5 (1999), printed pp. 404–405, PDF pages 8–9 of `/Users/artemchernikov/Downloads/s000290050052 (1).pdf`.

## Exact target

Let `n,k ≥ 1`, `F : RealEuclidean (n+k) → RealEuclidean k` be globally `C¹` and have coordinate functions in Wilkie's expanded weak family `S̃`. Let `a` be a regular value of `F` in the rectangular sense

```lean
∀ x, F x = a → Function.Surjective (fderiv ℝ F x)
```

Let `U` be a nonempty open ball in `RealEuclidean n`, and define

```lean
X := {x : RealEuclidean (n+k) |
  F x = a ∧ realEuclideanTakeLeft x ∈ U}
```

Assume `X.Nonempty`, `Bornology.IsBounded X`, and `realEuclideanTakeLeft '' X ≠ U` (equivalently, some point of `U` is missed). Corollary 2.9 then asks for one **fixed** `cols : Fin k ↪ Fin (n+k)` and `η : ℝ` with `0 < η` such that

```lean
Set.Icc (0 : ℝ) η ⊆
  (fun x ↦ (standardJacobianColumnMinor F cols x) ^ 2) '' X
```

The paper assumes an open ball, not an arbitrary open set. The squaring is part of its statement. The conclusion is an image interval on the bounded regular fiber, not merely existence of a zero determinant.

## Already formalized

* `fderiv_surjective_iff_exists_standardJacobianColumnMinor_ne_zero` in `SmoothFamilyRectangularJacobianMinors.lean` produces a nonzero maximal minor at every regular fiber point.
* `IsGeometricFunctionFamily.standardJacobianColumnMinor_mem` in the same module puts each selected determinant in a derivative-closed geometric function family. Its square is handled by the geometric family's square closure, once the target set-family interface is chosen.
* `continuous_standardJacobianMinor_of_contDiff_one` in `SmoothFamilyConstantRankLocalFiber.lean` yields continuity of each fixed column minor by taking row embedding `Function.Embedding.refl (Fin k)`.
* `exists_localProjectionChart_of_standardJacobianMinor_ne_zero` in `SmoothFamilyRankStratumLocalFiber.lean` supplies an implicit chart for the equation map near a nonzero selected minor. It does not yet identify the visible projection on the level fiber as a local homeomorphism.
* Mathlib `isPreconnected_connectedComponentIn`, `connectedComponentIn_subset`, and `IsPreconnected.intermediate_value` provide the connected-component/IVT endpoint. `WilkieFixedMinorConnectedInterval.lean` stages this as a source-only generic theorem with explicit zero and nonzero witnesses. `eq_of_nonempty_relatively_clopen_of_preconnected` stages the last connected-ball conclusion once relative openness and closedness of a projected component are proved.
* `PositiveArityOMinimalWeakSetStructure.coordinateImage_unaryPieceDecomposable` and `UnaryPieceDecomposable.finite_of_interior_eq_empty` in `CharbonnelSection5ElementaryInputs.lean` formalize the unary consequence of WS5: an infinite unary member must contain an interval.

## Differential and topological gaps

1. **Wilkie 2.8 regular slicing.** For `f` a visible coordinate, the set of `b` with `(a,b)` singular for `(F,f)` must be placed in the expanded set family. Wilkie uses derivative closure (his 2.6), WS5, weak selection (2.3), and piecewise `C¹` smoothness (2.5) to prove it finite. No maintained weak-selection/smooth-selection theorem or exact singular-value-image membership interface was found. The square-map null-critical-values result in `LionUpperNumbersCenterControl.lean` does not cover this rectangular augmented map and does not by itself make an arbitrary null unary set finite.
2. **Finite visible projection branch.** A connected component `Y` of the **full** fiber through `x∈X` must be shown to stay over one point of `U` when `π[X]` is finite. This follows by pure topology: `π[Y]` is preconnected, and its intersection with the open ball `U` is nonempty and finite; the intersection is relatively clopen in `π[Y]`, hence equals `π[Y]`, which is then a singleton. The staged `eq_singleton_of_preconnected_finite_inter_open` supplies this set argument. Then `Y` is bounded and globally closed, hence compact. For a nonzero fixed minor at `x`, show the complementary-coordinate projection is a local homeomorphism on `Y`; if that minor never vanished on compact `Y`, its image would be a nonempty compact open subset of `ℝⁿ`, impossible for `n≥1`. The current selected-output chart does not implement this complementary projection.
3. **Infinite visible projection branch.** Wilkie inductively fixes visible coordinates using 2.8. Each slice needs insertion/permutation of a coordinate, regularity transport from `(F,f)` to the sliced `F`, open-ball slice geometry, boundedness, nonemptiness, and exact transport of a selected minor back to the original matrix. These are not packaged in the maintained local chart modules.
4. **Vertical minor fork.** Once a point has nonzero minor in the last `k` (hidden) columns, construct the square map `(π,F)` and prove its derivative invertible from that block determinant. The inverse function theorem should make `π` locally open on the fiber. For a connected component `Y` of `X`, boundedness and relative closedness in `U×ℝᵏ` make `π[Y]` relatively closed in `U`; if the vertical determinant is nonzero everywhere on `Y`, its local openness makes `π[Y]` relatively open. The staged relative-clopen lemma then gives `π[Y]=U`, contradicting missing projection. Hence the **same vertical minor** vanishes on `Y` and the staged IVT theorem applies.

The narrowest useful next theorem is the vertical-minor fork: from `F` globally `C¹`, rectangular regularity, bounded `X`, `U` an open ball, and a component of `X` containing a point with nonzero hidden-column determinant, prove either a zero of that determinant in that component or that the component projects onto all of `U`. This is differential topology and properness over `U`; it requires no weak selection. The finite-projection case and the 2.8 slicing induction are separate prerequisites for obtaining such a component in every source-shaped instance.

No Lean or Lake command was run. The staged Lean module is unimported and has a separate Scratch `#print axioms` file awaiting parent compilation.
