# Case 2 affine-family closure and the exceptional unary premise

This is a source-level audit; no Lean compilation was run. It concerns only the WS5 set-membership premise `hBmem` in `Scratch/Case2RecursiveAssemblyDraft.lean`. It does not establish Wilkie's smooth singular-witness selection.

## Exact scope of the current premise

`wilkieCase2_recursive_fixedMinorAlternative` currently takes an arbitrary weak family `C` and asks for membership for **every** `m`, product map `F`, target `a`, and visible coordinate `i` (lines 225–230). This universally quantified premise cannot follow from the Abel family: arbitrary `F` need not have Abel-family coordinates, and arbitrary `C` need not be the Charbonnel closure. The theorem needs a specialization with

```lean
C := charbonnelClosure (literalZeroSetFamily (abelGeometricFamily A))
```

and a coordinatewise Abel-family invariant for the maps encountered in its recursion. The invariant may be stated for the flat presentation

```lean
H := F ∘ (wilkieCase2ProductFlatEquiv m q).symm
hH : FunctionTupleInFamily (abelGeometricFamily A) H
```

at each arity. Proving `hH` for the original Abel map is a separate datum; the affine-closure API propagates it to every recursively selected slice.

## Closure under each selected slice

The maintained `abelGeometricFamily_affine_comp` (or `IsGeometricFunctionFamily.affine_comp`) preserves every scalar coordinate of a tuple under an affine map. `IsAbel.geometric_smooth_derivativeClosed_abelGeometricFamily` supplies the three structural hypotheses for `wilkie28_exceptionalParameterSet_mem_literalZeroCharbonnel` (which proves the needed unary closure membership for flat maps). `wilkieCase2_flat_slice_map_eq` identifies the flattened lower product map with

```lean
H ∘ wilkieCase2FlatCastInsert i b.
```

The missing elementary adapter is an affine-map witness for `wilkieCase2FlatCastInsert`. A precise source target is

```lean
def wilkieCase2FlatCastInsertAffine {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ) :
    RealEuclidean (m + q) →ᵃ[ℝ]
      RealEuclidean ((m + 1) + q)

theorem wilkieCase2FlatCastInsertAffine_apply {m q : ℕ}
    (i : Fin (m + 1)) (b : ℝ)
    (z : RealEuclidean (m + q)) :
    wilkieCase2FlatCastInsertAffine i b z =
      wilkieCase2FlatCastInsert i b z
```

One construction uses the linear function `wilkieCase2FlatCastInsert i 0` plus the constant vector `wilkieCase2FlatCastInsert i b 0`, exactly as `integerAffineEquationMap` is built from a linear map and `AffineMap.const`. Componentwise `Fin.insertNth` identities prove linearity and the displayed equality; the arity cast is just coordinate reindexing. The maintained `wilkieCase2_coordinateInsertLinear` is the same zero-insertion linear part before the cast. Once this adapter exists, the tuple step is coordinatewise:

```lean
theorem case2_flatTuple_mem_slice
    {G : (n : ℕ) → Set (RealEuclideanFunction n)}
    (hG : IsGeometricFunctionFamily G)
    {m q : ℕ}
    (H : RealEuclidean ((m + 1) + q) → RealEuclidean q)
    (hH : FunctionTupleInFamily G H)
    (i : Fin (m + 1)) (b : ℝ) :
    FunctionTupleInFamily G (H ∘ wilkieCase2FlatCastInsert i b) := by
  intro j
  -- Convert `(fun z => H (wilkieCase2FlatCastInsert i b z) j)`
  -- to `(fun z => H z j) ∘ wilkieCase2FlatCastInsertAffine i b`.
  -- Apply `hG.affine_comp (hH j)`, then the affine-apply equality.
```

This is a deterministic property for **every** value `b`, including the good value selected by Theorem 2.8. An equivalent global reachability invariant is `H = H₀ ∘ ℓ` for an affine `ℓ` into the original flat source. Composition with `wilkieCase2FlatCastInsertAffine i b` updates `ℓ` at each recursion step.

For the exceptional value at a visible coordinate, the flat pivot is the coordinate polynomial

```lean
let j : Fin ((m + 1) + q) := Fin.castAdd q i
let g : RealEuclideanFunction ((m + 1) + q) := fun z => z j
have hg : g ∈ abelGeometricFamily A ((m + 1) + q) := by
  simpa [g] using
    (isGeometricFunctionFamily_abelGeometricFamily A).polynomial
      (MvPolynomial.X j)
```

The canonical product/flat equivalence gives `g (wilkieCase2ProductFlatEquiv (m + 1) q x) = x.1 i` by `wilkieCase2ProductFlatEquiv_visible`.

## The necessary exceptional-set transport

The maintained membership theorem is typed for a map from `RealEuclidean n`; the recursive draft uses a product source. Thus `hH` and `hg` do **not** directly type-check as inputs proving membership of `exceptionalParameterSet F (fun x => x.1 i) a`. A continuous-linear-equivalence transport lemma is required; a source-only candidate proof is staged in `Scratch/Case2ExceptionalProductFlatTransportDraft.lean`:

```lean
theorem exceptionalParameterSet_comp_linearEquiv
    {E D K : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (L : E ≃L[ℝ] D) (H : D → K) (g : D → ℝ) (a : K)
    (hHdiff : ∀ z, DifferentiableAt ℝ H z)
    (hgdiff : ∀ z, DifferentiableAt ℝ g z) :
    Wilkie28MathlibOnly.exceptionalParameterSet (H ∘ L) (g ∘ L) a =
      Wilkie28MathlibOnly.exceptionalParameterSet H g a
```

For `z = L x`, the two chain rules identify the product augmented derivative with the flat augmented derivative precomposed by `L`. Since `L` is surjective, the derivatives are surjective simultaneously. The fiber and pivot equations agree by definition; witnesses transfer by `L` and `L.symm`. Smoothness follows from the flat tuple membership and the polynomial pivot. Specializing to `L := wilkieCase2ProductFlatEquiv (m + 1) q`, `H := wilkieCase2Flatten F`, and `g z := z (Fin.castAdd q i)` yields the equality of product and flat exceptional scalar sets. A small `funext` bridge gives `F = H ∘ L` and `x.1 i = g (L x)`.

After rewriting by this equality, `wilkie28_exceptionalParameterSet_mem_literalZeroCharbonnel` supplies the product-shaped unary membership for every reachable `F`, every target `a`, and every `i`. `wilkie28WeakSelectionIncidence_sourceData` also supplies a closed literal-zero incidence set and its exact projection for each such flat map; it asserts no selector.

## What this does and does not close

The algebraic route discharges the `hBmem` **membership** branch only after the recursive theorem is specialized to reachable Abel-family tuples and the two adapters above are formalized. It cannot discharge the present globally quantified `hBmem` in place. The separate `hselection` premise remains: `wilkie28_exceptionalCoordinateValues_finite_of_WS5_and_selection` needs `Wilkie28MathlibOnly.SmoothSingularWitnessSelection` for every encountered map. Neither affine family closure nor the literal-zero incidence theorem constructs that selector. WS5 itself for this `C` additionally uses the maintained `literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure`, whose hypothesis includes `HasUniformFiberFiniteness (abelGeometricFamily A)`.
