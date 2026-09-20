# Corollary 2.9 Case 2 full assembly audit

Source: Wilkie, printed pp. 404–405, PDF pages 8–9 of `/Users/artemchernikov/Downloads/s000290050052 (1).pdf`. The source fiber is `wilkieFiberOver F a U = F⁻¹ {a} ∩ realEuclideanTakeLeft ⁻¹' U`, with `U` a ball in the **visible** coordinates. Boundedness of this fiber is a standing hypothesis. A visible ball alone cannot bound the hidden coordinates. The maintained ambient-full-ball slice lemmas have a different fiber shape. `Scratch/WilkieCase2FullAssemblyDraft.lean` stages the visible-cylinder regularity and attained 2.8/WS5 choice bridge.

## Exact inductive invariant

For each arity `m`, flat map `F : RealEuclidean (m + q) → RealEuclidean q`, target `a`, and visible domain `U : Set (RealEuclidean m)`, under global `C¹`, regularity, boundedness of `wilkieFiberOver F a U`, nonemptiness, and openness of `U`, prove

```lean
(∃ cols : Fin q ↪ Fin (m + q), ∃ η : ℝ,
  0 < η ∧ Set.Icc (0 : ℝ) η ⊆
    (fun y ↦ (standardJacobianColumnMinor F cols y) ^ 2) ''
      wilkieFiberOver F a U) ∨
(∃ x ∈ wilkieFiberOver F a U,
  standardJacobianColumnMinor F (Fin.natAddEmb m) x ≠ 0)
```

At `m = 0`, `wilkieZeroVisible_verticalMinor_ne_zero_of_regular` gives the right certificate. At `m + 1`, a finite visible image gives the left certificate through `wilkieFiniteVisibleImage_sameMinor_squared_interval`; an infinite visible image gives an attained good coordinate through Theorem 2.8 and the staged cylinder bridge. The lower-arity left certificate is lifted as an interval; the lower-arity right certificate is lifted pointwise for the fixed hidden-column minor. Finally, for the original ball `U`, the maintained vertical projection fork turns a right certificate into `π[X] = U` or an interval for the **same** hidden-column minor. This invariant is necessary: full projection of a single coordinate slice does not imply full projection of the unsliced fiber.

## Typed bridge signatures still needed

Here `E_m := wilkieCase2ProductFlatEquiv m q`, `I_i,b := wilkieCase2FlatCastInsert i b`, and `U' := (Fin.insertNth i b) ⁻¹' U`. The arity-cast derivative identities are not present in maintained files.

1. **Visible-cylinder flat equivalence.** The product slice bridge must connect to the flat `wilkieFiberOver` used by Case 1 and the vertical fork:

```lean
theorem wilkieCase2_productFlat_cylinder_eq
    {m q : ℕ}
    (F : ((Fin m → ℝ) × (Fin q → ℝ)) → RealEuclidean q)
    (a : RealEuclidean q) (U : Set (RealEuclidean m)) :
    (wilkieCase2ProductFlatEquiv m q) ''
        wilkieCase2VisibleCylinderFiber F a U =
      wilkieFiberOver
        (F ∘ (wilkieCase2ProductFlatEquiv m q).symm) a U
```

The equality uses `wilkieCase2ProductFlatEquiv_visible` and the bijection; it should also yield equivalence of boundedness, nonemptiness, and finite visible images.

2. **Slice-domain convexity.** Openness is in the staged cylinder theorem. Preconnectedness does **not** pass to the preimage of an arbitrary preconnected `U` under coordinate insertion, so preserve convexity of the source ball instead:

```lean
theorem wilkieCase2_visible_domain_convex_of_convex
    {m : ℕ} {U : Set (RealEuclidean (m + 1))}
    (hU : Convex ℝ U) (i : Fin (m + 1)) (b : ℝ) :
    Convex ℝ ((Fin.insertNth i b) ⁻¹' U)
```

This makes each sliced `U'` preconnected for the final vertical fork and retains the paper's ball geometry without requiring an explicit radius formula.

3. **Inserted flat fiber inclusion and Jacobian.** For `F : RealEuclidean ((m + 1) + q) → RealEuclidean q` and `G := F ∘ I_i,b`, show

```lean
I_i,b '' wilkieFiberOver G a U' ⊆ wilkieFiberOver F a U
```

and, for `y` in the lower fiber,

```lean
standardRectangularJacobian G y =
  (standardRectangularJacobian F (I_i,b y)).submatrix id
    (fun j : Fin (m + q) ↦
      ((wilkieCase2FlatFixedIndex (q := q) i).succAbove j).cast
        (wilkieCase2_add_succ_cast m q))
```

The latter is the `wilkieCase2_flatJacobian_coordinateInsert` identity after the `(m + q) + 1 = (m + 1) + q` cast. It discharges `hJac` in `wilkieCase2_sliceMinor_squared_interval_transport`; the former discharges `himage`. An exact visible-cylinder analogue of `wilkieCase2_ballSliceMinor_squared_interval_lift` can then be stated with lower `wilkieFiberOver G a U'` and upper `wilkieFiberOver F a U`, using the deterministic selected-column injection induced by `I_i,b`.

4. **Pointwise hidden-column lift.** The right certificate requires a different result from interval transport:

```lean
theorem wilkieCase2_flatVerticalMinor_sq_insert
    {m q : ℕ}
    (F : RealEuclidean ((m + 1) + q) → RealEuclidean q)
    (i : Fin (m + 1)) (b : ℝ) (y : RealEuclidean (m + q))
    (hFdiff : DifferentiableAt ℝ F
      (wilkieCase2FlatCastInsert i b y)) :
    (standardJacobianColumnMinor
      (F ∘ wilkieCase2FlatCastInsert i b)
      (Fin.natAddEmb m) y) ^ 2 =
    (standardJacobianColumnMinor F (Fin.natAddEmb (m + 1))
      (wilkieCase2FlatCastInsert i b y)) ^ 2
```

The maintained `wilkieCase2FlatFixedIndex_free_hidden` is precisely the column-index identity needed here. The square equality is enough to transport nonzeroness, and the inserted-fiber inclusion transports the witness.

5. **C¹ and Theorem 2.8 data at every slice.** Global `C¹` for `G` follows from affine insertion and the cast. Theorem 2.8's finite exceptional values must be supplied for every recursively obtained `G`, not only the original `F`. The maintained `wilkie28_exceptionalCoordinateValues_finite_of_family_WS5_selection` can do this if geometric-family tuple membership and coordinate membership are preserved under each affine pullback. Its sole remaining paper-specific premise is `SmoothSingularWitnessSelection` for each stage; the family membership bridge is algebraic but must be threaded through the induction. Alternatively, state the finite exceptional-set conclusion as the precise Theorem 2.8 hypothesis for each eligible stage.

No source-shaped full Case 2 theorem follows yet from the listed maintained lemmas alone. The staged cylinder theorem solves the analytic/nonempty/bounded step; the interval and hidden-column cast identities are the decisive remaining fixed-minor bridges.
