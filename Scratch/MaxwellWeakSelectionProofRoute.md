# Maxwell/Wilkie 2.3: proof route for the maintained incidence family

**Status:** proof design only. No Maxwell weak-selection theorem is proved by the maintained files or by mathlib. The route below isolates a compact unary geometric lemma that would make a direct, mathlib-only proof possible. It must be established, not added as an axiom or inferred from WS5 alone.

## Source and exact target

Wilkie, *A theorem of the complement and some new o-minimal structures*, §1.1–1.6 and Theorem 2.3, printed pp. 399–401, 403, local PDF `/Users/artemchernikov/Downloads/s000290050052 (1).pdf`. Wilkie says Maxwell [10] supplies the proofs; Maxwell's article is [Steve Maxwell, *A general model completeness result for expansions of the real ordered field*, Ann. Pure Appl. Logic 95 (1998), 185–227](https://www.sciencedirect.com/science/article/pii/S0168007298000128). The public publisher page supplies metadata/abstract, not the proof text. The 1997 Bonn report [§3.4](https://theory.cs.uni-bonn.de/ftp/reports/cs-reports/1997/85173-CS.pdf) repeats the theorem statement, also without a proof. This note therefore does not attribute the proposed compact-band argument to Maxwell.

For a positive-arity family `C` closed under finite unions, projections and topological closures, the family-level theorem needed is:

```
weakSelection (hC : PositiveArityOMinimalWeakSetStructure C)
  {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
  {A : Set (RealEuclidean p)} {B : Set (RealEuclidean (p + q))}
  (hA : A ∈ C p) (hB : B ∈ C (p + q))
  (hAint : (interior A).Nonempty)
  (hfiber : ∀ x ∈ A, ∃ y, realEuclideanAppend x y ∈ B) :
  ∃ (U : Set (RealEuclidean p)) (φ : RealEuclidean p → RealEuclidean q),
    IsOpen U ∧ U.Nonempty ∧ U ⊆ A ∧ U ∈ C p ∧
    {w | ∃ x ∈ U, w = realEuclideanAppend x (φ x)} ∈ C (p + q) ∧
    ∀ x ∈ U, realEuclideanAppend x (φ x) ∈ B
```

This is the **intended nonvacuous** Wilkie 2.3 with `C` already closed under the three Charbonnel operations. The printed sentence says “there exists an open set `U`” without explicitly writing `U ≠ ∅`; its use in 2.5 and 2.8 needs the nonempty reading, and the Lean target must state it. If phrased for an arbitrary o-minimal weak base `S`, the conclusion lies in `charbonnelClosure S`; one needs an idempotence lemma `charbonnelClosure C = C` before applying it to this maintained `C`. That lemma is a description induction from `charbonnelClosure_union`, `charbonnelClosure_projection`, `charbonnelClosure_topologicalClosure`, and intersection/semialgebraic membership. It is a separate adapter, not complement closure.

Set `C := charbonnelClosure (literalZeroSetFamily G)`. `literalZeroSet_charbonnelClosure_positiveArityOMinimalWeakSetStructure` in `CharbonnelComplementPipeline.lean` gives WS1–WS6 from `hG`, `hsmooth`, `hUFF`. `wilkie28WeakSelectionIncidence_sourceData` in `Wilkie28WeakSelectionIncidence.lean` gives a particularly strong `B`: the singular-witness incidence is a **closed literal zero set** in `C (1+n)`, and `A := wilkie28FlatExceptionalSlice F f a` is its exact first-coordinate projection and belongs to `C 1`. `wilkie28FlatExceptionalSlice_eq_exceptionalParameterSet` identifies the scalar target. These maintained statements satisfy the family and full-fiber inputs to 2.3, but produce no selector.

The direct specialized target is `Nonempty (Wilkie28WeakSelectedWitness C F f a)` from `Wilkie28SelectionComposition.lean` under nonempty interior of the exceptional scalar set. A general 2.3 result gives `U`, `φ`, and `graph_mem`; `wilkie28ExceptionalResidual_append_eq_zero_iff` plus the maximal-minor/rank bridge gives its `F_eq`, `f_eq`, and `singular` fields. Convert `RealEuclidean 1` to `ℝ`, identify the restricted graph, and extend `φ` outside `U` only for the total-function field. The source's positive `p,q` conditions hold in the intended application.

## Concrete compact reduction, already supported by the API

For this incidence, write `K_m := B ∩ Metric.closedBall 0 (m : ℝ)`. It is compact because `B` is closed and Euclidean closed balls are compact. `literalZeroSet_charbonnelClosure_compactTruncationMembership` in `CharbonnelSection5ElementaryInputs.lean` gives `K_m ∈ C (1+n)`; alternatively WS2 plus WS1 does. Its visible projection `P_m` belongs to `C 1` by `charbonnelClosure_projection`, and is compact/closed by `maxwellClosedLiftProjectionTruncation_isCompact`'s underlying compact-image argument. The projections exhaust `A`, since every incidence witness has finite norm.

Choose a nonempty open interval `W ⊆ interior A`. The closed sets `P_m ∩ W` cover `W`. Mathlib's `IsOpen.baireSpace` and `nonempty_interior_of_iUnion_of_closed` (or `dense_iUnion_interior_of_closed`) yield some `m` and a nonempty open interval `W' ⊆ W ∩ P_m`. Shrink to a real-parameter interval with endpoints in `ℝ`; WS2 makes `W'` a member of `C 1`. Thus 2.3 reduces to a compact member whose every fiber over `W'` is nonempty. This step needs Baire category and closedness, not the still-unproved complement theorem, cell decomposition, or o-minimality of the generated structure.

## Sufficient geometric core and induction on witness arity

The most useful new lemma to seek is a **compact unary local selector**. For every `p>0`, every compact `K ∈ C (p+1)`, and every nonempty open ball `W ⊆ projection K`, it should produce a smaller nonempty open ball `U ⊆ W`, `U ∈ C p`, and a continuous `s : U → ℝ` whose restricted graph is in `C (p+1)` and contained in `K`. Continuity is needed for the simple witness-coordinate induction below. This is stronger than the bare unary case of 2.3; it has no maintained proof.

A promising **sufficient, unproved** geometric formulation is a local band-or-constant lemma: on some ball `U ⊆ W`, either one fixed `c : ℝ` lies in every fiber, or one fixed open interval `I` meets each fiber in exactly one point. In the first case the constant graph is semialgebraic and lies in `C` by WS2. In the second, the graph is exactly `K ∩ (U × I)` and lies in `C` by WS2, WS3/WS4, and WS1. Closedness of `K` and compact bounded fibers make the unique section continuous locally. **Do not assume this dichotomy follows just from finite vertical-fiber components:** a closed relation can have densely changing fibers. Its proof would have to exploit the *uniform affine-section* WS5 bound and likely the WS6/Charbonnel closure-regularity machinery. `MaxwellCompactComponentSeparation.lean` concerns closure-node component bounds, not this selector; it does not prove band isolation.

If that unary lemma is proved, select `q` coordinates inductively. Given a continuous prefix `φ_r : U → ℝ^r` with graph in `C` and with each prefix extendable to a point of compact `K`, form the residual relation

```
R_r := {(x,y) : x ∈ U ∧ (x, φ_r x, y) ∈ K},
```

where `y ∈ ℝ^(q-r)`. Its membership in `C` follows by a fiber product: combine the prefix graph and `K`, impose equality of the duplicated visible/prefix coordinates using semialgebraic diagonal sets, permute coordinate blocks, then project. No universal quantifier or complement is needed. Because `φ_r` is continuous and `K` compact, `R_r` is relatively closed over `U`; on a bounded smaller ball its ambient closure is compact and agrees with `R_r` above that ball. Project to the next witness coordinate, apply the unary compact lemma on a smaller ball, and combine the graphs by another fiber product/projection. Keep the selected prefix graph inside `K` and preserve continuity. The exact closure-over-open-ball equality and the finite-coordinate graph membership lemmas are new adapters; unlike band isolation they are routine topology and family algebra.

There is a real caveat here: a selector from *bare* 2.3 need not be continuous, so its residual relation need not be relatively closed. The induction cannot silently use compactness after taking a fiber product with an arbitrary weak-family graph. A direct general-arity Maxwell proof could avoid this induction; the route above requires the stronger continuous unary lemma.

## What WS1–WS6 do and do not discharge

Wilkie's §§1.4–1.6 and 2.3 say that o-minimal weak structure axioms are **mathematically sufficient** for 2.3 after Charbonnel closure. They do not make the selector a one-line consequence of the maintained Lean structure fields. The repo proves WS5 for this `C` and WS6 closed lifts, and its closure/projection/intersection algebra supplies the compact reduction. It has **not** proved the compact unary band-or-constant lemma, an equivalent family-member graph extraction theorem, or the source's 2.3 theorem. `CharbonnelClosureInteriorRegularity.lean` explicitly leaves `MaxwellInteriorGapComponentSelection` open, so a route using Wilkie 2.1/closure-empty-interior must first prove that independent gap; it cannot cite 2.1 as maintained. The resulting selection graph is needed again for Wilkie 2.4. `Wilkie28SelectionComposition.lean` only combines selection and almost-everywhere smoothness *as hypotheses* into the differential contradiction.

The most efficient next proof-design experiment is the compact unary local graph-extraction lemma above, formulated for `p=1` first and tested against compact weak-family examples with moving interval fibers and branching graphs. If band isolation fails, retain the compact unary selector statement as the exact core and seek Maxwell's original proof text. Michael/topological/measurable selection from mathlib cannot substitute: those theorems produce a section under different correspondence hypotheses and give no `graph ∈ C` conclusion.
