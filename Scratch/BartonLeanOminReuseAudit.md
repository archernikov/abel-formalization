# Reid Barton's Lean 3 o-minimality repository: residual-focused reuse audit

## Scope and standard for reuse

This audit examines the checkout at `/tmp/lean-omin.Yh5k0w`, commit
`fd733c6d95ef6f4743aae97de5e15df79877c00e` (2020-12-07).  Its
`leanpkg.toml` pins Lean 3.23.0 and mathlib commit
`81207e091bf54fd5dda2237292a81013d1acc65f`.  The repository README calls
`src/o_minimal` the official development and `omin` a playground which may
contain unfinished proofs.  A source scan finds no active `sorry`, `admit`, or
added axiom in the official tree.  The playground does contain active `sorry`s,
notably in `omin/cells.lean`, `omin/topology.lean`, and the alternate
higher-dimensional choice construction in `omin/def_choice/choice5.lean`.

The older project-level audit in `BARTON_REUSE_AUDIT.md` correctly concludes
that no wholesale port is useful.  This note asks the narrower question:
does Barton contain a theorem or proof pattern that can close one of the
*current* Wilkie-complement residuals before complement closure, projection
closure of the eventual definable family, or o-minimality has been established?

There is one important distinction in the present project.  A
`CharbonnelDescription` has projection as a syntax constructor, so
`charbonnelClosure_projection` is available internally without assuming that
the original literal-zero family is projection closed.  That internal
constructor is legitimate.  A Barton result does not count as pre-complement
reuse when it assumes a `struc`, `o_minimal`, or `o_minimal_add`, because those
classes already contain the closure or unary-tameness conclusions being
proved here.

## Conclusion

No theorem in the checkout closes a current residual.  The one genuinely
pre-o-minimal projection algorithm, `triangular_projection`, applies only to
an *isolating* function family.  Isolation says that every primitive
constraint can already be written globally as one graph, one lower or upper
ray, or a constraint in fewer variables.  This is unavailable for the Abel
analytic family and would bypass the finite-branch refinement that Wilkie's
Section 4 is intended to prove.

Several proof patterns are sound and useful as cross-checks:

1. induction over finite-union and finite-intersection syntax;
2. graph-incidence proofs of composition, preimage, and coordinate reindexing;
3. projection of a finite system of scalar lower and upper bounds by pairwise
   comparison;
4. coordinate-by-coordinate promotion of scalar choice to vector choice; and
5. gluing membership or graph definability over a supplied finite cover.

All five already have stronger, Lean 4, mathlib-only counterparts in this
project.  None constructs the missing lower-dimensional refinement, proves
the Section 5 analytic steps, proves Maxwell's family-geometric closure
regularity, supplies the Section 5.3(c) stationary-component argument, or
proves Lion's uniform fiber bound.

## Assumption audit

### The core `struc` API is post-complement and post-projection

`src/o_minimal/structure.lean:25-42` defines `struc`.  Its fields include:

* `struc.definable_compl` at lines 33-34;
* `struc.definable_proj1` at lines 41-42;
* union, products, and an equality locus.

Consequently, most of the official API cannot be used to prove the theorem of
the complement.  In particular:

* `struc.definable_univ` (`structure.lean:58`) uses complement of the empty
  set;
* `struc.definable_inter` (`structure.lean:64`) derives intersection using
  three complements;
* `struc.definable_proj` (`structure.lean:150`) iterates the assumed
  one-coordinate projection; and
* `struc.definable_reindex_aux` / `struc.definable_reindex`
  (`structure.lean:164,193`) use equality loci, products, intersection, and
  projection.

The incidence idea in the reindexing proof is good, but its theorem statement
is too strong for pre-complement use.  The current project already implements
the adapted proof with the right assumptions:

* `PositiveArityWeakSetStructure.linear_preimage_mem` in
  `AbelFormalization/MaxwellExtendedSlopeClusterMembership.lean` uses WS1,
  WS2 polynomial signs, WS3, and `charbonnelClosure_projection`;
* `PositiveArityWeakSetStructure.toDescriptionReindexBase` and the description
  reindexing results in `AbelFormalization/CharbonnelDescriptionAlgebra.lean`
  handle coordinate bijections; and
* `literalZeroSet_charbonnelClosure_linearEquiv_image` in
  `AbelFormalization/CharbonnelLinearEquivClosure.lean` handles the full
  linear-equivalence clause for the literal-zero closure.

Porting Barton's reindexing lemmas would therefore duplicate a more general
existing incidence construction.

### The definable-set/function API uses those fields transitively

`src/o_minimal/definable.lean` defines `def_set` and graph-based `def_fun`.
The dependency boundary is explicit:

* `def_set.proj` and `def_set.exists` (`definable.lean:177,188`) use projection;
* `def_set.forall` (`definable.lean:195`) is complement-exists-complement;
* `def_fun.comp` (`definable.lean:278`) introduces an existential witness;
* `def_fun.preimage` (`definable.lean:328`) projects a graph incidence; and
* `def_fun.image` / `def_fun.range` (`definable.lean:425,432`) use existential
  projection.

These are useful formulas, not pre-complement theorems.  Their role is already
covered by `ProjectedZeroDefinabilityBridge`,
`ProjectedZeroFirstOrderBridge`, and the many explicit incidence modules in
the current development.  Barton's `def_set.forall` is especially unsuitable
for proving canonical selectors before complement closure: it is exactly
where complement enters.

## Concrete candidate patterns

### 1. Finite closure induction and final Boolean assembly

The generic file `src/for_mathlib/closure.lean` contains:

* `finite_union_closure` and `finite_inter_closure`;
* `preserves_finite_unions.bind'` and `preserves_finite_inters.bind'`;
* `closed_under_finite_inters_finite_union_closure`; and
* `closed_under_complements_finite_union_closure`.

`finite_union_struc_hypotheses.promote_hypothesis` in
`src/o_minimal/examples/from_finite_unions.lean:76` promotes an operation that
preserves empty sets and binary unions from basic sets to their finite-union
closure.  `struc_of_finite_union` (`from_finite_unions.lean:94`) then assembles
a `struc`, but its hypotheses explicitly include complements and projections
of basic sets (`definable_compl_basic` and `definable_proj1_basic`, lines
45-54).

The current equivalents are already present:

* `finite_iUnion_mem` and
  `CharbonnelFiniteCompatibleCellCover.complement_mem` in
  `AbelFormalization/CharbonnelClosedBoundaryCellAssembly.lean`;
* `charbonnelClosure_union` in
  `AbelFormalization/CharbonnelClosureDescription.lean`; and
* `UnaryPieceDecomposable.union`, `.inter`, and `.compl` in
  `AbelFormalization/UnaryPieceDecomposition.lean`.

Porting feasibility is easy, but there is no gain.  These induction principles
assemble a result once complements of generators or a finite compatible cover
are known.  They do not produce the compatible cover or prove a complement of
a recursive Charbonnel description.

### 2. Complementing primitive order constraints

The private `key` proof in
`src/o_minimal/examples/from_function_family.lean:179-211` complements a
primitive equality with the two strict inequalities and complements a strict
inequality with equality plus the reverse strict inequality.  The public
wrapper is
`function_family_struc_hypotheses.finite_inter_struc_hypotheses`
(`from_function_family.lean:216`).  Its input
`function_family_struc_hypotheses` still assumes
`definable_proj1_basic` (`from_function_family.lean:160-168`).

The same trichotomy/De Morgan argument is already proved for the richer local
syntax by `PolynomialSignConstructible.compl` in
`AbelFormalization/ProjectedZeroPolynomialSigns.lean`.  This closes
complements of polynomial sign conditions only.  It cannot complement a
projection or topological-closure node, which is precisely why Wilkie's
theorem remains necessary.

`src/o_minimal/examples/from_finite_inters.lean` has the analogous pattern:
`finite_inter_struc_hypotheses` assumes complements of primitives and
projections of basics, and
`finite_inter_struc_hypotheses.finite_union_struc_hypotheses` merely promotes
those assumptions.  It supplies no projection theorem for the analytic
basics.

### 3. The isolating-family triangular projection

This is the closest Barton result to Wilkie's cell argument, and the only
substantial projection result which does not assume a `struc` or
`o_minimal`.

The relevant source is `src/o_minimal/examples/isolating.lean`:

* `function_family.is_isolating` (line 81) requires every equality or strict
  inequality in `n+1` variables to be globally equivalent to one of `tt`,
  `ff`, one graph, one lower or upper ray, or a constraint in the first `n`
  variables;
* `last_variable_constraints` (line 99) stores either one graph or finite
  lower/upper families;
* `triangular_constraints` (line 130) recursively stores these constraints;
* `triangular_constraints_of_constraint` (line 284) triangularizes one
  primitive constraint;
* `triangular_constraints.closed_under_finite_intersections` (line 321)
  merges triangular systems;
* `triangular_constraints_iff` (line 421) identifies triangular systems with
  finite intersections of primitives; and
* `triangular_projection` (line 453) eliminates the final coordinate.

The band case of `triangular_projection` uses
`order_constraints_feasible_iff` from `src/o_minimal/dunlo.lean:30`: a finite
system `g_i < y < h_j` is feasible in a dense unbounded linear order exactly
when every `g_i < h_j`.  This is a clean, complement-free elimination pattern.
`function_family_struc_hypotheses_of_isolating` (`isolating.lean:501`) uses it
to discharge `definable_proj1_basic`, and `o_minimal_of_isolating`
(`isolating.lean:534`) supplies the final unary argument.

Porting `order_constraints_feasible_iff` alone would be easy.  Porting the
full triangular syntax would be moderate work because Lean 3 `finvec` and the
old finite-intersection APIs must be replaced.  Neither port closes a current
gap:

* the Abel function family has no `is_isolating` proof;
* an analytic equation can have several moving roots, collisions, and
  singular fibers, while an isolated equality permits only one global graph;
* the proof neither constructs a lower-dimensional partition on which the
  number of roots is constant nor proves the graph functions continuous; and
* assuming isolation for the relevant analytic constraints would assume the
  central local branch decomposition rather than derive it.

The current project implements the correct multi-branch replacement:

* `CharbonnelOrderedSelectorRegion` and
  `charbonnelOrderedSelectorRelativeCellCover` in
  `AbelFormalization/CharbonnelOrderedSelectorCells.lean` give graph, ray, and
  consecutive-band cells;
* `charbonnelOrderedSelectorRegionCarrier_mem_charbonnelClosure` and
  `charbonnelFiniteSelectorRelativeCellCover_of_graph_mem` in
  `AbelFormalization/CharbonnelOrderedSelectorMembership.lean` prove their
  family membership without complement closure;
* `continuousOn_maxwellOrderedScalarFiberEnumeration` in
  `AbelFormalization/CharbonnelOrderedSelectorContinuity.lean` derives
  continuity from exact cardinality, no escape, and no collision; and
* `charbonnelRestrictedGraph_maxwellOrderedScalarFiberEnumeration_mem_charbonnelClosure`
  plus
  `CharbonnelFiniteCompatibleCellCover.finiteFiberRelationCylinderCover_of_relation_mem`
  in `AbelFormalization/CharbonnelOrderedSelectorGraph.lean` remove the
  canonical graph-membership premise.

Thus Barton's triangular proof confirms the architecture—reduce the last
coordinate to finitely ordered boundary functions and push pairwise comparisons
to the base—but the current code already contains the part that can be proved
under WS1--WS4.  What remains is the simultaneous base refinement producing
constant finite cardinality, no escape, and no collision.

### 4. The semilinear specialization

`src/o_minimal/examples/semilinear.lean` contains
`semilinear_function_family_eq_constraint` (line 124),
`semilinear_function_family_lt_constraint` (line 148),
`semilinear_function_family_is_isolating` (line 188), and
`semilinear_o_minimal` (line 209).  The first two split on whether the
coefficient of the last coordinate is zero and otherwise solve the linear
constraint.

This is concrete quantifier elimination for linear inequalities, but it has no
analytic analogue.  Polynomial-sign sets are already supplied by WS2, and
the current incidence machinery handles arbitrary linear maps.  The
semilinear proof gives neither an analytic root stratification nor a result
about closures of projected zero sets.

### 5. Finite-cover gluing

`src/o_minimal/Def.lean` defines `Def.cover` (line 87), a finite jointly
surjective family of definable maps.  `Def.set_subcanonical` (line 93) and
`Def.subcanonical` (line 109) prove that local definability on every cover
member glues globally.  `Def.cover.pullback` (line 130) pulls a cover back.
The parallel sheaf API appears as `cover.pullback`, `definable_cover_of_Def`,
and `definable_cover` in `src/o_minimal/sheaf/covers.lean`.

The proof pattern is a finite union of images.  Therefore the Barton theorem
uses `def_fun.image`, which uses existential projection.  Moreover, it assumes
the cover and every local certificate; it does not construct or refine a
cover.  `sep_cover` in `sheaf/covers.lean:99` additionally uses the complement
of the separating set.

The corresponding finite bookkeeping is already stronger and more directly
suited to the residual:

* `CharbonnelFiniteCompatibleCellCover.flattenRelativeCylinders` in
  `AbelFormalization/CharbonnelOrderedSelectorCells.lean` flattens dependent
  finite covers over a finite base cover;
* `CharbonnelFiniteCompatibleCellCover.complement_mem` performs the final
  finite-union gluing; and
* `CharbonnelFiniteSelectorCylinderData.compatibleCover_of_boundaryIntersection`
  in `AbelFormalization/CharbonnelBoundarySelectorAssembly.lean` transfers the
  assembled cover from the boundary intersection to the closed target.

Barton's gluing lemmas cannot supply the missing base cover, its fiber strata,
or the local no-escape/no-collision data.

### 6. Unary tameness and the first monotonicity lemma

`src/o_minimal/tame/basic.lean` defines `interval_or_point` and `tame`, then
proves `tame.induction`, `tame_compl_interval_or_pt`, Boolean closure, and
`tame.finite_or_contains_interval` (line 223).  These are independent of a
particular structure once a tame decomposition has been supplied.

The current `UnaryPieceDecomposable` API is an exact Lean 4 counterpart and is
already used by `CharbonnelSection5ElementaryInputs` for the unary WS5 base.
There is no missing unary-tameness lemma to port.

`mono1` in `src/o_minimal/mono1.lean:17` is not pre-complement.  It assumes
`[o_minimal S]`.  Its proof first obtains finite fibers from unary tameness,
then defines the set of least representatives

`K = {x' | forall x'', f x' = f x'' -> x' <= x''}`

and proves `K` definable with `def_set.forall`.  That universal quantifier is
implemented using complement and projection.  It then applies unary tameness
again to find an interval.  The theorem gives an injective-or-constant
subinterval, not continuity or differentiability.

The finite ordered-tuple incidence in
`CharbonnelOrderedSelectorGraph.lean` is already the complement-free analogue
of the least-representative idea: it exposes a canonical entry existentially,
without defining a universal-minimum predicate.  Using `mono1` for Maxwell
selection or Wilkie cells would be circular.

### 7. Definable choice

The choice development is under the unofficial `omin/def_choice` tree.  Its
most relevant declarations are:

* `chosen_one` in `choice3.lean:215`, defined by a least element or by
  infimum/supremum and interval cases;
* `chosen_one_mem` in `choice4.lean:41`;
* `definable_choice_1` in `choice5.lean:21`;
* `definable_choice_n` in `choice.lean:56`; and
* the general right-inverse theorem `definable_choice` in
  `choice.lean:108`.

The scalar proof and the coordinate recursion themselves are explicit.  The
same file `choice5.lean` has later active `sorry`s in the alternate theorem
`definable_chosen_n'`, so the playground as a whole is not an acceptable
dependency.  More decisively, every relevant file assumes `[OQM R]` and
`[o_minimal_add S]`; `o_minimal_add` in `omin/oqm.lean:14` extends full
`o_minimal S`.  The scalar proof invokes `tame_of_def`, and the definability of
least/infimum/supremum predicates uses universal quantification.

It also produces a definable selector, with no continuity statement.  Hence it
cannot establish the pre-complement continuous selectors needed in Section 4.
The only reusable architecture is the recursion in `definable_choice_n`:
project to a prefix, choose the prefix, restrict the last-coordinate relation,
choose one scalar, and join the graphs.  This is already implemented by
`maxwellScalarResidualRelation`, `maxwellJoinFunctionGraphs`, and
`maxwellWeakSelection_succOutput_of_localConstantFiberCardinality` in
`AbelFormalization/MaxwellWeakSelection.lean`.

### 8. Cells and topology in the playground

`omin/cells.lean` defines `struc.cell` (line 12) with cylinder, graph, rays,
and open-band shapes, and `struc.decomposition` (line 43).  It has active
`sorry`s in `init_definable` and `cell.definable`; it proves no theorem that a
decomposition exists.  Its graph functions are merely `def_fun S`; the cell
constructors do not require continuity.  It also begins from a full `struc`,
so complement and projection are already fields.

The compiled `CharbonnelCellShape`, ordered-selector cover, membership,
continuity, graph-incidence, and boundary-compatibility modules in the current
project strictly subsume the usable content.

`omin/topology.lean` does not help with Maxwell's closure-regularity residual.
Its box characterization `mem_interior_iff` is an active `sorry`, and
`def_interior` uses `def_set.forall`, hence complement and projection.  It has
no Baire-category, meagre-fiber, closure-interior, or WS5 component-selection
argument.  The relevant current work is instead
`KuratowskiUlamProduct`, `CharbonnelClosureInteriorRegularity`, and
`MaxwellMeagreClosureFamilyEquivalence`.

## Residual-by-residual verdict

The current interfaces used in the comparison are
`CharbonnelBoundarySelectorRefinementProperty` and
`CharbonnelHigherDimensionalClosedLiftCellCoverProperty` for Section 4,
`CharbonnelSection53NoDescentSuccessorChoice` and
`CharbonnelSection53NoLimitComponentCollapse` around the Section 5.3(c)
branch, `CharbonnelSection5AnalyticStep` for the remaining analytic package,
`HasMaxwellMeagreClosureComponentSelection` /
`CharbonnelClosureInteriorRegularity` for Maxwell's Lemma 2.7 step, and
`HasUniformFiberFiniteness` for Lion's input.

| Current residual | Closest Barton material | Verdict |
| --- | --- | --- |
| Section 4 simultaneous lower-dimensional refinement for projected closed lifts | `triangular_projection`, `definable_choice_n`, and the unfinished `struc.cell` syntax | No closure.  Isolation is unavailable; choice assumes o-minimality; the cell file has no existence theorem.  Barton's code never constructs a finite base-cell cover with constant fiber cardinality, no escape, and no collision. |
| Section 5.3(c) minimum-defect/radius successor and stationary affine explosion | No component-support or nested-ball development | No overlap.  Nothing in the repository tracks component parents, defects, radius control, or turns stationary collisions into a WS5 contradiction. |
| Sections 5.4--5.7 analytic stabilization/approximation | No analytic, measure, Sardian, or rank-induction development | No overlap. |
| Maxwell Lemma 2.7 family-geometric closure/interior regularity | Unfinished `def_interior`; `mono1` after o-minimality | Circular or incomplete.  There is no meagre-fiber plus WS5 argument. |
| Lion uniform fiber finiteness | Unary `tame.finite_or_contains_interval` and `mono1` | No overlap.  These give no parameter-uniform bound on connected components of higher-dimensional regular fibers. |
| Final Boolean/projection/first-order assembly after the complement theorem | `struc_of_finite_union`, `o_minimal_of_function_family`, and the `def_set`/`def_fun` API | Conceptual checklist only.  The project already has `ProjectedZeroComplementEnvelope.oMinimal` and the first-order bridges, specialized to positive arities and the actual Abel language. |

The exact current Section 4 endpoint is particularly sharp.  Once a finite
compatible base cover is supplied, the theorem
`CharbonnelFiniteCompatibleCellCover.finiteFiberRelationCylinderCover_of_relation_mem`
needs only exact finite fiber cardinality, `MaxwellScalarFiberNoEscape`, and
`MaxwellScalarFiberNoCollision`; canonical graph membership, selector
continuity, ordering, rays, bands, cylinders, flattening, and final finite
union are now internal.  Barton contains no mechanism for producing those
three local facts simultaneously on a finite recursive base cover.

## Porting recommendation

Do not port any Barton module into `AbelFormalization`.

If a future proof explicitly needs feasibility of finitely many scalar lower
and upper bounds, `order_constraints_feasible_iff` is the only attractive
standalone lemma.  It should then be reproved directly against current
mathlib's finite-order API, rather than importing or transliterating the Lean
3 framework.  It does not currently discharge an open premise.

The useful architectural lessons are already reflected in the code:

* use existential graph incidences instead of universal least-element
  predicates before complement closure;
* isolate all finite-union assembly from the theorem which constructs the
  pieces;
* recurse over output coordinates only after a scalar selection theorem is
  available; and
* treat last-coordinate projection as a finite ordered-boundary problem only
  after the lower-dimensional refinement has established finitely many
  continuous branches.

No `AbelFormalization/*.lean`, umbrella, README, or dependency file was edited
as part of this audit.
