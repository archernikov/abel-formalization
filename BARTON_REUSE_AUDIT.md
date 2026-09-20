# Reid Barton's `lean-omin`: reuse audit

Source audited: [`rwbarton/lean-omin`](https://github.com/rwbarton/lean-omin),
master commit `fd733c6d95ef6f4743aae97de5e15df79877c00e` (2020-12-07).
The repository pins Lean 3.23.0 and mathlib commit
`81207e091bf54fd5dda2237292a81013d1acc65f`.  Its `src/o_minimal`
directory is the official, approximately 4,500-line development; a strict
source scan found no active `sorry`, `admit`, or added `axiom` there.  The
separate `omin` playground contains unfinished proofs and is not a sound
dependency candidate.

## What the development proves

The official tree provides:

* a coordinate-family definition of a first-order structure, with Boolean
  operations, products, equality loci, projection, and coordinate reindexing;
* a compositional API for definable sets, functions, values, finite
  quantifiers, and ordinary existential and universal quantifiers;
* the one-dimensional `tame` class of finite unions of points and intervals;
* constructors promoting finite-union, finite-intersection, and
  function-family presentations to an o-minimal structure;
* o-minimality of semilinear sets and the first unary
  injective-or-constant lemma used in the monotonicity argument.

The separate `omin` playground contains unfinished definable-choice files;
in particular `omin/def_choice/choice5.lean` has active `sorry` declarations.
Those files are not part of the sound `src/o_minimal` development and are
not reusable proof dependencies.

The most relevant result is
`o_minimal_of_function_family`.  Its hypotheses include
`definable_proj1_basic`: every one-coordinate projection of a basic set must
already belong to the proposed definable family.  It also requires unary
tameness of each primitive equality or strict-inequality locus.  Thus it is a
clean final assembly theorem; it does not prove the projection/complement
theorem needed for the Abel family.

## Mapping to this Lean 4 project

| Barton API | Existing Lean 4 replacement here | Decision |
| --- | --- | --- |
| `struc`, Boolean closure, products, equality and projections | `ProjectedZeroComplementEnvelope`, `PositiveArityWeakSetStructure`, and `CharbonnelDescription` | Keep the current APIs: they encode Wilkie's positive-arity hypotheses and rank data. |
| `def_set` / `def_fun` closure under formulas and quantifiers | mathlib `FirstOrder.Language`, `Set.Definable`, `ProjectedZeroDefinabilityBridge`, and `ProjectedZeroFirstOrderBridge` | Already replaced by a current mathlib-based formula induction. |
| finite-union/intersection promotion | `UnaryPieceDecomposition`, `SmoothFamilyOMinimalityCriterion`, and the Charbonnel algebra modules | Reuse the proof pattern as a cross-check; the needed Lean 4 statements are already proved. |
| `o_minimal_of_function_family` | `oMinimal_of_unarySetFamily`, `oMinimal_of_firstOrderExpansion`, and `ProjectedZeroComplementEnvelope.toOMinimal` | The local endpoint is more directly aligned with the paper. |
| semilinear o-minimality | mathlib's ordered-real and polynomial infrastructure plus the project's polynomial-sign bridge | No bearing on the new analytic generator. |
| unary tameness and `mono1`'s local injective-or-constant argument | the project's unary-piece and compact graph-branch reductions | Useful as a proof-architecture check, but it assumes full o-minimality and supplies neither continuity nor differentiability, so using it to prove Maxwell 2.3--2.4 would be circular. |

## Reuse decision

No wholesale port is useful.  The reusable material is the architecture of
the final closure argument, and the current project already contains Lean 4,
mathlib-only versions specialized to the exact Abel statement.  Barton's code
does not contain Wilkie's approximation/boundary induction, the theorem of the
complement, Lion's uniform-fiber theorem, or a proof that projected Abel zero
sets satisfy the projection hypothesis.

The audit therefore avoids a redundant Lean 3 port.  We will continue to use
the repository as an independent checklist for the final Boolean/projection
and first-order assembly.  Its sound tree contains no closed-bad-locus,
`ContDiff`, or arbitrary-order regularization theorem for a functional graph,
so it does not shorten the Maxwell 2.4 proof.  The remaining work stays
exactly:

1. uniform fiber finiteness for the Abel geometric family;
2. Wilkie--Karpinski--Macintyre complement closure from the formalized
   weak-structure and differentiability hypotheses;
3. instantiation of the already-proved first-order endpoint.
