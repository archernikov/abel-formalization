# Section 5.3(c): stationary deletion and component replacement

This is a source-only audit. The new, unimported Lean module
`Scratch/CharbonnelSection53DeletedComponentReplacement.lean` has not been
compiled. It imports maintained
`CharbonnelSection53StationaryLimitSupport` and does not alter any maintained
file.

In the [printed proof, pp. 697–698, §5.3(c)](https://aif.centre-mersenne.org/item/10.5802/aif.1270.pdf),
the late vertical images lie inside disjoint open neighborhoods of the
limit-fiber components. The text then concludes that the limit count `M′`
equals the stationary ball count `M`. Localization and support give a
distinct *stage* component for each limit component, hence `M′ ≤ M`.
They do not show that every stage component meets the limit fiber. Several
stage components can disappear or be replaced within one open neighborhood.

The staged theorem
`charbonnelSection53_nextVerticalImage_subset_without_defectiveComponent`
proves exactly what one successor deletion does: for a defective component
`c` of the predecessor ball, `V_next ⊆ V_old \ carrier(c)`. Its stationary
specialization applies at every index of an actual chain. The proof is
direct from the definition of `β`: if `t` belonged to both `V_next` and
`carrier(c)`, its base witness would lie in the deleted support of `c`.
The finite-cardinality theorem
`charbonnelSection53_sameRank_forces_parentCollision` then states that,
once a parent-component map is constructed, equal component counts and
one missing old component force two new components to have the same old
parent. This is the concrete replacement mechanism that an affine-section
argument would have to control across infinitely many stages.

A single-stage example shows why full WS5 cannot simply be inserted into
the printed `M′=M` inference. Let `ω=[0,1]` and
`S=([0,1]×{0}) ∪ ({1/2}×[1,2])` in the plane. Both pieces are compact and
convex. Every affine section intersects each piece in a convex set, so the
section has at most two connected components: full WS5 holds with `N=2`.
The projection of `S` is all of `ω`. A positive relative ball containing
`1/2` has vertical image `{0} ∪ [1,2]`, global count `M=2`, and defect
`δ=1`: the upper component has base support `{1/2}` while the lower has
full ball support. Choose such a ball also containing `x=0`. Then `x`
avoids `β`, but the fiber at `x` is `{0}`, with `M′=1`.

This example is **not** a counterexample to
`CharbonnelSection53NoLimitComponentCollapse`, whose antecedent is an
actual stationary deletion chain. Every successor avoiding `β={1/2}`
has vertical count `1`, so it leaves the global `M=2` stratum immediately.
The example demonstrates only that compactness, full WS5, global rank,
minimal positive defect, and support/localization at one stage do not
imply `M′=M`.

For a genuine stationary chain, each deletion removes a defective old
component while the next ball still has count `M`. The proof therefore
needs a uniform way to rule out indefinitely repeated replacement by
splitting retained components. The maintained interface
`CharbonnelSection53StationaryForcesAffineExplosion` names one sufficient
route: show every finite affine-section component bound is exceeded.
Neither the printed local-count step nor the currently maintained
compact/deletion lemmas construct that affine section. No conclusion about
whether full WS5 alone excludes all such chains is asserted here.
