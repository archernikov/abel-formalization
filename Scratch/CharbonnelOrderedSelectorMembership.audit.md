# Ordered-selector family membership audit

Maintained module:
`AbelFormalization/CharbonnelOrderedSelectorMembership.lean`.
It is imported by `AbelFormalization.lean`.

The family-membership endpoints are:

- `charbonnelLowerRayCell_mem_charbonnelClosure_of_graph_mem`;
- `charbonnelUpperRayCell_mem_charbonnelClosure_of_graph_mem`;
- `charbonnelOpenBand_mem_charbonnelClosure_of_graph_mem`;
- `charbonnelCylinderCell_mem_charbonnelClosure`;
- `charbonnelOrderedSelectorRegionCarrier_mem_charbonnelClosure`;
- `charbonnelFiniteSelectorRelativeCellCover_membership`.

The last theorem returns exactly the `hzeroMem` and `hpositiveMem`
arguments of `charbonnelFiniteSelectorRelativeCellCover`.  The convenience
definitions
`charbonnelFiniteSelectorRelativeCellCover_of_graph_mem` and
`CharbonnelFiniteCompatibleCellCover.finiteSelectorCylinderCover_of_graph_mem`
apply those facts to the local and flattened ordered-selector constructions.

For a lower or upper ray, the proof adjoins one hidden scalar `t`, pulls the
restricted selector graph back along `(x,y,t) ↦ (x,t)`, intersects it with
the polynomial-sign constraint `y < t` or `t < y`, and applies
`charbonnelClosure_projection`.  An open band is the WS1 intersection of an
upper and a lower ray.  A zero-selector cylinder is the WS3 product of its
base with the WS2 unary universal set.  No complement closure is used.

The maintained endpoint assumes
`PositiveArityWeakSetStructure (charbonnelClosure S)`, base membership, and
membership of every restricted selector graph.  Its residual inputs are the
geometric and analytic data already explicit in
`CharbonnelOrderedSelectorCells`: base cell shape, selector continuity,
strict ordering, and the exact-fibre description.  It does not duplicate
continuity, fibre-cardinality, or selector-construction work.

Verification:

```text
sh ../../work/run-lake.sh env lean \
  AbelFormalization/CharbonnelOrderedSelectorMembership.lean
```

exited successfully.  Building the named module also succeeded.  The full
umbrella build reached an unrelated failure in
`CharbonnelSection53ParentCollision.lean`; it reported no failure in this
module or its umbrella import.
