# Wilkie 2.8, 2.9, and 3.10 checkpoint

This checkpoint records maintained Lean 4/mathlib proofs and the exact open
interfaces of a historical route. It supplements `README.md` and
`DEPENDENCIES.md`; the compiled final theorem is recorded there.

## Completed and imported

- `Wilkie28ExceptionalMathlibOnly`: the chain-rule contradiction on a
  differentiable singular-witness section of a regular fiber.
- `Wilkie28ExceptionalMembership`: the exceptional unary set is exactly a
  rank-one projection of the zero set of an augmented Jacobian
  sum-of-squares residual in a geometric derivative-closed family.
- `Wilkie28ExceptionalWS5Reduction` and
  `Wilkie28ExceptionalFamilyFinite`: unary WS5 decomposition makes the
  exceptional set finite from the explicit smooth witness-selection input.
- `Wilkie28SelectionComposition`: weak selected-graph membership together
  with a closed empty-interior nonsmooth set produces the needed nonempty
  open differentiable section.
- `Wilkie28WeakSelectionIncidence`: the singular parameter–witness
  incidence is a closed literal zero set in the closure family and projects
  exactly to the exceptional unary set.
- `Wilkie28WeakSelectionCompactBaireReduction`: nonempty interior of the
  exceptional set localizes to one compact singular-incidence truncation
  whose visible projection has nonempty interior and remains in the same
  Charbonnel closure.
- `Wilkie28WeakSelectionCompactExtraction`: a local family-member graph
  inside such a compact truncation gives the exact weak singular-witness
  structure, with derivative nonsurjectivity recovered from the residual's
  vanishing maximal minors.
- `MaxwellCompactComponentMembership` and
  `Wilkie28WeakSelectionCompactComponentReduction`: WS5 localizes the compact
  incidence to one connected component whose visible projection still has
  interior; the component remains a family member because it can be isolated
  by a finite union of semialgebraic balls. An explicit local family-member
  graph is constructed if the component projection is injective, if one fixed
  hidden section has interior, or if a polynomial-sign cut exposes an
  injective branch with projected interior.
- `MaxwellCompactInjectiveSelectorContinuity`,
  `MaxwellImplicitSelectorSmoothness`, and
  `Wilkie28WeakSelectionFiniteClosedCover`: projection from a compact
  single-valued relation is a homeomorphism onto its visible image, so every
  selected graph in it is continuous. A regular square implicit system then
  makes that selector differentiable by mathlib's implicit-function theorem.
  A finite closed polynomial-sign cover by such single-valued pieces
  automatically contains one piece with projected interior and supplies the
  local graph; regular implicit systems on all pieces simultaneously discharge
  the smoothness step on the selected branch.
- `WilkieFiniteVisibleProjectionCase`: unconditional Corollary 2.9 Case 1
  for a bounded regular fiber and finite visible image, using an arbitrary
  nonzero maximal Jacobian column minor.
- `WilkieCase2CombinatorialDescent`: an infinite visible image has an
  infinite coordinate image; it chooses an *attained fiber value* outside
  any finite coordinate exceptional set, and packages arity descent with
  explicit geometric slice and certificate-lift interfaces.
- `WilkieCase2SliceRegularity`: outside the exceptional set, every point
  of the attained slice has surjective augmented derivative. A concrete
  visible/hidden product-coordinate insertion proves the ball slice is
  nonempty, bounded, regular, and open in its inserted domain.
- `WilkieCase2MinorTransport`: a selected squared maximal minor survives
  row/column reordering and lifts its initial image interval from a slice
  to the original fiber under exact Jacobian and fiber-inclusion premises.
- `WilkieCase2FlatJacobianInsertion`: affine flat coordinate insertion
  carries standard source basis vectors to the corresponding free columns,
  making the sliced Jacobian the original Jacobian with one column omitted.
- `WilkieCase2FlatBallMinorIntervalLift`: for a literal fixed-coordinate
  ball slice, the selected squared-minor interval lifts to the original
  ball fiber; it proves the Jacobian and inclusion interfaces internally.
- `WilkieZeroVisibleVerticalMinor`: the zero-visible-arity terminal
  regularity condition makes the vertical maximal minor nonzero after
  reindexing `Fin (0 + k)` to `Fin k`.
- `WilkieCase2ProductFlatEquiv`: concatenation and an explicit arity cast
  commute with visible-coordinate insertion; transported balls and sliced
  derivative surjectivity agree under the continuous linear equivalence.
- `WilkieCase2VisibleCylinderChoice`: over a source-shaped visible cylinder,
  a good attained coordinate value yields a nonempty bounded regular lower
  slice over an open visible target. Under actual WS5 plus exceptional-set
  membership and the explicit smooth-selection input, an infinite visible
  image supplies such a value.
- `WilkieCase2CylinderMinorIntervalLift`: a selected squared-minor interval
  on the literal lower visible-cylinder fiber lifts to the original fiber,
  with the Nat arity cast, Jacobian submatrix, and fiber inclusion proved
  internally.
- `WilkieCase2HiddenMinorCast`: the fixed hidden-column minor agrees exactly
  under casted visible-coordinate insertion, so its pointwise nonzeroness
  lifts through the recursive slice.
- `WilkieCase2FlatCylinderSliceBridge`: the product and flat cylinder
  descriptions agree and inherit boundedness, nonemptiness, regularity, and
  insertion into the original restricted fiber.
- `WilkieCase2RecursiveFixedMinorAlternative` and
  `WilkieCase2ReachableRecursiveAlternative`: the full conditional Case 2
  two-certificate recursion and final projection fork compile, with source
  inputs restricted to affine descendants of one original map.
- `WilkieCase2ExceptionalProductFlatTransport`,
  `WilkieCase2FlatAffineFamilyClosure`, and
  `WilkieCase2ReachableExceptionalMembership`: exceptional sets transport
  through flat/product equivalence, affine slices preserve tuple membership,
  and the exceptional unary Charbonnel-membership premise is discharged for
  all reachable Abel-family stages.
- `WilkieCase2AbelConditional`: for an initial Abel-family tuple and uniform
  fiber finiteness, the entire Case 2 projection-or-selected-minor interval
  conclusion follows with smooth singular-witness selection as the sole
  recursive source premise.
- `WilkieCase2AbelMaxwellReduction`: the smooth-selection premise is expanded
  into the source's exact Maxwell 2.3 compact local graph extraction and 2.4
  almost-everywhere smoothness properties at reachable affine stages;
  product/flat selection transport is proved. A second compiled endpoint
  replaces general graph extraction by the concrete polynomial-sign
  injective-branch property on each large compact component. A third endpoint
  accepts any finite closed cover of every such component by polynomial-sign
  pieces on which visible projection is injective. The regular-implicit
  refinement supplies differentiable graphs directly and therefore proves
  the Case 2 conclusion without a separate 2.4 premise.
- `CharbonnelSardianProjectionRadialFiniteCover`: radial accumulation on a
  fixed fiber localizes to one member of a finite visible cover; if that
  member belongs to the Charbonnel closure, the earlier UFF/WS5 small-level
  result applies.

These maintained modules compiled individually and in the project umbrella.
Focused `#print axioms` checks for their central theorems returned only
`propext`, `Classical.choice`, and `Quot.sound`.  The current whole-library
audit has the same permitted-axiom result and includes the compiled theorem
`AbelFormalization.mainTheorem : MainTheorem`.

## Historical alternate-route obligations

The open interfaces recorded by this checkpoint have since been bypassed or
discharged in the compiled final route.  Maxwell weak selection and smoothness,
Lion uniform fiber finiteness, the Sardian projection constructor, and the
bounded deep Section 4 induction are all supplied internally.  The
compact/Baire graph-extraction and Section 5.3 stationary-chain developments
remain useful alternate partial routes; their open branches are not premises
of `AbelFormalization.mainTheorem`.

The working project uses Lean `4.34.0-rc2` and mathlib as its only Lake
dependency. Source-only drafts remain in `Scratch`; maintained modules above
are imported by `AbelFormalization.lean`.
