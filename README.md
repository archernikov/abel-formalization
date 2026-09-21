# A transexponential o-minimal structure

The real field expanded by the function $x\mapsto A(1+x^2)$, where $A$ is a
normalized analytic Abel function for $e^x-1$, is an o-minimal structure that
defines a function that grows faster than any finite iterate of the exponential
function.

**Author and responsible maintainer:** Artem Chernikov. **License:** Apache-2.0.
This project formalizes Artem Chernikov's private manuscript, which contains
his new original proof of the theorem obtained using GPT6 Astra. A paper with a
careful human presentation is in preparation. The manuscript is the source of
the theorem and proof architecture; the Lean development and its agent-led
audits are described in [formalization.yaml](formalization.yaml).

The repository contains a [Palomar submission package](PALOMAR.md), including
an independent [Challenge](Challenge.lean) and the corresponding
[Solution](Solution.lean). The repository is public. On 21 September 2026,
commit [`acf1a5a`](https://github.com/archernikov/abel-formalization/tree/acf1a5a138aa966e1380e4af3100e6c286d00fe6)
passed the [official full preflight](https://github.com/archernikov/abel-formalization/actions/runs/35649982169)
with source-based provenance and was submitted to Palomar as
**`3scl7d17niez`**. The
[registry verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/35653060781)
and subsequent review are pending. The result is not yet registered; this
receipt does not change the exact source commit under review.

The prepared theorem package has passed the full Lean build, the three audits,
and Comparator replay in both NanoDa and Lean's default kernel at the
[recorded private verification snapshot](PALOMAR.md#verified-private-snapshot).

**This project proves the paper's main theorem.** The theorem
`AbelFormalization.mainTheorem : MainTheorem` establishes the o-minimality,
definability, and transexponential conclusions from the stated Abel hypotheses,
without adding an axiom.

The project also proves `AbelFormalization.exists_isAbel : ∃ A, IsAbel A`.
This construction was developed for the Lean project in addition to the
manuscript's conditional proof and existence discussion. It supplies an
analytic positive invariant density and integrates and normalizes it to
satisfy exactly the four Abel hypotheses.
`exists_abel_ominimal_expansion` combines this witness with the main theorem.
See [the existence construction](ABEL_EXISTENCE_CONSTRUCTION.md) and
[the statement correspondence audit](MAIN_THEOREM_CORRESPONDENCE_AUDIT.md).

The source is *A transexponential o-minimal structure (maybe)*, version 29,
7 September 2026, a user-supplied manuscript named `omin.tex` (not included
in this repository). The proposed main theorem appears at lines 131–141
of that source.

## What is formalized

The development uses precisely the paper's assumptions on `A`:
analyticity on `(0,∞)`, positive derivative there, `A(1)=0`, and
`A(exp(x)-1)=A(x)+1` for positive `x`. Lean functions are total; no condition
is imposed on the irrelevant values of `A` outside `(0,∞)`.

The proved consequences include:

- Unconditional existence of an Abel function satisfying all four stated
  hypotheses, and hence existence of the claimed o-minimal expansion.
- Strict monotonicity, injectivity, and surjectivity from `(0,∞)` onto `ℝ`.
- Positive exponential iterates, Abel iteration identities, and divergence.
- Construction of the inverse, its continuity, positive derivative, and
  recurrence `T(s+1)=exp(T(s))-1`.
- The full transexponential growth clause, directly from the stated Abel
  hypotheses. This proof needs no o-minimality assumption.
- First-order definability of the full exponential and the positive-input
  inverse from `C₀(x)=A(1+x²)`.
- Analyticity of `C₀` at every real point and the signed-Stirling derivative
  transport identity for every positive order.
- The limits `x A′(x) → 0`, `x^(3/2) A′(x) → ∞`, and `A⁽ʳ⁾(x) → 0`
  for every `r ≥ 1`, together with `A = O(log)`.
- The eventual inverse derivative bounds `T < T′ ≤ T^(3/2)` and
  `(log log T)′(s) > T′(s−2) > T(s−2)`.
- For every fixed `M > 0`, compatible holomorphic extensions on all disks
  of radius `M` centered sufficiently far to the right, with the uniform
  bound `|A(z)| ≤ K_M log x` on the disk centered at `x`.
- The sequence separation theorem, including the finite-cluster assertions
  after any fixed number of logarithms and the singleton case.
- Decomposition into a fundamental interval and an iteration count tending
  to infinity.
- Contour Hermite interpolation, with an explicit analytic remainder,
  existence and uniqueness, and combined multiplicities at colliding nodes.
- Full multivariable analyticity of the integrated interpolation coefficients,
  uniform bounds for ordinary and factorial-normalized coefficients, and
  their exact rescaling under nonzero complex scalar substitution.
- The full manuscript Hermite lemma assembled directly from
  the Abel assumptions: a fixed bounded open node domain, compatible complex
  branches, coefficients bounded by `K0*(1+x)`, explicit interpolation jets,
  the central constant coefficient, and the central signed-Stirling identity
  with a uniformly bounded, jointly holomorphic remainder.
- The central function's joint analyticity and linear growth bound, its
  signed-Stirling jets and zero-scale coefficients, and the complex rescaling
  identity obtained from the real Abel equation.
- Analytic contour families with values in a Banach space and uniformly
  bounded analytic divided-difference remainders, including joint complex
  Fréchet differentiability across zero scale.
- The actual ring of real-analytic germs, its analytic representatives,
  evaluation map, unit criterion, unique maximal ideal, and real residue
  field. The analytic identity principle proves that it is an integral domain.
  Directional differentiation gives real-linear derivations, including
  coordinate partial derivatives. Analytic pullbacks give algebra maps and
  equivalences, with explicit coordinate addition and restriction maps.
- A convergent analytic Hadamard decomposition proves that the maximal ideal
  is generated by the coordinate germs in every finite dimension. The actual
  cotangent space has dimension `p` over the residue field, and an explicit
  coordinate prime chain proves Krull dimension at least `p`.
- The actual analytic-germ ring is Noetherian and regular in every finite
  dimension, with Krull dimension exactly the number of variables. This is
  proved by convergent division and induction on the dimension. In one
  variable every nonzero ideal is generated by a coordinate power, so the
  ring is also a discrete valuation ring.
- The faithful real algebra map from polynomials into analytic coordinate
  germs, represented by ordinary polynomial evaluation.
- A complete real Banach algebra of weighted absolutely summable multivariate
  coefficient series, with the Cauchy-product norm estimate and bounded
  evaluation maps. Every actual analytic germ has a weighted coefficient
  representative at some positive radius, and such coefficient series
  evaluate to genuinely analytic functions near zero.
- A regularizing continuous linear coordinate change for every nonzero
  analytic germ, its first nonzero axis coefficient, and scalar normalization.
  The coefficient-tail operator has its sharp norm bound. A derived radius
  shrink supplies the Neumann-series bound and produces division for every
  actual analytic dividend germ, with a remainder of fixed degree whose
  coefficients are actual analytic germs in the remaining variables.
  No smallness, quotient-convergence, or division-existence assumption is
  added to the general Noetherian theorem.
- The polynomial ideal contraction height bound in Section 3, for arbitrary
  ideals and any finite number of variables. Polynomial and Laurent
  coefficient extension preserve ideal height.
- The paper's polynomial-extraction lemma: an ideal of height at least
  `p+m` over the actual `p`-variable germ ring contains a monic real polynomial
  in each selected polynomial variable. Nonvanishing is proved both before
  and after coefficient embedding; the ideal need not be radical.
- For arbitrary signed integer weights, the full initial ideal is the
  specialization of the actual Laurent deformation and has height at least
  the original ideal. The generator equality uses all ideal elements and
  works with zero divisors in the coefficient ring.
- For every finite tuple of signed integer weights, the ideal of actual
  least lexicographic components equals successive scalar initial ideals
  and cannot have smaller height. The proof lifts homogeneous members of
  full initial ideals and handles arbitrary mixed-weight members explicitly.
- Full ordinary homogenization, defined by all literal homogenizations,
  equals the Laurent contraction, is saturated in the homogenizing parameter,
  and preserves ideal height.
- Identity-homogeneous ideals of additive group rings are extended from
  their coefficient contraction. For the actual finite-rank Laurent ring
  with exponent group `Fin h → ℤ`, this contraction preserves height.
- In any algebra over a characteristic-zero field, derivations preserve
  minimal primes of invariant ideals. A nonvanishing square derivation
  determinant therefore forces the prime height to be at least its size.
  This supplies an alternative to localization regularity for the rank argument.
- Actual polynomial coefficient and symbol derivations, including their
  action on analytic coefficient representatives. A full-row-rank matrix
  has a nonzero selected column minor, and the complete sum of squared
  minors is positive over the reals.
- The augmented ideal generated by the original equations and the inverse
  relation for their formal squared-minor sum has height at least the number
  of equations plus one. Contracting the inverse symbol and `a` auxiliary
  symbols costs at most `a+1` in height, including ideals of infinite height.
- A polynomial in actual analytic germs has a polynomial-valued germ with
  finite analytic coefficient representatives on one common neighborhood.
  Finite ideal identities hold there for every assignment of the independent
  symbols, without boundedness restrictions. Finitely many ideal members
  therefore vanish at the common zeros of the displayed generators on one
  neighborhood.
- The complete regular-zero elimination lemma (`lem:rank`, lines 744–814),
  over the actual analytic-germ ring. The original equation map uses only
  its supported analytic coefficients and an arbitrary smooth auxiliary
  function on the projected open domain. Its actual Fréchet derivative
  factors through the represented formal Jacobian, so surjectivity proves
  positivity of the squared-minor denominator. The exact retained-variable
  contraction has height at least `m+p`, and finitely many analytic generator
  representatives vanish at every regular zero on one common smaller
  neighborhood. No bound on the auxiliary symbols or inverse denominator
  is required.

- The actual finite-product triangular iteration `N_(j+1)=initial(J N_j)`
  eventually stabilizes permanently at a `J`-invariant submodule, assuming
  finite ambient module length, homogeneous initial data, and an actual
  unipotent triangular linear equivalence. Explicit short exact sequences
  prove preservation of every prefix length under full initial formation,
  and a bounded integer potential proves termination.
- Reverse inclusion of coordinatewise exponent upper sets is well-quasi-ordered,
  proved using finite box complements and Dickson–Higman arguments. Families
  with fixed positive-weight monomial counts and arbitrary integer component
  shifts are finite, and one finite Dickson cover has a common degree bound.
- Actual position-first polynomial-module leading terms are compatible with
  monomial multiplication. Matched leading coefficients can be cancelled with
  a strict decrease, so well-founded division lifts a finite leading cover to
  finite generators. Weighted coefficient projections make those generators
  homogeneous without changing their prescribed leading terms.
- Actual coefficient-coordinate echelon arguments identify every homogeneous
  piece's dimension with the corresponding slice of the full leading monomial
  submodule. Consequently, for any fixed weighted Hilbert function, one natural
  degree bound works for the actual homogeneous generators of every polynomial
  submodule having that function.
- The Artinian bridge uses actual quotients of induced ideal-power filtrations.
  Their canonical residue-field dimensions sum degreewise to the original
  module length, without choosing a coefficient-field section or claiming that
  individual layer dimensions stay fixed. Chosen coefficient-ideal generators
  give an explicit homogeneous finite free cover of the fixed ambient layer
  product. The cover intertwines all weighted components, and its kernel and
  the pullback of every induced layer sum are proved homogeneous. Finite-weight
  initial formation is also proved to commute with the relevant semilinear and
  homogeneous quotient maps. The induced degree slices are canonically
  identified with the component ranges, removing the last abstract hypothesis
  from the uniform residue-field generator theorem. The canonical map from the
  graded pullback onto the induced-layer sum is constructed and shown to
  commute with homogeneous components. Homogeneous numerator representatives
  of one finite pullback generating family span every induced quotient and
  lift through the finite filtration. This gives a uniform bound for finite
  homogeneous generating sets over the original Artinian local coefficient
  ring, without choosing a coefficient-field section. For the concrete
  terminal rank-one ideal iteration, localization away from the minimal
  primes, contraction, denominator clearing, saturated principal reduction,
  and induction on Krull dimension now give permanent stabilization over
  every Noetherian coefficient ring of bounded dimension. The manuscript's
  broader arbitrary graded-module formulation is not separately packaged as
  one theorem.

- The number of actual least or greatest nonzero leading coordinates of a
  finite-dimensional subspace equals its dimension. This is proved from
  explicit coordinate maps and module lengths, without an assumed echelon form.
- The actual finite-rank additive group algebra is the localization of a
  polynomial ring at its variables. An explicit finite exponent shift clears
  all denominators. Group Laurent rescaling is a genuine algebra equivalence
  with a proved coefficient permutation; weighted-component closure gives
  coefficient extension and preserves the contraction's height.
- The central Laurent contraction is constructed from actual polynomial
  translation, the full original least lexicographic initial ideal, inversion
  of all selected variables, rescaling, and literal contraction to the
  weight-zero polynomial subring. The final signed-Stirling block maps and time
  translation form an explicit polynomial algebra equivalence. Composing them
  gives the full algebraic central ideal, recovers the preliminary contraction
  by comap, and proves the required height inequality.
- Exact binomial commutator and signed-Stirling first/second lowering
  identities are proved, including boundary cases, over arbitrary rational
  algebras. The actual bounded terminal fields satisfy `L₁=-V₁`, `L₂=V₂/2`,
  and the exact Lie recurrence generating every positive `V_q`. The manuscript's
  simultaneous signed-Stirling map is now an explicit algebra equivalence with
  its independent block multigrading, and every chosen block has an exact
  polynomial index split. The parameter deformation identifies global
  homogeneous components with the relevant block-axis coefficients. The
  resulting vector fields are transported through simultaneous Laurent
  localization; triangular derivative extraction and multivariate
  derivative-stable extension remove every higher block variable. The
  localized multigrading then removes all Laurent variables, proving the
  qualitative terminal elimination identity and its retained-contraction
  height bound.
- For an arbitrary ordinary homogeneous ideal in `B[H,t]`, setting `H=1`
  cannot lower height. The proof identifies the localized ideal with a Laurent
  extension of the actual dehomogenized ideal and assumes no `H`-saturation.
  Regrouping and contracting a finite family of time variables then costs at
  most its cardinality, including the exact `height C - h` manuscript form.
- The quantitative transfer theorem is proved for the actual real derivative
  jets and analytic coefficient representatives. Finite support extraction,
  central/source evaluation identities, superpolynomial perturbation control,
  and inverse-power lower-bound transfer are all explicit. For one terminalized
  cluster, fixed localization coefficients now produce an actual
  denominator-cleared backward step, and the real-jet transfer theorem feeds
  directly into its terminal-generator lower bound. On an infinite separated
  tail, such a positive lower bound is proved incompatible with eventual
  common vanishing of the evaluated equations. A finite family theorem now
  concatenates the real-jet transfer/localization steps into an actual
  separated-cluster backward trace; balancing and cross-cluster hierarchy
  theorems derive its main scale conditions from the paper's separation data.
  The rank-elimination boundary now supplies the actual analytic-germ ideal,
  finite generators, analytic representatives, and evaluated vanishing on the
  restricted separated tail, with a nonempty padded transfer certificate and
  a terminal lower-bound seed from a genuine nonzero real polynomial.
- The restricted regular-zero base case `P(0,0)` is proved directly from the
  analytic-germ machinery. A monic specialization controls every auxiliary
  coordinate after the bounded parameters are forced to their limiting value.
  Exponential adjunction then proves the complete base row `P(0,q)`.
- The outer representative induction now removes every bounded representative
  using the lower-count slice theorem. From an infinite base regular-zero set,
  the maintained setup produces an injective subsequence with all
  representatives tending to infinity, a fixed Abel-time ordering, canonical
  nonempty ordered clusters, one natural width bound, and divergent gaps
  between clusters.
- For the complementary pair branch, the fixed pair and nearest integer are
  selected on one subsequence and the exact logarithmic displacement tends to
  zero. The nonlinear merge is a smooth injective coordinate change with
  invertible derivative. Its explicit pullback preserves injectivity, box
  convergence, tail-domain membership, and regular-zero membership. The exact
  infinite-set dichotomy either retains infinitely many simultaneously
  separated indices or produces a strict near-integer subsequence inside the
  chosen infinite set, already carrying a fixed pair and displacement limit.
- Pullback of every old base/tower expression is contained in a fixed enlarged
  exponential tower. Pulled Abel jets are classified exactly into ordinary
  lower-rank jets and two exceptional shifted families. Finite polynomial
  support now isolates all exceptional offsets, appends one graph coordinate
  per distinct offset, and places every graph equation in an explicit finite
  tower. Arbitrary-order exceptional derivatives have explicit positive common
  denominators and numerator identities in finite iterate towers. The selected
  `q + 2` sequence is transported to an injective `q + 1` sequence with the
  enlarged box limit and eventual merged-system regular zeros. The simultaneous
  graph system has an explicitly computed positive diagonal vertical derivative
  and therefore preserves regular zeros through the finite graph lift. All
  exceptional graph equations and derivative data can be placed in one common
  finite tower. Generic multivariable polynomial families are cleared by a
  positive common product denominator, and the transformed and graph rows are
  concatenated into one flat `Fin (n + N)` family with exact regular-zero
  transport and terminal-tower membership. The compressed old rows now have
  one explicit common tower: their finite jet support, all exceptional
  denominators and numerators, and every graph row are assembled into the
  denominator-cleared augmented square family at its terminal level.
- The final smooth-family stage now has exact Lean interfaces for geometric,
  globally smooth, derivative-closed, 0-regular, and uniformly fiber-finite
  families. The functions `C_r(x)=A^(r)(1+x^2)` are globally analytic and obey
  the exact affine-coordinate derivative formula. The concrete Abel family is
  the localization of an explicit finite numerator syntax by everywhere
  nonzero numerators; it is proved geometric, globally smooth under `IsAbel`,
  coordinate-derivative closed, and inclusive of the required `C_r` and `C_0`
  generators. Every numerator expression is also reduced to one explicit
  multivariable polynomial in the ordinary coordinates and a finite `Fin b`
  list of affine Abel-jet generators, including exact affine-substitution
  semantics. The rowwise lists for any square system are combined into one
  shared finite list and one polynomial per row. The resulting lifted
  numerator rows and all graph equations `s_j=1+ell_j(x)^2` are proved to lie
  in one restricted Abel expression base and recover the original square
  system exactly along the graph. Coordinatewise denominator clearing is
  formalized for every
  square tuple and target: it produces a numerator tuple with exactly the
  same regular-zero set, reducing 0-regularity to numerator-level finiteness.
  Smooth regular fibers are
  identified with the project's square `regularZeroSet`. Projected zero sets
  contain the empty and full sets, are closed under intersections, unions, and
  flat Cartesian products, are invariant under invertible linear changes of
  visible coordinates, have closed zero-set lifts, and contain flat graphs of
  family members. Polynomial equality, positivity, and negativity sets, and
  their finite Boolean sign normal forms, have explicit projected-zero
  encodings; complement closure of the sign syntax is proved by real
  trichotomy. Continuous fiber projection is proved not to increase the
  extended-natural number of connected components, both for product domains
  and flat `Fin (n+q)` coordinates; uniform fiber finiteness therefore gives
  one bound for every visible projection. The manuscript's matrix map
  `H_f(x,z,M)=(f(x,z),Mx,M)` is formalized componentwise, with its exact fiber
  identity and a single uniform bound for all affine matrix sections. The
  target unary-piece class has the required Boolean closure.

The regular-zero chain is now complete.  The finite analytic generator family
is transported through every ordered-cluster boundary, including the mixed
individual/simultaneous interfaces and the bottom terminal localization.  The
canonical diagonal data supplies all numerical separation margins, the
all-cluster backward propagation reaches the contradictory top lower bound,
and the resulting normalized separated contradiction closes the outer
representative induction.  Consequently every Abel numerator system has
finitely many regular zeros and the concrete geometric Abel family is proved
0-regular.  The rectangular-Jacobian development now supplies rank/minor
certificates, local implicit charts, and the full finite-dimensional
constant-rank fiber theorem, including rank zero.  A separate reduction makes
the quantifier boundary explicit: targetwise finite rank pieces give only
targetwise fiber finiteness, while one uniform bound on their finite cover
would give the required uniform fiber theorem.  The arbitrary-codimension
Lagrange system and its Sard-based generic-center theorem are also proved:
for every globally regular finite constraint tuple there is one squared-distance
center whose augmented critical system is regular at every zero.  The Charbonnel description
language, its exact rank weights, and the closed literal-zero-set base bridge
are also formalized without assuming complement closure.  Nonzero Jacobian
minor patches now have a reciprocal closed-equation lift, giving targetwise
finite connected components for every globally maximal-rank fiber piece.
The Lion development now follows Lion's 2002 proof directly.  The standard
carpet `1/(1+‖x‖²)` is in every geometric family, the enlarged map
`(x,u,v,t) ↦ (δ(x)-u², ‖g(x)-t‖²+v²,t)` is formalized in flat Euclidean
coordinates and remains in the family, and fiberwise-full generic parameters
are selected with Lion's nested shrinking-ball inequalities.  Uniform bounds
pass through decreasing compact intersections and increasing exhaustions, so
a generic bound for the enlarged map gives the bound for every original
fiber.  Carpeted leaves are now represented by their associated
`(U,δ,f)` data, and 0-regularity proves every terminal codimension-`n` leaf
finite.  Lemma 3 is formalized with the exact maximal-minor sum, its regular
locus, and the carpet `δ·|θ|/(1+|θ|)`.  For Lemma 4, the lifted
squared-distance denominator, radial carpet `δ_a`, and the resulting
critical carpet on the regular leaf are in the family and satisfy the required
compact-superlevel properties.  Every connected component of a leaf fiber
also contains a carpet maximum.  Lion's Rolle Lemma 5 is formalized for actual leaf equations as the
cardinal inequality between a full fiber and the connected components of the
preceding partial fiber; its source-facing form derives the augmented rank
condition from submersivity on the leaf.  The four-case strong induction and
finite-section sum estimates of Theorem 7' are also compiled.  An honest
Theorem 7' output consisting of a full L² parameter set and finitely many
genuine zero-dimensional leaves now specializes to the flat enlarged map;
0-regularity supplies its numeric bound and Lemma 6 turns it into UFF.  The
source-faithful Lion core is complete.  Rectangular parametric Sard
selects radial parameters for the finite critical-coefficient cover, the
numerical Theorem 7' induction gives conull generic fiber bounds, and the flat
compactification/Fubini bridge proves `HasUniformFiberFiniteness` from the four
standing family hypotheses.  The completed regular-zero theorem specializes
this result to `abelGeometricFamily A` for every `IsAbel A`.  The older
canonical rank/minor Lagrange-cover route is retained for comparison but is
not used by this theorem.

Maxwell meagre-closure component selection is now derived internally from the
lower-dimensional closure regularity induction and WS5.  The source-faithful
Lion theorem now supplies `HasUniformFiberFiniteness` outright, so it is no
longer a residual input to the complement-theorem pipeline.
Proper square maps now have finite regular full fibers
and one upper bound over each compact set of regular targets, leaving singular
and unbounded targets for the global theorem.  On the complement side, arbitrary real-linear image
closure gives WS1--WS4, Maxwell's compact comparison and numeric description
induction give WS5 conditional on uniform fiber finiteness, and Charbonnel's
section 5.8 closure-nullity witness is complete.  The complement checkpoint
places DC on the projected-zero base family, constructs the all-arity
first-order envelope from positive-arity complement closure, and records the
still-open steps in that alternate Section 5 route.  The moving closed-ball
incidence and its
uniform WS5 component bound formalize Charbonnel's section 5.3(a).  Closed
lifts now also give the required `F_sigma` and meagre presentations.
`KuratowskiUlamProduct` proves the missing category/Fubini theorem for
Baire-measurable subsets of a product.  Under WS5 and WS6,
`MaxwellMeagreClosureFamilyEquivalence` proves that the meagre finite-selection
predicate is exactly family-level closure-interior regularity.
`MaxwellMeagreClosureSelection` supplies the family-geometric argument:
disjoint vertical slabs, lower-dimensional closure regularity, and
Kuratowski--Ulam produce arbitrarily many components if a meagre member had
closure with interior, contradicting WS5.  Thus Maxwell selection and the
closure-interior regularity induction are both derived internally.  The
ambient-dimension induction is assembled with the connected compact
positive-volume successor: WS5 and compact
component isolation reduce the latter to connected members, and the resulting
`P'_n` induction plus closure regularity proves all four closure/interior/nullity
  equivalences directly.  A separate analysis of section 5.3(b,c) formalizes
the component interval and containment algebra under a full-support premise.
A compact semialgebraic counterexample shows that full support cannot be
required at the global maximum count; the source's descent may lower that
count.  The rank-one base is complete: full projection rules out zero
components, count one forces zero defect, and hence a positive-defect
stationary chain can only begin at component count at least two.
`CharbonnelSection53GlobalDichotomy` still assumes a rank-preserving
no-descent successor choice to construct the stationary chain.  Once such a
chain is available, its inclusion-induced parent maps produce pairwise
disjoint lost branches and an injective sequence of canonical heights.  If
each finite prefix meets one chordal affine section, those branches give
arbitrarily many affine-section components and WS5 excludes the chain.  A
common line is only a stronger sufficient case, and the two-branch case is
unconditional.  Thus this alternate section 5.3 route still needs both the
successor/localization step and finite-prefix chordal-section selection; it is
not an additional premise of the exact final reduction.  For sections
5.4--5.6, the infinite-fibre locus
belongs to the Charbonnel closure and its closure gives a closed exceptional
base; Maxwell closure-interior regularity supplies the interior lift.  This
repairs the printed local-closedness assertion, which is false even for compact
semialgebraic sets.  `CharbonnelSection57GraphExtraction` reduces Section 5.7
to a stable local closure-fibre bound.  The infinite-fibre bridge derives that
bound from Maxwell closure-interior regularity once stable components can be
localized inside any prescribed nonempty open part of the trace interior.
The relative-localization bridges preserve a prescribed open region during
lexicographic descent and convert relative stable components on an open base
to the ambient stable witness used by graph extraction.  Thus the Section 5.7
endpoint still asks for stable-closure open localization, but its local
geometric content is narrowed to the existing strict-refinement interface;
the fibre-cardinality inequality is no longer independent.  The final theorem
bypasses this alternate endpoint through direct positive-zero-trace category
smallness.  Maxwell's family-level closure-regularity/finite-selection argument
remains independent.
The retained deep-cell Section 4 induction is now complete.
`WilkieSection4UnaryPartitionBase` supplies the base case;
`WilkieSection4DeepBoundedSuccessorAssembly` and
`WilkieSection4DeepCommonRefinementSuccessor` prove the two successor clauses;
`WilkieSection4LiteralZeroInduction` iterates them in every dimension; and
`WilkieSection4DeepEndpointAssembly` packages the hereditary covers into the
bounded projection-coherent tower consumed by the complement pipeline.
Wilkie's bounded-coordinate homeomorphism, the semialgebraic graph of it and
its inverse, relative closedness, projection compatibility, the cube-relative
finite-cover complement, and pullback to ordinary complement closure are all
proved.  The unary cell base and finite-cover/WS6 endpoint are therefore
internal.

The Maxwell 2.3--2.4 route is now complete relative to the four Charbonnel
interfaces already produced by section 5: the positive-arity weak structure,
trace membership, and Theorems 2.1 and 2.2.  Lemma 2.3.1 has a compiled scalar
ordered-selection construction, vector coordinate induction, and continuity
localization.  Lemmas 2.2.1 and 2.2.2 are proved from WS5 and Theorem 2.1, so
continuous weak selection has no independent source premise.  Applying it on
a polynomial-sign ball inside Wilkie's exceptional slice produces the exact
weak singular witness directly.

For Theorem 2.4, directional quotient relations of pseudofunctions have empty
interior; localized one-sided IVT fills the extended fibers after deleting the
derived continuity obstruction; bounded cluster extraction supplies every
finite or signed-infinite cluster needed by the classification.  On the two
equal-infinity loci, singleton extended fibers give genuine fixed-base direct
limits, and WS5 extracts both affine-chord contradictions.  A complete
nine-case finite/positive-infinity/negative-infinity argument derives the
translated separation obstruction on the disagreement locus.  The corrected
first-order assembly therefore has no residual mechanism fields: it produces
the scalar first-order package, every finite differentiability order, vector
output reduction, and Maxwell almost-everywhere smoothness automatically.
`MaxwellSection5Smoothness` also derives Theorems 2.1 and 2.2 inside the
section 5 induction and feeds them to this automatic endpoint, so Maxwell 2.4
is no longer a separate hypothesis at that level.
The source uses balls relative to its base set `ω`; the formalized relative
stability endpoint is separate from the stronger ambient-ball interface.
The alternate global-stratum analysis now has compact component supports, the
maximum count and minimum defect, and a closed defective-support union.  For
stationary nested chains, compactness and deletion prove the singleton limit
and the source's projected neighborhood of the limit fiber.  Building the
rank-preserving chain still requires the explicit no-descent successor choice;
afterwards the chordal finite-prefix condition supplies the affine-section
explosion.  These are gaps in that alternate route rather than extra
hypotheses of the exact final reduction.  Wilkie's literal-zero
Sardian radial constituent and its nested positive-level modulus are proved
from smoothness and geometric-family closure.  The positive-projection
constructor now builds finite radial and squared-Jacobian-minor choices,
normalizes mixed depths, constructs the from-below and from-above clauses,
chooses one compact boundary scale for every possible old constituent, and
iterates the one-coordinate result to arbitrary positive hidden arity.
Wilkie Lemma 3.4 supplies the common regular-value modulus once the finite
critical-value set has empty interior.  The constructor is therefore reduced
to critical-value smallness.  `Wilkie27CriticalValues` proves that smallness
directly for family tuples: weak selection produces a local section through
the critical incidence, Maxwell almost-everywhere smoothness supplies a
differentiability point, and the chain rule contradicts nonsurjectivity.
Thus the complete arbitrary-block projection constructor no longer assumes a
general rectangular Morse--Sard theorem.
The 3.13
closed-section three-piece identity and earlier weak-family sign cuts are
proved.  Wilkie's literal source stages, their computed-depth embedding of
every maintained description, and the transfer of a stagewise Sardian
induction hypothesis to the three predecessor cuts are now formalized.  All
three source expansions preserve WS1–WS4, so every stage is weak from the
base weak-family assumption alone.  The one-row 3.12–3.13 frontier trace is
therefore available at every weak source stage.  For the maintained numeric
description syntax, explicit lower-rank exact and strict-side replacements
now prove the complete integer-affine rank branch, including arbitrary finite
affine systems at closure nodes.  No independent integer-affine rank input
remains; all source stages are Sardian from the positive-projection theorem.
Finite locally closed decomposition is retained only as a sufficient stronger
route to the closure-interior theorem; it is not attributed to Charbonnel.

Definability uses mathlib's `FirstOrder.Language` and `Set.Definable`, with
all real parameters allowed. O-minimality is explicitly finite decomposition
of every definable unary set into points and intervals, including rays.
It is not represented by an unspecified predicate or a regular-zero
finiteness hypothesis.

Reid Barton's earlier Lean 3 `lean-omin` development was audited for reuse.
Its Boolean/projection and first-order assembly patterns already have Lean 4,
mathlib-only counterparts in this project; its main function-family criterion
assumes the projection closure that Wilkie's complement theorem must supply.
See [BARTON_REUSE_AUDIT.md](BARTON_REUSE_AUDIT.md) for the source-level map and
the decision not to duplicate the old framework.

`mainTheorem_iff_ominimality` identifies the complete proposed theorem with
its o-minimality assertion, and `AbelFormalization.mainTheorem` proves that
proposition. See [DEPENDENCIES.md](DEPENDENCIES.md) for the dependency map.

## Build

Install Lean through elan, then run these commands in this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean AbelExistenceAudit.lean
lake env lean StatementCorrespondenceAudit.lean
```

The project pins Lean `v4.34.0-rc2` and mathlib commit
`e37d88a26f3791ed5a93daa1f949af1021b8d103`. Mathlib is the only direct
package dependency; its upstream dependencies are locked by `lake-manifest.json`.

`Audit.lean` checks declarations from every project module, including
definitions, instances, and theorem declarations, and rejects any declaration whose transitive axioms include
anything beyond Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
In particular, it rejects `sorryAx`. The checked development adds no axioms
and contains no `sorry`, `admit`, or `native_decide` proofs.

The repository includes the complete library in `AbelFormalization/`, its
public umbrella import, the standalone audits, and the development notes.
`Scratch/` preserves earlier experiments and targeted checks; it is an archive,
not part of the public library build, and its files need not compile individually
against the final library. Build caches and temporary PDF renderings are omitted.

Some historical verification logs record the original workstation's
`sh ../../work/run-lake.sh` wrapper. In a fresh clone with elan installed, use
`lake` directly in its place; the wrapper is not a project dependency.

## File guide

| File | Purpose |
| --- | --- |
| `AbelFormalization/Basic.lean` | Exact assumptions and initial dynamical results |
| `AbelFormalization/AbelExistence.lean` | Unconditional existence of a positive analytic invariant density and of `A` satisfying exactly `IsAbel` |
| `AbelFormalization/AbelExistentialMainTheorem.lean` | Applies the proved main theorem to the constructed witness, giving existence of the claimed o-minimal expansion |
| `AbelFormalization/Inverse.lean` | Positive-domain bijection and inverse identities |
| `AbelFormalization/Statement.lean` | Actual first-order language and complete target proposition |
| `AbelFormalization/Growth.lean` | Growth from monotonicity and the inverse recurrence |
| `AbelFormalization/Consequences.lean` | Growth specialized to the paper's hypotheses |
| `AbelFormalization/Definability.lean` | Explicit witnesses and first-order definability proofs |
| `AbelFormalization/Analytic.lean` | Generator analyticity and differentiated Abel equation |
| `AbelFormalization/DerivativeBounds.lean` | Compact and geometric bounds proving `x A′(x) → 0` |
| `AbelFormalization/InverseRegularity.lean` | Inverse continuity and differentiation |
| `AbelFormalization/Orbit.lean` | Fundamental interval decomposition |
| `AbelFormalization/OrbitBounds.lean` | General compact-orbit contraction principle |
| `AbelFormalization/Stirling.lean` | All-order transport and actual falling-factorial coefficients |
| `AbelFormalization/LowerDerivativeBounds.lean` | Scaled lower derivative limit and upper inverse derivative bound |
| `AbelFormalization/HigherDerivatives.lean` | Decay of every positive derivative |
| `AbelFormalization/LogBound.lean` | Eventual logarithmic upper bound and Big-O |
| `AbelFormalization/InverseEstimates.lean` | Inverse recurrence derivatives and double-log inequalities |
| `AbelFormalization/Hierarchy.lean` | Quantitative mean-value bound and power separation |
| `AbelFormalization/FiniteHierarchy.lean` | Separation modulo integers for all finite clusters |
| `AbelFormalization/ComplexExtension.lean` | Complexification of real power-series coefficients |
| `AbelFormalization/CompactComplexExtension.lean` | Uniform bounded local branches over a compact interval |
| `AbelFormalization/ComplexCompatibility.lean` | Identity principle and compatibility on overlapping disks |
| `AbelFormalization/ComplexLog.lean` | Quantitative principal-logarithm disk estimates |
| `AbelFormalization/ComplexLogIterates.lean` | Analyticity and disk control for every iterate count |
| `AbelFormalization/ComplexEstimates.lean` | Compatible fixed-radius disk extensions with logarithmic bounds |
| `AbelFormalization/ComplexStrip.lean` | One bounded analytic extension on every fixed-width right half-strip |
| `AbelFormalization/AnalyticEstimates.lean` | The complete analytic-estimates lemma assembled from its proofs |
| `AbelFormalization/HermiteNodeBounds.lean` | Node polynomial, colliding multiplicities, contour lower bound |
| `AbelFormalization/HermiteKernel.lean` | Polynomial divided-difference kernel, coefficients and degree bounds |
| `AbelFormalization/AnalyticMultiplicity.lean` | Vanishing jets, grouped divisibility, interpolation uniqueness |
| `AbelFormalization/HermiteContour.lean` | Actual contour coefficients and analytic remainder factorization |
| `AbelFormalization/HermiteInterpolation.lean` | Existence and uniqueness with combined multiplicities |
| `AbelFormalization/NormalizedPolynomial.lean` | Factorial-normalized coefficients and derivative expansions |
| `AbelFormalization/HermiteBounds.lean` | Compact uniform coefficient-kernel bounds |
| `AbelFormalization/HermiteAnalytic.lean` | Joint kernel analyticity and derivative bounds |
| `AbelFormalization/HermiteCoefficientBounds.lean` | Uniform ordinary and normalized coefficient bounds |
| `AbelFormalization/GeneralHermiteBounds.lean` | Bounds for arbitrary contour and node radii |
| `AbelFormalization/ContourFunctional.lean` | Bounded linear contour integration on continuous functions |
| `AbelFormalization/HermiteCoefficientAnalytic.lean` | Full multivariable analyticity of actual contour coefficients |
| `AbelFormalization/HermiteScaling.lean` | Polynomial and coefficient rescaling, including colliding nodes |
| `AbelFormalization/AbelHermiteFamily.lean` | Uniform Hermite family assembled from the Abel assumptions |
| `AbelFormalization/ComplexJets.lean` | Agreement of real and complex derivatives |
| `AbelFormalization/CentralJet.lean` | Central signed-Stirling jet formula |
| `AbelFormalization/CentralBounds.lean` | Joint central analyticity and uniform linear growth bound |
| `AbelFormalization/CentralCoefficients.lean` | Independent interpolation parameters and zero-scale coefficients |
| `AbelFormalization/CentralIdentity.lean` | Complex Abel rescaling identity on connected domains |
| `AbelFormalization/AnalyticRemainder.lean` | Analytic divided differences and the uniform Schwarz bound |
| `AbelFormalization/CentralCoefficientBounds.lean` | Uniform scale-disk bounds and scalar analytic remainders |
| `AbelFormalization/AnalyticCircleParameter.lean` | Differentiation of contour integrals in complex parameters |
| `AbelFormalization/AnalyticContourFamily.lean` | Banach-valued analytic contour families |
| `AbelFormalization/HermiteFamilyAnalytic.lean` | Joint analytic dependence on target families and nodes |
| `AbelFormalization/CentralCoefficientAnalytic.lean` | Joint analyticity of all independent central parameters |
| `AbelFormalization/ParametricCauchyRemainder.lean` | Fixed-contour remainder identity, joint holomorphy and bounds |
| `AbelFormalization/ParametricDividedDifference.lean` | Equality with the actual divided difference, including zero |
| `AbelFormalization/CentralRemainderHolomorphic.lean` | Joint holomorphy on the paper's parameter domain |
| `AbelFormalization/CentralSubstitution.lean` | Exact central coefficient formula at the exponential scale |
| `AbelFormalization/CentralThreshold.lean` | One threshold for every central interpolation constraint |
| `AbelFormalization/HermiteLemma.lean` | The complete uniform Hermite lemma, assembled from `IsAbel` |
| `AbelFormalization/AnalyticGerm.lean` | Actual real-analytic germ ring and evaluation |
| `AbelFormalization/AnalyticGermLocal.lean` | Units, locality, maximal ideal and residue field |
| `AbelFormalization/AnalyticGermDerivatives.lean` | Representative-independent directional differentiation |
| `AbelFormalization/AnalyticGermDerivation.lean` | Real-linear derivations and coordinate partial derivatives |
| `AbelFormalization/AnalyticGermDimensionZero.lean` | Zero-variable equivalence with ℝ, Noetherianity and dimension |
| `AbelFormalization/AnalyticGermDomain.lean` | Analytic identity principle rules out zero divisors |
| `AbelFormalization/AnalyticGermComposition.lean` | Analytic pullbacks, algebra equivalences and coordinate restrictions |
| `AbelFormalization/AnalyticHadamard.lean` | Convergent analytic factorization through the input coordinates |
| `AbelFormalization/AnalyticGermGenerators.lean` | The maximal ideal is generated by the coordinate germs |
| `AbelFormalization/AnalyticGermCotangent.lean` | Cotangent identification and dimension over the actual residue field |
| `AbelFormalization/AnalyticGermDimensionLower.lean` | Explicit coordinate prime chain and Krull dimension lower bound |
| `AbelFormalization/AnalyticGermOneVariable.lean` | Coordinate-power ideal classification, PID, Noetherianity and DVR |
| `AbelFormalization/AnalyticGermRegularLowDimension.lean` | Regularity and exact dimension in zero and one variables |
| `AbelFormalization/AnalyticGermNoetherianConsequences.lean` | General regularity and dimension conditional on Noetherianity |
| `AbelFormalization/AnalyticGermPolynomial.lean` | Faithful polynomial-coordinate algebra map |
| `AbelFormalization/AnalyticRegularDirection.lean` | Actual regularizing coordinate automorphism and finite axis order |
| `AbelFormalization/WeightedSeries.lean` | Weighted summability and Cauchy-product norm bounds |
| `AbelFormalization/WeightedSeriesBanach.lean` | Complete coefficient Banach algebra identified with ℓ¹ |
| `AbelFormalization/WeightedSeriesEvaluation.lean` | Absolutely convergent evaluation and algebra laws |
| `AbelFormalization/WeightedSeriesEvaluationMap.lean` | Bounded linear and algebra evaluation maps |
| `AbelFormalization/WeightedSeriesAnalytic.lean` | Actual analyticity from weighted coefficient convergence |
| `AbelFormalization/AnalyticWeightedRepresentation.lean` | Weighted representatives derived from actual analytic expansions |
| `AbelFormalization/BanachDivision.lean` | Abstract Neumann-series division, uniqueness and norm bounds |
| `AbelFormalization/WeightedSeriesDivision.lean` | Sharp coefficient-tail norm and weighted division under smallness |
| `AbelFormalization/IdealHeight.lean` | Polynomial contraction bound and extension height preservation |
| `AbelFormalization/LaurentIdealHeight.lean` | Monomial saturation and Laurent extension height preservation |
| `AbelFormalization/AnalyticGermNoetherian.lean` | Unconditional Noetherianity, regularity, and exact dimension in every finite dimension |
| `AbelFormalization/NoetherianByPrincipalQuotients.lean` | Finite quotient modules and the abstract principal-quotient induction step |
| `AbelFormalization/WeightedSeriesAxis.lean` | Actual axis expansions, analytic order, and first-coefficient normalization |
| `AbelFormalization/WeightedSeriesRestriction.lean` | Restriction to smaller positive radii with explicit value and norm bounds |
| `AbelFormalization/WeightedSeriesGerm.lean` | Actual analytic-germ algebra map and weighted representatives |
| `AbelFormalization/WeightedSeriesRegularSmallness.lean` | Derived anisotropic radius shrink and convergent coefficient division |
| `AbelFormalization/WeightedSeriesCoefficientSlice.lean` | Convergent coefficient slices, bounded slice operators, and finite reconstruction |
| `AbelFormalization/WeightedSeriesGermRemainder.lean` | Actual polynomial remainder identity with lower-dimensional analytic-germ coefficients |
| `AbelFormalization/WeightedSeriesGermDivision.lean` | Division for every actual analytic-germ dividend by a normalized regular divisor |
| `AbelFormalization/SaturatedSpecializationHeight.lean` | Parameter cancellation, minimal-prime avoidance, and specialization height |
| `AbelFormalization/LaurentRescaling.lean` | Actual signed-weight Laurent automorphism and exact coefficient permutation |
| `AbelFormalization/PolynomialExtraction.lean` | Monic scalar coordinate relations from maximum height over augmented local rings |
| `AbelFormalization/AnalyticGermPolynomialExtraction.lean` | Exact paper height(3) for actual analytic germs, with monic and nonzero conclusions |
| `AbelFormalization/LaurentIdealTools.lean` | Laurent coefficient ideals, polynomial contraction, and literal extension-height bridges |
| `AbelFormalization/WeightedDeformation.lean` | Actual Laurent deformation, derived saturation, and height of its special fiber |
| `AbelFormalization/WeightedNormalization.lean` | Minimum support weight, normalized transform, and actual least-weight specialization |
| `AbelFormalization/WeightedDeformationGenerators.lean` | All-element generator equality, full integer-weight initial ideal, and height bound |
| `AbelFormalization/OrdinaryHomogenization.lean` | Literal full ordinary homogenization, contraction equality, saturation, and height |
| `AbelFormalization/WeightedInitialComponents.lean` | Commuting weight projections, full initial ideal homogeneity, and homogeneous ideal invariance |
| `AbelFormalization/WeightedInitialLifting.lean` | Actual ideal-element lifts of every homogeneous initial-ideal member |
| `AbelFormalization/HomogeneousLaurentIdeal.lean` | Homogeneous Laurent ideals, coefficient contraction, and height equality |
| `AbelFormalization/LexicographicInitialForms.lean` | Actual Fin-indexed lexicographic minima and the head-tail component identity |
| `AbelFormalization/LexicographicInitialIdeals.lean` | Full lexicographic ideal equality with successive scalar initials and height bound |
| `AbelFormalization/MultivariateLaurentIdeal.lean` | Identity-graded group-ring ideals and finite-rank Laurent extension height |
| `AbelFormalization/DifferentialMinimalPrimes.lean` | Characteristic-zero derivations preserve minimal primes of invariant ideals |
| `AbelFormalization/DerivationHeight.lean` | Prime height bounds from actual nonvanishing derivation determinants |
| `AbelFormalization/PolynomialGermDerivations.lean` | Actual coefficient and symbol derivations, with analytic coefficient derivative representatives |
| `AbelFormalization/FullRankMinor.lean` | Nonzero selected column minors and positivity of the full squared-minor sum |
| `AbelFormalization/AugmentedJacobianHeight.lean` | Explicit inverse-relation Jacobian determinant and augmented ideal height |
| `AbelFormalization/PolynomialGermIdentities.lean` | Actual polynomial-valued germs, simultaneous analytic representatives, and finite identity transfer |
| `AbelFormalization/PolynomialDerivativeIdealExtension.lean` | Derivative-stable univariate polynomial ideals extend from their coefficient contraction |
| `AbelFormalization/MvPolynomialDerivativeIdealExtension.lean` | Simultaneously partial-derivative-stable multivariate ideals extend from coefficients |
| `AbelFormalization/PolynomialEliminationHeight.lean` | Exact height cost of contracting the auxiliary symbols and inverse symbol |
| `AbelFormalization/PolynomialGermIdealVanishing.lean` | Finite ideal identities vanish uniformly near the base point for all symbol assignments |
| `AbelFormalization/PolynomialEvaluationDerivative.lean` | Actual polynomial differential and the finite coefficient-family product rule |
| `AbelFormalization/PolynomialGermDifferentialRepresentatives.lean` | Coefficient and symbol derivatives represented using the original finite coefficient family |
| `AbelFormalization/PolynomialCoefficientFamilyDerivative.lean` | Derivative regrouping into coefficient derivatives and evaluated symbol gradients |
| `AbelFormalization/PolynomialGermSymbolMaps.lean` | Polynomial-valued germ compatibility with renaming and the inverse-relation tuple |
| `AbelFormalization/PolynomialEliminationLayout.lean` | Explicit flat-to-nested polynomial equivalence, retained contraction, and height transport |
| `AbelFormalization/SurjectiveJacobianRank.lean` | Full matrix rank and positive squared minors from a surjective derivative factorization |
| `AbelFormalization/GermMatrixMinors.lean` | Represented determinants and squared-minor sums, with uniform polynomial evaluation identities |
| `AbelFormalization/JacobianEliminationIdeal.lean` | Actual inverse-relation ideal and exact retained-variable contraction of the required height |
| `AbelFormalization/AnalyticJacobianElimination.lean` | Finite analytic elimination generators on a common neighborhood when the formal denominator is nonzero |
| `AbelFormalization/PolynomialFamilyFormalJacobian.lean` | Actual coefficient-family derivative factors through the formal polynomial Jacobian |
| `AbelFormalization/AnalyticGermFormalJacobian.lean` | Actual analytic-germ derivations and the same-family Jacobian and denominator representatives |
| `AbelFormalization/PolynomialCoefficientPadding.lean` | Zero padding of unused coefficients preserves the original equation map and its derivative |
| `AbelFormalization/PaperRankCoordinates.lean` | The paper's source coordinates and smooth substitution on its exact projected open domain |
| `AbelFormalization/AnalyticRegularZeroElimination.lean` | Elimination at actual regular zeros, with denominator positivity derived from surjectivity |
| `AbelFormalization/AnalyticRankElimination.lean` | The complete manuscript regular-zero elimination lemma with the original supported coefficient data |
| `AbelFormalization/FiniteWeightLengthDescent.lean` | Actual prefix projections and detection of triangular invariance by finite module lengths |
| `AbelFormalization/FiniteWeightInitialLength.lean` | Explicit prefix short exact sequences and length preservation for full initial formation |
| `AbelFormalization/FiniteWeightQuotient.lean` | Finite-weight initial formation under semilinear quotients and homogeneous denominators |
| `AbelFormalization/FiniteWeightIteration.lean` | The actual finite-product triangular iteration eventually stabilizes permanently |
| `AbelFormalization/LocalArtinianFiniteDescent.lean` | Degree-slice rank-nullity and abstract lifting through the induced Artinian filtration |
| `AbelFormalization/ArtinianInducedLayerDegreeIdentification.lean` | Canonical equivalence between induced degree layers and component ranges |
| `AbelFormalization/ArtinianUniformLayerPullbackGenerators.lean` | Uniform residue-field pullback generators with the degree identification discharged |
| `AbelFormalization/ArtinianBoundedGeneratorLifting.lean` | Compatible homogeneous representatives and uniform bounded generation over the original Artinian local ring |
| `AbelFormalization/ArtinianGradedCoverKernel.lean` | Component-intertwining graded cover with homogeneous kernels and induced-layer pullbacks |
| `AbelFormalization/ArtinianGradedLayerCover.lean` | Explicit homogeneous finite free cover of the finite ambient layer product |
| `AbelFormalization/ArtinianLayerComponents.lean` | Actual component maps on ambient and induced Artinian quotient layers |
| `AbelFormalization/ArtinianHomogeneousLayerSpan.lean` | Constant coefficient generators span each polynomial ideal-power numerator |
| `AbelFormalization/ArtinianHomogeneousLayerCover.lean` | Coefficientwise ideal-power stability and finite constant homogeneous numerator generators |
| `AbelFormalization/ArtinianAmbientLayerFinite.lean` | Finite residue-polynomial ambient layers and a fixed finite free cover |
| `AbelFormalization/IdealPowerLayers.lean` | Actual ideal-power quotient layers, residue actions, length sums, and degree-piece filtration |
| `AbelFormalization/MinimalPrimeDescent.lean` | Finite minimal-prime avoidance and dimension-dropping principal quotients |
| `AbelFormalization/MonomialUpperSetBoxes.lean` | Finite box complements and Dickson–Higman proof of reverse-inclusion WQO for exponent upper sets |
| `AbelFormalization/MonomialSubmoduleEncoding.lean` | Actual monomial polynomial submodules, exact containment, and finiteness with fixed standard-degree counts |
| `AbelFormalization/WeightedPolynomialModulePieces.lean` | Actual free polynomial module coordinates and degree-piece dimensions with positive weights and integer shifts |
| `AbelFormalization/WeightedMonomialCountFiniteness.lean` | Finite fibers and finite families for positive weighted monomial counts with integer shifts |
| `AbelFormalization/MonomialUpperFamilyGeneratorBounds.lean` | Uniform finite Dickson covers and generator-degree bounds for fixed weighted counts |
| `AbelFormalization/PolynomialModuleLeadingTerm.lean` | Actual position-first module leading terms and strict cancellation under monomial multiplication |
| `AbelFormalization/PolynomialModuleLeadingSubmodule.lean` | The actual leading-term upper family and its monomial polynomial submodule |
| `AbelFormalization/PolynomialModuleHomogeneous.lean` | Weighted coefficient projections and homogeneous leading-term witnesses |
| `AbelFormalization/PolynomialModuleLeadingDivision.lean` | Well-founded leading-term cancellation and finite generation from a Dickson cover |
| `AbelFormalization/PolynomialModuleHomogeneousGenerators.lean` | Actual finite homogeneous generators lifted from an exact leading cover |
| `AbelFormalization/PolynomialModuleHilbert.lean` | Actual leading-term Hilbert correspondence in shifted weighted degrees |
| `AbelFormalization/PolynomialModuleUniformGenerators.lean` | One homogeneous generator-degree bound for every submodule with a fixed weighted Hilbert function |
| `AbelFormalization/PolynomialGradedLexData.lean` | Concrete shifted multigrading and finite lexicographic iteration data for polynomial modules |
| `AbelFormalization/FiniteLeadingCoordinateDimension.lean` | Actual least/greatest leading-coordinate sets have cardinality equal to subspace dimension |
| `AbelFormalization/GroupLaurentRescaling.lean` | Explicit group exponent shear, coefficient permutation, and inverse rescaling |
| `AbelFormalization/GroupLaurentWeightedIdeal.lean` | Actual weighted-component contraction, coefficient extension, and height preservation |
| `AbelFormalization/FiniteLaurentLocalization.lean` | The actual finite-rank group algebra is the polynomial localization at the variables |
| `AbelFormalization/TerminalCoefficientIdentities.lean` | Exact binomial commutator and signed-Stirling lowering coefficients over arbitrary rational algebras |
| `AbelFormalization/PolynomialParameterDerivations.lean` | Genuine first and second logarithmic derivations from polynomial-parameter coefficients |
| `AbelFormalization/StirlingParameterHom.lean` | Actual finite-block Stirling parameter substitution and explicit variable coefficients |
| `AbelFormalization/TerminalIndexSplit.lean` | Exact split of one derivative block from the global polynomial variables |
| `AbelFormalization/TerminalGlobalStirling.lean` | Actual global signed-Stirling equivalence and independent block multigrading |
| `AbelFormalization/TerminalGlobalParameterDeformation.lean` | Simultaneous parameter deformation conserving total block weights |
| `AbelFormalization/TerminalBlockParameterSpecialization.lean` | Global component/axis bridge and preservation by every terminal block field |
| `AbelFormalization/TerminalInvariantDerivations.lean` | Bounded terminal vector fields, Lie recurrence, and invariant-ideal extraction |
| `AbelFormalization/TerminalLaurentDerivativeExtraction.lean` | One-block Laurent localization and triangular partial-derivative extraction |
| `AbelFormalization/TerminalMultiblockElimination.lean` | Simultaneous finite-block derivative elimination and retained coefficient extension |
| `AbelFormalization/TerminalGlobalMultiblockBridge.lean` | Global terminal fields transported into the simultaneous localized presentation |
| `AbelFormalization/TerminalLocalizedMultigradingBridge.lean` | Global grading transported to the exact localized multigrading |
| `AbelFormalization/TerminalGlobalAlgebraicElimination.lean` | Global hypotheses imply the qualitative retained-variable elimination identity |
| `AbelFormalization/CentralLaurentLocalization.lean` | The central polynomial-to-Laurent map as the actual variable localization |
| `AbelFormalization/TerminalGlobalHeightReduction.lean` | Localization and coefficient-extension height transfer after terminal elimination |
| `AbelFormalization/OrdinaryHomogeneousDehomogenizationHeight.lean` | Height under `H=1` for arbitrary homogeneous ideals and the subsequent time contraction |
| `AbelFormalization/WeightedGroupEvaluation.lean` | Actual least lexicographic initial generators give homogeneous group-algebra image ideals |
| `AbelFormalization/CentralLaurentContraction.lean` | Actual preliminary translation, Laurent inversion, rescaling, contraction, and height inequality |
| `AbelFormalization/CentralIdealConstruction.lean` | Full algebraic central ideal construction and height inequality |
| `AbelFormalization/CentralPolynomialEquiv.lean` | Signed-Stirling block automorphism, time translation, and height transport |
| `AbelFormalization/SeparatedDenominatorStep.lean` | Fixed terminal localization identities and a concrete one-cluster quantitative backward step |
| `AbelFormalization/SeparatedFiniteRealJetTrace.lean` | Balanced scale hypotheses and finite composition of real-jet cluster backward steps |
| `AbelFormalization/RestrictedRankEliminationTraceBoundary.lean` | Actual rank-elimination germs, representatives, nonempty real-jet certificate, restricted-tail vanishing, and terminal polynomial seed |
| `AbelFormalization/PaperRankClusterCurrying.lean` | Canonical cluster symbol split, polynomial currying/evaluation, rank-generator span transport, and terminal certificate |
| `AbelFormalization/RestrictedHermiteJetBlockification.lean` | Explicit Hermite block polynomials, selected Abel-jet evaluation, germ currying, compact uniform offset bound, and span transport |
| `AbelFormalization/RestrictedRankHermiteClusterRepresentatives.lean` | Pointwise analytic representatives commute with Hermite cluster blockification at the level of polynomial-valued germs |
| `AbelFormalization/InversePowerLowerBoundNonvanishing.lean` | Nonvacuous contradiction between inverse-power lower bounds and common equation zeros |
| `AbelFormalization/RestrictedBaseZeroCase.lean` | Direct analytic-germ proof of `P(0,0)` and the complete base row `P(0,q)` |
| `AbelFormalization/RestrictedAllRepresentativesDiverge.lean` | Lower-count finiteness removes the bounded representative branch |
| `AbelFormalization/RestrictedRepresentativeClusters.lean` | One subsequence with fixed order and bounded-or-divergent pairwise gaps |
| `AbelFormalization/RestrictedOrderedClusterPartition.lean` | Canonical ordered equivalence classes, uniform width, endpoints, and divergent gaps |
| `AbelFormalization/RestrictedAllUnboundedClusterSetup.lean` | End-to-end infinite-sequence setup for the outer induction |
| `AbelFormalization/RestrictedUnboundedPairSelection.lean` | Fixed cluster, pair, nearest integer, and logarithmic displacement limit |
| `AbelFormalization/RestrictedPairMergeCoordinates.lean` | Smooth injective pair-merge coordinate map and regular-zero transport |
| `AbelFormalization/RestrictedPairMergeSequenceTransport.lean` | Pullback sequence, enlarged box/domain convergence, and retained divergence |
| `AbelFormalization/RestrictedPairMergeExpressionPullback.lean` | Fixed coordinate tower, old-tower pullback, and exceptional Abel-jet split |
| `AbelFormalization/IteratedAbelDerivativeSubstitution.lean` | Positive common denominators and cleared numerators for derivatives through arbitrary fixed Abel iterates |
| `AbelFormalization/FiniteCommonDenominator.lean` | Positive product common denominator and division-free cleared numerators for finite rational data |
| `AbelFormalization/MvPolynomialDenominatorClearing.lean` | Degree-bounded denominator clearing for multivariable polynomial evaluation |
| `AbelFormalization/FiniteCommonDenominatorPolynomial.lean` | Common-denominator clearing for finite multivariable polynomial families |
| `AbelFormalization/RestrictedAllUnboundedPairBranch.lean` | End-to-end fixed-pair selection in the pointwise near-integer branch |
| `AbelFormalization/RestrictedAllUnboundedBranchDichotomy.lean` | Infinite separated-set versus strict near-integer subsequence dichotomy |
| `AbelFormalization/RestrictedAllUnboundedBranchSetupDichotomy.lean` | All-unbounded cluster setup with the separated/pair alternative and retained sequence data |
| `AbelFormalization/RestrictedAllUnboundedSeparatedPairElimination.lean` | Separated lower-bound contradiction forcing the fixed pair branch |
| `AbelFormalization/RestrictedAllUnboundedPairPullbackSequence.lean` | Concrete `q + 2` to `q + 1` pullback sequence and eventual merged-system regular zeros |
| `AbelFormalization/RestrictedPairMergeExceptionalJetGraphLift.lean` | Finite exceptional-offset graphs, iterate towers, and denominator-cleared jet identities |
| `AbelFormalization/RestrictedPairMergeExceptionalJetVerticalDerivative.lean` | Positive diagonal graph Jacobian and simultaneous regular-zero graph lift |
| `AbelFormalization/RestrictedPairMergeExceptionalCommonTower.lean` | One finite tower for all exceptional graph equations and derivative data |
| `AbelFormalization/RestrictedPairMergeExceptionalGraphSequence.lean` | Injective lower-count flat graph sequence with compact limit and regular zeros |
| `AbelFormalization/RestrictedPairMergeExceptionalFlatSystem.lean` | Concatenated transformed/graph equation family, output equivalence, regular-zero transfer, and tower membership |
| `AbelFormalization/RestrictedPairMergeCompressedCoordinates.lean` | Canonical compressed exceptional coordinates and exact denominator-cleared transformed-row identities |
| `AbelFormalization/RestrictedPairMergeCompressedSystemTower.lean` | Finite support compression and one terminal tower for every cleared transformed and graph row |
| `AbelFormalization/RestrictedPairMergeDenominatorClearedRegularZero.lean` | Common Abel-family domain, differentiability, positive denominator scaling, and regular-zero transport on the exceptional graph |
| `AbelFormalization/RestrictedPairMergeAugmentedRegularZero.lean` | Full cleared augmented graph system and exact regular-zero equivalence with the lower-count pullback |
| `AbelFormalization/RestrictedPairMergeLowerCountContradiction.lean` | Lower representative-count finiteness rules out the complete all-unbounded pair-merge branch |
| `AbelFormalization/RestrictedAllUnboundedSeparatedSetup.lean` | Eliminates the pair alternative and returns an infinite simultaneous-separation set from lower-count finiteness |
| `AbelFormalization/SeparatedRingHomRealJetStep.lean` | One-cluster real-jet and localization propagation with polynomially bounded sequence-valued coefficient-ring evaluation |
| `AbelFormalization/RestrictedRankHermiteCurriedRepresentatives.lean` | Simultaneous analytic representatives after Hermite blockification and active/coefficient currying, with support control and eventual agreement with the original rank representatives |
| `AbelFormalization/CommonStripHermiteAnalytic.lean` | Joint analyticity of the common-strip Hermite coefficient family |
| `AbelFormalization/CommonStripHermiteRealAnalytic.lean` | Real-analytic coefficient representatives on restricted boxes |
| `AbelFormalization/CommonStripAbelHermiteFamily.lean` | Common-strip Abel Hermite family and its analytic/remainder interfaces |
| `AbelFormalization/PaperRankHermiteCount.lean` | Arithmetic bridge between full Hermite coefficient, positive-derivative, and higher counts |
| `AbelFormalization/PaperRankFullHermiteValue.lean` | Full Hermite coordinate value, analyticity, and complete smoothness on the projected domain |
| `AbelFormalization/HermiteBeforeRankEquation.lean` | Exact full-Hermite evaluation/equation bridge and the corrected rank-elimination height wrapper |
| `AbelFormalization/AnalyticPolynomialEvaluationBounds.lean` | Polynomial growth of evaluations of point-dependent polynomials with fixed support and analytic scalar coefficients, including the curried coefficient-ring form |
| `AbelFormalization/SeparatedDependentCoefficientwiseTrace.lean` | Finite backward real-jet/localization trace with stage-dependent cluster sizes, coefficient rings, and coefficientwise evaluations |
| `AbelFormalization/OrderedClusterPrefixBlocks.lean` | Canonical prefix block types and active-plus-smaller-cluster equivalences for largest-to-smallest ordered-cluster recursion |
| `AbelFormalization/OrderedClusterPrefixCurrying.lean` | Reindexing and currying equivalence from each ordered-cluster prefix ring to the active cluster over the exact smaller-prefix coefficient ring |
| `AbelFormalization/OrderedClusterPrefixAlgebraicStep.lean` | Canonical one-cluster algebraic reduction on prefix rings, with exact currying height preservation and height loss |
| `AbelFormalization/PaperRankFlatHermiteReindexing.lean` | Algebra equivalence between a full flat Hermite retained-rank ring and the top ordered-cluster prefix ring |
| `AbelFormalization/OrderedClusterAlgebraicDescent.lean` | Coherent largest-to-smallest chain of ordered-cluster certificates and accumulated height preservation down to the zero-prefix ring |
| `AbelFormalization/OrderedClusterPrefixAnalyticDimension.lean` | Stage-dependent Krull-dimension bounds and recursive descent specialization over real-analytic germs |
| `AbelFormalization/OrderedClusterPrefixZeroRing.lean` | Canonical identification of the empty zero-prefix polynomial ring with its analytic-germ coefficient ring |
| `AbelFormalization/OrderedClusterBottomPolynomial.lean` | Height transfer at the final cluster and extraction of a nonzero real polynomial in one retained time variable |
| `AbelFormalization/ImplicitRegularZeroGraphLift.lean` | Local scalar implicit graph equations preserve regular zeros |
| `AbelFormalization/FiniteImplicitRegularZeroGraphLift.lean` | Simultaneous finite-dimensional implicit graph regularity theorem |
| `AbelFormalization/FiniteExplicitRegularZeroGraphLift.lean` | Explicit vector graph equations `z - ζ(x)` have identity vertical derivative and preserve regular zeros |
| `AbelFormalization/RestrictedFixedIterateShiftGraph.lean` | Allowed shift equation, positive vertical derivative, and graph regularity |
| `AbelFormalization/UnaryPieceDecomposition.lean` | Exact finite point/open-interval decompositions and Boolean closure |
| `AbelFormalization/UnaryNearZeroInterval.lean` | A positive unary set with finite point/interval/ray pieces accumulating at zero contains an entire near-zero positive interval; radial/minor range membership and WS5 finiteness are separate |
| `AbelFormalization/WilkieFixedMinorConnectedInterval.lean` | Preconnected finite-projection topology and a squared fixed-Jacobian-minor interval from explicit zero/nonzero witnesses on one fiber piece; both the finite-image arbitrary-minor branch and the later vertical-minor branch now supply their witnesses under their own hypotheses |
| `AbelFormalization/WilkieCompactOpenImageObstruction.lean` | A nonempty compact component cannot have an open image in a connected noncompact coordinate space; a conditional fixed-minor zero interface for complementary-coordinate charts |
| `AbelFormalization/WilkieRegularSliceLinearBridge.lean` | Augmented derivative surjectivity transfers to a coordinate-slice derivative once the coordinate insertion has the stated kernel-range identity; Wilkie 2.8's finite exceptional values remain open |
| `AbelFormalization/WilkieVerticalMinorProjectionFork.lean` | A bounded restricted-fiber component has relatively closed image; explicit local projected neighborhoods make that image relatively open, hence equal to a connected target |
| `AbelFormalization/WilkieVerticalMinorLocalProjection.lean` | For an open visible target, an invertible strict derivative of `(visible coordinates, F)` supplies the local projected neighborhoods and completes the conditional component-projection fork |
| `AbelFormalization/WilkieVerticalMinorDerivativeBridge.lean` | A nonzero fixed hidden-column minor makes the square-map derivative invertible; a bounded regular fiber component with that minor nonzero throughout projects onto the connected open target |
| `AbelFormalization/WilkieVerticalMinorMissingProjectionInterval.lean` | A missed target point forces a zero of the same vertical minor in the bounded regular restricted component; when it is nonzero at the base point, its square realizes a positive initial interval |
| `AbelFormalization/WilkieFiniteVisibleProjectionFork.lean` | Finite visible image makes the full regular-fiber component compact, and a complementary-coordinate IFT chart condition yields a same-minor zero and squared interval |
| `AbelFormalization/WilkieArbitraryMinorDerivativeBridge.lean` | Every nonzero maximal Jacobian column minor gives the required complementary-coordinate inverse-function chart by extending its columns to a permutation |
| `AbelFormalization/WilkieFiniteVisibleProjectionCase.lean` | Unconditional Wilkie 2.9 Case 1: finite visible image of a bounded regular fiber yields a fixed squared-minor initial interval for an arbitrary chosen maximal minor at the base point |
| `AbelFormalization/Wilkie28ExceptionalMathlibOnly.lean` | Theorem 2.8 derivative contradiction: a differentiable selected singular-witness curve on a regular fiber would make the augmented derivative surjective; finiteness follows from explicit unary-tameness and smooth-selection premises |
| `AbelFormalization/Wilkie28ExceptionalWS5Reduction.lean` | WS5 unary-piece decomposition supplies the tameness premise for a weak-family exceptional set; exceptional-set membership and smooth singular-witness selection remain explicit |
| `AbelFormalization/Wilkie28ExceptionalMembership.lean` | The exceptional unary set of Wilkie 2.8 is a rank-one projection of a literal zero set: an augmented Jacobian sum-of-squares residual belongs to the geometric derivative-closed family, and its zero set has exactly the singular-value projection |
| `AbelFormalization/Wilkie28WeakSelectionIncidence.lean` | The singular parameter–witness incidence is a closed literal zero set in the weak-family closure, and its visible projection is exactly the exceptional unary slice; Wilkie 2.3 selection is still separate |
| `AbelFormalization/Wilkie28ExceptionalFamilyFinite.lean` | Combines proved family membership with actual WS5 unary decomposition to give finite exceptional values on a regular fiber from the explicit smooth singular-witness selection premise |
| `AbelFormalization/WilkieCase2CombinatorialDescent.lean` | Case 2 finite-exception choice and arity induction: an infinite visible image yields an attained coordinate value outside the finite exceptional set; geometric slice construction and minor-certificate transport remain explicit interfaces |
| `AbelFormalization/WilkieCase2SliceRegularity.lean` | A good attained coordinate value yields an augmented surjective derivative at every fiber point; explicit visible-coordinate insertion gives a nonempty bounded regular ball slice with open inserted domain |
| `AbelFormalization/WilkieCase2MinorTransport.lean` | Row and column reordering preserve squared maximal minors; a slice squared-minor initial interval lifts into the original restricted fiber from the explicit Jacobian chain identity and fiber inclusion |
| `AbelFormalization/WilkieCase2FlatJacobianInsertion.lean` | The affine flat coordinate insertion has the expected derivative and basis transport; the sliced rectangular Jacobian is exactly the original Jacobian with the fixed source column omitted |
| `AbelFormalization/WilkieCase2FlatBallMinorIntervalLift.lean` | For a literal fixed-coordinate ball slice, the interval of a chosen sliced squared minor lifts to the original ball fiber; the Jacobian identity and fiber inclusion are proved inside the theorem |
| `AbelFormalization/WilkieZeroVisibleVerticalMinor.lean` | At zero visible arity a regular square fiber map has a nonzero vertical maximal minor, proved by reindexing `Fin (0 + k)` to `Fin k` and using matrix surjectivity |
| `AbelFormalization/WilkieCase2ProductFlatEquiv.lean` | The product visible/hidden ball slice commutes with one-coordinate flat insertion after an explicit Nat cast; ball preimages and sliced derivative surjectivity transport through the concatenation equivalence |
| `AbelFormalization/WilkieCase2VisibleCylinderChoice.lean` | Source-shaped visible-cylinder slice: a good attained coordinate value yields a nonempty bounded regular lower fiber over an open sliced visible target; WS5 and smooth selection select such a value from an infinite visible image |
| `AbelFormalization/WilkieCase2CylinderMinorIntervalLift.lean` | A selected squared maximal-minor interval on the literal sliced visible-cylinder fiber lifts to the original restricted fiber; the coordinate-arity cast, Jacobian identity, and fiber inclusion are proved internally |
| `AbelFormalization/WilkieCase2HiddenMinorCast.lean` | The fixed hidden-column minor agrees exactly under casted visible-coordinate insertion; nonzeroness transfers pointwise from a lower slice to the original flat map |
| `AbelFormalization/WilkieCase2FlatCylinderSliceBridge.lean` | The exact flat restricted fiber transports through visible/hidden concatenation to the product cylinder; its selected slice is open, bounded, nonempty, regular at good values, and inserts into the original fiber |
| `AbelFormalization/WilkieCase2RecursiveFixedMinorAlternative.lean` | Conditional full Case 2 arity descent: either one selected squared minor contains an initial interval on the restricted fiber or the fixed hidden-column minor is nonzero; a missed visible point then yields the final projection-or-interval fork |
| `AbelFormalization/WilkieCase2ExceptionalProductFlatTransport.lean` | Precomposition by a continuous linear equivalence preserves augmented-derivative exceptional values; the product visible-coordinate exceptional set equals the flat coordinate-pivot version |
| `AbelFormalization/WilkieCase2ReachableRecursiveAlternative.lean` | The Case 2 two-certificate arity recursion now restricts exceptional-set membership and smooth selection to maps reachable by affine visible-coordinate slices of one original map |
| `AbelFormalization/WilkieCase2FlatAffineFamilyClosure.lean` | The casted flat coordinate insertion is an affine map, so geometric-family tuple membership is preserved componentwise under every recursive Case 2 slice |
| `AbelFormalization/WilkieCase2ReachableExceptionalMembership.lean` | Reachable flat tuple membership is invariant under Case 2 slicing; for Abel-family tuples this discharges the exceptional unary Charbonnel-membership premise at every recursive stage |
| `AbelFormalization/WilkieCase2AbelConditional.lean` | For one Abel-family tuple and uniform fiber finiteness, the full Case 2 projection-or-selected-minor interval theorem follows with smooth singular-witness selection as its sole recursive source premise |
| `AbelFormalization/Wilkie28WeakSelectionCompactBaireReduction.lean` | If the exceptional unary set has interior, Baire category finds a compact singular-incidence truncation whose projected parameter set still has interior and remains in the Charbonnel closure; local family-member graph extraction remains open |
| `AbelFormalization/Wilkie28WeakSelectionCompactExtraction.lean` | A local weak-family graph inside the compact incidence truncation yields the exact weak singular-witness selector, including nonsurjectivity via maximal Jacobian minors; Wilkie 2.3 is reduced to compact local graph extraction |
| `AbelFormalization/Wilkie28MaxwellWeakSelection.lean` | Applies the proved Maxwell continuous weak-selection theorem on a polynomial-sign ball inside Wilkie's exceptional slice, transports the selected graph from `RealEuclidean 1` to `ℝ`, and discharges Wilkie 2.3 directly from WS5 plus Charbonnel Theorem 2.1 |
| `AbelFormalization/MaxwellCompactComponentMembership.lean` | Every connected component of a compact WS5 member is itself a weak-family member: finite component clopens are isolated by finite unions of polynomial-sign sup-norm balls, using only WS1--WS2 after WS5 supplies finiteness. Independently of finiteness, every component carrier of a compact Hausdorff set is compact. |
| `AbelFormalization/Wilkie28WeakSelectionCompactComponentReduction.lean` | A compact incidence with large projection has one connected family component whose projection still has interior; injective projection, a fixed hidden section with interior, or a polynomial-sign cut producing an injective branch each gives an explicit local family-member graph |
| `AbelFormalization/MaxwellCompactInjectiveSelectorContinuity.lean` | Projection from a compact one-parameter relation with injective visible projection is a homeomorphism onto its image, so its canonical selector, and every contained selected graph, is continuous |
| `AbelFormalization/MaxwellImplicitSelectorSmoothness.lean` | A continuous selector satisfying a smooth square implicit system with invertible hidden derivative agrees locally with mathlib's implicit function and is differentiable |
| `AbelFormalization/MaxwellWeakSelection.lean` | Source-faithful Lemma 2.3.1 assembly: increasing enumeration of finite scalar fibers, an explicit polynomial-sign selector incidence, scalar interior and empty-interior branches, vector coordinate induction, and continuity after removing coordinate discontinuity loci |
| `AbelFormalization/MaxwellLocalFiberCardinality.lean` | Proves Maxwell--Figueiredo Lemma 2.2.1 from WS5 and Theorem 2.1: a Fubini/component argument bounds fiber cardinality, and a maximal cardinality locus yields a smaller open family member with one fixed positive finite fiber size |
| `AbelFormalization/WilkieSection4FiberCardinalityLoci.lean` | Formalizes Wilkie's page-418 loci `A_i` by strictly ordered scalar fibre tuples, proves their extended-cardinality semantics, antitonicity and exact-cardinality strata, and transports every locus into the Charbonnel closure without complement closure; a bare weak family still needs an explicit existential-projection closure premise for the same-family statement |
| `AbelFormalization/MaxwellScalarFiberExtrema.lean` | Reflects scalar fibers to construct a family-member maximum selector alongside the existing minimum selector, proves their endpoint order properties, and supplies open-base approximation of closure-graph values |
| `AbelFormalization/MaxwellScalarDiscontinuity.lean` | Formalizes Lemma 2.2.2's closure-defined discontinuity locus, its Charbonnel membership, the full bounded/unbounded sequence dichotomy, and the terminal uniform-escape contradiction |
| `AbelFormalization/MaxwellScalarDiscontinuityEscape.lean` | Completes Lemma 2.2.2 by bounded-value and positive-gap exhaustions, reciprocal-infinity exclusion, exact finite closure fibers, the up/down extremal-selector split, and finite Archimedean escape; exports discontinuity control and continuous weak selection from WS5 plus Theorem 2.1 |
| `AbelFormalization/MaxwellDifferenceQuotientEmptyInterior.lean` | A directional difference-quotient relation of a scalar pseudofunction is again a pseudofunction and has empty interior; quotient multivaluedness is controlled by two null endpoint cylinders, eliminating the former empty-interior premise |
| `AbelFormalization/MaxwellC1DifferenceQuotientTrace.lean` | Completes Figueiredo Lemma 2.3.9: strict differentiability makes every finite zero-step slope equal the coordinate derivative, continuous Fréchet derivatives give the exact trace representation on an open domain, and the base-restricted trace equals the derivative graph |
| `AbelFormalization/MaxwellPositiveZeroTraceSmallness.lean` | Positive/reflected-negative trace membership and nullity, exact quotient-coordinate reindexing, one-sided trace closure, and Fubini nullity of finite-slope multivalued loci from the source interval-filling premise |
| `AbelFormalization/MaxwellSlopeClusterSmallness.lean` | Exact finite and infinite one-sided slope clusters, cross-side disagreement, affine-chord/IVT and translated-quotient contradictions, and the three-hard-case reduction of nondifferentiability; the remaining analytic extraction mechanisms are explicit interfaces |
| `AbelFormalization/MaxwellFirstOrderAssembly.lean` | Packages scalar first-order regularization and arbitrary-order/vector induction; the analytic core is reduced to slope-bad-locus nullity and differentiability of the chosen representative outside the common closed exceptional locus |
| `AbelFormalization/MaxwellFirstOrderAnalyticAdapter.lean` | Connects the source-level one-sided IVT, affine-chord, translated-separation, and residual cluster mechanisms to the first-order analytic core; quotient empty interior and slope-bad-locus nullity are derived rather than assumed |
| `AbelFormalization/MaxwellOneSidedSlopeIVT.lean` | Proves the finite and infinite one-sided IVT mechanism from a continuous scalar representative: exact trace sequences, convex shrinking step cores, finite interval filling, reciprocal infinity witnesses, divergent ordinary slopes, and the core straddling theorem |
| `AbelFormalization/MaxwellOneSidedExtendedIVT.lean` | Completes the exact four-case extended IVT of Figueiredo--Maxwell Lemma 2.3.3 without global finite-anchor assumptions: finite trace points supply their own comparison sequences, opposite infinities supply two divergent sequences, and restricted/unrestricted interval-filling packages retain only the necessary base-domain control |
| `AbelFormalization/MaxwellOneSidedClusterCoverage.lean` | Proves compactified one-sided slope-cluster existence at every interior pseudofunction base point: canonical shrinking steps and the bounded/unbounded real-sequence trichotomy yield a finite, positive-infinite, or negative-infinite source-defined cluster on each side |
| `AbelFormalization/MaxwellOneSidedBoundedClusterExtraction.lean` | Extracts cutoff-preserving bounded slope subsequences and converts their limits into finite extended-slope fiber values, supporting the complete finite/±∞ disagreement analysis |
| `AbelFormalization/MaxwellResidualOneSidedClusterData.lean` | Derives the residual finite-cluster compatibility and cluster classification used to cover nondifferentiability by the one-sided and hard slope loci |
| `AbelFormalization/MaxwellSlopeBadDomainClosure.lean` | Proves every coordinate slope-bad point lies in the closure of the original pseudofunction domain, enabling localization back into that open domain |
| `AbelFormalization/MaxwellSlopeBadLocalAssembly.lean` | Localizes the slope-bad cover and assembles the one-sided and hard cases without a global base-containment hypothesis |
| `AbelFormalization/MaxwellChosenContinuityBridge.lean` | Constructs the canonical selector's closed continuity obstruction and proves continuity on its complement from the scalar discontinuity theorem |
| `AbelFormalization/MaxwellChosenInfinitySmallness.lean` | Derives smallness of the selector's one-sided infinity obstruction and the regular derivative domain used by the corrected first-order assembly |
| `AbelFormalization/MaxwellLocalizedOneSidedIVT.lean` | Localizes actual quotient sources to the open uniqueness/continuity domain, proves all finite and infinite one-sided extended IVT cases there, and derives smallness of both extended-multivalued loci with no IVT premise |
| `AbelFormalization/MaxwellWS5AffineChordExtraction.lean` | Turns genuine fixed-base same-sign infinite quotient limits into the affine-chord obstruction using WS5 and Theorem 2.1 |
| `AbelFormalization/MaxwellTranslatedSeparationExtraction.lean` | Proves local quotient bounds for singleton finite/±∞ fibers, handles all nine disagreeing-fiber cases, and derives translated separation after avoiding the two null multivalued loci |
| `AbelFormalization/MaxwellSameInfinityDirectLimits.lean` | Converts source-defined moving-base infinity witnesses into fixed-base direct limits off the small multivalued loci, then derives both affine-chord mechanisms and full smallness of the equal-infinity loci |
| `AbelFormalization/MaxwellChosenDifferentiability.lean` | Replaces the former chosen Fréchet-differentiability premise by coordinate line derivatives, proves continuity of the selected coordinate derivatives from closed trace graphs, and derives strict Fréchet differentiability by finite-dimensional induction |
| `AbelFormalization/MaxwellCorrectedFirstOrderAssembly.lean` | Uses the honest open derivative-regular domain and the derived continuity, cluster, IVT, and infinity controls to produce the scalar first-order package from the hard cases |
| `AbelFormalization/MaxwellAutomaticFirstOrder.lean` | Constructs the remaining hard cases automatically, then proves the scalar first-order package, every finite scalar order, and Maxwell finite-output almost-everywhere smoothness from the four Charbonnel interfaces alone |
| `AbelFormalization/MaxwellSection5Smoothness.lean` | Extracts Charbonnel Theorems 2.1 and 2.2 from either the finite-decomposition induction or the source-shaped meagre-selection/analytic-step route, then feeds them into the automatic Maxwell theorem |
| `AbelFormalization/Wilkie28WeakSelectionFiniteClosedCover.lean` | A finite closed polynomial-sign cover by injective projection pieces contains a piece with projected interior; it yields a continuous local family graph, and regular smooth implicit systems on the pieces upgrade the selected graph to pointwise differentiability and the combined smooth singular-witness selection interface |
| `AbelFormalization/WilkieCase2AbelMaxwellReduction.lean` | The full Abel Case 2 projection-or-minor theorem discharges Maxwell 2.3 directly on every reachable affine slice; alternate compact-component, injective-branch, and finite-cover endpoints remain available, and product/flat selection transport is proved |
| `AbelFormalization/WilkieCase2AutomaticMaxwell.lean` | Derives Maxwell 2.4 internally and exposes Abel Case 2 from either Theorems 2.1/2.2, the finite-decomposition section 5 inputs, or the source-shaped meagre-selection plus analytic successor step |
| `AbelFormalization/Wilkie28SelectionComposition.lean` | A weak-family selected singular-witness graph plus a closed empty-interior nonsmooth set yields a differentiable singular-witness curve on a nonempty open domain; the direct Maxwell bridge supplies the weak graph, leaving Maxwell 2.4 as the smoothness input |
| `AbelFormalization/SmoothGeometricFamily.lean` | Geometric/smooth/fiber-finiteness interfaces and local regular-fiber characterization |
| `AbelFormalization/AbelSmoothGenerators.lean` | Global analyticity and affine-coordinate derivative identities for every `C_r` |
| `AbelFormalization/AbelGeometricFamily.lean` | Concrete finite numerator syntax and nowhere-zero quotient family, with geometric, smooth, derivative-closure, and generator proofs |
| `AbelFormalization/AbelNumeratorPolynomialPresentation.lean` | Explicit finite Abel-jet list and multivariable-polynomial presentation for every numerator expression |
| `AbelFormalization/AbelNumeratorSystemPresentation.lean` | Canonical sigma enumeration combining all rowwise numerator presentations into one shared finite generator list |
| `AbelFormalization/AbelNumeratorRestrictedGraphSystem.lean` | Restricted-base lifted numerator rows, argument graph equations, membership proofs, and exact graph evaluation |
| `AbelFormalization/AbelGeometricRegularZero.lean` | Simultaneous quotient presentations, denominator-cleared fiber systems, regular-zero equivalence, and reduction of 0-regularity to numerator finiteness |
| `AbelFormalization/AbelNumeratorRestrictedRegularZero.lean` | Explicit graph-lift regular-zero equivalence and deduction of concrete numerator finiteness from uniform restricted-base finiteness |
| `AbelFormalization/SmoothRegularZeroBridge.lean` | Equality of smooth square regular fibers with `regularZeroSet` and the 0-regularity bridge |
| `AbelFormalization/ProjectedZeroFamily.lean` | Projected-zero lattice/product/linear-image closure, closed lifts, and graph representation |
| `AbelFormalization/ProjectedZeroPolynomialSigns.lean` | Existential zero equations and Boolean closure for finite polynomial-sign normal forms |
| `AbelFormalization/ProjectedFiberComponents.lean` | Connected-component inequalities and uniform bounds for product and flat-coordinate projected fibers |
| `AbelFormalization/ProjectedZeroMatrixSections.lean` | The flat matrix-parameter map `H_f`, exact affine-section fiber identity, and uniform connected-component bound |
| `AbelFormalization/HermiteRankAllClusterBackwardContradiction.lean` | All-cluster backward propagation from the bottom terminal bound to the contradictory top bound |
| `AbelFormalization/RestrictedBaseSeparatedContradictionInduction.lean` | Normalized separated contradiction assembled into the outer restricted-base induction |
| `AbelFormalization/HermiteRankCanonicalSeparatedContradiction.lean` | Canonical diagonal specialization, complete regular-zero theorem, numerator finiteness, and concrete Abel-family 0-regularity |
| `AbelFormalization/LionRegularCodimensionOne.lean` | Finite connected components for closed regular codimension-one loci from 0-regularity |
| `AbelFormalization/LionUniformRegularFiberEncoding.lean` | Honest uniform square regular-fiber bound, parameter-recording derivative, and exact transfer to uniform fiber finiteness |
| `AbelFormalization/LionUniformPreimageReduction.lean` | Khovanskii upper numbers, Gabrielov's uniform upper-number property, and exact equivalences with uniform nondegenerate-preimage and regular-fiber bounds |
| `AbelFormalization/LionUpperNumbersCenterControl.lean` | Local inverse branches, Sard-null critical values, and Khovanskii's center-control theorem reducing Lion's step to Gabrielov uniformity |
| `AbelFormalization/LionUniformFiberNarrowing.lean` | Earlier separation of Lion's uniform upper-number input from fixed-square component encodings; the later canonical Lagrange reduction constructs those encodings, leaving uniform upper numbers and canonical finite regular Lagrange covers |
| `AbelFormalization/LionNestedFiberComponentBounds.lean` | Proves that one finite component bound survives decreasing intersections of compact sets, increasing unions, and Lion's combined two-stage limit |
| `AbelFormalization/LionCarpetCompactification.lean` | Formalizes the compact approximations cut out by a carpet and the topological compact-limit conclusion of Lion's Lemma 6 |
| `AbelFormalization/LionStandardCarpet.lean` | Constructs `1/(1+‖x‖²)` as a positive proper carpet on Euclidean space and proves it belongs to every geometric function family |
| `AbelFormalization/LionCompactificationFiber.lean` | Identifies each compact approximation with the projection of a fiber of Lion's enlarged map and transfers component bounds through that projection |
| `AbelFormalization/LionFullParameterSelection.lean` | Selects Lion's nested generic parameters from the fiberwise-full measure condition and proves that a generic component bound for the enlarged map bounds every fiber of the original map |
| `AbelFormalization/LionFlatCompactification.lean` | Writes Lion's enlarged map in flat `RealEuclidean` coordinates, proves exact compatibility with the product form, and proves all coordinates remain in the geometric family |
| `AbelFormalization/LionFlatCompactificationFiber.lean` | Identifies visible projections of flat enlarged-map fibers with Lion's compact approximations, keeps full-parameter selection in the correct Euclidean L² metric, and derives family UFF from full generic enlarged-map bounds |
| `AbelFormalization/LionCarpetedLeaf.lean` | Encodes Lion's associated carpeted-leaf triplet, proves the exact regular-locus carpet of Lemma 3, and proves every zero-dimensional leaf finite from family smoothness and 0-regularity |
| `AbelFormalization/LionCarpetedLeafFiber.lean` | Restricts a carpet to leaf fibers and proves that each connected component contains a carpet maximum |
| `AbelFormalization/LionLemma4CriticalCarpet.lean` | Constructs Lion's radial carpet and the exact parameter-dependent critical carpet on the regular leaf, with family membership and compact-superlevel proofs |
| `AbelFormalization/LionRadialParameterTransversality.lean` | Computes the actual radial log-gradient derivative in the center/height parameters and proves its surjectivity, including after every surjective tangent or normal quotient |
| `AbelFormalization/LionLemma4CriticalLocus.lean` | Identifies Lion's critical form with maximal Jacobian coefficients, proves its common zero locus is the augmented rank-defect locus, and shows every regular fiber component meets its trace |
| `AbelFormalization/LionLemma4RegularMinorCover.lean` | Builds the finite family of codimension `n-p` regular zero-section leaves from critical-form coefficients and reduces their cover of the critical trace to Lion's exact generic rank-selection consequence |
| `AbelFormalization/LionLemma4SectionAssembly.lean` | Takes the rank-selection and regular-target conclusions of the two Sard steps and proves that the final codimension `n-p` section leaves meet every connected component of the original regular fiber |
| `AbelFormalization/LionLeafMorseSard.lean` | Transfers Euclidean rectangular Morse--Sard through implicit charts to arbitrary carpeted leaves and proves that Lion's simultaneous original-leaf/section-leaf good-target set has null complement |
| `AbelFormalization/LionLemma4Counting.lean` | Feeds the actual finite section-leaf family into the Theorem 7' counting lemma, so recursive bounds for the section fibers sum to a component bound for the original good fiber |
| `AbelFormalization/LionRegularZeroSectionLeaf.lean` | Packages the regular zero-section leaf cut out by `(f,h)`, with the exact carrier and codimension used for the finite coefficient cover in Lemma 4 |
| `AbelFormalization/LionRolleFiberReduction.lean` | Specializes the normalized-cofactor arc machinery to leaf equations, derives augmented rank from submersivity on the leaf, and proves the quantitative full-fiber versus partial-fiber component inequality of Lion's Lemma 5 |
| `AbelFormalization/LionTheorem7RolleStep.lean` | Generalizes the Rolle inequality across arithmetic ambient-dimension equalities, identifies its partial and full sets with carpeted-leaf fibers, and proves the exact equal-dimensional `p ↦ p-1` component bound used by Theorem 7' |
| `AbelFormalization/LionTheorem7Induction.lean` | Formalizes the four source cases of the dimension-plus-target induction, finite Gabrielov-section sum estimates, Rolle composition, and the terminal finite-family bound for zero-dimensional carpeted leaves |
| `AbelFormalization/LionTheorem7FlatCompactificationBridge.lean` | Converts a full-parameter Theorem 7' output of finite terminal leaves for the standard flat enlarged map into a natural-number generic bound and then uniform fiber finiteness |
| `AbelFormalization/LionTheorem7GenericBound.lean` | Performs Lion's numerical Theorem 7' induction on leaf dimension plus target dimension, using the actual Lemma 4 sections in the high-dimensional case and the actual Lemma 5 Rolle inequality in the equal-dimensional case |
| `AbelFormalization/LionLowDimensionalImageNullity.lean` | Proves the low-dimensional branch of Theorem 7' by covering a carpeted leaf with countably many implicit charts and applying mathlib's Hausdorff-dimension nullity theorem to each chart image |
| `AbelFormalization/LionLemma4RadialSelectionTheorem.lean` | Uses rectangular parametric Sard and the logarithmic Lagrange submersion to prove the radial-selection premise of Lemma 4 from the standing geometric, smoothness, and derivative-closure hypotheses |
| `AbelFormalization/LionGenericBoundFlatBridge.lean` | Pulls the conull numerical Theorem 7' target set back through the flat compactification coordinates, applies Fubini to obtain Lion's nested full parameter set, and feeds it to Lemma 6 to obtain uniform fiber finiteness |
| `AbelFormalization/LionUniformFiberFinitenessTheorem.lean` | Closes the source-faithful Lion chain: the four standing family hypotheses imply uniform fiber finiteness with no residual premise, and every `IsAbel A` satisfies the result for `abelGeometricFamily A` |
| `AbelFormalization/MorseSardNonflatHypersurface.lean` | Decomposes a rank-zero source into its deepest flat locus and finitely many nonflat jet layers, each contained in a regular scalar hypersurface |
| `AbelFormalization/MorseSardRankNormalization.lean` | Normalizes an exact-rank point by an arbitrary-minor inverse chart so the residual slice has derivative zero |
| `AbelFormalization/SmoothFamilyRectangularJacobianMinors.lean` | Rectangular Jacobian minors and exact finite-dimensional rank certificates |
| `AbelFormalization/SmoothFamilyRectangularRankLocus.lean` | Rank loci characterized by vanishing and nonvanishing rectangular minors |
| `AbelFormalization/SmoothFamilyJacobianRankStrata.lean` | Finite row/column minor witnesses and selected-output derivative equivalences |
| `AbelFormalization/SmoothFamilyRankStratumLocalFiber.lean` | Selected-minor implicit charts with exact-rank local certificates |
| `AbelFormalization/SmoothFamilyConstantRankLocalFiber.lean` | Local equality of full and selected-output fibers under a neighborhood rank bound, including rank zero |
| `AbelFormalization/SmoothFamilyMaximalRankLocalFiber.lean` | Nonzero-minor extraction and local selected-output fiber equivalence at globally maximal derivative rank |
| `AbelFormalization/SmoothFamilyMaximalRankFiberFiniteness.lean` | Reciprocal-minor patches and targetwise finite connected components of globally maximal-rank fiber pieces |
| `AbelFormalization/SmoothFamilySelectedOutputClosure.lean` | Preservation of family membership under selected outputs and their translated fiber equations |
| `AbelFormalization/SmoothFamilyRankStratumFiberReduction.lean` | Targetwise and uniform finite-cover reductions through exact derivative-rank pieces |
| `AbelFormalization/CharbonnelClosureDescription.lean` | Positive-arity Charbonnel generator syntax, denotation, and exact source rank weights |
| `AbelFormalization/CharbonnelWeakStructure.lean` | Source-shaped positive-arity WS1–WS6/DC interfaces and rank-zero generator preservation |
| `AbelFormalization/CharbonnelDescriptionAlgebra.lean` | Closed-base coordinate reindexing, products, arbitrary intersections, and their sharp Charbonnel rank bounds |
| `AbelFormalization/CharbonnelSemiClosed.lean` | Servi 3.3.9: every Charbonnel carrier over a closed positive-arity weak structure has a closed Charbonnel lift with the same projection |
| `AbelFormalization/ClosedZeroSetCharbonnelBridge.lean` | Closed literal zero-set generators and rank-one Charbonnel descriptions of every projected zero set |
| `AbelFormalization/CharbonnelLinearEquivClosure.lean` | Arbitrary real-linear image closure by description induction and the resulting WS1–WS4 package |
| `AbelFormalization/CharbonnelApproximationModuli.lean` | Wilkie's recursive nested moduli, common refinements, and two-sided approximation predicates |
| `AbelFormalization/CharbonnelApproximationTrace.lean` | First-parameter halving, positive zero traces, compact limit descent, and the exact recursive conclusion of Wilkie's Lemma 3.3 |
| `AbelFormalization/CharbonnelTraceMembership.lean` | Algebraic closure and positive-zero-trace membership in the literal-zero Charbonnel closure, with the two remaining Charbonnel smallness statements isolated explicitly |
| `AbelFormalization/CharbonnelApproximationTraceSmallness.lean` | Exact `P'_n`, `Q_n`, and `P_n` predicates; Fubini, compact-truncation, Baire, finite locally closed decomposition, and induction reductions, with the analytic interfaces later narrowed by the Section 5 reduction and infinite-fibre bridge |
| `AbelFormalization/CharbonnelSection5ElementaryInputs.lean` | Polynomial-sign construction of integral sup-norm balls, closure under compact truncation, the WS5 proof of `P'_1`, and the exact Section 5 assembly interface |
| `AbelFormalization/CharbonnelClosureNullityWitnesses.lean` | Charbonnel §5.8 closed lifts, compact-fibre carrier, relative closedness, Fubini nullity, exact zero trace, and unconditional closure-nullity witnesses |
| `AbelFormalization/CharbonnelFiniteLocallyClosedReduction.lean` | Constructor induction reducing the optional finite locally closed route to its exact projection-decomposition input, plus a source-shaped Section 5 assembly from closure-interior regularity |
| `AbelFormalization/CharbonnelBoundaryApproximation.lean` | Wilkie 3.6's asymmetric closure/boundary approximation clauses, common-modulus union, and trace descent to a closed boundary carrier |
| `AbelFormalization/CharbonnelSardianConstituents.lean` | Source-shaped finite `ℓ`-Sardian constituent families, unused positive-parameter padding, and finite common-modulus refinements |
| `AbelFormalization/CharbonnelSardianEmptyInterior.lean` | Hausdorff-nullity and empty interior for exact-depth, padded, and finite common-depth Sardian constituent families |
| `AbelFormalization/CharbonnelSardianApproximationCertificate.lean` | Common-depth positive-order Sardian certificates joining projected-zero membership, empty interior, and asymmetric boundary approximation |
| `AbelFormalization/CharbonnelSardianCertificateAlgebra.lean` | Equal-hidden-depth concatenation, carrier union, indexed certificate views, and common-modulus union algebra for finite Sardian certificates |
| `AbelFormalization/CharbonnelSardianCertificatePadding.lean` | Positive-parameter padding through constituents, families, and asymmetric moduli, followed by arbitrary-hidden-depth certificate union at `max K L` |
| `AbelFormalization/CharbonnelSardianExactDepthExtension.lean` | Realize every old padded Sardian constituent as an exact common-depth constituent by setting trailing hidden-coordinate equations equal to the unused positive parameters; proves equality of carriers |
| `AbelFormalization/CharbonnelSardianRankConstructorReduction.lean` | Wilkie 3.7 target union and closure certificate constructors, zero-hidden-arity projection, and the literal-base, positive-projection, and integer-affine rank interfaces assembled by downstream proofs |
| `AbelFormalization/CharbonnelSardianLiteralZeroRadialBase.lean` | Wilkie 3.8 radial constituent with geometric-family membership, smooth equations, escape witness, and reduction of the base certificate to positive-level finite-cover moduli |
| `AbelFormalization/CharbonnelSardianLiteralZeroLevelControls.lean` | Compact small-level cutoff, finite frontier cover and segment IVT, reciprocal radial margin, and a nested modulus proving Wilkie 3.8's literal-zero base input from smoothness alone |
| `AbelFormalization/CharbonnelSardianProjectionTopology.lean` | Wilkie 3.10's topological target bridge: visible projection of the closure lies in the closure of the projection, with equal closures |
| `AbelFormalization/CharbonnelSardianProjectionConstituentAlgebra.lean` | Wilkie 3.10's finite radial or squared-Jacobian-minor Sardian constituent choices, geometric-family membership, and exact hidden-coordinate and positive-parameter shift; projection approximation remains unproved |
| `AbelFormalization/CharbonnelSardianProjectionRadialBranch.lean` | Exact reciprocal-polynomial radial branch carrier and level-dependent max-norm bound on its hidden witnesses; regular-value and approximation arguments remain open |
| `AbelFormalization/CharbonnelSardianProjectionFromBelowReduction.lean` | Wilkie 3.10 projected from-below clause from explicit old-modulus prefix, boundedness, and new-to-old section-lift premises; no from-above/regular-value theorem |
| `AbelFormalization/CharbonnelSardianProjectionPrefixSectionLift.lean` | Reindex the erased old visible coordinate as first new hidden coordinate, with `Fin.tail` old hidden data; any one radial/minor choice section lifts to its old constituent after dropping the last level |
| `AbelFormalization/CharbonnelSardianProjectionFiniteChoicePrefixLift.lean` | Extract the particular radial/minor choice from its finite carrier, and lift finite exact-depth lists while retaining an old constituent witness; mixed depths require exact-depth normalization |
| `AbelFormalization/CharbonnelSardianProjectionPaddedFamilyPrefixLift.lean` | Normalize a mixed-depth old finite Sardian family, assemble the finite projected choices at common depth, and lift every new section point into the original old-family carrier after deleting the global final level |
| `AbelFormalization/CharbonnelSardianProjectionFromBelowAssembly.lean` | Wilkie 3.10's full projected from-below clause for the normalized finite family from any old Sardian certificate and a unit successor modulus; the from-above regular-value/minor argument remains open |
| `AbelFormalization/CharbonnelSardianProjectionFromAboveLevelAlternative.lean` | Conditional Wilkie 3.10 small-level alternative: a connected radial subfiber with arbitrarily small values, or an explicit 2.9 squared-minor interval, yields finite projected-family members at every small final level; neither analytic branch premise is discharged |
| `AbelFormalization/CharbonnelSardianProjectionRadialValueImage.lean` | With visible `U` already in the literal-zero Charbonnel closure, build the fixed old-tuple fiber and reciprocal radial graph in that closure, then project to a positive scalar image; UFF supplies its WS5 unary decomposition |
| `AbelFormalization/CharbonnelSardianProjectionRadialWS5Levels.lean` | Under UFF, visible `U` closure-family membership, and radial-image accumulation at zero, WS5 and unary-piece finiteness give every small radial level and a point in the finite projected choice family |
| `AbelFormalization/CharbonnelSardianProjectionRadialFiniteCover.lean` | A finite cover localizes fixed-fiber radial accumulation to one member; when each cover member belongs to the literal-zero Charbonnel closure, the maintained UFF/WS5 theorem supplies all small projected radial levels there |
| `AbelFormalization/CharbonnelSardianProjectionRadialEscapeDichotomy.lean` | Proves that an old fixed-level fiber over a bounded visible set is bounded or its reciprocal-radial range accumulates at zero; in the unbounded branch WS5 supplies every sufficiently small projected radial level |
| `AbelFormalization/CharbonnelSardianProjectionCase2Bridge.lean` | Identifies the old Sardian tuple fiber with Wilkie Case 2, transports regularity/boundedness/nonemptiness across product/flat coordinates, and converts the fixed-minor alternative into all sufficiently small projected levels while retaining the full-projection branch for downstream localization |
| `AbelFormalization/CharbonnelSardianProjectionBoundaryLocalization.lean` | Eliminates the full-projection branch near the frontier of the closed target projection: a vertical fiber is uniformly separated from the target closure, the old from-below clause makes a fixed visible point absent from every sufficiently small old section, and the automatic Case 2 bridge therefore yields only the small-level outcome |
| `AbelFormalization/CharbonnelSardianProjectionFromAboveAssembly.lean` | Selects prefixwise uniform small-level intervals into a recursive successor modulus and combines them with the mixed-depth prefix lift to construct a complete one-coordinate Sardian projection certificate, including assembly after refinement of the old prefix modulus |
| `AbelFormalization/CharbonnelModulusFirstReparameterization.lean` | Implements Wilkie 3.10's first-coordinate reparameterization and proves that one common refined modulus keeps both the original old prefix and the prefix with first coordinate replaced by the chosen boundary scale bounded for the old modulus |
| `AbelFormalization/CharbonnelSardianProjectionBoundaryLift.lean` | Lifts a crossing of the frontier of the closed visible projection to a point on the old frontier along a fixed-hidden-coordinate segment inside a convex visible neighborhood |
| `AbelFormalization/CharbonnelSardianProjectionCompactUniformization.lean` | Extracts one uniform positive final-level interval from local boundary data over each compact frontier truncation and feeds it into the refined-modulus projection-certificate constructor |
| `AbelFormalization/CharbonnelSardianProjectionCriticalValues.lean` | Encodes exact-depth critical parameter values as one literal-zero Charbonnel member, proves regularity outside it, and isolates the general rectangular Morse–Sard smallness theorem |
| `AbelFormalization/CharbonnelSardianProjectionBoundaryScale.lean` | Uses compactness of each frontier truncation to choose a global positive scale with fixed-hidden boundary lifts and local geometric bounds |
| `AbelFormalization/CharbonnelSardianProjectionFamilyBoundaryScale.lean` | Takes the finite minimum of all constituent separation thresholds so the old piece selected by from-above approximation is uniformly covered |
| `AbelFormalization/WilkieLemma34NestedModulusAvoidance.lean` | Proves Wilkie Lemma 3.4 by arity induction from WS5 and Charbonnel 2.1: every empty-interior closure member is avoided by one nested positive modulus |
| `AbelFormalization/CharbonnelSardianProjectionRegularModulus.lean` | Applies Lemma 3.4 to the finite exact-depth critical-value set and intersects the resulting avoidance modulus with the old approximation modulus |
| `AbelFormalization/CharbonnelSardianProjectionLocalAssembly.lean` | Joins boundary scale, old-piece selection, regularity, the bounded-or-radial dichotomy, and compact uniformization into a complete one-coordinate projection certificate |
| `AbelFormalization/CharbonnelSardianProjectionOneCoordinate.lean` | Derives the one-coordinate certificate from critical-value smallness and iterates it, with explicit coordinate reassociation, to the full arbitrary-block projection-constructor interface |
| `AbelFormalization/MorseSardFlatJet.lean` | Proves the flat-jet part of rectangular Morse--Sard: under the classical differentiability order, the image of the locus where all derivatives through the critical order vanish has zero target volume, via a quantitative Taylor/Hölder covering argument |
| `AbelFormalization/RectangularMorseSard.lean` | Proves the constant-rank part of rectangular Morse–Sard, makes the rank-jump source nowhere dense, and reduces nullity of all critical values exactly to nullity of the rank-jump image |
| `AbelFormalization/CharbonnelSardianProjectionMorseSardReduction.lean` | Shows that the standard `C^(a-b+1)` rectangular Morse–Sard theorem makes the finite exact-depth bad set null and discharges Wilkie's complete positive-projection constructor |
| `AbelFormalization/Wilkie27CriticalValues.lean` | Proves critical-value empty interior for smooth family tuples by Wilkie weak selection plus Maxwell almost-everywhere smoothness, makes the finite exact-depth bad set null via Theorem 2.1, and discharges the projection constructor without a Morse–Sard premise |
| `AbelFormalization/CharbonnelSardianIntegerAffineSliceGeometry.lean` | Wilkie 3.12's affine-slice polynomial and family membership, hidden-coordinate elimination, finite hyperplane presentation, and the frontier-only condition for closed targets |
| `AbelFormalization/CharbonnelSardianIntegerAffineSliceLift.lean` | Wilkie 3.12's two-parameter radial/slice equation lift of old Sardian constituents and finite families; the frontier-trace and source-stage modules complete its approximation and rank applications |
| `AbelFormalization/CharbonnelSardianIntegerAffineSliceSections.lean` | Exact fixed-parameter visible section of the lifted constituent: the old section intersected with the closed radial sublevel and affine slice band, including the radial boundary witness |
| `AbelFormalization/CharbonnelCompactIntersectionThickening.lean` | Compact closed-set intersection neighborhood lemma needed by Wilkie 3.12 from-below approximation, with a common or separate closeness radius and valid empty-intersection behavior |
| `AbelFormalization/CharbonnelIntegerAffineSliceMetric.lean` | Correct one coordinate of a nonzero integer-affine row to its closed hyperplane at distance at most the form's magnitude; small squared levels lie in any chosen hyperplane thickening, and zero rows are classified |
| `AbelFormalization/CharbonnelCompactRadialIntegerAffineSliceBelow.lean` | Wilkie 3.12 fixed-parameter compact radial below-clause proximity to an actual closed-target/hyperplane intersection, with nonzero and both zero-row cases; nested modulus and the from-above clause remain open |
| `AbelFormalization/CharbonnelSardianIntegerAffineFamilySectionBridge.lean` | Extends the affine-slice section identity through common-depth padding and finite-family union, supplies the lifted family's compact below scales, and recovers finite-family membership from an old section witness |
| `AbelFormalization/CharbonnelSardianIntegerAffineFrontierTrace.lean` | Constructs Wilkie 3.12's full nested modulus for the exact frontier-hyperplane trace and proves both closure-approximation clauses for positive and negative integer-affine traces |
| `AbelFormalization/CharbonnelIntegerAffineSectionReplacement.lean` | Wilkie 3.13's exact three-piece `closure B ∩ H` identity and conditional certificate union from exact and one-sided traces; this closed-stage target can differ from `closure (B ∩ H)` |
| `AbelFormalization/CharbonnelIntegerAffineWeakStageSigns.lean` | Polynomial-sign presentations of integer-affine exact and strict side cuts, plus Wilkie 3.13's rank-zero base descriptions within an earlier weak-family stage; projected-zero rank-one replacements supply the downstream numeric rank bridge |
| `AbelFormalization/CharbonnelSourceStageHierarchy.lean` | Wilkie's literal source hierarchy `S(0)=S`, `S(i+1)=((S(i)ᵘ)ᵖʳ)ᶜˡ`, with nonempty finite-union, arbitrary-projection, and closure-at-infinity membership/induction APIs; computes a source depth for every maintained Charbonnel description, compares the two closure presentations under explicit weak-stage hypotheses, and turns a stagewise Sardian induction hypothesis into the exact/strict predecessor cuts used in 3.13 |
| `AbelFormalization/CharbonnelSourceStageWeakPreservation.lean` | Proves directly from WS1–WS4 that nonempty finite-union, arbitrary-projection, and closure-at-infinity expansions preserve positive-arity weak structures; hence every stage of Wilkie's literal source hierarchy is weak whenever the base family is weak |
| `AbelFormalization/CharbonnelSourceStageIntegerAffineTrace.lean` | Combines stage weakness with Wilkie 3.12's frontier traces to prove the one-row 3.13 stage step, iterates traces through finite affine systems, discharges the full numeric integer-affine Sardian rank input, and proves every literal-zero source stage Sardian from smooth geometric closure and the positive-projection constructor |
| `AbelFormalization/CharbonnelIntegerAffineSignCellFrontier.lean` | Nonzero integer-affine coordinate moves meet both strict sides in every hyperplane ball, so the positive and negative one-sided closures have the frontier trace required by Wilkie 3.12 |
| `AbelFormalization/CharbonnelClosureComponentBound.lean` | Universal polynomial encoding of affine sections, Maxwell's strict thickening, and the strict description-rank drop below a closure node |
| `AbelFormalization/MaxwellCompactComponentSeparation.lean` | Compact clopen separation transferring uniform strict-tube component bounds to a zero-defect limit fiber |
| `AbelFormalization/CharbonnelMaxwellClosureBound.lean` | Fixed-parameter tube homeomorphism, geometric Maxwell comparison, and the closure-node affine-section bound |
| `AbelFormalization/CharbonnelAffineSectionRankInduction.lean` | Numeric strong-rank induction proving WS5 for the whole literal-zero Charbonnel closure under uniform fiber finiteness |
| `AbelFormalization/CharbonnelSection5VerticalIncidence.lean` | Charbonnel §5.3(a): polynomial moving closed-ball incidence, its literal-zero closure membership, and the uniform vertical-image component bound from WS5 |
| `AbelFormalization/CharbonnelSection5LocalVerticalStability.lean` | Maximal local count, compact interval labels, and stable smaller-ball component bijections under a strong full-support premise; the source's count-lowering selection still needs correction and proof |
| `AbelFormalization/CharbonnelSection53RelativeLexDescent.lean` | Relative balls in `ω`, local lex-rank minimality, and relative interval stability from an explicit strict-refinement premise that permits component-count descent |
| `AbelFormalization/CharbonnelSection53GlobalStratum.lean` | Compact component base supports, global-max/minimum-defect choices, closed defective-support union, and setup for the alternate stationary-chain/WS5 affine-explosion route |
| `AbelFormalization/CharbonnelSection53GlobalDichotomy.lean` | Relative bad-support avoidance and local count maximization; a sufficient unproved one-step successor choice yields the nested stationary chain or direct lexicographic descent |
| `AbelFormalization/CharbonnelSection53DirectDescentRank.lean` | Direct lexicographic descent from the global minimum-defect stratum necessarily lowers the maximal component count `M` |
| `AbelFormalization/CharbonnelSection53CountSaturation.lean` | With no direct descent, an interior point of `B` outside its defective supports yields a bad-support-avoiding successor with the same global `M` and defect at least `δ` |
| `AbelFormalization/CharbonnelSection53DefectiveLabelAvoidance.lean` | Actual inclusion-induced vertical component labels over `B' ⊆ B \\ β` all map to old components with full support on `B`, leaving splitting and defect equality explicit |
| `AbelFormalization/CharbonnelSection53StationaryLimitSupport.lean` | Compact nested-ball singleton limit, late vertical localization, and the projected-neighborhood step for deletion chains; stationary exclusion is reduced to an explicit no-component-collapse premise |
| `AbelFormalization/CharbonnelSection53DeletedComponentReplacement.lean` | Deleting defective supports removes those old vertical components from a successor image; equal maximal counts require collisions in any old-parent component map |
| `AbelFormalization/CharbonnelSection53ParentCollision.lean` | Instantiates the actual inclusion-induced parent map in a stationary deletion chain: positive defect supplies a missing old component, and equality of the finite component counts forces two distinct successor components to share one surviving old parent |
| `AbelFormalization/CharbonnelSection53ParentCollisionIteration.lean` | Iterates collisions along an already supplied stationary chain, producing disjoint lost branches and injective canonical heights, and reduces exclusion of that chain to the lost-branch affine-separation statement |
| `AbelFormalization/CharbonnelSection53LostBranchAffineLine.lean` | Proves that selected points from distinct lost branches on one nondegenerate affine line occupy distinct components of the affine section; finite-prefix collinear selection is a sufficient condition for the alternate stationary-chain route, and the first two-branch prefix is unconditional |
| `AbelFormalization/CharbonnelSection53LostBranchChordalSection.lean` | Proves the segment obstruction between differently indexed lost branches and, for an already constructed stationary chain, reduces its exclusion to one chordal affine section through every finite prefix; common-line selection is recovered as a stronger sufficient special case |
| `AbelFormalization/CharbonnelSection53RankOneBase.lean` | Proves full projection gives nonzero local component count, count one forces zero defect, and the global `M = 1` stratum admits neither a positive-defect successor obligation nor a stationary nested chain |
| `AbelFormalization/CharbonnelSection5AnalyticReduction.lean` | Separates the compact exceptional-fiber argument of §§5.4--5.6 from the bounded graph extraction of §5.7, proves the measure/topology glue from those two source-shaped reductions, and reconstructs the full Section 5 analytic interface |
| `AbelFormalization/CharbonnelSection56InfiniteFiberLocus.lean` | Defines the canonical infinite vertical-fiber locus, identifies it with a finite-cardinality threshold under the WS5 component bound, proves its Charbonnel membership, and proves the Baire slab interior lift for closed relations |
| `AbelFormalization/CharbonnelSection56InfiniteFiberLocalClosedness.lean` | Repairs the false projected-local-closedness assertion in §5.5 by using the closure of the infinite-fiber locus as a closed exceptional base; Maxwell closure-interior regularity yields the required interior lift and the complete §§5.4--5.6 compact reduction |
| `AbelFormalization/CharbonnelSection57GraphExtraction.lean` | Extracts continuous labelled graphs from a compact stable interval witness and a closure-fiber cardinality bound, removes the unique zero branch using relative closedness, and reduces §5.7 to the explicit stable closure-fiber bound witness |
| `AbelFormalization/CharbonnelSection57InfiniteFiberBridge.lean` | Shows a finite limiting closure fibre has at most one point in each stable interval, uses the closed infinite-fibre exceptional base to derive the cardinality bound, and narrows the §5.7 residual to stable-closure open localization together with Maxwell selection |
| `AbelFormalization/CharbonnelSection57OpenLocalizationRelativeBridge.lean` | Runs relative lexicographic descent while retaining a prescribed nonempty open region and specializes UFF to an ambient stable closure witness from the explicit strict-refinement interface |
| `AbelFormalization/CharbonnelSection57OpenBaseRelativeBridge.lean` | Shrinks relative stable separation on an open trace base to an ordinary ambient stable witness, removing the artificial full-space base from the local Section 5.7 bridge |
| `AbelFormalization/KuratowskiUlamProduct.lean` | Full Kuratowski--Ulam theorem for Baire-measurable product sets, with residual sections for residual sets and meagre sections for meagre sets; this discharges the category/Fubini library step but not Maxwell's family-geometric component argument |
| `AbelFormalization/CharbonnelClosureInteriorRegularity.lean` | Closed-lift `F_sigma` exhaustion, meagreness reduction, and the exact equivalence between Maxwell finite selection and closure-interior regularity under WS5 |
| `AbelFormalization/MaxwellMeagreClosureFamilyEquivalence.lean` | Under `PositiveArityOMinimalWeakSetStructure C`, identifies `HasMaxwellMeagreClosureComponentSelection C` with both exclusion of meagre members whose closures have interior and `CharbonnelClosureInteriorRegularity C`; no arbitrary-set selection theorem is asserted |
| `AbelFormalization/MaxwellMeagreClosureSelection.lean` | Proves Maxwell's family-geometric selection step from disjoint vertical slabs, lower-dimensional closure regularity, Kuratowski--Ulam, and WS5, then derives closure-interior regularity and the literal-zero family selection unconditionally from the maintained induction hypotheses |
| `AbelFormalization/MaxwellClosureNullity.lean` | Maxwell's ambient-dimension closure/nullity induction, connected compact reduction, and the four closure/interior/nullity equivalences from the two remaining geometric successor steps |
| `AbelFormalization/CharbonnelComplementPipeline.lean` | Correctly located projected-zero DC input, Sardian rank-induction skeleton, closed-boundary interface, positive-arity complement assembly boundary, and concrete construction of the all-arity complement envelope |
| `AbelFormalization/CharbonnelClosedBoundaryCellAssembly.lean` | Proves unary complement closure from WS5, formalizes recursive graph/band cells and finite compatible covers, and reduces the former closed-boundary assembly premise to the higher-dimensional compatible-cover induction for projected closed lifts |
| `AbelFormalization/CharbonnelOrderedSelectorCells.lean` | Formalizes the full-dimensional Section 4 cylinder step: finitely many strictly ordered continuous exact-fibre selectors cut each base-cell cylinder into compatible graph, gap, and ray cells; handles empty fibres by one cylinder and flattens mixed-cardinality relative covers over a finite base cover, with every family-membership fact explicit |
| `AbelFormalization/CharbonnelOrderedSelectorMembership.lean` | Derives every selector ray, consecutive band, and empty-fibre cylinder membership from base membership and restricted selector-graph membership using only WS1--WS4, then plugs those results into the local and global finite-selector cover constructors |
| `AbelFormalization/CharbonnelOrderedSelectorContinuity.lean` | Constructs the canonical increasing `Fin r` enumeration of each exact finite scalar fibre, identifies its endpoints with the existing Maxwell minimum and maximum selectors, and proves every selector continuous from the two source-shaped local facts: closure/no-endpoint escape and uniform no-collision; a compactness argument derives no escape for closed relations in continuous bands, and a wrapper feeds the selectors directly to the membership-complete cell constructor |
| `AbelFormalization/CharbonnelOrderedSelectorGraph.lean` | Exposes an arbitrary entry of a full increasing fibre tuple by an existential-projection incidence, identifies that entry with the canonical selector under exact fibre cardinality, proves every canonical selector graph belongs to the Charbonnel closure, and supplies local and global cell-cover wrappers with all graph/ray/band/cylinder membership premises discharged |
| `AbelFormalization/WilkieSection4CollisionLocus.lean` | Formalizes Wilkie's positive pairwise-gap relation `H`, proves `H` and its closed zero-trace locus `H̃` belong to the Charbonnel closure, and derives the selector continuity module's uniform no-collision condition on every base cell disjoint from `H̃` |
| `AbelFormalization/WilkieSection4EndpointLoci.lean` | Formalizes the positive lower/upper endpoint-gap relations `H_f,H_g`, their Charbonnel membership and closed zero traces, and proves that relative closedness inside a continuous open band plus avoidance of both endpoint traces yields vertical closure stability and the selector no-escape condition |
| `AbelFormalization/WilkieSection4CardinalityStability.lean` | Derives Wilkie's positive cutoff `N` from WS5/Fubini and Theorem 2.1, proves the page-419 upper-semicontinuity argument by injecting each nearby scalar fibre into the limiting fibre under no escape and no collision, and constructs the full selector-cylinder cover on an open cell simultaneously compatible with the closed `A_j` loci |
| `AbelFormalization/WilkieSection4OpenCell.lean` | Joins the endpoint, collision, and cardinality loci into the complete full-dimensional local branch: relative closedness in the ambient band and avoidance of the three zero traces yield exact continuous ordered selectors and a finite compatible graph/band/ray cover of the cylinder over one nonempty open recursive cell |
| `AbelFormalization/WilkieSection4SimultaneousRefinement.lean` | Isolates the finite-family common-refinement content of Wilkie's `(II)ₙ` and proves that individual compatible covers from `(I)ₙ`, together with this common-refinement property, yield one finite recursive-cell cover simultaneously compatible with every closed target in the family |
| `AbelFormalization/WilkieSection4CommonRefinement.lean` | Proves the complete unary common-refinement theorem `(II)₁` by finite Boolean atoms and unary-piece decomposition, derives the exact cover-indexed form, and lifts simultaneous refinements through pure cylinders |
| `AbelFormalization/CharbonnelCellBoundaryCompatibility.lean` | Proves every recursive Charbonnel cell is preconnected and that a finite cell cover compatible with `A ∩ B` is automatically compatible with closed `A` whenever `B` contains `frontier A`; this discharges the topological boundary-carrier transfer in Wilkie's Section 4 induction |
| `AbelFormalization/CharbonnelUnaryCompatibleCellCover.lean` | Constructs the actual finite recursive-cell cover for every unary family member from WS5 decompositions of the member and its complement, and combines this `(I)₁` base with the higher-dimensional individual-cover property |
| `AbelFormalization/WilkieSection4LociRefinement.lean` | Packages all `closure A_j` and collision/endpoint traces as one finite closed family, proves their Charbonnel membership, and uses `(I)ₚ + (II)ₚ` to obtain a global cover simultaneously compatible with those loci and the ambient base cell |
| `AbelFormalization/WilkieSection4BadLocusExclusion.lean` | Proves finite scalar fibres make the collision and endpoint gap relations interiorless, localizes their zero traces to open cells, and applies Charbonnel Theorem 2.2 to turn simultaneous compatibility into automatic avoidance of all three bad loci |
| `AbelFormalization/WilkieSection4MixedCellAssembly.lean` | Flattens the complete open-cell selector construction and the lower-dimensional induction over a finite simultaneous base cover, including empty cells, and supplies both direct and boundary-intersection forms of Wilkie's final Section 4 assembly |
| `AbelFormalization/WilkieSection4SourceAssembly.lean` | Joins the internally derived cardinality cutoff, simultaneous loci refinement, Theorem 2.2 bad-locus exclusion, selector cylinders, outside-base cylinders, and non-open recursive branch into the source-shaped Section 4 open-band cover theorem |
| `AbelFormalization/WilkieSection4EnrichedCells.lean` | Retains projected bases, continuous boundary functions, restricted boundary-graph membership, and projection coherence in enriched graph/band/ray/cylinder cells; proves equality-locus refinement, strict boundary ordering, local/global selector compatibility, and the full enriched `(II)_{n+1}` common-refinement successor |
| `AbelFormalization/WilkieBoundedCompactification.lean` | Formalizes Wilkie's coordinate map `t ↦ t / √(1+t²)` as a homeomorphism onto the open cube, proves its graph and inverse graph are polynomial-sign constructible, transports Charbonnel membership in both directions, proves relative closedness and projection compatibility, and identifies the pullback of the bounded relative complement |
| `AbelFormalization/CharbonnelRelativeCoverComplement.lean` | Extracts a cube-relative set difference as the finite union of exactly the cover cells disjoint from the target, using only empty-set and binary-union closure, and specializes the result to the Charbonnel closure |
| `AbelFormalization/WilkieBoundedComplementAssembly.lean` | Packages relative compatible covers of bounded projected WS6 lifts and proves that they imply positive-arity complement closure for the literal-zero Charbonnel closure |
| `AbelFormalization/CharbonnelBoundarySelectorAssembly.lean` | Packages mixed-cardinality ordered-selector data over a finite recursive base cover, assembles its global cylinder cover, transfers boundary-intersection compatibility to a closed target, and reduces the higher-dimensional closed-member step to the exact simultaneous base-refinement premise |
| `AbelFormalization/CharbonnelSourceComplementPipeline.lean` | Replaces the finite-decomposition detour by the source-shaped route, constructs both Sardian branches internally, and exposes an endpoint with exactly UFF, Maxwell family selection, the Section 5 analytic step, and the narrowed closed-lift cell-cover premise |
| `AbelFormalization/CharbonnelBoundedSourceComplementPipeline.lean` | Strengthens the source-shaped endpoint so its Section 4 input is exactly the cube-relative compatible-cover property after Wilkie's bounded-coordinate transport |
| `AbelFormalization/CharbonnelSourceEnrichedCellPipeline.lean` | Gives dimension-local `(II)`, iterates the enriched successor from the unary base when enrichment is retained, converts finite enriched projected-lift decompositions into the closed-lift cover property, and exposes the earlier enriched-induction form of the Section 4 residual |
| `AbelFormalization/WilkieProjectionCoherentCellCover.lean` | Proves Wilkie's one-step projection argument for enriched cell covers: exact projected bases that are equal or disjoint induce a finite lower-dimensional cell cover compatible with the projected target |
| `AbelFormalization/WilkieSection4EnrichedSelectorOutput.lean` | Repackages every ordered-selector graph, band, ray, and cylinder as an enriched successor cell and proves local and global simultaneous-cover theorems that retain projected bases and boundary-graph certificates |
| `AbelFormalization/WilkieSection4PartitionedEnrichedSelectorOutput.lean` | Strengthens the source common refinement with its partition clause, carries equal-or-disjoint bases through the retained selector construction, and turns an enriched relative cover into a one-step projection-coherent enriched cover |
| `AbelFormalization/WilkieProjectionCoherentCellCoverTower.lean` | Consumes a lossless coherent cover at every positive-dimensional stage, projects it down to compatible covers, upgrades the relative covers globally using the established common-refinement induction, and feeds the supplied bounded tower into the complement and main-theorem pipelines |
| `AbelFormalization/WilkieSection4ProjectionTowerAssembly.lean` | States the tower interface only in positive dimensions, proves the older all-dimensional interface inconsistent because there are no zero-dimensional `CharbonnelCell`s, and transports the Section 4 endpoint through the corrected interface |
| `AbelFormalization/WilkieSection4GraphInduction.lean` | Proves the intrinsic graph-cell branch: the graph is homeomorphic to its recorded base, projected relative closedness and Charbonnel membership descend, and compatible lower-dimensional covers lift losslessly through the graph |
| `AbelFormalization/WilkieSection4BoundedEnrichedReduction.lean` | Builds the canonical open-cube enriched cell and reduces the bounded closed-member cover and successor-retention steps to the corrected positive-dimensional partitioned-refinement input |
| `AbelFormalization/WilkieSection4DeepEnrichedCells.lean` | Defines recursively enriched Wilkie cells whose projected base retains the same data at every lower dimension, and proves exact forgetting to the ordinary and one-step enriched cell APIs without changing carriers |
| `AbelFormalization/WilkieSection4DeepProjectionTower.lean` | Shows that one finite hereditary recursively enriched cover, with equality-or-disjointness at every projected depth, automatically generates the complete projection-coherent cover tower consumed by the complement pipeline |
| `AbelFormalization/WilkieSection4DeepSuccessorAssembly.lean` | Restricts enriched successor cells to recursively enriched partition pieces, assembles hereditary projection-coherent covers, and proves the complete two-dimensional bounded-cube base case; the downstream bounded-deep successor and simultaneous-induction modules complete the higher-dimensional refinement and assemble the all-dimensional tower |
| `AbelFormalization/LionRankPatchFixedSquareEncoding.lean` | Covers every C¹ rectangular fiber by finitely many canonical rank/selected-minor patches and proves that patchwise fixed-square encoders plus Gabrielov upper-number bounds imply UFF; characterizes each selected patch by one nonzero rank minor and vanishing successor minors |
| `AbelFormalization/LionRankPatchCanonicalLagrangeReduction.lean` | Presents each canonical closed rank/minor patch by explicit equations and proves that finite regular Lagrange covers for independent subtuples meeting every component construct the fixed-square atlas and, with Gabrielov bounds, uniform fiber finiteness |
| `AbelFormalization/LionRankPatchMainTheoremPipeline.lean` | Feeds the finite rank/minor atlas into the bounded source complement pipeline, giving pointwise o-minimality and family-wide `MainTheorem` endpoints from patch encoders, Gabrielov or fixed-square regular-fiber bounds, Maxwell selection, the Section 5 analytic step, and bounded relative cell covers |
| `AbelFormalization/WilkieLionExactResidualPipeline.lean` | The legacy endpoint now derives Maxwell selection internally and has four explicit inputs: Gabrielov bounds, canonical finite Lagrange covers, stable-closure open localization for §5.7, and bounded projection-coherent enriched tower assembly. The first two are being replaced by the source-faithful Lion Theorem 7' route above |
| `AbelFormalization/WilkieLionSourceExactResidualPipeline.lean` | Uses `IsAbel.hasUniformFiberFiniteness` internally and exposes conditional pointwise and family endpoints with exactly two premises: §5.7 stable-closure open localization and bounded projection-coherent Section 4 tower assembly; it does not prove either premise or `MainTheorem` unconditionally |
| `AbelFormalization/GeneralCodimensionLagrange.lean` | Square augmented Lagrange system, family closure, and normalized multiplier existence/uniqueness in arbitrary codimension |
| `AbelFormalization/GeneralCodimensionLagrangeGenericMorse.lean` | Center-parameter family, total submersivity, and a Sard-based center making every zero of the arbitrary-codimension Lagrange system regular |
| `AbelFormalization/LiftedComponentFiniteness.lean` | Injection of connected components into any finite auxiliary type meeting every component through proper minimizers |
| `AbelFormalization/GeneralCodimensionRegularComponents.lean` | Targetwise finite connected components for arbitrary-codimension globally regular zero loci and fibers |
| `AbelFormalization/LionGlobalSubmersionFixedSquare.lean` | One target-independent raw Lagrange parameter-recording square map, its family membership, derivative transfer, and targetwise Sard center selection |
| `AbelFormalization/LionGlobalSubmersionComponentEncoding.lean` | One fixed-square regular-fiber encoding and component injection for globally submersive rectangular family maps |
| `AbelFormalization/LionFixedMinorConstantRankComponentEncoding.lean` | One fixed-square regular-fiber encoding for lower-rank maps with a globally nonvanishing selected minor and matching global rank bound; the selected constraints agree locally with full fibers, while a fallback base point handles unrelated branches of the selected fiber |
| `AbelFormalization/LionProperRegularCompactUpperBound.lean` | Proper smooth square maps have bounded nearby full fibers at finite regular centers and one bound over compact sets of regular targets; the global Gabrielov bound remains open |
| `AbelFormalization/LionProperRegularFiberFinite.lean` | Proper square `C¹` maps have finite full fibers at regular targets by inverse-chart discreteness and compactness, discharging the compact-target bound's pointwise premise |
| `AbelFormalization/ReciprocalConstraintGraph.lean` | Closed reciprocal graph for replacing a nonzero constraint by one globally regular augmented equation |
| `AbelFormalization/Remaining.lean` | Equivalence between `MainTheorem` and its o-minimality clause |

The formalization found a concrete compact semialgebraic counterexample to the
printed §5.5 claim that the infinite-fiber locus is locally closed.  The
closure-based repair above proves the consequence actually needed by the
argument from the already retained Maxwell closure-interior premise.
