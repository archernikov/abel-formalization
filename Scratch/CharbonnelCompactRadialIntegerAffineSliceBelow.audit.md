# Wilkie 3.12 compact radial-slice below step: source-only audit

Frozen, unimported draft:
`Scratch/CharbonnelCompactRadialIntegerAffineSliceBelow.lean`.
No Lean/Lake command was run. No maintained module, umbrella, or README
was edited.

The nonzero-row theorem
`exists_compactRadial_integerAffineSlice_below_scales_of_nonzero`
uses only maintained topological and metric interfaces:

1. `isCompact_literalZeroVisibleRadialDenominator_sublevel` makes the
   visible set `K_r={x | D(x) ≤ r⁻¹}` compact at fixed positive radial `r`.
2. `isClosed_integerAffineSliceHyperplane` closes the exact displayed
   hyperplane `H`.
3. `compact_closed_intersection_thickening` chooses `etaOld>0` so points
   of `K_r` near both a **closed** target `A` and `H` are within `delta`
   of the actual intersection `A∩H`.
4. `exists_integerAffineSlice_sqLevel_thickening_scale` chooses
   `etaSlice>0` so `ell(x)^2≤etaSlice` puts `x` near `H`.

Thus a radial-confined point whose old section is `etaOld`-close to `A`
and whose positive slice-level equation has scale at most `etaSlice`
has a witness in `A∩H` within `delta`. The set-section wrapper uses the
exact intersection pattern of maintained
`wilkieAffineSliceConstituent_section_eq` after hidden-coordinate
elimination; it keeps old-section proximity explicit.

Zero rows are mathematically different and are proved separately.
If all coefficients and the constant vanish, `H=univ` and the old-target
witness is already a slice witness. If all coefficients vanish but the
integer constant is nonzero, `H=empty` and every squared level below one
is impossible by
`no_small_integerAffineSliceLevel_of_coeff_zero_constant_ne`. The
row-independent theorem classifies these cases. An empty list of equations
also represents a whole-space affine carrier, but finite-system assembly
is outside this one-row module.

This is the fixed-parameter **from-below topology**, not a completed
Wilkie 3.12 Sardian certificate. The source's nested modulus still must
choose radial, old-error, and slice-level parameters in the required
dependency order and prove old-section proximity uniformly. The
from-above/frontier clause needs separate density or intermediate-value
work. For an arbitrary nonclosed target `B`, this theorem can be applied
to `A=closure B`, producing proximity to `closure B∩H`. It does **not**
replace that set with `closure(B∩H)`; equality may fail without a specific
slice-density premise. In the closed-target case, the intersection itself
is closed and no such bridge is needed.

The likely elaboration checks for the compiler are let-unfolding of `K_r`
at `hxK` and simplification of the left-associated three-set intersection
in the section wrapper. The underlying composition is direct from the
compiled maintained lemmas.
