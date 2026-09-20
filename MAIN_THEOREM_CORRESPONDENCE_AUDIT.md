# Main-theorem statement correspondence audit

Date: 20 September 2026.

Verdict: no mathematical mismatch was found between the draft's **conditional
main theorem** and `AbelFormalization.mainTheorem : MainTheorem`. The hypotheses,
language, parameter convention, quantifiers, and conclusions agree. The separate
existence requirement is now supplied by `AbelFormalization.exists_isAbel`.

Source: the user-supplied `omin.tex` manuscript (not included in this
repository), Version 29, 7 September 2026. SHA-256:
`f71eff9a0f971a8b17ac33c956b34313625c4e986bb9f9dff269ff1b869029d2`.
The theorem is at source lines 131–141; its standing hypotheses are at 64–68,
and the inverse and definability conventions are at 111–129.

## Clause-by-clause comparison

Paths in the Lean column are relative to this project.

| Draft clause | Lean declaration and location | Result |
| --- | --- | --- |
| A is real analytic on (0, infinity). | `IsAbel.analytic`, `AbelFormalization/Basic.lean:28` | Exactly local real analyticity at every positive input. |
| A'(x) > 0 for every x > 0. | `IsAbel.deriv_pos`, `Basic.lean:30` | Same strict inequality and domain. |
| A(1) = 0. | `IsAbel.normalized`, `Basic.lean:31` | Identical. |
| A(exp(x) - 1) = A(x) + 1 for x > 0. | `E` and `IsAbel.abel`, `Basic.lean:24,32` | Identical. |
| C0(x) = A(1 + x squared). | `C0`, `Statement.lean:20` | Identical on all real x. |
| The structure is (R; <, +, multiplication, C0). | `AbelFunctionSymbol`, `AbelRelationSymbol`, `abelLanguage`, `abelStructure`, `Statement.lean:23–46` | Exactly those function/relation symbols interpreted on the actual reals. |
| All definability allows real parameters. | `UnaryDefinable`, `BinaryDefinable`, `Statement.lean:49,54` | Actual mathlib first-order definability over `Set.univ`. |
| Every definable unary set is a finite union of points and intervals. | `OMinimal`, `Statement.lean:77` | Quantifies over every definable subset of R; the union is indexed by `Fin n`. |
| The usual exponential is definable. | `ExponentialDefinable`, `Statement.lean:83` | Its full graph on all real inputs is definable. |
| T restricted to positive inputs is definable. | `PositiveInverseDefinable`, `Statement.lean:88` | The graph condition is `0 < p.1 ∧ p.2 = T p.1`; positivity restricts the input. |
| T is the inverse of A from (0, infinity) onto R. | `inverse`, `Inverse.lean:79`; inverse identities at 87–94 | Bijectivity and both inverse identities are proved from IsAbel, not assumed. |
| For each natural k there is a real threshold s_k, and all s > s_k satisfy T(s) > exp iterated k times at s. | `IsTransexponential`, `Statement.lean:98` | Same quantifier order, strict inequality, ordinary exponential, and inclusion of k = 0. |
| For every such A, all conclusions hold. | `MainTheorem`, `Statement.lean:104`; proof at `WilkieSection4LiteralZeroInduction.lean:78` | The final declaration has no extra geometric, finiteness, or complement-theorem premise. |

## Encoding details checked

- Lean's total function `A : R → R` does not strengthen the draft's domain.
  The hypotheses are local at positive points; `E x > 0` when `x > 0`;
  C0 samples only inputs at least 1; and the inverse uses `invFunOn A (Ioi 0)`.
  A function on the positive half-line can be extended arbitrarily elsewhere.
  There is no regularity requirement at zero or at negative inputs.
- `AnalyticOnNhd` here means analyticity at each point of the open set
  `Ioi 0`, not extension across its boundary or a uniform analytic radius.
  Mathlib defines this at `Mathlib/Analysis/Analytic/Basic.lean:120` and proves
  equivalence with `AnalyticOn` on open sets at
  `Mathlib/Analysis/Analytic/Within.lean:86`.
- Mathlib `Set.Definable` uses arbitrary first-order formulas in the
  language with parameter constants, at `Mathlib/ModelTheory/Definability.lean:56`.
  Its unary and binary specializations are at 298 and 302. Every formula still
  uses only finitely many parameters; `definable_iff_finitely_definable` is at 195.
- Neither formulas nor the quantified definable sets are restricted to
  quantifier-free, bounded, smooth, or projected-zero sets.
  `ProjectedZeroComplementEnvelope.abelBoundedFormula_mem`
  (`ProjectedZeroComplementCriterion.lean:316`) handles every formula
  constructor, including universal quantification.
  Here “BoundedFormula” tracks the number of bound variables, not a bounded
  real quantification domain. Its `oMinimal` theorem at line 366 returns the
  exact public `OMinimal A` proposition.
- The unary pieces are points, bounded open intervals, the two open rays,
  and the whole line. Closed or half-open intervals are represented by
  adding endpoint points. The empty set is represented with zero pieces.
  No disjointness requirement or bound uniform across all definable sets
  is imposed by the draft or by Lean.
- There is one fixed A in each structure. Neither the full function A nor
  multiple Abel functions are simultaneously added as primitive symbols.
  This respects the draft's scope remark at lines 149–171.
- The displayed language has no primitive 0, 1, negation, or division symbols,
  matching the draft's display. In any case this does not weaken definability:
  real parameters provide 0 and 1, and the graphs of additive negation and
  division are definable using addition, multiplication, and equality.

## Executable check

`StatementCorrespondenceAudit.lean` independently spells out the interpreted
real operations, the four assumptions, concrete singleton/interval/ray sets,
mathlib definability, both inverse identities, and the growth quantifiers.
Its `hypotheses_iff` proves the two directions of the hypothesis correspondence.
Its `expanded_main_theorem` derives the expanded draft conclusion from the
proved public theorem, without using `MainTheorem`, `OMinimal`, or
`UnaryPiece` as shorthand in the statement of that conclusion.

Commands run:

```sh
sh ../../work/run-lake.sh env lean StatementCorrespondenceAudit.lean
sh ../../work/run-lake.sh env lean AbelFormalization/Statement.lean
```

Both exited with code 0. The axiom checks for
`AbelFormalization.mainTheorem` and
`DraftStatementAudit.expanded_main_theorem` each returned exactly
`[propext, Classical.choice, Quot.sound]`. The audit rejects any other axiom.
The pinned mathlib checkout is unmodified and at
`e37d88a26f3791ed5a93daa1f949af1021b8d103`.

Two independent source reviews agreed with the correspondence findings.
This is a statement and semantics audit, with a fresh compiler/axiom check;
it is not a new line-by-line review of every intermediate mathematical lemma.

## Existence requirement supplied

The draft separately constructs an Abel function in lines 72–107 using
Szekeres. The earlier audit identified the lack of a formal existence witness.
The added theorem `exists_isAbel` in `AbelFormalization/AbelExistence.lean`
now proves `∃ A : ℝ → ℝ, IsAbel A` with no premises. It constructs a local
analytic positive invariant density, extends it by logarithmic iteration, and
integrates and normalizes it. The four fields of `IsAbel` are unchanged.

`exists_abel_ominimal_expansion` applies the existing universal theorem to this
witness. `AbelExistenceAudit.lean` independently spells out analyticity at
every positive input, strict positivity of the derivative, normalization at
1, and the exact Abel equation, and checks the axiom closure. See
[the existence construction](ABEL_EXISTENCE_CONSTRUCTION.md) and
`ABEL_EXISTENCE_VERIFICATION.txt` for the proof route and verification results.

The construction normalizes by the positive increment of the primitive,
rather than proving the precise Szekeres density asymptotic. This proves
exactly the required existence statement; uniqueness and identification with
a distinguished Szekeres solution are not asserted.

Stale comments in `Statement.lean` saying that there was no proof were corrected
to point to `WilkieSection4LiteralZeroInduction`. No mathematical definition,
hypothesis, or existing theorem proof was changed.
