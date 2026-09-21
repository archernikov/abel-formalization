# Palomar submission note

## Result

**Title:** *A transexponential o-minimal structure*

**Abstract:** The real field expanded by the function
$x\mapsto A(1+x^2)$, where $A$ is a normalized analytic Abel function for
$e^x-1$, is an o-minimal structure that defines a function that grows faster
than any finite iterate of the exponential function.

The Palomar comparison covers two declarations:

- `AbelFormalization.mainTheorem` proves the result for every function satisfying
  the four stated Abel hypotheses.
- `AbelFormalization.exists_abel_ominimal_expansion` constructs such a function
  and yields the unconditional existence of the claimed expansion.

This is the substantive proof repository, not a wrapper around another
formalization.

## Exact scope

The function `A : ℝ → ℝ` is total in Lean. Its hypotheses constrain only the
positive half-line: `A` is analytic there, its derivative is positive,
`A(1)=0`, and

\[
A(\exp(x)-1)=A(x)+1 \qquad (x>0).
\]

Its values at zero and at negative inputs are irrelevant. The primitive added
to the real field is `C₀(x)=A(1+x²)`, so it samples `A` only at positive
arguments. Definability is ordinary first-order definability with arbitrary
real parameters. The inverse conclusion concerns the graph of the inverse of
`A:(0,\infty)\to\mathbb R`, restricted to positive inputs. The growth statement
says that for every fixed natural number `k`, this inverse eventually strictly
dominates the `k`-fold iterate of the usual exponential.

The existence construction proves exactly the needed Abel hypotheses. It does
not prove uniqueness, identify the constructed density with Szekeres's
distinguished solution, or prove Szekeres's precise asymptotic normalization.
The statement and encoding comparison is documented in
[MAIN_THEOREM_CORRESPONDENCE_AUDIT.md](MAIN_THEOREM_CORRESPONDENCE_AUDIT.md), and
the construction is documented in
[ABEL_EXISTENCE_CONSTRUCTION.md](ABEL_EXISTENCE_CONSTRUCTION.md).

## Origin and sources

Artem Chernikov declares the result and proof development to be original work
obtained with the assistance of ChatGPT 6 Astra. This records the author's
account of origin and the production process; it is not an independent proof
of novelty or priority. A paper with a careful human presentation is in
preparation.

An earlier private source is Artem Chernikov's working manuscript
*A transexponential o-minimal structure (maybe)*, `omin.tex`, Version 29,
7 September 2026, SHA-256
`f71eff9a0f971a8b17ac33c956b34313625c4e986bb9f9dff269ff1b869029d2`. Its
file is not included in this repository.

The development uses the following mathematical background:

- A. J. Wilkie, *A theorem of the complement and some new o-minimal
  structures*, *Selecta Mathematica* 5 (1999), 397–421,
  [doi:10.1007/s000290050052](https://doi.org/10.1007/s000290050052).
- Jean-Marie Lion, *Finitude simple et structures o-minimales (Finiteness
  Property Implies o-Minimality)*, *The Journal of Symbolic Logic* 67 (2002),
  no. 4, 1616–1622, [JSTOR 3648591](https://www.jstor.org/stable/3648591).
- G. Szekeres, *Fractional iteration of exponentially growing functions*,
  *Journal of the Australian Mathematical Society* 2 (1962), no. 3, 301–320; §2, Lemma 1,
  p. 304, [doi:10.1017/S1446788700026902](https://doi.org/10.1017/S1446788700026902).

Reid Barton's
[`lean-omin`](https://github.com/rwbarton/lean-omin/tree/fd733c6d95ef6f4743aae97de5e15df79877c00e)
was audited as a related Lean 3 development. No code from it is imported or
ported here, and it does not formalize this Abel-function theorem. The audit is
in [BARTON_REUSE_AUDIT.md](BARTON_REUSE_AUDIT.md).

## Production and review

Artem Chernikov is the human author and responsible maintainer. ChatGPT 6 Astra
was used in the initial mathematical research. Codex agents using `gpt-6-astra`
and `gpt-5.6-sol` made material contributions to Lean proof development,
compilation, comparison, and audits. Exact prompt, token, time, and spending
totals were not reconstructed.

The repository has received agent-led statement, dependency, reuse, compiler,
and axiom audits. No completed independent human-expert review has been
reported, and no Palomar editorial review or registration is claimed. The
project is licensed under Apache-2.0.

## Submission state

`Challenge.lean`, `Solution.lean`, and `comparator.json` define the Palomar
surface. The two `sorry` declarations in `Challenge.lean` are deliberate
statement placeholders and are excluded from the built development's zero-sorry
count, as is the unbuilt historical `Scratch/` archive. `Solution.lean` imports
the substantive proofs, and Comparator is configured to permit only `propext`,
`Quot.sound`, and `Classical.choice`.

Before submission, the exact final commit must pass its local build, audit, and
Comparator checks and be published at a stable public Git commit. Palomar's
public mechanical workflow, independent NanoDa replay, editorial review, and
registration are later gates. None of those later gates has yet been passed by
this private pre-submission snapshot.

## Reproduce the checks

The Lean project depends only on the pinned Mathlib revision and its dependency
closure. Comparator, NanoDa, and the packaging validator are external checking
tools, not additional mathematical assumptions or Lake dependencies.

Run the ordinary Lean checks from the repository root:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean AbelExistenceAudit.lean
lake env lean StatementCorrespondenceAudit.lean
```

`lake build` includes the proof library, Challenge, and Solution. The two
intentional Challenge warnings are expected; the proof audits inspect the
Solution's proof environment, where those placeholders are absent.

The **Verify formalization** GitHub Actions workflow is started manually and
works with this repository's private visibility. It checks the metadata using
PalomarSubmission at `3561d237dcc4b28482558ad28a64d767d7cc8615`, detects the root
license, builds the project, runs the three audits, and runs the pinned
Comparator with NanoDa. Its logs stay with the private repository.

The standalone Comparator script is `scripts/verify-comparator.sh`. It requires
Linux with Landrun/systemd confinement, Git, Go, Rust/Cargo, Python, and Lean.
Its tool revisions match the recorded Palomar verification profile, with
`lean4export` selected for Lean `v4.34.0-rc2`. It downloads tools below ignored
`.cache/`; the proof build remains below ignored `.lake/`. A private CI pass is
useful evidence, but does not replace the official public preflight.

For local metadata/configuration checks, supply an independent checkout of the
pinned PalomarSubmission commit and install its Python requirements:

```sh
python scripts/check-palomar-package.py --pipeline /path/to/PalomarSubmission
```

Pass `--licensee /path/to/bundle` with Palomar's Ruby bundle installed and
`BUNDLE_GEMFILE` set to its Gemfile to include the same SPDX detection used in
CI. Without that option, the script explicitly reports that detection is
omitted. This helper checks the package structure and direct imports; the
official verifier separately authenticates the entire Challenge import closure.

## Later publication and intake

The separate **Official Palomar preflight (public repository only)** workflow
is manual and skips its verification job while the repository is private.
After an explicit publication decision, run it with `mode: full` for the exact
final commit and require a passing mechanical report. Review current Palomar
policy and tool pins again at that time.

The ordinary submission layout uses repository `archernikov/abel-formalization`,
the full final commit SHA, Comparator path `comparator.json`, and metadata path
`formalization.yaml`, with no nested project path. Intake is at
<https://submit.palomar-registry.org/>. Neither workflow submits or registers
the project. Registration requires a separate decision after the editorial
review has been delivered.
