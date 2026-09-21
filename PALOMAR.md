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

This project formalizes Artem Chernikov's private working manuscript
*A transexponential o-minimal structure (maybe)*, `omin.tex`, Version 29,
7 September 2026, SHA-256
`f71eff9a0f971a8b17ac33c956b34313625c4e986bb9f9dff269ff1b869029d2`.
The author states that this manuscript contains his new original proof of the
theorem obtained using GPT6 Astra. It supplied the conditional theorem and
proof architecture formalized here. A paper with a careful human presentation
is in preparation; the private manuscript file is not included in this
repository.

The metadata therefore identifies the private manuscript under `type: other`
and uses `relationship: formalizes`.
Palomar derives **source-based** provenance from that relationship: it records
where the theorem and proof were presented before formalization, while the
author's account of their mathematical originality is retained in the source
note. The project does not claim that the Lean development first presented
the manuscript's theorem or proof architecture.

The invariant-density construction of an Abel function was developed as an
additional part of the Lean project. It proves the existence discussed in the
manuscript and yields the unconditional Lean theorem
`exists_abel_ominimal_expansion` by applying the conditional theorem. This
construction is separately documented in
[ABEL_EXISTENCE_CONSTRUCTION.md](ABEL_EXISTENCE_CONSTRUCTION.md); it does not
establish Szekeres's stronger asymptotic or uniqueness.

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
reported. This account records the project's own audits and does not claim
Palomar registration. The project is licensed under Apache-2.0.

## Submission state

`Challenge.lean`, `Solution.lean`, and `comparator.json` define the Palomar
surface. The two `sorry` declarations in `Challenge.lean` are deliberate
statement placeholders and are excluded from the built development's zero-sorry
count, as is the unbuilt historical `Scratch/` archive. `Solution.lean` imports
the substantive proofs, and Comparator is configured to permit only `propext`,
`Quot.sound`, and `Classical.choice`.

The repository was made public with the author's approval on 21 September
2026. The exact submitted commit is
[`56de27174c84749290f007c8bb1c43840eded8c1`](https://github.com/archernikov/abel-formalization/tree/56de27174c84749290f007c8bb1c43840eded8c1).
Its [official full preflight](https://github.com/archernikov/abel-formalization/actions/runs/35640826200)
completed successfully at **19:18:28 UTC**, using the pinned PalomarSubmission
workflow and `palomar-standard-v1` profile. The mechanical report records
`status: pass`, no errors or warnings, high-trust Challenge provenance,
successful Comparator comparison, and acceptance by both NanoDa and Lean's
default kernel. The downloaded report's SHA-256 is
`9a01176d999442ad69893f807e94744ec1d6d0f49e7631cc6cc8cc708a57a5e1`.

Palomar received submission **`zaqsxewg529p`** at **19:21:44 UTC** on the same
date, with `comparator.json` selected at the repository root and the
responsible-author/maintainer relationship declared. Its
[registry verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/35644330031)
passed. Registration has not been authorized. The current metadata records the
manuscript as the substantive source being formalized, and an updated
submission is being prepared. This historical receipt does not claim
registration or publish an editorial outcome. Later documentation and
metadata commits do not change the source pinned by that earlier submission.

## Verified private snapshot

The **Verify formalization** workflow
[passed in run 35550508636](https://github.com/archernikov/abel-formalization/actions/runs/35550508636)
for commit
[`d98a773f50fecf6275f08276fe199f77ca53f832`](https://github.com/archernikov/abel-formalization/tree/d98a773f50fecf6275f08276fe199f77ca53f832),
finishing on **21 September 2026 at 02:08:45 UTC**. The repository was private.
The recorded checks passed:

- Palomar's pinned metadata/configuration validator and Apache-2.0 license
  detection.
- `lake build`, covering the full proof library, Challenge, and Solution.
- `Audit.lean`: all **20,726 project declarations**, including **14,823 theorem
  declarations** (generated helpers included), use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `AbelExistenceAudit.lean` and `StatementCorrespondenceAudit.lean`, including
  the expanded existence hypotheses and expanded draft theorem statement.
- Comparator comparison of both declarations listed above against Challenge.
- Independent NanoDa replay and replay in Lean's default kernel. Both accepted
  the solution, and Comparator concluded `Your solution is okay!`.

This is a verification record for the specified commit and checking workflow.
It is not a Palomar editorial decision or registration. The separate official
preflight result for the submitted commit is recorded above.

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
Comparator with NanoDa. Its logs were private during preparation and became
public when the repository was published.

The standalone Comparator script is `scripts/verify-comparator.sh`. It requires
Linux with Landrun/systemd confinement, Git, Go, Rust/Cargo, Python, and Lean.
Its tool revisions match the recorded Palomar verification profile, with
`lean4export` selected for Lean `v4.34.0-rc2`. It downloads tools below ignored
`.cache/`; the proof build remains below ignored `.lake/`. A private CI pass is
useful evidence, but does not replace the official public preflight.
The workflow frees unused hosted-runner SDK storage before installing Lean and
tests the confined Lake launch before the full build. The latter check can also
be run on a configured Linux host with
`./scripts/verify-comparator.sh --check-environment`.

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

## Submission and registration procedure

The separate **Official Palomar preflight (public repository only)** workflow
is manual and skips its verification job while the repository is private.
For a future submission, run it with `mode: full` for the exact proposed commit
and require a passing mechanical report. Review current Palomar policy and
tool pins again at that time.

The ordinary submission layout uses repository `archernikov/abel-formalization`,
the full final commit SHA, Comparator path `comparator.json`, and metadata path
`formalization.yaml`, with no nested project path. Intake is at
<https://submit.palomar-registry.org/>. Neither workflow submits or registers
the project. Registration requires a separate decision after the editorial
review has been delivered.
