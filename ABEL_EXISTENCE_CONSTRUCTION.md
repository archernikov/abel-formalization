# Abel existence construction

This note describes the existence argument implemented around
[`AbelExistence.lean`](AbelFormalization/AbelExistence.lean).  The construction
starts only from the dynamics

\[
E(x)=\exp(x)-1, \qquad L(x)=\log(1+x),
\]

and produces a function satisfying `IsAbel`.  It does not assume an Abel
function or an invariant density.  The resulting witness can then be supplied
to the manuscript's universal main theorem in
[`AbelExistentialMainTheorem.lean`](AbelFormalization/AbelExistentialMainTheorem.lean).

## Output declarations

`AbelExistence.lean` exposes two existence theorems:

```lean
theorem exists_analytic_invariant_density :
    ∃ b : ℝ → ℝ, AnalyticOnNhd ℝ b (Set.Ioi 0) ∧
      (∀ x > 0, 0 < b x) ∧
      (∀ x > 0, b (E x) * Real.exp x = b x)

theorem exists_isAbel : ∃ A : ℝ → ℝ, IsAbel A
```

The companion file `AbelExistentialMainTheorem.lean` applies the already
formalized conditional main theorem to that witness:

```lean
theorem exists_abel_ominimal_expansion :
    ∃ A : ℝ → ℝ, IsAbel A ∧
      OMinimal A ∧ ExponentialDefinable A ∧
        PositiveInverseDefinable A (inverse A) ∧
          IsTransexponential (inverse A)
```

Thus the existence construction and the long conditional development meet at
the small `IsAbel` interface.  The density construction itself does not use an
`IsAbel` hypothesis.

## Construction

### 1. A quadratic logarithmic defect

Let `complexL z = Complex.log (1 + z)`.  In
[`AbelLocalDensity.lean`](AbelFormalization/AbelLocalDensity.lean), the function
`logQuadraticTail` fills the removable singularity in

\[
\operatorname{complexL}(z)=z+z^2\tau(z),
\qquad \tau(0)=-\tfrac12.
\]

The factor

\[
\rho(z)=\frac{1}{(1+z)(1+z\tau(z))^2}
\]

is `densityRatio`.  It is analytic at zero, with
`densityRatio 0 = 1` and derivative zero there.  The additive defect is

\[
h(z)=\operatorname{Log}\rho(z),
\]

implemented as `logDensityDefect`.  The lemmas
`logDensityDefect_analyticAt_zero`, `logDensityDefect_zero`, and
`logDensityDefect_deriv_zero` say that $h$ is analytic at zero and
vanishes there to second order.

For positive real $x$, the factorization

\[
L(x)=x(1+x\tau(x))
\]

gives

\[
\operatorname{Re}h(x)
  =\log\!\left(\frac{x^2}{(1+x)L(x)^2}\right).
\]

This real-axis identity is supplied by `logDensityDefect_ofReal_re`.  It is the
exact multiplicative correction needed by the density invariance equation.

The general lemma
`exists_quadratic_bound_of_analytic_zero` in
[`AbelQuadraticDefectBound.lean`](AbelFormalization/AbelQuadraticDefectBound.lean)
then supplies $R>0$ and $C\geq0$ such that $h$ is analytic on the
punctured ball of radius $R$ and

\[
\lVert h(z)\rVert\leq C\lVert z\rVert^2
\quad (0<\lVert z\rVert<R).
\]

### 2. Normal convergence along logarithmic orbits

[`AbelLogBounds.lean`](AbelFormalization/AbelLogBounds.lean) proves the real
orbit estimate

\[
L^{\circ n}(x)\leq \frac{4}{n+1}
\qquad (0<x\leq1),
\]

through `L_iterate_le_four_div`.  Its complex half-disk lemmas say that

\[
\operatorname{complexL}^{\circ n}
  \bigl(B(x,x/2)\bigr)
 \subseteq
  B\bigl(L^{\circ n}(x),L^{\circ n}(x)/2\bigr),
\]

and that the iterate is analytic on the source disk.  The relevant declarations
are `complexL_iterate_mapsTo_half_ball` and
`complexL_iterate_analyticOnNhd_half_ball`.

Define the orbit sum, as in
[`AbelDensitySeries.lean`](AbelFormalization/AbelDensitySeries.lean), by

\[
S(z)=\sum_{n=0}^{\infty}h
  \bigl(\operatorname{complexL}^{\circ n}(z)\bigr).
\]

On $B(x,x/2)$, the preceding disk estimate bounds the norm of the $n$-th
orbit point by $6/(n+1)$.  The quadratic defect bound therefore gives the
summable majorant

\[
\left\lVert h
  \bigl(\operatorname{complexL}^{\circ n}(z)\bigr)\right\rVert
 \leq \frac{36C}{(n+1)^2}.
\]

The normal-convergence lemma `analyticOnNhd_logDensitySum_of_bound` makes
`logDensitySum h` analytic on such a disk.

### 3. A local positive invariant density

The local real density is

\[
b_0(x)=\frac{\exp(\operatorname{Re}S(x))}{x^2},
\]

which is `densityFromLogDefect h`.  It is positive for $x>0$.  Shifting the
convergent series by one term gives

\[
S(x)=h(x)+S(L(x)).
\]

Combining this identity with the real-axis formula for $h$ yields

\[
\frac{b_0(L(x))}{1+x}=b_0(x).
\]

`densityFromLogDefect_invariant` proves this calculation.
`exists_local_density_of_log_defect` in
[`AbelLocalDensityAssembly.lean`](AbelFormalization/AbelLocalDensityAssembly.lean)
packages normal convergence, real analyticity, positivity, and this local
invariance on some interval $(0,\varepsilon)$.

### 4. Extension to every positive real

[`AbelDensityExtension.lean`](AbelFormalization/AbelDensityExtension.lean)
proves that $L^{\circ n}(x)\to0$ for every $x>0$.  Once an iterate lies in
the local interval, pull the local density back by that iterate.  For any
sufficiently large $n$, set

\[
B(x)=b_0(L^{\circ n}(x))
  \prod_{k=0}^{n-1}\frac{1}{1+L^{\circ k}(x)}.
\]

The product is `logIterateWeight`.  Local invariance makes the displayed value
independent of the chosen sufficiently large $n$.  Fixing one such $n$ on a
neighborhood of each point proves analyticity; positivity follows from the
positive local density and positive factors.

The theorem `exists_global_density_of_local` produces a positive analytic
function $B$ on $(0,\infty)$ satisfying

\[
B(E(x))\exp(x)=B(x).
\]

The direction and factor in this equation are the chain rule for an Abel
derivative, since $E'(x)=\exp(x)$.

### 5. Integration and unit-increment normalization

[`AbelExistenceFromDensity.lean`](AbelFormalization/AbelExistenceFromDensity.lean)
defines the primitive

\[
F(x)=\int_1^x B(t)\,dt.
\]

The file proves that $F$ is real analytic on $(0,\infty)$ and
$F'(x)=B(x)>0$.  For

\[
D(x)=F(E(x))-F(x),
\]

the density equation gives

\[
D'(x)=B(E(x))\exp(x)-B(x)=0.
\]

Consequently $D$ is constant on the connected positive half-line.  Put

\[
c=F(E(1)).
\]

Because $F(1)=0$, this is the constant increment.  Moreover $E(1)>1$ and
$F$ is strictly increasing, so $c>0$.  Finally define

\[
A(x)=\frac{F(x)}{c}.
\]

The theorem `exists_isAbel_of_analytic_density` verifies all four fields of
`IsAbel`:

| `IsAbel` field | Construction fact |
| --- | --- |
| `analytic` | $F/c$ is analytic on $(0,\infty)$. |
| `deriv_pos` | $A'(x)=B(x)/c>0$. |
| `normalized` | $A(1)=0$, because the primitive is based at $1$. |
| `abel` | $A(E(x))=A(x)+1$, because $F(E(x))-F(x)=c$. |

As usual for this project, the Lean function is total, while these properties
only constrain its values on the positive real axis.

## Module and lemma chain

The supporting declarations form the following dependency-compatible chain.
At the top level, `AbelExistence.lean` first obtains the local density and then
applies the extension theorem.

| Module | Main role and declarations |
| --- | --- |
| [`Basic.lean`](AbelFormalization/Basic.lean) | Defines `E` and the four-field structure `IsAbel`. |
| [`Inverse.lean`](AbelFormalization/Inverse.lean) | Defines `L` and proves the real inverse and positivity facts used by the orbit arguments. |
| [`ComplexLog.lean`](AbelFormalization/ComplexLog.lean), [`ComplexLogIterates.lean`](AbelFormalization/ComplexLogIterates.lean) | Define `complexL`, prove disk contraction and iterate identities. |
| [`AbelLocalDensity.lean`](AbelFormalization/AbelLocalDensity.lean) | Defines `logQuadraticTail`, `densityRatio`, and `logDensityDefect`; proves second-order vanishing and the real-axis defect identity. |
| [`AbelQuadraticDefectBound.lean`](AbelFormalization/AbelQuadraticDefectBound.lean) | `exists_quadratic_bound_of_analytic_zero` turns second-order vanishing into a local $C\lVert z\rVert^2$ bound. |
| [`AbelLogBounds.lean`](AbelFormalization/AbelLogBounds.lean) | Gives inverse-linear real orbit decay and invariant complex half-disks. |
| [`AbelDensityExtension.lean`](AbelFormalization/AbelDensityExtension.lean) | Proves entry of inverse orbits into every neighborhood of zero and defines stable finite pullbacks; `exists_global_density_of_local` extends a local density to $(0,\infty)$. |
| [`AbelDensitySeries.lean`](AbelFormalization/AbelDensitySeries.lean) | Defines `logDensitySum` and `densityFromLogDefect`; proves normal convergence and local invariance from a defect identity. |
| [`AbelLocalDensityAssembly.lean`](AbelFormalization/AbelLocalDensityAssembly.lean) | `exists_local_density_of_log_defect` constructs the local positive analytic density. |
| [`AbelExistenceFromDensity.lean`](AbelFormalization/AbelExistenceFromDensity.lean) | `exists_isAbel_of_analytic_density` integrates and normalizes the global density. |
| [`AbelExistence.lean`](AbelFormalization/AbelExistence.lean) | Exposes `exists_analytic_invariant_density` and `exists_isAbel`. |
| [`AbelExistentialMainTheorem.lean`](AbelFormalization/AbelExistentialMainTheorem.lean) | Combines `exists_isAbel` with the universal `mainTheorem`. |

## Relation to Szekeres's normalization

Szekeres's §2, Lemma 1 in *Fractional iteration of exponentially growing
functions* states, for a real-analytic map on the positive half-line with
$f(x)>x$, $f'(x)>0$, and

\[
f(x)=x+a x^2+\cdots \quad (a>0),
\]

the existence of a distinguished differential Abel function $b$, with the
asymptotic normalization

\[
x^2 b(x)\longrightarrow \frac1a
\quad\text{as }x\downarrow0.
\]

For $f=E=\exp(x)-1$, one has $a=1/2$, so Szekeres's normalized density has
$x^2b(x)\to2$.  The source is G. Szekeres, “Fractional iteration of
exponentially growing functions,” *Journal of the Australian Mathematical
Society* 2 (1962), §2, Lemma 1, p. 304
([DOI](https://doi.org/10.1017/S1446788700026902)).

The Lean construction uses a different normalization route.  It first builds
a positive invariant density by the logarithmic-defect series.  It then
integrates that density, proves that the Abel increment is some constant
$c>0$, and divides the primitive by $c$.  This enforces translation by
exactly one without first proving an asymptotic value for the density at zero.

Accordingly, the current existence theorem makes no claim that the initially
constructed density has Szekeres's asymptotic normalization.  It also makes no
claim of uniqueness, of identification with a principal Szekeres solution, or
of the higher derivative asymptotics in Szekeres's lemma.  Those would require
additional theorems beyond `exists_isAbel`.

## Verification status

Verified on 20 September 2026. The targeted Lake build of
`AbelFormalization.AbelExistence` completed successfully (2841 jobs).
The existential main-theorem module and updated public umbrella each passed
direct Lean compilation. `AbelExistenceAudit.lean` passed, independently
expanding the four required properties of the witness.

The axiom closure of `exists_isAbel`, `exists_abel_ominimal_expansion`, and
the expanded existence statement is exactly
`[propext, Classical.choice, Quot.sound]`. The audit rejects every other axiom.
No proof placeholder or added axiom occurs in the new construction.
Mathlib remains the only Lake dependency and its pinned source is unchanged.

The exact commands, results, and scope of verification are recorded in
[`ABEL_EXISTENCE_VERIFICATION.txt`](ABEL_EXISTENCE_VERIFICATION.txt); raw
audit output is in
[`ABEL_EXISTENCE_AUDIT_OUTPUT.txt`](ABEL_EXISTENCE_AUDIT_OUTPUT.txt).
