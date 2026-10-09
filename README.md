# tate-curves-theta

Tate curves, q-uniformization, and the formal algebraic theta function.

## Status

The classical `q`-uniformization and theta-function package is **complete and
`sorry`-free** at the current tip. All results below live in the namespace
`TateCurvesTheta` (most under `TateCurvesTheta.TateParameter`), for a Tate parameter
`t : TateParameter K` (a unit `q` with `‖q‖ < 1`) over a field `K` with
`[NormedField K] [CompleteSpace K] [IsUltrametricDist K]`. The only extra hypotheses are
the arithmetic ones written into the statements: `(12 : K) ≠ 0`, or
`TameResidueChar K := ‖(2 : K)‖ = 1 ∧ (12 : K) ≠ 0` for the group law and uniformization.

Evidence: `git grep -nwE 'sorry|admit'` finds no occurrence in any `.lean` file except
in docstrings, and there are no `axiom`/`opaque`/`native_decide` declarations. The
validation script below builds with `lake build --wfail`, under which a `sorry` warning
fails the build.

### Theta function (Mochizuki, *The Étale Theta Function*, Prop. 1.4, classical content)

* Convergence: `thetaTerm_summable`; product form `thetaProd`.
* Quasi-periodicity: `theta_q_smul`, `theta_zpow_q_smul`.
* Inversion and oddness: `theta_inv`, `thetaOdd_inv`, `thetaOdd_q_smul`,
  `thetaOdd_eq_zero_iff` (for the odd theta `thetaOdd u = u · θ(-u²)`).
* Jacobi triple product, unconditional: `theta_eq_thetaProd` (via the Durfee-square identity
  `thetaProdNormConst_eq_one` and the Strassmann-type coefficient uniqueness
  `laurentCoeffUnique`).
* Zero divisor: `theta_eq_zero_iff` (`θ(u) = 0 ↔ u ∈ -qᶻ`), `thetaProd_eq_zero_iff`.

### Tate curve and `q`-uniformization (Silverman, *Advanced Topics*, V.3.1)

* Weierstrass identity, unconditional under `12 ≠ 0`: `tateDefect_eq_zero`,
  `tatePoint_mem'` (the Tate point `(X(u), Y(u))` lies on `E_q` for `u ∉ qᶻ`), proved by
  the Eisenstein pair-identity computation.
* Group law: `tatePoint_mul`, `tatePointHom` with `tatePointHom_ker = qᶻ`,
  `mapTatePointHom_injective`.
* Surjectivity and the isomorphism `Kˣ/qᶻ ≃* E_q(K)`: `tatePoint_surjective`,
  `mapTatePointHom_bijective`, `tateUniformization`. These take the Weierstrass identity
  as an argument `hmem`, which `tatePoint_mem'` discharges.

### The Tate `q`-parameter

* `j`-invariant: `tateJ`, `tateJ_eq_j`, `norm_tateJ` (`‖j(E_q)‖ = ‖q‖⁻¹`),
  `one_lt_norm_tateJ`.
* Characterization (`12 ≠ 0`): `tateJ_injective`, `exists_tateParameter_tateJ_eq`,
  `existsUnique_tateParameter_tateJ_eq`, and
  `existsUnique_splitMultiplicative_tateParameter` (each `j` with `‖j‖ > 1` has a unique
  Tate parameter, whose curve has split multiplicative reduction).
* Reduction: `tateCurveInt`, `isSplitMultiplicative_reduction`,
  `tateCurve_multiplicative_reduction`.
* Normalized order (IUT I, Def. 3.1(c)): `IsUniformizer`, `orderZ`, `toOrdered`
  (`OrderedTateParameter`).
* Base change along isometric extensions `L/K`: `baseChange`, `ord_baseChange`,
  `orderZ_baseChange`, `algebraMap_X`, `algebraMap_Y`, `map_tateCurve`, `algebraMap_tateJ`.

### Open / out of scope

* The classical converse "every curve over `K` with split multiplicative reduction is
  `K`-isomorphic to some `E_q`" (Silverman V.5.3, triviality of the quadratic twist) is not
  stated here; downstream (`iut`) builds the isomorphism from `tateJ` plus its own twist
  argument.
* The relation of theta values to continuous Kummer classes is not started.
* Anabelian rigidity claims of *The Étale Theta Function* are out of scope by design.
  This repository is also distinct from `elliptic-reduction` (reduction theory; an empty
  scaffold at present).

## Dependencies

Mathlib (`v4.32.0`) and, as a Lake dependency only,
[`formal-schemes`](https://github.com/lana-agents/formal-schemes) (pinned in
`lakefile.toml`). No file currently imports `FormalSchemes`; the integral model and the
special fibre are done concretely over the unit ball (`integerRing`, `integerIdeal`).

Intended links, not dependencies: the connection to Kummer classes is meant to use
[`continuous-kummer-theory`](https://github.com/lana-agents/continuous-kummer-theory), and
log-volumes [`padic-log-volume`](https://github.com/lana-agents/padic-log-volume). Both are
currently empty scaffold repositories and are not required in `lakefile.toml`.

## Use in `iut`

[`lana-agents/iut`](https://github.com/lana-agents/iut) pins this repository at
`ca6c227` and uses it to build the local Θ-data at the bad places (`Iut/Cor312/ThetaData/`,
`Iut/Concrete/`): existence and uniqueness of the Tate parameter from the `j`-invariant
(`exists_tateParameter_tateJ_eq`, `tateJ_injective`,
`existsUnique_splitMultiplicative_tateParameter`), the uniformization `tateUniformization`
with `tatePoint_mem'`, `TameResidueChar`, `IsUniformizer`/`toOrdered` for the normalized
order, and the base-change naturality `baseChange`, `algebraMap_X`, `algebraMap_Y`.

## Established sources

* Tate's `q`-uniformization; J. Tate, *A review of non-Archimedean elliptic functions*.
* Mumford, *An analytic construction of degenerating abelian varieties over complete rings*
  (appendix to Faltings–Chai).
* Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V.
* Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations*, Prop. 1.4.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`.
Library sources live under `TateCurvesTheta/`, and every file must be imported from
the root module `TateCurvesTheta.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib TateCurvesTheta --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#13](https://taxis.lana.merten.dev/issues/13), [#36](https://taxis.lana.merten.dev/issues/36), [#37](https://taxis.lana.merten.dev/issues/37)
