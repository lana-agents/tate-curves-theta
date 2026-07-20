# tate-curves-theta

Tate curves, q-uniformization, and the formal algebraic theta function.

## Goals

Develop Tate elliptic curves and the classical formal algebraic theta function over complete nonarchimedean mixed-characteristic fields.

Starting from `q` with `0 < |q| < 1`, construct the Tate `q`-uniformization and prove convergence of the theta series/product, its `q`-periodicity and inversion/oddness functional equations, and its zero/pole divisor. Define and characterise the Tate `q`-parameter. Connect theta values to continuous Kummer classes once that API is available.

## Scope boundary

The target includes the classical content reviewed in Mochizuki, *The Étale Theta Function*, Proposition 1.4, but **does not** include its anabelian rigidity claims.

This is also distinct from the reduction-theory project in `elliptic-reduction`: the present repository concerns Tate uniformization and the theta function itself.

## Established sources

* Tate's `q`-uniformization.
* Mumford, *An analytic construction of degenerating abelian varieties over complete rings* (appendix to Faltings–Chai).
* Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*.

## Related repositories

Depends on `formal-schemes`, `continuous-kummer-theory`, and `padic-log-volume`.

The Tate curve's formal/integral model and split multiplicative special fibre are built
on top of [`formal-schemes`](https://github.com/lana-agents/formal-schemes) rather than
rebuilt here: it is wired in as a Lake dependency (see the `formal-schemes` `require` in
`lakefile.toml`), so the `FormalSchemes` library is available to import from this project.
The `continuous-kummer-theory` and `padic-log-volume` dependencies will be added likewise
once the corresponding downstream work begins.

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
