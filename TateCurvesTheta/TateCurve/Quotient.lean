/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.AnalyticQuotient
import TateCurvesTheta.QParameter.Basic

/-!
# Bridging the Tate parameter to the analytic quotient `Kˣ/qᶻ`

The project carries two closely-related data structures for the multiplicative Tate
parameter, both of which package a unit `q : Kˣ` with `‖q‖ < 1`:

* `TateCurvesTheta.TateDatum` (in `AnalyticQuotient.lean`) supports the group-theoretic
  `q`-uniformization layer: the subgroup `qᶻ`, the analytic quotient `Kˣ ⧸ qᶻ`, the
  projection `toAnalyticQuotient`, and the exact sequence / functoriality in
  `Uniformization.lean`.
* `TateCurvesTheta.TateParameter` (in `QParameter/Basic.lean`) carries the metric/order API
  and is the datum used by the Weierstrass model (`Weierstrass.lean`), the discriminant
  (`Discriminant.lean`) and the Tate coordinate series `X`, `Y` (`Parametrization.lean`).

This file reconciles the two by the forgetful bridge `TateParameter.toTateDatum`, which
re-exports the whole analytic-quotient API for a `TateParameter` without duplicating the
group-theoretic development. In particular `toAnalyticQuotient_q_mul` records the invariance
`[q·u] = [u]` in `Kˣ/qᶻ`, the descent principle that carries any `q`-periodic function on
`Kˣ` — such as the Tate coordinates `X`, `Y`, proved invariant under `u ↦ q·u` in
`Parametrization.lean` — down to the quotient.

Everything here is purely group-theoretic: no completeness or ultrametric hypothesis is
needed.

## Main definitions

* `TateCurvesTheta.TateParameter.toTateDatum`: the `TateDatum` underlying a `TateParameter`.
* `TateParameter.qpowers`, `TateParameter.AnalyticQuotient`, `TateParameter.toAnalyticQuotient`:
  the analytic-quotient API re-exported for a `TateParameter`.

## Main results

* `TateParameter.toAnalyticQuotient_q`: the Tate parameter is trivial in `Kˣ/qᶻ`.
* `TateParameter.toAnalyticQuotient_q_mul`: `[q·u] = [u]`, the descent principle for
  `q`-periodic functions.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter V.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] (t : TateParameter K)

/-- The **`TateDatum` underlying a `TateParameter`**: same unit `q`, same smallness `‖q‖ < 1`.
This forgetful bridge connects the metric parameter datum to the group-theoretic
`q`-uniformization layer, so the analytic-quotient API is available for a `TateParameter`
without duplicating it. -/
def toTateDatum : TateDatum K where
  q := t.q
  norm_q_lt_one := t.norm_lt_one

@[simp] lemma toTateDatum_q : t.toTateDatum.q = t.q := rfl

/-- The subgroup `qᶻ ≤ Kˣ` attached to a Tate parameter. -/
abbrev qpowers : Subgroup Kˣ := t.toTateDatum.qpowers

/-- The **Tate analytic quotient** `Kˣ / qᶻ` attached to a Tate parameter. -/
abbrev AnalyticQuotient := t.toTateDatum.AnalyticQuotient

/-- The natural projection `Kˣ → Kˣ / qᶻ` attached to a Tate parameter. -/
abbrev toAnalyticQuotient : Kˣ →* t.AnalyticQuotient := t.toTateDatum.toAnalyticQuotient

/-- The Tate parameter maps to the identity in the analytic quotient. -/
@[simp] lemma toAnalyticQuotient_q : t.toAnalyticQuotient t.q = 1 :=
  t.toTateDatum.toAnalyticQuotient_q

/-- **Descent principle.** Multiplying by the Tate parameter is invisible in the analytic
quotient: `[q·u] = [u]`. Consequently every `q`-periodic function on `Kˣ` (e.g. the Tate
coordinates `X`, `Y`, invariant under `u ↦ q·u`) descends to a function on `Kˣ/qᶻ`. -/
@[simp] lemma toAnalyticQuotient_q_mul (u : Kˣ) :
    t.toAnalyticQuotient (t.q * u) = t.toAnalyticQuotient u := by
  rw [map_mul, toAnalyticQuotient_q, one_mul]

end TateParameter

end TateCurvesTheta
