/-
Copyright (c) 2026 The TateCurvesTheta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The TateCurvesTheta contributors
-/
import TateCurvesTheta.AnalyticQuotient

/-!
# The Tate uniformization short exact sequence

Building on `TateCurvesTheta/AnalyticQuotient.lean`, this file records the basic
homological data of Tate's `q`-uniformization at the level of the analytic torus.

Fix a Tate datum `T = (q, ‖q‖ < 1)` over a complete nonarchimedean field `K`.  The
projection `Kˣ → Kˣ / qᶻ` fits into the short exact sequence
`1 → qᶻ → Kˣ → Kˣ / qᶻ → 1`, and two points of `Kˣ` become equal in the analytic
quotient exactly when they differ by an integer power of `q`.  These facts are the
group-theoretic shadow of the analytic isomorphism `Kˣ / qᶻ ≃ E_q(K)`, and are what
downstream files (the Weierstrass model, functoriality, and the Kummer/theta theory)
consume from the quotient.

## Main results

* `TateDatum.toAnalyticQuotient_surjective` : the projection `Kˣ → Kˣ / qᶻ` is
  surjective.
* `TateDatum.ker_toAnalyticQuotient` : its kernel is exactly `qᶻ`.  Together with
  surjectivity this is the short exact sequence `1 → qᶻ → Kˣ → Kˣ / qᶻ → 1`.
* `TateDatum.toAnalyticQuotient_eq_iff` : `a` and `b` have the same image iff
  `a / b` is an integer power of `q` — the fundamental `q`-congruence relation.
* `TateDatum.toAnalyticQuotient_mul_zpow` : the projection is invariant under
  multiplication by `qⁿ`, i.e. `qᶻ`-periodicity of the uniformization.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter V.
-/

namespace TateCurvesTheta

namespace TateDatum

variable {K : Type*} [NormedField K] (T : TateDatum K)

/-- The projection `Kˣ → Kˣ / qᶻ` onto the Tate analytic quotient is surjective. -/
lemma toAnalyticQuotient_surjective : Function.Surjective T.toAnalyticQuotient :=
  QuotientGroup.mk'_surjective T.qpowers

/-- The kernel of the projection `Kˣ → Kˣ / qᶻ` is exactly the subgroup `qᶻ`.

Combined with `toAnalyticQuotient_surjective`, this expresses the Tate
uniformization short exact sequence `1 → qᶻ → Kˣ → Kˣ / qᶻ → 1`. -/
lemma ker_toAnalyticQuotient : T.toAnalyticQuotient.ker = T.qpowers :=
  QuotientGroup.ker_mk' T.qpowers

/-- Two units of `K` have the same image in the analytic quotient `Kˣ / qᶻ` if and
only if their ratio is an integer power of the Tate parameter `q`.  This is the
fundamental `q`-congruence relation underlying the uniformization. -/
lemma toAnalyticQuotient_eq_iff {a b : Kˣ} :
    T.toAnalyticQuotient a = T.toAnalyticQuotient b ↔ ∃ n : ℤ, T.q ^ n = a / b := by
  rw [toAnalyticQuotient, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_iff_div_mem]
  exact Subgroup.mem_zpowers_iff

/-- The projection `Kˣ → Kˣ / qᶻ` is invariant under multiplication by an integer
power of `q`: the uniformization is `qᶻ`-periodic. -/
@[simp] lemma toAnalyticQuotient_mul_zpow (a : Kˣ) (n : ℤ) :
    T.toAnalyticQuotient (a * T.q ^ n) = T.toAnalyticQuotient a := by
  rw [map_mul, map_zpow, toAnalyticQuotient_q, one_zpow, mul_one]

/-- Points differing by a single factor of `q` agree in the analytic quotient. -/
lemma toAnalyticQuotient_mul_q (a : Kˣ) :
    T.toAnalyticQuotient (a * T.q) = T.toAnalyticQuotient a := by
  simp

end TateDatum

end TateCurvesTheta
