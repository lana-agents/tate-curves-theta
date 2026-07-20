/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.Theta.Uniqueness
import TateCurvesTheta.Theta.Divisor

/-!
# The Jacobi triple product identity `theta = thetaProd` (reduction)

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the naive
`q`-theta series `theta` (`Theta/Basic.lean`) and its product form `thetaProd`
(`Theta/Product.lean`) satisfy the *same* `q`-periodicity functional equation
`f (q·u) = (q·u)⁻¹ · f u` (`theta_q_smul`, `thetaProd_q_smul`). The classical **Jacobi triple
product identity** asserts they are in fact equal:
```
theta t u = thetaProd t u   for every u : Kˣ.
```

This file closes the identity **modulo two precisely-stated inputs**, using the `q`-difference
uniqueness engine `TateParameter.const_of_qinvariant_laurent` of `Theta/Uniqueness.lean` (#119):

1. `LaurentCoeffUnique K` — the nonarchimedean coefficient-uniqueness principle, discharged for
   densely-normed `K` in `Theta/StrictDominant.lean` (#121) and, unconditionally, via the
   Strassmann route tracked by #122/#127.
2. `RatioLaurentRepr t` — the **residual analytic seam**: the ratio `theta / thetaProd` is
   represented by a convergent, `q`-invariant two-sided Laurent series. See the definition below
   for the precise statement and the remarks for why its `q`-invariance clause is carried as a
   hypothesis rather than derived here.

Given these, the engine forces the ratio's Laurent series to be a constant `c₀`, hence
`theta u = c₀ · thetaProd u` for **all** `u : Kˣ` (`theta_eq_const_mul_thetaProd`). A single
non-vanishing normalization value pins `c₀ = 1` and delivers the identity
(`theta_eq_thetaProd`), which in turn makes the series-theta divisor of `Theta/Divisor.lean`
(#88) unconditional (`theta_eq_zero_iff`).

## The residual seam `RatioLaurentRepr`

The one genuinely analytic step flagged in `Theta/Product.lean` is exhibiting the quotient
`theta u / thetaProd u` as a convergent two-sided Laurent series — the division of two
convergent products over the complete nonarchimedean field `K`. We package exactly what the
engine consumes:

* a coefficient family `c : ℤ → K`, summable on all of `Kˣ`;
* the factorization `theta u = (∑' n, cₙ uⁿ) · thetaProd u` for every `u : Kˣ`;
* the `q`-invariance of the series `∑' n, cₙ (q·u)ⁿ = ∑' n, cₙ uⁿ`.

The `q`-invariance is the *series-level* form of `TateParameter.thetaDiv_q_smul` (the ratio is
`q`-invariant because `theta` and `thetaProd` share the automorphy factor `(q·u)⁻¹`). It is
carried inside the seam rather than derived from `thetaDiv_q_smul` here because that lemma only
controls the ratio **off** the discrete zero locus `-qᶻ` of `thetaProd`; propagating the shift
relation across the zero locus to *all* of `Kˣ` needs the continuity of the Laurent series
together with the density of `Kˣ ∖ (-qᶻ)`, a topological input not yet in this tree. Both
clauses hold once the reciprocal `1 / thetaProd` is developed as a Laurent series (the deferred
analytic work); this file delivers the reusable reduction that consumes them.

## Main definitions

* `TateCurvesTheta.TateParameter.RatioLaurentRepr` : the residual analytic seam above.

## Main results

* `TateParameter.theta_eq_const_mul_thetaProd` : given `LaurentCoeffUnique K` and
  `RatioLaurentRepr t`, there is a constant `c₀` with `theta u = c₀ · thetaProd u` for all `u`.
* `TateParameter.theta_eq_thetaProd` : with, in addition, one normalization value
  (`theta u₀ = thetaProd u₀` at a point `u₀` where `thetaProd u₀ ≠ 0`), `theta = thetaProd`.
* `TateParameter.theta_eq_zero_iff` : consequently the series-theta divisor is the `qᶻ`-orbit of
  `-1`, unconditionally on the `theta = thetaProd` seam (only on the two inputs above).

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.4 (Jacobi triple product via the
  functional-equation uniqueness argument).
* S. Mochizuki, *The Étale Theta Function*, §1, Proposition 1.4.
-/

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- **The residual analytic seam for the triple product identity.** The ratio
`theta / thetaProd` is represented by a convergent, `q`-invariant two-sided Laurent series:
there is a coefficient family `c : ℤ → K` that is summable on all of `Kˣ`, factorizes
`theta u = (∑' n, cₙ uⁿ) · thetaProd u` for every `u`, and whose series is `q`-invariant
(`∑' n, cₙ (q·u)ⁿ = ∑' n, cₙ uⁿ`).

This is the "division of two convergent products" step flagged in `Theta/Product.lean`; see the
module docstring for why the `q`-invariance clause is included here. It is exactly the shape
consumed by `const_of_qinvariant_laurent`. -/
def RatioLaurentRepr : Prop :=
  ∃ c : ℤ → K,
    (∀ u : Kˣ, Summable fun n : ℤ => c n * (u : K) ^ n) ∧
    (∀ u : Kˣ, t.theta u = (∑' n : ℤ, c n * (u : K) ^ n) * t.thetaProd u) ∧
    (∀ u : Kˣ,
      (∑' n : ℤ, c n * ((t.q : K) * (u : K)) ^ n) = ∑' n : ℤ, c n * (u : K) ^ n)

/-- **The ratio `theta / thetaProd` is a global constant.** Given the coefficient-uniqueness
principle `LaurentCoeffUnique K` and the Laurent representation of the ratio
(`RatioLaurentRepr t`), the `q`-difference engine `const_of_qinvariant_laurent` collapses the
representing series to its constant term `c₀ := c 0`, so `theta u = c₀ · thetaProd u` for every
`u : Kˣ`. -/
theorem theta_eq_const_mul_thetaProd (huniq : LaurentCoeffUnique K) (hrepr : t.RatioLaurentRepr) :
    ∃ c₀ : K, ∀ u : Kˣ, t.theta u = c₀ * t.thetaProd u := by
  obtain ⟨c, hsum, hid, hqinv⟩ := hrepr
  -- The engine forces the representing series to equal its constant term `c 0` everywhere.
  have hconst : ∀ u : Kˣ, (∑' n : ℤ, c n * (u : K) ^ n) = c 0 :=
    t.const_of_qinvariant_laurent huniq c hsum hqinv
  refine ⟨c 0, fun u => ?_⟩
  rw [hid u, hconst u]

/-- **The Jacobi triple product identity `theta = thetaProd`.** Beyond the coefficient-uniqueness
principle and the ratio's Laurent representation, all that is needed is a single normalization:
one point `u₀` where `thetaProd u₀ ≠ 0` and `theta u₀ = thetaProd u₀`. This pins the constant
`c₀` of `theta_eq_const_mul_thetaProd` to `1`, giving `theta u = thetaProd u` for every `u`
(including the zero locus `-qᶻ`, where both sides vanish, since the factorization is stated for
all `u`). -/
theorem theta_eq_thetaProd (huniq : LaurentCoeffUnique K) (hrepr : t.RatioLaurentRepr)
    {u₀ : Kˣ} (hu₀ : t.thetaProd u₀ ≠ 0) (hnorm : t.theta u₀ = t.thetaProd u₀) (u : Kˣ) :
    t.theta u = t.thetaProd u := by
  obtain ⟨c₀, hc₀⟩ := t.theta_eq_const_mul_thetaProd huniq hrepr
  -- Normalize: `c₀ · thetaProd u₀ = theta u₀ = thetaProd u₀`, so `thetaProd u₀ ≠ 0` gives `c₀ = 1`.
  have hc1 : c₀ = 1 := by
    have h := hc₀ u₀
    rw [hnorm] at h
    have h' : (c₀ - 1) * t.thetaProd u₀ = 0 := by ring_nf; linear_combination -h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact sub_eq_zero.mp h''
    · exact absurd h'' hu₀
  rw [hc₀ u, hc1, one_mul]

/-- **The zero divisor of the naive series `theta`, unconditionally on the identity seam.** Given
the coefficient-uniqueness principle, the ratio's Laurent representation, and the single
normalization value, the series `theta` vanishes exactly on the `qᶻ`-orbit of `-1`:
`theta u = 0 ↔ ∃ k : ℤ, (u : K) = -qᵏ`. This discharges the conditionality of
`theta_eq_zero_iff_of_eq_thetaProd` (`Theta/Divisor.lean`, #88). -/
theorem theta_eq_zero_iff [CompleteSpace K] (huniq : LaurentCoeffUnique K)
    (hrepr : t.RatioLaurentRepr) {u₀ : Kˣ} (hu₀ : t.thetaProd u₀ ≠ 0)
    (hnorm : t.theta u₀ = t.thetaProd u₀) (u : Kˣ) :
    t.theta u = 0 ↔ ∃ k : ℤ, (u : K) = -(t.q : K) ^ k :=
  t.theta_eq_zero_iff_of_eq_thetaProd u (t.theta_eq_thetaProd huniq hrepr hu₀ hnorm u)

end TateParameter

end TateCurvesTheta
