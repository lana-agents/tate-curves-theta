/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import TateCurvesTheta.Theta.Basic

/-!
# The `q`-periodicity (quasi-periodicity) functional equation of the `q`-theta function

For a Tate parameter `q` over a nonarchimedean field `K`, the naive `q`-theta series
`θ q u = ∑' n : ℤ, q ^ (e n) * u ^ n` (with `e n = n * (n + 1) / 2` the triangular exponent,
fixed in `TateCurvesTheta.Theta.Basic`) is *not* invariant under the `qᶻ`-action `u ↦ q · u`;
instead it transforms by an explicit monomial automorphy factor. This quasi-periodicity is
exactly what makes `θ` a section of a line bundle on `E_q = Kˣ/qᶻ` rather than a genuine
function on the quotient.

## Main results

* `TateCurvesTheta.thetaExp_add` : `e (m + n) = e m + e n + m * n`, the quadratic identity
  driving the index shift.
* `TateCurvesTheta.TateParameter.theta_zpow_smul_eq` : the reindexing identity
  `θ q u = q ^ (e m) * u ^ m * θ q (qᵐ · u)`.
* `TateCurvesTheta.TateParameter.theta_zpow_q_smul` : the full `qᶻ`-automorphy
  `θ q (qᵐ · u) = (q ^ (e m) * u ^ m)⁻¹ * θ q u` for every `m : ℤ`.
* `TateCurvesTheta.TateParameter.theta_q_smul` : the single-shift functional equation
  `θ q (q · u) = (q · u)⁻¹ * θ q u`.

The identities hold over any `NormedField` (they are purely formal reindexings of the
defining `tsum`, valid via the division-ring `tsum_mul_left` even when the series fails to
converge, in which case both sides vanish); convergence of `θ` itself is the content of
`Theta.Basic`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter V.
* S. Mochizuki, *The Étale Theta Function*, §1, Proposition 1.4.
-/

namespace TateCurvesTheta

/-- The triangular exponent is quasi-additive: `e (m + n) = e m + e n + m * n`. This is the
combinatorial identity behind the `q`-periodicity of the theta series. -/
lemma thetaExp_add (m n : ℤ) : thetaExp (m + n) = thetaExp m + thetaExp n + m * n := by
  have h2 : (2 : ℤ) * thetaExp (m + n) = 2 * (thetaExp m + thetaExp n + m * n) := by
    have h := two_mul_thetaExp (m + n)
    have hm := two_mul_thetaExp m
    have hn := two_mul_thetaExp n
    linear_combination h - hm - hn
  linarith

/-- The triangular exponent at `1` is `1`. -/
lemma thetaExp_one : thetaExp 1 = 1 := by decide

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (T : TateParameter K)

/-- **Reindexing identity for the `q`-theta series.** Shifting the summation index by `m`
peels off the monomial `q ^ (e m) * u ^ m`:
`θ q u = q ^ (e m) * u ^ m * θ q (qᵐ · u)`.

This is the source of the quasi-periodicity; it is a formal reindexing of the defining
`tsum` (via `Equiv.addRight` and the quadratic identity `thetaExp_add`) and needs no
convergence hypotheses. -/
theorem theta_zpow_smul_eq (u : Kˣ) (m : ℤ) :
    T.theta u = (T.q : K) ^ thetaExp m * (u : K) ^ m * T.theta (T.q ^ m * u) := by
  have hq : (T.q : K) ≠ 0 := T.q.ne_zero
  have hu : (u : K) ≠ 0 := u.ne_zero
  simp only [theta]
  rw [← Equiv.tsum_eq (Equiv.addRight m) (T.thetaTerm u)]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  simp only [thetaTerm, Equiv.coe_addRight, Units.val_mul, Units.val_zpow_eq_zpow_val]
  rw [thetaExp_add n m, mul_zpow, ← zpow_mul, zpow_add₀ hq, zpow_add₀ hq, zpow_add₀ hu,
    mul_comm n m]
  ring

/-- **The full `qᶻ`-automorphy of the `q`-theta function.** For every `m : ℤ`,
`θ q (qᵐ · u) = (q ^ (e m) * u ^ m)⁻¹ * θ q u`, with the automorphy factor the reciprocal of
the theta monomial `q ^ (e m) * u ^ m`. -/
theorem theta_zpow_q_smul (u : Kˣ) (m : ℤ) :
    T.theta (T.q ^ m * u) = ((T.q : K) ^ thetaExp m * (u : K) ^ m)⁻¹ * T.theta u := by
  have hq : (T.q : K) ≠ 0 := T.q.ne_zero
  have hu : (u : K) ≠ 0 := u.ne_zero
  have hC : (T.q : K) ^ thetaExp m * (u : K) ^ m ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hq) (zpow_ne_zero _ hu)
  rw [T.theta_zpow_smul_eq u m, ← mul_assoc, inv_mul_cancel₀ hC, one_mul]

/-- **The `q`-periodicity functional equation.** Under the generating translation `u ↦ q · u`
the `q`-theta function transforms by the automorphy factor `(q · u)⁻¹`:
`θ q (q · u) = (q · u)⁻¹ * θ q u`. -/
theorem theta_q_smul (u : Kˣ) :
    T.theta (T.q * u) = ((T.q : K) * (u : K))⁻¹ * T.theta u := by
  have h := T.theta_zpow_q_smul u 1
  simpa only [zpow_one, thetaExp_one] using h

end TateParameter

end TateCurvesTheta
