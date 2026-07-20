/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.Filter.AtTopBot.Ring
import TateCurvesTheta.QParameter.Basic

/-!
# The naive `q`-theta series of the Tate curve and its convergence

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the *naive
`q`-theta series* is the two-sided Laurent series in a unit `u : Kˣ`
```
θ q u = ∑' n : ℤ, q ^ (e n) * u ^ n,   e n = n * (n + 1) / 2,
```
where `e n` is the `n`-th triangular number. The key features of `e` are that it is a
*nonnegative* integer for every `n : ℤ` (`thetaExp_nonneg`, so `q ^ (e n)` is an honest
nonnegative power of the small element `q`) and that it grows *quadratically*
(`2 * e n = n * (n + 1)`, `thetaExp_cast`).

This file fixes the normalization — the **unsigned** series above, the cleanest convergence
target — and proves that the family `n ↦ q ^ (e n) * u ^ n` is unconditionally `Summable`.
The functional equations of `θ` (`q`-periodicity, inversion) and its divisor build on the
normalization chosen here and are developed in sibling files.

## Convergence

Convergence needs two hypotheses beyond the metric datum of a `TateParameter`: completeness
(`[CompleteSpace K]`) and the nonarchimedean/ultrametric triangle inequality
(`[IsUltrametricDist K]`). These specialize the general `TateParameter` base field and are
added locally, matching the seam-style of `QParameter/BaseChange.lean`. In a complete
nonarchimedean additive group a family is summable as soon as its terms tend to zero along
the cofinite filter (`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`), and the
term norm here is
```
‖q ^ (e n) * u ^ n‖ = ‖q‖ ^ (e n) * ‖u‖ ^ n = exp (log‖q‖ · e n + log‖u‖ · n),
```
whose exponent is a downward quadratic in `n` (leading coefficient `log‖q‖ / 2 < 0`), hence
tends to `-∞` on both `atBot` and `atTop`, i.e. on all of `cofinite = atBot ⊔ atTop`. This
two-sided decay of the term norm is the analytic core.

## Main definitions

* `TateCurvesTheta.thetaExp` : the triangular exponent `e n = n * (n + 1) / 2`.
* `TateCurvesTheta.TateParameter.thetaTerm` : the general term `q ^ (e n) * u ^ n`.
* `TateCurvesTheta.TateParameter.theta` : the naive `q`-theta function `∑' n, thetaTerm n`.

## Main results

* `thetaExp_nonneg`, `two_mul_thetaExp`, `thetaExp_cast` : basic facts about the triangular
  exponent, reused by the functional-equation files.
* `TateParameter.thetaTerm_summable` : the theta family is `Summable` over a complete
  nonarchimedean field.
* `TateParameter.theta_apply` : the defining `tsum` unfolding of `theta`.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter V.
* S. Mochizuki, *The Étale Theta Function*, §1, Proposition 1.4.
-/

open Filter Topology

namespace TateCurvesTheta

/-- The **triangular exponent** `e n = n * (n + 1) / 2` appearing in the `q`-theta series.
The integer division is exact because `n * (n + 1)` is even (`two_mul_thetaExp`). -/
def thetaExp (n : ℤ) : ℤ := n * (n + 1) / 2

/-- The triangular exponent doubles to the product of consecutive integers: `2 * e n = n*(n+1)`.
The division in `thetaExp` is therefore exact. -/
lemma two_mul_thetaExp (n : ℤ) : 2 * thetaExp n = n * (n + 1) := by
  have h : (2 : ℤ) ∣ n * (n + 1) := (Int.even_mul_succ_self n).two_dvd
  rw [thetaExp, Int.mul_ediv_cancel' h]

/-- The triangular exponent is nonnegative for every integer `n`, so `q ^ (e n)` is a genuine
nonnegative power of `q`. -/
lemma thetaExp_nonneg (n : ℤ) : 0 ≤ thetaExp n := by
  have h2 : 2 * thetaExp n = n * (n + 1) := two_mul_thetaExp n
  have hnn : 0 ≤ n * (n + 1) := by
    by_cases h : 0 ≤ n
    · exact mul_nonneg h (by omega)
    · have key : (0 : ℤ) ≤ (-n) * (-(n + 1)) := mul_nonneg (by omega) (by omega)
      nlinarith [key]
  omega

/-- The real cast of the triangular exponent as a quadratic: `(e n : ℝ) = n * (n + 1) / 2`. -/
lemma thetaExp_cast (n : ℤ) : (thetaExp n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  have h : (2 : ℝ) * (thetaExp n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) := by
    exact_mod_cast two_mul_thetaExp n
  linarith

namespace TateParameter

variable {K : Type*} [NormedField K]

/-- The general term `q ^ (e n) * u ^ n` of the naive `q`-theta series, indexed by `n : ℤ`. -/
noncomputable def thetaTerm (T : TateParameter K) (u : Kˣ) (n : ℤ) : K :=
  (T.q : K) ^ (thetaExp n) * (u : K) ^ n

/-- The **naive `q`-theta function** `θ q u = ∑' n : ℤ, q ^ (e n) * u ^ n` (unsigned
normalization). Over a complete nonarchimedean field the series converges
(`thetaTerm_summable`). -/
noncomputable def theta (T : TateParameter K) (u : Kˣ) : K :=
  ∑' n : ℤ, T.thetaTerm u n

/-- The defining unfolding of the `q`-theta function as a `tsum`. -/
lemma theta_apply (T : TateParameter K) (u : Kˣ) :
    T.theta u = ∑' n : ℤ, (T.q : K) ^ (thetaExp n) * (u : K) ^ n :=
  rfl

/-- **Convergence of the naive `q`-theta series.** Over a complete nonarchimedean field, the
family `n ↦ q ^ (e n) * u ^ n` is unconditionally summable: the term norm
`‖q‖ ^ (e n) * ‖u‖ ^ n` decays to zero as `|n| → ∞` because the triangular exponent `e n`
grows quadratically while `0 < ‖q‖ < 1`. -/
theorem thetaTerm_summable [CompleteSpace K] [IsUltrametricDist K]
    (T : TateParameter K) (u : Kˣ) : Summable (T.thetaTerm u) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ha : 0 < ‖(T.q : K)‖ := T.norm_q_pos
  have hb : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  -- The term norm is `exp` of a downward quadratic in `n`.
  have hnorm : (fun n : ℤ => ‖T.thetaTerm u n‖)
      = fun n : ℤ =>
        Real.exp (Real.log ‖(T.q : K)‖ * (thetaExp n : ℝ) + Real.log ‖(u : K)‖ * (n : ℝ)) := by
    funext n
    rw [thetaTerm, norm_mul, norm_zpow, norm_zpow,
      ← Real.rpow_intCast ‖(T.q : K)‖ (thetaExp n), ← Real.rpow_intCast ‖(u : K)‖ n,
      Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, ← Real.exp_add]
  -- The exponent tends to `-∞` along the cofinite filter, so `exp` of it tends to `0`.
  have hg : Tendsto
      (fun n : ℤ => Real.log ‖(T.q : K)‖ * (thetaExp n : ℝ) + Real.log ‖(u : K)‖ * (n : ℝ))
      cofinite atBot := by
    have hLa2 : Real.log ‖(T.q : K)‖ / 2 < 0 := by
      have := Real.log_neg ha T.norm_lt_one
      linarith
    have hfac :
        (fun n : ℤ =>
            Real.log ‖(T.q : K)‖ * (thetaExp n : ℝ) + Real.log ‖(u : K)‖ * (n : ℝ))
          = fun n : ℤ =>
            (n : ℝ) * ((Real.log ‖(T.q : K)‖ / 2 + Real.log ‖(u : K)‖)
              + Real.log ‖(T.q : K)‖ / 2 * (n : ℝ)) := by
      funext n
      rw [thetaExp_cast]
      ring
    rw [hfac, Int.cofinite_eq, tendsto_sup]
    refine ⟨?_, ?_⟩
    · exact Tendsto.atBot_mul_atTop₀ (tendsto_intCast_atBot_iff.2 tendsto_id)
        (Tendsto.add_atTop tendsto_const_nhds
          (Tendsto.const_mul_atBot_of_neg hLa2 (tendsto_intCast_atBot_iff.2 tendsto_id)))
    · exact Tendsto.atTop_mul_atBot₀ tendsto_intCast_atTop_atTop
        (Tendsto.add_atBot tendsto_const_nhds
          (Tendsto.const_mul_atTop_of_neg hLa2 tendsto_intCast_atTop_atTop))
  rw [hnorm]
  exact Real.tendsto_exp_atBot.comp hg

end TateParameter

end TateCurvesTheta
