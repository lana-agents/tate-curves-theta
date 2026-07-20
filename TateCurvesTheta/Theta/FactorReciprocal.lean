/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import TateCurvesTheta.Theta.FactorSeries

/-!
# The reciprocal power series of the elementary theta factor on the unit ball

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the elementary
theta factor `thetaProdFactor c = ∏' n : ℕ, (1 + qⁿ · c)` (see `Theta/Product.lean`) is a unit on
the open unit ball `‖c‖ < 1`, with reciprocal a convergent power series
```
1 / thetaProdFactor c = ∑' k, F k · cᵏ    (‖c‖ < 1),
```
where the coefficients `F k` are the **Cauchy inverse** of the Euler `q`-binomial coefficients
`E k = factorCoeff` (`Theta/FactorSeries.lean`), determined by `F 0 = 1` and the recursion
`F (n+1) = -∑_{k ≤ n} E (k+1) · F (n-k)`.

The restriction `‖c‖ < 1` is essential: `thetaProdFactor` vanishes exactly on `c ∈ -qᶻ`
(`thetaProdFactor_eq_zero_iff` in `Theta/Divisor.lean`), the nearest zero being `c = -1` with
`‖c‖ = 1`, so the reciprocal has radius of convergence exactly `1`.

## Strategy

The coefficient recursion is engineered so that the discrete convolution of `E` with `F` is the
Kronecker delta at `0` (`factorCoeff_recipCoeff_convolution`). Both power series are **absolutely**
summable on `‖c‖ < 1` (their coefficients are norm-bounded by `1`, so the term norms are dominated
by the geometric series `‖c‖ᵏ`); hence the classical Cauchy product
`tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm` applies and collapses to `1` via the
convolution identity — no nonarchimedean `NonarchimedeanRing` Cauchy product is needed.

## Main definitions

* `TateCurvesTheta.TateParameter.recipCoeff` : the reciprocal coefficients `F k`.

## Main results

* `TateParameter.recipCoeff_zero` : `F 0 = 1`.
* `TateParameter.norm_recipCoeff_le_one` : `‖F k‖ ≤ 1`.
* `TateParameter.recipCoeff_summable` : the reciprocal series `∑ F k cᵏ` converges for `‖c‖ < 1`.
* `TateParameter.thetaProdFactor_mul_tsum_recipCoeff` : the reciprocal identity
  `thetaProdFactor c · ∑' k, F k cᵏ = 1` for `‖c‖ < 1`.

## References

* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.2 (Euler's `q`-binomial theorem).
* A. Robert, *A Course in p-adic Analysis*, §6 (convergent series; units `1 + x` with `‖x‖ < 1`).
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

open Filter Topology Finset

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- The **reciprocal coefficients** of the elementary theta factor: the Cauchy inverse of the
Euler `q`-binomial coefficients `factorCoeff`. Defined by `F 0 = 1` and the recursion
`F (n+1) = -∑_{k < n+1} E (k+1) · F (n-k)`, which is exactly the vanishing of the convolution
`∑_{i+j = m} E i · F j` for `m ≥ 1`. -/
noncomputable def recipCoeff (t : TateParameter K) : ℕ → K
  | 0 => 1
  | (n + 1) => -∑ k ∈ Finset.range (n + 1), t.factorCoeff (k + 1) * recipCoeff t (n - k)
  decreasing_by exact Nat.lt_succ_of_le (Nat.sub_le n k)

@[simp] lemma recipCoeff_zero : recipCoeff t 0 = 1 := by rw [recipCoeff]

lemma recipCoeff_succ (n : ℕ) :
    recipCoeff t (n + 1)
      = -∑ k ∈ Finset.range (n + 1), t.factorCoeff (k + 1) * recipCoeff t (n - k) := by
  rw [recipCoeff]

/-- **Every reciprocal coefficient has norm at most one.** By strong induction: the constant term
is `1`, and each `F (n+1)` is (minus) an ultrametric finite sum of products `E (k+1) · F (n-k)`,
whose norms are `≤ 1` since `‖E (k+1)‖ ≤ 1` and `‖F (n-k)‖ ≤ 1` (induction hypothesis). -/
lemma norm_recipCoeff_le_one [IsUltrametricDist K] (n : ℕ) : ‖recipCoeff t n‖ ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | (m + 1) =>
      rw [recipCoeff_succ, norm_neg]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) fun k _ => ?_
      rw [norm_mul]
      have h2 : ‖recipCoeff t (m - k)‖ ≤ 1 := ih (m - k) (Nat.lt_succ_of_le (Nat.sub_le m k))
      calc ‖t.factorCoeff (k + 1)‖ * ‖recipCoeff t (m - k)‖
          ≤ 1 * 1 :=
            mul_le_mul (t.norm_factorCoeff_le_one (k + 1)) h2 (norm_nonneg _) (by norm_num)
        _ = 1 := one_mul 1

/-- **Absolute summability of the `q`-binomial power series on the unit ball.** For `‖c‖ < 1` the
term norms `‖E k cᵏ‖ = ‖E k‖·‖c‖ᵏ ≤ ‖c‖ᵏ` are dominated by the convergent geometric series. -/
lemma summable_norm_factorCoeff_mul_pow [IsUltrametricDist K] {c : K} (hc : ‖c‖ < 1) :
    Summable (fun k : ℕ => ‖factorCoeff t k * c ^ k‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    (summable_geometric_of_lt_one (norm_nonneg c) hc)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg c) k) (t.norm_factorCoeff_le_one k)

/-- **Absolute summability of the reciprocal power series on the unit ball.** As above, using
`‖F k‖ ≤ 1`. -/
lemma summable_norm_recipCoeff_mul_pow [IsUltrametricDist K] {c : K} (hc : ‖c‖ < 1) :
    Summable (fun k : ℕ => ‖recipCoeff t k * c ^ k‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    (summable_geometric_of_lt_one (norm_nonneg c) hc)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg c) k) (t.norm_recipCoeff_le_one k)

/-- The reciprocal power series `∑ F k cᵏ` converges for every `c` on the open unit ball. -/
lemma recipCoeff_summable [CompleteSpace K] [IsUltrametricDist K] {c : K} (hc : ‖c‖ < 1) :
    Summable (fun k : ℕ => recipCoeff t k * c ^ k) :=
  (t.summable_norm_recipCoeff_mul_pow hc).of_norm

/-- **The Cauchy convolution of `E` and `F` is the Kronecker delta at `0`.** This is the defining
property of the reciprocal coefficients: `∑_{k ≤ n} E k · F (n-k) = 1` if `n = 0` and `0`
otherwise. The `n ≥ 1` case is the recursion `recipCoeff_succ` after peeling the `k = 0` term. -/
lemma factorCoeff_recipCoeff_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), t.factorCoeff k * recipCoeff t (n - k)
      = if n = 0 then 1 else 0 := by
  match n with
  | 0 => simp
  | (m + 1) =>
    rw [if_neg (Nat.succ_ne_zero m),
      Finset.sum_range_succ' (fun k => t.factorCoeff k * recipCoeff t (m + 1 - k)) (m + 1)]
    simp only [factorCoeff_zero, one_mul, Nat.sub_zero, Nat.succ_sub_succ]
    rw [recipCoeff_succ]
    exact add_neg_cancel _

/-- **The reciprocal identity on the unit ball.** For `‖c‖ < 1`,
```
thetaProdFactor c · (∑' k, F k cᵏ) = 1,
```
so `∑' k, F k cᵏ` is the reciprocal `1 / thetaProdFactor c`. The proof rewrites `thetaProdFactor c`
as the Euler `q`-binomial series (`thetaProdFactor_eq_tsum`), forms the absolutely convergent Cauchy
product with the reciprocal series, and collapses each Cauchy coefficient via
`factorCoeff_recipCoeff_convolution`, leaving only the constant term `1`. -/
theorem thetaProdFactor_mul_tsum_recipCoeff [CompleteSpace K] [IsUltrametricDist K]
    {c : K} (hc : ‖c‖ < 1) :
    t.thetaProdFactor c * ∑' k : ℕ, recipCoeff t k * c ^ k = 1 := by
  rw [t.thetaProdFactor_eq_tsum c,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
      (t.summable_norm_factorCoeff_mul_pow hc) (t.summable_norm_recipCoeff_mul_pow hc)]
  have hterm : ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + 1),
        factorCoeff t k * c ^ k * (recipCoeff t (n - k) * c ^ (n - k)))
        = (if n = 0 then 1 else 0) * c ^ n := by
    intro n
    rw [← t.factorCoeff_recipCoeff_convolution n, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hpow : c ^ k * c ^ (n - k) = c ^ n := by
      rw [← pow_add, Nat.add_sub_cancel' hk]
    rw [← hpow]; ring
  rw [tsum_congr hterm, tsum_eq_single 0 fun n hn => by rw [if_neg hn]; ring]
  simp

end TateParameter

end TateCurvesTheta
