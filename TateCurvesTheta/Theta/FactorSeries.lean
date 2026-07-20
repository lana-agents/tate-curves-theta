/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import TateCurvesTheta.Theta.Product

/-!
# The Euler `q`-binomial power series expansion of the elementary theta factor

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the elementary
theta factor `thetaProdFactor c = ∏' n : ℕ, (1 + qⁿ · c)` (see `Theta/Product.lean`) admits a
convergent power series expansion in `c`,
```
∏' n, (1 + qⁿ · c) = ∑' k, E k · cᵏ,
```
where the coefficients `E k` are the **Euler `q`-binomial coefficients**, determined by the
recursion `E 0 = 1`, `(1 - q^(k+1)) · E (k+1) = qᵏ · E k`. This is the nonarchimedean analogue of
Euler's classical identity `∏ (1 + qⁿ x) = ∑ q^{k(k-1)/2} / ((1-q)⋯(1-qᵏ)) · xᵏ`.

## Strategy

The proof is by the functional-equation/uniqueness method, avoiding any Cauchy product. Writing
`S c = ∑' k, E k · cᵏ`:

* the coefficient recursion is engineered so that `S` satisfies the *same* functional equation
  `S c = (1 + c) · S (q · c)` as `thetaProdFactor` (`tsum_factorCoeff_eq`);
* iterating peels off the finite partial product, `S c = (∏ n < N, (1 + qⁿ c)) · S (q^N c)`
  (`tsum_factorCoeff_eq_prod_mul`);
* letting `N → ∞`, the partial products converge to `thetaProdFactor c` and `S (q^N c) → S 0 = 1`
  because `q^N c → 0` and `‖S x - 1‖ ≤ ‖x‖` on the unit ball (`norm_tsum_sub_one_le`).

Uniqueness of limits closes the identity (`thetaProdFactor_eq_tsum`).

## Main definitions

* `TateCurvesTheta.TateParameter.factorCoeff` : the Euler `q`-binomial coefficients `E k`.

## Main results

* `TateParameter.norm_factorCoeff` : `‖E k‖ = ‖q‖ ^ (k * (k - 1) / 2)`.
* `TateParameter.factorCoeff_summable` : the power series `∑ E k cᵏ` converges for every `c`.
* `TateParameter.tsum_factorCoeff_eq` : the series functional equation
  `∑ E k cᵏ = (1 + c) · ∑ E k (q c)ᵏ`.
* `TateParameter.thetaProdFactor_eq_tsum` : the expansion `thetaProdFactor c = ∑' k, E k cᵏ`.

## References

* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.2 (Euler's `q`-binomial theorem).
* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter V.
-/

open Filter Topology Finset

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- The **Euler `q`-binomial coefficients** of the elementary theta factor, defined by the
recursion `E 0 = 1` and `E (k+1) = qᵏ · (1 - q^(k+1))⁻¹ · E k`. Equivalently
`(1 - q^(k+1)) · E (k+1) = qᵏ · E k`; this is exactly the coefficient recursion forced by the
functional equation `S c = (1 + c) · S (q c)` of the power series `S c = ∑' k, E k cᵏ`. -/
noncomputable def factorCoeff (t : TateParameter K) : ℕ → K
  | 0 => 1
  | (k + 1) => (t.q : K) ^ k * (1 - (t.q : K) ^ (k + 1))⁻¹ * factorCoeff t k

@[simp] lemma factorCoeff_zero : factorCoeff t 0 = 1 := rfl

lemma factorCoeff_succ (k : ℕ) :
    factorCoeff t (k + 1) = (t.q : K) ^ k * (1 - (t.q : K) ^ (k + 1))⁻¹ * factorCoeff t k := rfl

/-- **Isosceles-triangle estimate for the denominators.** In an ultrametric field `‖1‖ = 1`
strictly dominates `‖q^(k+1)‖ = ‖q‖^(k+1) < 1`, so `‖1 - q^(k+1)‖ = max 1 ‖q^(k+1)‖ = 1`. -/
lemma norm_one_sub_qpow [IsUltrametricDist K] (k : ℕ) :
    ‖(1 : K) - (t.q : K) ^ (k + 1)‖ = 1 := by
  have hlt : ‖(t.q : K) ^ (k + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) t.norm_lt_one (Nat.succ_ne_zero k)
  have hne : ‖(1 : K)‖ ≠ ‖-(t.q : K) ^ (k + 1)‖ := by
    rw [norm_one, norm_neg]
    exact ne_of_gt hlt
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, norm_neg]
  exact max_eq_left (le_of_lt hlt)

/-- The denominator `1 - q^(k+1)` is nonzero (its norm is `1`). -/
lemma one_sub_qpow_ne_zero [IsUltrametricDist K] (k : ℕ) :
    (1 : K) - (t.q : K) ^ (k + 1) ≠ 0 := by
  have h := t.norm_one_sub_qpow k
  intro hz
  rw [hz, norm_zero] at h
  exact one_ne_zero h.symm

/-- **The multiplicative form of the coefficient recursion.** Clearing the inverse in the
definition gives `(1 - q^(k+1)) · E (k+1) = qᵏ · E k`, the shape used to match coefficients in
the series functional equation. -/
lemma factorCoeff_rec [IsUltrametricDist K] (k : ℕ) :
    (1 - (t.q : K) ^ (k + 1)) * factorCoeff t (k + 1) = (t.q : K) ^ k * factorCoeff t k := by
  have hne := t.one_sub_qpow_ne_zero k
  have key : factorCoeff t (k + 1)
      = (t.q : K) ^ k * factorCoeff t k * (1 - (t.q : K) ^ (k + 1))⁻¹ := by
    rw [factorCoeff_succ]; ring
  rw [key, ← mul_assoc, mul_comm (1 - (t.q : K) ^ (k + 1)) ((t.q : K) ^ k * factorCoeff t k),
    mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- **The norm of the successive coefficient.** Since `‖1 - q^(k+1)‖ = 1`, the recursion gives
`‖E (k+1)‖ = ‖q‖ᵏ · ‖E k‖`. -/
lemma norm_factorCoeff_succ [IsUltrametricDist K] (k : ℕ) :
    ‖factorCoeff t (k + 1)‖ = ‖(t.q : K)‖ ^ k * ‖factorCoeff t k‖ := by
  rw [factorCoeff_succ, norm_mul, norm_mul, norm_pow, norm_inv, t.norm_one_sub_qpow k, inv_one]
  ring

/-- **Lemma A: the norm of the Euler `q`-binomial coefficients.** By induction on the recursion,
`‖E k‖ = ‖q‖ ^ (k * (k - 1) / 2)`, the triangular-number exponent. -/
lemma norm_factorCoeff [IsUltrametricDist K] (k : ℕ) :
    ‖factorCoeff t k‖ = ‖(t.q : K)‖ ^ (k * (k - 1) / 2) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hexp : n + n * (n - 1) / 2 = (n + 1) * ((n + 1) - 1) / 2 := by
      rw [← Finset.sum_range_id n, ← Finset.sum_range_id (n + 1), Finset.sum_range_succ]
      exact Nat.add_comm _ _
    rw [t.norm_factorCoeff_succ, ih, ← pow_add, hexp]

/-- Every Euler `q`-binomial coefficient has norm at most one. -/
lemma norm_factorCoeff_le_one [IsUltrametricDist K] (k : ℕ) : ‖factorCoeff t k‖ ≤ 1 := by
  rw [t.norm_factorCoeff k]
  exact pow_le_one₀ (norm_nonneg _) (le_of_lt t.norm_lt_one)

/-- **Lemma B: summability of the power series.** For every `c`, the family `k ↦ E k · cᵏ` is
summable: consecutive term norms satisfy `‖E (k+1) c^(k+1)‖ = (‖q‖ᵏ ‖c‖) · ‖E k cᵏ‖` and the
ratio `‖q‖ᵏ ‖c‖ → 0`, so the ratio test applies. -/
lemma factorCoeff_summable [CompleteSpace K] [IsUltrametricDist K] (c : K) :
    Summable (fun k : ℕ => factorCoeff t k * c ^ k) := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  have htend : Tendsto (fun k : ℕ => ‖(t.q : K)‖ ^ k * ‖c‖) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (t.q : K)) t.norm_lt_one).mul_const ‖c‖
  filter_upwards [htend.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num)] with k hk
  have key : ‖factorCoeff t (k + 1) * c ^ (k + 1)‖
      = ‖(t.q : K)‖ ^ k * ‖c‖ * ‖factorCoeff t k * c ^ k‖ := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, t.norm_factorCoeff_succ k]
    ring
  rw [key]
  exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)

/-- **Lemma C: the functional equation at the series level.** The power series
`S c = ∑' k, E k cᵏ` satisfies `S c = (1 + c) · S (q c)`, the same functional equation as
`thetaProdFactor` (`thetaProdFactor_eq`). This is pure `tsum` algebra: expanding the right-hand
side and subtracting the diagonal part `∑ E k qᵏ cᵏ`, the recursion
`(1 - q^(k+1)) E (k+1) = qᵏ E k` matches the two remaining series coefficient by coefficient. -/
lemma tsum_factorCoeff_eq [CompleteSpace K] [IsUltrametricDist K] (c : K) :
    (∑' k : ℕ, factorCoeff t k * c ^ k)
      = (1 + c) * ∑' k : ℕ, factorCoeff t k * ((t.q : K) * c) ^ k := by
  have hf := t.factorCoeff_summable c
  have hg := t.factorCoeff_summable ((t.q : K) * c)
  have hd : Summable
      (fun k : ℕ => factorCoeff t k * c ^ k - factorCoeff t k * ((t.q : K) * c) ^ k) := hf.sub hg
  -- Split `f = g + d` with `d k = f k - g k`, then evaluate `∑ d = c · ∑ g`.
  have hsplit : ∀ k : ℕ, factorCoeff t k * c ^ k
      = factorCoeff t k * ((t.q : K) * c) ^ k
        + (factorCoeff t k * c ^ k - factorCoeff t k * ((t.q : K) * c) ^ k) := by
    intro k; ring
  rw [tsum_congr hsplit, Summable.tsum_add hg hd, add_mul, one_mul]
  congr 1
  -- `∑ d = c · ∑ g`, using `d 0 = 0` and the recursion on the tail.
  rw [hd.tsum_eq_zero_add]
  simp only [factorCoeff_zero, pow_zero, mul_one, sub_self, zero_add]
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  -- `d (k+1) = c · g k`.
  have hrec := t.factorCoeff_rec k
  rw [mul_pow, mul_pow, pow_succ ((t.q : K)) k, pow_succ c k]
  linear_combination (c ^ k * c) * hrec

/-- **Iterated functional equation.** Peeling the functional equation `N` times exhibits the
finite partial product: `S c = (∏ n < N, (1 + qⁿ c)) · S (q^N c)`. -/
lemma tsum_factorCoeff_eq_prod_mul [CompleteSpace K] [IsUltrametricDist K] (c : K) (N : ℕ) :
    (∑' k : ℕ, factorCoeff t k * c ^ k)
      = (∏ n ∈ Finset.range N, (1 + (t.q : K) ^ n * c))
        * ∑' k : ℕ, factorCoeff t k * ((t.q : K) ^ N * c) ^ k := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hq : (t.q : K) * ((t.q : K) ^ N * c) = (t.q : K) ^ (N + 1) * c := by
      rw [pow_succ]; ring
    rw [ih, t.tsum_factorCoeff_eq ((t.q : K) ^ N * c), hq, Finset.prod_range_succ]
    ring

/-- **Tail estimate near zero.** On the closed unit ball, `‖S x - 1‖ ≤ ‖x‖`. Peeling the constant
term, `S x - 1 = x · ∑' k, E (k+1) xᵏ`, and the ultrametric bound `‖∑' k, E (k+1) xᵏ‖ ≤ 1`
(each `‖E (k+1) xᵏ‖ ≤ 1`) gives the estimate. -/
lemma norm_tsum_sub_one_le [CompleteSpace K] [IsUltrametricDist K] (x : K) (hx : ‖x‖ ≤ 1) :
    ‖(∑' k : ℕ, factorCoeff t k * x ^ k) - 1‖ ≤ ‖x‖ := by
  have hsum := t.factorCoeff_summable x
  rw [hsum.tsum_eq_zero_add]
  simp only [factorCoeff_zero, pow_zero, mul_one, add_sub_cancel_left]
  have hcongr : (∑' k : ℕ, factorCoeff t (k + 1) * x ^ (k + 1))
      = x * ∑' k : ℕ, factorCoeff t (k + 1) * x ^ k := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [pow_succ]; ring
  rw [hcongr, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  refine (IsUltrametricDist.norm_tsum_le _).trans (ciSup_le fun k => ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_one₀ (t.norm_factorCoeff_le_one _) (pow_nonneg (norm_nonneg _) _)
    (pow_le_one₀ (norm_nonneg _) hx)

/-- **The Euler `q`-binomial expansion of the elementary theta factor.** For every `c`,
```
thetaProdFactor c = ∏' n, (1 + qⁿ c) = ∑' k, E k cᵏ.
```
Both sides agree because `S c = ∑' k, E k cᵏ` satisfies the defining functional equation of
`thetaProdFactor`; iterating it peels the finite partial product `∏ n < N, (1 + qⁿ c)`, whose limit
is `thetaProdFactor c`, while the remainder `S (q^N c) → S 0 = 1` since `q^N c → 0`. -/
theorem thetaProdFactor_eq_tsum [CompleteSpace K] [IsUltrametricDist K] (c : K) :
    t.thetaProdFactor c = ∑' k : ℕ, factorCoeff t k * c ^ k := by
  -- Partial products converge to `thetaProdFactor c`.
  have hprod : Tendsto (fun N => ∏ n ∈ Finset.range N, (1 + (t.q : K) ^ n * c)) atTop
      (𝓝 (t.thetaProdFactor c)) := by
    have h := (t.multipliable_thetaProdFactor c).hasProd.tendsto_prod_nat
    rwa [← thetaProdFactor_apply] at h
  -- The remainder tends to `1`.
  have hS : Tendsto (fun N => ∑' k : ℕ, factorCoeff t k * ((t.q : K) ^ N * c) ^ k) atTop (𝓝 1) := by
    have hqc : Tendsto (fun N : ℕ => (t.q : K) ^ N * c) atTop (𝓝 0) := by
      simpa using t.tendsto_pow_atTop_zero.mul_const c
    have hnorm : Tendsto (fun N : ℕ => ‖(t.q : K) ^ N * c‖) atTop (𝓝 0) := by
      simpa using hqc.norm
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm' ?_ hnorm
    filter_upwards [hnorm.eventually_le_const (show (0 : ℝ) < 1 by norm_num)] with N hN
    exact t.norm_tsum_sub_one_le _ hN
  -- Combine and use uniqueness of limits.
  have hcomb : Tendsto (fun N => (∏ n ∈ Finset.range N, (1 + (t.q : K) ^ n * c))
      * ∑' k : ℕ, factorCoeff t k * ((t.q : K) ^ N * c) ^ k) atTop
      (𝓝 (t.thetaProdFactor c * 1)) := hprod.mul hS
  rw [mul_one] at hcomb
  have hconst : Tendsto (fun _ : ℕ => ∑' k : ℕ, factorCoeff t k * c ^ k) atTop
      (𝓝 (∑' k : ℕ, factorCoeff t k * c ^ k)) := tendsto_const_nhds
  rw [funext fun N => t.tsum_factorCoeff_eq_prod_mul c N] at hconst
  exact (tendsto_nhds_unique hconst hcomb).symm

end TateParameter

end TateCurvesTheta
