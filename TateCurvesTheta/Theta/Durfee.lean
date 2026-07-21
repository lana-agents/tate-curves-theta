/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Group.Tannery
import TateCurvesTheta.Theta.Normalization
import TateCurvesTheta.Theta.QBinomial
import TateCurvesTheta.Theta.Divisor

/-!
# The Durfee-square identity and the unconditional Jacobi triple product `theta = thetaProd`

The closed-form reduction (`Theta/Normalization.lean`, #160) pins the whole `theta = thetaProd`
flagship to a **single scalar normalization**
```
thetaProdNormConst = thetaProdFactor(-q) · ∑' k, factorCoeff k ² · qᵏ = 1,
```
classically the **Durfee-square identity** `∑ₖ q^{k²}/((q;q)ₖ)² = 1/(q;q)_∞`. This file proves
that identity by taking the `n → ∞` limit of the *finite* q-Vandermonde / Durfee-square identity
`∑ₖ q^{k²}·([n;k]_q)² = [2n;n]_q` (`Theta/QBinomial.lean`, #165), and thereby delivers the
**unconditional** Jacobi triple product identity together with the (now unconditional) divisor of
the naive theta series.

## Strategy

Write `q = (t.q : K)` and `P = thetaProdFactor(-q)`, a nonzero constant
(`thetaProdFactor_neg_q_ne_zero`).

* **Closed form of the Euler coefficients:** `factorCoeff k · (q;q)ₖ = q^{k(k-1)/2}`
  (`factorCoeff_mul_qPoch`), whence `factorCoeff k ² · qᵏ · (q;q)ₖ² = q^{k²}`
  (`factorCoeff_sq_mul`).
* **Partial products converge:** `(q;q)ₙ = ∏_{j<n}(1 - q^{j+1}) = ∏_{j<n}(1 + qʲ·(-q)) → P`
  (`qPoch_tendsto`), because these are exactly the partial products of `thetaProdFactor(-q)`.
* **Termwise limit of the finite summand:** for each fixed `k`, `[n;k]_q → (q;q)ₖ⁻¹` as `n → ∞`
  (from the division-free closed form `[n;k]·(q;q)ₖ·(q;q)_{n-k} = (q;q)ₙ`), so
  `q^{k²}·([n;k]_q)² → q^{k²}·(q;q)ₖ⁻² = factorCoeff k ²·qᵏ`.
* **Dominated convergence** (`tendsto_tsum_of_dominated_convergence`, with the uniform bound
  `‖q^{k²}·([n;k]_q)²‖ ≤ ‖q‖^{k²}` summable, using `‖[n;k]_q‖ ≤ 1`) turns
  `[2n;n]_q = ∑ₖ q^{k²}·([n;k]_q)²` into `∑' k, factorCoeff k ²·qᵏ` in the limit.
* **Separately** `[2n;n]_q = (q;q)_{2n}·((q;q)ₙ²)⁻¹ → P·(P²)⁻¹ = P⁻¹`.
* Uniqueness of limits gives `∑' k, factorCoeff k ²·qᵏ = P⁻¹`, i.e.
  `thetaProdNormConst = P·P⁻¹ = 1`.

## Main results

* `TateParameter.thetaProdNormConst_eq_one` : the Durfee-square identity `thetaProdNormConst = 1`.
* `TateParameter.theta_eq_thetaProd` : the **unconditional** Jacobi triple product identity
  `theta u = thetaProd u`.
* `TateParameter.theta_eq_zero_iff` : the **unconditional** zero divisor of the naive theta series,
  `theta u = 0 ↔ ∃ k : ℤ, (u : K) = -qᵏ`.

## References

* G. E. Andrews, *The Theory of Partitions*, §3.3 (the Durfee square).
* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.2–10.4.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
-/

open Filter Topology Finset

namespace TateCurvesTheta

/-! ### General finite q-series facts (over a nonarchimedean field) -/

section General

variable {K : Type*} [NormedField K]

/-- The q-Pochhammer symbol as the partial product of the `thetaProdFactor(-q)` family:
`(q;q)_N = ∏_{j<N} (1 - q^{j+1}) = ∏_{j<N} (1 + qʲ·(-q))`. -/
lemma qPoch_eq_prod (q : K) (N : ℕ) :
    qPoch q N = ∏ n ∈ Finset.range N, (1 + q ^ n * (-q)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, ← ih, qPoch_succ]
    ring

/-- **Uniform norm bound on Gaussian binomials.** Over an ultrametric field with `‖q‖ ≤ 1`,
`‖[n;k]_q‖ ≤ 1` for all `n, k`, by induction on the q-Pascal recursion. -/
lemma norm_gaussBinom_le_one [IsUltrametricDist K] {q : K} (hq : ‖q‖ ≤ 1) :
    ∀ n k : ℕ, ‖gaussBinom q n k‖ ≤ 1
  | _, 0 => by rw [gaussBinom_zero_right]; simp
  | 0, (_ + 1) => by rw [gaussBinom_zero_succ]; simp
  | (n + 1), (k + 1) => by
      rw [gaussBinom_succ_succ]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact norm_gaussBinom_le_one hq n (k + 1)
      · rw [norm_mul, norm_pow]
        exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hq) (norm_nonneg _)
          (norm_gaussBinom_le_one hq n k)

end General

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-! ### Closed form of the Euler `q`-binomial coefficients -/

omit [CompleteSpace K] in
/-- **Division-free closed form of the Euler coefficients:** `factorCoeff k · (q;q)ₖ =
q^{k(k-1)/2}`. Both sides satisfy the same recursion, the inverse `(1 - q^{k+1})⁻¹` in
`factorCoeff` cancelling the extra `(q;q)` factor. -/
lemma factorCoeff_mul_qPoch (k : ℕ) :
    factorCoeff t k * qPoch (t.q : K) k = (t.q : K) ^ (k * (k - 1) / 2) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hne := t.one_sub_qpow_ne_zero n
    have hexp : n + n * (n - 1) / 2 = (n + 1) * ((n + 1) - 1) / 2 := by
      rw [← Finset.sum_range_id n, ← Finset.sum_range_id (n + 1), Finset.sum_range_succ]
      exact Nat.add_comm _ _
    rw [factorCoeff_succ, qPoch_succ]
    calc
      (t.q : K) ^ n * (1 - (t.q : K) ^ (n + 1))⁻¹ * factorCoeff t n
            * (qPoch (t.q : K) n * (1 - (t.q : K) ^ (n + 1)))
          = (t.q : K) ^ n * (factorCoeff t n * qPoch (t.q : K) n)
            * ((1 - (t.q : K) ^ (n + 1))⁻¹ * (1 - (t.q : K) ^ (n + 1))) := by ring
      _ = (t.q : K) ^ n * (t.q : K) ^ (n * (n - 1) / 2) * 1 := by
            rw [ih, inv_mul_cancel₀ hne]
      _ = (t.q : K) ^ (n + n * (n - 1) / 2) := by rw [mul_one, ← pow_add]
      _ = (t.q : K) ^ ((n + 1) * ((n + 1) - 1) / 2) := by rw [hexp]

/-- The exponent bookkeeping `k(k-1)/2 · 2 + k = k²` (the division is exact as `k(k-1)` is even). -/
private lemma durfee_exp (k : ℕ) : k * (k - 1) / 2 * 2 + k = k * k := by
  have hdvd : 2 ∣ k * (k - 1) := by
    rcases k with _ | m
    · simp
    · rw [Nat.succ_sub_one]
      have : Even ((m + 1) * m) := by rw [Nat.mul_comm]; exact Nat.even_mul_succ_self m
      exact this.two_dvd
  rw [Nat.div_mul_cancel hdvd]
  rcases k with _ | m
  · rfl
  · rw [Nat.succ_sub_one]; ring

omit [CompleteSpace K] in
/-- **The Durfee summand in closed form:** `factorCoeff k ² · qᵏ · (q;q)ₖ² = q^{k²}`
(division-free). Squaring `factorCoeff_mul_qPoch` and multiplying by `qᵏ`, the exponents add to
`k(k-1) + k = k²`. -/
lemma factorCoeff_sq_mul (k : ℕ) :
    factorCoeff t k ^ 2 * (t.q : K) ^ k * qPoch (t.q : K) k ^ 2 = (t.q : K) ^ (k * k) := by
  have h : (factorCoeff t k * qPoch (t.q : K) k) ^ 2 = ((t.q : K) ^ (k * (k - 1) / 2)) ^ 2 := by
    rw [t.factorCoeff_mul_qPoch k]
  rw [mul_pow] at h
  calc
    factorCoeff t k ^ 2 * (t.q : K) ^ k * qPoch (t.q : K) k ^ 2
        = factorCoeff t k ^ 2 * qPoch (t.q : K) k ^ 2 * (t.q : K) ^ k := by ring
    _ = ((t.q : K) ^ (k * (k - 1) / 2)) ^ 2 * (t.q : K) ^ k := by rw [h]
    _ = (t.q : K) ^ (k * (k - 1) / 2 * 2) * (t.q : K) ^ k := by rw [← pow_mul]
    _ = (t.q : K) ^ (k * (k - 1) / 2 * 2 + k) := by rw [← pow_add]
    _ = (t.q : K) ^ (k * k) := by rw [durfee_exp]

/-! ### Convergence of the partial q-Pochhammer products -/

omit [CompleteSpace K] in
/-- `(q;q)ₖ ≠ 0`: each factor `1 - q^{j+1}` is a unit. -/
lemma qPoch_ne_zero' (k : ℕ) : qPoch (t.q : K) k ≠ 0 :=
  qPoch_ne_zero (t.q : K) t.one_sub_qpow_ne_zero k

omit [IsUltrametricDist K] in
/-- **The partial q-Pochhammer products converge to `thetaProdFactor(-q)`.** They are exactly the
partial products of the multipliable family `n ↦ 1 + qⁿ·(-q)`. -/
lemma qPoch_tendsto :
    Tendsto (fun N => qPoch (t.q : K) N) atTop (𝓝 (t.thetaProdFactor (-(t.q : K)))) := by
  have h := (t.multipliable_thetaProdFactor (-(t.q : K))).hasProd.tendsto_prod_nat
  rw [← thetaProdFactor_apply] at h
  exact h.congr fun N => (qPoch_eq_prod (t.q : K) N).symm

/-- `n ↦ n - k` tends to `atTop`. -/
private lemma tendsto_sub_atTop (k : ℕ) : Tendsto (fun n : ℕ => n - k) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b + k, fun a ha => by omega⟩

/-- `n ↦ 2 * n` tends to `atTop`. -/
private lemma tendsto_two_mul_atTop : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => by omega⟩

/-! ### The two limits and the Durfee identity -/

/-- **Termwise limit of the finite Durfee summand.** For each fixed `k`,
`q^{k²}·([n;k]_q)² → factorCoeff k ²·qᵏ` as `n → ∞`. -/
lemma tendsto_durfee_summand (k : ℕ) :
    Tendsto (fun n => (t.q : K) ^ (k * k) * gaussBinom (t.q : K) n k ^ 2) atTop
      (𝓝 (factorCoeff t k ^ 2 * (t.q : K) ^ k)) := by
  set P := t.thetaProdFactor (-(t.q : K)) with hP
  have hPne : P ≠ 0 := t.thetaProdFactor_neg_q_ne_zero
  -- `[n;k]_q · (q;q)ₖ → 1`.
  have hgbk : Tendsto (fun n => gaussBinom (t.q : K) n k * qPoch (t.q : K) k) atTop (𝓝 1) := by
    have hnum : Tendsto (fun n => qPoch (t.q : K) n) atTop (𝓝 P) := t.qPoch_tendsto
    have hden : Tendsto (fun n => qPoch (t.q : K) (n - k)) atTop (𝓝 P) :=
      t.qPoch_tendsto.comp (tendsto_sub_atTop k)
    have hlim : Tendsto (fun n => qPoch (t.q : K) n * (qPoch (t.q : K) (n - k))⁻¹) atTop
        (𝓝 (P * P⁻¹)) := hnum.mul (hden.inv₀ hPne)
    rw [mul_inv_cancel₀ hPne] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop k] with n hn
    have hcf := gaussBinom_mul_qPoch (t.q : K) hn
    rw [← hcf, ← mul_assoc, mul_inv_cancel_right₀ (t.qPoch_ne_zero' (n - k))]
  -- `[n;k]_q → (q;q)ₖ⁻¹`.
  have hgb : Tendsto (fun n => gaussBinom (t.q : K) n k) atTop (𝓝 ((qPoch (t.q : K) k)⁻¹)) := by
    have h := hgbk.mul_const ((qPoch (t.q : K) k)⁻¹)
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards with n
    rw [mul_inv_cancel_right₀ (t.qPoch_ne_zero' k)]
  -- Assemble the summand limit and rewrite the target via the closed form.
  have hlim := (hgb.pow 2).const_mul ((t.q : K) ^ (k * k))
  have heq : (t.q : K) ^ (k * k) * ((qPoch (t.q : K) k)⁻¹) ^ 2
      = factorCoeff t k ^ 2 * (t.q : K) ^ k := by
    rw [inv_pow, ← t.factorCoeff_sq_mul k,
      mul_inv_cancel_right₀ (pow_ne_zero 2 (t.qPoch_ne_zero' k))]
  rwa [heq] at hlim

/-- **The Durfee-square identity** `thetaProdNormConst = 1`, obtained as the `n → ∞` limit of the
finite q-Vandermonde identity `∑ₖ q^{k²}·([n;k]_q)² = [2n;n]_q`. This is the sole scalar residual of
the whole `theta = thetaProd` flagship. -/
theorem thetaProdNormConst_eq_one : t.thetaProdNormConst = 1 := by
  set P := t.thetaProdFactor (-(t.q : K)) with hP
  have hPne : P ≠ 0 := t.thetaProdFactor_neg_q_ne_zero
  have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
  -- Uniform summable bound `‖q‖^{k²}` for dominated convergence.
  have hbound : Summable (fun k : ℕ => ‖(t.q : K)‖ ^ (k * k)) := by
    refine Summable.of_nonneg_of_le (fun k => pow_nonneg (norm_nonneg _) _) (fun k => ?_)
      (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one)
    refine pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt t.norm_lt_one) ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · exact Nat.le_mul_of_pos_left k hk
  -- Dominated convergence: `∑' k, [finite summand] → ∑' k, factorCoeff k²·qᵏ`.
  have hDCT : Tendsto (fun n => ∑' k : ℕ, (t.q : K) ^ (k * k) * gaussBinom (t.q : K) n k ^ 2)
      atTop (𝓝 (∑' k : ℕ, factorCoeff t k ^ 2 * (t.q : K) ^ k)) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun k => t.tendsto_durfee_summand k) ?_
    refine Filter.Eventually.of_forall fun n k => ?_
    rw [norm_mul, norm_pow, norm_pow]
    refine mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) ?_
    exact pow_le_one₀ (norm_nonneg _) (norm_gaussBinom_le_one (le_of_lt t.norm_lt_one) n k)
  -- The finite sum equals `[2n;n]_q` (the q-Vandermonde/Durfee identity).
  have hLHS : ∀ n, (∑' k : ℕ, (t.q : K) ^ (k * k) * gaussBinom (t.q : K) n k ^ 2)
      = gaussBinom (t.q : K) (2 * n) n := by
    intro n
    rw [tsum_eq_sum (s := Finset.range (n + 1)) fun k hk => ?_]
    · exact gaussBinom_two_mul_self hq0 t.one_sub_qpow_ne_zero n
    · rw [Finset.mem_range, not_lt] at hk
      rw [gaussBinom_eq_zero_of_lt (t.q : K) (by omega : n < k)]
      simp
  simp only [hLHS] at hDCT
  -- `[2n;n]_q → P⁻¹`.
  have hgb2n : Tendsto (fun n => gaussBinom (t.q : K) (2 * n) n) atTop (𝓝 (P⁻¹)) := by
    have key : ∀ n, gaussBinom (t.q : K) (2 * n) n * (qPoch (t.q : K) n * qPoch (t.q : K) n)
        = qPoch (t.q : K) (2 * n) := by
      intro n
      have h := gaussBinom_mul_qPoch (t.q : K) (show n ≤ 2 * n by omega)
      rwa [show 2 * n - n = n by omega] at h
    have hnum : Tendsto (fun n => qPoch (t.q : K) (2 * n)) atTop (𝓝 P) :=
      t.qPoch_tendsto.comp tendsto_two_mul_atTop
    have hden : Tendsto (fun n => qPoch (t.q : K) n * qPoch (t.q : K) n) atTop (𝓝 (P * P)) :=
      t.qPoch_tendsto.mul t.qPoch_tendsto
    have hlim : Tendsto
        (fun n => qPoch (t.q : K) (2 * n) * (qPoch (t.q : K) n * qPoch (t.q : K) n)⁻¹)
        atTop (𝓝 (P * (P * P)⁻¹)) := hnum.mul (hden.inv₀ (mul_ne_zero hPne hPne))
    rw [show P * (P * P)⁻¹ = P⁻¹ by field_simp] at hlim
    refine hlim.congr' ?_
    filter_upwards with n
    rw [← key n, mul_inv_cancel_right₀ (mul_ne_zero (t.qPoch_ne_zero' n) (t.qPoch_ne_zero' n))]
  -- Uniqueness of limits pins the sum, and `P · P⁻¹ = 1`.
  have hsum_eq : (∑' k : ℕ, factorCoeff t k ^ 2 * (t.q : K) ^ k) = P⁻¹ :=
    tendsto_nhds_unique hDCT hgb2n
  rw [thetaProdNormConst, ← hP, hsum_eq, mul_inv_cancel₀ hPne]

/-! ### The unconditional Jacobi triple product and its divisor -/

/-- **The Jacobi triple product identity `theta = thetaProd`, unconditionally.** Over any complete
nonarchimedean field the naive `q`-theta series equals its product form for every `u : Kˣ`. All
analytic content (the rigid-analytic global Laurent expansion, #148) and the scalar normalization
(the Durfee-square identity, `thetaProdNormConst_eq_one`) are discharged; the coefficient-uniqueness
principle is `laurentCoeffUnique`. -/
theorem theta_eq_thetaProd (u : Kˣ) : t.theta u = t.thetaProd u :=
  t.theta_eq_thetaProd_of_durfee t.thetaProdNormConst_eq_one u

/-- **The zero divisor of the naive theta series, unconditionally.** `theta u = 0` exactly on the
`qᶻ`-orbit of `-1`. This discharges the conditionality of `theta_eq_zero_iff_of_eq_thetaProd`
(`Theta/Divisor.lean`, #88). -/
theorem theta_eq_zero_iff (u : Kˣ) :
    t.theta u = 0 ↔ ∃ k : ℤ, (u : K) = -(t.q : K) ^ k :=
  t.theta_eq_zero_iff_of_eq_thetaProd u (t.theta_eq_thetaProd u)

end TateParameter

end TateCurvesTheta
