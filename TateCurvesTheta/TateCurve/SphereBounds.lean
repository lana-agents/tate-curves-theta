/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.TateCurve.Discriminant
import TateCurvesTheta.TateCurve.Parametrization

/-!
# Leading-term bounds for the Tate coordinates on the unit sphere and the middle annulus

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the Tate
coordinate series `X(u) = ∑' n, qⁿu/(1-qⁿu)² - 2s₁(q)` and
`Y(u) = ∑' n, (qⁿu)²/(1-qⁿu)³ + s₁(q)` are dominated by finitely many leading terms on each
norm regime of the fundamental annulus `‖q‖ < ‖u‖ ≤ 1`:

* on the **unit sphere** `‖u‖ = 1` the `n = 0` term dominates, and
  `X(u) = u/(1-u)² + O(q)`, `Y(u) = u²/(1-u)³ + O(q)`;
* on the **middle annulus** `‖q‖ < ‖u‖ < 1` the two terms `n = 0` and `n = -1` dominate, and
  `X(u) = Xterm₀ + Xterm₋₁ + O(q)`, `Y(u) = Yterm₀ + Yterm₋₁ + O(q)`.

This is the estimate layer for the surjectivity of the Tate parametrization: matching an
affine point `(x, y)` of `E_q` against these expansions pins the candidate parameter `u` down
to a leading term plus an `O(q)`-perturbation. The file also records the exact norms of the
leading terms (via the ultrametric isosceles law `‖1 - w‖ = max 1 ‖w‖`) and the curve-side
norm classification: any affine point with `‖x‖ ≤ 1` has `‖y‖ ≤ 1`, and in the deep zone
`‖x‖² ≤ ‖q‖` the Weierstrass equation forces `‖y‖² = ‖q‖` with `‖x‖ ≤ ‖y‖`.

## Main results

* `TateParameter.norm_X_sub_node_le`, `TateParameter.norm_Y_sub_node_le`: on `‖u‖ = 1`,
  `‖X(u) - u/(1-u)²‖ ≤ ‖q‖` and `‖Y(u) - u²/(1-u)³‖ ≤ ‖q‖`.
* `TateParameter.norm_X_sub_annulus_le`, `TateParameter.norm_Y_sub_annulus_le`: on
  `‖q‖ < ‖u‖ < 1`, the sum minus its `n = 0` and `n = -1` terms has norm `≤ ‖q‖`.
* `TateParameter.norm_Xterm_zero`, `norm_Xterm_neg_one`, `norm_Yterm_zero`,
  `norm_Yterm_neg_one`: the exact leading-term norms `‖u‖`, `‖q‖/‖u‖`, `‖u‖²`, `‖q‖/‖u‖`.
* `TateParameter.norm_y_le_one_of_norm_x_le_one`: curve-side integrality — `‖x‖ ≤ 1` forces
  `‖y‖ ≤ 1` on `E_q`.
* `TateParameter.norm_y_sq_eq_of_node`: curve-side deep-zone classification — `‖x‖² ≤ ‖q‖`
  and `‖x‖ < 1` force `‖y‖² = ‖q‖` and `‖x‖ ≤ ‖y‖` on `E_q`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* P. Roquette, *Analytic theory of elliptic functions over local fields*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-! ### Closed forms of the leading terms -/

/-- The `n = 0` term of the `X`-coordinate series is `u/(1-u)²`. -/
lemma Xterm_zero_apply (u : Kˣ) : t.Xterm u 0 = (u : K) / (1 - (u : K)) ^ 2 := by
  rw [Xterm_apply, zpow_zero, one_mul]

/-- The `n = 0` term of the `Y`-coordinate series is `u²/(1-u)³`. -/
lemma Yterm_zero_apply (u : Kˣ) : t.Yterm u 0 = (u : K) ^ 2 / (1 - (u : K)) ^ 3 := by
  rw [Yterm_apply, zpow_zero, one_mul]

section Nonarchimedean

variable [IsUltrametricDist K]

/-! ### Exact norms of a single coordinate term

Writing `w = qⁿu`, the isosceles law `‖1 - w‖ = max 1 ‖w‖` gives `‖Xterm‖ = ‖w‖` and
`‖Yterm‖ = ‖w‖²` for `‖w‖ < 1`, and `‖Xterm‖ = ‖Yterm‖ = ‖w‖⁻¹` for `‖w‖ > 1`. -/

/-- For `‖qⁿu‖ < 1` the `X`-term has norm exactly `‖qⁿu‖`. -/
lemma norm_Xterm_of_norm_lt_one {u : Kˣ} {n : ℤ} (h : ‖(t.q : K) ^ n * (u : K)‖ < 1) :
    ‖t.Xterm u n‖ = ‖(t.q : K) ^ n * (u : K)‖ := by
  rw [Xterm_apply, norm_div, norm_pow, norm_one_sub_of_norm_ne_one h.ne,
    max_eq_left h.le, one_pow, div_one]

/-- For `‖qⁿu‖ > 1` the `X`-term has norm exactly `‖qⁿu‖⁻¹`. -/
lemma norm_Xterm_of_one_lt_norm {u : Kˣ} {n : ℤ} (h : 1 < ‖(t.q : K) ^ n * (u : K)‖) :
    ‖t.Xterm u n‖ = ‖(t.q : K) ^ n * (u : K)‖⁻¹ := by
  have h0 : ‖(t.q : K) ^ n * (u : K)‖ ≠ 0 := (lt_trans one_pos h).ne'
  rw [Xterm_apply, norm_div, norm_pow, norm_one_sub_of_norm_ne_one h.ne',
    max_eq_right h.le, pow_two, div_mul_cancel_left₀ h0]

/-- For `‖qⁿu‖ < 1` the `Y`-term has norm exactly `‖qⁿu‖²`. -/
lemma norm_Yterm_of_norm_lt_one {u : Kˣ} {n : ℤ} (h : ‖(t.q : K) ^ n * (u : K)‖ < 1) :
    ‖t.Yterm u n‖ = ‖(t.q : K) ^ n * (u : K)‖ ^ 2 := by
  rw [Yterm_apply, norm_div, norm_pow, norm_pow, norm_one_sub_of_norm_ne_one h.ne,
    max_eq_left h.le, one_pow, div_one]

/-- For `‖qⁿu‖ > 1` the `Y`-term has norm exactly `‖qⁿu‖⁻¹`. -/
lemma norm_Yterm_of_one_lt_norm {u : Kˣ} {n : ℤ} (h : 1 < ‖(t.q : K) ^ n * (u : K)‖) :
    ‖t.Yterm u n‖ = ‖(t.q : K) ^ n * (u : K)‖⁻¹ := by
  have h0 : ‖(t.q : K) ^ n * (u : K)‖ ≠ 0 := (lt_trans one_pos h).ne'
  rw [Yterm_apply, norm_div, norm_pow, norm_pow, norm_one_sub_of_norm_ne_one h.ne',
    max_eq_right h.le,
    show ‖(t.q : K) ^ n * (u : K)‖ ^ 3
      = ‖(t.q : K) ^ n * (u : K)‖ ^ 2 * ‖(t.q : K) ^ n * (u : K)‖ from by ring,
    div_mul_cancel_left₀ (pow_ne_zero 2 h0)]

/-! ### Exact norms of the leading terms on the middle annulus -/

/-- On `‖u‖ < 1` the leading `X`-term has norm `‖u‖`. -/
lemma norm_Xterm_zero {u : Kˣ} (hhi : ‖(u : K)‖ < 1) : ‖t.Xterm u 0‖ = ‖(u : K)‖ := by
  have h : ‖(t.q : K) ^ (0 : ℤ) * (u : K)‖ < 1 := by rwa [zpow_zero, one_mul]
  have := t.norm_Xterm_of_norm_lt_one h
  rwa [zpow_zero, one_mul] at this

/-- On `‖u‖ < 1` the leading `Y`-term has norm `‖u‖²`. -/
lemma norm_Yterm_zero {u : Kˣ} (hhi : ‖(u : K)‖ < 1) : ‖t.Yterm u 0‖ = ‖(u : K)‖ ^ 2 := by
  have h : ‖(t.q : K) ^ (0 : ℤ) * (u : K)‖ < 1 := by rwa [zpow_zero, one_mul]
  have := t.norm_Yterm_of_norm_lt_one h
  rwa [zpow_zero, one_mul] at this

omit [IsUltrametricDist K] in
/-- The norm `‖u/q‖ = ‖u‖/‖q‖` of the base point of the `n = -1` term. -/
private lemma norm_qzpow_neg_one_mul (u : Kˣ) :
    ‖(t.q : K) ^ (-1 : ℤ) * (u : K)‖ = ‖(u : K)‖ / ‖(t.q : K)‖ := by
  rw [norm_mul, norm_zpow, zpow_neg_one, inv_mul_eq_div]

/-- On `‖q‖ < ‖u‖` the subleading `X`-term (`n = -1`) has norm `‖q‖/‖u‖`. -/
lemma norm_Xterm_neg_one {u : Kˣ} (hlo : ‖(t.q : K)‖ < ‖(u : K)‖) :
    ‖t.Xterm u (-1)‖ = ‖(t.q : K)‖ / ‖(u : K)‖ := by
  have h1 : 1 < ‖(t.q : K) ^ (-1 : ℤ) * (u : K)‖ := by
    rw [t.norm_qzpow_neg_one_mul u]
    exact (one_lt_div t.norm_q_pos).mpr hlo
  rw [t.norm_Xterm_of_one_lt_norm h1, t.norm_qzpow_neg_one_mul u, inv_div]

/-- On `‖q‖ < ‖u‖` the subleading `Y`-term (`n = -1`) has norm `‖q‖/‖u‖`.

Note the exact norm is `‖q‖/‖u‖` and **not** `(‖q‖/‖u‖)²`: for `‖w‖ > 1` the `Y`-term
`w²/(1-w)³` has norm `‖w‖²/‖w‖³ = ‖w‖⁻¹`, here with `w = u/q`. -/
lemma norm_Yterm_neg_one {u : Kˣ} (hlo : ‖(t.q : K)‖ < ‖(u : K)‖) :
    ‖t.Yterm u (-1)‖ = ‖(t.q : K)‖ / ‖(u : K)‖ := by
  have h1 : 1 < ‖(t.q : K) ^ (-1 : ℤ) * (u : K)‖ := by
    rw [t.norm_qzpow_neg_one_mul u]
    exact (one_lt_div t.norm_q_pos).mpr hlo
  rw [t.norm_Yterm_of_one_lt_norm h1, t.norm_qzpow_neg_one_mul u, inv_div]

/-! ### Uniform `O(q)`-bounds on the non-leading terms -/

/-- If the base point is small, `‖qⁿu‖ ≤ ‖q‖`, then both coordinate terms are `O(q)`. -/
private lemma norm_term_le_of_norm_le {u : Kˣ} {n : ℤ}
    (h : ‖(t.q : K) ^ n * (u : K)‖ ≤ ‖(t.q : K)‖) :
    ‖t.Xterm u n‖ ≤ ‖(t.q : K)‖ ∧ ‖t.Yterm u n‖ ≤ ‖(t.q : K)‖ := by
  have h1 : ‖(t.q : K) ^ n * (u : K)‖ < 1 := lt_of_le_of_lt h t.norm_lt_one
  refine ⟨by rw [t.norm_Xterm_of_norm_lt_one h1]; exact h, ?_⟩
  rw [t.norm_Yterm_of_norm_lt_one h1]
  calc ‖(t.q : K) ^ n * (u : K)‖ ^ 2
      = ‖(t.q : K) ^ n * (u : K)‖ * ‖(t.q : K) ^ n * (u : K)‖ := pow_two _
    _ ≤ ‖(t.q : K)‖ * 1 := mul_le_mul h h1.le (norm_nonneg _) t.norm_q_pos.le
    _ = ‖(t.q : K)‖ := mul_one _

/-- If the base point is large, `‖q‖⁻¹ ≤ ‖qⁿu‖`, then both coordinate terms are `O(q)`. -/
private lemma norm_term_le_of_inv_norm_le {u : Kˣ} {n : ℤ}
    (h : ‖(t.q : K)‖⁻¹ ≤ ‖(t.q : K) ^ n * (u : K)‖) :
    ‖t.Xterm u n‖ ≤ ‖(t.q : K)‖ ∧ ‖t.Yterm u n‖ ≤ ‖(t.q : K)‖ := by
  have h1 : 1 < ‖(t.q : K) ^ n * (u : K)‖ :=
    lt_of_lt_of_le ((one_lt_inv₀ t.norm_q_pos).mpr t.norm_lt_one) h
  have hbound : ‖(t.q : K) ^ n * (u : K)‖⁻¹ ≤ ‖(t.q : K)‖ := by
    calc ‖(t.q : K) ^ n * (u : K)‖⁻¹
        ≤ (‖(t.q : K)‖⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr t.norm_q_pos) h
      _ = ‖(t.q : K)‖ := inv_inv _
  exact ⟨by rw [t.norm_Xterm_of_one_lt_norm h1]; exact hbound,
    by rw [t.norm_Yterm_of_one_lt_norm h1]; exact hbound⟩

/-- **Unit-sphere tail bound.** For `‖u‖ = 1` and `n ≠ 0`, both coordinate terms are
`O(q)`: the base point `qⁿu` has norm `‖q‖ⁿ ≤ ‖q‖` for `n ≥ 1` and `‖q‖ⁿ ≥ ‖q‖⁻¹` for
`n ≤ -1`. -/
private lemma norm_term_le_sphere {u : Kˣ} (hu : ‖(u : K)‖ = 1) {n : ℤ} (hn : n ≠ 0) :
    ‖t.Xterm u n‖ ≤ ‖(t.q : K)‖ ∧ ‖t.Yterm u n‖ ≤ ‖(t.q : K)‖ := by
  have hq0 : (0 : ℝ) < ‖(t.q : K)‖ := t.norm_q_pos
  have hbase : ‖(t.q : K) ^ n * (u : K)‖ = ‖(t.q : K)‖ ^ n := by
    rw [norm_mul, norm_zpow, hu, mul_one]
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · refine t.norm_term_le_of_inv_norm_le ?_
    rw [hbase]
    calc ‖(t.q : K)‖⁻¹ = ‖(t.q : K)‖ ^ (-1 : ℤ) := (zpow_neg_one _).symm
      _ ≤ ‖(t.q : K)‖ ^ n :=
          zpow_le_zpow_right_of_le_one₀ hq0 t.norm_lt_one.le (by omega)
  · refine t.norm_term_le_of_norm_le ?_
    rw [hbase]
    calc ‖(t.q : K)‖ ^ n ≤ ‖(t.q : K)‖ ^ (1 : ℤ) :=
          zpow_le_zpow_right_of_le_one₀ hq0 t.norm_lt_one.le (by omega)
      _ = ‖(t.q : K)‖ := zpow_one _

/-- **Middle-annulus tail bound.** For `‖q‖ < ‖u‖ < 1` and `n ∉ {0, -1}`, both coordinate
terms are `O(q)`: the base point has norm `‖q‖ⁿ‖u‖ ≤ ‖q‖‖u‖ ≤ ‖q‖` for `n ≥ 1` and
`‖q‖ⁿ‖u‖ ≥ ‖q‖⁻²‖u‖ > ‖q‖⁻¹` for `n ≤ -2`. -/
private lemma norm_term_le_annulus {u : Kˣ} (hlo : ‖(t.q : K)‖ < ‖(u : K)‖)
    (hhi : ‖(u : K)‖ < 1) {n : ℤ} (hn0 : n ≠ 0) (hn1 : n ≠ -1) :
    ‖t.Xterm u n‖ ≤ ‖(t.q : K)‖ ∧ ‖t.Yterm u n‖ ≤ ‖(t.q : K)‖ := by
  have hq0 : (0 : ℝ) < ‖(t.q : K)‖ := t.norm_q_pos
  have hbase : ‖(t.q : K) ^ n * (u : K)‖ = ‖(t.q : K)‖ ^ n * ‖(u : K)‖ := by
    rw [norm_mul, norm_zpow]
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  · -- `n ≤ -2`
    refine t.norm_term_le_of_inv_norm_le ?_
    rw [hbase]
    have hpow : ‖(t.q : K)‖ ^ (-2 : ℤ) * ‖(t.q : K)‖ = ‖(t.q : K)‖⁻¹ := by
      rw [show (-2 : ℤ) = -1 + -1 from by norm_num, zpow_add₀ hq0.ne', zpow_neg_one]
      exact inv_mul_cancel_right₀ hq0.ne' _
    calc ‖(t.q : K)‖⁻¹ = ‖(t.q : K)‖ ^ (-2 : ℤ) * ‖(t.q : K)‖ := hpow.symm
      _ ≤ ‖(t.q : K)‖ ^ (-2 : ℤ) * ‖(u : K)‖ :=
          mul_le_mul_of_nonneg_left hlo.le (zpow_pos hq0 _).le
      _ ≤ ‖(t.q : K)‖ ^ n * ‖(u : K)‖ :=
          mul_le_mul_of_nonneg_right
            (zpow_le_zpow_right_of_le_one₀ hq0 t.norm_lt_one.le (by omega)) (norm_nonneg _)
  · -- `n ≥ 1`
    refine t.norm_term_le_of_norm_le ?_
    rw [hbase]
    have hq_le : ‖(t.q : K)‖ ^ n ≤ ‖(t.q : K)‖ := by
      calc ‖(t.q : K)‖ ^ n ≤ ‖(t.q : K)‖ ^ (1 : ℤ) :=
            zpow_le_zpow_right_of_le_one₀ hq0 t.norm_lt_one.le (by omega)
        _ = ‖(t.q : K)‖ := zpow_one _
    calc ‖(t.q : K)‖ ^ n * ‖(u : K)‖
        ≤ ‖(t.q : K)‖ * ‖(u : K)‖ := mul_le_mul_of_nonneg_right hq_le (norm_nonneg _)
      _ ≤ ‖(t.q : K)‖ * 1 := mul_le_mul_of_nonneg_left hhi.le hq0.le
      _ = ‖(t.q : K)‖ := mul_one _

variable [CompleteSpace K]

/-- The Eisenstein constant of the `X`-series is `O(q)`: `‖2 s₁(q)‖ ≤ ‖q‖`. -/
private lemma norm_two_mul_eisenstein_le : ‖2 * t.eisenstein 1‖ ≤ ‖(t.q : K)‖ := by
  rw [norm_mul]
  calc ‖(2 : K)‖ * ‖t.eisenstein 1‖
      ≤ 1 * ‖(t.q : K)‖ := by
        gcongr
        · simpa using IsUltrametricDist.norm_natCast_le_one K 2
        · exact t.norm_eisenstein_le 1
    _ = ‖(t.q : K)‖ := one_mul _

/-! ### Leading-term approximation on the unit sphere -/

/-- **Unit-sphere approximation of `X`.** For `‖u‖ = 1` the Tate `X`-coordinate is the
node coordinate `u/(1-u)²` up to an error of norm `≤ ‖q‖`: every series term with `n ≠ 0`
and the Eisenstein constant are `O(q)`. -/
theorem norm_X_sub_node_le {u : Kˣ} (hu : ‖(u : K)‖ = 1) :
    ‖t.X u - (u : K) / (1 - (u : K)) ^ 2‖ ≤ ‖(t.q : K)‖ := by
  have hkey : t.X u - (u : K) / (1 - (u : K)) ^ 2
      = (∑' n : ℤ, if n = 0 then 0 else t.Xterm u n) - 2 * t.eisenstein 1 := by
    rw [X_apply, (t.Xterm_summable u).tsum_eq_add_tsum_ite 0, t.Xterm_zero_apply u]
    ring
  rw [hkey, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n => ?_
    by_cases hn : n = 0
    · rw [if_pos hn, norm_zero]; exact norm_nonneg _
    · rw [if_neg hn]
      exact (t.norm_term_le_sphere hu hn).1
  · rw [norm_neg]
    exact t.norm_two_mul_eisenstein_le

/-- **Unit-sphere approximation of `Y`.** For `‖u‖ = 1` the Tate `Y`-coordinate is the
node coordinate `u²/(1-u)³` up to an error of norm `≤ ‖q‖`. -/
theorem norm_Y_sub_node_le {u : Kˣ} (hu : ‖(u : K)‖ = 1) :
    ‖t.Y u - (u : K) ^ 2 / (1 - (u : K)) ^ 3‖ ≤ ‖(t.q : K)‖ := by
  have hkey : t.Y u - (u : K) ^ 2 / (1 - (u : K)) ^ 3
      = (∑' n : ℤ, if n = 0 then 0 else t.Yterm u n) + t.eisenstein 1 := by
    rw [Y_apply, (t.Yterm_summable u).tsum_eq_add_tsum_ite 0, t.Yterm_zero_apply u]
    ring
  rw [hkey]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n => ?_
    by_cases hn : n = 0
    · rw [if_pos hn, norm_zero]; exact norm_nonneg _
    · rw [if_neg hn]
      exact (t.norm_term_le_sphere hu hn).2
  · exact t.norm_eisenstein_le 1

/-! ### Leading-term approximation on the middle annulus -/

/-- **Middle-annulus approximation of `X`.** For `‖q‖ < ‖u‖ < 1` the Tate `X`-coordinate
is the sum of its `n = 0` and `n = -1` terms up to an error of norm `≤ ‖q‖`. -/
theorem norm_X_sub_annulus_le {u : Kˣ} (hlo : ‖(t.q : K)‖ < ‖(u : K)‖)
    (hhi : ‖(u : K)‖ < 1) :
    ‖t.X u - t.Xterm u 0 - t.Xterm u (-1)‖ ≤ ‖(t.q : K)‖ := by
  classical
  have hg : Summable (fun n : ℤ => if n = 0 then 0 else t.Xterm u n) := by
    have heq : (fun n : ℤ => if n = 0 then 0 else t.Xterm u n)
        = Function.update (t.Xterm u) 0 0 := by
      funext n
      rw [Function.update_apply]
    rw [heq]
    exact (t.Xterm_summable u).update 0 0
  have hkey : t.X u - t.Xterm u 0 - t.Xterm u (-1)
      = (∑' n : ℤ, if n = -1 then 0 else if n = 0 then 0 else t.Xterm u n)
        - 2 * t.eisenstein 1 := by
    rw [X_apply, (t.Xterm_summable u).tsum_eq_add_tsum_ite 0, hg.tsum_eq_add_tsum_ite (-1)]
    rw [if_neg (by norm_num : ¬ ((-1 : ℤ) = 0))]
    ring
  rw [hkey, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n => ?_
    by_cases hn1 : n = -1
    · rw [if_pos hn1, norm_zero]; exact norm_nonneg _
    · rw [if_neg hn1]
      by_cases hn0 : n = 0
      · rw [if_pos hn0, norm_zero]; exact norm_nonneg _
      · rw [if_neg hn0]
        exact (t.norm_term_le_annulus hlo hhi hn0 hn1).1
  · rw [norm_neg]
    exact t.norm_two_mul_eisenstein_le

/-- **Middle-annulus approximation of `Y`.** For `‖q‖ < ‖u‖ < 1` the Tate `Y`-coordinate
is the sum of its `n = 0` and `n = -1` terms up to an error of norm `≤ ‖q‖`. -/
theorem norm_Y_sub_annulus_le {u : Kˣ} (hlo : ‖(t.q : K)‖ < ‖(u : K)‖)
    (hhi : ‖(u : K)‖ < 1) :
    ‖t.Y u - t.Yterm u 0 - t.Yterm u (-1)‖ ≤ ‖(t.q : K)‖ := by
  classical
  have hg : Summable (fun n : ℤ => if n = 0 then 0 else t.Yterm u n) := by
    have heq : (fun n : ℤ => if n = 0 then 0 else t.Yterm u n)
        = Function.update (t.Yterm u) 0 0 := by
      funext n
      rw [Function.update_apply]
    rw [heq]
    exact (t.Yterm_summable u).update 0 0
  have hkey : t.Y u - t.Yterm u 0 - t.Yterm u (-1)
      = (∑' n : ℤ, if n = -1 then 0 else if n = 0 then 0 else t.Yterm u n)
        + t.eisenstein 1 := by
    rw [Y_apply, (t.Yterm_summable u).tsum_eq_add_tsum_ite 0, hg.tsum_eq_add_tsum_ite (-1)]
    rw [if_neg (by norm_num : ¬ ((-1 : ℤ) = 0))]
    ring
  rw [hkey]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n => ?_
    by_cases hn1 : n = -1
    · rw [if_pos hn1, norm_zero]; exact norm_nonneg _
    · rw [if_neg hn1]
      by_cases hn0 : n = 0
      · rw [if_pos hn0, norm_zero]; exact norm_nonneg _
      · rw [if_neg hn0]
        exact (t.norm_term_le_annulus hlo hhi hn0 hn1).2
  · exact t.norm_eisenstein_le 1

/-! ### Curve-side norm classification -/

/-- **Integral points stay integral.** On the Tate curve `y² + xy = x³ + a₄x + a₆`
(residue characteristic `≠ 2, 3`), an affine point with `‖x‖ ≤ 1` has `‖y‖ ≤ 1`: otherwise
`‖y² + xy‖ = ‖y‖² > 1` would exceed the norm of the right-hand side, which is `≤ 1` by the
integrality `‖a₄‖, ‖a₆‖ ≤ ‖q‖ < 1`. -/
theorem norm_y_le_one_of_norm_x_le_one (h12 : ‖(12 : K)‖ = 1) {x y : K}
    (hxy : y ^ 2 + x * y = x ^ 3 + t.a₄ * x + t.a₆) (hx : ‖x‖ ≤ 1) : ‖y‖ ≤ 1 := by
  by_contra hcon
  rw [not_le] at hcon
  have hy0 : (0 : ℝ) < ‖y‖ := lt_trans one_pos hcon
  have hxy_lt : ‖x‖ * ‖y‖ < ‖y‖ * ‖y‖ :=
    mul_lt_mul_of_pos_right (lt_of_le_of_lt hx hcon) hy0
  have hne : ‖y ^ 2‖ ≠ ‖x * y‖ := by
    rw [norm_pow, norm_mul, pow_two]
    exact hxy_lt.ne'
  have hL : ‖y ^ 2 + x * y‖ = ‖y‖ ^ 2 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_pow, norm_mul]
    exact max_eq_left (by rw [pow_two]; exact hxy_lt.le)
  have hR : ‖x ^ 3 + t.a₄ * x + t.a₆‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) hx
      · rw [norm_mul]
        exact mul_le_one₀ (t.norm_a₄_le.trans t.norm_lt_one.le) (norm_nonneg _) hx
    · exact (t.norm_a₆_le h12).trans t.norm_lt_one.le
  have hcontra : ‖y‖ ^ 2 ≤ 1 := by
    rw [← hL, hxy]
    exact hR
  nlinarith

/-- **Deep-zone norm classification on the Tate curve.** For an affine point of `E_q` with
`‖x‖² ≤ ‖q‖` and `‖x‖ < 1` (residue characteristic `≠ 2, 3`), the right-hand side
`x³ + a₄x + a₆` of the Weierstrass equation has norm exactly `‖q‖` — its leading term is
`a₆ = -q + O(q²)` — and the ultrametric analysis of `‖y‖·‖y + x‖ = ‖q‖` forces
`‖y‖² = ‖q‖` together with `‖x‖ ≤ ‖y‖`.

The a-priori disjunction (either `‖y‖² = ‖q‖`, or the boundary case `‖x‖² = ‖q‖` with
`‖y‖ ≤ ‖x‖`) collapses: `‖y‖ < ‖x‖` would give `‖q‖ = ‖y‖·‖x‖ < ‖x‖² ≤ ‖q‖`, and
`‖y‖ = ‖x‖` forces `‖x‖² = ‖q‖ = ‖y‖²`, so the first alternative always holds. -/
theorem norm_y_sq_eq_of_node (h12 : ‖(12 : K)‖ = 1) {x y : K}
    (hxy : y ^ 2 + x * y = x ^ 3 + t.a₄ * x + t.a₆)
    (hx : ‖x‖ ^ 2 ≤ ‖(t.q : K)‖) (hx1 : ‖x‖ < 1) :
    ‖y‖ ^ 2 = ‖(t.q : K)‖ ∧ ‖x‖ ≤ ‖y‖ := by
  have hq0 : (0 : ℝ) < ‖(t.q : K)‖ := t.norm_q_pos
  -- the non-`q` part of the right-hand side is strictly smaller than `‖q‖`
  have hsmall : ‖x ^ 3 + t.a₄ * x + (t.a₆ + (t.q : K))‖ < ‖(t.q : K)‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_pow]
        nlinarith [norm_nonneg x, mul_le_mul_of_nonneg_left hx (norm_nonneg x),
          mul_lt_mul_of_pos_right hx1 hq0]
      · rw [norm_mul]
        nlinarith [norm_nonneg x, mul_le_mul_of_nonneg_right t.norm_a₄_le (norm_nonneg x),
          mul_lt_mul_of_pos_left hx1 hq0]
    · exact lt_of_le_of_lt (t.norm_a₆_add_q_le h12) t.norm_q_sq_lt
  -- hence the right-hand side has norm exactly `‖q‖`
  have hRHS : ‖x ^ 3 + t.a₄ * x + t.a₆‖ = ‖(t.q : K)‖ := by
    have hrw : x ^ 3 + t.a₄ * x + t.a₆
        = (x ^ 3 + t.a₄ * x + (t.a₆ + (t.q : K))) + -(t.q : K) := by ring
    rw [hrw, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg]; exact hsmall.ne), norm_neg, max_eq_right hsmall.le]
  have hL : ‖y‖ * ‖y + x‖ = ‖(t.q : K)‖ := by
    rw [← norm_mul, show y * (y + x) = y ^ 2 + x * y from by ring, hxy]
    exact hRHS
  rcases lt_trichotomy ‖y‖ ‖x‖ with hlt | heq | hgt
  · -- `‖y‖ < ‖x‖` is impossible: `‖q‖ = ‖y‖·‖x‖ < ‖x‖² ≤ ‖q‖`
    exfalso
    have hx0 : (0 : ℝ) < ‖x‖ := lt_of_le_of_lt (norm_nonneg y) hlt
    have hyx : ‖y + x‖ = ‖x‖ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le]
    rw [hyx] at hL
    nlinarith [mul_lt_mul_of_pos_right hlt hx0]
  · -- `‖y‖ = ‖x‖` forces the boundary `‖x‖² = ‖q‖ = ‖y‖²`
    have hyx_le : ‖y + x‖ ≤ ‖y‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      exact le_of_eq (by rw [← heq, max_self])
    have hQle : ‖(t.q : K)‖ ≤ ‖y‖ ^ 2 := by
      calc ‖(t.q : K)‖ = ‖y‖ * ‖y + x‖ := hL.symm
        _ ≤ ‖y‖ * ‖y‖ := mul_le_mul_of_nonneg_left hyx_le (norm_nonneg y)
        _ = ‖y‖ ^ 2 := (pow_two _).symm
    have hyQ : ‖y‖ ^ 2 ≤ ‖(t.q : K)‖ := by
      rw [heq]
      exact hx
    exact ⟨le_antisymm hyQ hQle, le_of_eq heq.symm⟩
  · -- `‖x‖ < ‖y‖`: the generic branch `‖y‖² = ‖q‖`
    have hyx : ‖y + x‖ = ‖y‖ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hgt.ne', max_eq_left hgt.le]
    rw [hyx] at hL
    exact ⟨by rw [pow_two]; exact hL, hgt.le⟩

end Nonarchimedean

end TateParameter

end TateCurvesTheta
