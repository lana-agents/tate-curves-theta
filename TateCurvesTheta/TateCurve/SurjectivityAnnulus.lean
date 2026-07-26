/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.TateCurve.GroupLaw
import TateCurvesTheta.TateCurve.SphereBounds

/-!
# Surjectivity of the Tate parametrization on the open unit polydisc

Every affine point `(x, y)` of the Tate curve `E_q` with `‖x‖ < 1` and `‖y‖ < 1` lies in the
range of the Tate point map `u ↦ (X(u), Y(u))`. Together with the large-point surjectivity
`exists_tatePoint_eq_some` (`TateCurve/GroupLaw.lean`), this is the last analytic zone of the
surjectivity of the Tate uniformization `Kˣ/qᶻ → E_q(K)`.

The method is **translation to the large region** — no Newton iteration. Given a small point
`P = (x, y)`, we add an explicit Tate point `P(s)` with `s` in the middle annulus
`‖q‖ < ‖s‖ < 1`, chosen from the coordinates of `P` so that the secant slope `λ` through `P`
and `P(s)` has `‖λ‖ > 1`. The ultrametric dominance `‖λ² + λ - x - X(s)‖ = ‖λ‖² > 1` then
places the sum `P + P(s)` in the solved region `1 < ‖x'‖`, and subtracting `P(s)` via the
group homomorphism (`tatePoint_mul`, `tatePoint_inv`) recovers `P` as a Tate point. The two
zones are:

* **middle zone** `‖q‖ < ‖x‖²`: translate by `s = q/x`. The exact value
  `Xterm s (-1) = x/(1-x)²` makes `s` a near-hit, `‖x - X(s)‖ ≤ max ‖x‖² (‖q‖/‖x‖)`, while
  the curve equation forces `‖2y + x‖ = ‖x‖`; since the two secant slopes of the branches
  `P`, `-P` differ by `(2y + x)/(x - X(s))`, one branch has `‖λ‖ > 1` (**branch pair**).
* **edge zone** `‖x‖² ≤ ‖q‖`: here `‖y‖² = ‖q‖` and `‖x‖ ≤ ‖y‖`
  (`norm_y_sq_eq_of_node`); translate by `s = -y`. The chord–slope identity
  `(y - Y(s))·(y + Y(s) + x) = (x - X(s))·(x² + xX(s) + X(s)² + a₄ - Y(s))`, valid for any
  two curve points, expresses `λ` as a quotient whose numerator has norm exactly
  `‖Y(s)‖ = ‖y‖` and whose denominator is `O(q)` by the key identity
  `y·(x + y + q/y) = x³ + a₄x + (a₆ + q)`; hence `‖λ‖ ≥ ‖y‖⁻¹ > 1` — an automatic
  near-hit with no sub-cases, valid up to and including the `2`-torsion vicinity.

If the chosen translate happens to satisfy `X(s) = x` exactly, the two curve equations factor
as `(y - Y(s))·(y + Y(s) + x) = 0`, so `P = P(s)` or `P = -P(s) = P(s⁻¹)` (**exact-hit
short-circuit**).

## Main results

* `TateCurvesTheta.TateParameter.notMem_qpowers_of_norm_lt`: units of the open middle annulus
  avoid `qᶻ`.
* `TateCurvesTheta.TateParameter.Xterm_neg_one_eq`, `Yterm_neg_one_eq`: closed forms
  `Xterm u (-1) = c/(1-c)²`, `Yterm u (-1) = -c/(1-c)³` for `c = q/u`.
* `TateCurvesTheta.TateParameter.mem_range_tatePoint_of_X_eq`: the exact-hit short-circuit.
* `TateCurvesTheta.TateParameter.mem_range_tatePoint_of_one_lt_slope`: the translation
  engine — a translate with secant slope of norm `> 1` puts the point in the range.
* `TateCurvesTheta.TateParameter.mem_range_tatePoint_of_annulus`: surjectivity onto all
  affine points with `‖x‖ < 1` and `‖y‖ < 1`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, §4.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* P. Roquette, *Analytic theory of elliptic functions over local fields*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-! ### Norm and value preliminaries -/

omit [CompleteSpace K] in
/-- The ultrametric triangle inequality for differences. -/
private lemma norm_sub_le_max (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max a (-b)).trans (le_of_eq (by rw [norm_neg]))

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- A unit whose norm lies strictly between `‖q‖` and `1` avoids the orbit subgroup `qᶻ`:
the norms `‖q‖ⁿ` are `≥ 1` for `n ≤ 0` and `≤ ‖q‖` for `n ≥ 1`. -/
lemma notMem_qpowers_of_norm_lt {s : Kˣ} (hlo : ‖(t.q : K)‖ < ‖(s : K)‖)
    (hhi : ‖(s : K)‖ < 1) : s ∉ t.qpowers := by
  intro hmem'
  obtain ⟨n, hn⟩ := t.mem_qpowers_iff_val_eq.mp hmem'
  have hnorm : ‖(s : K)‖ = ‖(t.q : K)‖ ^ n := by rw [hn, norm_zpow]
  rcases le_or_gt n 0 with hn0 | hn0
  · have hge : (1 : ℝ) ≤ ‖(t.q : K)‖ ^ n := by
      calc (1 : ℝ) = ‖(t.q : K)‖ ^ (0 : ℤ) := (zpow_zero _).symm
        _ ≤ ‖(t.q : K)‖ ^ n :=
            zpow_le_zpow_right_of_le_one₀ t.norm_q_pos t.norm_lt_one.le hn0
    rw [hnorm] at hhi
    linarith
  · have hle : ‖(t.q : K)‖ ^ n ≤ ‖(t.q : K)‖ := by
      calc ‖(t.q : K)‖ ^ n ≤ ‖(t.q : K)‖ ^ (1 : ℤ) :=
            zpow_le_zpow_right_of_le_one₀ t.norm_q_pos t.norm_lt_one.le (by omega)
        _ = ‖(t.q : K)‖ := zpow_one _
    rw [hnorm] at hlo
    linarith

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **Closed form of the subleading `X`-term.** For a unit `u` and `c` with `u·c = q`
(that is, `c = q/u`), the `n = -1` term of the `X`-series is exactly `c/(1-c)²`. -/
lemma Xterm_neg_one_eq {u : Kˣ} {c : K} (huc : (u : K) * c = (t.q : K)) (hc1 : c ≠ 1) :
    t.Xterm u (-1) = c / (1 - c) ^ 2 := by
  have hu0 : (u : K) ≠ 0 := Units.ne_zero u
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at huc
    exact t.q.ne_zero huc.symm
  have harg : (t.q : K) ^ (-1 : ℤ) * (u : K) = c⁻¹ := by
    rw [zpow_neg_one, ← huc, mul_inv, mul_comm ((u : K)⁻¹) c⁻¹, mul_assoc,
      inv_mul_cancel₀ hu0, mul_one]
  have h1c : (1 : K) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have h1ci : (1 : K) - c⁻¹ ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hc1 (inv_eq_one.mp h.symm)
  rw [Xterm_apply, harg, div_eq_div_iff (pow_ne_zero 2 h1ci) (pow_ne_zero 2 h1c)]
  field_simp
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **Closed form of the subleading `Y`-term.** For a unit `u` and `c` with `u·c = q`,
the `n = -1` term of the `Y`-series is exactly `-c/(1-c)³` (note the sign: the value of
`w²/(1-w)³` at `w = c⁻¹` is `c/(c-1)³`). -/
lemma Yterm_neg_one_eq {u : Kˣ} {c : K} (huc : (u : K) * c = (t.q : K)) (hc1 : c ≠ 1) :
    t.Yterm u (-1) = -(c / (1 - c) ^ 3) := by
  have hu0 : (u : K) ≠ 0 := Units.ne_zero u
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at huc
    exact t.q.ne_zero huc.symm
  have harg : (t.q : K) ^ (-1 : ℤ) * (u : K) = c⁻¹ := by
    rw [zpow_neg_one, ← huc, mul_inv, mul_comm ((u : K)⁻¹) c⁻¹, mul_assoc,
      inv_mul_cancel₀ hu0, mul_one]
  have h1c : (1 : K) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have h1ci : (1 : K) - c⁻¹ ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hc1 (inv_eq_one.mp h.symm)
  rw [Yterm_apply, harg, ← neg_div, div_eq_div_iff (pow_ne_zero 3 h1ci) (pow_ne_zero 3 h1c)]
  field_simp
  ring

/-! ### The translation engine -/

variable (hmem : ∀ u : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) →
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u)) (h12 : ‖(12 : K)‖ = 1)

/-- **Exact-hit short-circuit.** If a translate `s` off the orbit satisfies `X(s) = x`, then
the two curve equations factor as `(y - Y(s))·(y + Y(s) + x) = 0`, so the point `(x, y)` is
`P(s)` or `-P(s) = P(s⁻¹)`; either way it lies in the range of the Tate point map. -/
lemma mem_range_tatePoint_of_X_eq {x y : K}
    (hns : t.tateCurve.toAffine.Nonsingular x y) {s : Kˣ} (hs : s ∉ t.qpowers)
    (hXeq : t.X s = x) :
    ∃ u : Kˣ, t.tatePoint hmem h12 u = .some x y hns := by
  have hxy : y ^ 2 + x * y = x ^ 3 + t.a₄ * x + t.a₆ :=
    (t.tateCurve_equation_iff x y).mp hns.1
  have hcs : t.Y s ^ 2 + t.X s * t.Y s = t.X s ^ 3 + t.a₄ * t.X s + t.a₆ :=
    (t.tateCurve_equation_iff _ _).mp (hmem s (t.qzpow_mul_ne_one_of_notMem hs))
  rw [hXeq] at hcs
  have hfac : (y - t.Y s) * (y + t.Y s + x) = 0 := by linear_combination hxy - hcs
  rcases mul_eq_zero.mp hfac with h0 | h0
  · -- `y = Y(s)`: the point is the Tate point of `s`
    refine ⟨s, ?_⟩
    rw [t.tatePoint_of_notMem hmem h12 hs]
    exact point_some_congr hXeq (sub_eq_zero.mp h0).symm
  · -- `y = -Y(s) - x`: the point is the negation, the Tate point of `s⁻¹`
    refine ⟨s⁻¹, ?_⟩
    rw [t.tatePoint_inv hmem h12, t.tatePoint_of_notMem hmem h12 hs,
      WeierstrassCurve.Affine.Point.neg_some]
    refine point_some_congr hXeq ?_
    rw [WeierstrassCurve.Affine.negY, tateCurve_a₁, tateCurve_a₃]
    linear_combination -h0 - hXeq

/-- **The translation engine.** If a translate `s` off the orbit has `X(s) ≠ x`, both
abscissae have norm `< 1`, and the secant slope through `(x, y)` and `(X(s), Y(s))` has norm
`> 1`, then the sum `P + P(s)` lands in the large region `1 < ‖x'‖` — solved by
`exists_tatePoint_eq_some` — and subtracting `P(s)` recovers `P` as a Tate point. -/
lemma mem_range_tatePoint_of_one_lt_slope {x y : K}
    (hns : t.tateCurve.toAffine.Nonsingular x y) {s : Kˣ} (hs : s ∉ t.qpowers)
    (hXne : t.X s ≠ x) (hx1 : ‖x‖ < 1) (hXs1 : ‖t.X s‖ < 1)
    (hlam : 1 < ‖(y - t.Y s) / (x - t.X s)‖) :
    ∃ u : Kˣ, t.tatePoint hmem h12 u = .some x y hns := by
  classical
  haveI := t.tateCurve_isElliptic h12
  have hxne : x ≠ t.X s := hXne.symm
  have hns_s : t.tateCurve.toAffine.Nonsingular (t.X s) (t.Y s) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (hmem s (t.qzpow_mul_ne_one_of_notMem hs))
  -- the secant slope has norm `> 1`
  have hslope : t.tateCurve.toAffine.slope x (t.X s) y (t.Y s)
      = (y - t.Y s) / (x - t.X s) := WeierstrassCurve.Affine.slope_of_X_ne hxne
  have hl1 : 1 < ‖t.tateCurve.toAffine.slope x (t.X s) y (t.Y s)‖ := by
    rw [hslope]; exact hlam
  -- hence the `X`-coordinate of the sum has norm `‖λ‖² > 1`
  have hlarge : 1 <
      ‖t.tateCurve.toAffine.addX x (t.X s) (t.tateCurve.toAffine.slope x (t.X s) y (t.Y s))‖ := by
    set l : K := t.tateCurve.toAffine.slope x (t.X s) y (t.Y s) with hl_def
    have haddX : t.tateCurve.toAffine.addX x (t.X s) l = l ^ 2 + (l - x - t.X s) := by
      rw [WeierstrassCurve.Affine.addX, tateCurve_a₁, tateCurve_a₂]
      ring
    have hrest : ‖l - x - t.X s‖ < ‖l ^ 2‖ := by
      rw [norm_pow]
      have h1 : ‖l - x - t.X s‖ ≤ ‖l‖ :=
        (norm_sub_le_max _ _).trans (max_le ((norm_sub_le_max _ _).trans
          (max_le le_rfl (hx1.le.trans hl1.le))) (hXs1.le.trans hl1.le))
      nlinarith [norm_nonneg l]
    rw [haddX, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrest.ne',
      max_eq_left hrest.le, norm_pow]
    nlinarith [norm_nonneg l]
  -- the sum is a Tate point of some unit `v`
  have hQns := WeierstrassCurve.Affine.nonsingular_negAdd hns hns_s fun hxy => hxne hxy.left
  obtain ⟨v, hv⟩ := t.exists_tatePoint_eq_some hmem h12 hQns hlarge
  have hadd := WeierstrassCurve.Affine.Point.add_of_X_ne' (h₁ := hns) (h₂ := hns_s) hxne
  have hPs : t.tatePoint hmem h12 s = .some (t.X s) (t.Y s) hns_s :=
    t.tatePoint_of_notMem hmem h12 hs
  have hsum : WeierstrassCurve.Affine.Point.some x y hns + t.tatePoint hmem h12 s
      = -t.tatePoint hmem h12 v := by
    rw [hPs, hv]
    exact hadd
  refine ⟨v⁻¹ * s⁻¹, ?_⟩
  rw [t.tatePoint_mul hmem h12, t.tatePoint_inv hmem h12, t.tatePoint_inv hmem h12, ← hsum]
  abel

/-! ### The middle zone `‖q‖ < ‖x‖²`: translate by `q/x`, branch pair -/

/-- **Middle-zone surjectivity.** An affine point with `‖q‖ < ‖x‖²` and `‖x‖ < 1` is a Tate
point. The translate `s = q/x` is a near-hit: by the exact value `Xterm s (-1) = x/(1-x)²`,
`‖x - X(s)‖ ≤ max ‖x‖² (‖q‖/‖x‖) < ‖x‖`, while the curve equation forces `‖2y + x‖ = ‖x‖`.
Since the secant slopes of the two branches `P`, `-P` differ by `(2y + x)/(x - X(s))`, of
norm `> 1`, one branch feeds the translation engine. -/
lemma mem_range_tatePoint_of_middle_zone {x y : K}
    (hns : t.tateCurve.toAffine.Nonsingular x y) (hx1 : ‖x‖ < 1)
    (hq_lt : ‖(t.q : K)‖ < ‖x‖ ^ 2) :
    ∃ u : Kˣ, t.tatePoint hmem h12 u = .some x y hns := by
  classical
  have hxy : y ^ 2 + x * y = x ^ 3 + t.a₄ * x + t.a₆ :=
    (t.tateCurve_equation_iff x y).mp hns.1
  have hq0 : (0 : ℝ) < ‖(t.q : K)‖ := t.norm_q_pos
  have hx0' : (0 : ℝ) < ‖x‖ := by nlinarith [norm_nonneg x]
  have hx0 : x ≠ 0 := norm_pos_iff.mp hx0'
  -- the translate `s = q/x` lies in the open middle annulus
  have ht0 : (t.q : K) / x ≠ 0 := div_ne_zero t.q.ne_zero hx0
  set s : Kˣ := Units.mk0 _ ht0 with hs_def
  have hsval : (s : K) = (t.q : K) / x := rfl
  have hsnorm : ‖(s : K)‖ = ‖(t.q : K)‖ / ‖x‖ := by rw [hsval, norm_div]
  have hlo : ‖(t.q : K)‖ < ‖(s : K)‖ := by
    rw [hsnorm, lt_div_iff₀ hx0']
    nlinarith
  have hhi : ‖(s : K)‖ < 1 := by
    rw [hsnorm, div_lt_one hx0']
    nlinarith
  have hs : s ∉ t.qpowers := t.notMem_qpowers_of_norm_lt hlo hhi
  by_cases hXeq : t.X s = x
  · exact t.mem_range_tatePoint_of_X_eq hmem h12 hns hs hXeq
  -- curve-side norms: `‖y‖ ≤ ‖x‖`, hence `‖2y + x‖ = ‖x‖`
  have hRHS : ‖x ^ 3 + t.a₄ * x + t.a₆‖ < ‖x‖ ^ 2 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt
      ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)) ?_)
    · rw [norm_pow]
      nlinarith
    · rw [norm_mul]
      nlinarith [t.norm_a₄_le, norm_nonneg t.a₄, norm_nonneg x]
    · exact (t.norm_a₆_le h12).trans_lt hq_lt
  have hprod : ‖y‖ * ‖y + x‖ = ‖x ^ 3 + t.a₄ * x + t.a₆‖ := by
    rw [← norm_mul, show y * (y + x) = y ^ 2 + x * y from by ring, hxy]
  have hyx : ‖y‖ ≤ ‖x‖ := by
    by_contra hcon
    rw [not_le] at hcon
    have hplus : ‖y + x‖ = ‖y‖ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hcon.ne', max_eq_left hcon.le]
    rw [hplus] at hprod
    nlinarith
  have h2yx : ‖2 * y + x‖ = ‖x‖ := by
    rcases lt_or_eq_of_le hyx with hlt | heq
    · have h2y : ‖2 * y‖ < ‖x‖ := by
        rw [norm_mul]
        calc ‖(2 : K)‖ * ‖y‖ ≤ 1 * ‖y‖ := by
              gcongr
              simpa using IsUltrametricDist.norm_natCast_le_one K 2
          _ = ‖y‖ := one_mul _
          _ < ‖x‖ := hlt
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2y.ne, max_eq_right h2y.le]
    · have hyx_lt : ‖y + x‖ < ‖y‖ := by nlinarith [norm_nonneg (y + x)]
      rw [show 2 * y + x = y + (y + x) from by ring,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hyx_lt.ne', max_eq_left hyx_lt.le,
        heq]
  -- the near-hit bound `δ = ‖x - X(s)‖ ≤ max ‖x‖² (‖q‖/‖x‖)`
  have hx_ne_one : x ≠ 1 := by
    intro h
    rw [h, norm_one] at hx1
    exact lt_irrefl _ hx1
  have hXm1 : t.Xterm s (-1) = x / (1 - x) ^ 2 :=
    t.Xterm_neg_one_eq (by rw [hsval]; exact div_mul_cancel₀ _ hx0) hx_ne_one
  have hnorm1x : ‖(1 : K) - x‖ = 1 := by
    rw [norm_one_sub_of_norm_ne_one hx1.ne, max_eq_left hx1.le]
  have hlead : ‖x - t.Xterm s (-1)‖ ≤ ‖x‖ ^ 2 := by
    have h1x : (1 : K) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx_ne_one)
    have hval : x - t.Xterm s (-1) = x ^ 2 * (x - 2) / (1 - x) ^ 2 := by
      rw [hXm1]
      field_simp
      ring
    rw [hval, norm_div, norm_pow, hnorm1x, one_pow, div_one, norm_mul, norm_pow]
    have h2 : ‖x - (2 : K)‖ ≤ 1 := by
      refine (norm_sub_le_max _ _).trans (max_le hx1.le ?_)
      simpa using IsUltrametricDist.norm_natCast_le_one K 2
    exact mul_le_of_le_one_right (by positivity) h2
  have hE : ‖t.X s - t.Xterm s 0 - t.Xterm s (-1)‖ ≤ ‖(t.q : K)‖ :=
    t.norm_X_sub_annulus_le hlo hhi
  have hXt0 : ‖t.Xterm s 0‖ = ‖(t.q : K)‖ / ‖x‖ := by rw [t.norm_Xterm_zero hhi, hsnorm]
  have hdelta : ‖x - t.X s‖ ≤ max (‖x‖ ^ 2) (‖(t.q : K)‖ / ‖x‖) := by
    rw [show x - t.X s = (x - t.Xterm s (-1)) - t.Xterm s 0
        - (t.X s - t.Xterm s 0 - t.Xterm s (-1)) from by ring]
    refine (norm_sub_le_max _ _).trans (max_le ((norm_sub_le_max _ _).trans
      (max_le (le_max_of_le_left hlead) ?_)) ?_)
    · rw [hXt0]
      exact le_max_right _ _
    · refine le_max_of_le_right (hE.trans ?_)
      rw [le_div_iff₀ hx0']
      nlinarith
  have hM : max (‖x‖ ^ 2) (‖(t.q : K)‖ / ‖x‖) < ‖x‖ := by
    refine max_lt (by nlinarith) ?_
    rw [div_lt_iff₀ hx0']
    nlinarith
  -- `‖X(s)‖ < 1`, for the engine
  have hXs1 : ‖t.X s‖ < 1 := by
    rw [show t.X s = t.Xterm s 0 + t.Xterm s (-1)
        + (t.X s - t.Xterm s 0 - t.Xterm s (-1)) from by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt
      ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)) ?_)
    · rw [t.norm_Xterm_zero hhi]
      exact hhi
    · rw [hXm1, norm_div, norm_pow, hnorm1x, one_pow, div_one]
      exact hx1
    · exact hE.trans_lt t.norm_lt_one
  -- branch pair: one of the two secant slopes has norm `> 1`
  have hdx : x - t.X s ≠ 0 := sub_ne_zero.mpr fun h => hXeq h.symm
  have hdx' : (0 : ℝ) < ‖x - t.X s‖ := norm_pos_iff.mpr hdx
  have hbig : 1 < ‖(2 * y + x) / (x - t.X s)‖ := by
    rw [norm_div, h2yx, one_lt_div hdx']
    exact lt_of_le_of_lt hdelta hM
  have hone : 1 < ‖(y - t.Y s) / (x - t.X s)‖ ∨
      1 < ‖(-y - x - t.Y s) / (x - t.X s)‖ := by
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    have hdiff : (y - t.Y s) / (x - t.X s) - (-y - x - t.Y s) / (x - t.X s)
        = (2 * y + x) / (x - t.X s) := by
      rw [div_sub_div_same]
      congr 1
      ring
    have hle := (norm_sub_le_max ((y - t.Y s) / (x - t.X s))
      ((-y - x - t.Y s) / (x - t.X s))).trans (max_le hcon.1 hcon.2)
    rw [hdiff] at hle
    exact absurd hbig (not_lt.mpr hle)
  rcases hone with h1 | h2
  · exact t.mem_range_tatePoint_of_one_lt_slope hmem h12 hns hs hXeq hx1 hXs1 h1
  · -- the branch `-P` wins: conclude for `-P`, then negate
    haveI := t.tateCurve_isElliptic h12
    have hnegY : t.tateCurve.toAffine.negY x y = -y - x := by
      rw [WeierstrassCurve.Affine.negY, tateCurve_a₁, tateCurve_a₃]
      ring
    have hnsneg : t.tateCurve.toAffine.Nonsingular x (t.tateCurve.toAffine.negY x y) :=
      (t.tateCurve.toAffine.nonsingular_neg x y).mpr hns
    obtain ⟨v, hv⟩ := t.mem_range_tatePoint_of_one_lt_slope hmem h12 hnsneg hs hXeq hx1 hXs1
      (by rw [hnegY]; exact h2)
    refine ⟨v⁻¹, ?_⟩
    rw [t.tatePoint_inv hmem h12, hv, WeierstrassCurve.Affine.Point.neg_some]
    exact point_some_congr rfl (t.tateCurve.toAffine.negY_negY x y)

/-! ### The edge zone `‖x‖² ≤ ‖q‖`: translate by `-y`, automatic near-hit -/

/-- **Edge-zone surjectivity.** An affine point with `‖x‖² ≤ ‖q‖` and `‖x‖ < 1` — so
`‖y‖² = ‖q‖` and `‖x‖ ≤ ‖y‖` by `norm_y_sq_eq_of_node` — is a Tate point. The translate
`s = -y` is an automatic near-hit: by the chord–slope identity the secant slope is
`(x² + xX(s) + X(s)² + a₄ - Y(s)) / (y + Y(s) + x)`, whose numerator has norm exactly
`‖Y(s)‖ = ‖y‖` while the denominator is `≤ ‖q‖` by the key identity
`y·(x + y - q/s) = x³ + a₄x + (a₆ + q)`; hence `‖λ‖ ≥ ‖y‖⁻¹ > 1`, with no sub-cases —
the estimate holds up to and including the `2`-torsion vicinity. -/
lemma mem_range_tatePoint_of_edge_zone {x y : K}
    (hns : t.tateCurve.toAffine.Nonsingular x y) (hx1 : ‖x‖ < 1) (hy1 : ‖y‖ < 1)
    (hq_ge : ‖x‖ ^ 2 ≤ ‖(t.q : K)‖) :
    ∃ u : Kˣ, t.tatePoint hmem h12 u = .some x y hns := by
  classical
  have hxy : y ^ 2 + x * y = x ^ 3 + t.a₄ * x + t.a₆ :=
    (t.tateCurve_equation_iff x y).mp hns.1
  obtain ⟨hy2, hxy_le⟩ := t.norm_y_sq_eq_of_node h12 hxy hq_ge hx1
  have hq0 : (0 : ℝ) < ‖(t.q : K)‖ := t.norm_q_pos
  have hy0' : (0 : ℝ) < ‖y‖ := by nlinarith [norm_nonneg y]
  have hy0 : y ≠ 0 := norm_pos_iff.mp hy0'
  have hq_le_y : ‖(t.q : K)‖ ≤ ‖y‖ := by
    rw [← hy2]
    nlinarith
  -- the translate `s = -y` lies in the open middle annulus
  have hty : -y ≠ 0 := neg_ne_zero.mpr hy0
  set s : Kˣ := Units.mk0 _ hty with hs_def
  have hsval : (s : K) = -y := rfl
  have hsnorm : ‖(s : K)‖ = ‖y‖ := by rw [hsval, norm_neg]
  have hlo : ‖(t.q : K)‖ < ‖(s : K)‖ := by
    rw [hsnorm, ← hy2]
    nlinarith
  have hhi : ‖(s : K)‖ < 1 := by
    rw [hsnorm]
    exact hy1
  have hs : s ∉ t.qpowers := t.notMem_qpowers_of_norm_lt hlo hhi
  by_cases hXeq : t.X s = x
  · exact t.mem_range_tatePoint_of_X_eq hmem h12 hns hs hXeq
  -- the value `c = q/s = -q/y`
  set c : K := -((t.q : K) / y) with hc_def
  have hcnorm : ‖c‖ = ‖y‖ := by
    rw [hc_def, norm_neg, norm_div, ← hy2, pow_two, mul_div_assoc, div_self hy0'.ne',
      mul_one]
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, norm_one] at hcnorm
    exact hy1.ne hcnorm.symm
  have huc : (s : K) * c = (t.q : K) := by
    rw [hsval, hc_def, neg_mul_neg, mul_comm]
    exact div_mul_cancel₀ _ hy0
  have hyc : y * c = -(t.q : K) := by
    rw [hc_def, mul_neg, mul_comm y ((t.q : K) / y), div_mul_cancel₀ _ hy0]
  -- `‖Y(s)‖ = ‖y‖`: the `n = -1` term dominates
  have hEY : ‖t.Y s - t.Yterm s 0 - t.Yterm s (-1)‖ ≤ ‖(t.q : K)‖ :=
    t.norm_Y_sub_annulus_le hlo hhi
  have hYm1_norm : ‖t.Yterm s (-1)‖ = ‖y‖ := by
    rw [t.norm_Yterm_neg_one hlo, hsnorm, ← hy2, pow_two, mul_div_assoc,
      div_self hy0'.ne', mul_one]
  have hYs : ‖t.Y s‖ = ‖y‖ := by
    have hsmall : ‖t.Yterm s 0 + (t.Y s - t.Yterm s 0 - t.Yterm s (-1))‖ < ‖y‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [t.norm_Yterm_zero hhi, hsnorm]
        nlinarith
      · refine hEY.trans_lt ?_
        rw [← hy2]
        nlinarith
    rw [show t.Y s = t.Yterm s (-1) + (t.Yterm s 0
        + (t.Y s - t.Yterm s 0 - t.Yterm s (-1))) from by ring,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by rw [hYm1_norm]; exact hsmall.ne'), hYm1_norm]
    exact max_eq_left hsmall.le
  -- `‖X(s)‖ ≤ ‖y‖`
  have hEX : ‖t.X s - t.Xterm s 0 - t.Xterm s (-1)‖ ≤ ‖(t.q : K)‖ :=
    t.norm_X_sub_annulus_le hlo hhi
  have hXs_le : ‖t.X s‖ ≤ ‖y‖ := by
    rw [show t.X s = t.Xterm s 0 + t.Xterm s (-1)
        + (t.X s - t.Xterm s 0 - t.Xterm s (-1)) from by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) (hEX.trans hq_le_y))
    · exact le_of_eq (by rw [t.norm_Xterm_zero hhi, hsnorm])
    · exact le_of_eq (by rw [t.norm_Xterm_neg_one hlo, hsnorm, ← hy2, pow_two,
        mul_div_assoc, div_self hy0'.ne', mul_one])
  -- the numerator of the slope has norm exactly `‖y‖`
  have hyy : ‖y‖ ^ 2 < ‖y‖ := by nlinarith
  have hN : ‖x ^ 2 + x * t.X s + t.X s ^ 2 + t.a₄ - t.Y s‖ = ‖y‖ := by
    have hquad : ‖x ^ 2 + x * t.X s + t.X s ^ 2 + t.a₄‖ < ‖y‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt
        ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt
          ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)) ?_)) ?_)
      · rw [norm_pow]
        nlinarith [norm_nonneg x]
      · rw [norm_mul]
        nlinarith [norm_nonneg x, norm_nonneg (t.X s)]
      · rw [norm_pow]
        nlinarith [norm_nonneg (t.X s)]
      · calc ‖t.a₄‖ ≤ ‖(t.q : K)‖ := t.norm_a₄_le
          _ = ‖y‖ ^ 2 := hy2.symm
          _ < ‖y‖ := hyy
    rw [show x ^ 2 + x * t.X s + t.X s ^ 2 + t.a₄ - t.Y s
        = (x ^ 2 + x * t.X s + t.X s ^ 2 + t.a₄) + -t.Y s from by ring,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by rw [norm_neg, hYs]; exact hquad.ne),
      norm_neg, hYs, max_eq_right hquad.le]
  -- the denominator of the slope is `O(q)`, by the key curve identity
  have hkey : y * (x + y - c) = x ^ 3 + t.a₄ * x + (t.a₆ + (t.q : K)) := by
    linear_combination hxy - hyc
  have hkey_norm : ‖x + y - c‖ ≤ ‖(t.q : K)‖ := by
    have hRHS_le : ‖x ^ 3 + t.a₄ * x + (t.a₆ + (t.q : K))‖ ≤ ‖(t.q : K)‖ * ‖y‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) ?_)
      · rw [norm_pow]
        calc ‖x‖ ^ 3 ≤ ‖y‖ ^ 3 := pow_le_pow_left₀ (norm_nonneg x) hxy_le 3
          _ = ‖(t.q : K)‖ * ‖y‖ := by rw [← hy2]; ring
      · rw [norm_mul]
        exact mul_le_mul t.norm_a₄_le hxy_le (norm_nonneg x) hq0.le
      · refine (t.norm_a₆_add_q_le h12).trans ?_
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hq_le_y hq0.le
    have hcancel : ‖y‖ * ‖x + y - c‖ ≤ ‖y‖ * ‖(t.q : K)‖ := by
      rw [← norm_mul, hkey]
      exact hRHS_le.trans (le_of_eq (mul_comm _ _))
    exact le_of_mul_le_mul_left hcancel hy0'
  have hnorm1c : ‖(1 : K) - c‖ = 1 := by
    rw [norm_one_sub_of_norm_ne_one (by rw [hcnorm]; exact hy1.ne),
      max_eq_left (by rw [hcnorm]; exact hy1.le)]
  have h1c : (1 : K) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have hcube : ‖c - c / (1 - c) ^ 3‖ ≤ ‖(t.q : K)‖ := by
    have hval : c - c / (1 - c) ^ 3 = -(c ^ 2 * (3 - 3 * c + c ^ 2)) / (1 - c) ^ 3 := by
      field_simp
      ring
    rw [hval, norm_div, norm_neg, norm_mul, norm_pow, norm_pow, hnorm1c, one_pow, div_one]
    have h3le : ‖(3 : K)‖ ≤ 1 := by simpa using IsUltrametricDist.norm_natCast_le_one K 3
    have h3 : ‖(3 : K) - 3 * c + c ^ 2‖ ≤ 1 := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((norm_sub_le_max _ _).trans (max_le h3le ?_)) ?_)
      · rw [norm_mul]
        nlinarith [norm_nonneg c, norm_nonneg (3 : K)]
      · rw [norm_pow]
        nlinarith [norm_nonneg c]
    calc ‖c‖ ^ 2 * ‖(3 : K) - 3 * c + c ^ 2‖ ≤ ‖c‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = ‖(t.q : K)‖ := by rw [mul_one, hcnorm, hy2]
  have hD : ‖y + t.Y s + x‖ ≤ ‖(t.q : K)‖ := by
    have hYm1 : t.Yterm s (-1) = -(c / (1 - c) ^ 3) := t.Yterm_neg_one_eq huc hc1
    rw [show y + t.Y s + x = (x + y - c) + ((c - c / (1 - c) ^ 3)
        + (t.Yterm s 0 + (t.Y s - t.Yterm s 0 - t.Yterm s (-1)))) from by rw [hYm1]; ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hkey_norm
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hcube
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hEY)))))
    exact le_of_eq (by rw [t.norm_Yterm_zero hhi, hsnorm, hy2])
  -- the chord–slope identity forces `‖λ‖ ≥ ‖y‖⁻¹ > 1`
  have hcurve_s : t.Y s ^ 2 + t.X s * t.Y s = t.X s ^ 3 + t.a₄ * t.X s + t.a₆ :=
    (t.tateCurve_equation_iff _ _).mp (hmem s (t.qzpow_mul_ne_one_of_notMem hs))
  have hchord : (y - t.Y s) * (y + t.Y s + x)
      = (x - t.X s) * (x ^ 2 + x * t.X s + t.X s ^ 2 + t.a₄ - t.Y s) := by
    linear_combination hxy - hcurve_s
  have hdx : x - t.X s ≠ 0 := sub_ne_zero.mpr fun h => hXeq h.symm
  have hN0 : x ^ 2 + x * t.X s + t.X s ^ 2 + t.a₄ - t.Y s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hN
    exact hy0'.ne hN
  have hD0 : y + t.Y s + x ≠ 0 := by
    intro h
    rw [h, mul_zero] at hchord
    exact hN0 ((mul_eq_zero.mp hchord.symm).resolve_left hdx)
  have hlam : 1 < ‖(y - t.Y s) / (x - t.X s)‖ := by
    have hlam_eq : (y - t.Y s) / (x - t.X s)
        = (x ^ 2 + x * t.X s + t.X s ^ 2 + t.a₄ - t.Y s) / (y + t.Y s + x) := by
      rw [div_eq_div_iff hdx hD0]
      linear_combination hchord
    rw [hlam_eq, norm_div, hN, one_lt_div (norm_pos_iff.mpr hD0)]
    calc ‖y + t.Y s + x‖ ≤ ‖(t.q : K)‖ := hD
      _ = ‖y‖ ^ 2 := hy2.symm
      _ < ‖y‖ := hyy
  exact t.mem_range_tatePoint_of_one_lt_slope hmem h12 hns hs hXeq hx1
    (hXs_le.trans_lt hy1) hlam

/-! ### Assembly -/

/-- **Surjectivity of the Tate parametrization on the open unit polydisc.** Every affine
point of the Tate curve with `‖x‖ < 1` and `‖y‖ < 1` lies in the range of the Tate point
map `u ↦ (X(u), Y(u))`. Together with `exists_tatePoint_eq_some` this covers all affine
points with `‖x‖ ≠ 1`. -/
theorem mem_range_tatePoint_of_annulus {x y : K}
    (hns : t.tateCurve.toAffine.Nonsingular x y) (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    ∃ u : Kˣ, t.tatePoint hmem h12 u = WeierstrassCurve.Affine.Point.some x y hns := by
  rcases le_or_gt (‖x‖ ^ 2) ‖(t.q : K)‖ with h | h
  · exact t.mem_range_tatePoint_of_edge_zone hmem h12 hns hx hy h
  · exact t.mem_range_tatePoint_of_middle_zone hmem h12 hns hx h

end TateParameter

end TateCurvesTheta
