/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.TateCurve.CoordinateInversion
import TateCurvesTheta.TateCurve.IntegralModel
import TateCurvesTheta.TateCurve.TatePointOnCurve

/-!
# Surjectivity of the Tate parametrization onto large points

Every affine point `(x, y)` of the Tate curve `E_q : y² + xy = x³ + a₄x + a₆` with large
`x`-coordinate, `1 < ‖x‖`, is hit by the Tate parametrization: there is an *off-orbit* unit
`u : Kˣ` (i.e. `qⁿu ≠ 1` for all `n : ℤ`) with `X(u) = x` and `Y(u) = y`
(`exists_tate_coord_of_one_lt_norm`). This is the "large point" case of the surjectivity of
`Kˣ/qᶻ → E_q(K)` (Silverman, *Advanced Topics*, Ch. V, Thm 3.1).

## The ultrametric Newton iteration

The ultrametric norm bookkeeping on the curve forces `‖y‖² = ‖x‖³`
(`norm_y_sq_eq_norm_x_cube`), so `z₀ := x/y` satisfies `‖z₀‖² · ‖x‖ = 1` and `‖z₀‖ < 1`.
Writing the candidate parameter as `u = 1 + w` with `‖w‖ = ‖z₀‖ =: ρ` and splitting off the
`n = 0` term of the coordinate series,
```
X(1 + w) = (1 + w)/w² - g(w),   g(w) := 2s₁(q) - ∑_{n ≠ 0} qⁿ(1+w)/(1 - qⁿ(1+w))²,
```
the equation `X(1 + w) = x` becomes the vanishing of `h(w) := w²(x + g(w)) - w - 1`. On the
unit-ball `‖w‖ < 1` the tail satisfies the uniform bound `‖g(w)‖ ≤ ‖q‖` and — via the exact
per-term slope identity for the difference of two nodal kernels — the Lipschitz estimate
`‖g(w') - g(w)‖ ≤ ‖q‖·‖w' - w‖`.

A first-order fixed-point reformulation of the quadratic `h(w) = 0` (e.g. the map
`w ↦ (w(x + g(w)) - 1)⁻¹`) does *not* contract: its multiplier at the root is
`-(1 + w∞)`, of norm exactly `1` — the two roots `u`, `u⁻¹` of the (even) equation
`X(u) = x` make any such iteration oscillate. Instead we run a derivative-free **Newton
iteration** `w ← w - h(w)/D(w)` with the exact chord slope `D(w) := 2w(x + g(w)) - 1`,
starting at `z₀`. The curve equation gives the exact initial smallness
`h(z₀) = z₀²(g(z₀) - c)` with `c := a₄/x + a₆/x²`, so `‖h(z₀)‖ ≤ ρ²·max(‖q‖, ρ²)`, and the
algebraic expansion
```
h(w') - h(w) - (w' - w)·D(w) = (w' - w)²(x + g(w)) + w'²(g(w') - g(w))
```
yields the quadratic-decay invariant `‖w_k‖ = ρ`, `‖h(w_k)‖ ≤ κᵏ⁺¹` with
`κ := ρ²·max(‖q‖, ρ²) < 1`. The iterates are `κ`-geometrically Cauchy, and the limit `w∞`
satisfies `h(w∞) = 0`, i.e. `X(1 + w∞) = x`. Finally `(x, Y(1+w∞))` and `(x, y)` solve the
same quadratic in `y`, so `y = Y(u)` or `y = -Y(u) - x = Y(u⁻¹)` — the coordinate inversion
symmetry finishes the proof.

## The hypothesis `‖2‖ = 1`

Keeping `‖D(w)‖ = ρ⁻¹` along the iteration uses `‖2w(x + g(w))‖ = ρ⁻¹ > 1`, which needs
`‖(2 : K)‖ = 1` (residue characteristic `≠ 2`). This restriction is genuine for any such
local argument: in residue characteristic `2`, on the shell `‖x‖ = ‖2‖⁻²` the point can be
`2`-adically close to the large `2`-torsion point `(X(-1), Y(-1))`, where the two candidate
parameters `u` and `u⁻¹` collide and the quadratic for `w` degenerates; separating them
requires a global (zero-counting) argument rather than a contraction from the given point.

## Main results

* `TateParameter.norm_y_sq_eq_norm_x_cube`: on the curve, `1 < ‖x‖` forces `‖y‖² = ‖x‖³`.
* `TateParameter.exists_tate_coord_of_one_lt_norm`: every affine point with `1 < ‖x‖` is
  `(X(u), Y(u))` for an off-orbit unit `u`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* P. Roquette, *Analytic theory of elliptic functions over local fields*.
-/

open Filter Topology

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-! ### The tail series and the Newton auxiliary functions

All auxiliary functions are total (`tsum` junk values are irrelevant): every lemma about
them assumes `‖w‖ < 1`, which keeps the denominators away from zero. -/

/-- The `n`-th term of the **tail** of the `X`-coordinate series at `u = 1 + w`: the term
`qⁿ(1+w)/(1 - qⁿ(1+w))²` for `n ≠ 0`, and `0` at the split-off index `n = 0`. -/
private def tailTerm (w : K) (n : ℤ) : K :=
  if n = 0 then 0 else (t.q : K) ^ n * (1 + w) / (1 - (t.q : K) ^ n * (1 + w)) ^ 2

/-- The **tail sum** `∑_{n ≠ 0} qⁿ(1+w)/(1 - qⁿ(1+w))²` of the `X`-coordinate series. -/
private def tailSum (w : K) : K := ∑' n : ℤ, t.tailTerm w n

/-- The **small part** `g(w) := 2s₁(q) - tailSum(w)` of the `X`-coordinate at `1 + w`, so
that `X(1+w) = (1+w)/w² - g(w)`. It satisfies `‖g(w)‖ ≤ ‖q‖` on `‖w‖ < 1`. -/
private def gAux (w : K) : K := 2 * t.eisenstein 1 - t.tailSum w

/-- The **Newton objective** `h(w) := w²(x + g(w)) - w - 1`, whose vanishing (for `w ≠ 0`)
is equivalent to `X(1 + w) = x`. -/
private def hAux (x w : K) : K := w ^ 2 * (x + t.gAux w) - w - 1

/-- The **chord slope** `D(w) := 2w(x + g(w)) - 1` used as the (derivative-free) Newton
denominator; on the sphere `‖w‖ = ρ` it has norm exactly `ρ⁻¹` when `‖2‖ = 1`. -/
private def dAux (x w : K) : K := 2 * w * (x + t.gAux w) - 1

/-- The **Newton iterates** `w₀ := z`, `w_{k+1} := w_k - h(w_k)/D(w_k)`. -/
private def newtonSeq (t : TateParameter K) (x z : K) : ℕ → K
  | 0 => z
  | k + 1 =>
    newtonSeq t x z k - t.hAux x (newtonSeq t x z k) / t.dAux x (newtonSeq t x z k)

private lemma tailSum_apply (w : K) : t.tailSum w = ∑' n : ℤ, t.tailTerm w n := rfl

private lemma gAux_apply (w : K) : t.gAux w = 2 * t.eisenstein 1 - t.tailSum w := rfl

private lemma hAux_apply (x w : K) : t.hAux x w = w ^ 2 * (x + t.gAux w) - w - 1 := rfl

private lemma dAux_apply (x w : K) : t.dAux x w = 2 * w * (x + t.gAux w) - 1 := rfl

private lemma newtonSeq_zero (x z : K) : t.newtonSeq x z 0 = z := rfl

private lemma newtonSeq_succ (x z : K) (k : ℕ) :
    t.newtonSeq x z (k + 1) =
      t.newtonSeq x z k
        - t.hAux x (t.newtonSeq x z k) / t.dAux x (t.newtonSeq x z k) := rfl

/-- **The Newton expansion identity.** The second-order remainder of `hAux` along the chord
slope `dAux` is exactly `(b - a)²(x + g(a)) + b²(g(b) - g(a))` — a ring identity treating
the values of `gAux` as opaque constants. -/
private lemma hAux_sub_sub (x a b : K) :
    t.hAux x b - t.hAux x a - (b - a) * t.dAux x a
      = (b - a) ^ 2 * (x + t.gAux a) + b ^ 2 * (t.gAux b - t.gAux a) := by
  simp only [hAux_apply, dAux_apply]
  ring

/-! ### Real norm bookkeeping for the powers `‖q‖ⁿ`, `n : ℤ` -/

/-- For `1 ≤ n`, `‖q‖ⁿ ≤ ‖q‖`. -/
private lemma norm_q_zpow_le {n : ℤ} (hn : 1 ≤ n) : ‖(t.q : K)‖ ^ n ≤ ‖(t.q : K)‖ := by
  simpa using zpow_le_zpow_right_of_le_one₀ t.norm_q_pos t.norm_lt_one.le hn

/-- For `1 ≤ n`, `‖q‖ⁿ < 1`. -/
private lemma norm_q_zpow_lt_one {n : ℤ} (hn : 1 ≤ n) : ‖(t.q : K)‖ ^ n < 1 :=
  (t.norm_q_zpow_le hn).trans_lt t.norm_lt_one

/-- For `n ≤ -1`, `1 < ‖q‖ⁿ`. -/
private lemma one_lt_norm_q_zpow {n : ℤ} (hn : n ≤ -1) : 1 < ‖(t.q : K)‖ ^ n := by
  have h2 : ‖(t.q : K)‖ ^ (-n) < 1 := t.norm_q_zpow_lt_one (by omega)
  have hpos : (0 : ℝ) < ‖(t.q : K)‖ ^ (-n) := zpow_pos t.norm_q_pos _
  have := (one_lt_inv₀ hpos).mpr h2
  rwa [← zpow_neg, neg_neg] at this

section Nonarchimedean

variable [IsUltrametricDist K]

/-! ### Ultrametric norm bookkeeping near `u = 1` -/

/-- In a nonarchimedean field, `‖1 + w‖ = 1` whenever `‖w‖ < 1`. -/
private lemma norm_one_add {w : K} (hw : ‖w‖ < 1) : ‖(1 : K) + w‖ = 1 := by
  have hne : ‖(1 : K)‖ ≠ ‖w‖ := by rw [norm_one]; exact (ne_of_lt hw).symm
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, max_eq_left hw.le]

/-- The orbit point `qⁿ(1+w)` has norm `‖q‖ⁿ` for `‖w‖ < 1`. -/
private lemma norm_orbit_pt {w : K} (hw : ‖w‖ < 1) (n : ℤ) :
    ‖(t.q : K) ^ n * (1 + w)‖ = ‖(t.q : K)‖ ^ n := by
  rw [norm_mul, norm_zpow, norm_one_add hw, mul_one]

/-- For `n ≠ 0` and `‖w‖ < 1`, the orbit point `qⁿ(1+w)` has norm `≠ 1`. -/
private lemma norm_orbit_pt_ne_one {w : K} (hw : ‖w‖ < 1) {n : ℤ} (hn : n ≠ 0) :
    ‖(t.q : K) ^ n * (1 + w)‖ ≠ 1 := by
  rw [t.norm_orbit_pt hw n]
  rcases lt_or_gt_of_ne hn with h | h
  · exact ne_of_gt (t.one_lt_norm_q_zpow (by omega))
  · exact ne_of_lt (t.norm_q_zpow_lt_one (by omega))

/-- For `n ≠ 0` and `‖w‖ < 1`, the denominator `1 - qⁿ(1+w)` is nonzero. -/
private lemma one_sub_orbit_pt_ne_zero {w : K} (hw : ‖w‖ < 1) {n : ℤ} (hn : n ≠ 0) :
    (1 : K) - (t.q : K) ^ n * (1 + w) ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  exact t.norm_orbit_pt_ne_one hw hn (by rw [← h, norm_one])

/-- For `n ≠ 0` and `‖w‖ < 1`, `‖1 - qⁿ(1+w)‖ = max 1 ‖q‖ⁿ` (ultrametric isosceles law). -/
private lemma norm_one_sub_orbit_pt {w : K} (hw : ‖w‖ < 1) {n : ℤ} (hn : n ≠ 0) :
    ‖(1 : K) - (t.q : K) ^ n * (1 + w)‖ = max 1 (‖(t.q : K)‖ ^ n) := by
  rw [norm_one_sub_of_norm_ne_one (t.norm_orbit_pt_ne_one hw hn), t.norm_orbit_pt hw n]

/-- **Uniform geometric bound on the tail terms**: `‖tailTerm w n‖ ≤ ‖q‖` for `‖w‖ < 1`. -/
private lemma norm_tailTerm_le {w : K} (hw : ‖w‖ < 1) (n : ℤ) :
    ‖t.tailTerm w n‖ ≤ ‖(t.q : K)‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : t.tailTerm w 0 = 0 := by simp [tailTerm]
    rw [h0, norm_zero]
    exact t.norm_q_pos.le
  · rw [tailTerm, if_neg hn, norm_div, norm_pow, t.norm_one_sub_orbit_pt hw hn,
      t.norm_orbit_pt hw n]
    rcases lt_or_gt_of_ne hn with h | h
    · -- `n ≤ -1`: the term norm is `‖q‖ⁿ/(‖q‖ⁿ)² = ‖q‖⁻ⁿ ≤ ‖q‖`.
      have hR : 1 < ‖(t.q : K)‖ ^ n := t.one_lt_norm_q_zpow (by omega)
      have hR0 : (0 : ℝ) < ‖(t.q : K)‖ ^ n := lt_trans one_pos hR
      rw [max_eq_right hR.le]
      have hcalc : ‖(t.q : K)‖ ^ n / (‖(t.q : K)‖ ^ n) ^ 2 = ‖(t.q : K)‖ ^ (-n) := by
        rw [zpow_neg, sq, ← div_div, div_self hR0.ne', one_div]
      rw [hcalc]
      exact t.norm_q_zpow_le (by omega)
    · -- `1 ≤ n`: the term norm is `‖q‖ⁿ ≤ ‖q‖`.
      have hR : ‖(t.q : K)‖ ^ n < 1 := t.norm_q_zpow_lt_one (by omega)
      rw [max_eq_left hR.le, one_pow, div_one]
      exact t.norm_q_zpow_le (by omega)

/-- **Per-term Lipschitz estimate for the tail.** The difference of two tail terms
factors exactly as `qⁿ(w' - w)(1 - q²ⁿ(1+w)(1+w'))/((1 - qⁿ(1+w))²(1 - qⁿ(1+w'))²)`, and
each factor is controlled ultrametrically: `‖tailTerm w' n - tailTerm w n‖ ≤ ‖q‖·‖w'-w‖`. -/
private lemma norm_tailTerm_sub_le {w w' : K} (hw : ‖w‖ < 1) (hw' : ‖w'‖ < 1) (n : ℤ) :
    ‖t.tailTerm w' n - t.tailTerm w n‖ ≤ ‖(t.q : K)‖ * ‖w' - w‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : ∀ v : K, t.tailTerm v 0 = 0 := fun v => by simp [tailTerm]
    rw [h0, h0, sub_zero, norm_zero]
    positivity
  · have hd : (1 : K) - (t.q : K) ^ n * (1 + w) ≠ 0 := t.one_sub_orbit_pt_ne_zero hw hn
    have hd' : (1 : K) - (t.q : K) ^ n * (1 + w') ≠ 0 := t.one_sub_orbit_pt_ne_zero hw' hn
    have key : t.tailTerm w' n - t.tailTerm w n
        = (t.q : K) ^ n * (w' - w) * (1 - ((t.q : K) ^ n) ^ 2 * ((1 + w) * (1 + w')))
            / ((1 - (t.q : K) ^ n * (1 + w)) ^ 2 * (1 - (t.q : K) ^ n * (1 + w')) ^ 2) := by
      simp only [tailTerm, if_neg hn]
      field_simp
      ring
    have hC : ‖((t.q : K) ^ n) ^ 2 * ((1 + w) * (1 + w'))‖ = (‖(t.q : K)‖ ^ n) ^ 2 := by
      rw [norm_mul, norm_mul, norm_pow, norm_zpow, norm_one_add hw, norm_one_add hw',
        one_mul, mul_one]
    rw [key, norm_div, norm_mul, norm_mul, norm_zpow, norm_mul, norm_pow, norm_pow,
      t.norm_one_sub_orbit_pt hw hn, t.norm_one_sub_orbit_pt hw' hn]
    rcases lt_or_gt_of_ne hn with h | h
    · -- `n ≤ -1`: total factor `‖q‖³ⁿ/‖q‖⁴ⁿ = ‖q‖⁻ⁿ ≤ ‖q‖`.
      have hR : 1 < ‖(t.q : K)‖ ^ n := t.one_lt_norm_q_zpow (by omega)
      have hR0 : (0 : ℝ) < ‖(t.q : K)‖ ^ n := lt_trans one_pos hR
      have hR2 : 1 < (‖(t.q : K)‖ ^ n) ^ 2 := one_lt_pow₀ hR two_ne_zero
      have hCne : ‖((t.q : K) ^ n) ^ 2 * ((1 + w) * (1 + w'))‖ ≠ 1 := by
        rw [hC]; exact ne_of_gt hR2
      rw [norm_one_sub_of_norm_ne_one hCne, hC, max_eq_right hR2.le, max_eq_right hR.le]
      have hcalc : ‖(t.q : K)‖ ^ n * ‖w' - w‖ * (‖(t.q : K)‖ ^ n) ^ 2
            / ((‖(t.q : K)‖ ^ n) ^ 2 * (‖(t.q : K)‖ ^ n) ^ 2)
          = ‖(t.q : K)‖ ^ (-n) * ‖w' - w‖ := by
        rw [zpow_neg]
        field_simp
      rw [hcalc]
      exact mul_le_mul_of_nonneg_right (t.norm_q_zpow_le (by omega)) (norm_nonneg _)
    · -- `1 ≤ n`: total factor `‖q‖ⁿ ≤ ‖q‖`.
      have hR : ‖(t.q : K)‖ ^ n < 1 := t.norm_q_zpow_lt_one (by omega)
      have hR0 : (0 : ℝ) ≤ ‖(t.q : K)‖ ^ n := (zpow_pos t.norm_q_pos _).le
      have hR2 : (‖(t.q : K)‖ ^ n) ^ 2 < 1 := pow_lt_one₀ hR0 hR two_ne_zero
      have hCne : ‖((t.q : K) ^ n) ^ 2 * ((1 + w) * (1 + w'))‖ ≠ 1 := by
        rw [hC]; exact ne_of_lt hR2
      rw [norm_one_sub_of_norm_ne_one hCne, hC, max_eq_left hR2.le, max_eq_left hR.le,
        one_pow, mul_one, one_mul, div_one]
      exact mul_le_mul_of_nonneg_right (t.norm_q_zpow_le (by omega)) (norm_nonneg _)

/-- **Uniform bound on the tail sum**: `‖tailSum w‖ ≤ ‖q‖` for `‖w‖ < 1`. -/
private lemma norm_tailSum_le {w : K} (hw : ‖w‖ < 1) : ‖t.tailSum w‖ ≤ ‖(t.q : K)‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _)
    fun n => t.norm_tailTerm_le hw n

variable [CompleteSpace K]

/-! ### Summability, uniform bounds, and the Lipschitz estimate for the tail -/

/-- The tail family is summable for `‖w‖ < 1`: it is the update-at-`0` of the summable
`X`-coordinate family at the unit `1 + w`. -/
private lemma summable_tailTerm {w : K} (hw : ‖w‖ < 1) : Summable (t.tailTerm w) := by
  have h1w : (1 : K) + w ≠ 0 := by
    intro h
    have h1 : ‖(1 : K) + w‖ = 1 := norm_one_add hw
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  have hupd : t.tailTerm w = Function.update (t.Xterm (Units.mk0 (1 + w) h1w)) 0 0 := by
    funext n
    rw [Function.update_apply, tailTerm, Xterm_apply, Units.val_mk0]
  rw [hupd]
  exact (t.Xterm_summable _).update 0 0

/-- **Uniform bound on the small part**: `‖g(w)‖ ≤ ‖q‖ < 1` for `‖w‖ < 1`. -/
private lemma norm_gAux_le {w : K} (hw : ‖w‖ < 1) : ‖t.gAux w‖ ≤ ‖(t.q : K)‖ := by
  rw [gAux_apply, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖(2 : K)‖ * ‖t.eisenstein 1‖
        ≤ 1 * ‖(t.q : K)‖ := by
          gcongr
          · simpa using IsUltrametricDist.norm_natCast_le_one K 2
          · exact t.norm_eisenstein_le 1
      _ = ‖(t.q : K)‖ := one_mul _
  · rw [norm_neg]
    exact t.norm_tailSum_le hw

/-- **Lipschitz estimate for the small part**: `‖g(w') - g(w)‖ ≤ ‖q‖·‖w' - w‖` on the open
unit ball. -/
private lemma norm_gAux_sub_le {w w' : K} (hw : ‖w‖ < 1) (hw' : ‖w'‖ < 1) :
    ‖t.gAux w' - t.gAux w‖ ≤ ‖(t.q : K)‖ * ‖w' - w‖ := by
  have hdiff : t.gAux w' - t.gAux w = ∑' n : ℤ, (t.tailTerm w n - t.tailTerm w' n) := by
    rw [(t.summable_tailTerm hw).tsum_sub (t.summable_tailTerm hw'), gAux_apply, gAux_apply,
      tailSum_apply, tailSum_apply]
    ring
  rw [hdiff]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n => ?_
  rw [norm_sub_rev]
  exact t.norm_tailTerm_sub_le hw hw' n

/-- **Splitting off the `n = 0` term of the `X`-coordinate at `u = 1 + w`**:
`X(1 + w) = (1 + w)/w² - g(w)`. -/
private lemma X_mk0_eq {w : K} (h1w : (1 : K) + w ≠ 0) :
    t.X (Units.mk0 (1 + w) h1w) = (1 + w) / w ^ 2 - t.gAux w := by
  rw [X_apply, (t.Xterm_summable _).tsum_eq_add_tsum_ite 0]
  have h1 : t.Xterm (Units.mk0 (1 + w) h1w) 0 = (1 + w) / w ^ 2 := by
    rw [Xterm_apply, Units.val_mk0, zpow_zero, one_mul]
    congr 1
    rw [show (1 : K) - (1 + w) = -w by ring, neg_pow]
    ring
  have h2 : (∑' n : ℤ, if n = 0 then 0 else t.Xterm (Units.mk0 (1 + w) h1w) n)
      = t.tailSum w := by
    rw [tailSum_apply]
    exact tsum_congr fun n => by rw [tailTerm, Xterm_apply, Units.val_mk0]
  rw [h1, h2, gAux_apply]
  ring

/-! ### Step 1: norm bookkeeping on the curve -/

/-- **Large points sit on the branch `‖y‖² = ‖x‖³`.** For an affine point of the Tate curve
with `1 < ‖x‖`, the ultrametric dominant-term analysis of `y² + xy = x³ + a₄x + a₆`
(using the integrality `‖a₄‖, ‖a₆‖ < 1`) forces `‖y‖² = ‖x‖³`. -/
theorem norm_y_sq_eq_norm_x_cube (h12 : (12 : K) ≠ 0) {x y : K}
    (hxy : y ^ 2 + x * y = x ^ 3 + t.a₄ * x + t.a₆) (hx : 1 < ‖x‖) :
    ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  have hb0 : (0 : ℝ) < ‖x‖ := lt_trans one_pos hx
  have hb3 : (1 : ℝ) < ‖x‖ ^ 3 := one_lt_pow₀ hx three_ne_zero
  -- the right-hand side has norm exactly `‖x‖³`
  have hsmall : ‖t.a₄ * x + t.a₆‖ < ‖x‖ ^ 3 := by
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      calc ‖t.a₄‖ * ‖x‖ < 1 * ‖x‖ := by gcongr; exact t.norm_a₄_lt_one
        _ = ‖x‖ := one_mul _
        _ < ‖x‖ ^ 3 := by nlinarith [mul_pos (mul_pos hb0 hb0) (sub_pos.mpr hx)]
    · exact lt_trans (t.norm_a₆_lt_one h12) hb3
  have hRHS : ‖x ^ 3 + t.a₄ * x + t.a₆‖ = ‖x‖ ^ 3 := by
    rw [show x ^ 3 + t.a₄ * x + t.a₆ = x ^ 3 + (t.a₄ * x + t.a₆) by ring]
    have hne : ‖x ^ 3‖ ≠ ‖t.a₄ * x + t.a₆‖ := by
      rw [norm_pow]; exact ne_of_gt hsmall
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_pow,
      max_eq_left hsmall.le]
  have hL : ‖y ^ 2 + x * y‖ = ‖x‖ ^ 3 := by rw [hxy]; exact hRHS
  -- `y ≠ 0`
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hL
    simp only [zero_pow two_ne_zero, mul_zero, add_zero, norm_zero] at hL
    nlinarith
  have ha0 : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy0
  -- `‖y‖ ≠ ‖x‖`, else the left side would be too small
  have hab : ‖y‖ ≠ ‖x‖ := by
    intro h
    have hle : ‖y ^ 2 + x * y‖ ≤ ‖x‖ ^ 2 := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_pow, h]
      · rw [norm_mul, h, sq]
    nlinarith [mul_pos (mul_pos hb0 hb0) (sub_pos.mpr hx)]
  -- the isosceles law identifies the maximum
  have hne : ‖y ^ 2‖ ≠ ‖x * y‖ := by
    rw [norm_pow, norm_mul]
    intro h
    rw [sq] at h
    exact hab (mul_right_cancel₀ ha0.ne' h)
  have hmax : max (‖y‖ ^ 2) (‖x‖ * ‖y‖) = ‖x‖ ^ 3 := by
    rw [← norm_pow, ← norm_mul, ← IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne]
    exact hL
  rcases max_cases (‖y‖ ^ 2) (‖x‖ * ‖y‖) with ⟨heq, _⟩ | ⟨heq, hlt⟩
  · rw [heq] at hmax; exact hmax
  · -- the case `max = ‖x‖·‖y‖` forces `‖y‖ = ‖x‖²`, contradicting `‖y‖² < ‖x‖·‖y‖`
    exfalso
    rw [heq] at hmax
    have hy_eq : ‖y‖ = ‖x‖ ^ 2 := by
      have h3 : ‖x‖ * ‖y‖ = ‖x‖ * ‖x‖ ^ 2 := by rw [hmax]; ring
      exact mul_left_cancel₀ hb0.ne' h3
    nlinarith [mul_pos (mul_pos (mul_pos hb0 hb0) hb0) (sub_pos.mpr hx)]

/-! ### The ultrametric Newton iteration -/

/-- **Existence of a root of the Newton objective.** Given `1 < ‖x‖`, a seed `z` on the
critical sphere `‖z‖²·‖x‖ = 1` with the initial smallness `‖h(z)‖ ≤ ‖z‖²·max(‖q‖, ‖z‖²)`,
and `‖2‖ = 1`, the Newton iteration `w ← w - h(w)/D(w)` stays on the sphere `‖w‖ = ‖z‖`,
its objective decays geometrically with ratio `κ = ‖z‖²·max(‖q‖, ‖z‖²) < 1`, and its limit
`w` satisfies `h(w) = 0`. -/
private lemma exists_root_hAux (h2 : ‖(2 : K)‖ = 1) {x z : K} (hx : 1 < ‖x‖)
    (hzx : ‖z‖ ^ 2 * ‖x‖ = 1)
    (hz0 : ‖t.hAux x z‖ ≤ ‖z‖ ^ 2 * max ‖(t.q : K)‖ (‖z‖ ^ 2)) :
    ∃ w : K, ‖w‖ = ‖z‖ ∧ t.hAux x w = 0 := by
  have hx0 : (0 : ℝ) < ‖x‖ := lt_trans one_pos hx
  have hρ0' : (0 : ℝ) < ‖z‖ := by
    rcases eq_or_lt_of_le (norm_nonneg z) with h | h
    · exfalso; rw [← h] at hzx; norm_num at hzx
    · exact h
  set ρ := ‖z‖ with hρ_def
  have hρ0 : 0 < ρ := hρ0'
  have hρ1 : ρ < 1 := by
    rcases lt_or_ge ρ 1 with h | h
    · exact h
    · exfalso
      have h1 : (1 : ℝ) ≤ ρ ^ 2 := one_le_pow₀ h
      nlinarith
  set C₀ := max ‖(t.q : K)‖ (ρ ^ 2) with hC₀_def
  have hC₀0 : 0 < C₀ := lt_max_of_lt_left t.norm_q_pos
  have hC₀1 : C₀ < 1 := max_lt t.norm_lt_one (pow_lt_one₀ hρ0.le hρ1 two_ne_zero)
  set κ := ρ ^ 2 * C₀ with hκ_def
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ < 1 := by
    have h1 : ρ ^ 2 < 1 := pow_lt_one₀ hρ0.le hρ1 two_ne_zero
    have h2 : ρ ^ 2 * C₀ < ρ ^ 2 * 1 := mul_lt_mul_of_pos_left hC₀1 (by positivity)
    rw [hκ_def]
    nlinarith
  have hρx : ρ * ‖x‖ = ρ⁻¹ := by
    rw [inv_eq_one_div, eq_div_iff hρ0.ne']
    nlinarith
  have hρinv1 : (1 : ℝ) < ρ⁻¹ := (one_lt_inv₀ hρ0).mpr hρ1
  -- the small part does not move the norm of `x`
  have hxg : ∀ w : K, ‖w‖ < 1 → ‖x + t.gAux w‖ = ‖x‖ := by
    intro w hw
    have hlt : ‖t.gAux w‖ < ‖x‖ :=
      lt_of_le_of_lt (t.norm_gAux_le hw) (lt_trans t.norm_lt_one hx)
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hlt),
      max_eq_left hlt.le]
  -- the chord slope has norm exactly `ρ⁻¹` on the sphere
  have hD : ∀ w : K, ‖w‖ = ρ → ‖t.dAux x w‖ = ρ⁻¹ := by
    intro w hwρ
    have hw1 : ‖w‖ < 1 := by rw [hwρ]; exact hρ1
    have hnorm2 : ‖2 * w * (x + t.gAux w)‖ = ρ⁻¹ := by
      rw [norm_mul, norm_mul, h2, one_mul, hwρ, hxg w hw1, hρx]
    have hne : ‖2 * w * (x + t.gAux w)‖ ≠ ‖-(1 : K)‖ := by
      rw [hnorm2, norm_neg, norm_one]
      exact ne_of_gt hρinv1
    rw [dAux_apply, sub_eq_add_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_one, hnorm2,
      max_eq_left hρinv1.le]
  set W := t.newtonSeq x z with hW_def
  -- the sphere-and-decay invariant of the Newton iteration
  have inv : ∀ k, ‖W k‖ = ρ ∧ ‖t.hAux x (W k)‖ ≤ κ ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨rfl, ?_⟩
      rw [pow_one, hκ_def]
      exact hz0
    | succ k ih =>
      obtain ⟨hWk, hhk⟩ := ih
      have hw1 : ‖W k‖ < 1 := by rw [hWk]; exact hρ1
      have hDk : ‖t.dAux x (W k)‖ = ρ⁻¹ := hD (W k) hWk
      have hDne : t.dAux x (W k) ≠ 0 := by
        intro h
        rw [h, norm_zero] at hDk
        exact (inv_pos.mpr hρ0).ne' hDk.symm
      have hκk1 : κ ^ (k + 1) < 1 := pow_lt_one₀ hκ0.le hκ1 (Nat.succ_ne_zero k)
      have hstep : W (k + 1) - W k = -(t.hAux x (W k) / t.dAux x (W k)) := by
        rw [hW_def, t.newtonSeq_succ x z k]
        ring
      have hΔ : ‖W (k + 1) - W k‖ = ρ * ‖t.hAux x (W k)‖ := by
        rw [hstep, norm_neg, norm_div, hDk, div_inv_eq_mul, mul_comm]
      have hΔlt : ‖W (k + 1) - W k‖ < ρ := by
        rw [hΔ]
        calc ρ * ‖t.hAux x (W k)‖ ≤ ρ * κ ^ (k + 1) :=
              mul_le_mul_of_nonneg_left hhk hρ0.le
          _ < ρ * 1 := mul_lt_mul_of_pos_left hκk1 hρ0
          _ = ρ := mul_one ρ
      have hWk1 : ‖W (k + 1)‖ = ρ := by
        have hsplit : W (k + 1) = W k + (W (k + 1) - W k) := by ring
        have hne : ‖W k‖ ≠ ‖W (k + 1) - W k‖ := by
          rw [hWk]; exact (ne_of_lt hΔlt).symm
        rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hWk,
          max_eq_left hΔlt.le]
      have hw1' : ‖W (k + 1)‖ < 1 := by rw [hWk1]; exact hρ1
      -- the Newton expansion: the linear terms cancel exactly
      have hcancel : t.hAux x (W k) + (W (k + 1) - W k) * t.dAux x (W k) = 0 := by
        rw [hstep, neg_mul, div_mul_cancel₀ _ hDne, add_neg_cancel]
      have hexp : t.hAux x (W (k + 1))
          = (W (k + 1) - W k) ^ 2 * (x + t.gAux (W k))
            + (W (k + 1)) ^ 2 * (t.gAux (W (k + 1)) - t.gAux (W k)) := by
        linear_combination t.hAux_sub_sub x (W k) (W (k + 1)) + hcancel
      refine ⟨hWk1, ?_⟩
      rw [hexp]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · -- quadratic term: `‖Δ‖²‖x‖ = ‖h(w_k)‖² ≤ κ^{k+2}`
        rw [norm_mul, norm_pow, hΔ, hxg (W k) hw1]
        calc (ρ * ‖t.hAux x (W k)‖) ^ 2 * ‖x‖
            = ρ ^ 2 * ‖x‖ * ‖t.hAux x (W k)‖ ^ 2 := by ring
          _ = ‖t.hAux x (W k)‖ ^ 2 := by rw [hzx, one_mul]
          _ ≤ (κ ^ (k + 1)) ^ 2 := by gcongr
          _ ≤ κ ^ (k + 1 + 1) := by
              rw [← pow_mul]
              exact pow_le_pow_of_le_one hκ0.le hκ1.le (by omega)
      · -- Lipschitz term: `ρ²·‖q‖·ρ·‖h(w_k)‖ ≤ κ·κ^{k+1}`
        rw [norm_mul, norm_pow, hWk1]
        calc ρ ^ 2 * ‖t.gAux (W (k + 1)) - t.gAux (W k)‖
            ≤ ρ ^ 2 * (‖(t.q : K)‖ * ‖W (k + 1) - W k‖) := by
              gcongr
              exact t.norm_gAux_sub_le hw1 hw1'
          _ = ρ ^ 2 * ‖(t.q : K)‖ * ρ * ‖t.hAux x (W k)‖ := by rw [hΔ]; ring
          _ ≤ κ * κ ^ (k + 1) := by
              refine mul_le_mul ?_ hhk (norm_nonneg _) hκ0.le
              have hqC : ‖(t.q : K)‖ ≤ C₀ := le_max_left _ _
              have hqρ : ‖(t.q : K)‖ * ρ ≤ C₀ := by
                have h1 := mul_le_mul hqC hρ1.le hρ0.le hC₀0.le
                rwa [mul_one] at h1
              calc ρ ^ 2 * ‖(t.q : K)‖ * ρ = ρ ^ 2 * (‖(t.q : K)‖ * ρ) := by ring
                _ ≤ ρ ^ 2 * C₀ := mul_le_mul_of_nonneg_left hqρ (sq_nonneg ρ)
                _ = κ := by rw [hκ_def]
          _ = κ ^ (k + 1 + 1) := by ring
  -- the iterates form a geometric Cauchy sequence
  have hΔall : ∀ k, ‖W (k + 1) - W k‖ = ρ * ‖t.hAux x (W k)‖ := by
    intro k
    have hDk : ‖t.dAux x (W k)‖ = ρ⁻¹ := hD (W k) (inv k).1
    have hstep : W (k + 1) - W k = -(t.hAux x (W k) / t.dAux x (W k)) := by
      rw [hW_def, t.newtonSeq_succ x z k]
      ring
    rw [hstep, norm_neg, norm_div, hDk, div_inv_eq_mul, mul_comm]
  have hdist : ∀ k, dist (W k) (W (k + 1)) ≤ ρ * κ * κ ^ k := by
    intro k
    rw [dist_eq_norm, norm_sub_rev, hΔall k]
    calc ρ * ‖t.hAux x (W k)‖ ≤ ρ * κ ^ (k + 1) :=
          mul_le_mul_of_nonneg_left (inv k).2 hρ0.le
      _ = ρ * κ * κ ^ k := by ring
  obtain ⟨w, hlim⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric κ (ρ * κ) hκ1 hdist)
  -- the limit stays on the sphere
  have hwρ : ‖w‖ = ρ := by
    refine tendsto_nhds_unique (hlim.norm) ?_
    have hconst : (fun k => ‖W k‖) = fun _ => ρ := funext fun k => (inv k).1
    rw [hconst]
    exact tendsto_const_nhds
  have hw1 : ‖w‖ < 1 := by rw [hwρ]; exact hρ1
  -- the objective tends to `0` along the iterates ...
  have hh0 : Tendsto (fun k => t.hAux x (W k)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun k => (inv k).2) ?_
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0.le hκ1).mul_const κ
    rw [zero_mul] at h
    exact h.congr fun k => by rw [pow_succ]
  -- ... and to `h(w)` by the Lipschitz continuity of `hAux` on the sphere
  have hhw : Tendsto (fun k => t.hAux x (W k)) atTop (𝓝 (t.hAux x w)) := by
    have key : ∀ k, ‖t.hAux x (W k) - t.hAux x w‖ ≤ ρ⁻¹ * ‖W k - w‖ := by
      intro k
      have hWk : ‖W k‖ = ρ := (inv k).1
      have hwk1 : ‖W k‖ < 1 := by rw [hWk]; exact hρ1
      have hΔle : ‖W k - w‖ ≤ ρ := by
        refine le_trans ?_ (max_le_iff.mpr ⟨le_of_eq hWk, le_of_eq hwρ⟩ : max ‖W k‖ ‖w‖ ≤ ρ)
        rw [sub_eq_add_neg]
        exact le_trans (IsUltrametricDist.norm_add_le_max _ _)
          (max_le_max le_rfl (le_of_eq (norm_neg w)))
      have hexp : t.hAux x (W k) - t.hAux x w
          = (W k - w) * t.dAux x w + (W k - w) ^ 2 * (x + t.gAux w)
            + (W k) ^ 2 * (t.gAux (W k) - t.gAux w) := by
        linear_combination t.hAux_sub_sub x w (W k)
      rw [hexp]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)) ?_)
      · rw [norm_mul, hD w hwρ, mul_comm]
      · rw [norm_mul, norm_pow, hxg w hw1, sq]
        calc ‖W k - w‖ * ‖W k - w‖ * ‖x‖
            ≤ ρ * ‖W k - w‖ * ‖x‖ := by gcongr
          _ = ρ * ‖x‖ * ‖W k - w‖ := by ring
          _ = ρ⁻¹ * ‖W k - w‖ := by rw [hρx]
      · rw [norm_mul, norm_pow, hWk]
        calc ρ ^ 2 * ‖t.gAux (W k) - t.gAux w‖
            ≤ ρ ^ 2 * (‖(t.q : K)‖ * ‖W k - w‖) := by
              gcongr
              exact t.norm_gAux_sub_le hw1 hwk1
          _ ≤ 1 * (1 * ‖W k - w‖) := by
              gcongr
              · exact pow_le_one₀ hρ0.le hρ1.le
              · exact t.norm_lt_one.le
          _ = ‖W k - w‖ := by ring
          _ ≤ ρ⁻¹ * ‖W k - w‖ := by
              refine le_mul_of_one_le_left (norm_nonneg _) hρinv1.le
    have hlim0 : Tendsto (fun k => ρ⁻¹ * ‖W k - w‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => W k - w) atTop (𝓝 0) := by
        simpa using hlim.sub_const w
      have h2 := h1.norm
      rw [norm_zero] at h2
      simpa using h2.const_mul ρ⁻¹
    have h4 : Tendsto (fun k => t.hAux x (W k) - t.hAux x w) atTop (𝓝 0) :=
      squeeze_zero_norm key hlim0
    have h5 := h4.add_const (t.hAux x w)
    rw [zero_add] at h5
    exact h5.congr fun k => by ring
  exact ⟨w, hwρ, tendsto_nhds_unique hhw hh0⟩

/-! ### The surjectivity theorem for large points -/

/-- **Surjectivity of the Tate parametrization onto large points.** Every affine point
`(x, y)` of the Tate curve `y² + xy = x³ + a₄x + a₆` with `1 < ‖x‖` is the image
`(X(u), Y(u))` of an off-orbit unit `u : Kˣ` — produced by the ultrametric Newton
iteration for `X(1 + w) = x` started at `w₀ = x/y`, with the sign of `y` corrected by the
coordinate inversion `u ↦ u⁻¹` if needed. The hypothesis `‖(2 : K)‖ = 1` (residue
characteristic `≠ 2`) keeps the Newton slope invertible; `(12 : K) ≠ 0` is the standing
characteristic assumption of the Weierstrass identity for `(X(u), Y(u))`. -/
theorem exists_tate_coord_of_one_lt_norm (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0)
    {x y : K} (hxy : y ^ 2 + x * y = x ^ 3 + t.a₄ * x + t.a₆) (hx : 1 < ‖x‖) :
    ∃ u : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) ∧ t.X u = x ∧ t.Y u = y := by
  have hb0 : (0 : ℝ) < ‖x‖ := lt_trans one_pos hx
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    linarith
  -- Step 1: norm bookkeeping
  have hy2 : ‖y‖ ^ 2 = ‖x‖ ^ 3 := t.norm_y_sq_eq_norm_x_cube h12 hxy hx
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, norm_zero] at hy2
    have h3 : (1 : ℝ) < ‖x‖ ^ 3 := one_lt_pow₀ hx three_ne_zero
    nlinarith
  have hyn0 : (0 : ℝ) < ‖y‖ := norm_pos_iff.mpr hy0
  set z₀ := x / y with hz₀_def
  have hzx : ‖z₀‖ ^ 2 * ‖x‖ = 1 := by
    rw [hz₀_def, norm_div, div_pow, hy2]
    field_simp
  have hρ0 : (0 : ℝ) < ‖z₀‖ := by
    rcases eq_or_lt_of_le (norm_nonneg z₀) with h | h
    · exfalso; rw [← h] at hzx; norm_num at hzx
    · exact h
  have hρ1 : ‖z₀‖ < 1 := by
    rcases lt_or_ge ‖z₀‖ 1 with h | h
    · exact h
    · exfalso
      have h1 : (1 : ℝ) ≤ ‖z₀‖ ^ 2 := one_le_pow₀ h
      nlinarith
  -- Step 2: the exact quadratic satisfied by `z₀ = x/y`
  have hc : (1 : K) + z₀ = z₀ ^ 2 * (x + (t.a₄ / x + t.a₆ / x ^ 2)) := by
    rw [hz₀_def]
    field_simp
    linear_combination hxy
  have hcnorm : ‖t.a₄ / x + t.a₆ / x ^ 2‖ ≤ ‖z₀‖ ^ 2 := by
    have hxinv : ‖x‖⁻¹ = ‖z₀‖ ^ 2 := by
      rw [inv_eq_one_div, eq_comm, eq_div_iff hb0.ne']
      exact hzx
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_div, ← hxinv, div_eq_mul_inv]
      calc ‖t.a₄‖ * ‖x‖⁻¹ ≤ 1 * ‖x‖⁻¹ := by
            gcongr
            exact t.norm_a₄_lt_one.le
        _ = ‖x‖⁻¹ := one_mul _
    · rw [norm_div, norm_pow, ← hxinv, div_eq_mul_inv]
      calc ‖t.a₆‖ * (‖x‖ ^ 2)⁻¹ ≤ 1 * (‖x‖ ^ 2)⁻¹ := by
            gcongr
            exact (t.norm_a₆_lt_one h12).le
        _ = (‖x‖ ^ 2)⁻¹ := one_mul _
        _ ≤ ‖x‖⁻¹ := by
            rw [sq]
            rw [mul_inv]
            calc ‖x‖⁻¹ * ‖x‖⁻¹ ≤ 1 * ‖x‖⁻¹ := by
                  gcongr
                  exact inv_le_one_of_one_le₀ hx.le
              _ = ‖x‖⁻¹ := one_mul _
  -- Step 3: initial smallness of the Newton objective at `z₀`
  have hz0 : ‖t.hAux x z₀‖ ≤ ‖z₀‖ ^ 2 * max ‖(t.q : K)‖ (‖z₀‖ ^ 2) := by
    have hkey : t.hAux x z₀ = z₀ ^ 2 * (t.gAux z₀ - (t.a₄ / x + t.a₆ / x ^ 2)) := by
      rw [hAux_apply]
      linear_combination -hc
    rw [hkey, norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact le_max_of_le_left (t.norm_gAux_le hρ1)
    · rw [norm_neg]
      exact le_max_of_le_right hcnorm
  -- Step 4: run the Newton iteration
  obtain ⟨w, hwρ, hwroot⟩ := t.exists_root_hAux h2 hx hzx hz0
  have hw1 : ‖w‖ < 1 := by rw [hwρ]; exact hρ1
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hwρ
    exact hρ0.ne hwρ
  have h1w : (1 : K) + w ≠ 0 := by
    intro h
    have h1 : ‖(1 : K) + w‖ = 1 := norm_one_add hw1
    rw [h, norm_zero] at h1
    exact one_ne_zero h1.symm
  set u : Kˣ := Units.mk0 (1 + w) h1w with hu_def
  -- `u` is off the orbit
  have hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1 := by
    intro n hcontra
    rw [hu_def, Units.val_mk0] at hcontra
    rcases eq_or_ne n 0 with rfl | hn
    · rw [zpow_zero, one_mul] at hcontra
      exact hw0 (by linear_combination hcontra)
    · exact t.norm_orbit_pt_ne_one hw1 hn (by rw [hcontra, norm_one])
  -- `X u = x`
  have hXu : t.X u = x := by
    have hg1 : (1 + w) / w ^ 2 = x + t.gAux w := by
      have hroot' := hwroot
      rw [hAux_apply] at hroot'
      rw [div_eq_iff (pow_ne_zero 2 hw0)]
      linear_combination -hroot'
    rw [hu_def, t.X_mk0_eq h1w, hg1]
    ring
  -- Step 5: recover `y` via the quadratic in the second coordinate
  have hYu : (t.Y u) ^ 2 + x * t.Y u = x ^ 3 + t.a₄ * x + t.a₆ := by
    have hmem := t.tatePoint_mem' h12 hu
    rw [t.tateCurve_equation_iff, hXu] at hmem
    exact hmem
  have hfactor : (y - t.Y u) * (y + t.Y u + x) = 0 := by
    linear_combination hxy - hYu
  rcases mul_eq_zero.mp hfactor with h | h
  · exact ⟨u, hu, hXu, (sub_eq_zero.mp h).symm⟩
  · refine ⟨u⁻¹, t.inv_off_orbit hu, ?_, ?_⟩
    · rw [t.X_inv hu, hXu]
    · rw [t.Y_inv hu, hXu]
      linear_combination -h

end Nonarchimedean

end TateParameter

end TateCurvesTheta
