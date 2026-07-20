/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.Filter.AtTopBot.Ring
import TateCurvesTheta.TateCurve.Weierstrass

/-!
# The Tate parametrization: coordinate series `X(u)`, `Y(u)` and their convergence

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), Tate's
analytic parametrization of the curve `E_q` sends a point `u : Kˣ` to the affine point
`(X(u), Y(u))`, where (Silverman, *Advanced Topics*, Ch. V, Thm 3.1)
```
X q u = ∑' n : ℤ, qⁿ u / (1 - qⁿ u)²  - 2 s₁(q),
Y q u = ∑' n : ℤ, (qⁿ u)² / (1 - qⁿ u)³ + s₁(q),
```
with `sₖ(q)` the Eisenstein-type series of `TateCurvesTheta/TateCurve/Weierstrass.lean`.

This file fixes that normalization, defines the general terms `Xterm`, `Yterm` and the
coordinate functions `X`, `Y`, and proves the two defining series are unconditionally
`Summable` over a complete nonarchimedean field. This is the analytic-convergence foundation
for the full parametrization isomorphism `Kˣ/qᶻ ≅ E_q(K)`, whose hard core (the Weierstrass
equation for `(X(u), Y(u))` and the group isomorphism) is developed in a sibling file.

## Convergence

As in the theta-series issue, convergence needs completeness (`[CompleteSpace K]`) and the
ultrametric triangle inequality (`[IsUltrametricDist K]`) on top of the metric datum of a
`TateParameter`; these are added locally with a seam comment. In a complete nonarchimedean
group a family is summable as soon as its terms tend to zero along `cofinite`
(`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`), and here the term norm decays on
both ends of `ℤ`: writing `x = qⁿ u` with `‖x‖ = ‖q‖ⁿ ‖u‖`, the ultrametric isosceles law gives
`‖1 - x‖ = max 1 ‖x‖`, so
```
‖Xterm n‖ = ‖x‖ / (max 1 ‖x‖)²  =  ‖x‖       (‖x‖ < 1),   ‖x‖⁻¹  (‖x‖ > 1),
‖Yterm n‖ = ‖x‖² / (max 1 ‖x‖)³ =  ‖x‖²      (‖x‖ < 1),   ‖x‖⁻¹  (‖x‖ > 1).
```
Since `‖x‖ = ‖q‖ⁿ ‖u‖ → 0` as `n → +∞` and `→ +∞` as `n → -∞` (`0 < ‖q‖ < 1`), both term
norms tend to `0` on `atTop` and on `atBot`, i.e. on all of `cofinite = atBot ⊔ atTop`. (The
single index — if any — with `‖x‖ = 1` is irrelevant to a cofinite limit.)

## Main definitions

* `TateCurvesTheta.TateParameter.Xterm`, `TateParameter.Yterm`: the general terms of the
  coordinate series.
* `TateCurvesTheta.TateParameter.X`, `TateParameter.Y`: the Tate coordinate functions.

## Main results

* `TateParameter.norm_one_sub_of_norm_ne_one`: `‖1 - x‖ = max 1 ‖x‖` when `‖x‖ ≠ 1`.
* `TateParameter.one_sub_qzpow_mul_ne_zero`: `1 - qⁿ u ≠ 0` for `u ∉ qᶻ`.
* `TateParameter.Xterm_summable`, `TateParameter.Yterm_summable`: the coordinate series
  converge over a complete nonarchimedean field.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

open Filter Topology

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- The general term `qⁿ u / (1 - qⁿ u)²` of the `X`-coordinate series, indexed by `n : ℤ`. -/
def Xterm (u : Kˣ) (n : ℤ) : K :=
  (t.q : K) ^ n * (u : K) / (1 - (t.q : K) ^ n * (u : K)) ^ 2

/-- The general term `(qⁿ u)² / (1 - qⁿ u)³` of the `Y`-coordinate series, indexed by `n : ℤ`. -/
def Yterm (u : Kˣ) (n : ℤ) : K :=
  ((t.q : K) ^ n * (u : K)) ^ 2 / (1 - (t.q : K) ^ n * (u : K)) ^ 3

@[simp] lemma Xterm_apply (u : Kˣ) (n : ℤ) :
    t.Xterm u n = (t.q : K) ^ n * (u : K) / (1 - (t.q : K) ^ n * (u : K)) ^ 2 := rfl

@[simp] lemma Yterm_apply (u : Kˣ) (n : ℤ) :
    t.Yterm u n = ((t.q : K) ^ n * (u : K)) ^ 2 / (1 - (t.q : K) ^ n * (u : K)) ^ 3 := rfl

/-- The **Tate `X`-coordinate** `X q u = ∑' n, qⁿ u / (1 - qⁿ u)² - 2 s₁(q)`. -/
def X (u : Kˣ) : K := (∑' n : ℤ, t.Xterm u n) - 2 * t.eisenstein 1

/-- The **Tate `Y`-coordinate** `Y q u = ∑' n, (qⁿ u)² / (1 - qⁿ u)³ + s₁(q)`. -/
def Y (u : Kˣ) : K := (∑' n : ℤ, t.Yterm u n) + t.eisenstein 1

lemma X_apply (u : Kˣ) : t.X u = (∑' n : ℤ, t.Xterm u n) - 2 * t.eisenstein 1 := rfl

lemma Y_apply (u : Kˣ) : t.Y u = (∑' n : ℤ, t.Yterm u n) + t.eisenstein 1 := rfl

/-- For `u ∉ qᶻ` — equivalently `qⁿ u ≠ 1` for all `n : ℤ` — the factor `1 - qⁿ u` occurring in
the denominators of the Tate coordinate series is nonzero. -/
lemma one_sub_qzpow_mul_ne_zero {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) (n : ℤ) :
    (1 : K) - (t.q : K) ^ n * (u : K) ≠ 0 :=
  sub_ne_zero.mpr (hu n).symm

/-- The real-analytic size `‖qⁿ u‖ = ‖q‖ⁿ ‖u‖` of the base point of the `n`-th term, packaged as
a sequence in `n : ℤ`. It tends to `0` on `atTop` and to `+∞` on `atBot`. -/
private def sizeSeq (u : Kˣ) (n : ℤ) : ℝ := ‖(t.q : K)‖ ^ n * ‖(u : K)‖

private lemma norm_qzpow_mul (u : Kˣ) (n : ℤ) :
    ‖(t.q : K) ^ n * (u : K)‖ = t.sizeSeq u n := by
  simp only [sizeSeq, norm_mul, norm_zpow]

private lemma sizeSeq_eq_exp (u : Kˣ) (n : ℤ) :
    t.sizeSeq u n = Real.exp (Real.log ‖(t.q : K)‖ * (n : ℝ) + Real.log ‖(u : K)‖) := by
  have ha : 0 < ‖(t.q : K)‖ := t.norm_q_pos
  have hb : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  simp only [sizeSeq]
  rw [← Real.rpow_intCast ‖(t.q : K)‖ n, Real.rpow_def_of_pos ha, Real.exp_add, Real.exp_log hb]

private lemma tendsto_sizeSeq_atTop (u : Kˣ) : Tendsto (t.sizeSeq u) atTop (𝓝 0) := by
  have ha : 0 < ‖(t.q : K)‖ := t.norm_q_pos
  have hlq : Real.log ‖(t.q : K)‖ < 0 := Real.log_neg ha t.norm_lt_one
  have hf : Tendsto
      (fun n : ℤ => Real.log ‖(t.q : K)‖ * (n : ℝ) + Real.log ‖(u : K)‖) atTop atBot :=
    tendsto_atBot_add_const_right atTop (Real.log ‖(u : K)‖)
      (Tendsto.const_mul_atTop_of_neg hlq tendsto_intCast_atTop_atTop)
  have he : Tendsto
      (fun n : ℤ => Real.exp (Real.log ‖(t.q : K)‖ * (n : ℝ) + Real.log ‖(u : K)‖))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hf
  exact he.congr fun n => (t.sizeSeq_eq_exp u n).symm

private lemma tendsto_sizeSeq_atBot (u : Kˣ) : Tendsto (t.sizeSeq u) atBot atTop := by
  have ha : 0 < ‖(t.q : K)‖ := t.norm_q_pos
  have hlq : Real.log ‖(t.q : K)‖ < 0 := Real.log_neg ha t.norm_lt_one
  have hf : Tendsto
      (fun n : ℤ => Real.log ‖(t.q : K)‖ * (n : ℝ) + Real.log ‖(u : K)‖) atBot atTop :=
    tendsto_atTop_add_const_right atBot (Real.log ‖(u : K)‖)
      (Tendsto.const_mul_atBot_of_neg hlq (tendsto_intCast_atBot_iff.2 tendsto_id))
  have he : Tendsto
      (fun n : ℤ => Real.exp (Real.log ‖(t.q : K)‖ * (n : ℝ) + Real.log ‖(u : K)‖))
      atBot atTop := Real.tendsto_exp_atTop.comp hf
  exact he.congr fun n => (t.sizeSeq_eq_exp u n).symm

section Nonarchimedean

variable [IsUltrametricDist K]

/-- In a nonarchimedean field, `‖1 - x‖ = max 1 ‖x‖` whenever `‖x‖ ≠ 1`: the ultrametric
"isosceles" law makes the norm of the difference the larger of the two norms. -/
lemma norm_one_sub_of_norm_ne_one {x : K} (h : ‖x‖ ≠ 1) : ‖(1 : K) - x‖ = max 1 ‖x‖ := by
  have hne : ‖(1 : K)‖ ≠ ‖-x‖ := by rw [norm_one, norm_neg]; exact h.symm
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, norm_neg]

variable [CompleteSpace K]

/-- **Convergence of the Tate `X`-coordinate series.** Over a complete nonarchimedean field the
family `n ↦ qⁿ u / (1 - qⁿ u)²` is unconditionally summable: its term norm equals `‖q‖ⁿ‖u‖` for
`n → +∞` and `(‖q‖ⁿ‖u‖)⁻¹` for `n → -∞`, both of which tend to `0`. -/
theorem Xterm_summable (u : Kˣ) : Summable (t.Xterm u) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Int.cofinite_eq, tendsto_sup]
  constructor
  · -- `atBot`: eventually `‖qⁿ u‖ > 1`, so `‖Xterm n‖ = (‖q‖ⁿ‖u‖)⁻¹ → 0`.
    have hlim : Tendsto (fun n : ℤ => (t.sizeSeq u n)⁻¹) atBot (𝓝 0) :=
      (t.tendsto_sizeSeq_atBot u).inv_tendsto_atTop
    refine hlim.congr' ?_
    filter_upwards [(t.tendsto_sizeSeq_atBot u).eventually_gt_atTop 1] with n hn
    have hne0 : t.sizeSeq u n ≠ 0 := (lt_trans one_pos hn).ne'
    have hx : ‖(t.q : K) ^ n * (u : K)‖ = t.sizeSeq u n := t.norm_qzpow_mul u n
    have hxne : ‖(t.q : K) ^ n * (u : K)‖ ≠ 1 := by rw [hx]; exact ne_of_gt hn
    rw [Xterm_apply, norm_div, norm_pow, norm_one_sub_of_norm_ne_one hxne, hx, max_eq_right hn.le]
    field_simp
  · -- `atTop`: eventually `‖qⁿ u‖ < 1`, so `‖Xterm n‖ = ‖q‖ⁿ‖u‖ → 0`.
    refine (t.tendsto_sizeSeq_atTop u).congr' ?_
    filter_upwards [(t.tendsto_sizeSeq_atTop u).eventually (eventually_lt_nhds one_pos)] with n hn
    have hx : ‖(t.q : K) ^ n * (u : K)‖ = t.sizeSeq u n := t.norm_qzpow_mul u n
    have hxne : ‖(t.q : K) ^ n * (u : K)‖ ≠ 1 := by rw [hx]; exact ne_of_lt hn
    rw [Xterm_apply, norm_div, norm_pow, norm_one_sub_of_norm_ne_one hxne, hx,
      max_eq_left hn.le, one_pow, div_one]

/-- **Convergence of the Tate `Y`-coordinate series.** Over a complete nonarchimedean field the
family `n ↦ (qⁿ u)² / (1 - qⁿ u)³` is unconditionally summable: its term norm equals `(‖q‖ⁿ‖u‖)²`
for `n → +∞` and `(‖q‖ⁿ‖u‖)⁻¹` for `n → -∞`, both of which tend to `0`. -/
theorem Yterm_summable (u : Kˣ) : Summable (t.Yterm u) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Int.cofinite_eq, tendsto_sup]
  constructor
  · -- `atBot`: `‖Yterm n‖ = ‖x‖²/‖x‖³ = ‖x‖⁻¹ → 0`.
    have hlim : Tendsto (fun n : ℤ => (t.sizeSeq u n)⁻¹) atBot (𝓝 0) :=
      (t.tendsto_sizeSeq_atBot u).inv_tendsto_atTop
    refine hlim.congr' ?_
    filter_upwards [(t.tendsto_sizeSeq_atBot u).eventually_gt_atTop 1] with n hn
    have hne0 : t.sizeSeq u n ≠ 0 := (lt_trans one_pos hn).ne'
    have hx : ‖(t.q : K) ^ n * (u : K)‖ = t.sizeSeq u n := t.norm_qzpow_mul u n
    have hxne : ‖(t.q : K) ^ n * (u : K)‖ ≠ 1 := by rw [hx]; exact ne_of_gt hn
    rw [Yterm_apply, norm_div, norm_pow, norm_pow, norm_one_sub_of_norm_ne_one hxne, hx,
      max_eq_right hn.le]
    field_simp
  · -- `atTop`: `‖Yterm n‖ = ‖x‖²/1 = ‖x‖² → 0`.
    have hlim : Tendsto (fun n : ℤ => (t.sizeSeq u n) ^ 2) atTop (𝓝 0) := by
      have := (t.tendsto_sizeSeq_atTop u).pow 2
      simpa using this
    refine hlim.congr' ?_
    filter_upwards [(t.tendsto_sizeSeq_atTop u).eventually (eventually_lt_nhds one_pos)] with n hn
    have hx : ‖(t.q : K) ^ n * (u : K)‖ = t.sizeSeq u n := t.norm_qzpow_mul u n
    have hxne : ‖(t.q : K) ^ n * (u : K)‖ ≠ 1 := by rw [hx]; exact ne_of_lt hn
    rw [Yterm_apply, norm_div, norm_pow, norm_pow, norm_one_sub_of_norm_ne_one hxne, hx,
      max_eq_left hn.le, one_pow, div_one]

end Nonarchimedean

end TateParameter

end TateCurvesTheta
