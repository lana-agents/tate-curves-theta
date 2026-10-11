/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Square roots in complete ultrametric fields (Hensel's lemma for `X² - a`)

Let `K` be a complete ultrametric normed field. If `‖a - 1‖ < ‖4‖`, then `a` is a square, with a
square root `y` satisfying `‖y - 1‖ < ‖2‖`. This is Hensel's lemma for `X² - a` at the
approximate root `1` (`‖f(1)‖ < ‖f'(1)‖²`), valid in **every** residue characteristic; in
residue characteristic `≠ 2` (`‖2‖ = 1`) it says that every element of the open unit ball
around `1` is a square.

The proof is the Babylonian (Newton) iteration `y (n + 1) = (y n + a / y n) / 2`, started at
`y 0 = 1`, with the exact identities

* `((y + a / y) / 2) ^ 2 - a = (y ^ 2 - a) ^ 2 / (4 * y ^ 2)`,
* `(y + a / y) / 2 - y = (a - y ^ 2) / (2 * y)`.

With `ρ := ‖a - 1‖ / ‖4‖ < 1` every `y n` is a unit, the defect `‖y n ^ 2 - a‖` is at most
`‖4‖ ρ ^ (n + 1)`, and the increments are at most `‖2‖ ρ ^ (n + 1)`.

This generalises the residue-characteristic-`≠ 2` argument of `lana-agents/iut`
(`Iut/Cor312/ThetaData/UltrametricSqrt.lean`) to arbitrary residue characteristic.

## Main results

* `TateCurvesTheta.exists_sq_eq_of_norm_sub_one_lt_norm_four`: `‖a - 1‖ < ‖4‖ → ∃ y, y² = a`,
  with `‖y - 1‖ < ‖2‖`.
* `TateCurvesTheta.exists_sq_eq_of_norm_sq_sub_lt`: for `‖2‖ = 1`, a unit `x₀` with
  `‖x₀² - a‖ < 1` refines to a square root `x` of `a` with `‖x - x₀‖ < 1`.
-/

open Filter Topology

namespace TateCurvesTheta

variable {K : Type*} [NormedField K]

/-- The Babylonian (Newton) iteration for a square root of `a`, started at `1`. -/
noncomputable def babylonianSqrt (a : K) : ℕ → K
  | 0 => 1
  | n + 1 => (babylonianSqrt a n + a / babylonianSqrt a n) / 2

@[simp]
theorem babylonianSqrt_zero (a : K) : babylonianSqrt a 0 = 1 := rfl

theorem babylonianSqrt_succ (a : K) (n : ℕ) :
    babylonianSqrt a (n + 1) = (babylonianSqrt a n + a / babylonianSqrt a n) / 2 := rfl

/-- The exact one-step identity for the defect of the Babylonian iteration. -/
theorem babylonian_step_sq_sub (a x : K) (hx : x ≠ 0) (h2 : (2 : K) ≠ 0) :
    ((x + a / x) / 2) ^ 2 - a = (x ^ 2 - a) ^ 2 / (4 * x ^ 2) := by
  have h4 : (4 : K) = 2 * 2 := by norm_num
  rw [h4]
  field_simp
  ring

/-- The exact one-step identity for the increment of the Babylonian iteration. -/
theorem babylonian_step_sub (a x : K) (hx : x ≠ 0) (h2 : (2 : K) ≠ 0) :
    (x + a / x) / 2 - x = (a - x ^ 2) / (2 * x) := by
  field_simp
  ring

/-- `‖4‖ = ‖2‖²`. -/
theorem norm_four_eq : ‖(4 : K)‖ = ‖(2 : K)‖ ^ 2 := by
  rw [← norm_pow]
  norm_num

variable [IsUltrametricDist K]

/-- In an ultrametric field, `‖2‖ ≤ 1`. -/
theorem norm_two_le_one : ‖(2 : K)‖ ≤ 1 := by
  rw [← Nat.cast_ofNat]
  exact IsUltrametricDist.norm_natCast_le_one K 2

/-- In an ultrametric field, a perturbation of a unit by an element of norm `< 1` is a unit. -/
theorem norm_eq_one_of_norm_sub_lt_one {x y : K} (hx : ‖x‖ = 1) (h : ‖y - x‖ < 1) :
    ‖y‖ = 1 := by
  have hy : y = x + (y - x) := by ring
  have hne : ‖x‖ ≠ ‖y - x‖ := by
    rw [hx]
    exact h.ne'
  rw [hy, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hx, max_eq_left h.le]

section Iteration

variable {a : K} (ha : ‖a - 1‖ < ‖(4 : K)‖)
include ha

omit [IsUltrametricDist K] in
theorem two_ne_zero_of_norm_sub_one_lt : (2 : K) ≠ 0 := by
  intro h
  have h4 : (4 : K) = 2 * 2 := by norm_num
  rw [h4, h, mul_zero, norm_zero] at ha
  exact (norm_nonneg _).not_gt ha

omit [IsUltrametricDist K] in
theorem norm_two_pos_of_norm_sub_one_lt : 0 < ‖(2 : K)‖ :=
  norm_pos_iff.mpr (two_ne_zero_of_norm_sub_one_lt ha)

/-- Along the Babylonian iteration with `ρ = ‖a - 1‖ / ‖4‖ < 1`, every term is a unit and the
defect at stage `n` is at most `‖4‖ ρ ^ (n + 1)`. -/
theorem babylonianSqrt_bound (n : ℕ) :
    ‖babylonianSqrt a n‖ = 1 ∧
      ‖babylonianSqrt a n ^ 2 - a‖ ≤ ‖(4 : K)‖ * (‖a - 1‖ / ‖(4 : K)‖) ^ (n + 1) := by
  have h2 := two_ne_zero_of_norm_sub_one_lt ha
  have h2pos := norm_two_pos_of_norm_sub_one_lt ha
  have h4pos : 0 < ‖(4 : K)‖ := by rw [norm_four_eq]; positivity
  set ρ := ‖a - 1‖ / ‖(4 : K)‖ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one h4pos).mpr ha
  induction n with
  | zero =>
    refine ⟨by simp, ?_⟩
    rw [hρ, zero_add, pow_one, mul_div_cancel₀ _ h4pos.ne', babylonianSqrt_zero, one_pow,
      norm_sub_rev]
  | succ n ih =>
    obtain ⟨hn, hb⟩ := ih
    have hn0 : babylonianSqrt a n ≠ 0 := by
      intro h
      rw [h, norm_zero] at hn
      exact zero_ne_one hn
    have hstep : ‖babylonianSqrt a (n + 1) ^ 2 - a‖ =
        ‖babylonianSqrt a n ^ 2 - a‖ ^ 2 / ‖(4 : K)‖ := by
      rw [babylonianSqrt_succ, babylonian_step_sq_sub a _ hn0 h2, norm_div, norm_mul, norm_pow,
        norm_pow, hn, one_pow, mul_one]
    have hinc : ‖babylonianSqrt a (n + 1) - babylonianSqrt a n‖ =
        ‖babylonianSqrt a n ^ 2 - a‖ / ‖(2 : K)‖ := by
      rw [babylonianSqrt_succ, babylonian_step_sub a _ hn0 h2, norm_div, norm_mul, hn, mul_one,
        norm_sub_rev]
    have hlt : ‖babylonianSqrt a (n + 1) - babylonianSqrt a n‖ < 1 := by
      rw [hinc, div_lt_one h2pos]
      calc ‖babylonianSqrt a n ^ 2 - a‖ ≤ ‖(4 : K)‖ * ρ ^ (n + 1) := hb
        _ < ‖(4 : K)‖ * 1 := by
          gcongr
          exact pow_lt_one₀ hρ0 hρ1 n.succ_ne_zero
        _ = ‖(2 : K)‖ * ‖(2 : K)‖ := by rw [mul_one, norm_four_eq, sq]
        _ ≤ ‖(2 : K)‖ * 1 := by gcongr; exact norm_two_le_one
        _ = ‖(2 : K)‖ := mul_one _
    refine ⟨norm_eq_one_of_norm_sub_lt_one hn hlt, ?_⟩
    rw [hstep, div_le_iff₀ h4pos]
    calc ‖babylonianSqrt a n ^ 2 - a‖ ^ 2 ≤ (‖(4 : K)‖ * ρ ^ (n + 1)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = ‖(4 : K)‖ * ‖(4 : K)‖ * ρ ^ (2 * (n + 1)) := by ring
      _ ≤ ‖(4 : K)‖ * ‖(4 : K)‖ * ρ ^ (n + 1 + 1) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hρ0 hρ1.le (by omega : n + 1 + 1 ≤ 2 * (n + 1)))
            (by positivity)
      _ = ‖(4 : K)‖ * ρ ^ (n + 1 + 1) * ‖(4 : K)‖ := by ring

/-- The increments of the Babylonian iteration are at most `‖2‖ ρ ^ (n + 1)`. -/
theorem norm_babylonianSqrt_succ_sub_le (n : ℕ) :
    ‖babylonianSqrt a (n + 1) - babylonianSqrt a n‖ ≤
      ‖(2 : K)‖ * (‖a - 1‖ / ‖(4 : K)‖) ^ (n + 1) := by
  have h2 := two_ne_zero_of_norm_sub_one_lt ha
  have h2pos := norm_two_pos_of_norm_sub_one_lt ha
  obtain ⟨hn, hb⟩ := babylonianSqrt_bound ha n
  have hn0 : babylonianSqrt a n ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  rw [babylonianSqrt_succ, babylonian_step_sub a _ hn0 h2, norm_div, norm_mul, hn, mul_one,
    norm_sub_rev, div_le_iff₀ h2pos]
  calc ‖babylonianSqrt a n ^ 2 - a‖ ≤ ‖(4 : K)‖ * (‖a - 1‖ / ‖(4 : K)‖) ^ (n + 1) := hb
    _ = ‖(2 : K)‖ * (‖a - 1‖ / ‖(4 : K)‖) ^ (n + 1) * ‖(2 : K)‖ := by
        rw [norm_four_eq]; ring

/-- Every term of the Babylonian iteration lies within `‖2‖ ρ` of `1`. -/
theorem norm_babylonianSqrt_sub_one_le (n : ℕ) :
    ‖babylonianSqrt a n - 1‖ ≤ ‖(2 : K)‖ * (‖a - 1‖ / ‖(4 : K)‖) := by
  have h4pos : 0 < ‖(4 : K)‖ := by
    rw [norm_four_eq]
    have := norm_two_pos_of_norm_sub_one_lt ha
    positivity
  have hρ0 : 0 ≤ ‖a - 1‖ / ‖(4 : K)‖ := by positivity
  have hρ1 : ‖a - 1‖ / ‖(4 : K)‖ ≤ 1 := ((div_lt_one h4pos).mpr ha).le
  induction n with
  | zero => simp only [babylonianSqrt_zero, sub_self, norm_zero]; positivity
  | succ n ih =>
    have hinc := norm_babylonianSqrt_succ_sub_le ha n
    have hinc' : ‖babylonianSqrt a (n + 1) - babylonianSqrt a n‖ ≤
        ‖(2 : K)‖ * (‖a - 1‖ / ‖(4 : K)‖) := by
      refine hinc.trans ?_
      gcongr
      exact pow_le_of_le_one hρ0 hρ1 n.succ_ne_zero
    have hsplit : babylonianSqrt a (n + 1) - 1 =
        (babylonianSqrt a (n + 1) - babylonianSqrt a n) + (babylonianSqrt a n - 1) := by ring
    rw [hsplit]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hinc' ih)

end Iteration

variable [CompleteSpace K]

/-- **Hensel's lemma for square roots**, in every residue characteristic: in a complete
ultrametric field, an element `a` with `‖a - 1‖ < ‖4‖` has a square root `y` with
`‖y - 1‖ < ‖2‖`. -/
theorem exists_sq_eq_of_norm_sub_one_lt_norm_four {a : K} (ha : ‖a - 1‖ < ‖(4 : K)‖) :
    ∃ y : K, y ^ 2 = a ∧ ‖y - 1‖ < ‖(2 : K)‖ := by
  have h2pos := norm_two_pos_of_norm_sub_one_lt ha
  have h4pos : 0 < ‖(4 : K)‖ := by rw [norm_four_eq]; positivity
  set ρ := ‖a - 1‖ / ‖(4 : K)‖ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := (div_lt_one h4pos).mpr ha
  set u : ℕ → K := babylonianSqrt a with hu
  have hdist : ∀ n, dist (u n) (u (n + 1)) ≤ (‖(2 : K)‖ * ρ) * ρ ^ n := by
    intro n
    rw [dist_eq_norm, norm_sub_rev, mul_assoc, ← pow_succ']
    exact norm_babylonianSqrt_succ_sub_le ha n
  have hcauchy : CauchySeq u := cauchySeq_of_le_geometric ρ _ hρ1 hdist
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨y, ?_, ?_⟩
  · have h1 : Tendsto (fun n => u n ^ 2 - a) atTop (𝓝 (y ^ 2 - a)) := (hy.pow 2).sub_const a
    have hpow : Tendsto (fun n : ℕ => ‖(4 : K)‖ * ρ ^ (n + 1)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
        (tendsto_add_atTop_nat 1)).const_mul ‖(4 : K)‖
      simpa using this
    have h0 : Tendsto (fun n => u n ^ 2 - a) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => (babylonianSqrt_bound ha n).2) hpow
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h0)
  · have hlim : Tendsto (fun n => ‖u n - 1‖) atTop (𝓝 ‖y - 1‖) := (hy.sub_const 1).norm
    have hle : ‖y - 1‖ ≤ ‖(2 : K)‖ * ρ :=
      le_of_tendsto' hlim fun n => norm_babylonianSqrt_sub_one_le ha n
    calc ‖y - 1‖ ≤ ‖(2 : K)‖ * ρ := hle
      _ < ‖(2 : K)‖ * 1 := by gcongr
      _ = ‖(2 : K)‖ := mul_one _

/-- **Hensel's lemma for square roots, residue characteristic `≠ 2`**: if `‖2‖ = 1`, a unit `x₀`
with `‖x₀² - a‖ < 1` refines to a square root `x` of `a` with `‖x - x₀‖ < 1`. -/
theorem exists_sq_eq_of_norm_sq_sub_lt (h2 : ‖(2 : K)‖ = 1) {a x₀ : K} (hx₀ : ‖x₀‖ = 1)
    (h : ‖x₀ ^ 2 - a‖ < 1) : ∃ x : K, x ^ 2 = a ∧ ‖x - x₀‖ < 1 := by
  have hx0 : x₀ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx₀
    exact zero_ne_one hx₀
  have ha : ‖a / x₀ ^ 2 - 1‖ < ‖(4 : K)‖ := by
    have : a / x₀ ^ 2 - 1 = -(x₀ ^ 2 - a) / x₀ ^ 2 := by field_simp; ring
    rw [this, norm_div, norm_neg, norm_pow, hx₀, one_pow, div_one, norm_four_eq, h2, one_pow]
    exact h
  obtain ⟨y, hy, hy1⟩ := exists_sq_eq_of_norm_sub_one_lt_norm_four ha
  refine ⟨x₀ * y, ?_, ?_⟩
  · rw [mul_pow, hy]
    field_simp
  · have : x₀ * y - x₀ = x₀ * (y - 1) := by ring
    rw [this, norm_mul, hx₀, one_mul, ← h2]
    exact hy1

/-- In a complete ultrametric field with `‖2‖ = 1`, every element of the open unit ball around
`1` is a square. -/
theorem exists_sq_eq_of_norm_sub_one_lt (h2 : ‖(2 : K)‖ = 1) {a : K} (ha : ‖a - 1‖ < 1) :
    ∃ x : K, x ^ 2 = a := by
  have : ‖a - 1‖ < ‖(4 : K)‖ := by rw [norm_four_eq, h2, one_pow]; exact ha
  obtain ⟨x, hx, -⟩ := exists_sq_eq_of_norm_sub_one_lt_norm_four this
  exact ⟨x, hx⟩

end TateCurvesTheta
