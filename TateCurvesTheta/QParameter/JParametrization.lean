/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.SpecificLimits.Normed
import TateCurvesTheta.TateCurve.JInvariant

/-!
# Existence and uniqueness of the Tate parameter with prescribed `j`-invariant

Over a complete nonarchimedean field `K` (with `‖12‖ = 1`, i.e. residue characteristic
`≠ 2, 3`), the map `q ↦ j(E_q)` is a **bijection** from Tate parameters (`0 < ‖q‖ < 1`)
onto the non-integral locus `{j : K | 1 < ‖j‖}`. This is the analytic heart of Tate's
theory: every elliptic curve over `K` with non-integral `j`-invariant has a (unique)
candidate Tate parameter, the first step towards the uniformization theorem for curves
with split multiplicative reduction (issue #37).

The proof is quantitative. All the `q`-series involved (`sₖ(q)`, `a₄`, `a₆`, `c₄`, `Δ`)
are Lipschitz in `q` with constant `1`, and the "degree `≥ 2`" combinations
`sₖ(q) - q`, `a₆ + q`, `Δ - q` are Lipschitz with the strictly smaller constant
`max ‖q₁‖ ‖q₂‖`. By the ultrametric isosceles law the leading terms dominate, giving the
exact isometries `‖Δ₁ - Δ₂‖ = ‖q₁ - q₂‖` and

`‖j(E_{q₁}) - j(E_{q₂})‖ = ‖q₁ - q₂‖ / (‖q₁‖ · ‖q₂‖)`,

whence injectivity. Existence is a Banach fixed-point argument on the sphere
`‖x‖ = ‖j‖⁻¹`: the iteration `x ↦ x · c₄(x)³ / (j · Δ(x))` contracts with factor
`‖j‖⁻¹ < 1`, and its fixed point `q` satisfies `c₄(q)³ = j · Δ(q)`, i.e. `j(E_q) = j`.

## Main results

* `TateCurvesTheta.TateParameter.norm_eisenstein_sub_le`,
  `norm_eisenstein_sub_q_sub_le`: Lipschitz estimates for the Eisenstein series.
* `TateCurvesTheta.TateParameter.norm_tateCurve_Δ_sub_Δ`:
  the discriminant is an isometry in `q`: `‖Δ₁ - Δ₂‖ = ‖q₁ - q₂‖`.
* `TateCurvesTheta.TateParameter.norm_tateJ_sub_tateJ`:
  the `j`-isometry `‖j₁ - j₂‖ = ‖q₁ - q₂‖ / (‖q₁‖ · ‖q₂‖)`.
* `TateCurvesTheta.TateParameter.tateJ_injective`: `q ↦ j(E_q)` is injective.
* `TateCurvesTheta.TateParameter.exists_tateParameter_tateJ_eq`,
  `existsUnique_tateParameter_tateJ_eq`: for every `j : K` with `1 < ‖j‖` there is a
  unique Tate parameter `q` with `j(E_q) = j`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V,
  Theorem 3.1 (the `q ↔ j` bijection; compare also the integrality statement of
  Lemma 5.1(b), of which the Lipschitz estimates here are the metric shadow).
* J. Tate, *A review of non-Archimedean elliptic functions*.
* P. Roquette, *Analytic theory of elliptic functions over local fields*.
-/

open Filter Topology

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]

/-- Two Tate parameters with the same underlying field element are equal. -/
private lemma eq_of_q_eq {t₁ t₂ : TateParameter K} (h : (t₁.q : K) = (t₂.q : K)) :
    t₁ = t₂ := by
  cases t₁
  cases t₂
  simp only [mk.injEq]
  exact Units.ext h

/-- Package a nonzero element of norm less than one as a Tate parameter. -/
def ofNormLtOne {x : K} (h0 : x ≠ 0) (h1 : ‖x‖ < 1) : TateParameter K :=
  ⟨Units.mk0 x h0, by simpa using h1⟩

@[simp] lemma ofNormLtOne_q {x : K} (h0 : x ≠ 0) (h1 : ‖x‖ < 1) :
    ((ofNormLtOne h0 h1).q : K) = x := rfl

variable [IsUltrametricDist K]

/-- **Ultrametric power-difference bound**: `‖x^(n+1) - y^(n+1)‖ ≤ max ‖x‖ ‖y‖ ^ n · ‖x - y‖`,
by induction from `x^(n+2) - y^(n+2) = x (x^(n+1) - y^(n+1)) + y^(n+1) (x - y)` and the
ultrametric inequality. -/
lemma norm_pow_sub_pow_le (x y : K) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ (max ‖x‖ ‖y‖) ^ n * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show x ^ (n + 2) - y ^ (n + 2)
        = x * (x ^ (n + 1) - y ^ (n + 1)) + y ^ (n + 1) * (x - y) from by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖x‖ * ‖x ^ (n + 1) - y ^ (n + 1)‖
          ≤ max ‖x‖ ‖y‖ * ((max ‖x‖ ‖y‖) ^ n * ‖x - y‖) :=
            mul_le_mul (le_max_left _ _) ih (norm_nonneg _)
              (le_trans (norm_nonneg x) (le_max_left _ _))
        _ = (max ‖x‖ ‖y‖) ^ (n + 1) * ‖x - y‖ := by ring
    · rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _) (norm_nonneg _)

/-- In a nonarchimedean normed field, every natural-number literal `≥ 2` has norm `≤ 1`. -/
private lemma norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : K)‖ ≤ 1 := by
  rw [← Nat.cast_ofNat]
  exact IsUltrametricDist.norm_natCast_le_one K _

/-- Power-difference bound relative to a common norm bound `a` and difference bound `d`. -/
private lemma pow_diff_bound {u v : K} {a d : ℝ} (hu : ‖u‖ ≤ a) (hv : ‖v‖ ≤ a)
    (huv : ‖u - v‖ ≤ d) (n : ℕ) : ‖u ^ (n + 1) - v ^ (n + 1)‖ ≤ a ^ n * d := by
  refine (norm_pow_sub_pow_le u v n).trans ?_
  exact mul_le_mul
    (pow_le_pow_left₀ (le_trans (norm_nonneg u) (le_max_left _ _)) (max_le hu hv) n)
    huv (norm_nonneg _) (pow_nonneg (le_trans (norm_nonneg u) hu) n)

variable (t₁ t₂ : TateParameter K)

/-- Termwise Lipschitz estimate for the Eisenstein series: the `m = n + 1` summands at two
Tate parameters differ by at most `max ‖q₁‖ ‖q₂‖ ^ n · ‖q₁ - q₂‖`. -/
private lemma norm_eisensteinSummand_sub_le (k n : ℕ) :
    ‖((n + 1 : ℕ) : K) ^ k * (t₁.q : K) ^ (n + 1) / (1 - (t₁.q : K) ^ (n + 1))
        - ((n + 1 : ℕ) : K) ^ k * (t₂.q : K) ^ (n + 1) / (1 - (t₂.q : K) ^ (n + 1))‖
      ≤ (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ n * ‖(t₁.q : K) - (t₂.q : K)‖ := by
  have h1 := t₁.one_sub_qpow_ne_zero n
  have h2 := t₂.one_sub_qpow_ne_zero n
  rw [div_sub_div _ _ h1 h2,
    show ((n + 1 : ℕ) : K) ^ k * (t₁.q : K) ^ (n + 1) * (1 - (t₂.q : K) ^ (n + 1))
        - (1 - (t₁.q : K) ^ (n + 1)) * (((n + 1 : ℕ) : K) ^ k * (t₂.q : K) ^ (n + 1))
      = ((n + 1 : ℕ) : K) ^ k * ((t₁.q : K) ^ (n + 1) - (t₂.q : K) ^ (n + 1)) from by ring,
    norm_div, norm_mul, norm_mul, t₁.norm_one_sub_qpow n, t₂.norm_one_sub_qpow n, one_mul,
    div_one, norm_pow]
  calc ‖((n + 1 : ℕ) : K)‖ ^ k * ‖(t₁.q : K) ^ (n + 1) - (t₂.q : K) ^ (n + 1)‖
      ≤ 1 * ((max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ n * ‖(t₁.q : K) - (t₂.q : K)‖) :=
        mul_le_mul (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K _))
          (norm_pow_sub_pow_le _ _ n) (norm_nonneg _) zero_le_one
    _ = (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ n * ‖(t₁.q : K) - (t₂.q : K)‖ := one_mul _

variable [CompleteSpace K]

/-- **Lipschitz estimate for the Eisenstein series**:
`‖sₖ(q₁) - sₖ(q₂)‖ ≤ ‖q₁ - q₂‖`. -/
lemma norm_eisenstein_sub_le (k : ℕ) :
    ‖t₁.eisenstein k - t₂.eisenstein k‖ ≤ ‖(t₁.q : K) - (t₂.q : K)‖ := by
  have h1 := t₁.eisenstein_summand_summable k
  have h2 := t₂.eisenstein_summand_summable k
  rw [eisenstein, eisenstein, ← h1.tsum_sub h2]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n => ?_
  refine (t₁.norm_eisensteinSummand_sub_le t₂ k n).trans ?_
  calc (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ n * ‖(t₁.q : K) - (t₂.q : K)‖
      ≤ 1 * ‖(t₁.q : K) - (t₂.q : K)‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ (le_trans (norm_nonneg _) (le_max_left _ _))
            (max_le t₁.norm_lt_one.le t₂.norm_lt_one.le)) (norm_nonneg _)
    _ = ‖(t₁.q : K) - (t₂.q : K)‖ := one_mul _

/-- **Degree-`≥ 2` Lipschitz estimate for the Eisenstein series**: subtracting the common
leading term `q` improves the Lipschitz constant to `max ‖q₁‖ ‖q₂‖`:
`‖(sₖ(q₁) - q₁) - (sₖ(q₂) - q₂)‖ ≤ max ‖q₁‖ ‖q₂‖ · ‖q₁ - q₂‖`. -/
lemma norm_eisenstein_sub_q_sub_le (k : ℕ) :
    ‖(t₁.eisenstein k - (t₁.q : K)) - (t₂.eisenstein k - (t₂.q : K))‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
  have hM0 : (0 : ℝ) ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ :=
    le_trans (norm_nonneg _) (le_max_left _ _)
  have hM1 : max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ ≤ 1 :=
    max_le t₁.norm_lt_one.le t₂.norm_lt_one.le
  have h1 := t₁.eisenstein_summand_summable k
  have h2 := t₂.eisenstein_summand_summable k
  have hg : Summable fun n : ℕ =>
      ((n + 1 : ℕ) : K) ^ k * (t₁.q : K) ^ (n + 1) / (1 - (t₁.q : K) ^ (n + 1))
        - ((n + 1 : ℕ) : K) ^ k * (t₂.q : K) ^ (n + 1) / (1 - (t₂.q : K) ^ (n + 1)) :=
    h1.sub h2
  -- split the difference of the two series into the `m = 1` head and the `m ≥ 2` tail
  have e12 : t₁.eisenstein k - t₂.eisenstein k
      = (((0 + 1 : ℕ) : K) ^ k * (t₁.q : K) ^ (0 + 1) / (1 - (t₁.q : K) ^ (0 + 1))
          - ((0 + 1 : ℕ) : K) ^ k * (t₂.q : K) ^ (0 + 1) / (1 - (t₂.q : K) ^ (0 + 1)))
        + ∑' n : ℕ,
            (((n + 1 + 1 : ℕ) : K) ^ k * (t₁.q : K) ^ (n + 1 + 1)
                / (1 - (t₁.q : K) ^ (n + 1 + 1))
              - ((n + 1 + 1 : ℕ) : K) ^ k * (t₂.q : K) ^ (n + 1 + 1)
                / (1 - (t₂.q : K) ^ (n + 1 + 1))) := by
    rw [eisenstein, eisenstein, ← h1.tsum_sub h2]
    exact hg.tsum_eq_zero_add
  rw [show (t₁.eisenstein k - (t₁.q : K)) - (t₂.eisenstein k - (t₂.q : K))
      = (t₁.eisenstein k - t₂.eisenstein k) - ((t₁.q : K) - (t₂.q : K)) from by ring,
    e12, add_sub_right_comm]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · -- head term: `q₁²/(1 - q₁) - q₂²/(1 - q₂)`
    have hne1 : (1 : K) - (t₁.q : K) ≠ 0 := by simpa using t₁.one_sub_qpow_ne_zero 0
    have hne2 : (1 : K) - (t₂.q : K) ≠ 0 := by simpa using t₂.one_sub_qpow_ne_zero 0
    have hb1 : ((0 + 1 : ℕ) : K) ^ k * (t₁.q : K) ^ (0 + 1) / (1 - (t₁.q : K) ^ (0 + 1))
        - (t₁.q : K) = (t₁.q : K) ^ 2 / (1 - (t₁.q : K)) := by
      simp only [Nat.cast_one, one_pow, pow_one, zero_add]
      field_simp
      ring
    have hb2 : ((0 + 1 : ℕ) : K) ^ k * (t₂.q : K) ^ (0 + 1) / (1 - (t₂.q : K) ^ (0 + 1))
        - (t₂.q : K) = (t₂.q : K) ^ 2 / (1 - (t₂.q : K)) := by
      simp only [Nat.cast_one, one_pow, pow_one, zero_add]
      field_simp
      ring
    rw [show ((0 + 1 : ℕ) : K) ^ k * (t₁.q : K) ^ (0 + 1) / (1 - (t₁.q : K) ^ (0 + 1))
          - ((0 + 1 : ℕ) : K) ^ k * (t₂.q : K) ^ (0 + 1) / (1 - (t₂.q : K) ^ (0 + 1))
          - ((t₁.q : K) - (t₂.q : K))
        = (((0 + 1 : ℕ) : K) ^ k * (t₁.q : K) ^ (0 + 1) / (1 - (t₁.q : K) ^ (0 + 1))
            - (t₁.q : K))
          - (((0 + 1 : ℕ) : K) ^ k * (t₂.q : K) ^ (0 + 1) / (1 - (t₂.q : K) ^ (0 + 1))
            - (t₂.q : K)) from by ring,
      hb1, hb2, div_sub_div _ _ hne1 hne2,
      show (t₁.q : K) ^ 2 * (1 - (t₂.q : K)) - (1 - (t₁.q : K)) * (t₂.q : K) ^ 2
        = ((t₁.q : K) - (t₂.q : K)) * ((t₁.q : K) + (t₂.q : K) - (t₁.q : K) * (t₂.q : K))
          from by ring,
      norm_div, norm_mul, norm_mul,
      show (1 : K) - (t₁.q : K) = 1 - (t₁.q : K) ^ (0 + 1) from by rw [pow_one],
      t₁.norm_one_sub_qpow 0,
      show (1 : K) - (t₂.q : K) = 1 - (t₂.q : K) ^ (0 + 1) from by rw [pow_one],
      t₂.norm_one_sub_qpow 0, one_mul, div_one]
    have hfac : ‖(t₁.q : K) + (t₂.q : K) - (t₁.q : K) * (t₂.q : K)‖
        ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ := by
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (le_max_left _ _) (le_max_right _ _))) ?_)
      rw [norm_neg, norm_mul]
      calc ‖(t₁.q : K)‖ * ‖(t₂.q : K)‖
          ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * 1 :=
            mul_le_mul (le_max_left _ _) t₂.norm_lt_one.le (norm_nonneg _) hM0
        _ = max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ := mul_one _
    calc ‖(t₁.q : K) - (t₂.q : K)‖ * ‖(t₁.q : K) + (t₂.q : K) - (t₁.q : K) * (t₂.q : K)‖
        ≤ ‖(t₁.q : K) - (t₂.q : K)‖ * max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ :=
          mul_le_mul_of_nonneg_left hfac (norm_nonneg _)
      _ = max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := mul_comm _ _
  · -- tail: every summand with `m ≥ 2` is bounded by `max ‖q₁‖ ‖q₂‖ · ‖q₁ - q₂‖`
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
      (mul_nonneg hM0 (norm_nonneg _)) fun n => ?_
    refine (t₁.norm_eisensteinSummand_sub_le t₂ k (n + 1)).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_of_le_one hM0 hM1 n.succ_ne_zero)
      (norm_nonneg _)

/-- **Lipschitz estimate for `a₄`**: `‖a₄(q₁) - a₄(q₂)‖ ≤ ‖q₁ - q₂‖`. -/
lemma norm_a₄_sub_le : ‖t₁.a₄ - t₂.a₄‖ ≤ ‖(t₁.q : K) - (t₂.q : K)‖ := by
  rw [show t₁.a₄ - t₂.a₄ = -5 * (t₁.eisenstein 3 - t₂.eisenstein 3) from by
      rw [a₄_def, a₄_def]; ring,
    norm_mul, norm_neg]
  calc ‖(5 : K)‖ * ‖t₁.eisenstein 3 - t₂.eisenstein 3‖
      ≤ 1 * ‖(t₁.q : K) - (t₂.q : K)‖ :=
        mul_le_mul (norm_ofNat_le_one 5) (t₁.norm_eisenstein_sub_le t₂ 3) (norm_nonneg _)
          zero_le_one
    _ = ‖(t₁.q : K) - (t₂.q : K)‖ := one_mul _

/-- **Lipschitz estimate for `a₆`**: `‖a₆(q₁) - a₆(q₂)‖ ≤ ‖q₁ - q₂‖`
(residue characteristic `≠ 2, 3`). -/
lemma norm_a₆_sub_le (h12 : ‖(12 : K)‖ = 1) :
    ‖t₁.a₆ - t₂.a₆‖ ≤ ‖(t₁.q : K) - (t₂.q : K)‖ := by
  rw [a₆_def, a₆_def, div_sub_div_same,
    show -(5 * t₁.eisenstein 3 + 7 * t₁.eisenstein 5)
        - -(5 * t₂.eisenstein 3 + 7 * t₂.eisenstein 5)
      = -(5 * (t₁.eisenstein 3 - t₂.eisenstein 3) + 7 * (t₁.eisenstein 5 - t₂.eisenstein 5))
        from by ring,
    norm_div, h12, div_one, norm_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖(5 : K)‖ * ‖t₁.eisenstein 3 - t₂.eisenstein 3‖
        ≤ 1 * ‖(t₁.q : K) - (t₂.q : K)‖ :=
          mul_le_mul (norm_ofNat_le_one 5) (t₁.norm_eisenstein_sub_le t₂ 3) (norm_nonneg _)
            zero_le_one
      _ = ‖(t₁.q : K) - (t₂.q : K)‖ := one_mul _
  · rw [norm_mul]
    calc ‖(7 : K)‖ * ‖t₁.eisenstein 5 - t₂.eisenstein 5‖
        ≤ 1 * ‖(t₁.q : K) - (t₂.q : K)‖ :=
          mul_le_mul (norm_ofNat_le_one 7) (t₁.norm_eisenstein_sub_le t₂ 5) (norm_nonneg _)
            zero_le_one
      _ = ‖(t₁.q : K) - (t₂.q : K)‖ := one_mul _

/-- **Lipschitz estimate for `c₄`**: `‖c₄(E_{q₁}) - c₄(E_{q₂})‖ ≤ ‖q₁ - q₂‖`. -/
lemma norm_tateCurve_c₄_sub_le :
    ‖t₁.tateCurve.c₄ - t₂.tateCurve.c₄‖ ≤ ‖(t₁.q : K) - (t₂.q : K)‖ := by
  rw [show t₁.tateCurve.c₄ - t₂.tateCurve.c₄ = -48 * (t₁.a₄ - t₂.a₄) from by
      rw [tateCurve_c₄_eq, tateCurve_c₄_eq]; ring,
    norm_mul, norm_neg]
  calc ‖(48 : K)‖ * ‖t₁.a₄ - t₂.a₄‖
      ≤ 1 * ‖(t₁.q : K) - (t₂.q : K)‖ :=
        mul_le_mul (norm_ofNat_le_one 48) (t₁.norm_a₄_sub_le t₂) (norm_nonneg _) zero_le_one
    _ = ‖(t₁.q : K) - (t₂.q : K)‖ := one_mul _

/-- **Lipschitz estimate for `c₄³`**: `‖c₄(E_{q₁})³ - c₄(E_{q₂})³‖ ≤ ‖q₁ - q₂‖`, since
`‖c₄‖ = 1`. -/
lemma norm_tateCurve_c₄_cube_sub_le :
    ‖t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3‖ ≤ ‖(t₁.q : K) - (t₂.q : K)‖ := by
  have h := norm_pow_sub_pow_le t₁.tateCurve.c₄ t₂.tateCurve.c₄ 2
  rw [t₁.norm_tateCurve_c₄, t₂.norm_tateCurve_c₄, max_self, one_pow, one_mul] at h
  simpa using h.trans (t₁.norm_tateCurve_c₄_sub_le t₂)

/-- **Degree-`≥ 2` Lipschitz estimate for `a₆ + q`**:
`‖(a₆(q₁) + q₁) - (a₆(q₂) + q₂)‖ ≤ max ‖q₁‖ ‖q₂‖ · ‖q₁ - q₂‖`
(residue characteristic `≠ 2, 3`). -/
lemma norm_a₆_add_q_sub_le (h12 : ‖(12 : K)‖ = 1) :
    ‖(t₁.a₆ + (t₁.q : K)) - (t₂.a₆ + (t₂.q : K))‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
  have hM0 : (0 : ℝ) ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ :=
    le_trans (norm_nonneg _) (le_max_left _ _)
  have h12ne : (12 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h12; exact zero_ne_one h12
  have key₁ : t₁.a₆ + (t₁.q : K)
      = -(5 * (t₁.eisenstein 3 - (t₁.q : K)) + 7 * (t₁.eisenstein 5 - (t₁.q : K))) / 12 := by
    rw [a₆_def]; field_simp; ring
  have key₂ : t₂.a₆ + (t₂.q : K)
      = -(5 * (t₂.eisenstein 3 - (t₂.q : K)) + 7 * (t₂.eisenstein 5 - (t₂.q : K))) / 12 := by
    rw [a₆_def]; field_simp; ring
  rw [key₁, key₂, div_sub_div_same,
    show -(5 * (t₁.eisenstein 3 - (t₁.q : K)) + 7 * (t₁.eisenstein 5 - (t₁.q : K)))
        - -(5 * (t₂.eisenstein 3 - (t₂.q : K)) + 7 * (t₂.eisenstein 5 - (t₂.q : K)))
      = -(5 * ((t₁.eisenstein 3 - (t₁.q : K)) - (t₂.eisenstein 3 - (t₂.q : K)))
          + 7 * ((t₁.eisenstein 5 - (t₁.q : K)) - (t₂.eisenstein 5 - (t₂.q : K))))
        from by ring,
    norm_div, h12, div_one, norm_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖(5 : K)‖ * ‖(t₁.eisenstein 3 - (t₁.q : K)) - (t₂.eisenstein 3 - (t₂.q : K))‖
        ≤ 1 * (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖) :=
          mul_le_mul (norm_ofNat_le_one 5) (t₁.norm_eisenstein_sub_q_sub_le t₂ 3)
            (norm_nonneg _) zero_le_one
      _ = max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := one_mul _
  · rw [norm_mul]
    calc ‖(7 : K)‖ * ‖(t₁.eisenstein 5 - (t₁.q : K)) - (t₂.eisenstein 5 - (t₂.q : K))‖
        ≤ 1 * (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖) :=
          mul_le_mul (norm_ofNat_le_one 7) (t₁.norm_eisenstein_sub_q_sub_le t₂ 5)
            (norm_nonneg _) zero_le_one
      _ = max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := one_mul _

/-- **Degree-`≥ 2` Lipschitz estimate for `Δ - q`**:
`‖(Δ(E_{q₁}) - q₁) - (Δ(E_{q₂}) - q₂)‖ ≤ max ‖q₁‖ ‖q₂‖ · ‖q₁ - q₂‖`
(residue characteristic `≠ 2, 3`). -/
lemma norm_tateCurve_Δ_sub_q_sub_le (h12 : ‖(12 : K)‖ = 1) :
    ‖(t₁.tateCurve.Δ - (t₁.q : K)) - (t₂.tateCurve.Δ - (t₂.q : K))‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
  have hM0 : (0 : ℝ) ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ :=
    le_trans (norm_nonneg _) (le_max_left _ _)
  have hM1 : max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ ≤ 1 :=
    max_le t₁.norm_lt_one.le t₂.norm_lt_one.le
  have ha₄₁ : ‖t₁.a₄‖ ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ := t₁.norm_a₄_le.trans (le_max_left _ _)
  have ha₄₂ : ‖t₂.a₄‖ ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ := t₂.norm_a₄_le.trans (le_max_right _ _)
  have ha₆₁ : ‖t₁.a₆‖ ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ :=
    (t₁.norm_a₆_le h12).trans (le_max_left _ _)
  have ha₆₂ : ‖t₂.a₆‖ ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ :=
    (t₂.norm_a₆_le h12).trans (le_max_right _ _)
  have hMsq : (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ 2 * ‖(t₁.q : K) - (t₂.q : K)‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ :=
    mul_le_mul_of_nonneg_right (pow_le_of_le_one hM0 hM1 two_ne_zero) (norm_nonneg _)
  rw [show (t₁.tateCurve.Δ - (t₁.q : K)) - (t₂.tateCurve.Δ - (t₂.q : K))
      = -((t₁.a₆ + (t₁.q : K)) - (t₂.a₆ + (t₂.q : K)))
        + (t₁.a₄ ^ 2 - t₂.a₄ ^ 2) + (-64) * (t₁.a₄ ^ 3 - t₂.a₄ ^ 3)
        + (-432) * (t₁.a₆ ^ 2 - t₂.a₆ ^ 2) + 72 * (t₁.a₄ * t₁.a₆ - t₂.a₄ * t₂.a₆)
      from by rw [t₁.tateCurve_Δ_eq, t₂.tateCurve_Δ_eq]; ring]
  have b1 : ‖-((t₁.a₆ + (t₁.q : K)) - (t₂.a₆ + (t₂.q : K)))‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
    rw [norm_neg]; exact t₁.norm_a₆_add_q_sub_le t₂ h12
  have b2 : ‖t₁.a₄ ^ 2 - t₂.a₄ ^ 2‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
    simpa using pow_diff_bound ha₄₁ ha₄₂ (t₁.norm_a₄_sub_le t₂) 1
  have b3 : ‖(-64 : K) * (t₁.a₄ ^ 3 - t₂.a₄ ^ 3)‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
    rw [norm_mul, norm_neg]
    have h3 : ‖t₁.a₄ ^ 3 - t₂.a₄ ^ 3‖
        ≤ (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ 2 * ‖(t₁.q : K) - (t₂.q : K)‖ := by
      simpa using pow_diff_bound ha₄₁ ha₄₂ (t₁.norm_a₄_sub_le t₂) 2
    calc ‖(64 : K)‖ * ‖t₁.a₄ ^ 3 - t₂.a₄ ^ 3‖
        ≤ 1 * (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖) :=
          mul_le_mul (norm_ofNat_le_one 64) (h3.trans hMsq) (norm_nonneg _) zero_le_one
      _ = max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := one_mul _
  have b4 : ‖(-432 : K) * (t₁.a₆ ^ 2 - t₂.a₆ ^ 2)‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
    rw [norm_mul, norm_neg]
    have h2 : ‖t₁.a₆ ^ 2 - t₂.a₆ ^ 2‖
        ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
      simpa using pow_diff_bound ha₆₁ ha₆₂ (t₁.norm_a₆_sub_le t₂ h12) 1
    calc ‖(432 : K)‖ * ‖t₁.a₆ ^ 2 - t₂.a₆ ^ 2‖
        ≤ 1 * (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖) :=
          mul_le_mul (norm_ofNat_le_one 432) h2 (norm_nonneg _) zero_le_one
      _ = max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := one_mul _
  have b5 : ‖(72 : K) * (t₁.a₄ * t₁.a₆ - t₂.a₄ * t₂.a₆)‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
    rw [norm_mul]
    have hinner : ‖t₁.a₄ * t₁.a₆ - t₂.a₄ * t₂.a₆‖
        ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
      rw [show t₁.a₄ * t₁.a₆ - t₂.a₄ * t₂.a₆
          = t₁.a₄ * (t₁.a₆ - t₂.a₆) + t₂.a₆ * (t₁.a₄ - t₂.a₄) from by ring]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        exact mul_le_mul ha₄₁ (t₁.norm_a₆_sub_le t₂ h12) (norm_nonneg _) hM0
      · rw [norm_mul]
        exact mul_le_mul ha₆₂ (t₁.norm_a₄_sub_le t₂) (norm_nonneg _) hM0
    calc ‖(72 : K)‖ * ‖t₁.a₄ * t₁.a₆ - t₂.a₄ * t₂.a₆‖
        ≤ 1 * (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖) :=
          mul_le_mul (norm_ofNat_le_one 72) hinner (norm_nonneg _) zero_le_one
      _ = max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := one_mul _
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le b1 b2)) b3)) b4)) b5)

/-- **The discriminant is an isometry in the Tate parameter**:
`‖Δ(E_{q₁}) - Δ(E_{q₂})‖ = ‖q₁ - q₂‖`, by the ultrametric isosceles law applied to the
degree-`≥ 2` estimate for `Δ - q` (residue characteristic `≠ 2, 3`). -/
theorem norm_tateCurve_Δ_sub_Δ (h12 : ‖(12 : K)‖ = 1) :
    ‖t₁.tateCurve.Δ - t₂.tateCurve.Δ‖ = ‖(t₁.q : K) - (t₂.q : K)‖ := by
  by_cases hq : (t₁.q : K) = (t₂.q : K)
  · rw [eq_of_q_eq hq]
    simp
  · have hD : 0 < ‖(t₁.q : K) - (t₂.q : K)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
    have hM1 : max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ < 1 := max_lt t₁.norm_lt_one t₂.norm_lt_one
    have hlt : ‖(t₁.tateCurve.Δ - (t₁.q : K)) - (t₂.tateCurve.Δ - (t₂.q : K))‖
        < ‖(t₁.q : K) - (t₂.q : K)‖ :=
      (t₁.norm_tateCurve_Δ_sub_q_sub_le t₂ h12).trans_lt (mul_lt_of_lt_one_left hD hM1)
    rw [show t₁.tateCurve.Δ - t₂.tateCurve.Δ
        = ((t₁.q : K) - (t₂.q : K))
          + ((t₁.tateCurve.Δ - (t₁.q : K)) - (t₂.tateCurve.Δ - (t₂.q : K))) from by ring,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

/-- **The `j`-isometry**: `‖j(E_{q₁}) - j(E_{q₂})‖ = ‖q₁ - q₂‖ / (‖q₁‖ · ‖q₂‖)`
(residue characteristic `≠ 2, 3`). The numerator `c₄₁³·Δ₂ - Δ₁·c₄₂³` decomposes as
`c₄₁³·(Δ₂ - Δ₁) + Δ₁·(c₄₁³ - c₄₂³)`, in which the first summand has exact norm
`‖q₁ - q₂‖` and strictly dominates the second, so the isosceles law applies. -/
theorem norm_tateJ_sub_tateJ (h12 : ‖(12 : K)‖ = 1) :
    ‖t₁.tateJ - t₂.tateJ‖
      = ‖(t₁.q : K) - (t₂.q : K)‖ / (‖(t₁.q : K)‖ * ‖(t₂.q : K)‖) := by
  by_cases hq : (t₁.q : K) = (t₂.q : K)
  · rw [eq_of_q_eq hq]
    simp
  · have hD : 0 < ‖(t₁.q : K) - (t₂.q : K)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
    have hΔ₁ := t₁.tateCurve_Δ_ne_zero h12
    have hΔ₂ := t₂.tateCurve_Δ_ne_zero h12
    have hkey : t₁.tateJ - t₂.tateJ
        = (t₁.tateCurve.c₄ ^ 3 * t₂.tateCurve.Δ - t₁.tateCurve.Δ * t₂.tateCurve.c₄ ^ 3)
          / (t₁.tateCurve.Δ * t₂.tateCurve.Δ) := by
      rw [tateJ_def, tateJ_def, div_sub_div _ _ hΔ₁ hΔ₂]
    have h1 : ‖t₁.tateCurve.c₄ ^ 3 * (t₂.tateCurve.Δ - t₁.tateCurve.Δ)‖
        = ‖(t₁.q : K) - (t₂.q : K)‖ := by
      rw [norm_mul, norm_pow, t₁.norm_tateCurve_c₄, one_pow, one_mul,
        t₂.norm_tateCurve_Δ_sub_Δ t₁ h12]
      exact norm_sub_rev _ _
    have h2 : ‖t₁.tateCurve.Δ * (t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3)‖
        < ‖(t₁.q : K) - (t₂.q : K)‖ := by
      calc ‖t₁.tateCurve.Δ * (t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3)‖
          = ‖t₁.tateCurve.Δ‖ * ‖t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3‖ := norm_mul _ _
        _ ≤ ‖(t₁.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
            rw [t₁.norm_tateCurve_Δ h12]
            exact mul_le_mul_of_nonneg_left (t₁.norm_tateCurve_c₄_cube_sub_le t₂)
              (norm_nonneg _)
        _ < ‖(t₁.q : K) - (t₂.q : K)‖ := mul_lt_of_lt_one_left hD t₁.norm_lt_one
    have hnum : ‖t₁.tateCurve.c₄ ^ 3 * t₂.tateCurve.Δ - t₁.tateCurve.Δ * t₂.tateCurve.c₄ ^ 3‖
        = ‖(t₁.q : K) - (t₂.q : K)‖ := by
      rw [show t₁.tateCurve.c₄ ^ 3 * t₂.tateCurve.Δ - t₁.tateCurve.Δ * t₂.tateCurve.c₄ ^ 3
          = t₁.tateCurve.c₄ ^ 3 * (t₂.tateCurve.Δ - t₁.tateCurve.Δ)
            + t₁.tateCurve.Δ * (t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3) from by ring,
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h1]; exact h2.ne'), h1,
        max_eq_left h2.le]
    rw [hkey, norm_div, hnum, norm_mul, t₁.norm_tateCurve_Δ h12, t₂.norm_tateCurve_Δ h12]

/-- **Injectivity of `q ↦ j(E_q)`**: distinct Tate parameters have distinct `j`-invariants
(residue characteristic `≠ 2, 3`). -/
theorem tateJ_injective (h12 : ‖(12 : K)‖ = 1) (h : t₁.tateJ = t₂.tateJ) : t₁ = t₂ := by
  have h0 := t₁.norm_tateJ_sub_tateJ t₂ h12
  rw [h, sub_self, norm_zero] at h0
  have hpos : 0 < ‖(t₁.q : K)‖ * ‖(t₂.q : K)‖ := mul_pos t₁.norm_q_pos t₂.norm_q_pos
  rcases div_eq_zero_iff.mp h0.symm with hD | hP
  · exact eq_of_q_eq (sub_eq_zero.mp (norm_eq_zero.mp hD))
  · exact absurd hP hpos.ne'

/-- Numerator estimate for the fixed-point contraction: with `g(q) = Δ(E_q) - q` of norm
`≤ ‖q‖²`, the numerator `q₁c₄₁³Δ₂ - q₂c₄₂³Δ₁` decomposes as
`q₁q₂(c₄₁³ - c₄₂³) + c₄₁³(q₁·g(q₂) - q₂·g(q₁)) + g(q₁)q₂(c₄₁³ - c₄₂³)`, each summand of
norm `≤ max ‖q₁‖ ‖q₂‖ ² · ‖q₁ - q₂‖`. -/
private lemma norm_contraction_num_le (h12 : ‖(12 : K)‖ = 1) :
    ‖(t₁.q : K) * t₁.tateCurve.c₄ ^ 3 * t₂.tateCurve.Δ
        - (t₂.q : K) * t₂.tateCurve.c₄ ^ 3 * t₁.tateCurve.Δ‖
      ≤ (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ 2 * ‖(t₁.q : K) - (t₂.q : K)‖ := by
  have hM0 : (0 : ℝ) ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ :=
    le_trans (norm_nonneg _) (le_max_left _ _)
  have hg21 : ‖(t₂.tateCurve.Δ - (t₂.q : K)) - (t₁.tateCurve.Δ - (t₁.q : K))‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
    have h := t₂.norm_tateCurve_Δ_sub_q_sub_le t₁ h12
    rwa [max_comm ‖(t₂.q : K)‖ ‖(t₁.q : K)‖, norm_sub_rev (t₂.q : K) (t₁.q : K)] at h
  have hg1 : ‖t₁.tateCurve.Δ - (t₁.q : K)‖ ≤ (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ 2 :=
    (t₁.norm_tateCurve_Δ_sub_q_le h12).trans
      (pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) 2)
  have hb1 : ‖(t₁.q : K) * (t₂.q : K) * (t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3)‖
      ≤ (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ 2 * ‖(t₁.q : K) - (t₂.q : K)‖ := by
    rw [norm_mul, norm_mul]
    calc ‖(t₁.q : K)‖ * ‖(t₂.q : K)‖ * ‖t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3‖
        ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖
            * ‖(t₁.q : K) - (t₂.q : K)‖ :=
          mul_le_mul
            (mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _) hM0)
            (t₁.norm_tateCurve_c₄_cube_sub_le t₂) (norm_nonneg _) (mul_nonneg hM0 hM0)
      _ = (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ 2 * ‖(t₁.q : K) - (t₂.q : K)‖ := by ring
  have hb2 : ‖t₁.tateCurve.c₄ ^ 3
      * ((t₁.q : K) * (t₂.tateCurve.Δ - (t₂.q : K))
        - (t₂.q : K) * (t₁.tateCurve.Δ - (t₁.q : K)))‖
      ≤ (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ 2 * ‖(t₁.q : K) - (t₂.q : K)‖ := by
    rw [norm_mul, norm_pow, t₁.norm_tateCurve_c₄, one_pow, one_mul,
      show (t₁.q : K) * (t₂.tateCurve.Δ - (t₂.q : K))
          - (t₂.q : K) * (t₁.tateCurve.Δ - (t₁.q : K))
        = (t₁.q : K) * ((t₂.tateCurve.Δ - (t₂.q : K)) - (t₁.tateCurve.Δ - (t₁.q : K)))
          + (t₁.tateCurve.Δ - (t₁.q : K)) * ((t₁.q : K) - (t₂.q : K)) from by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖(t₁.q : K)‖
            * ‖(t₂.tateCurve.Δ - (t₂.q : K)) - (t₁.tateCurve.Δ - (t₁.q : K))‖
          ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖
              * (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖) :=
            mul_le_mul (le_max_left _ _) hg21 (norm_nonneg _) hM0
        _ = (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ 2 * ‖(t₁.q : K) - (t₂.q : K)‖ := by ring
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hg1 (norm_nonneg _)
  have hb3 : ‖(t₁.tateCurve.Δ - (t₁.q : K)) * (t₂.q : K)
      * (t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3)‖
      ≤ (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ 2 * ‖(t₁.q : K) - (t₂.q : K)‖ := by
    rw [norm_mul, norm_mul]
    calc ‖t₁.tateCurve.Δ - (t₁.q : K)‖ * ‖(t₂.q : K)‖
          * ‖t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3‖
        ≤ (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ 2 * 1 * ‖(t₁.q : K) - (t₂.q : K)‖ :=
          mul_le_mul
            (mul_le_mul hg1 t₂.norm_lt_one.le (norm_nonneg _) (pow_nonneg hM0 2))
            (t₁.norm_tateCurve_c₄_cube_sub_le t₂) (norm_nonneg _) (by positivity)
      _ = (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ 2 * ‖(t₁.q : K) - (t₂.q : K)‖ := by ring
  rw [show (t₁.q : K) * t₁.tateCurve.c₄ ^ 3 * t₂.tateCurve.Δ
      - (t₂.q : K) * t₂.tateCurve.c₄ ^ 3 * t₁.tateCurve.Δ
    = (t₁.q : K) * (t₂.q : K) * (t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3)
      + t₁.tateCurve.c₄ ^ 3
        * ((t₁.q : K) * (t₂.tateCurve.Δ - (t₂.q : K))
          - (t₂.q : K) * (t₁.tateCurve.Δ - (t₁.q : K)))
      + (t₁.tateCurve.Δ - (t₁.q : K)) * (t₂.q : K)
        * (t₁.tateCurve.c₄ ^ 3 - t₂.tateCurve.c₄ ^ 3) from by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb1 hb2)) hb3)

open Classical in
/-- Auxiliary total iteration map for the fixed-point construction: for `x ≠ 0` of norm
less than one, `Φ_j(x) = x·c₄(E_x)³ / (j·Δ(E_x))`; junk value `x` otherwise. Its fixed
points of norm `‖j‖⁻¹` are exactly the Tate parameters with `j(E_q) = j`. -/
private def phi (j x : K) : K :=
  if h : x ≠ 0 ∧ ‖x‖ < 1 then
    x * (ofNormLtOne h.1 h.2).tateCurve.c₄ ^ 3 / (j * (ofNormLtOne h.1 h.2).tateCurve.Δ)
  else x

omit [IsUltrametricDist K] [CompleteSpace K] in
private lemma phi_of_pos {j x : K} (h0 : x ≠ 0) (h1 : ‖x‖ < 1) :
    phi j x = x * (ofNormLtOne h0 h1).tateCurve.c₄ ^ 3
      / (j * (ofNormLtOne h0 h1).tateCurve.Δ) :=
  dif_pos ⟨h0, h1⟩

/-- The iteration map sends the punctured unit ball onto the sphere of radius `‖j‖⁻¹`. -/
private lemma norm_phi (h12 : ‖(12 : K)‖ = 1) {j x : K} (h0 : x ≠ 0) (h1 : ‖x‖ < 1) :
    ‖phi j x‖ = ‖j‖⁻¹ := by
  rw [phi_of_pos h0 h1, norm_div, norm_mul, norm_mul, norm_pow,
    (ofNormLtOne h0 h1).norm_tateCurve_c₄, one_pow, mul_one,
    (ofNormLtOne h0 h1).norm_tateCurve_Δ h12, ofNormLtOne_q, mul_comm, ← div_div,
    div_self (norm_ne_zero_iff.mpr h0), one_div]

/-- The contraction estimate on the sphere `‖x‖ = ‖j‖⁻¹`:
`‖Φ_j(x) - Φ_j(y)‖ ≤ ‖j‖⁻¹·‖x - y‖`. -/
private lemma norm_phi_sub_phi (h12 : ‖(12 : K)‖ = 1) {j x y : K} (hj : 1 < ‖j‖)
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : ‖x‖ = ‖j‖⁻¹) (hy : ‖y‖ = ‖j‖⁻¹) :
    ‖phi j x - phi j y‖ ≤ ‖j‖⁻¹ * ‖x - y‖ := by
  have hjpos : 0 < ‖j‖ := lt_trans one_pos hj
  have hj0 : j ≠ 0 := norm_pos_iff.mp hjpos
  have hr0 : 0 < ‖j‖⁻¹ := inv_pos.mpr hjpos
  have hr1 : ‖j‖⁻¹ < 1 := (inv_lt_one₀ hjpos).mpr hj
  have hx1 : ‖x‖ < 1 := by rw [hx]; exact hr1
  have hy1 : ‖y‖ < 1 := by rw [hy]; exact hr1
  have hΔx := (ofNormLtOne hx0 hx1).tateCurve_Δ_ne_zero h12
  have hΔy := (ofNormLtOne hy0 hy1).tateCurve_Δ_ne_zero h12
  have hkey : phi j x - phi j y
      = (x * (ofNormLtOne hx0 hx1).tateCurve.c₄ ^ 3 * (ofNormLtOne hy0 hy1).tateCurve.Δ
          - y * (ofNormLtOne hy0 hy1).tateCurve.c₄ ^ 3 * (ofNormLtOne hx0 hx1).tateCurve.Δ)
        / (j * ((ofNormLtOne hx0 hx1).tateCurve.Δ * (ofNormLtOne hy0 hy1).tateCurve.Δ)) := by
    rw [phi_of_pos hx0 hx1, phi_of_pos hy0 hy1,
      div_sub_div _ _ (mul_ne_zero hj0 hΔx) (mul_ne_zero hj0 hΔy),
      div_eq_div_iff (mul_ne_zero (mul_ne_zero hj0 hΔx) (mul_ne_zero hj0 hΔy))
        (mul_ne_zero hj0 (mul_ne_zero hΔx hΔy))]
    ring
  have hnum := norm_contraction_num_le (ofNormLtOne hx0 hx1) (ofNormLtOne hy0 hy1) h12
  simp only [ofNormLtOne_q] at hnum
  rw [hx, hy, max_self] at hnum
  have hden : ‖j * ((ofNormLtOne hx0 hx1).tateCurve.Δ * (ofNormLtOne hy0 hy1).tateCurve.Δ)‖
      = ‖j‖⁻¹ := by
    rw [norm_mul, norm_mul, (ofNormLtOne hx0 hx1).norm_tateCurve_Δ h12,
      (ofNormLtOne hy0 hy1).norm_tateCurve_Δ h12, ofNormLtOne_q, ofNormLtOne_q, hx, hy,
      ← mul_assoc, mul_inv_cancel₀ hjpos.ne', one_mul]
  rw [hkey, norm_div, hden, div_le_iff₀ hr0]
  exact hnum.trans (le_of_eq (by ring))

/-- The fixed-point iteration `x₀ = j⁻¹`, `x_{k+1} = Φ_j(x_k)`. -/
private def jSeq (j : K) : ℕ → K
  | 0 => j⁻¹
  | n + 1 => phi j (jSeq j n)

/-- The iteration stays on the sphere of radius `‖j‖⁻¹`. -/
private lemma norm_jSeq (h12 : ‖(12 : K)‖ = 1) {j : K} (hj : 1 < ‖j‖) (n : ℕ) :
    ‖jSeq j n‖ = ‖j‖⁻¹ := by
  have hjpos : 0 < ‖j‖ := lt_trans one_pos hj
  have hr0 : 0 < ‖j‖⁻¹ := inv_pos.mpr hjpos
  have hr1 : ‖j‖⁻¹ < 1 := (inv_lt_one₀ hjpos).mpr hj
  induction n with
  | zero => simp [jSeq]
  | succ n ih =>
    have h0 : jSeq j n ≠ 0 := norm_pos_iff.mp (by rw [ih]; exact hr0)
    have h1 : ‖jSeq j n‖ < 1 := by rw [ih]; exact hr1
    rw [jSeq]
    exact norm_phi h12 h0 h1

/-- Geometric decay of consecutive differences along the iteration. -/
private lemma norm_jSeq_sub_le (h12 : ‖(12 : K)‖ = 1) {j : K} (hj : 1 < ‖j‖) (n : ℕ) :
    ‖jSeq j n - jSeq j (n + 1)‖ ≤ ‖jSeq j 0 - jSeq j 1‖ * (‖j‖⁻¹) ^ n := by
  have hjpos : 0 < ‖j‖ := lt_trans one_pos hj
  have hr0 : 0 < ‖j‖⁻¹ := inv_pos.mpr hjpos
  have hne : ∀ m, jSeq j m ≠ 0 := fun m =>
    norm_pos_iff.mp (by rw [norm_jSeq h12 hj m]; exact hr0)
  induction n with
  | zero => simp
  | succ n ih =>
    calc ‖jSeq j (n + 1) - jSeq j (n + 2)‖
        = ‖phi j (jSeq j n) - phi j (jSeq j (n + 1))‖ := rfl
      _ ≤ ‖j‖⁻¹ * ‖jSeq j n - jSeq j (n + 1)‖ :=
          norm_phi_sub_phi h12 hj (hne n) (hne (n + 1)) (norm_jSeq h12 hj n)
            (norm_jSeq h12 hj (n + 1))
      _ ≤ ‖j‖⁻¹ * (‖jSeq j 0 - jSeq j 1‖ * (‖j‖⁻¹) ^ n) :=
          mul_le_mul_of_nonneg_left ih hr0.le
      _ = ‖jSeq j 0 - jSeq j 1‖ * (‖j‖⁻¹) ^ (n + 1) := by ring

/-- **Existence of the Tate parameter with prescribed `j`-invariant**: for every `j : K`
with `1 < ‖j‖` there is a Tate parameter `q` with `j(E_q) = j` (residue characteristic
`≠ 2, 3`). The parameter is produced as the limit of the contracting fixed-point iteration
`x₀ = j⁻¹`, `x_{k+1} = x_k·c₄(E_{x_k})³/(j·Δ(E_{x_k}))` on the sphere `‖x‖ = ‖j‖⁻¹`. -/
theorem exists_tateParameter_tateJ_eq (h12 : ‖(12 : K)‖ = 1) {j : K} (hj : 1 < ‖j‖) :
    ∃ t : TateParameter K, t.tateJ = j := by
  have hjpos : 0 < ‖j‖ := lt_trans one_pos hj
  have hj0 : j ≠ 0 := norm_pos_iff.mp hjpos
  have hr0 : 0 < ‖j‖⁻¹ := inv_pos.mpr hjpos
  have hr1 : ‖j‖⁻¹ < 1 := (inv_lt_one₀ hjpos).mpr hj
  have hnorm : ∀ n, ‖jSeq j n‖ = ‖j‖⁻¹ := norm_jSeq h12 hj
  have hne : ∀ n, jSeq j n ≠ 0 := fun n => norm_pos_iff.mp (by rw [hnorm n]; exact hr0)
  -- the iteration is Cauchy, with limit `L` on the sphere `‖x‖ = ‖j‖⁻¹`
  have hcauchy : CauchySeq (jSeq j) :=
    SeminormedAddCommGroup.cauchySeq_of_le_geometric hr1 (norm_jSeq_sub_le h12 hj)
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hLnorm : ‖L‖ = ‖j‖⁻¹ := by
    refine tendsto_nhds_unique hL.norm ?_
    rw [show (fun n => ‖jSeq j n‖) = fun _ => ‖j‖⁻¹ from funext hnorm]
    exact tendsto_const_nhds
  have hL0 : L ≠ 0 := norm_pos_iff.mp (by rw [hLnorm]; exact hr0)
  have hL1 : ‖L‖ < 1 := by rw [hLnorm]; exact hr1
  -- `L` is a fixed point of the iteration map
  have hfix : phi j L = L := by
    have hshift : Tendsto (fun n : ℕ => jSeq j (n + 1)) atTop (𝓝 L) :=
      hL.comp (tendsto_add_atTop_nat 1)
    have hbound : ∀ n, ‖phi j L - jSeq j (n + 1)‖ ≤ ‖j‖⁻¹ * ‖L - jSeq j n‖ := fun n =>
      norm_phi_sub_phi h12 hj hL0 (hne n) hLnorm (hnorm n)
    have htends1 : Tendsto (fun n => ‖phi j L - jSeq j (n + 1)‖) atTop (𝓝 ‖phi j L - L‖) :=
      (tendsto_const_nhds.sub hshift).norm
    have htends2 : Tendsto (fun n => ‖j‖⁻¹ * ‖L - jSeq j n‖) atTop
        (𝓝 (‖j‖⁻¹ * ‖L - L‖)) :=
      ((tendsto_const_nhds.sub hL).norm).const_mul _
    have hle : ‖phi j L - L‖ ≤ ‖j‖⁻¹ * ‖L - L‖ :=
      le_of_tendsto_of_tendsto' htends1 htends2 hbound
    rw [sub_self, norm_zero, mul_zero] at hle
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hle)
  -- the fixed-point equation is exactly `c₄³ = j·Δ`, i.e. `j(E_L) = j`
  refine ⟨ofNormLtOne hL0 hL1, ?_⟩
  have hΔ := (ofNormLtOne hL0 hL1).tateCurve_Δ_ne_zero h12
  rw [phi_of_pos hL0 hL1, div_eq_iff (mul_ne_zero hj0 hΔ)] at hfix
  rw [tateJ_def, mul_left_cancel₀ hL0 hfix]
  exact mul_div_cancel_right₀ j hΔ

/-- **Existence and uniqueness of the Tate parameter with prescribed `j`-invariant**:
`q ↦ j(E_q)` is a bijection from Tate parameters onto `{j : K | 1 < ‖j‖}` (residue
characteristic `≠ 2, 3`). -/
theorem existsUnique_tateParameter_tateJ_eq (h12 : ‖(12 : K)‖ = 1) {j : K}
    (hj : 1 < ‖j‖) : ∃! t : TateParameter K, t.tateJ = j := by
  obtain ⟨t, ht⟩ := exists_tateParameter_tateJ_eq h12 hj
  exact ⟨t, ht, fun t' ht' => tateJ_injective t' t h12 (ht'.trans ht.symm)⟩

end TateParameter

end TateCurvesTheta
