/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import TateCurvesTheta.TateCurve.Weierstrass

/-!
# Nonvanishing of the discriminant of the Tate curve `E_q`

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the Tate
Weierstrass curve `E_q` (`TateCurvesTheta/TateCurve/Weierstrass.lean`) has nonzero discriminant,
and hence is an elliptic curve. Classically this is the modular product identity
`Δ(E_q) = q · ∏_{n ≥ 1} (1 - qⁿ)²⁴` (Silverman, *Advanced Topics*, Ch. V, Thm 3.1), whose leading
term is `q`.

This file proves the *nonvanishing* `Δ(E_q) ≠ 0` — the fact needed to upgrade `E_q` to an
elliptic curve — via the ultrametric leading-term argument sanctioned as the interim target of
the issue, **without** proving the full product formula. The strategy is:

* each Eisenstein series `sₖ(q)` has leading term `q`: `‖sₖ(q) - q‖ ≤ ‖q‖²`
  (`norm_eisenstein_sub_q_le`), since the `m = 1` term is `q / (1 - q) = q + O(q²)` and every
  later term has norm `≤ ‖q‖²`;
* consequently `‖a₄(q)‖ ≤ ‖q‖` and `‖a₆(q) + q‖ ≤ ‖q‖²`, i.e. `a₆(q) = -q + O(q²)`;
* expanding `Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆` in the Tate coefficients gives
  `Δ(E_q) = -a₆ + a₄² - 64a₄³ - 432a₆² + 72a₄a₆`, whose leading term is `-a₆ = q + O(q²)`, so
  `‖Δ(E_q) - q‖ ≤ ‖q‖²` and therefore `‖Δ(E_q)‖ = ‖q‖ ≠ 0` by the ultrametric isosceles law.

## The `12` hypothesis

The coefficient `a₆(q) = -(5 s₃(q) + 7 s₅(q)) / 12` involves a division by `12`. Controlling its
norm requires `12` to be a unit of norm one, i.e. that the residue characteristic is `≠ 2, 3`. We
carry this as an explicit hypothesis `h12 : ‖(12 : K)‖ = 1` on the two `a₆`-dependent results and
the discriminant theorem, rather than as a global instance, so that the statements stay honest
about what is assumed. (Over a residue field of characteristic `2` or `3` the `a₆`-integrality that
underlies the leading-term estimate rests instead on the exact `12`-divisibility of `5 s₃ + 7 s₅`,
part of the deferred product-formula content.)

## What is proved vs. assumed

* **Proved unconditionally** (no product formula): the leading-term estimates
  `norm_eisenstein_sub_q_le`, `norm_eisenstein_le`, `norm_a₄_le`, and the discriminant expansion
  `tateCurve_Δ_eq`.
* **Proved under `‖(12 : K)‖ = 1`**: `norm_a₆_add_q_le`, `norm_a₆_le`, `tateCurve_Δ_ne_zero`, and
  the upgrade `tateCurve_isElliptic`.
* **Not proved here** (documented seam): the exact product formula
  `Δ(E_q) = q · ∏ (1 - qⁿ)²⁴` and the removal of the `12`-hypothesis. The current Mathlib does not
  expose a standalone `EllipticCurve` structure; upgrading is therefore packaged as the
  `WeierstrassCurve.IsElliptic` typeclass instance `tateCurve_isElliptic`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-- In a nonarchimedean normed field, every natural-number literal `≥ 2` has norm `≤ 1`. -/
private lemma norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : K)‖ ≤ 1 := by
  rw [← Nat.cast_ofNat]
  exact IsUltrametricDist.norm_natCast_le_one K _

omit [IsUltrametricDist K] in
/-- `‖q‖² ≤ ‖q‖`, since `0 < ‖q‖ < 1`. -/
private lemma norm_q_sq_le : ‖(t.q : K)‖ ^ 2 ≤ ‖(t.q : K)‖ := by
  calc ‖(t.q : K)‖ ^ 2
      ≤ ‖(t.q : K)‖ ^ 1 :=
        pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le (by norm_num)
    _ = ‖(t.q : K)‖ := pow_one _

/-- Each term of the Eisenstein series `sₖ(q)` has norm `≤ ‖q‖ⁿ⁺¹`: the natural-number factor
`(n + 1)ᵏ` is harmless (`‖(n + 1 : K)‖ ≤ 1`) and the denominator `1 - qⁿ⁺¹` has norm `1`. -/
private lemma norm_eisenstein_term_le (k n : ℕ) :
    ‖((n + 1 : ℕ) : K) ^ k * (t.q : K) ^ (n + 1) / (1 - (t.q : K) ^ (n + 1))‖
      ≤ ‖(t.q : K)‖ ^ (n + 1) := by
  rw [norm_div, norm_mul, norm_pow, norm_pow, t.norm_one_sub_qpow n, div_one]
  calc ‖((n + 1 : ℕ) : K)‖ ^ k * ‖(t.q : K)‖ ^ (n + 1)
      ≤ 1 ^ k * ‖(t.q : K)‖ ^ (n + 1) := by
        gcongr
        exact IsUltrametricDist.norm_natCast_le_one K (n + 1)
    _ = ‖(t.q : K)‖ ^ (n + 1) := by rw [one_pow, one_mul]

variable [CompleteSpace K]

/-- **Leading term of the Eisenstein series.** `sₖ(q) = q + O(q²)`: the `m = 1` term is
`q / (1 - q) = q + q²/(1 - q)` and every later term has norm `≤ ‖q‖²`, so in the ultrametric world
`‖sₖ(q) - q‖ ≤ ‖q‖²`. -/
lemma norm_eisenstein_sub_q_le (k : ℕ) :
    ‖t.eisenstein k - (t.q : K)‖ ≤ ‖(t.q : K)‖ ^ 2 := by
  have hsum := t.eisenstein_summand_summable k
  rw [eisenstein, hsum.tsum_eq_zero_add]
  -- The `n = 0` term is `q / (1 - q)`; fold the subtracted `q` into it.
  have hq0 : ((0 + 1 : ℕ) : K) ^ k * (t.q : K) ^ (0 + 1) / (1 - (t.q : K) ^ (0 + 1))
      - (t.q : K) = (t.q : K) ^ 2 / (1 - (t.q : K)) := by
    have hne : (1 : K) - (t.q : K) ≠ 0 := by
      simpa using t.one_sub_qpow_ne_zero 0
    simp only [Nat.cast_one, one_pow, pow_one, zero_add]
    field_simp
    ring
  rw [show (((0 + 1 : ℕ) : K) ^ k * (t.q : K) ^ (0 + 1) / (1 - (t.q : K) ^ (0 + 1))
        + ∑' n : ℕ, ((n + 1 + 1 : ℕ) : K) ^ k * (t.q : K) ^ (n + 1 + 1)
          / (1 - (t.q : K) ^ (n + 1 + 1))) - (t.q : K)
      = (((0 + 1 : ℕ) : K) ^ k * (t.q : K) ^ (0 + 1) / (1 - (t.q : K) ^ (0 + 1)) - (t.q : K))
        + ∑' n : ℕ, ((n + 1 + 1 : ℕ) : K) ^ k * (t.q : K) ^ (n + 1 + 1)
          / (1 - (t.q : K) ^ (n + 1 + 1)) from by ring]
  rw [hq0]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · -- `‖q²/(1-q)‖ = ‖q‖²`.
    rw [norm_div, norm_pow, show (1 : K) - (t.q : K) = 1 - (t.q : K) ^ (0 + 1) by rw [pow_one],
      t.norm_one_sub_qpow 0, div_one]
  · -- `‖∑ later terms‖ ≤ ‖q‖²`.
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) (fun n => ?_)
    refine (t.norm_eisenstein_term_le k (n + 1)).trans ?_
    exact pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le (by omega)

/-- The Eisenstein series is norm-bounded by `‖q‖`: `‖sₖ(q)‖ ≤ ‖q‖`. -/
lemma norm_eisenstein_le (k : ℕ) : ‖t.eisenstein k‖ ≤ ‖(t.q : K)‖ := by
  have h := t.norm_eisenstein_sub_q_le k
  rw [show t.eisenstein k = (t.eisenstein k - (t.q : K)) + (t.q : K) from by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (le_refl _))
  exact h.trans t.norm_q_sq_le

/-- The Tate coefficient `a₄(q) = -5 s₃(q)` is norm-bounded by `‖q‖`. -/
lemma norm_a₄_le : ‖t.a₄‖ ≤ ‖(t.q : K)‖ := by
  simp only [a₄_def, norm_mul, norm_neg]
  calc ‖(5 : K)‖ * ‖t.eisenstein 3‖
      ≤ 1 * ‖(t.q : K)‖ :=
        mul_le_mul (norm_ofNat_le_one 5) (t.norm_eisenstein_le 3) (norm_nonneg _) zero_le_one
    _ = ‖(t.q : K)‖ := one_mul _

/-- **Leading term of `a₆`.** `a₆(q) = -q + O(q²)`, i.e. `‖a₆(q) + q‖ ≤ ‖q‖²`. Requires `12` to be
a unit of norm one (residue characteristic `≠ 2, 3`). -/
lemma norm_a₆_add_q_le (h12 : ‖(12 : K)‖ = 1) :
    ‖t.a₆ + (t.q : K)‖ ≤ ‖(t.q : K)‖ ^ 2 := by
  have h12ne : (12 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h12; exact zero_ne_one h12
  have key : t.a₆ + (t.q : K)
      = -(5 * (t.eisenstein 3 - (t.q : K)) + 7 * (t.eisenstein 5 - (t.q : K))) / 12 := by
    rw [a₆_def]; field_simp; ring
  rw [key, norm_div, h12, div_one, norm_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖(5 : K)‖ * ‖t.eisenstein 3 - (t.q : K)‖
        ≤ 1 * ‖(t.q : K)‖ ^ 2 :=
          mul_le_mul (norm_ofNat_le_one 5) (t.norm_eisenstein_sub_q_le 3) (norm_nonneg _)
            zero_le_one
      _ = ‖(t.q : K)‖ ^ 2 := one_mul _
  · rw [norm_mul]
    calc ‖(7 : K)‖ * ‖t.eisenstein 5 - (t.q : K)‖
        ≤ 1 * ‖(t.q : K)‖ ^ 2 :=
          mul_le_mul (norm_ofNat_le_one 7) (t.norm_eisenstein_sub_q_le 5) (norm_nonneg _)
            zero_le_one
      _ = ‖(t.q : K)‖ ^ 2 := one_mul _

/-- The Tate coefficient `a₆(q)` is norm-bounded by `‖q‖` (residue characteristic `≠ 2, 3`). -/
lemma norm_a₆_le (h12 : ‖(12 : K)‖ = 1) : ‖t.a₆‖ ≤ ‖(t.q : K)‖ := by
  have h := t.norm_a₆_add_q_le h12
  rw [show t.a₆ = (t.a₆ + (t.q : K)) - (t.q : K) from by ring, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact h.trans t.norm_q_sq_le
  · rw [norm_neg]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The discriminant of the Tate curve in terms of its coefficients.** Expanding
`Δ = -b₂²b₈ - 8b₄³ - 27b₆² + 9b₂b₄b₆` with the Tate `b`-invariants `b₂ = 1`, `b₄ = 2a₄`,
`b₆ = 4a₆`, `b₈ = a₆ - a₄²` gives a polynomial in `a₄(q), a₆(q)`. -/
lemma tateCurve_Δ_eq :
    t.tateCurve.Δ = -t.a₆ + t.a₄ ^ 2 - 64 * t.a₄ ^ 3 - 432 * t.a₆ ^ 2 + 72 * t.a₄ * t.a₆ := by
  simp only [WeierstrassCurve.Δ, t.tateCurve_b₂, t.tateCurve_b₄, t.tateCurve_b₆, t.tateCurve_b₈]
  ring

/-- **Nonvanishing of the discriminant.** Over a complete nonarchimedean field (residue
characteristic `≠ 2, 3`), `Δ(E_q) ≠ 0`. The proof shows `‖Δ(E_q) - q‖ ≤ ‖q‖² < ‖q‖`, so the
ultrametric isosceles law forces `‖Δ(E_q)‖ = ‖q‖ > 0`. -/
theorem tateCurve_Δ_ne_zero (h12 : ‖(12 : K)‖ = 1) : t.tateCurve.Δ ≠ 0 := by
  have hΔ := t.tateCurve_Δ_eq
  -- `Δ - q` is a sum of five terms each of norm `≤ ‖q‖²`.
  have hDnorm : ‖t.tateCurve.Δ - (t.q : K)‖ ≤ ‖(t.q : K)‖ ^ 2 := by
    have hrw : t.tateCurve.Δ - (t.q : K)
        = -(t.a₆ + (t.q : K)) + t.a₄ ^ 2 + (-64) * t.a₄ ^ 3 + (-432) * t.a₆ ^ 2
            + 72 * t.a₄ * t.a₆ := by
      rw [hΔ]; ring
    rw [hrw]
    have b1 : ‖-(t.a₆ + (t.q : K))‖ ≤ ‖(t.q : K)‖ ^ 2 := by
      rw [norm_neg]; exact t.norm_a₆_add_q_le h12
    have b2 : ‖t.a₄ ^ 2‖ ≤ ‖(t.q : K)‖ ^ 2 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) t.norm_a₄_le 2
    have b3 : ‖(-64 : K) * t.a₄ ^ 3‖ ≤ ‖(t.q : K)‖ ^ 2 := by
      rw [norm_mul, norm_neg, norm_pow]
      calc ‖(64 : K)‖ * ‖t.a₄‖ ^ 3
          ≤ 1 * ‖(t.q : K)‖ ^ 3 :=
            mul_le_mul (norm_ofNat_le_one 64) (pow_le_pow_left₀ (norm_nonneg _) t.norm_a₄_le 3)
              (pow_nonneg (norm_nonneg _) 3) zero_le_one
        _ = ‖(t.q : K)‖ ^ 3 := one_mul _
        _ ≤ ‖(t.q : K)‖ ^ 2 :=
            pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le (by norm_num)
    have b4 : ‖(-432 : K) * t.a₆ ^ 2‖ ≤ ‖(t.q : K)‖ ^ 2 := by
      rw [norm_mul, norm_neg, norm_pow]
      calc ‖(432 : K)‖ * ‖t.a₆‖ ^ 2
          ≤ 1 * ‖(t.q : K)‖ ^ 2 :=
            mul_le_mul (norm_ofNat_le_one 432)
              (pow_le_pow_left₀ (norm_nonneg _) (t.norm_a₆_le h12) 2)
              (pow_nonneg (norm_nonneg _) 2) zero_le_one
        _ = ‖(t.q : K)‖ ^ 2 := one_mul _
    have b5 : ‖(72 : K) * t.a₄ * t.a₆‖ ≤ ‖(t.q : K)‖ ^ 2 := by
      rw [norm_mul, norm_mul, pow_two]
      calc ‖(72 : K)‖ * ‖t.a₄‖ * ‖t.a₆‖
          ≤ 1 * ‖(t.q : K)‖ * ‖(t.q : K)‖ :=
            mul_le_mul
              (mul_le_mul (norm_ofNat_le_one 72) t.norm_a₄_le (norm_nonneg _) zero_le_one)
              (t.norm_a₆_le h12) (norm_nonneg _) (by positivity)
        _ = ‖(t.q : K)‖ * ‖(t.q : K)‖ := by rw [one_mul]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le
          ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le b1 b2)) b3)) b4)) b5)
  -- `‖q‖² < ‖q‖`, so `‖Δ‖ ≥ ‖q‖ - ‖q‖² > 0`.
  have hlt : ‖(t.q : K)‖ ^ 2 < ‖(t.q : K)‖ := by
    calc ‖(t.q : K)‖ ^ 2 = ‖(t.q : K)‖ * ‖(t.q : K)‖ := by rw [pow_two]
      _ < 1 * ‖(t.q : K)‖ := by
          gcongr
          exacts [t.norm_q_pos, t.norm_lt_one]
      _ = ‖(t.q : K)‖ := one_mul _
  have hpos : 0 < ‖t.tateCurve.Δ‖ := by
    have h1 : ‖(t.q : K)‖ - ‖(t.q : K) - t.tateCurve.Δ‖ ≤ ‖t.tateCurve.Δ‖ := by
      simpa using norm_sub_norm_le (t.q : K) ((t.q : K) - t.tateCurve.Δ)
    have h2 : ‖(t.q : K) - t.tateCurve.Δ‖ ≤ ‖(t.q : K)‖ ^ 2 := by
      rw [norm_sub_rev]; exact hDnorm
    linarith
  exact norm_pos_iff.mp hpos

/-- **The Tate curve is an elliptic curve.** Under the residue-characteristic hypothesis
`‖(12 : K)‖ = 1`, the nonvanishing of the discriminant upgrades `E_q` to a
`WeierstrassCurve.IsElliptic` instance (the current Mathlib replacement for a standalone
`EllipticCurve` structure). -/
theorem tateCurve_isElliptic (h12 : ‖(12 : K)‖ = 1) : t.tateCurve.IsElliptic :=
  ⟨(t.tateCurve_Δ_ne_zero h12).isUnit⟩

end TateParameter

end TateCurvesTheta
