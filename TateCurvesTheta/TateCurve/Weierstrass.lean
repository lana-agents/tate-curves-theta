/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import TateCurvesTheta.QParameter.Basic

/-!
# The Tate Weierstrass model `E_q`

Given a Tate parameter `q` over a complete nonarchimedean field `K`, the Tate curve is the
elliptic curve with the classical Weierstrass equation
`y² + xy = x³ + a₄(q) x + a₆(q)`, where the coefficients are built from the Eisenstein-type
`q`-series
`sₖ(q) = ∑_{m ≥ 1} mᵏ qᵐ / (1 - qᵐ)`
via `a₄(q) = -5 s₃(q)` and `a₆(q) = -(5 s₃(q) + 7 s₅(q)) / 12`
(Silverman, *Advanced Topics*, Ch. V, Thm 3.1).

This file constructs those coefficients, proves the defining `q`-series converge, and packages
the resulting `WeierstrassCurve K`. Upgrading it to an `EllipticCurve K` requires the classical
modular identity `Δ = q ∏_{n ≥ 1} (1 - qⁿ)²⁴` and is deferred to a dependent issue.

## Specialization of the base field

`TateCurvesTheta.TateParameter` is defined over an arbitrary `NormedField`. Convergence of the
Eisenstein series genuinely needs two extra hypotheses, added locally here (matching the seam
convention of `QParameter/BaseChange.lean`):

* `[IsUltrametricDist K]` (nonarchimedean absolute value): it forces `‖1 - qᵐ‖ = 1`, so every
  term of `sₖ(q)` has norm `‖(m : K)‖ᵏ · ‖q‖ᵐ ≤ ‖q‖ᵐ` — a purely geometric bound (in the
  ultrametric world the naive polynomial factor `mᵏ` is harmless because `‖(m : K)‖ ≤ 1`);
* `[CompleteSpace K]`: the norm-summable family is then summable in `K`.

## Main definitions

* `TateCurvesTheta.TateParameter.eisenstein`: the `q`-series `sₖ(q)`.
* `TateCurvesTheta.TateParameter.a₄`, `TateParameter.a₆`: the Tate coefficients.
* `TateCurvesTheta.TateParameter.tateCurve`: the Weierstrass curve `E_q : WeierstrassCurve K`.

## Main results

* `TateParameter.norm_one_sub_qpow`: `‖1 - qⁿ⁺¹‖ = 1`.
* `TateParameter.eisenstein_summand_summable`: the family defining `sₖ(q)` is summable.
* `TateParameter.tateCurve_b₂`, `_b₄`, `_b₆`, `_b₈`: the `b`-invariants of `E_q`, groundwork for
  the deferred discriminant computation.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter V, Theorem 3.1.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- The **Eisenstein-type `q`-series** `sₖ(q) = ∑_{m ≥ 1} mᵏ qᵐ / (1 - qᵐ)`, indexed by
`m = n + 1` over `n : ℕ`. It is the building block of the Tate coefficients. -/
def eisenstein (k : ℕ) : K :=
  ∑' n : ℕ, ((n + 1 : ℕ) : K) ^ k * (t.q : K) ^ (n + 1) / (1 - (t.q : K) ^ (n + 1))

section Nonarchimedean

variable [IsUltrametricDist K]

/-- In a nonarchimedean field, `1 - qⁿ⁺¹` has norm `1`: since `‖qⁿ⁺¹‖ < 1 = ‖1‖`, the
ultrametric "isosceles" law makes the norm of the difference equal to the larger of the two. -/
lemma norm_one_sub_qpow (n : ℕ) : ‖(1 : K) - (t.q : K) ^ (n + 1)‖ = 1 := by
  have hlt : ‖(t.q : K) ^ (n + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) t.norm_lt_one (Nat.succ_ne_zero n)
  have hne : ‖(1 : K)‖ ≠ ‖(t.q : K) ^ (n + 1)‖ := by
    rw [norm_one]; exact (ne_of_lt hlt).symm
  rw [sub_eq_add_neg,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rwa [norm_neg]),
    norm_neg, norm_one, max_eq_left hlt.le]

/-- The factor `1 - qⁿ⁺¹` in the denominator of the Eisenstein series is nonzero. -/
lemma one_sub_qpow_ne_zero (n : ℕ) : (1 : K) - (t.q : K) ^ (n + 1) ≠ 0 :=
  norm_pos_iff.mp (by rw [t.norm_one_sub_qpow n]; exact one_pos)

variable [CompleteSpace K]

/-- The family defining the Eisenstein series `sₖ(q)` is summable: each term has norm
`‖(n + 1 : K)‖ᵏ · ‖q‖ⁿ⁺¹ ≤ ‖q‖ⁿ⁺¹`, dominated by the convergent geometric series `∑ ‖q‖ⁿ⁺¹`. -/
lemma eisenstein_summand_summable (k : ℕ) :
    Summable fun n : ℕ =>
      ((n + 1 : ℕ) : K) ^ k * (t.q : K) ^ (n + 1) / (1 - (t.q : K) ^ (n + 1)) := by
  have hg : Summable fun n : ℕ => ‖(t.q : K)‖ ^ (n + 1) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one).mul_right ‖(t.q : K)‖
  refine hg.of_norm_bounded ?_
  intro n
  rw [norm_div, norm_mul, norm_pow, norm_pow, t.norm_one_sub_qpow n, div_one]
  calc ‖((n + 1 : ℕ) : K)‖ ^ k * ‖(t.q : K)‖ ^ (n + 1)
      ≤ 1 ^ k * ‖(t.q : K)‖ ^ (n + 1) := by
        gcongr
        exact IsUltrametricDist.norm_natCast_le_one K (n + 1)
    _ = ‖(t.q : K)‖ ^ (n + 1) := by rw [one_pow, one_mul]

end Nonarchimedean

/-- The Tate coefficient `a₄(q) = -5 s₃(q)`. -/
def a₄ : K := -5 * t.eisenstein 3

/-- The Tate coefficient `a₆(q) = -(5 s₃(q) + 7 s₅(q)) / 12`. -/
def a₆ : K := -(5 * t.eisenstein 3 + 7 * t.eisenstein 5) / 12

lemma a₄_def : t.a₄ = -5 * t.eisenstein 3 := rfl

lemma a₆_def : t.a₆ = -(5 * t.eisenstein 3 + 7 * t.eisenstein 5) / 12 := rfl

/-- The **Tate Weierstrass curve** `E_q : y² + xy = x³ + a₄(q) x + a₆(q)`. -/
def tateCurve : WeierstrassCurve K where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := t.a₄
  a₆ := t.a₆

@[simp] lemma tateCurve_a₁ : t.tateCurve.a₁ = 1 := rfl
@[simp] lemma tateCurve_a₂ : t.tateCurve.a₂ = 0 := rfl
@[simp] lemma tateCurve_a₃ : t.tateCurve.a₃ = 0 := rfl
@[simp] lemma tateCurve_a₄ : t.tateCurve.a₄ = t.a₄ := rfl
@[simp] lemma tateCurve_a₆ : t.tateCurve.a₆ = t.a₆ := rfl

/-- The `b₂`-invariant of the Tate curve is `1`. -/
lemma tateCurve_b₂ : t.tateCurve.b₂ = 1 := by
  simp only [WeierstrassCurve.b₂, tateCurve_a₁, tateCurve_a₂]; ring

/-- The `b₄`-invariant of the Tate curve is `2 a₄(q)`. -/
lemma tateCurve_b₄ : t.tateCurve.b₄ = 2 * t.a₄ := by
  simp only [WeierstrassCurve.b₄, tateCurve_a₄, tateCurve_a₁, tateCurve_a₃]; ring

/-- The `b₆`-invariant of the Tate curve is `4 a₆(q)`. -/
lemma tateCurve_b₆ : t.tateCurve.b₆ = 4 * t.a₆ := by
  simp only [WeierstrassCurve.b₆, tateCurve_a₆, tateCurve_a₃]; ring

/-- The `b₈`-invariant of the Tate curve is `a₆(q) - a₄(q)²`. -/
lemma tateCurve_b₈ : t.tateCurve.b₈ = t.a₆ - t.a₄ ^ 2 := by
  simp only [WeierstrassCurve.b₈, tateCurve_a₆, tateCurve_a₄, tateCurve_a₁, tateCurve_a₂,
    tateCurve_a₃]; ring

end TateParameter

end TateCurvesTheta
