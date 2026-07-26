/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.TateCurve.Discriminant

/-!
# The `j`-invariant of the Tate curve

The `j`-invariant of `E_q : y² + xy = x³ + a₄x + a₆` as an explicit element of `K`:
`tateJ = c₄³/Δ` with `c₄ = 1 - 48a₄`. Ultrametrically the invariants have exact norms
`‖c₄‖ = 1` and `‖Δ‖ = ‖q‖` (`Discriminant.lean`), so

* `norm_tateJ` : `‖j(E_q)‖ = ‖q‖⁻¹`, in particular
* `one_lt_norm_tateJ` : `‖j(E_q)‖ > 1` — the Tate curve always has non-integral
  `j`-invariant, the analytic incarnation of potentially multiplicative reduction.

This is the input for the existence and uniqueness of the Tate parameter with prescribed
`j`-invariant (`QParameter/JParametrization.lean`): `q ↦ j(E_q)` is an injective map onto
`{j : ‖j‖ > 1}`.

## Main definitions and results

* `TateCurvesTheta.TateParameter.tateJ`: the `j`-invariant `c₄³/Δ` of `E_q`.
* `TateCurvesTheta.TateParameter.tateJ_eq_j`: agreement with Mathlib's
  `WeierstrassCurve.j` under `‖12‖ = 1`.
* `TateCurvesTheta.TateParameter.norm_tateCurve_c₄`: `‖c₄(E_q)‖ = 1`.
* `TateCurvesTheta.TateParameter.norm_tateJ`, `one_lt_norm_tateJ`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The `c₄`-invariant of the Tate curve: `c₄(E_q) = 1 - 48·a₄`. -/
lemma tateCurve_c₄_eq : t.tateCurve.c₄ = 1 - 48 * t.a₄ := by
  simp only [WeierstrassCurve.c₄, t.tateCurve_b₂, t.tateCurve_b₄]
  ring

/-- Leading-term estimate for `c₄`: `‖c₄(E_q) - 1‖ ≤ ‖q‖`. -/
lemma norm_tateCurve_c₄_sub_one_le : ‖t.tateCurve.c₄ - 1‖ ≤ ‖(t.q : K)‖ := by
  rw [tateCurve_c₄_eq, show (1 : K) - 48 * t.a₄ - 1 = -(48 * t.a₄) by ring, norm_neg,
    norm_mul]
  calc ‖(48 : K)‖ * ‖t.a₄‖ ≤ 1 * ‖(t.q : K)‖ := by
        refine mul_le_mul ?_ t.norm_a₄_le (norm_nonneg _) zero_le_one
        simpa using IsUltrametricDist.norm_natCast_le_one K 48
    _ = ‖(t.q : K)‖ := one_mul _

/-- **The exact norm of `c₄`**: `‖c₄(E_q)‖ = 1`, by the ultrametric isosceles law. -/
theorem norm_tateCurve_c₄ : ‖t.tateCurve.c₄‖ = 1 := by
  have hlt : ‖t.tateCurve.c₄ - 1‖ < 1 :=
    lt_of_le_of_lt t.norm_tateCurve_c₄_sub_one_le t.norm_lt_one
  have hup : ‖t.tateCurve.c₄‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (t.tateCurve.c₄ - 1) (1 : K)
    simpa using h.trans (max_le hlt.le (by simp))
  have hdown : (1 : ℝ) ≤ ‖t.tateCurve.c₄‖ := by
    by_contra hcon
    rw [not_le] at hcon
    have h := IsUltrametricDist.norm_add_le_max ((1 : K) - t.tateCurve.c₄) t.tateCurve.c₄
    rw [sub_add_cancel] at h
    have h1 : ‖(1 : K) - t.tateCurve.c₄‖ < 1 := by rwa [norm_sub_rev]
    have := h.trans_lt (max_lt h1 hcon)
    simp at this
  exact le_antisymm hup hdown

/-- The `c₄`-invariant of the Tate curve is nonzero. -/
theorem tateCurve_c₄_ne_zero : t.tateCurve.c₄ ≠ 0 := by
  intro h
  have := t.norm_tateCurve_c₄
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- **The `j`-invariant of the Tate curve** `E_q`, as the explicit element `c₄³/Δ` of `K`
(independent of the `IsElliptic` instance; see `tateJ_eq_j` for the agreement with
Mathlib's `WeierstrassCurve.j`). -/
def tateJ : K := t.tateCurve.c₄ ^ 3 / t.tateCurve.Δ

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma tateJ_def : t.tateJ = t.tateCurve.c₄ ^ 3 / t.tateCurve.Δ := rfl

/-- The defining equation of the `j`-invariant, denominator-cleared. -/
lemma tateJ_mul_Δ (h12 : ‖(12 : K)‖ = 1) :
    t.tateJ * t.tateCurve.Δ = t.tateCurve.c₄ ^ 3 :=
  div_mul_cancel₀ _ (t.tateCurve_Δ_ne_zero h12)

/-- `tateJ` agrees with Mathlib's `j`-invariant of the elliptic curve `E_q`. -/
lemma tateJ_eq_j (h12 : ‖(12 : K)‖ = 1) :
    haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
    t.tateJ = t.tateCurve.j := by
  haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
  rw [WeierstrassCurve.j, tateJ, div_eq_inv_mul]
  congr 1
  rw [← WeierstrassCurve.coe_Δ', ← Units.val_inv_eq_inv_val]

/-- **The norm of the `j`-invariant of the Tate curve**: `‖j(E_q)‖ = ‖q‖⁻¹`. -/
theorem norm_tateJ (h12 : ‖(12 : K)‖ = 1) : ‖t.tateJ‖ = ‖(t.q : K)‖⁻¹ := by
  rw [tateJ, norm_div, norm_pow, t.norm_tateCurve_c₄, one_pow, t.norm_tateCurve_Δ h12,
    one_div]

/-- **The Tate curve has non-integral `j`-invariant**: `1 < ‖j(E_q)‖`. -/
theorem one_lt_norm_tateJ (h12 : ‖(12 : K)‖ = 1) : 1 < ‖t.tateJ‖ := by
  rw [t.norm_tateJ h12]
  exact (one_lt_inv₀ t.norm_q_pos).mpr t.norm_lt_one

end TateParameter

end TateCurvesTheta
