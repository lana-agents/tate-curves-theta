/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.SpecificLimits.Normed
import TateCurvesTheta.TateCurve.Parametrization

/-!
# Per-term geometric Laurent expansions of the Tate coordinate terms `Xterm`, `Yterm`

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the Tate
coordinate series (`TateCurve/Parametrization.lean`) are built from the terms
```
Xterm u n = qⁿu / (1 - qⁿu)²,   Yterm u n = (qⁿu)² / (1 - qⁿu)³.
```
Each such term is a rational function of `w := qⁿ u` with its only pole at `w = 1`, and therefore
develops as a convergent **geometric power series** on each side of the unit sphere `‖w‖ = 1`.

This file records those per-term expansions, in `HasSum` form, as reusable infrastructure. It is
step 1 of the pole-cancellation Laurent development of the Weierstrass defect
(`TateParameter.DefectLaurentRepr`, issue #146): the two-sided Laurent series of the defect is
assembled from the geometric expansions of the individual `Xterm`/`Yterm` (which do *not* extend to
global Laurent series — they have genuine poles on `qᶻ`) followed by the Cauchy product and the
`qᶻ`-pole cancellation. Only the elementary per-term expansions live here; the Cauchy product and
pole-cancellation summability remain the analytic crux of #146.

## The two sides

The exponent `‖qⁿ u‖ = ‖q‖ⁿ · ‖u‖` crosses `1` as `n` ranges over `ℤ`, so both developments occur:

* **Inner side `‖qⁿ u‖ < 1`** (large positive `n`). The classical geometric developments
  `w/(1-w)² = ∑ₘ m wᵐ` and `w²/(1-w)³ = ∑ₘ C(m+2,2) w^{m+2}` hold directly
  (`hasSum_coe_mul_geometric_of_norm_lt_one`, `hasSum_choose_mul_geometric_of_norm_lt_one`).
* **Outer side `1 < ‖qⁿ u‖`** (large negative `n`). Writing `v := (qⁿ u)⁻¹` with `‖v‖ < 1`, the
  reflection identities `w/(1-w)² = v/(1-v)²` and `w²/(1-w)³ = -v/(1-v)³` (both from
  `1 - w = -w(1 - v)`) reduce the outer development to the inner one in the variable `v`.

## Main results

* `TateParameter.Xterm_hasSum_of_norm_lt_one` / `TateParameter.Xterm_hasSum_of_one_lt_norm`
* `TateParameter.Yterm_hasSum_of_norm_lt_one` / `TateParameter.Yterm_hasSum_of_one_lt_norm`

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.2.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K) (u : Kˣ) (n : ℤ)

/-- The value `w = qⁿ u` occurring in the `n`-th coordinate term is nonzero (`q` and `u` are
units). -/
private lemma qzpow_mul_ne_zero : (t.q : K) ^ n * (u : K) ≠ 0 :=
  mul_ne_zero (zpow_ne_zero n t.q.ne_zero) u.ne_zero

/-- **Inner geometric expansion of the `X`-term.** For `‖qⁿ u‖ < 1`, the term
`Xterm u n = qⁿu/(1-qⁿu)²` develops as the convergent power series `∑ₘ m·(qⁿu)ᵐ`. -/
theorem Xterm_hasSum_of_norm_lt_one (h : ‖(t.q : K) ^ n * (u : K)‖ < 1) :
    HasSum (fun m : ℕ => (m : K) * ((t.q : K) ^ n * (u : K)) ^ m) (t.Xterm u n) := by
  rw [Xterm_apply]
  exact hasSum_coe_mul_geometric_of_norm_lt_one h

/-- **Inner geometric expansion of the `Y`-term.** For `‖qⁿ u‖ < 1`, the term
`Yterm u n = (qⁿu)²/(1-qⁿu)³` develops as the convergent power series `∑ₘ C(m+2,2)·(qⁿu)^{m+2}`. -/
theorem Yterm_hasSum_of_norm_lt_one (h : ‖(t.q : K) ^ n * (u : K)‖ < 1) :
    HasSum (fun m : ℕ => ((m + 2).choose 2 : K) * ((t.q : K) ^ n * (u : K)) ^ (m + 2))
      (t.Yterm u n) := by
  set w : K := (t.q : K) ^ n * (u : K) with hw
  have hval : t.Yterm u n = w ^ 2 * (1 / (1 - w) ^ 3) := by
    rw [Yterm_apply, ← hw, mul_one_div]
  have hkey : ∀ m : ℕ,
      ((m + 2).choose 2 : K) * w ^ (m + 2) = w ^ 2 * (((m + 2).choose 2 : K) * w ^ m) := by
    intro m; rw [pow_add]; ring
  rw [hval]
  simp_rw [hkey]
  exact (hasSum_choose_mul_geometric_of_norm_lt_one 2 h).mul_left (w ^ 2)

/-- **Outer geometric expansion of the `X`-term.** For `1 < ‖qⁿ u‖`, writing `v = (qⁿu)⁻¹`
(`‖v‖ < 1`), the term `Xterm u n = qⁿu/(1-qⁿu)²` develops as `∑ₘ m·vᵐ`. The reflection identity
`w/(1-w)² = v/(1-v)²` comes from `1 - w = -w(1 - v)`. -/
theorem Xterm_hasSum_of_one_lt_norm (h : 1 < ‖(t.q : K) ^ n * (u : K)‖) :
    HasSum (fun m : ℕ => (m : K) * (((t.q : K) ^ n * (u : K))⁻¹) ^ m) (t.Xterm u n) := by
  set w : K := (t.q : K) ^ n * (u : K) with hw
  have hw0 : w ≠ 0 := t.qzpow_mul_ne_zero u n
  have hv : ‖w⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h
  have hne1 : w ≠ 1 := by intro hc; rw [hc] at h; simp at h
  have hsub : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  have hvne1 : w⁻¹ ≠ 1 := by rw [ne_eq, inv_eq_one]; exact hne1
  have hsubv : (1 : K) - w⁻¹ ≠ 0 := sub_ne_zero.mpr (Ne.symm hvne1)
  have hrefl : t.Xterm u n = w⁻¹ / (1 - w⁻¹) ^ 2 := by
    rw [Xterm_apply, ← hw]; field_simp; ring
  rw [hrefl]
  exact hasSum_coe_mul_geometric_of_norm_lt_one hv

/-- **Outer geometric expansion of the `Y`-term.** For `1 < ‖qⁿ u‖`, writing `v = (qⁿu)⁻¹`
(`‖v‖ < 1`), the term `Yterm u n = (qⁿu)²/(1-qⁿu)³` develops as `∑ₘ -C(m+2,2)·v^{m+1}`. The
reflection identity `w²/(1-w)³ = -v/(1-v)³` again comes from `1 - w = -w(1 - v)`. -/
theorem Yterm_hasSum_of_one_lt_norm (h : 1 < ‖(t.q : K) ^ n * (u : K)‖) :
    HasSum (fun m : ℕ => -(((m + 2).choose 2 : K) * (((t.q : K) ^ n * (u : K))⁻¹) ^ (m + 1)))
      (t.Yterm u n) := by
  set w : K := (t.q : K) ^ n * (u : K) with hw
  have hw0 : w ≠ 0 := t.qzpow_mul_ne_zero u n
  have hv : ‖w⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h
  have hne1 : w ≠ 1 := by intro hc; rw [hc] at h; simp at h
  have hsub : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  have hvne1 : w⁻¹ ≠ 1 := by rw [ne_eq, inv_eq_one]; exact hne1
  have hsubv : (1 : K) - w⁻¹ ≠ 0 := sub_ne_zero.mpr (Ne.symm hvne1)
  have hrefl : t.Yterm u n = -(w⁻¹ * (1 / (1 - w⁻¹) ^ 3)) := by
    rw [Yterm_apply, ← hw]; field_simp; ring
  have hkey : ∀ m : ℕ,
      -(((m + 2).choose 2 : K) * (w⁻¹) ^ (m + 1))
        = -(w⁻¹ * (((m + 2).choose 2 : K) * (w⁻¹) ^ m)) := by
    intro m; rw [pow_succ]; ring
  rw [hrefl]
  simp_rw [hkey]
  exact ((hasSum_choose_mul_geometric_of_norm_lt_one 2 hv).mul_left w⁻¹).neg

end TateParameter

end TateCurvesTheta
