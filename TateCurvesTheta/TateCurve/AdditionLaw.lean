/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.TateCurve.CoordinateInversion
import TateCurvesTheta.TateCurve.PointMap
import TateCurvesTheta.TateCurve.TatePointOnCurve

/-!
# The addition law of the Tate parametrization: negation and the secant step

This file provides the elliptic-curve side of the additivity of the Tate point map:

* **negation**: `tatePoint u⁻¹ = -tatePoint u`, from the inversion symmetry
  `X(u⁻¹) = X(u)`, `Y(u⁻¹) = -Y(u) - X(u)` of the coordinates;
* **the secant step** (`tatePoint_add_of_line`): if the affine points of three off-orbit
  units `u`, `v`, `w` with pairwise distinct `X`-coordinates lie on one line
  `y = λx + μ`, and `w = (u·v)⁻¹`, then `tatePoint u + tatePoint v = tatePoint (u·v)` —
  by matching Mathlib's slope/`addX`/`addY` formulas against the **three-root Vieta
  identity** for the cubic obtained by restricting the Weierstrass equation to the line.

The analytic input — that the line through `P(u)` and `P(v)` meets the curve again at the
class of `(u·v)⁻¹` — is the nonarchimedean Abel theorem, supplied by the weight-space
machinery elsewhere; this file consumes only its conclusion.

## Main results

* `TateCurvesTheta.TateParameter.tatePoint_inv`: negation.
* `TateCurvesTheta.TateParameter.vieta_sum_of_three_roots`: the divided-difference Vieta
  identity for three distinct roots of the restricted cubic.
* `TateCurvesTheta.TateParameter.tatePoint_add_of_line`: the secant-case addition law.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)
variable (hmem : ∀ u : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) →
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u)) (h12 : ‖(12 : K)‖ = 1)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Membership in `qpowers` is inversion-stable. -/
lemma inv_mem_qpowers_iff (u : Kˣ) : u⁻¹ ∈ t.qpowers ↔ u ∈ t.qpowers := by
  constructor
  · intro h
    simpa using inv_mem h
  · intro h
    exact inv_mem h

/-- **Negation**: the Tate point map intertwines `u ↦ u⁻¹` with negation on the curve. -/
theorem tatePoint_inv (u : Kˣ) :
    t.tatePoint hmem h12 u⁻¹ = -t.tatePoint hmem h12 u := by
  classical
  by_cases hu : u ∈ t.qpowers
  · have hu' : u⁻¹ ∈ t.qpowers := inv_mem hu
    rw [t.tatePoint_of_mem hmem h12 hu, t.tatePoint_of_mem hmem h12 hu', neg_zero]
  · have hu' : u⁻¹ ∉ t.qpowers := fun h => hu ((t.inv_mem_qpowers_iff u).mp h)
    have hoff := t.qzpow_mul_ne_one_of_notMem hu
    rw [t.tatePoint_of_notMem hmem h12 hu, t.tatePoint_of_notMem hmem h12 hu']
    rw [WeierstrassCurve.Affine.Point.neg_some]
    refine point_some_congr ?_ ?_
    · exact t.X_inv hoff
    · rw [t.Y_inv hoff]
      rw [WeierstrassCurve.Affine.negY, tateCurve_a₁, tateCurve_a₃]
      ring

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **Three-root Vieta by divided differences**: if `x₁, x₂, x₃` are pairwise distinct
roots of the cubic `-x³ + s·x² + b·x + c`, then `x₁ + x₂ + x₃ = s`. -/
lemma vieta_sum_of_three_roots {x₁ x₂ x₃ s b c : K}
    (h12' : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (e₁ : -x₁ ^ 3 + s * x₁ ^ 2 + b * x₁ + c = 0)
    (e₂ : -x₂ ^ 3 + s * x₂ ^ 2 + b * x₂ + c = 0)
    (e₃ : -x₃ ^ 3 + s * x₃ ^ 2 + b * x₃ + c = 0) :
    x₁ + x₂ + x₃ = s := by
  have d12 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr h12'
  have d13 : x₁ - x₃ ≠ 0 := sub_ne_zero.mpr h13
  have d23 : x₂ - x₃ ≠ 0 := sub_ne_zero.mpr h23
  -- first divided differences
  have f12 : -(x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) + s * (x₁ + x₂) + b = 0 := by
    have hfac : (x₁ - x₂) * (-(x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) + s * (x₁ + x₂) + b) = 0 := by
      linear_combination e₁ - e₂
    exact (mul_eq_zero.mp hfac).resolve_left d12
  have f13 : -(x₁ ^ 2 + x₁ * x₃ + x₃ ^ 2) + s * (x₁ + x₃) + b = 0 := by
    have hfac : (x₁ - x₃) * (-(x₁ ^ 2 + x₁ * x₃ + x₃ ^ 2) + s * (x₁ + x₃) + b) = 0 := by
      linear_combination e₁ - e₃
    exact (mul_eq_zero.mp hfac).resolve_left d13
  -- second divided difference
  have hfac2 : (x₂ - x₃) * (-(x₁ + x₂ + x₃) + s) = 0 := by
    linear_combination f12 - f13
  have hlast := (mul_eq_zero.mp hfac2).resolve_left d23
  linear_combination -hlast

section Secant

variable [DecidableEq K]

omit [CompleteSpace K] [IsUltrametricDist K] [DecidableEq K] in
/-- Restricting the Weierstrass equation to a line `y = λx + μ` produces the cubic
`-x³ + (λ² + λ)x² + (2λμ + μ - a₄)x + (μ² - a₆) = 0` at any curve point on the line. -/
private lemma cubic_of_on_line {x y lam mu : K}
    (hcurve : y ^ 2 + x * y = x ^ 3 + t.a₄ * x + t.a₆) (hline : y = lam * x + mu) :
    -x ^ 3 + (lam ^ 2 + lam) * x ^ 2 + (2 * lam * mu + mu - t.a₄) * x
      + (mu ^ 2 - t.a₆) = 0 := by
  rw [hline] at hcurve
  linear_combination hcurve

/-- **The secant step of the addition law.** If the affine Tate points of `u`, `v` and
`w = (u·v)⁻¹` — all off the orbit, with pairwise distinct `X`-coordinates — lie on the
line `y = λx + μ`, then `tatePoint u + tatePoint v = tatePoint (u·v)`. -/
theorem tatePoint_add_of_line {u v : Kˣ} (hu : u ∉ t.qpowers) (hv : v ∉ t.qpowers)
    (hw : (u * v)⁻¹ ∉ t.qpowers) {lam mu : K}
    (h1 : t.Y u = lam * t.X u + mu) (h2 : t.Y v = lam * t.X v + mu)
    (h3 : t.Y ((u * v)⁻¹) = lam * t.X ((u * v)⁻¹) + mu)
    (hx12 : t.X u ≠ t.X v) (hx13 : t.X u ≠ t.X ((u * v)⁻¹))
    (hx23 : t.X v ≠ t.X ((u * v)⁻¹)) :
    t.tatePoint hmem h12 u + t.tatePoint hmem h12 v = t.tatePoint hmem h12 (u * v) := by
  set w : Kˣ := (u * v)⁻¹ with hwdef
  set W := t.tateCurve.toAffine with hW
  haveI : W.IsElliptic := t.tateCurve_isElliptic h12
  -- curve equations for the three points
  have hcu : t.Y u ^ 2 + t.X u * t.Y u = t.X u ^ 3 + t.a₄ * t.X u + t.a₆ :=
    (t.tateCurve_equation_iff _ _).mp (hmem u (t.qzpow_mul_ne_one_of_notMem hu))
  have hcv : t.Y v ^ 2 + t.X v * t.Y v = t.X v ^ 3 + t.a₄ * t.X v + t.a₆ :=
    (t.tateCurve_equation_iff _ _).mp (hmem v (t.qzpow_mul_ne_one_of_notMem hv))
  have hcw : t.Y w ^ 2 + t.X w * t.Y w = t.X w ^ 3 + t.a₄ * t.X w + t.a₆ :=
    (t.tateCurve_equation_iff _ _).mp (hmem w (t.qzpow_mul_ne_one_of_notMem hw))
  -- Vieta: the third abscissa is the addition abscissa
  have hvieta : t.X u + t.X v + t.X w = lam ^ 2 + lam :=
    vieta_sum_of_three_roots hx12 hx13 hx23
      (t.cubic_of_on_line hcu h1) (t.cubic_of_on_line hcv h2) (t.cubic_of_on_line hcw h3)
  -- the slope of the secant is λ
  have hslope : W.slope (t.X u) (t.X v) (t.Y u) (t.Y v) = lam := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx12, h1, h2,
      div_eq_iff (sub_ne_zero.mpr hx12)]
    ring
  -- rewrite both sides as `some` points and match coordinates
  rw [t.tatePoint_of_notMem hmem h12 hu, t.tatePoint_of_notMem hmem h12 hv]
  have haddeq := WeierstrassCurve.Affine.Point.add_of_X_ne'
    (W := W) (h₁ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (hmem u (t.qzpow_mul_ne_one_of_notMem hu)))
    (h₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (hmem v (t.qzpow_mul_ne_one_of_notMem hv))) hx12
  rw [haddeq]
  have hPuv : t.tatePoint hmem h12 (u * v) = -t.tatePoint hmem h12 w := by
    have h := t.tatePoint_inv hmem h12 (u * v)
    rw [← hwdef] at h
    have h' := congrArg Neg.neg h
    rw [neg_neg] at h'
    exact h'.symm
  rw [hPuv, t.tatePoint_of_notMem hmem h12 hw, neg_inj]
  refine point_some_congr ?_ ?_
  · -- addX matches X w
    show W.addX (t.X u) (t.X v) (W.slope (t.X u) (t.X v) (t.Y u) (t.Y v)) = t.X w
    rw [hslope, WeierstrassCurve.Affine.addX]
    have ha₁ : W.a₁ = 1 := t.tateCurve_a₁
    have ha₂ : W.a₂ = 0 := t.tateCurve_a₂
    rw [ha₁, ha₂]
    linear_combination -hvieta
  · -- negAddY matches Y w
    show W.negAddY (t.X u) (t.X v) (t.Y u)
        (W.slope (t.X u) (t.X v) (t.Y u) (t.Y v)) = t.Y w
    rw [hslope, WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX]
    have ha₁ : W.a₁ = 1 := t.tateCurve_a₁
    have ha₂ : W.a₂ = 0 := t.tateCurve_a₂
    rw [ha₁, ha₂, h3, h1]
    linear_combination lam * (-hvieta)

end Secant

end TateParameter

end TateCurvesTheta
