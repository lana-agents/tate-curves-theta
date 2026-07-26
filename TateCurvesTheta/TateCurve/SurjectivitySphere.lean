/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.TateCurve.GroupLaw
import TateCurvesTheta.TateCurve.SphereBounds

/-!
# Surjectivity of the Tate parametrization: unit-sphere points

Every affine point of the Tate curve with `‖x‖ = 1` (equivalently, reducing to the
*smooth locus* of the nodal special fibre) lies in the range of the Tate point map. The
proof is **Newton-free**: the explicit unit `u₀ := y/(x+y)` satisfies the exact curve
identities

* `p(u₀) - x = (a₄x + a₆)/x²`,  `y_k(u₀) - y = y(a₄x + a₆)/x³`

(`p(v) = v/(1-v)²`, `y_k(v) = v²/(1-v)³` the nodal kernels), so `X(u₀)`, `Y(u₀)` agree
with `x`, `y` to order `‖q‖` — the nodal `Gₘ`-parametrization lifts on the nose. Then
the secant from `(x, y)` to the *inverse* Tate point `P(u₀⁻¹)` (or, at the ramification
locus `2y + x ≡ 0`, to `P(-1)`) has slope of norm `> 1`, so the sum lands in the region
`1 < ‖x'‖` already covered by the large-point parametrization
(`exists_tatePoint_eq_some`); subtracting through the group homomorphism finishes.

## Main results

* `TateCurvesTheta.TateParameter.mem_range_of_X_eq`: the exact-hit branch selector.
* `TateCurvesTheta.TateParameter.mem_range_of_slope_norm_gt`: the translation engine —
  a secant of slope-norm `> 1` to an off-orbit Tate point pushes an affine point into
  the solved large region.
* `TateCurvesTheta.TateParameter.mem_range_tatePoint_of_unit_sphere`: every affine
  point with `‖x‖ = 1`, `‖y‖ ≤ 1` is a Tate point.

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
variable (hmem : ∀ u : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) →
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u)) (h12 : ‖(12 : K)‖ = 1)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The ultrametric domination law: `‖b‖ < ‖a‖` forces `‖a + b‖ = ‖a‖`. -/
lemma norm_add_eq_left_of_norm_lt [IsUltrametricDist K] {a b : K} (h : ‖b‖ < ‖a‖) :
    ‖a + b‖ = ‖a‖ := by
  refine le_antisymm ((IsUltrametricDist.norm_add_le_max a b).trans
    (max_le le_rfl h.le)) ?_
  by_contra hcon
  rw [not_le] at hcon
  have hle := IsUltrametricDist.norm_add_le_max (a + b) (-b)
  rw [add_neg_cancel_right, norm_neg] at hle
  exact absurd (hle.trans_lt (max_lt hcon h)) (lt_irrefl _)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Ultrametric bound for differences: `‖a - b‖ ≤ max ‖a‖ ‖b‖`. -/
lemma norm_sub_le_max' [IsUltrametricDist K] (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max a (-b)).trans (by rw [norm_neg])

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- A unit of norm one other than `1` is off the orbit subgroup `qᶻ`. -/
lemma notMem_qpowers_of_norm_one {s : Kˣ} (hs : ‖(s : K)‖ = 1) (hs1 : s ≠ 1) :
    s ∉ t.qpowers := by
  intro h
  obtain ⟨n, hn⟩ := t.mem_qpowers_iff_val_eq.mp h
  have hq0 : (0 : ℝ) < ‖(t.q : K)‖ := t.norm_q_pos
  have hq1 : ‖(t.q : K)‖ < 1 := t.norm_lt_one
  have hnorm : ‖(t.q : K)‖ ^ n = 1 := by
    rw [← norm_zpow, ← hn, hs]
  have hn0 : n = 0 := by
    by_contra hn0
    have hlt : ∀ m : ℤ, 0 < m → ‖(t.q : K)‖ ^ m < 1 := by
      intro m hm
      calc ‖(t.q : K)‖ ^ m = ‖(t.q : K)‖ ^ m.toNat := by
            rw [← zpow_natCast, Int.toNat_of_nonneg hm.le]
        _ ≤ ‖(t.q : K)‖ ^ 1 := pow_le_pow_of_le_one hq0.le hq1.le (by omega)
        _ < 1 := by rwa [pow_one]
    rcases lt_or_gt_of_ne hn0 with hneg | hpos
    · have h1 := hlt (-n) (by omega)
      have h2 : (1 : ℝ) < ‖(t.q : K)‖ ^ n := by
        rw [← neg_neg n, zpow_neg]
        exact (one_lt_inv₀ (zpow_pos hq0 _)).mpr h1
      linarith [hnorm ▸ h2]
    · linarith [hnorm ▸ hlt n hpos]
  rw [hn0, zpow_zero] at hn
  exact hs1 (Units.ext (by simpa using hn))

/-- **Exact-hit branch selector**: if `X(s) = x` for an off-orbit unit `s`, then the
affine point `(x, y)` is `tatePoint s` or `tatePoint s⁻¹`. -/
lemma mem_range_of_X_eq {s : Kˣ} (hs : s ∉ t.qpowers) {x y : K}
    (hns : t.tateCurve.toAffine.Nonsingular x y) (hXeq : t.X s = x) :
    ∃ u : Kˣ, t.tatePoint hmem h12 u =
      WeierstrassCurve.Affine.Point.some x y hns := by
  classical
  subst hXeq
  have hoff := t.qzpow_mul_ne_one_of_notMem hs
  have hxy : y ^ 2 + t.X s * y = t.X s ^ 3 + t.a₄ * t.X s + t.a₆ :=
    (t.tateCurve_equation_iff _ y).mp hns.1
  have hsxy : t.Y s ^ 2 + t.X s * t.Y s = t.X s ^ 3 + t.a₄ * t.X s + t.a₆ :=
    (t.tateCurve_equation_iff _ _).mp (hmem s hoff)
  have hfac : (y - t.Y s) * (y + t.Y s + t.X s) = 0 := by
    linear_combination hxy - hsxy
  rcases mul_eq_zero.mp hfac with h0 | h0
  · refine ⟨s, ?_⟩
    rw [t.tatePoint_of_notMem hmem h12 hs]
    exact point_some_congr rfl (sub_eq_zero.mp h0).symm
  · have hs' : s⁻¹ ∉ t.qpowers := fun h => hs ((t.inv_mem_qpowers_iff s).mp h)
    refine ⟨s⁻¹, ?_⟩
    rw [t.tatePoint_of_notMem hmem h12 hs']
    refine point_some_congr (t.X_inv hoff) ?_
    rw [t.Y_inv hoff]
    linear_combination -h0

/-- **The translation engine**: a secant of slope-norm `> 1` from an affine point to an
off-orbit Tate point of integral abscissa pushes the sum into the solved large-point
region `1 < ‖x'‖`; subtracting the Tate point exhibits the original point in the range
of the parametrization. -/
lemma mem_range_of_slope_norm_gt {s : Kˣ} (hs : s ∉ t.qpowers)
    {x y : K} (hns : t.tateCurve.toAffine.Nonsingular x y) (hne : x ≠ t.X s)
    (hx1 : ‖x‖ ≤ 1) (hXs1 : ‖t.X s‖ ≤ 1)
    (hlam : 1 < ‖(y - t.Y s) / (x - t.X s)‖) :
    ∃ u : Kˣ, t.tatePoint hmem h12 u =
      WeierstrassCurve.Affine.Point.some x y hns := by
  classical
  set W := t.tateCurve.toAffine with hW
  haveI : W.IsElliptic := t.tateCurve_isElliptic h12
  have hoff := t.qzpow_mul_ne_one_of_notMem hs
  have hnss : W.Nonsingular (t.X s) (t.Y s) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (hmem s hoff)
  set lam : K := (y - t.Y s) / (x - t.X s) with hlamdef
  have hslope : W.slope x (t.X s) y (t.Y s) = lam :=
    WeierstrassCurve.Affine.slope_of_X_ne hne
  -- the abscissa of the sum is `lam² + lam - x - X s`, of norm `‖lam‖² > 1`
  have haddX : W.addX x (t.X s) (W.slope x (t.X s) y (t.Y s))
      = lam ^ 2 + lam - x - t.X s := by
    rw [hslope, WeierstrassCurve.Affine.addX, t.tateCurve_a₁, t.tateCurve_a₂]
    ring
  have hxbig : 1 < ‖W.addX x (t.X s) (W.slope x (t.X s) y (t.Y s))‖ := by
    rw [haddX]
    have h1 : ‖lam - x - t.X s‖ ≤ ‖lam‖ := by
      have e1 : lam - x - t.X s = lam + (-x + -t.X s) := by ring
      rw [e1]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_neg]; exact hx1.trans hlam.le
      · rw [norm_neg]; exact hXs1.trans hlam.le
    have h2 : ‖lam - x - t.X s‖ < ‖lam ^ 2‖ := by
      rw [norm_pow]
      refine lt_of_le_of_lt h1 ?_
      nlinarith [hlam]
    have e2 : lam ^ 2 + lam - x - t.X s = lam ^ 2 + (lam - x - t.X s) := by ring
    rw [e2, norm_add_eq_left_of_norm_lt h2, norm_pow]
    nlinarith [hlam, norm_nonneg lam]
  -- solve the sum in the large region and subtract
  have hcond : ¬(x = t.X s ∧ y = W.negY (t.X s) (t.Y s)) := fun h => hne h.1
  obtain ⟨v, hv⟩ := t.exists_tatePoint_eq_some hmem h12
    (WeierstrassCurve.Affine.nonsingular_add hns hnss hcond) hxbig
  refine ⟨v * s⁻¹, ?_⟩
  have hsum : WeierstrassCurve.Affine.Point.some x y hns + t.tatePoint hmem h12 s
      = t.tatePoint hmem h12 v := by
    rw [t.tatePoint_of_notMem hmem h12 hs, hv]
    exact WeierstrassCurve.Affine.Point.add_of_X_ne hne
  rw [t.tatePoint_mul hmem h12 v s⁻¹, t.tatePoint_inv hmem h12 s, ← hsum]
  abel

/-- **Unit-sphere surjectivity**: every affine point of the Tate curve with `‖x‖ = 1`
and `‖y‖ ≤ 1` — i.e. reducing to the smooth locus of the nodal special fibre — lies in
the range of the Tate point map. -/
theorem mem_range_tatePoint_of_unit_sphere {x y : K}
    (hns : t.tateCurve.toAffine.Nonsingular x y) (hx : ‖x‖ = 1) (hy : ‖y‖ ≤ 1) :
    ∃ u : Kˣ, t.tatePoint hmem h12 u =
      WeierstrassCurve.Affine.Point.some x y hns := by
  classical
  have hq0 : (0 : ℝ) < ‖(t.q : K)‖ := t.norm_q_pos
  have hq1 : ‖(t.q : K)‖ < 1 := t.norm_lt_one
  have h2 : ‖(2 : K)‖ = 1 := norm_two_eq_one_of_norm_twelve h12
  have hxy : y ^ 2 + x * y = x ^ 3 + t.a₄ * x + t.a₆ :=
    (t.tateCurve_equation_iff x y).mp hns.1
  have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; linarith
  have ha₄x : ‖t.a₄ * x + t.a₆‖ ≤ ‖(t.q : K)‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (t.norm_a₆_le h12))
    rw [norm_mul, hx, mul_one]
    exact t.norm_a₄_le
  have hrhs : ‖x ^ 3 + t.a₄ * x + t.a₆‖ = 1 := by
    have e : x ^ 3 + t.a₄ * x + t.a₆ = x ^ 3 + (t.a₄ * x + t.a₆) := by ring
    rw [e, norm_add_eq_left_of_norm_lt (by
      rw [norm_pow, hx, one_pow]; exact ha₄x.trans_lt hq1), norm_pow, hx, one_pow]
  have hy1 : ‖y‖ = 1 := by
    by_contra h
    have hylt : ‖y‖ < 1 := lt_of_le_of_ne hy h
    have hsmall : ‖y ^ 2 + x * y‖ < 1 := by
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
      · rw [norm_pow]; nlinarith [norm_nonneg y]
      · rw [norm_mul, hx, one_mul]; exact hylt
    rw [hxy, hrhs] at hsmall
    linarith
  have hxy1 : ‖x + y‖ = 1 := by
    have hfac : y * (y + x) = x ^ 3 + t.a₄ * x + t.a₆ := by linear_combination hxy
    have hnorm := congrArg norm hfac
    rw [norm_mul, hy1, one_mul, hrhs] at hnorm
    rwa [add_comm]
  have hxy0 : x + y ≠ 0 := by intro h; rw [h, norm_zero] at hxy1; linarith
  have hy0 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy1; linarith
  -- the explicit nodal-parametrization unit `u₀ = y/(x+y)`
  set v : K := y / (x + y) with hvdef
  have hv0 : v ≠ 0 := div_ne_zero hy0 hxy0
  set u₀ : Kˣ := Units.mk0 v hv0 with hu₀def
  have hu₀val : ((u₀ : Kˣ) : K) = v := rfl
  have hvnorm : ‖v‖ = 1 := by rw [hvdef, norm_div, hy1, hxy1, div_one]
  have hone_sub : 1 - v = x / (x + y) := by
    rw [hvdef]
    field_simp
    ring
  have h1v0 : 1 - v ≠ 0 := by
    rw [hone_sub]
    exact div_ne_zero hx0 hxy0
  have hu₀ne1 : u₀ ≠ 1 := by
    intro h
    have hv1 : v = 1 := by rw [← hu₀val, h, Units.val_one]
    exact h1v0 (by rw [hv1, sub_self])
  have hu₀mem : u₀ ∉ t.qpowers :=
    t.notMem_qpowers_of_norm_one (by rw [hu₀val]; exact hvnorm) hu₀ne1
  have hoff := t.qzpow_mul_ne_one_of_notMem hu₀mem
  -- exact nodal identities: the parametrization hits `(x, y)` to order `‖q‖`
  have hpc : y * (x + y) - x ^ 3 = t.a₄ * x + t.a₆ := by linear_combination hxy
  have hfrac : v / (1 - v) ^ 2 = y * (x + y) / x ^ 2 := by
    rw [hone_sub, hvdef, div_pow, div_div_div_comm,
      show ((x + y) : K) / (x + y) ^ 2 = 1 / (x + y) from by
        rw [pow_two, div_mul_eq_div_div, div_self hxy0],
      div_div_eq_mul_div, div_one, div_mul_eq_mul_div]
  have hfrac2 : v ^ 2 / (1 - v) ^ 3 = y ^ 2 * (x + y) / x ^ 3 := by
    rw [hone_sub, hvdef, div_pow, div_pow, div_div_div_comm,
      show ((x + y) : K) ^ 2 / (x + y) ^ 3 = 1 / (x + y) from by
        rw [show ((x + y) : K) ^ 3 = (x + y) ^ 2 * (x + y) from by ring,
          div_mul_eq_div_div, div_self (pow_ne_zero 2 hxy0)],
      div_div_eq_mul_div, div_one, div_mul_eq_mul_div]
  have hx2 : (x : K) ^ 2 ≠ 0 := pow_ne_zero 2 hx0
  have hx3 : (x : K) ^ 3 ≠ 0 := pow_ne_zero 3 hx0
  have hp : v / (1 - v) ^ 2 - x = (t.a₄ * x + t.a₆) / x ^ 2 := by
    rw [hfrac, eq_div_iff hx2, sub_mul, div_mul_cancel₀ _ hx2]
    linear_combination hpc
  have hyk : v ^ 2 / (1 - v) ^ 3 - y = y * (t.a₄ * x + t.a₆) / x ^ 3 := by
    rw [hfrac2, eq_div_iff hx3, sub_mul, div_mul_cancel₀ _ hx3]
    linear_combination y * hpc
  have hXu₀ : ‖t.X u₀ - x‖ ≤ ‖(t.q : K)‖ := by
    have hb := t.norm_X_sub_node_le (u := u₀) (by rw [hu₀val]; exact hvnorm)
    have hsplit : t.X u₀ - x
        = (t.X u₀ - (u₀ : K) / (1 - (u₀ : K)) ^ 2) + (v / (1 - v) ^ 2 - x) := by
      rw [hu₀val]; ring
    rw [hsplit]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb ?_)
    rw [hp, norm_div, norm_pow, hx, one_pow, div_one]
    exact ha₄x
  have hYu₀ : ‖t.Y u₀ - y‖ ≤ ‖(t.q : K)‖ := by
    have hb := t.norm_Y_sub_node_le (u := u₀) (by rw [hu₀val]; exact hvnorm)
    have hsplit : t.Y u₀ - y
        = (t.Y u₀ - (u₀ : K) ^ 2 / (1 - (u₀ : K)) ^ 3) + (v ^ 2 / (1 - v) ^ 3 - y) := by
      rw [hu₀val]; ring
    rw [hsplit]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb ?_)
    rw [hyk, norm_div, norm_mul, norm_pow, hx, one_pow, div_one, hy1, one_mul]
    exact ha₄x
  have hXu₀1 : ‖t.X u₀‖ ≤ 1 := by
    have e : t.X u₀ = x + (t.X u₀ - x) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx.le ?_)
    exact hXu₀.trans hq1.le
  -- the inverse point `s = u₀⁻¹`
  set s : Kˣ := u₀⁻¹ with hsdef
  have hsmem : s ∉ t.qpowers := fun h => hu₀mem ((t.inv_mem_qpowers_iff u₀).mp h)
  have hXs : t.X s = t.X u₀ := t.X_inv hoff
  have hYs : t.Y s = -t.Y u₀ - t.X u₀ := t.Y_inv hoff
  have hXs1 : ‖t.X s‖ ≤ 1 := by rw [hXs]; exact hXu₀1
  by_cases hhit : t.X s = x
  · exact t.mem_range_of_X_eq hmem h12 hsmem hns hhit
  have hδ : ‖x - t.X s‖ ≤ ‖(t.q : K)‖ := by
    rw [hXs, show x - t.X u₀ = -(t.X u₀ - x) by ring, norm_neg]
    exact hXu₀
  have hδ0 : x - t.X s ≠ 0 := sub_ne_zero.mpr (Ne.symm hhit)
  by_cases hgen : ‖2 * y + x‖ = 1
  · -- generic position: the secant to `P(u₀⁻¹)` has huge slope
    have hN : ‖y - t.Y s‖ = 1 := by
      have hNval : y - t.Y s = (2 * y + x) + ((t.Y u₀ - y) + (t.X u₀ - x)) := by
        rw [hYs]; ring
      rw [hNval, norm_add_eq_left_of_norm_lt (by
        rw [hgen]
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
          (max_lt (hYu₀.trans_lt hq1) (hXu₀.trans_lt hq1)))]
      exact hgen
    have hlam : 1 < ‖(y - t.Y s) / (x - t.X s)‖ := by
      rw [norm_div, hN, one_div]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hδ0)).mpr (hδ.trans_lt hq1)
    exact t.mem_range_of_slope_norm_gt hmem h12 hsmem hns (Ne.symm hhit) hx.le hXs1 hlam
  · -- ramification position `2y + x ≡ 0`: translate by the literal unit `-1`
    have h4 : ‖(4 : K)‖ = 1 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this, norm_mul, h2, one_mul]
    have h40 : (4 : K) ≠ 0 := by intro h; rw [h, norm_zero] at h4; linarith
    have h20 : (2 : K) ≠ 0 := by intro h; rw [h, norm_zero] at h2; linarith
    have h2yx : ‖2 * y + x‖ < 1 := by
      refine lt_of_le_of_ne ?_ hgen
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hx.le)
      rw [norm_mul, h2, one_mul]
      exact hy
    have hneg1ne : (-1 : Kˣ) ≠ 1 := by
      intro h
      have : ((-1 : Kˣ) : K) = 1 := by rw [h, Units.val_one]
      rw [Units.val_neg, Units.val_one] at this
      exact h20 (by linear_combination -this)
    have hneg1mem : (-1 : Kˣ) ∉ t.qpowers :=
      t.notMem_qpowers_of_norm_one (by rw [Units.val_neg, Units.val_one, norm_neg, norm_one])
        hneg1ne
    have hoff1 := t.qzpow_mul_ne_one_of_notMem hneg1mem
    have hval : ((-1 : Kˣ) : K) = -1 := by rw [Units.val_neg, Units.val_one]
    -- x is near the branch point `-1/4`
    have hx4 : ‖x + 4⁻¹‖ < 1 := by
      have h4inv : (4 : K) * 4⁻¹ = 1 := mul_inv_cancel₀ h40
      have hkey : x ^ 2 * (x + 4⁻¹) * 4
          = (2 * y + x) ^ 2 - 4 * (t.a₄ * x) - 4 * t.a₆ := by
        linear_combination (-4 : K) * hxy + x ^ 2 * h4inv
      have hnorm := congrArg norm hkey
      simp only [norm_mul, norm_pow, hx, one_pow, h4, one_mul, mul_one] at hnorm
      rw [hnorm]
      refine lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt ?_ ?_)
      · refine lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt ?_ ?_)
        · rw [norm_pow]
          nlinarith [norm_nonneg (2 * y + x)]
        · rw [show ((4 : K)) * (t.a₄ * x) = 4 * t.a₄ * x from by ring, norm_mul,
            norm_mul, h4, one_mul, hx, mul_one]
          exact t.norm_a₄_le.trans_lt hq1
      · rw [norm_mul, h4, one_mul]
        exact (t.norm_a₆_le h12).trans_lt hq1
    -- `X(-1) ≡ -1/4` and `Y(-1) ≡ 1/8`
    have hp1 : ((-1 : Kˣ) : K) / (1 - ((-1 : Kˣ) : K)) ^ 2 = -4⁻¹ := by
      rw [hval, show (1 : K) - -1 = 2 by ring, show ((2 : K)) ^ 2 = 4 by norm_num,
        neg_div, one_div]
    have hyk1 : ((-1 : Kˣ) : K) ^ 2 / (1 - ((-1 : Kˣ) : K)) ^ 3 = 8⁻¹ := by
      rw [hval, show ((-1 : K)) ^ 2 = 1 by ring, show (1 : K) - -1 = 2 by ring,
        show ((2 : K)) ^ 3 = 8 by norm_num, one_div]
    have hXneg : ‖t.X (-1) + 4⁻¹‖ ≤ ‖(t.q : K)‖ := by
      have hb := t.norm_X_sub_node_le (u := (-1 : Kˣ)) (by rw [hval]; simp)
      rwa [hp1, sub_neg_eq_add] at hb
    have hYneg : ‖t.Y (-1) - 8⁻¹‖ ≤ ‖(t.q : K)‖ := by
      have hb := t.norm_Y_sub_node_le (u := (-1 : Kˣ)) (by rw [hval]; simp)
      rwa [hyk1] at hb
    have hXneg1 : ‖t.X (-1)‖ ≤ 1 := by
      have e : t.X (-1) = -(4 : K)⁻¹ + (t.X (-1) + 4⁻¹) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hXneg.trans hq1.le))
      rw [norm_neg, norm_inv, h4, inv_one]
    by_cases hhit' : t.X (-1) = x
    · exact t.mem_range_of_X_eq hmem h12 hneg1mem hns hhit'
    -- `y ≡ 1/8`
    have hy8 : ‖y - 8⁻¹‖ < 1 := by
      have h8 : ‖(8 : K)‖ = 1 := by
        have : (8 : K) = 2 * 4 := by norm_num
        rw [this, norm_mul, h2, h4, one_mul]
      have h8inv : (8 : K)⁻¹ * 2 = 4⁻¹ := by
        rw [show (8 : K) = 4 * 2 by norm_num, mul_inv]
        have h20' : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h20
        rw [mul_assoc, h20', mul_one]
      have hkey : (y - 8⁻¹) * 2 = (2 * y + x) - (x + 4⁻¹) := by
        linear_combination -h8inv
      have hnorm := congrArg norm hkey
      rw [norm_mul, h2, mul_one] at hnorm
      rw [hnorm]
      exact lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt h2yx hx4)
    -- the curve equation at `-1` and the divided-difference identity
    have hc2 : t.Y (-1) ^ 2 + t.X (-1) * t.Y (-1)
        = t.X (-1) ^ 3 + t.a₄ * t.X (-1) + t.a₆ :=
      (t.tateCurve_equation_iff _ _).mp (hmem _ hoff1)
    have hident : (y - t.Y (-1)) * (y + t.Y (-1) + x)
        = (x - t.X (-1)) * (x ^ 2 + x * t.X (-1) + t.X (-1) ^ 2 + t.a₄ - t.Y (-1)) := by
      linear_combination hxy - hc2
    -- `‖M‖ = 1` where `M ≡ 3/16 - 1/8 = 1/16`
    have h16 : ‖(16 : K)⁻¹‖ = 1 := by
      have : (16 : K) = 4 * 4 := by norm_num
      rw [norm_inv, this, norm_mul, h4, one_mul, inv_one]
    have hM : ‖x ^ 2 + x * t.X (-1) + t.X (-1) ^ 2 + t.a₄ - t.Y (-1)‖ = 1 := by
      have h1616 : (4 : K)⁻¹ * 4⁻¹ = 16⁻¹ := by
        rw [← mul_inv]
        norm_num
      have hsq : ∀ a b : K, ‖a + 4⁻¹‖ < 1 → ‖b + 4⁻¹‖ < 1 → ‖a * b - 16⁻¹‖ < 1 := by
        intro a b ha hb
        have e : a * b - 16⁻¹
            = (a + 4⁻¹) * (b + 4⁻¹) + (-4⁻¹) * ((a + 4⁻¹) + (b + 4⁻¹)) := by
          linear_combination h1616
        rw [e]
        have h4i : ‖(-4⁻¹ : K)‖ = 1 := by rw [norm_neg, norm_inv, h4, inv_one]
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
        · rw [norm_mul]; nlinarith [norm_nonneg (a + 4⁻¹), norm_nonneg (b + 4⁻¹)]
        · rw [norm_mul, h4i, one_mul]
          exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      have hXneg' : ‖t.X (-1) + 4⁻¹‖ < 1 := hXneg.trans_lt hq1
      have h1 := hsq x x hx4 hx4
      have h2' := hsq x (t.X (-1)) hx4 hXneg'
      have h3 := hsq (t.X (-1)) (t.X (-1)) hXneg' hXneg'
      have h160 : (16 : K) ≠ 0 := by
        intro h
        have h16n : ‖(16 : K)‖ = 1 := by
          rw [show (16 : K) = 4 * 4 by norm_num, norm_mul, h4, one_mul]
        rw [h, norm_zero] at h16n
        linarith
      have h80 : (8 : K) ≠ 0 := by
        intro h
        have h8n : ‖(8 : K)‖ = 1 := by
          rw [show (8 : K) = 2 * 4 by norm_num, norm_mul, h2, h4, one_mul]
        rw [h, norm_zero] at h8n
        linarith
      have h816' : (8 : K)⁻¹ = 2 * 16⁻¹ := by
        field_simp
        norm_num
      have hMsub : ‖(x ^ 2 + x * t.X (-1) + t.X (-1) ^ 2 + t.a₄ - t.Y (-1)) - 16⁻¹‖
          < 1 := by
        have e : (x ^ 2 + x * t.X (-1) + t.X (-1) ^ 2 + t.a₄ - t.Y (-1)) - 16⁻¹
            = (x * x - 16⁻¹) + ((x * t.X (-1) - 16⁻¹) + ((t.X (-1) * t.X (-1) - 16⁻¹)
              + (t.a₄ + (-(t.Y (-1) - 8⁻¹) + (-16⁻¹ + 8⁻¹ - 16⁻¹))))) := by
          linear_combination (-2 : K) * h816'
        rw [e]
        have h816 : (-16⁻¹ + 8⁻¹ - 16⁻¹ : K) = 0 := by
          linear_combination h816'
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 ?_)
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2' ?_)
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h3 ?_)
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
          (max_lt (t.norm_a₄_le.trans_lt hq1) ?_)
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
        · rw [norm_neg]; exact hYneg.trans_lt hq1
        · rw [h816, norm_zero]; linarith
      have e : x ^ 2 + x * t.X (-1) + t.X (-1) ^ 2 + t.a₄ - t.Y (-1)
          = (16⁻¹ : K) + ((x ^ 2 + x * t.X (-1) + t.X (-1) ^ 2 + t.a₄ - t.Y (-1))
            - 16⁻¹) := by ring
      rw [e, norm_add_eq_left_of_norm_lt (by rw [h16]; exact hMsub), h16]
    -- the denominator `D = y + Y(-1) + x` is small and nonzero
    have hM0 : x ^ 2 + x * t.X (-1) + t.X (-1) ^ 2 + t.a₄ - t.Y (-1) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hM
      linarith
    have hD : ‖y + t.Y (-1) + x‖ < 1 := by
      have e : y + t.Y (-1) + x = (2 * y + x) + ((t.Y (-1) - 8⁻¹) - (y - 8⁻¹)) := by
        ring
      rw [e]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h2yx ?_)
      exact lt_of_le_of_lt (norm_sub_le_max' _ _) (max_lt (hYneg.trans_lt hq1) hy8)
    have hD0 : y + t.Y (-1) + x ≠ 0 := by
      intro h
      rw [h, mul_zero] at hident
      exact absurd hident.symm
        (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hhit')) hM0)
    have hlam : 1 < ‖(y - t.Y (-1)) / (x - t.X (-1))‖ := by
      have heq : (y - t.Y (-1)) / (x - t.X (-1))
          = (x ^ 2 + x * t.X (-1) + t.X (-1) ^ 2 + t.a₄ - t.Y (-1))
            / (y + t.Y (-1) + x) := by
        rw [div_eq_div_iff (sub_ne_zero.mpr (Ne.symm hhit')) hD0]
        linear_combination hident
      rw [heq, norm_div, hM, one_div]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hD0)).mpr hD
    exact t.mem_range_of_slope_norm_gt hmem h12 hneg1mem hns (Ne.symm hhit') hx.le
      hXneg1 hlam

end TateParameter

end TateCurvesTheta
