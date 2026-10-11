/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TateCurvesTheta.Converse.SplitIsTate

/-!
# Split multiplicative reduction via the tangent quadratic (residue characteristic `≠ 2`)

For a Weierstrass curve `W` with `‖c₄‖ = 1` and `‖Δ‖ < 1` (multiplicative reduction), the node of
the reduction has tangent directions given by the quadratic
`f(r) = c₄ r² + a₁ c₄ r - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`, whose discriminant is `-c₄c₆`:

`(2 c₄ r + a₁ c₄)² = -c₄c₆ + 4 c₄ f(r)` (`tangent_sq_eq`).

The reduction is *split* exactly when `f` has a root modulo the maximal ideal. In residue
characteristic `≠ 2` (`‖2‖ = 1`), Hensel's lemma shows that this happens iff `-c₄c₆`, equivalently
`γ(W) = -c₄/c₆`, is a square in `K` (`isSquare_gammaInvariant_iff_exists_tangent_root`). Combined
with `exists_variableChange_tateCurve_iff`, a curve with split multiplicative reduction is a Tate
curve (`exists_variableChange_tateCurve_of_tangent_root`); this is the statement used by
`lana-agents/iut` (`Iut.exists_variableChange_tateCurve`, same hypotheses).

The same equivalence holds in **every** residue characteristic, assuming only `2 ≠ 0` in `K`
(`isSquare_gammaInvariant_iff_exists_tangent_root'`): a root `r` of `f` modulo `𝔪` is
automatically simple, since `f'(r)² = -c₄c₆ + 4c₄f(r)` is a unit, and then
`-c₄c₆ = f'(r)² + 4·(-c₄ f(r))` is a square by Hensel's lemma in the form
`isSquare_sq_add_four_mul` (`‖s‖ = 1`, `‖e‖ < 1` ⇒ `s² + 4e` is a square), which only needs the
precision `‖4e/s²‖ < ‖4‖` of `exists_sq_eq_of_norm_sub_one_lt_norm_four`. The link with the
abstract split multiplicative reduction type is `TateCurvesTheta.Converse.ReductionType`.
-/

namespace TateCurvesTheta

open WeierstrassCurve

variable {K : Type*} [NormedField K]

/-- The tangent quadratic `c₄ r² + a₁ c₄ r - (54 b₆ - 3 b₂ b₄ + a₂ c₄)` at the node. -/
def tangentQuadratic (W : WeierstrassCurve K) (r : K) : K :=
  W.c₄ * r ^ 2 + W.a₁ * W.c₄ * r - (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)

/-- **The discriminant of the tangent quadratic is `-c₄c₆`**:
`(2 c₄ r + a₁ c₄)² = -c₄c₆ + 4 c₄ f(r)`. -/
lemma tangent_sq_eq (W : WeierstrassCurve K) (r : K) :
    (2 * W.c₄ * r + W.a₁ * W.c₄) ^ 2 = -(W.c₄ * W.c₆) + 4 * W.c₄ * tangentQuadratic W r := by
  simp only [tangentQuadratic, c₄, c₆, b₂, b₄, b₆]
  ring

/-- `γ(W)` is a square iff `-c₄c₆` is (for `c₆ ≠ 0`). -/
lemma isSquare_gammaInvariant_iff (W : WeierstrassCurve K) (hc₆ : W.c₆ ≠ 0) :
    IsSquare (gammaInvariant W) ↔ IsSquare (-(W.c₄ * W.c₆)) := by
  have hγ : gammaInvariant W = -(W.c₄ * W.c₆) / W.c₆ ^ 2 := by
    rw [gammaInvariant]
    field_simp
  have hγ' : -(W.c₄ * W.c₆) = gammaInvariant W * W.c₆ ^ 2 := by
    rw [hγ]
    field_simp
  constructor
  · intro h
    rw [hγ']
    exact h.mul (IsSquare.sq _)
  · intro h
    rw [hγ]
    exact h.div (IsSquare.sq _)

/-- A square root of `-c₄c₆` gives an exact root of the tangent quadratic (`2 c₄ ≠ 0`). -/
lemma exists_tangentQuadratic_eq_zero (W : WeierstrassCurve K) (h2 : (2 : K) ≠ 0)
    (hc₄ : W.c₄ ≠ 0) (hsq : IsSquare (-(W.c₄ * W.c₆))) : ∃ r : K, tangentQuadratic W r = 0 := by
  obtain ⟨s, hs⟩ := hsq
  refine ⟨(s - W.a₁ * W.c₄) / (2 * W.c₄), ?_⟩
  have h := tangent_sq_eq W ((s - W.a₁ * W.c₄) / (2 * W.c₄))
  have hs' : 2 * W.c₄ * ((s - W.a₁ * W.c₄) / (2 * W.c₄)) + W.a₁ * W.c₄ = s := by
    field_simp
    ring
  rw [hs', sq, hs] at h
  have h4 : (4 : K) * W.c₄ ≠ 0 :=
    mul_ne_zero (by rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2) hc₄
  exact (mul_eq_zero.mp (by linear_combination -h : (4 : K) * W.c₄ * _ = 0)).resolve_left h4

variable [IsUltrametricDist K]

private lemma norm_ofNat_le_one' (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  rw [← Nat.cast_ofNat]
  exact IsUltrametricDist.norm_natCast_le_one K _

private lemma norm_add_eq_left {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

/-- `‖c₆‖ = 1` for a curve with `‖c₄‖ = 1`, `‖Δ‖ < 1`. -/
lemma norm_c₆_eq_one (W : WeierstrassCurve K) (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1) :
    ‖W.c₆‖ = 1 := by
  have h : W.c₆ ^ 2 = W.c₄ ^ 3 + -(1728 * W.Δ) := by linear_combination W.c_relation
  have hn : ‖W.c₆ ^ 2‖ = 1 := by
    rw [h, norm_add_eq_left, norm_pow, hc₄, one_pow]
    rw [norm_pow, hc₄, one_pow, norm_neg, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_ofNat_le_one' 1728) (norm_nonneg _) hΔ
  rw [norm_pow] at hn
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hn

omit [IsUltrametricDist K] in
/-- `‖j‖ > 1` for an elliptic curve with `‖c₄‖ = 1`, `‖Δ‖ < 1`. -/
lemma one_lt_norm_j (W : WeierstrassCurve K) [W.IsElliptic] (hc₄ : ‖W.c₄‖ = 1)
    (hΔ : ‖W.Δ‖ < 1) : 1 < ‖W.j‖ := by
  have hΔpos : 0 < ‖W.Δ‖ := norm_pos_iff.mpr (Δ_ne_zero W)
  rw [j, Units.val_inv_eq_inv_val, coe_Δ', norm_mul, norm_inv, norm_pow, hc₄, one_pow, mul_one]
  exact (one_lt_inv₀ hΔpos).mpr hΔ

variable [CompleteSpace K]

/-- **Split reduction gives a square `γ`** (`‖2‖ = 1`): if the tangent quadratic has a root
modulo the maximal ideal, then `-c₄c₆` and hence `γ(W)` are squares in `K`. -/
theorem isSquare_gammaInvariant_of_tangent_root (h2 : ‖(2 : K)‖ = 1) (W : WeierstrassCurve K)
    (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1) (hroot : ∃ r : K, ‖tangentQuadratic W r‖ < 1) :
    IsSquare (gammaInvariant W) := by
  obtain ⟨r, hr⟩ := hroot
  have hc₆ := norm_c₆_eq_one W hc₄ hΔ
  have hc₆0 : W.c₆ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc₆
    exact zero_ne_one hc₆
  rw [isSquare_gammaInvariant_iff W hc₆0]
  set s := 2 * W.c₄ * r + W.a₁ * W.c₄
  have hs2 := tangent_sq_eq W r
  have hε : ‖4 * W.c₄ * tangentQuadratic W r‖ < 1 := by
    rw [norm_mul, norm_mul, hc₄, mul_one]
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_ofNat_le_one' 4) (norm_nonneg _) hr
  have hD : ‖-(W.c₄ * W.c₆)‖ = 1 := by rw [norm_neg, norm_mul, hc₄, hc₆, one_mul]
  have hsn : ‖s‖ = 1 := by
    have : ‖s ^ 2‖ = 1 := by
      rw [hs2, norm_add_eq_left, hD]
      rw [hD]
      exact hε
    rw [norm_pow] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  have hlt : ‖s ^ 2 - -(W.c₄ * W.c₆)‖ < 1 := by
    rw [hs2, add_sub_cancel_left]
    exact hε
  obtain ⟨x, hx, -⟩ := exists_sq_eq_of_norm_sq_sub_lt h2 hsn hlt
  exact ⟨x, by rw [← hx, sq]⟩

/-- **Split multiplicative reduction ⟺ `γ(W)` is a square** (`‖2‖ = 1`, `‖c₄‖ = 1`,
`‖Δ‖ < 1`): the tangent quadratic at the node has a root modulo the maximal ideal iff `γ(W)` is
a square in `K` (and then it even has an exact root in `K`). -/
theorem isSquare_gammaInvariant_iff_exists_tangent_root (h2 : ‖(2 : K)‖ = 1)
    (W : WeierstrassCurve K) (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1) :
    IsSquare (gammaInvariant W) ↔ ∃ r : K, ‖tangentQuadratic W r‖ < 1 := by
  refine ⟨fun h => ?_, isSquare_gammaInvariant_of_tangent_root h2 W hc₄ hΔ⟩
  have hc₆ := norm_c₆_eq_one W hc₄ hΔ
  have hne : ∀ {x : K}, ‖x‖ = 1 → x ≠ 0 := fun hx h0 => by
    rw [h0, norm_zero] at hx
    exact zero_ne_one hx
  have h2' : (2 : K) ≠ 0 := hne h2
  rw [isSquare_gammaInvariant_iff W (hne hc₆)] at h
  obtain ⟨r, hr⟩ := exists_tangentQuadratic_eq_zero W h2' (hne hc₄) h
  exact ⟨r, by rw [hr, norm_zero]; exact zero_lt_one⟩

/-! ### Every residue characteristic -/

/-- **Hensel's lemma, unit-square form** (every residue characteristic, `2 ≠ 0`): if `‖s‖ = 1` and
`‖e‖ < 1`, then `s² + 4e` is a square. -/
theorem isSquare_sq_add_four_mul (h2 : (2 : K) ≠ 0) {s e : K} (hs : ‖s‖ = 1) (he : ‖e‖ < 1) :
    IsSquare (s ^ 2 + 4 * e) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, norm_zero] at hs
    exact zero_ne_one hs
  have h4pos : 0 < ‖(4 : K)‖ := by
    rw [norm_pos_iff, show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have ha : ‖(1 + 4 * e / s ^ 2) - 1‖ < ‖(4 : K)‖ := by
    rw [add_sub_cancel_left, norm_div, norm_mul, norm_pow, hs, one_pow, div_one]
    exact mul_lt_of_lt_one_right h4pos he
  obtain ⟨y, hy, -⟩ := exists_sq_eq_of_norm_sub_one_lt_norm_four ha
  refine ⟨s * y, ?_⟩
  rw [← sq, mul_pow, hy]
  field_simp

/-- **Split reduction gives a square `γ`, every residue characteristic** (`2 ≠ 0` in `K`): if
`‖c₄‖ = 1`, `‖Δ‖ < 1` and the tangent quadratic has a root modulo the maximal ideal, then `γ(W)`
is a square. The root is automatically simple: `f'(r)² = -c₄c₆ + 4c₄f(r)` is a unit. -/
theorem isSquare_gammaInvariant_of_tangent_root' (h2 : (2 : K) ≠ 0) (W : WeierstrassCurve K)
    (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1) (hroot : ∃ r : K, ‖tangentQuadratic W r‖ < 1) :
    IsSquare (gammaInvariant W) := by
  obtain ⟨r, hr⟩ := hroot
  have hc₆ := norm_c₆_eq_one W hc₄ hΔ
  have hc₆0 : W.c₆ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc₆
    exact zero_ne_one hc₆
  rw [isSquare_gammaInvariant_iff W hc₆0]
  set s := 2 * W.c₄ * r + W.a₁ * W.c₄
  have hs2 := tangent_sq_eq W r
  have hε : ‖4 * W.c₄ * tangentQuadratic W r‖ < 1 := by
    rw [norm_mul, norm_mul, hc₄, mul_one]
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_ofNat_le_one' 4) (norm_nonneg _) hr
  have hD : ‖-(W.c₄ * W.c₆)‖ = 1 := by rw [norm_neg, norm_mul, hc₄, hc₆, one_mul]
  have hsn : ‖s‖ = 1 := by
    have : ‖s ^ 2‖ = 1 := by
      rw [hs2, norm_add_eq_left, hD]
      rw [hD]
      exact hε
    rw [norm_pow] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this
  have he : ‖-(W.c₄ * tangentQuadratic W r)‖ < 1 := by
    rw [norm_neg, norm_mul, hc₄, one_mul]
    exact hr
  have := isSquare_sq_add_four_mul h2 hsn he
  rwa [hs2, show -(W.c₄ * W.c₆) + 4 * W.c₄ * tangentQuadratic W r +
    4 * -(W.c₄ * tangentQuadratic W r) = -(W.c₄ * W.c₆) by ring] at this

/-- **The tangent criterion in every residue characteristic** (`2 ≠ 0` in `K`, `‖c₄‖ = 1`,
`‖Δ‖ < 1`): `γ(W)` is a square in `K` iff the tangent quadratic has a root modulo the maximal
ideal (and then it has an exact root in `K`). -/
theorem isSquare_gammaInvariant_iff_exists_tangent_root' (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) (hc₄ : ‖W.c₄‖ = 1) (hΔ : ‖W.Δ‖ < 1) :
    IsSquare (gammaInvariant W) ↔ ∃ r : K, ‖tangentQuadratic W r‖ < 1 := by
  refine ⟨fun h => ?_, isSquare_gammaInvariant_of_tangent_root' h2 W hc₄ hΔ⟩
  have hc₆ := norm_c₆_eq_one W hc₄ hΔ
  have hne : ∀ {x : K}, ‖x‖ = 1 → x ≠ 0 := fun hx h0 => by
    rw [h0, norm_zero] at hx
    exact zero_ne_one hx
  rw [isSquare_gammaInvariant_iff W (hne hc₆)] at h
  obtain ⟨r, hr⟩ := exists_tangentQuadratic_eq_zero W h2 (hne hc₄) h
  exact ⟨r, by rw [hr, norm_zero]; exact zero_lt_one⟩

/-- **Tate's theorem, split-reduction form** (`‖2‖ = 1`, `12 ≠ 0`): an elliptic curve with
`‖c₄‖ = 1`, `‖Δ‖ < 1` whose tangent quadratic at the node has a root modulo the maximal ideal
is isomorphic over `K` to the Tate curve `E_q` with `j(E_q) = j(W)`. This is the library form of
`Iut.exists_variableChange_tateCurve` (same hypotheses and conclusion). -/
theorem exists_variableChange_tateCurve_of_tangent_root (h2 : ‖(2 : K)‖ = 1)
    (h12 : (12 : K) ≠ 0) (W : WeierstrassCurve K) [W.IsElliptic] (hc₄ : ‖W.c₄‖ = 1)
    (hΔ : ‖W.Δ‖ < 1) (hroot : ∃ r : K, ‖tangentQuadratic W r‖ < 1) :
    ∃ (t : TateParameter K) (C : VariableChange K), C • W = t.tateCurve ∧ t.tateJ = W.j := by
  have hj := one_lt_norm_j W hc₄ hΔ
  obtain ⟨C, hC⟩ := exists_variableChange_tateCurve h12 W hj
    (isSquare_gammaInvariant_of_tangent_root h2 W hc₄ hΔ hroot)
  exact ⟨_, C, hC, TateParameter.ofJ_tateJ h12 hj⟩

end TateCurvesTheta
