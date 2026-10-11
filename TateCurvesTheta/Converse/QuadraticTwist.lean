/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TateCurvesTheta.Converse.WeierstrassIso

/-!
# Quadratic twists of Weierstrass curves

For a Weierstrass curve `W` and `d` in a commutative ring, the **quadratic twist** of `W` by `d` is
`W^d : y² = x³ + d b₂ x² + 8 d² b₄ x + 16 d³ b₆`. Over a field with `2 ≠ 0`, `W` is isomorphic to
`y² = 4x³ + b₂x² + 2b₄x + b₆`, and `W^d` is (up to the scaling `x ↦ 4x`, `y ↦ 8y`) the curve
`d y² = 4x³ + b₂x² + 2b₄x + b₆`, i.e. the twist of `W` by the quadratic character of
`F(√d)/F`. The formula is polynomial, so it is defined over any commutative ring and has

`b₂(W^d) = 4 d b₂`, `b₄(W^d) = 16 d² b₄`, `b₆(W^d) = 64 d³ b₆`,
`c₄(W^d) = 2⁴ d² c₄`, `c₆(W^d) = 2⁶ d³ c₆`, `Δ(W^d) = 2¹² d⁶ Δ`,

so `j(W^d) = j(W)` and `γ(W^d) = γ(W) / (4d)` (`gammaInvariant_quadraticTwist`).

## Main results (over a field `F` with `2, 3 ≠ 0`)

* `isElliptic_quadraticTwist` : `W^d` is elliptic for `d ≠ 0`; `j_quadraticTwist`.
* `exists_variableChange_quadraticTwist_iff` : for `j(W) ≠ 0, 1728`, `W ≅ W^d` over `F` iff `d`
  is a square; more generally `exists_variableChange_quadraticTwist_iff'`:
  `W' ≅ W^d` iff `d · γ(W) γ(W')` is a square, for `W'` with `j(W') = j(W)`.
* `exists_variableChange_quadraticTwist_gammaInvariant` : every curve `W'` with `j(W') = j(W)`
  is isomorphic over `F` to the twist of `W` by `γ(W) γ(W')`.
-/

namespace TateCurvesTheta

open WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R]

/-- The **quadratic twist** `y² = x³ + d b₂ x² + 8 d² b₄ x + 16 d³ b₆` of `W` by `d`. -/
def quadraticTwist (W : WeierstrassCurve R) (d : R) : WeierstrassCurve R :=
  ⟨0, d * W.b₂, 0, 8 * d ^ 2 * W.b₄, 16 * d ^ 3 * W.b₆⟩

variable (W : WeierstrassCurve R) (d : R)

@[simp] lemma quadraticTwist_a₁ : (quadraticTwist W d).a₁ = 0 := rfl
@[simp] lemma quadraticTwist_a₂ : (quadraticTwist W d).a₂ = d * W.b₂ := rfl
@[simp] lemma quadraticTwist_a₃ : (quadraticTwist W d).a₃ = 0 := rfl
@[simp] lemma quadraticTwist_a₄ : (quadraticTwist W d).a₄ = 8 * d ^ 2 * W.b₄ := rfl
@[simp] lemma quadraticTwist_a₆ : (quadraticTwist W d).a₆ = 16 * d ^ 3 * W.b₆ := rfl

lemma quadraticTwist_b₂ : (quadraticTwist W d).b₂ = 4 * d * W.b₂ := by
  simp only [b₂, quadraticTwist]
  ring

lemma quadraticTwist_b₄ : (quadraticTwist W d).b₄ = 16 * d ^ 2 * W.b₄ := by
  simp only [b₄, quadraticTwist]
  ring

lemma quadraticTwist_b₆ : (quadraticTwist W d).b₆ = 64 * d ^ 3 * W.b₆ := by
  simp only [b₆, quadraticTwist]
  ring

lemma quadraticTwist_c₄ : (quadraticTwist W d).c₄ = 2 ^ 4 * d ^ 2 * W.c₄ := by
  rw [c₄, c₄, quadraticTwist_b₂, quadraticTwist_b₄]
  ring

lemma quadraticTwist_c₆ : (quadraticTwist W d).c₆ = 2 ^ 6 * d ^ 3 * W.c₆ := by
  rw [c₆, c₆, quadraticTwist_b₂, quadraticTwist_b₄, quadraticTwist_b₆]
  ring

lemma quadraticTwist_Δ : (quadraticTwist W d).Δ = 2 ^ 12 * d ^ 6 * W.Δ := by
  have hb₈ : (quadraticTwist W d).b₈ = 64 * d ^ 4 * (W.b₂ * W.b₆ - W.b₄ ^ 2) := by
    simp only [b₈, quadraticTwist, b₂, b₄, b₆]
    ring
  rw [Δ, Δ, hb₈, quadraticTwist_b₂, quadraticTwist_b₄, quadraticTwist_b₆]
  linear_combination (1024 * d ^ 6 * W.b₂ ^ 2) * W.b_relation

/-- The twist commutes with base change. -/
lemma map_quadraticTwist {S : Type*} [CommRing S] (f : R →+* S) :
    (quadraticTwist W d).map f = quadraticTwist (W.map f) (f d) := by
  ext <;> simp [quadraticTwist, map_b₂, map_b₄, map_b₆, map_ofNat f]

end CommRing

variable {F : Type*} [Field F]

/-- `γ(W^d) = γ(W) / (4d)`. -/
lemma gammaInvariant_quadraticTwist (W : WeierstrassCurve F) {d : F} (hd : d ≠ 0)
    (h2 : (2 : F) ≠ 0) : gammaInvariant (quadraticTwist W d) = gammaInvariant W / (4 * d) := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  rw [gammaInvariant, gammaInvariant, quadraticTwist_c₄, quadraticTwist_c₆]
  by_cases h6 : W.c₆ = 0
  · simp [h6]
  · field_simp
    ring

/-- The twist of an elliptic curve by `d ≠ 0` is elliptic (`2 ≠ 0`). -/
lemma isElliptic_quadraticTwist (W : WeierstrassCurve F) [W.IsElliptic] {d : F} (hd : d ≠ 0)
    (h2 : (2 : F) ≠ 0) : (quadraticTwist W d).IsElliptic := by
  constructor
  rw [quadraticTwist_Δ, isUnit_iff_ne_zero]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ hd)) (Δ_ne_zero W)

/-- `j(W) = c₄³ / Δ`. -/
lemma j_eq_div (W : WeierstrassCurve F) [W.IsElliptic] : W.j = W.c₄ ^ 3 / W.Δ := by
  rw [j, Units.val_inv_eq_inv_val, coe_Δ', div_eq_mul_inv, mul_comm]

/-- The twist has the same `j`-invariant. -/
lemma j_quadraticTwist (W : WeierstrassCurve F) [W.IsElliptic] {d : F} (hd : d ≠ 0)
    (h2 : (2 : F) ≠ 0) [(quadraticTwist W d).IsElliptic] : (quadraticTwist W d).j = W.j := by
  rw [j_eq_div, j_eq_div, quadraticTwist_c₄, quadraticTwist_Δ]
  have := Δ_ne_zero W
  field_simp

section Iso

variable (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (W W' : WeierstrassCurve F) [W.IsElliptic]
  [W'.IsElliptic]
include h2 h3

/-- **Isomorphism with a twist**: for `j(W') = j(W) ≠ 0, 1728` and `d ≠ 0`, `W'` is isomorphic
over `F` to the twist `W^d` iff `d · γ(W) · γ(W')` is a square. -/
theorem exists_variableChange_quadraticTwist_iff' (hj0 : W.j ≠ 0) (hj1728 : W.j ≠ 1728)
    (hj : W'.j = W.j) {d : F} (hd : d ≠ 0) :
    (∃ C : VariableChange F, C • W' = quadraticTwist W d) ↔
      IsSquare (d * gammaInvariant W * gammaInvariant W') := by
  haveI := isElliptic_quadraticTwist W hd h2
  have hγ := gammaInvariant_ne_zero W hj0 hj1728
  have hγ' := gammaInvariant_ne_zero W' (hj ▸ hj0) (hj ▸ hj1728)
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  rw [exists_variableChange_iff_isSquare h2 h3 W' _ (hj ▸ hj0) (hj ▸ hj1728)
    (hj.trans (j_quadraticTwist W hd h2).symm), gammaInvariant_quadraticTwist W hd h2]
  have key : gammaInvariant W / (4 * d) / gammaInvariant W' =
      (d * gammaInvariant W * gammaInvariant W') / (2 * d * gammaInvariant W') ^ 2 := by
    field_simp
    ring
  rw [key]
  constructor
  · intro h
    have := h.mul (IsSquare.sq (2 * d * gammaInvariant W'))
    rwa [div_mul_cancel₀ _ (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero h2 hd) hγ'))] at this
  · exact fun h => h.div (IsSquare.sq _)

/-- **A curve is isomorphic to its twist by `d` iff `d` is a square** (`j ≠ 0, 1728`). -/
theorem exists_variableChange_quadraticTwist_iff (hj0 : W.j ≠ 0) (hj1728 : W.j ≠ 1728)
    {d : F} (hd : d ≠ 0) :
    (∃ C : VariableChange F, C • W = quadraticTwist W d) ↔ IsSquare d := by
  rw [exists_variableChange_quadraticTwist_iff' h2 h3 W W hj0 hj1728 rfl hd, mul_assoc,
    ← sq]
  have hγ := gammaInvariant_ne_zero W hj0 hj1728
  constructor
  · intro h
    have := h.div (IsSquare.sq (gammaInvariant W))
    rwa [mul_div_cancel_right₀ _ (pow_ne_zero 2 hγ)] at this
  · exact fun h => h.mul (IsSquare.sq _)

/-- **Every curve with the same `j ≠ 0, 1728` is a twist**: `W'` is isomorphic over `F` to the
twist of `W` by `γ(W) γ(W')`. -/
theorem exists_variableChange_quadraticTwist_gammaInvariant (hj0 : W.j ≠ 0)
    (hj1728 : W.j ≠ 1728) (hj : W'.j = W.j) :
    ∃ C : VariableChange F, C • W' = quadraticTwist W (gammaInvariant W * gammaInvariant W') := by
  have hγ := gammaInvariant_ne_zero W hj0 hj1728
  have hγ' := gammaInvariant_ne_zero W' (hj ▸ hj0) (hj ▸ hj1728)
  rw [exists_variableChange_quadraticTwist_iff' h2 h3 W W' hj0 hj1728 hj (mul_ne_zero hγ hγ')]
  exact ⟨gammaInvariant W * gammaInvariant W', by ring⟩

end Iso

end TateCurvesTheta
