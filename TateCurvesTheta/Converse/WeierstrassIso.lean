/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Isomorphisms of Weierstrass curves with `j ≠ 0, 1728`

Over a field `F` with `2 ≠ 0` and `3 ≠ 0`, two elliptic Weierstrass curves `W, W'` with the
same `j`-invariant `j ≠ 0, 1728` are isomorphic by a change of variables over `F` if and only if
the quotient `γ(W') / γ(W)` of their **twist invariants** `γ(W) = -c₄(W) / c₆(W)` is a square in
`F` (Silverman, *Advanced Topics*, proof of V.5.3; *AEC* III.1.4 and X.5.4); in that case the
change of variables is unique up to the automorphism group `{1, -1}` of `W'`.

## Main results

* `TateCurvesTheta.gammaInvariant` : `γ(W) = -c₄ / c₆`, and `gammaInvariant_variableChange`:
  `γ(C • W) = u(C)² · γ(W)`.
* `TateCurvesTheta.c₄_ne_zero_of_j_ne_zero`, `c₆_ne_zero_of_j_ne_1728`.
* `TateCurvesTheta.exists_variableChange_of_c₄_c₆` : `c₄ = u⁴ c₄'`, `c₆ = u⁶ c₆'` give a change of
  variables `C • W = W'`.
* `TateCurvesTheta.exists_variableChange_iff_isSquare` : for equal `j ≠ 0, 1728`,
  `(∃ C, C • W = W') ↔ IsSquare (γ(W') / γ(W))`.
* `TateCurvesTheta.negChange`, `negChange_smul` : the negation `(u, r, s, t) = (-1, 0, -a₁, -a₃)`
  is an automorphism of `W`.
* `TateCurvesTheta.eq_one_or_eq_negChange` : for `c₄ c₆ ≠ 0` the only automorphisms of `W` are
  `1` and `negChange W`; hence `smul_eq_iff_of_smul_eq`: any two isomorphisms `W ≅ W'` agree up
  to the sign `negChange W'`.
-/

namespace TateCurvesTheta

open WeierstrassCurve

variable {F : Type*} [Field F]

/-- The **twist invariant** `γ(W) = -c₄(W) / c₆(W)` of a Weierstrass curve (Silverman,
*Advanced Topics*, V.5): for `j ≠ 0, 1728` its class in `Fˣ / Fˣ²` classifies the quadratic twists
with the given `j`-invariant. -/
noncomputable def gammaInvariant (W : WeierstrassCurve F) : F := -W.c₄ / W.c₆

lemma gammaInvariant_def (W : WeierstrassCurve F) : gammaInvariant W = -W.c₄ / W.c₆ := rfl

/-- `γ(C • W) = u² γ(W)`. -/
lemma gammaInvariant_variableChange (W : WeierstrassCurve F) (C : VariableChange F) :
    gammaInvariant (C • W) = (C.u : F) ^ 2 * gammaInvariant W := by
  have hu := C.u.ne_zero
  rw [gammaInvariant, gammaInvariant, variableChange_c₄, variableChange_c₆,
    Units.val_inv_eq_inv_val]
  by_cases h6 : W.c₆ = 0
  · simp [h6]
  · field_simp

section JInvariant

variable (W : WeierstrassCurve F) [W.IsElliptic]

/-- `c₄³ = j Δ`. -/
lemma c₄_pow_three_eq : W.c₄ ^ 3 = W.j * W.Δ := by
  rw [j, ← coe_Δ', mul_comm, ← mul_assoc, Units.mul_inv, one_mul]

/-- `c₆² = (j - 1728) Δ`. -/
lemma c₆_sq_eq : W.c₆ ^ 2 = (W.j - 1728) * W.Δ := by
  linear_combination (c₄_pow_three_eq W) + W.c_relation

lemma Δ_ne_zero : W.Δ ≠ 0 := by
  rw [← coe_Δ']
  exact W.Δ'.ne_zero

lemma c₄_ne_zero_of_j_ne_zero (hj : W.j ≠ 0) : W.c₄ ≠ 0 := fun h => hj (W.j_eq_zero h)

lemma c₆_ne_zero_of_j_ne_1728 (hj : W.j ≠ 1728) : W.c₆ ≠ 0 := by
  intro h
  have := (c₆_sq_eq W)
  rw [h, zero_pow two_ne_zero, eq_comm, mul_eq_zero, sub_eq_zero] at this
  exact this.elim hj (Δ_ne_zero W)

lemma gammaInvariant_ne_zero (hj0 : W.j ≠ 0) (hj1728 : W.j ≠ 1728) : gammaInvariant W ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr ((c₄_ne_zero_of_j_ne_zero W) hj0))
    ((c₆_ne_zero_of_j_ne_1728 W) hj1728)

end JInvariant

section ShortNF

/-- The scaling change of variables `(u, 0, 0, 0)`. -/
def scaleChange (u : Fˣ) : VariableChange F := ⟨u, 0, 0, 0⟩

instance scaleChange_isShortNF (u : Fˣ) (W : WeierstrassCurve F) [W.IsShortNF] :
    (scaleChange u • W).IsShortNF := by
  constructor <;>
    simp [scaleChange, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      a₂_of_isShortNF]

/-- A short normal form is determined by `c₄` and `c₆` when `2, 3 ≠ 0`. -/
lemma eq_of_isShortNF (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (W W' : WeierstrassCurve F)
    [W.IsShortNF] [W'.IsShortNF] (h4 : W.c₄ = W'.c₄) (h6 : W.c₆ = W'.c₆) : W = W' := by
  have h48 : (48 : F) ≠ 0 := by
    rw [show (48 : F) = 2 ^ 4 * 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) h3
  have h864 : (864 : F) ≠ 0 := by
    rw [show (864 : F) = 2 ^ 5 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  rw [c₄_of_isShortNF, c₄_of_isShortNF] at h4
  rw [c₆_of_isShortNF, c₆_of_isShortNF] at h6
  ext
  · rw [a₁_of_isShortNF, a₁_of_isShortNF]
  · rw [a₂_of_isShortNF, a₂_of_isShortNF]
  · rw [a₃_of_isShortNF, a₃_of_isShortNF]
  · exact mul_left_cancel₀ (neg_ne_zero.mpr h48) h4
  · exact mul_left_cancel₀ (neg_ne_zero.mpr h864) h6

/-- **Isomorphism from the `c`-invariants.** If `c₄(W) = u⁴ c₄(W')` and `c₆(W) = u⁶ c₆(W')`, then
some change of variables (with scaling factor `u`) carries `W` to `W'` (`2, 3 ≠ 0`). -/
theorem exists_variableChange_of_c₄_c₆ (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (W W' : WeierstrassCurve F) (u : Fˣ) (h4 : W.c₄ = (u : F) ^ 4 * W'.c₄)
    (h6 : W.c₆ = (u : F) ^ 6 * W'.c₆) : ∃ C : VariableChange F, C • W = W' := by
  letI := invertibleOfNonzero h2
  letI := invertibleOfNonzero h3
  obtain ⟨C₁, hC₁⟩ := W.exists_variableChange_isShortNF
  obtain ⟨C₂, hC₂⟩ := W'.exists_variableChange_isShortNF
  set v : Fˣ := u * C₂.u * C₁.u⁻¹ with hv
  have key : scaleChange v • C₁ • W = C₂ • W' := by
    have h₁ := C₁.u.ne_zero
    have h₂ := C₂.u.ne_zero
    have hu := u.ne_zero
    refine eq_of_isShortNF h2 h3 _ _ ?_ ?_
    · rw [variableChange_c₄, variableChange_c₄, variableChange_c₄, h4]
      simp only [scaleChange, hv, Units.val_inv_eq_inv_val, Units.val_mul]
      field_simp
    · rw [variableChange_c₆, variableChange_c₆, variableChange_c₆, h6]
      simp only [scaleChange, hv, Units.val_inv_eq_inv_val, Units.val_mul]
      field_simp
  refine ⟨C₂⁻¹ * (scaleChange v * C₁), ?_⟩
  rw [mul_smul, mul_smul, key, inv_smul_smul]

end ShortNF

section IsSquare

variable (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (W W' : WeierstrassCurve F)
  [W.IsElliptic] [W'.IsElliptic]
include h2 h3

/-- **Curves with equal `j ≠ 0, 1728` are isomorphic iff `γ(W')/γ(W)` is a square** (`2, 3 ≠ 0`).
-/
theorem exists_variableChange_iff_isSquare (hj0 : W.j ≠ 0) (hj1728 : W.j ≠ 1728)
    (hj : W.j = W'.j) :
    (∃ C : VariableChange F, C • W = W') ↔ IsSquare (gammaInvariant W' / gammaInvariant W) := by
  have hγ := (gammaInvariant_ne_zero W) hj0 hj1728
  constructor
  · rintro ⟨C, rfl⟩
    refine ⟨C.u, ?_⟩
    rw [gammaInvariant_variableChange, mul_div_assoc, div_self hγ, mul_one, sq]
  · rintro ⟨μ, hμ⟩
    have hc₄ := (c₄_ne_zero_of_j_ne_zero W) hj0
    have hc₆ := (c₆_ne_zero_of_j_ne_1728 W) hj1728
    have hc₄' := (c₄_ne_zero_of_j_ne_zero W') (hj ▸ hj0)
    have hc₆' := (c₆_ne_zero_of_j_ne_1728 W') (hj ▸ hj1728)
    -- `c₄³ c₆'² = c₄'³ c₆²`
    have E2 : W.c₄ ^ 3 * W'.c₆ ^ 2 = W'.c₄ ^ 3 * W.c₆ ^ 2 := by
      rw [(c₄_pow_three_eq W), (c₆_sq_eq W'), (c₄_pow_three_eq W'), (c₆_sq_eq W), hj]
      ring
    -- `c₄' c₆ = μ² c₆' c₄`
    have E1 : W'.c₄ * W.c₆ = μ ^ 2 * (W'.c₆ * W.c₄) := by
      rw [gammaInvariant, gammaInvariant, div_div_div_eq,
        div_eq_iff (mul_ne_zero hc₆' (neg_ne_zero.mpr hc₄))] at hμ
      linear_combination -hμ
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero, zero_mul] at E1
      exact mul_ne_zero hc₄' hc₆ E1
    refine exists_variableChange_of_c₄_c₆ h2 h3 W W' (Units.mk0 μ hμ0) ?_ ?_
    · rw [Units.val_mk0]
      apply mul_left_cancel₀ (pow_ne_zero 2 (mul_ne_zero hc₆' hc₄))
      linear_combination E2 + W'.c₄ * (μ ^ 2 * W'.c₆ * W.c₄ + W'.c₄ * W.c₆) * E1
    · rw [Units.val_mk0]
      apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hc₆') (pow_ne_zero 3 hc₄))
      linear_combination W.c₆ * E2 + ((W'.c₄ * W.c₆) ^ 2 + W'.c₄ * W.c₆ * (μ ^ 2 * (W'.c₆ * W.c₄))
        + (μ ^ 2 * (W'.c₆ * W.c₄)) ^ 2) * E1

end IsSquare

section Automorphism

/-- The **negation** change of variables `(u, r, s, t) = (-1, 0, -a₁, -a₃)` of `W`; on points it
is `(x, y) ↦ (x, -y - a₁ x - a₃)`, i.e. `P ↦ -P`. -/
def negChange (W : WeierstrassCurve F) : VariableChange F := ⟨-1, 0, -W.a₁, -W.a₃⟩

@[simp] lemma negChange_u (W : WeierstrassCurve F) : (negChange W).u = -1 := rfl
@[simp] lemma negChange_r (W : WeierstrassCurve F) : (negChange W).r = 0 := rfl
@[simp] lemma negChange_s (W : WeierstrassCurve F) : (negChange W).s = -W.a₁ := rfl
@[simp] lemma negChange_t (W : WeierstrassCurve F) : (negChange W).t = -W.a₃ := rfl

/-- The negation is an automorphism of `W`. -/
lemma negChange_smul (W : WeierstrassCurve F) : negChange W • W = W := by
  ext
  · rw [variableChange_a₁]; simp; ring
  · rw [variableChange_a₂]; simp; ring
  · rw [variableChange_a₃]; simp; ring
  · rw [variableChange_a₄]; simp; ring
  · rw [variableChange_a₆]; simp; ring

lemma negChange_ne_one (h2 : (2 : F) ≠ 0) (W : WeierstrassCurve F) : negChange W ≠ 1 := by
  intro h
  have := congrArg (fun C : VariableChange F => (C.u : F)) h
  simp only [negChange_u, VariableChange.one_def, Units.val_neg, Units.val_one] at this
  apply h2
  linear_combination -this

/-- **The automorphisms of a curve with `c₄ c₆ ≠ 0`** (i.e. `j ≠ 0, 1728`) are `1` and the
negation (`2, 3 ≠ 0`). -/
theorem eq_one_or_eq_negChange (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (W : WeierstrassCurve F)
    (hc₄ : W.c₄ ≠ 0) (hc₆ : W.c₆ ≠ 0) {D : VariableChange F} (hD : D • W = W) :
    D = 1 ∨ D = negChange W := by
  have hu0 := D.u.ne_zero
  have e4 := variableChange_c₄ W D
  have e6 := variableChange_c₆ W D
  have e1 := variableChange_a₁ W D
  have e2 := variableChange_a₂ W D
  have e3 := variableChange_a₃ W D
  rw [hD, Units.val_inv_eq_inv_val] at e1 e2 e3 e4 e6
  have hu4 : (D.u : F) ^ 4 = 1 := by
    rw [inv_pow, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero 4 hu0)] at e4
    exact mul_left_cancel₀ hc₄ (by linear_combination e4)
  have hu6 : (D.u : F) ^ 6 = 1 := by
    rw [inv_pow, eq_inv_mul_iff_mul_eq₀ (pow_ne_zero 6 hu0)] at e6
    exact mul_left_cancel₀ hc₆ (by linear_combination e6)
  have hu2 : (D.u : F) * (D.u : F) = 1 := by linear_combination hu6 - (D.u : F) ^ 2 * hu4
  field_simp at e1 e2 e3
  rcases mul_self_eq_one_iff.mp hu2 with hu | hu
  · have hs : D.s = 0 := by
      rw [hu] at e1
      exact (mul_eq_zero.mp (by linear_combination -e1 : (2 : F) * D.s = 0)).resolve_left h2
    have hr : D.r = 0 := by
      rw [hu, hs] at e2
      exact (mul_eq_zero.mp (by linear_combination -e2 : (3 : F) * D.r = 0)).resolve_left h3
    have ht : D.t = 0 := by
      rw [hu, hr] at e3
      exact (mul_eq_zero.mp (by linear_combination -e3 : (2 : F) * D.t = 0)).resolve_left h2
    left
    ext
    · rw [hu]; rfl
    · rw [hr]; rfl
    · rw [hs]; rfl
    · rw [ht]; rfl
  · have hs : D.s = -W.a₁ := by
      rw [hu] at e1
      have : (2 : F) * (D.s + W.a₁) = 0 := by linear_combination -e1
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_left h2)
    have hr : D.r = 0 := by
      rw [hu, hs] at e2
      exact (mul_eq_zero.mp (by linear_combination -e2 : (3 : F) * D.r = 0)).resolve_left h3
    have ht : D.t = -W.a₃ := by
      rw [hu, hr] at e3
      have : (2 : F) * (D.t + W.a₃) = 0 := by linear_combination -e3
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_left h2)
    right
    ext
    · rw [hu]; rfl
    · rw [hr]; rfl
    · rw [hs]; rfl
    · rw [ht]; rfl

/-- **Isomorphisms are unique up to sign**: if `C • W = W'` and `c₄ c₆(W') ≠ 0`, then
`C' • W = W'` exactly for `C' = C` and `C' = negChange W' * C`. -/
theorem smul_eq_iff_of_smul_eq (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {W W' : WeierstrassCurve F} (hc₄ : W'.c₄ ≠ 0) (hc₆ : W'.c₆ ≠ 0) {C : VariableChange F}
    (hC : C • W = W') (C' : VariableChange F) :
    C' • W = W' ↔ C' = C ∨ C' = negChange W' * C := by
  constructor
  · intro hC'
    have hD : (C' * C⁻¹) • W' = W' := by
      rw [mul_smul, ← hC, inv_smul_smul, hC', hC]
    rcases eq_one_or_eq_negChange h2 h3 W' hc₄ hc₆ hD with h | h
    · left
      rw [← mul_inv_eq_one, h]
    · right
      rw [← h, inv_mul_cancel_right]
  · rintro (rfl | rfl)
    · exact hC
    · rw [mul_smul, hC, negChange_smul]

end Automorphism

end TateCurvesTheta
