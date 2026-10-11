/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TateCurvesTheta.Analysis.UltrametricSqrt
import TateCurvesTheta.Converse.WeierstrassIso
import TateCurvesTheta.QParameter.OfJ
import TateCurvesTheta.TateCurve.IntegralModel

/-!
# Curves with split multiplicative reduction are Tate curves (Silverman V.5.3)

Let `K` be a complete ultrametric field with `(12 : K) ≠ 0` (e.g. any complete nonarchimedean
field of characteristic `0`, in **every** residue characteristic), and let `W` be an elliptic
curve over `K` with non-integral `j`-invariant `‖j(W)‖ > 1`. Let `q = ofJ j(W)` be the unique Tate
parameter with `j(E_q) = j(W)`. Then (Silverman, *Advanced Topics*, Theorem V.5.3):

* `W` is `K`-isomorphic to `E_q` (by a change of Weierstrass variables) **iff** the twist
  invariant `γ(W) = -c₄(W)/c₆(W)` is a square in `K`
  (`exists_variableChange_tateCurve_iff`);
* more intrinsically, `W` is isomorphic to *some* Tate curve iff `‖j(W)‖ > 1` and `γ(W)` is a
  square (`exists_tateParameter_variableChange_iff`);
* the Tate parameter is unique (`eq_ofJ_of_smul_eq_tateCurve`, and `existsUnique_tateParameter`
  in the packaged form), and the isomorphism `W ≅ E_q` is unique up to the automorphism `-1` of
  `E_q`, which is the change of variables `(u, r, s, t) = (-1, 0, -1, 0)`
  (`smul_eq_tateCurve_iff`, `negChange_tateCurve`).

The only analytic input beyond the `q`-parameter is that `γ(E_q)` is a square
(`TateParameter.isSquare_gammaInvariant`): `-c₄c₆(E_q) = 1 + 8δ` with `‖δ‖ < 1`, so
`‖-c₄c₆(E_q) - 1‖ < ‖4‖` and Hensel's lemma for square roots
(`exists_sq_eq_of_norm_sub_one_lt_norm_four`) applies in every residue characteristic. The
algebraic input is the isomorphism criterion `exists_variableChange_iff_isSquare` for curves with
equal `j ≠ 0, 1728`.

The link with the reduction type in residue characteristic `≠ 2` (the tangent quadratic at the
node has a rational root) is `TateCurvesTheta.Converse.TangentCriterion`.

This ports and generalises `Iut.exists_variableChange_tateCurve` of `lana-agents/iut`
(`Iut/Cor312/ThetaData/TateIsomorphism.lean`), which assumed `‖2‖ = 1` and a model with
`‖c₄‖ = 1`, and `Iut.eq_one_or_negChange_of_smul_tateCurve` (`TateStructureUnique.lean`).
-/

namespace TateCurvesTheta

open WeierstrassCurve

variable {K : Type*} [NormedField K]

/-- Equal curves have equal `j`-invariants (for any choice of the `IsElliptic` instances). -/
lemma j_congr {W W' : WeierstrassCurve K} [W.IsElliptic] [W'.IsElliptic] (h : W = W') :
    W.j = W'.j := by
  subst h
  rfl

lemma two_ne_zero_of_twelve (h12 : (12 : K) ≠ 0) : (2 : K) ≠ 0 := by
  intro h
  apply h12
  rw [show (12 : K) = 2 * 6 by norm_num, h, zero_mul]

lemma three_ne_zero_of_twelve (h12 : (12 : K) ≠ 0) : (3 : K) ≠ 0 := by
  intro h
  apply h12
  rw [show (12 : K) = 3 * 4 by norm_num, h, zero_mul]

section Ultrametric

variable [IsUltrametricDist K]

private lemma norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : K)‖ ≤ 1 := by
  rw [← Nat.cast_ofNat]
  exact IsUltrametricDist.norm_natCast_le_one K _

/-- A non-integral `j`-invariant is neither `0` nor `1728`. -/
lemma ne_zero_and_ne_1728_of_one_lt_norm {j : K} (hj : 1 < ‖j‖) : j ≠ 0 ∧ j ≠ 1728 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, norm_zero] at hj
    linarith
  · rw [h] at hj
    exact (norm_ofNat_le_one 1728).not_gt hj

namespace TateParameter

variable (t : TateParameter K)

omit [IsUltrametricDist K] in
/-- `c₆(E_q) = -1 + 72 a₄ - 864 a₆`. -/
lemma tateCurve_c₆ : t.tateCurve.c₆ = -1 + 72 * t.a₄ - 864 * t.a₆ := by
  simp only [c₆, t.tateCurve_b₂, t.tateCurve_b₄, t.tateCurve_b₆]
  ring

omit [IsUltrametricDist K] in
/-- `-c₄c₆(E_q) = 1 + 8 δ` with `δ = a₄(-15 + 432 a₄ - 5184 a₆) + 108 a₆`. -/
lemma neg_c₄_mul_c₆_eq : -(t.tateCurve.c₄ * t.tateCurve.c₆) =
    1 + 8 * (t.a₄ * (-15 + 432 * t.a₄ - 5184 * t.a₆) + 108 * t.a₆) := by
  rw [t.tateCurve_c₄, tateCurve_c₆]
  ring

variable [CompleteSpace K]

/-- `‖c₆(E_q)‖ = 1`. -/
lemma norm_tateCurve_c₆ (h12 : (12 : K) ≠ 0) : ‖t.tateCurve.c₆‖ = 1 := by
  have h4 := t.norm_a₄_lt_one
  have h6 := t.norm_a₆_lt_one h12
  have hs : ‖72 * t.a₄ - 864 * t.a₆‖ < 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (norm_ofNat_le_one 72) (norm_nonneg _) h4
    · rw [norm_neg, norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (norm_ofNat_le_one 864) (norm_nonneg _) h6
  have : t.tateCurve.c₆ = -1 + (72 * t.a₄ - 864 * t.a₆) := by rw [tateCurve_c₆]; ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_neg, norm_one,
    max_eq_left hs.le]
  rw [norm_neg, norm_one]
  exact hs.ne'

/-- `‖-c₄c₆(E_q) - 1‖ < ‖4‖`: the hypothesis of Hensel's lemma for a square root of `-c₄c₆`. -/
lemma norm_neg_c₄_mul_c₆_sub_one_lt (h12 : (12 : K) ≠ 0) :
    ‖-(t.tateCurve.c₄ * t.tateCurve.c₆) - 1‖ < ‖(4 : K)‖ := by
  have h4 := t.norm_a₄_lt_one
  have h6 := t.norm_a₆_lt_one h12
  have h2 := two_ne_zero_of_twelve h12
  set δ := t.a₄ * (-15 + 432 * t.a₄ - 5184 * t.a₆) + 108 * t.a₆ with hδ
  have hδ1 : ‖δ‖ < 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      refine mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h4 ?_
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
        · rw [norm_neg]
          exact norm_ofNat_le_one 15
        · rw [norm_mul]
          exact mul_le_one₀ (norm_ofNat_le_one 432) (norm_nonneg _) h4.le
      · rw [norm_neg, norm_mul]
        exact mul_le_one₀ (norm_ofNat_le_one 5184) (norm_nonneg _) h6.le
    · rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (norm_ofNat_le_one 108) (norm_nonneg _) h6
  have h8 : ‖(8 : K)‖ = ‖(2 : K)‖ * ‖(4 : K)‖ := by
    rw [← norm_mul]
    norm_num
  have h2pos : 0 < ‖(2 : K)‖ := norm_pos_iff.mpr h2
  have h4pos : 0 < ‖(4 : K)‖ := by rw [norm_four_eq]; positivity
  rw [t.neg_c₄_mul_c₆_eq, add_sub_cancel_left, norm_mul, h8]
  calc ‖(2 : K)‖ * ‖(4 : K)‖ * ‖δ‖ ≤ 1 * ‖(4 : K)‖ * ‖δ‖ := by
        gcongr
        exact norm_two_le_one (K := K)
    _ < 1 * ‖(4 : K)‖ * 1 := by gcongr
    _ = ‖(4 : K)‖ := by ring

/-- **`γ(E_q)` is a square**, in every residue characteristic: `-c₄c₆(E_q)` is a square by
Hensel's lemma, and `γ = -c₄/c₆ = -c₄c₆ / c₆²`. -/
theorem isSquare_gammaInvariant (h12 : (12 : K) ≠ 0) : IsSquare (gammaInvariant t.tateCurve) := by
  obtain ⟨y, hy, -⟩ := exists_sq_eq_of_norm_sub_one_lt_norm_four
    (t.norm_neg_c₄_mul_c₆_sub_one_lt h12)
  have hc₆ : t.tateCurve.c₆ ≠ 0 := by
    intro h
    have := t.norm_tateCurve_c₆ h12
    rw [h, norm_zero] at this
    exact zero_ne_one this
  refine ⟨y / t.tateCurve.c₆, ?_⟩
  rw [gammaInvariant, ← sq, div_pow, hy]
  field_simp

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The negation automorphism of `E_q` is `(u, r, s, t) = (-1, 0, -1, 0)`. -/
lemma negChange_tateCurve : negChange t.tateCurve = ⟨-1, 0, -1, 0⟩ := by
  simp [negChange]

end TateParameter

/-! ## The converse theorem -/

variable [CompleteSpace K] (h12 : (12 : K) ≠ 0) (W : WeierstrassCurve K) [W.IsElliptic]
include h12

/-- If a change of variables carries `W` to `E_q`, then `j(E_q) = j(W)`. -/
lemma tateJ_eq_of_smul_eq_tateCurve {t : TateParameter K} {C : VariableChange K}
    (hC : C • W = t.tateCurve) : t.tateJ = W.j := by
  haveI := t.tateCurve_isElliptic h12
  rw [t.tateJ_eq_j h12, ← j_congr hC, variableChange_j]

/-- **Uniqueness of the Tate parameter**: if `W ≅ E_q`, then `q = ofJ j(W)`. -/
theorem eq_ofJ_of_smul_eq_tateCurve (hj : 1 < ‖W.j‖) {t : TateParameter K}
    {C : VariableChange K} (hC : C • W = t.tateCurve) : t = TateParameter.ofJ h12 hj :=
  TateParameter.eq_ofJ h12 hj (tateJ_eq_of_smul_eq_tateCurve h12 W hC)

/-- **Silverman V.5.3, `K`-rational form**: for `‖j(W)‖ > 1`, the curve `W` is isomorphic over
`K` to the Tate curve `E_q` of `q = ofJ j(W)` if and only if `γ(W) = -c₄/c₆` is a square in
`K`. -/
theorem exists_variableChange_tateCurve_iff (hj : 1 < ‖W.j‖) :
    (∃ C : VariableChange K, C • W = (TateParameter.ofJ h12 hj).tateCurve) ↔
      IsSquare (gammaInvariant W) := by
  set t := TateParameter.ofJ h12 hj
  haveI := t.tateCurve_isElliptic h12
  obtain ⟨hj0, hj1728⟩ := ne_zero_and_ne_1728_of_one_lt_norm hj
  have hjt : W.j = t.tateCurve.j := by
    rw [← t.tateJ_eq_j h12, TateParameter.ofJ_tateJ]
  rw [exists_variableChange_iff_isSquare (two_ne_zero_of_twelve h12)
    (three_ne_zero_of_twelve h12) W t.tateCurve hj0 hj1728 hjt]
  have hγ := gammaInvariant_ne_zero W hj0 hj1728
  have hγt := gammaInvariant_ne_zero t.tateCurve (hjt ▸ hj0) (hjt ▸ hj1728)
  have hsq := t.isSquare_gammaInvariant h12
  constructor
  · intro h
    have := hsq.div h
    rwa [div_div_cancel₀ hγt] at this
  · exact hsq.div

/-- **Silverman V.5.3, existence**: if `‖j(W)‖ > 1` and `γ(W)` is a square, then `W` is
isomorphic over `K` to the Tate curve of `q = ofJ j(W)`. -/
theorem exists_variableChange_tateCurve (hj : 1 < ‖W.j‖) (hγ : IsSquare (gammaInvariant W)) :
    ∃ C : VariableChange K, C • W = (TateParameter.ofJ h12 hj).tateCurve :=
  (exists_variableChange_tateCurve_iff h12 W hj).mpr hγ

/-- **Silverman V.5.3, intrinsic form**: `W` is isomorphic over `K` to some Tate curve if and
only if `‖j(W)‖ > 1` and `γ(W)` is a square in `K`. -/
theorem exists_tateParameter_variableChange_iff :
    (∃ (t : TateParameter K) (C : VariableChange K), C • W = t.tateCurve) ↔
      1 < ‖W.j‖ ∧ IsSquare (gammaInvariant W) := by
  constructor
  · rintro ⟨t, C, hC⟩
    refine ⟨tateJ_eq_of_smul_eq_tateCurve h12 W hC ▸ t.one_lt_norm_tateJ h12, ?_⟩
    have hγ := t.isSquare_gammaInvariant h12
    rw [← hC, gammaInvariant_variableChange] at hγ
    have hu := C.u.ne_zero
    have := hγ.div (IsSquare.sq (C.u : K))
    rwa [mul_div_cancel_left₀ _ (pow_ne_zero 2 hu)] at this
  · rintro ⟨hj, hγ⟩
    exact ⟨_, exists_variableChange_tateCurve h12 W hj hγ⟩

omit [W.IsElliptic] in
/-- **The isomorphism is unique up to sign**: if `C • W = E_q`, then the changes of variables
carrying `W` to `E_q` are exactly `C` and `negChange E_q * C`, where `negChange E_q` is the
automorphism `(-1, 0, -1, 0)` (`P ↦ -P`) of `E_q`. -/
theorem smul_eq_tateCurve_iff {t : TateParameter K} {C : VariableChange K}
    (hC : C • W = t.tateCurve) (C' : VariableChange K) :
    C' • W = t.tateCurve ↔ C' = C ∨ C' = negChange t.tateCurve * C := by
  haveI := t.tateCurve_isElliptic h12
  obtain ⟨hj0, hj1728⟩ := ne_zero_and_ne_1728_of_one_lt_norm
    (t.tateJ_eq_j h12 ▸ t.one_lt_norm_tateJ h12)
  exact smul_eq_iff_of_smul_eq (two_ne_zero_of_twelve h12) (three_ne_zero_of_twelve h12)
    (c₄_ne_zero_of_j_ne_zero _ hj0) (c₆_ne_zero_of_j_ne_1728 _ hj1728) hC C'

/-- **Silverman V.5.3, packaged**: if `‖j(W)‖ > 1` and `γ(W)` is a square, there is a *unique*
Tate parameter `q` with `W ≅ E_q` over `K` (namely `q = ofJ j(W)`), and the isomorphism is unique
up to the automorphism `-1` of `E_q`. -/
theorem existsUnique_tateParameter (hj : 1 < ‖W.j‖) (hγ : IsSquare (gammaInvariant W)) :
    ∃! t : TateParameter K, ∃ C : VariableChange K, C • W = t.tateCurve ∧
      ∀ C' : VariableChange K, C' • W = t.tateCurve ↔ C' = C ∨ C' = negChange t.tateCurve * C := by
  obtain ⟨C, hC⟩ := exists_variableChange_tateCurve h12 W hj hγ
  refine ⟨_, ⟨C, hC, smul_eq_tateCurve_iff h12 W hC⟩, ?_⟩
  rintro t ⟨C', hC', -⟩
  exact eq_ofJ_of_smul_eq_tateCurve h12 W hj hC'

end Ultrametric

end TateCurvesTheta
