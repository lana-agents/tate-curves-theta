/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot
import TateCurvesTheta.Converse.QuadraticTwist
import TateCurvesTheta.Converse.SplitIsTate
import TateCurvesTheta.TateCurve.CoordinateBaseChange

/-!
# The non-split case of Silverman V.5.3: quadratic twists of Tate curves

Let `K` be a complete ultrametric field with `(12 : K) ≠ 0`, `W` an elliptic curve over `K` with
`‖j(W)‖ > 1`, `q = ofJ j(W)` its Tate parameter and `γ = γ(W) = -c₄/c₆` its twist invariant. When
`γ` is **not** a square in `K`, `W` is not `K`-isomorphic to `E_q`
(`exists_variableChange_tateCurve_iff`); instead (Silverman, *Advanced Topics*, V.5.3(b)):

* `W` is `K`-isomorphic to the quadratic twist `E_q^γ` of `E_q` by `γ`
  (`exists_variableChange_quadraticTwist_tateCurve`, valid whether or not `γ` is a square), and
  `E_q^γ` is not `K`-isomorphic to `E_q` (`not_exists_variableChange_tateCurve_quadraticTwist`);
* over any field extension `L / K` in which `γ` becomes a square, in particular over
  `L = K(√γ) = K[X]/(X² - γ)` (`SqrtGammaField`, a quadratic extension), the base changes of `W`
  and `E_q` become isomorphic (`exists_variableChange_map_tateCurve_iff`,
  `exists_variableChange_sqrtGammaField`).

These statements are algebraic over `L`: `E_q` over `L` is the base change
`E_q.map (algebraMap K L)` of the curve over `K`. When `L` carries an absolute value extending
that of `K` (the repository's base-change setting `[NormedField L] [NormedAlgebra K L]`, e.g. the
spectral norm on a finite extension of a complete field), this base change *is* the Tate curve of
the base-changed parameter, `map_tateCurve`, and `exists_variableChange_baseChange_tateCurve_iff`
states the result in that form.

`nonsplit_tateCurve` packages the non-split case.
-/

namespace TateCurvesTheta

open WeierstrassCurve Polynomial

section Field

variable {F L : Type*} [Field F] [Field L]

/-- `γ` commutes with base change. -/
lemma gammaInvariant_map (W : WeierstrassCurve F) (f : F →+* L) :
    gammaInvariant (W.map f) = f (gammaInvariant W) := by
  rw [gammaInvariant, gammaInvariant, map_c₄, map_c₆, map_div₀, map_neg]

lemma ofNat_ne_zero_of_algebra [Algebra F L] (n : ℕ) [n.AtLeastTwo] (h : (OfNat.ofNat n : F) ≠ 0) :
    (OfNat.ofNat n : L) ≠ 0 := by
  rw [← map_ofNat (algebraMap F L) n]
  exact (_root_.map_ne_zero _).mpr h

end Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (h12 : (12 : K) ≠ 0) (W : WeierstrassCurve K) [W.IsElliptic]
include h12

/-- **`W` is a twist of `E_q`** (any `γ`): `W` is isomorphic over `K` to the quadratic twist of the
Tate curve `E_q`, `q = ofJ j(W)`, by `γ(W)`. -/
theorem exists_variableChange_quadraticTwist_tateCurve (hj : 1 < ‖W.j‖) :
    ∃ C : VariableChange K,
      C • W = quadraticTwist (TateParameter.ofJ h12 hj).tateCurve (gammaInvariant W) := by
  set t := TateParameter.ofJ h12 hj
  haveI := t.tateCurve_isElliptic h12
  obtain ⟨hj0, hj1728⟩ := ne_zero_and_ne_1728_of_one_lt_norm hj
  have hjt : W.j = t.tateCurve.j := by
    rw [← t.tateJ_eq_j h12, TateParameter.ofJ_tateJ]
  have h2 := two_ne_zero_of_twelve h12
  have h3 := three_ne_zero_of_twelve h12
  rw [exists_variableChange_quadraticTwist_iff' h2 h3 t.tateCurve W (hjt ▸ hj0) (hjt ▸ hj1728)
    hjt (gammaInvariant_ne_zero W hj0 hj1728)]
  obtain ⟨s, hs⟩ := t.isSquare_gammaInvariant h12
  exact ⟨gammaInvariant W * s, by rw [hs]; ring⟩

/-- **The twist is not split**: if `γ(W)` is not a square, the twist `E_q^γ` is not isomorphic
to `E_q` over `K`. -/
theorem not_exists_variableChange_tateCurve_quadraticTwist (hj : 1 < ‖W.j‖)
    (hγ : ¬IsSquare (gammaInvariant W)) :
    ¬∃ C : VariableChange K, C • (TateParameter.ofJ h12 hj).tateCurve =
      quadraticTwist (TateParameter.ofJ h12 hj).tateCurve (gammaInvariant W) := by
  set t := TateParameter.ofJ h12 hj
  haveI := t.tateCurve_isElliptic h12
  obtain ⟨hj0, hj1728⟩ := ne_zero_and_ne_1728_of_one_lt_norm hj
  have hjt : W.j = t.tateCurve.j := by
    rw [← t.tateJ_eq_j h12, TateParameter.ofJ_tateJ]
  rw [exists_variableChange_quadraticTwist_iff (two_ne_zero_of_twelve h12)
    (three_ne_zero_of_twelve h12) t.tateCurve (hjt ▸ hj0) (hjt ▸ hj1728)
    (gammaInvariant_ne_zero W hj0 hj1728)]
  exact hγ

/-- **Isomorphism after base change**: for any field extension `L / K`, the base changes of `W`
and of `E_q` (`q = ofJ j(W)`) are isomorphic over `L` iff `γ(W)` becomes a square in `L`. -/
theorem exists_variableChange_map_tateCurve_iff (L : Type*) [Field L] [Algebra K L]
    (hj : 1 < ‖W.j‖) :
    (∃ C : VariableChange L, C • W.map (algebraMap K L) =
        (TateParameter.ofJ h12 hj).tateCurve.map (algebraMap K L)) ↔
      IsSquare (algebraMap K L (gammaInvariant W)) := by
  set t := TateParameter.ofJ h12 hj
  haveI := t.tateCurve_isElliptic h12
  obtain ⟨hj0, hj1728⟩ := ne_zero_and_ne_1728_of_one_lt_norm hj
  have hjt : W.j = t.tateCurve.j := by
    rw [← t.tateJ_eq_j h12, TateParameter.ofJ_tateJ]
  have h2 : (2 : L) ≠ 0 := ofNat_ne_zero_of_algebra 2 (two_ne_zero_of_twelve h12)
  have h3 : (3 : L) ≠ 0 := ofNat_ne_zero_of_algebra 3 (three_ne_zero_of_twelve h12)
  have h1728 : (1728 : L) = algebraMap K L 1728 := (map_ofNat _ 1728).symm
  rw [exists_variableChange_iff_isSquare h2 h3 _ _
    (by rw [map_j]; exact (_root_.map_ne_zero _).mpr hj0)
    (by rw [map_j, h1728]; exact (algebraMap K L).injective.ne hj1728)
    (by rw [map_j, map_j, hjt]),
    gammaInvariant_map, gammaInvariant_map]
  have hγ := (_root_.map_ne_zero (algebraMap K L)).mpr (gammaInvariant_ne_zero W hj0 hj1728)
  obtain ⟨s, hs⟩ := t.isSquare_gammaInvariant h12
  have hs' : algebraMap K L (gammaInvariant t.tateCurve) = algebraMap K L s ^ 2 := by
    rw [hs, map_mul, sq]
  have hs0 : algebraMap K L s ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero, ← map_zero (algebraMap K L)] at hs'
    exact gammaInvariant_ne_zero t.tateCurve (hjt ▸ hj0) (hjt ▸ hj1728)
      ((algebraMap K L).injective hs')
  rw [hs']
  constructor
  · intro h
    have := (IsSquare.sq (algebraMap K L s)).div h
    rwa [div_div_cancel₀ (pow_ne_zero 2 hs0)] at this
  · exact (IsSquare.sq _).div

/-- **Isomorphism with the Tate curve over a valued extension**: if `L / K` carries an absolute
value extending that of `K`, then `W_L` is isomorphic over `L` to the Tate curve of the
base-changed parameter iff `γ(W)` is a square in `L`. -/
theorem exists_variableChange_baseChange_tateCurve_iff (L : Type*) [NormedField L]
    [NormedAlgebra K L] (hj : 1 < ‖W.j‖) :
    (∃ C : VariableChange L, C • W.map (algebraMap K L) =
        ((TateParameter.ofJ h12 hj).baseChange L).tateCurve) ↔
      IsSquare (algebraMap K L (gammaInvariant W)) := by
  rw [← TateParameter.map_tateCurve]
  exact exists_variableChange_map_tateCurve_iff h12 W L hj

omit h12 [W.IsElliptic] [IsUltrametricDist K] [CompleteSpace K] in
/-- `X² - γ` is irreducible when `γ` is not a square. -/
lemma irreducible_X_sq_sub_C {γ : K} (hγ : ¬IsSquare γ) : Irreducible (X ^ 2 - C γ) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => hγ ⟨b, by rw [← hb, sq]⟩

/-- The field `K(√γ) = K[X]/(X² - γ)`, for `γ = γ(W)`. It is a field (a quadratic extension of
`K`) when `γ` is not a square (`irreducible_X_sq_sub_C`). -/
abbrev SqrtGammaField (W : WeierstrassCurve K) : Type _ := AdjoinRoot (X ^ 2 - C (gammaInvariant W))

omit h12 [W.IsElliptic] [IsUltrametricDist K] [CompleteSpace K] in
/-- `γ(W)` is a square in `K(√γ)`. -/
lemma isSquare_algebraMap_sqrtGammaField :
    IsSquare (algebraMap K (SqrtGammaField W) (gammaInvariant W)) := by
  refine ⟨AdjoinRoot.root _, ?_⟩
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C (gammaInvariant W))
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [AdjoinRoot.algebraMap_eq, ← sq]
  exact (sub_eq_zero.mp h).symm

omit h12 [W.IsElliptic] [IsUltrametricDist K] [CompleteSpace K] in
/-- `K(√γ)` is a quadratic extension when `γ` is not a square. -/
lemma finrank_sqrtGammaField (hγ : ¬IsSquare (gammaInvariant W)) :
    haveI := Fact.mk (irreducible_X_sq_sub_C hγ)
    Module.finrank K (SqrtGammaField W) = 2 := by
  have hf : X ^ 2 - C (gammaInvariant W) ≠ 0 := (irreducible_X_sq_sub_C hγ).ne_zero
  rw [(AdjoinRoot.powerBasis hf).finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]

/-- **`W` becomes isomorphic to `E_q` over `K(√γ)`** (`γ = γ(W)` not a square in `K`). -/
theorem exists_variableChange_sqrtGammaField (hj : 1 < ‖W.j‖)
    (hγ : ¬IsSquare (gammaInvariant W)) :
    haveI := Fact.mk (irreducible_X_sq_sub_C hγ)
    ∃ C : VariableChange (SqrtGammaField W),
      C • W.map (algebraMap K (SqrtGammaField W)) =
        (TateParameter.ofJ h12 hj).tateCurve.map (algebraMap K (SqrtGammaField W)) := by
  haveI := Fact.mk (irreducible_X_sq_sub_C hγ)
  exact (exists_variableChange_map_tateCurve_iff h12 W _ hj).mpr
    (isSquare_algebraMap_sqrtGammaField W)

/-- **Silverman V.5.3, non-split case.** Let `‖j(W)‖ > 1`, `q = ofJ j(W)`, and suppose
`γ(W) = -c₄/c₆` is not a square in `K`. Then
1. `W` is not isomorphic to `E_q` over `K`;
2. `W` is isomorphic over `K` to the quadratic twist `E_q^γ` of `E_q` by `γ(W)`;
3. `E_q^γ` is not isomorphic to `E_q` over `K`;
4. `W` and `E_q` become isomorphic over the quadratic extension `K(√γ)`. -/
theorem nonsplit_tateCurve (hj : 1 < ‖W.j‖) (hγ : ¬IsSquare (gammaInvariant W)) :
    (¬∃ C : VariableChange K, C • W = (TateParameter.ofJ h12 hj).tateCurve) ∧
    (∃ C : VariableChange K,
      C • W = quadraticTwist (TateParameter.ofJ h12 hj).tateCurve (gammaInvariant W)) ∧
    (¬∃ C : VariableChange K, C • (TateParameter.ofJ h12 hj).tateCurve =
      quadraticTwist (TateParameter.ofJ h12 hj).tateCurve (gammaInvariant W)) ∧
    haveI := Fact.mk (irreducible_X_sq_sub_C hγ)
    Module.finrank K (SqrtGammaField W) = 2 ∧
    ∃ C : VariableChange (SqrtGammaField W),
      C • W.map (algebraMap K (SqrtGammaField W)) =
        (TateParameter.ofJ h12 hj).tateCurve.map (algebraMap K (SqrtGammaField W)) :=
  ⟨fun h => hγ ((exists_variableChange_tateCurve_iff h12 W hj).mp h),
    exists_variableChange_quadraticTwist_tateCurve h12 W hj,
    not_exists_variableChange_tateCurve_quadraticTwist h12 W hj hγ,
    finrank_sqrtGammaField W hγ, exists_variableChange_sqrtGammaField h12 W hj hγ⟩

end TateCurvesTheta
