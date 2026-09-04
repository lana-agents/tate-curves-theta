/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.TateCurve.DefectCoeffBaseChange
import TateCurvesTheta.TateCurve.JInvariant

/-!
# Base change of the Tate coordinate functions and the Tate curve

For a Tate parameter `q` over a complete nonarchimedean field `K` and an isometric extension
`L / K` (modelled as `[NormedField L] [NormedAlgebra K L]`, see
`TateCurvesTheta/QParameter/BaseChange.lean`), the Tate coordinate series
```
X q u = ∑' n : ℤ, qⁿ u / (1 - qⁿ u)²  - 2 s₁(q),
Y q u = ∑' n : ℤ, (qⁿ u)² / (1 - qⁿ u)³ + s₁(q)
```
are defined termwise by rational expressions in `q` and `u`, so the algebra map `K → L` —
an isometry, hence continuous — carries each of them onto the corresponding series of the
base-changed parameter `baseChange L q` evaluated at the image unit. Likewise the Tate
Weierstrass curve `E_q` and its `j`-invariant `c₄³ / Δ` are given by universal formulas in the
coefficients `a₄(q), a₆(q)`, which commute with the extension by
`TateCurvesTheta/TateCurve/DefectCoeffBaseChange.lean`.

## Main results

* `TateParameter.algebraMap_Xterm`, `TateParameter.algebraMap_Yterm`: the general terms of the
  coordinate series commute with the extension.
* `TateParameter.algebraMap_X`, `TateParameter.algebraMap_Y`: the coordinate functions commute
  with the extension.
* `TateParameter.baseChange_notMem`: the image of a unit `u ∉ qᶻ` again avoids `qᶻ`.
* `TateParameter.map_tateCurve`: `E_q` base-changes to `E_{baseChange q}`.
* `TateParameter.algebraMap_tateJ`: the `j`-invariant commutes with the extension.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (L : Type*) [NormedField L] [NormedAlgebra K L]
variable (t : TateParameter K)

/-- The underlying element of the image of a unit under the algebra map. -/
lemma coe_units_map_algebraMap (u : Kˣ) :
    ((Units.map (algebraMap K L).toMonoidHom u : Lˣ) : L) = algebraMap K L (u : K) :=
  Units.coe_map _ _

/-- The algebra map of an isometric extension maps convergent sums to convergent sums. -/
private lemma algebraMap_tsum' {ι : Type*} {f : ι → K} (hf : Summable f) :
    algebraMap K L (∑' i : ι, f i) = ∑' i : ι, algebraMap K L (f i) :=
  ((hf.hasSum.map (algebraMap K L)
    (AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap' L)).continuous).tsum_eq).symm

/-! ### The general terms -/

/-- The general term of the `X`-coordinate series commutes with an isometric extension. -/
lemma algebraMap_Xterm (u : Kˣ) (n : ℤ) :
    algebraMap K L (t.Xterm u n)
      = (t.baseChange L).Xterm (Units.map (algebraMap K L).toMonoidHom u) n := by
  rw [Xterm_apply, Xterm_apply, map_div₀, map_pow, map_sub, map_one, map_mul, map_zpow₀,
    baseChange_q_coe, coe_units_map_algebraMap]

/-- The general term of the `Y`-coordinate series commutes with an isometric extension. -/
lemma algebraMap_Yterm (u : Kˣ) (n : ℤ) :
    algebraMap K L (t.Yterm u n)
      = (t.baseChange L).Yterm (Units.map (algebraMap K L).toMonoidHom u) n := by
  rw [Yterm_apply, Yterm_apply, map_div₀, map_pow, map_pow, map_sub, map_one, map_mul,
    map_zpow₀, baseChange_q_coe, coe_units_map_algebraMap]

/-- A unit avoiding `qᶻ` in `K` still avoids `qᶻ` after an isometric extension, since the
algebra map is injective. -/
lemma baseChange_notMem {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) (n : ℤ) :
    ((t.baseChange L).q : L) ^ n * ((Units.map (algebraMap K L).toMonoidHom u : Lˣ) : L)
      ≠ 1 := by
  rw [baseChange_q_coe, coe_units_map_algebraMap, ← map_zpow₀, ← map_mul,
    ← map_one (algebraMap K L)]
  exact fun h => hu n ((algebraMap K L).injective h)

/-! ### The coordinate functions -/

section Coordinates

variable [IsUltrametricDist K] [CompleteSpace K]

/-- The Tate `X`-coordinate commutes with an isometric extension. -/
theorem algebraMap_X (u : Kˣ) :
    algebraMap K L (t.X u) = (t.baseChange L).X (Units.map (algebraMap K L).toMonoidHom u) := by
  rw [X_apply, X_apply, map_sub, map_mul, map_ofNat, t.algebraMap_eisenstein L,
    algebraMap_tsum' L (t.Xterm_summable u)]
  congr 1
  exact tsum_congr fun n => t.algebraMap_Xterm L u n

/-- The Tate `Y`-coordinate commutes with an isometric extension. -/
theorem algebraMap_Y (u : Kˣ) :
    algebraMap K L (t.Y u) = (t.baseChange L).Y (Units.map (algebraMap K L).toMonoidHom u) := by
  rw [Y_apply, Y_apply, map_add, t.algebraMap_eisenstein L,
    algebraMap_tsum' L (t.Yterm_summable u)]
  congr 1
  exact tsum_congr fun n => t.algebraMap_Yterm L u n

/-! ### The Tate curve and its `j`-invariant -/

/-- The Tate Weierstrass curve `E_q` base-changes to the Tate curve of the base-changed
parameter. -/
theorem map_tateCurve : t.tateCurve.map (algebraMap K L) = (t.baseChange L).tateCurve := by
  simp only [WeierstrassCurve.map, tateCurve, map_one, map_zero, t.algebraMap_a₄ L,
    t.algebraMap_a₆ L]

/-- The `j`-invariant `c₄³ / Δ` of the Tate curve commutes with an isometric extension. -/
theorem algebraMap_tateJ : algebraMap K L t.tateJ = (t.baseChange L).tateJ := by
  rw [tateJ_def, tateJ_def, map_div₀, map_pow, ← WeierstrassCurve.map_c₄,
    ← WeierstrassCurve.map_Δ, t.map_tateCurve L]

end Coordinates

end TateParameter

end TateCurvesTheta
