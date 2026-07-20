/-
Copyright (c) 2026 The TateCurvesTheta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The TateCurvesTheta contributors
-/
import Mathlib
import TateCurvesTheta.AnalyticQuotient

/-!
# The group-theoretic `q`-uniformization sequence and its functoriality

Building on `TateCurvesTheta.AnalyticQuotient`, this file records the exact sequence
underlying Tate's `q`-uniformization at the level of abstract groups, together with its
functoriality under a complete field extension `L / K`.

For a Tate datum `q` over `K`, the analytic quotient `Kˣ / qᶻ` sits in the short exact
sequence
```
1 ⟶ qᶻ ⟶ Kˣ ⟶ Kˣ / qᶻ ⟶ 1,
```
i.e. the quotient projection `toAnalyticQuotient` is surjective with kernel exactly `qᶻ`.
The middle term `Kˣ` is the group of `K`-points of the multiplicative group `𝔾ₘ`, and the
quotient is the group of `K`-points of the Tate curve `E_q`; the Weierstrass model of `E_q`
(which requires the nonarchimedean convergence of Tate's series and is deferred to a later
layer) makes the quotient concrete, but the group-theoretic content of the sequence is
already available here.

We also record functoriality: a complete field extension `L / K`, modelled as
`[NormedField L] [NormedAlgebra K L]`, carries a Tate datum over `K` to one over `L`
(`TateDatum.baseChange`, the smallness `‖q‖ < 1` being preserved by the isometry
`norm_algebraMap'`), and induces a group homomorphism `Kˣ / qᶻ →* Lˣ / qᶻ` on the analytic
quotients (`TateDatum.mapAnalyticQuotient`) compatible with the projections.

## Main definitions

* `TateDatum.baseChange` : the Tate datum over `L` obtained from one over `K`.
* `TateDatum.mapAnalyticQuotient` : the induced group hom `Kˣ / qᶻ →* Lˣ / qᶻ`.

## Main results

* `TateDatum.toAnalyticQuotient_surjective` : the projection `Kˣ → Kˣ / qᶻ` is surjective.
* `TateDatum.ker_toAnalyticQuotient` : its kernel is exactly `qᶻ`.
* `TateDatum.toAnalyticQuotient_eq_one_iff` : `x ↦ 1` in `Kˣ / qᶻ` iff `x ∈ qᶻ`.
* `TateDatum.mapAnalyticQuotient_comp_toAnalyticQuotient` : the induced map commutes with the
  two projections (functoriality of `q`-uniformization).

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter V.
-/

namespace TateCurvesTheta

namespace TateDatum

variable {K : Type*} [NormedField K] (T : TateDatum K)

/-! ### The exact sequence `1 → qᶻ → Kˣ → Kˣ/qᶻ → 1` -/

/-- The uniformization projection `Kˣ → Kˣ / qᶻ` is surjective. -/
lemma toAnalyticQuotient_surjective : Function.Surjective T.toAnalyticQuotient :=
  QuotientGroup.mk'_surjective T.qpowers

/-- The kernel of the uniformization projection is exactly the subgroup `qᶻ`. -/
@[simp] lemma ker_toAnalyticQuotient : T.toAnalyticQuotient.ker = T.qpowers :=
  QuotientGroup.ker_mk' T.qpowers

/-- An element of `Kˣ` maps to the identity of `Kˣ / qᶻ` iff it is an integer power of `q`. -/
lemma toAnalyticQuotient_eq_one_iff {x : Kˣ} :
    T.toAnalyticQuotient x = 1 ↔ x ∈ T.qpowers := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

/-- Two units have the same image in `Kˣ / qᶻ` iff they differ by an integer power of `q`. -/
lemma toAnalyticQuotient_eq_iff {x y : Kˣ} :
    T.toAnalyticQuotient x = T.toAnalyticQuotient y ↔ x⁻¹ * y ∈ T.qpowers := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]

/-! ### Functoriality under a complete field extension `L / K` -/

variable (L : Type*) [NormedField L] [NormedAlgebra K L]

/-- **Base change** of a Tate datum along a complete field extension `L / K`: the underlying
unit is the image of `q` under `algebraMap K L`, and `‖q‖ < 1` is preserved because the
absolute value of `L` extends that of `K` (`‖algebraMap K L q‖ = ‖q‖`). -/
def baseChange : TateDatum L where
  q := Units.map (algebraMap K L).toMonoidHom T.q
  norm_q_lt_one := by
    have h : ‖((Units.map (algebraMap K L).toMonoidHom T.q : Lˣ) : L)‖ = ‖(T.q : K)‖ := by
      rw [Units.coe_map]; exact norm_algebraMap' L (T.q : K)
    rw [h]; exact T.norm_q_lt_one

@[simp] lemma baseChange_q_coe :
    ((T.baseChange L).q : L) = algebraMap K L (T.q : K) :=
  Units.coe_map _ _

/-- Base change sends `qᶻ ≤ Kˣ` into `qᶻ ≤ Lˣ` under the induced unit map `Units.map`. -/
lemma qpowers_le_comap :
    T.qpowers ≤
      Subgroup.comap (Units.map (algebraMap K L).toMonoidHom) (T.baseChange L).qpowers := by
  rw [qpowers, Subgroup.zpowers_le, Subgroup.mem_comap]
  exact (T.baseChange L).q_mem_qpowers

/-- **Functoriality of `q`-uniformization.**  A complete field extension `L / K` induces a
group homomorphism `Kˣ / qᶻ →* Lˣ / qᶻ` on the analytic quotients, compatible with the
uniformization projections (`mapAnalyticQuotient_comp_toAnalyticQuotient`). -/
def mapAnalyticQuotient : T.AnalyticQuotient →* (T.baseChange L).AnalyticQuotient :=
  QuotientGroup.map T.qpowers (T.baseChange L).qpowers
    (Units.map (algebraMap K L).toMonoidHom) (T.qpowers_le_comap L)

/-- The induced map on analytic quotients commutes with the two uniformization projections:
it sends the class of `x` to the class of `algebraMap K L x`. -/
@[simp] lemma mapAnalyticQuotient_comp_toAnalyticQuotient (x : Kˣ) :
    T.mapAnalyticQuotient L (T.toAnalyticQuotient x) =
      (T.baseChange L).toAnalyticQuotient (Units.map (algebraMap K L).toMonoidHom x) :=
  QuotientGroup.map_mk' _ _ _ _ x

end TateDatum

end TateCurvesTheta
