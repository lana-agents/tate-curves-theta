/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Module.Basic
import TateCurvesTheta.QParameter.Basic

/-!
# Base change of the Tate `q`-parameter along a complete field extension

Given a Tate parameter `q` over a complete nonarchimedean field `K` and a complete field
extension `L / K`, the element `q` is again a Tate parameter over `L`: the defining
inequalities `0 < ‖q‖ < 1` are preserved because the absolute value of `L` restricts to the
absolute value of `K`.

We model the extension `L / K` as `[NormedField L] [NormedAlgebra K L]`. For a normed field
`L` one has `‖(1 : L)‖ = 1`, so `NormedAlgebra K L` supplies exactly the isometry property
`‖algebraMap K L x‖ = ‖x‖` (`norm_algebraMap'`) that characterises an extension of the
absolute value. This is the hypothesis satisfied by the unique extension of the absolute
value to a complete valued-field extension (Silverman, *Advanced Topics*, Ch. II), and it is
the seam through which the shared normalized-valuation infrastructure (project-3 #4) will be
plugged in later without changing any statement here.

## Main definitions

* `TateCurvesTheta.TateParameter.baseChange`: the image `TateParameter L` of a
  `TateParameter K` under `algebraMap K L`.

## Main results

* `TateParameter.baseChange_q_coe`: the underlying element of the base-changed parameter is
  `algebraMap K L q`.
* `TateParameter.norm_baseChange`: `‖(baseChange q)‖ = ‖q‖` (the absolute value is preserved).
* `TateParameter.ord_baseChange`: `ord (baseChange q) = ord q`. The **real-valued** normalized
  order is *invariant* under an isometric complete extension.

## The normalized order under ramification

The order `ord q = -Real.log ‖q‖` used here is the real-valued local-height convention
(IUT I, Definition 3.1(c)); it is computed from the absolute value and is therefore literally
unchanged when the absolute value extends isometrically (`ord_baseChange`).

The *discrete* normalized additive valuation `v_L`, normalized so that a uniformizer has
`v_L = 1`, is instead the one that scales by the ramification index:
`v_L (algebraMap K L x) = e(L/K) · v_K x`. That normalization is deliberately deferred to the
shared valuation infrastructure (project-3 #4); when it lands, the ramification scaling is a
statement about `v_L` refining `ord`, and `ord_baseChange` above records the compatible fact
that the underlying real absolute value—hence the real-valued `ord`—does not change. Keeping
the two apart here is intentional: the real order is normalization-free, while the integer
order carries the `e(L/K)` factor.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapters II, V.
* S. Mochizuki, *Inter-universal Teichmüller Theory I*, Definition 3.1(c).
-/

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (L : Type*) [NormedField L] [NormedAlgebra K L]

/-- **Base change** of a Tate parameter along a complete field extension `L / K`.

The underlying unit is the image of `q` under `algebraMap K L`, and `‖·‖ < 1` is preserved
because `‖algebraMap K L q‖ = ‖q‖` (the absolute value of `L` extends that of `K`). -/
def baseChange (t : TateParameter K) : TateParameter L where
  q := Units.map (algebraMap K L).toMonoidHom t.q
  norm_lt_one := by
    have h : ‖((Units.map (algebraMap K L).toMonoidHom t.q : Lˣ) : L)‖ = ‖(t.q : K)‖ := by
      rw [Units.coe_map]
      exact norm_algebraMap' L (t.q : K)
    rw [h]
    exact t.norm_lt_one

@[simp]
lemma baseChange_q_coe (t : TateParameter K) :
    ((t.baseChange L).q : L) = algebraMap K L (t.q : K) :=
  Units.coe_map _ _

/-- The absolute value of a Tate parameter is preserved under a complete field extension. -/
@[simp]
lemma norm_baseChange (t : TateParameter K) :
    ‖((t.baseChange L).q : L)‖ = ‖(t.q : K)‖ := by
  rw [baseChange_q_coe, norm_algebraMap']

/-- The real-valued normalized order is invariant under a complete field extension: the
absolute value—and hence `ord = -log ‖q‖`—is unchanged. The ramification-index scaling is
carried by the discrete normalized valuation instead (see the module docstring). -/
@[simp]
lemma ord_baseChange (t : TateParameter K) : (t.baseChange L).ord = t.ord := by
  simp only [ord, norm_baseChange]

end TateParameter

end TateCurvesTheta
