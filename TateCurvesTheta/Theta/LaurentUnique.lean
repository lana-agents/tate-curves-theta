/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.Theta.Uniqueness
import TateCurvesTheta.Analysis.UltrametricSum

/-!
# Reducing nonarchimedean Laurent coefficient uniqueness to a strict-dominant radius

The `q`-difference engine in `Theta/Uniqueness.lean` (#119) is proved conditionally on the
`LaurentCoeffUnique K` principle: over a complete nonarchimedean field, a convergent two-sided
Laurent series `∑' n : ℤ, cₙ uⁿ` is determined by its values on `Kˣ`. That principle is the
nonarchimedean identity theorem for Laurent expansions, whose full proof is a Newton-polygon /
maximum-modulus argument absent from Mathlib.

This file discharges the *analytic* half of that argument once and for all, isolating the
remaining content as a single sharp, purely **existential** seam. Concretely, combining the
dominant-term principle `IsUltrametricDist.norm_tsum_eq_of_dominant`
(`Analysis/UltrametricSum.lean`, #121 Milestone A) with linearity, we reduce
`LaurentCoeffUnique K` to:

> **`LaurentStrictDom K`** — for every coefficient family `c : ℤ → K` whose Laurent series is
> summable on all of `Kˣ` and which is not identically zero, there is a radius (a unit
> `u : Kˣ`) and an index `n₀` at which the term `cₙ₀ uⁿ₀` **strictly dominates** every other
> term `cₙ uⁿ` in norm.

This is exactly the Newton-polygon *vertex-selection* step named as the residual seam in #121:
all the infinite-sum / ultrametric analysis (the isosceles max-modulus law, tail domination) is
now done; what remains is the finite geometric fact that a nonzero convergent Laurent family has
a strictly dominant term at some available radius. `LaurentStrictDom` is therefore a strictly
smaller and more elementary obligation than `LaurentCoeffUnique`.

## Main definitions

* `TateCurvesTheta.LaurentStrictDom` : the strict-dominant-radius principle (the sharpened seam).

## Main results

* `TateCurvesTheta.tsum_ne_zero_of_strictDom` : under `LaurentStrictDom`, a nonzero summable
  Laurent family has some `u : Kˣ` at which its sum is nonzero.
* `TateCurvesTheta.laurentCoeffUnique_of_strictDom` : `LaurentStrictDom K → LaurentCoeffUnique K`.
* `TateCurvesTheta.TateParameter.const_of_qinvariant_laurent_of_strictDom` : the #119 engine with
  its `LaurentCoeffUnique` hypothesis replaced by the sharper `LaurentStrictDom`.

## The residual seam

`LaurentStrictDom K` is *not* proved here; it genuinely requires a hypothesis on `K`. It holds,
for instance, when the value group `‖Kˣ‖` is rich enough that some radius avoids the (Newton-
polygon corner) radii at which two indices tie — the "generic radius" case — and, in the
discrete-value-group / finite-residue-field case (e.g. `ℚₚ`), requires the Strassmann /
finiteness-of-zeros input flagged in #122. It is stated precisely so a follow-up can discharge it
for the project's `K` and thereby make the whole `q`-difference engine — and downstream
`theta = thetaProd` (#105/#88), `tatePoint_mem` route 1 (#116) and surjectivity (#118) —
unconditional.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* A. Robert, *A Course in p-adic Analysis*, §6.1–6.2 (the maximum term; Strassmann's theorem).
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
-/

open Filter Topology

namespace TateCurvesTheta

variable {K : Type*} [NormedField K]

/-- **Strict-dominant-radius principle** — the sharpened residual seam for Laurent coefficient
uniqueness. For every coefficient family `c : ℤ → K` giving a summable Laurent series on all of
`Kˣ` and not identically zero, there exist a unit `u : Kˣ` (a choice of radius) and an index
`n₀` at which the term `cₙ₀ · uⁿ₀` strictly dominates every other term `cₙ · uⁿ` in norm.

This is the Newton-polygon vertex-selection step: it carries no infinite-sum content (that is
handled by `IsUltrametricDist.norm_tsum_eq_of_dominant`), only the finite geometric assertion
that a nonzero convergent Laurent family has a strict maximum term at some available radius. -/
def LaurentStrictDom (K : Type*) [NormedField K] : Prop :=
  ∀ c : ℤ → K,
    (∀ u : Kˣ, Summable fun n : ℤ => c n * (u : K) ^ n) →
    (∃ m : ℤ, c m ≠ 0) →
    ∃ (u : Kˣ) (n₀ : ℤ),
      ∀ n : ℤ, n ≠ n₀ → ‖c n * (u : K) ^ n‖ < ‖c n₀ * (u : K) ^ n₀‖

variable [CompleteSpace K] [IsUltrametricDist K]

/-- Under `LaurentStrictDom`, a nonzero convergent Laurent series does **not** vanish identically
on `Kˣ`: at the strictly-dominating radius the dominant-term principle
`IsUltrametricDist.norm_tsum_eq_of_dominant` pins the sum's norm to that of the (nonzero)
dominant term. -/
theorem tsum_ne_zero_of_strictDom (hdom : LaurentStrictDom K) (c : ℤ → K)
    (hsum : ∀ u : Kˣ, Summable fun n : ℤ => c n * (u : K) ^ n) (hc : ∃ m : ℤ, c m ≠ 0) :
    ∃ u : Kˣ, (∑' n : ℤ, c n * (u : K) ^ n) ≠ 0 := by
  obtain ⟨u, n₀, hlt⟩ := hdom c hsum hc
  refine ⟨u, ?_⟩
  -- The dominant term strictly exceeds a genuine competitor, hence is nonzero.
  have hpos : 0 < ‖c n₀ * (u : K) ^ n₀‖ :=
    lt_of_le_of_lt (norm_nonneg _) (hlt (n₀ + 1) (by omega))
  have hval : ‖∑' n : ℤ, c n * (u : K) ^ n‖ = ‖c n₀ * (u : K) ^ n₀‖ :=
    IsUltrametricDist.norm_tsum_eq_of_dominant (hsum u) hlt
  rw [← norm_ne_zero_iff, hval]
  exact ne_of_gt hpos

/-- **Reduction of `LaurentCoeffUnique` to `LaurentStrictDom`.** By linearity (apply to the
difference `c := a - b`) coefficient uniqueness is equivalent to: a summable Laurent family that
vanishes identically on `Kˣ` is the zero family. `tsum_ne_zero_of_strictDom` supplies exactly the
contrapositive, so the strict-dominant-radius principle implies coefficient uniqueness. -/
theorem laurentCoeffUnique_of_strictDom (hdom : LaurentStrictDom K) : LaurentCoeffUnique K := by
  intro a b hsa hsb heq
  by_contra hab
  -- `c := a - b` is a nonzero coefficient family whose Laurent series vanishes on all of `Kˣ`.
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hab
  have hcm : a m - b m ≠ 0 := sub_ne_zero.mpr hm
  have hcsum : ∀ u : Kˣ, Summable fun n : ℤ => (a n - b n) * (u : K) ^ n := by
    intro u
    refine ((hsa u).sub (hsb u)).congr fun n => ?_
    rw [sub_mul]
  have hczero : ∀ u : Kˣ, (∑' n : ℤ, (a n - b n) * (u : K) ^ n) = 0 := by
    intro u
    have hsplit : (∑' n : ℤ, (a n - b n) * (u : K) ^ n)
        = (∑' n : ℤ, a n * (u : K) ^ n) - ∑' n : ℤ, b n * (u : K) ^ n := by
      rw [← (hsa u).tsum_sub (hsb u)]
      exact tsum_congr fun n => by rw [sub_mul]
    rw [hsplit, heq u, sub_self]
  obtain ⟨u, hu⟩ := tsum_ne_zero_of_strictDom hdom (fun n => a n - b n) hcsum ⟨m, hcm⟩
  exact hu (hczero u)

namespace TateParameter

variable (t : TateParameter K)

/-- **The `q`-difference engine under the sharpened seam.** The #119 engine
`const_of_qinvariant_laurent`, with its `LaurentCoeffUnique` hypothesis replaced by the strictly
weaker, purely existential `LaurentStrictDom`: a `q`-invariant convergent Laurent series equals
its constant term `a₀` at every `u : Kˣ`. -/
theorem const_of_qinvariant_laurent_of_strictDom (hdom : LaurentStrictDom K) (a : ℤ → K)
    (hsum : ∀ u : Kˣ, Summable fun n : ℤ => a n * (u : K) ^ n)
    (hqinv : ∀ u : Kˣ,
      (∑' n : ℤ, a n * ((t.q : K) * (u : K)) ^ n) = ∑' n : ℤ, a n * (u : K) ^ n) :
    ∀ u : Kˣ, (∑' n : ℤ, a n * (u : K) ^ n) = a 0 :=
  t.const_of_qinvariant_laurent (laurentCoeffUnique_of_strictDom hdom) a hsum hqinv

end TateParameter

end TateCurvesTheta
