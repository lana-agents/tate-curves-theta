/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Group.Ultra
import TateCurvesTheta.Theta.Uniqueness

/-!
# Reducing nonarchimedean Laurent coefficient uniqueness to finiteness of zeros on a sphere

The `q`-difference engine in `Theta/Uniqueness.lean` (#119) is proved conditionally on the
`LaurentCoeffUnique K` principle: over a complete nonarchimedean field, a convergent two-sided
Laurent series `∑' n : ℤ, cₙ uⁿ` is determined by its values on `Kˣ`. That principle is the
nonarchimedean identity theorem for Laurent expansions.

A *sibling* reduction (`Theta/LaurentUnique.lean`, #121) reduces `LaurentCoeffUnique` to
`LaurentStrictDom`: the existence, for a nonzero family, of a radius at which one term
**strictly** dominates. That seam is unfortunately **false for discretely-valued fields** such
as `ℚₚ`: the family `cₙ = qⁿ⁽ⁿ⁻¹⁾ᐟ²` is nonzero and summable on every `u : Kˣ`, yet at every
radius `‖u‖ = ‖q‖ᵂ` (all radii, since the value group is `‖q‖ℤ`) the maximal term norm is
attained by *two* adjacent indices `n = −w` and `n = −w + 1` — a Newton polygon whose edge
slopes exhaust `ℤ`. So no strictly dominant term exists, and `LaurentStrictDom (ℚₚ)` cannot be
discharged for the project's abstract `K` (which is realized by `ℚₚ`).

This file installs the **correct** residual seam, the one that survives the discrete case:

> **`LaurentSphereZerosFinite K`** — a nonzero coefficient family `c : ℤ → K` whose Laurent
> series is summable on all of `Kˣ` has, on each sphere `{u : Kˣ | ‖u‖ = ρ}`, only **finitely
> many** zeros of `u ↦ ∑' n, cₙ uⁿ`.

This is exactly the Strassmann / Newton-polygon *finiteness of zeros* input (Robert §6.2): a
nonzero convergent (Laurent) series has finitely many roots on each sphere. Unlike
`LaurentStrictDom`, it is *true* for `ℚₚ`, so discharging it makes the whole `q`-difference
engine — and downstream `theta = thetaProd` (#105/#88), `tatePoint_mem` route 1 (#116) and
surjectivity (#118) — unconditional.

The reduction proved here is elementary and unconditional: if a nonzero family vanished on **all**
of `Kˣ`, it would in particular vanish at the infinitely many *distinct* norm-one units
`1 + qᵏ⁺¹` (`k : ℕ`) — each has norm exactly `1` by the ultrametric isosceles law and they are
pairwise distinct because `‖q‖ᵏ⁺¹` is strictly antitone — contradicting finiteness of the zeros
on the unit sphere. Feeding `LaurentSphereZerosFinite` gives `LaurentCoeffUnique`.

## Main definitions

* `TateCurvesTheta.LaurentSphereZerosFinite` : the finiteness-of-zeros-per-sphere seam (the
  Strassmann input), the honest residual obligation for coefficient uniqueness.

## Main results

* `TateCurvesTheta.TateParameter.norm_one_add_qpow` : `‖1 + qᵏ⁺¹‖ = 1`.
* `TateCurvesTheta.TateParameter.sphereWitness` : the norm-one units `1 + qᵏ⁺¹`, and
  `sphereWitness_injective` : they are pairwise distinct.
* `TateCurvesTheta.TateParameter.laurentCoeffUnique_of_sphereZerosFinite` :
  `LaurentSphereZerosFinite K → LaurentCoeffUnique K`.
* `TateCurvesTheta.TateParameter.const_of_qinvariant_laurent_of_sphereZerosFinite` : the #119
  engine with its `LaurentCoeffUnique` hypothesis replaced by `LaurentSphereZerosFinite`.

## The residual seam

`LaurentSphereZerosFinite K` is *not* proved here: it is Strassmann's theorem for the sphere,
absent from Mathlib (no Newton-polygon / Weierstrass-preparation machinery over nonarchimedean
fields as of 2026-07). It is stated precisely so a follow-up can discharge it — via the ultrametric
Newton polygon of `c` restricted to a sphere — and thereby settle `LaurentCoeffUnique` for the
project's `K`, including the discrete case `ℚₚ` that `LaurentStrictDom` cannot reach.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* A. Robert, *A Course in p-adic Analysis*, §6.1–6.2 (the maximum term; Strassmann's theorem;
  finiteness of zeros of a convergent series).
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, §IV (Newton polygons).
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
-/

open Filter Topology

namespace TateCurvesTheta

variable {K : Type*} [NormedField K]

/-- **Finiteness of zeros on a sphere** — the Strassmann residual seam for Laurent coefficient
uniqueness. For every coefficient family `c : ℤ → K` giving a summable Laurent series on all of
`Kˣ` and not identically zero, and every radius `ρ : ℝ`, the set of units `u` with `‖u‖ = ρ` at
which the series vanishes is finite.

This is the nonarchimedean *finiteness of zeros* fact (Newton polygon / Strassmann): a nonzero
convergent series has only finitely many roots on each sphere. In contrast to
`LaurentStrictDom`, it holds for discretely-valued `K` such as `ℚₚ`. -/
def LaurentSphereZerosFinite (K : Type*) [NormedField K] : Prop :=
  ∀ c : ℤ → K, c ≠ 0 →
    (∀ u : Kˣ, Summable fun n : ℤ => c n * (u : K) ^ n) →
    ∀ ρ : ℝ, {u : Kˣ | ‖(u : K)‖ = ρ ∧ (∑' n : ℤ, c n * (u : K) ^ n) = 0}.Finite

namespace TateParameter

variable [IsUltrametricDist K] (t : TateParameter K)

/-- **The norm-one units `1 + qᵏ⁺¹`.** Since `‖qᵏ⁺¹‖ = ‖q‖ᵏ⁺¹ < 1 = ‖1‖`, the ultrametric
isosceles law forces `‖1 + qᵏ⁺¹‖ = max ‖1‖ ‖qᵏ⁺¹‖ = 1`. -/
lemma norm_one_add_qpow (k : ℕ) : ‖(1 : K) + (t.q : K) ^ (k + 1)‖ = 1 := by
  have hlt : ‖(t.q : K) ^ (k + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) t.norm_lt_one (Nat.succ_ne_zero k)
  have hne : ‖(1 : K)‖ ≠ ‖(t.q : K) ^ (k + 1)‖ := by
    rw [norm_one]; exact ne_of_gt hlt
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one, max_eq_left hlt.le]

/-- The elements `1 + qᵏ⁺¹` are nonzero (their norm is `1`), hence lie in `Kˣ`. -/
lemma one_add_qpow_ne_zero (k : ℕ) : (1 : K) + (t.q : K) ^ (k + 1) ≠ 0 := by
  intro h
  have := t.norm_one_add_qpow k
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

/-- The norm-one unit `1 + qᵏ⁺¹` as an element of `Kˣ`. -/
noncomputable def sphereWitness (k : ℕ) : Kˣ :=
  Units.mk0 ((1 : K) + (t.q : K) ^ (k + 1)) (t.one_add_qpow_ne_zero k)

@[simp] lemma sphereWitness_val (k : ℕ) :
    (t.sphereWitness k : K) = (1 : K) + (t.q : K) ^ (k + 1) := rfl

/-- The witnesses `1 + qᵏ⁺¹` are pairwise distinct: their `q`-parts `qᵏ⁺¹` have distinct norms
`‖q‖ᵏ⁺¹` (strictly antitone since `0 < ‖q‖ < 1`), so `pow_right_injective₀` separates the
exponents. -/
lemma sphereWitness_injective : Function.Injective t.sphereWitness := by
  intro j k h
  have hv : (1 : K) + (t.q : K) ^ (j + 1) = (1 : K) + (t.q : K) ^ (k + 1) := by
    have := congrArg (Units.val) h
    simpa only [sphereWitness_val] using this
  have hq : (t.q : K) ^ (j + 1) = (t.q : K) ^ (k + 1) := add_left_cancel hv
  have hnorm : ‖(t.q : K)‖ ^ (j + 1) = ‖(t.q : K)‖ ^ (k + 1) := by
    rw [← norm_pow, ← norm_pow, hq]
  have := pow_right_injective₀ t.norm_q_pos (ne_of_lt t.norm_lt_one) hnorm
  omega

/-- **Reduction of `LaurentCoeffUnique` to `LaurentSphereZerosFinite`.** By linearity (apply to
the difference `c := a - b`) coefficient uniqueness is equivalent to: a summable Laurent family
that vanishes identically on `Kˣ` is the zero family. If such a family `c` were nonzero, then by
`LaurentSphereZerosFinite` its zeros on the unit sphere `{u | ‖u‖ = 1}` are finite; but the
infinitely many distinct norm-one units `1 + qᵏ⁺¹` (`k : ℕ`, `sphereWitness`) are all zeros of
the series, a contradiction. Hence `c = 0`, i.e. `a = b`. -/
theorem laurentCoeffUnique_of_sphereZerosFinite (t : TateParameter K)
    (hfin : LaurentSphereZerosFinite K) : LaurentCoeffUnique K := by
  intro a b hsa hsb heq
  by_contra hab
  -- `c := a - b` is a nonzero coefficient family whose Laurent series vanishes on all of `Kˣ`.
  have hcne : (a - b) ≠ 0 := sub_ne_zero.mpr hab
  have hcsum : ∀ u : Kˣ, Summable fun n : ℤ => (a - b) n * (u : K) ^ n := by
    intro u
    refine ((hsa u).sub (hsb u)).congr fun n => ?_
    rw [Pi.sub_apply, sub_mul]
  have hczero : ∀ u : Kˣ, (∑' n : ℤ, (a - b) n * (u : K) ^ n) = 0 := by
    intro u
    have hsplit : (∑' n : ℤ, (a - b) n * (u : K) ^ n)
        = (∑' n : ℤ, a n * (u : K) ^ n) - ∑' n : ℤ, b n * (u : K) ^ n := by
      rw [← (hsa u).tsum_sub (hsb u)]
      exact tsum_congr fun n => by rw [Pi.sub_apply, sub_mul]
    rw [hsplit, heq u, sub_self]
  -- The zeros on the unit sphere are finite …
  have hZfin := hfin (a - b) hcne hcsum 1
  -- … yet each `sphereWitness k` is such a zero, and they are pairwise distinct.
  have hmem : ∀ k : ℕ, t.sphereWitness k ∈
      {u : Kˣ | ‖(u : K)‖ = 1 ∧ (∑' n : ℤ, (a - b) n * (u : K) ^ n) = 0} := by
    intro k
    exact ⟨by rw [sphereWitness_val]; exact t.norm_one_add_qpow k, hczero _⟩
  exact (Set.infinite_of_injective_forall_mem t.sphereWitness_injective hmem) hZfin

/-- **The `q`-difference engine under the Strassmann seam.** The #119 engine
`const_of_qinvariant_laurent`, with its `LaurentCoeffUnique` hypothesis replaced by
`LaurentSphereZerosFinite`: a `q`-invariant convergent Laurent series equals its constant term
`a₀` at every `u : Kˣ`. Unlike the `LaurentStrictDom` variant, the seam consumed here is not
vacuous for discretely-valued `K`. -/
theorem const_of_qinvariant_laurent_of_sphereZerosFinite (hfin : LaurentSphereZerosFinite K)
    (a : ℤ → K) (hsum : ∀ u : Kˣ, Summable fun n : ℤ => a n * (u : K) ^ n)
    (hqinv : ∀ u : Kˣ,
      (∑' n : ℤ, a n * ((t.q : K) * (u : K)) ^ n) = ∑' n : ℤ, a n * (u : K) ^ n) :
    ∀ u : Kˣ, (∑' n : ℤ, a n * (u : K) ^ n) = a 0 :=
  t.const_of_qinvariant_laurent (t.laurentCoeffUnique_of_sphereZerosFinite hfin) a hsum hqinv

end TateParameter

end TateCurvesTheta
