/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# The dominant-term principle for ultrametric infinite sums

Over a complete ultrametric normed group, a summable family with a **strictly dominant** term
has its sum controlled by that term: if `‖g i₀‖ > ‖g i‖` for every `i ≠ i₀`, then
`‖∑' i, g i‖ = ‖g i₀‖`. In particular such a sum is nonzero whenever the dominant term is.

This is the additive/`tsum` analogue of the ultrametric "isosceles" principle
`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, extended from two summands to an infinite
summable family. It is the reusable analytic core behind nonarchimedean coefficient uniqueness
for convergent Laurent series (a `∑' n : ℤ, cₙ uⁿ` that vanishes on all of `Kˣ` must have all
`cₙ = 0`): picking a radius `‖u‖` at which one coefficient strictly dominates forces that
coefficient to vanish.

## Main results

* `IsUltrametricDist.norm_tsum_eq_of_dominant` : for a summable `g : ι → M` with a strictly
  dominant term at `i₀`, `‖∑' i, g i‖ = ‖g i₀‖`.
* `IsUltrametricDist.tsum_ne_zero_of_dominant` : the same hypotheses with `g i₀ ≠ 0` give
  `∑' i, g i ≠ 0`.

## Implementation notes

The tail `∑' i, (if i = i₀ then 0 else g i)` is bounded strictly below `‖g i₀‖` by combining:
* `Summable.tendsto_cofinite_zero`, so `{i | ‖g i‖ ≥ ‖g i₀‖}`-type superlevel sets are finite and
  the tail admits a *uniform* bound `C < ‖g i₀‖` (finite max over the superlevel set, else a
  fixed fraction of `‖g i₀‖`);
* `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg` to push that bound through the `tsum`;
* `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm` to conclude via the isosceles law.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* A. Robert, *A Course in p-adic Analysis*, §6.1 (nonarchimedean series and the maximum term).
-/

open Filter Topology

namespace IsUltrametricDist

variable {ι : Type*} {M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M] [CompleteSpace M]

set_option linter.unusedSectionVars false in
/-- **Uniform strict bound on the non-dominant part.** If `g` is summable and `‖g i‖ < r` for
every `i` while `0 < r`, and moreover the family decays (which summability supplies), there is a
single `C < r` bounding every `‖g i‖`. Stated for the `if`-masked family so it can bound the
tail of a dominant-term decomposition. -/
theorem exists_uniform_bound_lt_of_summable {g : ι → M} (hg : Summable g) {r : ℝ} (hr : 0 < r)
    (hlt : ∀ i, ‖g i‖ < r) : ∃ C, C < r ∧ ∀ i, ‖g i‖ ≤ C := by
  classical
  have hr2 : (0 : ℝ) < r / 2 := by positivity
  -- Summability makes the norms tend to `0` along the cofinite filter.
  have htend : Tendsto (fun i => ‖g i‖) cofinite (𝓝 0) := by
    simpa using hg.tendsto_cofinite_zero.norm
  have hev : ∀ᶠ i in cofinite, ‖g i‖ < r / 2 := htend.eventually (Iio_mem_nhds hr2)
  -- Hence the superlevel set `{i | r / 2 ≤ ‖g i‖}` is finite.
  have hfin : {i | ¬ ‖g i‖ < r / 2}.Finite := eventually_cofinite.mp hev
  by_cases hne : hfin.toFinset.Nonempty
  · -- Take the max of `r / 2` and the finite maximum over the superlevel set.
    refine ⟨max (r / 2) (hfin.toFinset.sup' hne (fun i => ‖g i‖)), ?_, ?_⟩
    · exact max_lt (by linarith) ((Finset.sup'_lt_iff hne).mpr (fun i _ => hlt i))
    · intro i
      by_cases hi : i ∈ hfin.toFinset
      · exact le_trans (Finset.le_sup' (fun i => ‖g i‖) hi) (le_max_right _ _)
      · have hlt2 : ‖g i‖ < r / 2 := by
          by_contra h
          exact hi (hfin.mem_toFinset.mpr h)
        exact le_trans hlt2.le (le_max_left _ _)
  · -- The superlevel set is empty, so `r / 2` already bounds everything.
    refine ⟨r / 2, by linarith, fun i => ?_⟩
    have hlt2 : ‖g i‖ < r / 2 := by
      by_contra h
      exact hne ⟨i, hfin.mem_toFinset.mpr h⟩
    exact hlt2.le

/-- **Dominant-term principle for ultrametric sums.** For a summable family `g : ι → M` over a
complete ultrametric normed additive group, if the term at `i₀` strictly dominates all others in
norm (`‖g i‖ < ‖g i₀‖` for `i ≠ i₀`), then the whole sum has norm exactly `‖g i₀‖`. -/
theorem norm_tsum_eq_of_dominant {g : ι → M} (hg : Summable g) {i₀ : ι}
    (hdom : ∀ i, i ≠ i₀ → ‖g i‖ < ‖g i₀‖) : ‖∑' i, g i‖ = ‖g i₀‖ := by
  classical
  by_cases hz : g i₀ = 0
  · -- If the dominant term is zero, every term is zero and so is the sum.
    have hall : ∀ i, g i = 0 := by
      intro i
      rcases eq_or_ne i i₀ with hi | hi
      · rw [hi]; exact hz
      · have := hdom i hi
        rw [hz, norm_zero] at this
        exact absurd (norm_nonneg _) (not_le.mpr this)
    rw [tsum_congr hall, tsum_zero, hz]
  · have hpos : 0 < ‖g i₀‖ := norm_pos_iff.mpr hz
    -- Mask out the dominant term; the remaining family is summable.
    have hupd : Summable (Function.update g i₀ 0) := hg.update i₀ 0
    have hlt : ∀ i, ‖Function.update g i₀ 0 i‖ < ‖g i₀‖ := by
      intro i
      rcases eq_or_ne i i₀ with hi | hi
      · simpa [hi] using hpos
      · rw [Function.update_of_ne hi]
        exact hdom i hi
    -- Uniformly bound the tail strictly below `‖g i₀‖`.
    obtain ⟨C, hClt, hCbd⟩ := exists_uniform_bound_lt_of_summable hupd hpos hlt
    have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hCbd i₀)
    have htlt : ‖∑' i, Function.update g i₀ 0 i‖ < ‖g i₀‖ :=
      lt_of_le_of_lt (norm_tsum_le_of_forall_le_of_nonneg hCnn hCbd) hClt
    -- Split off the dominant term and apply the isosceles law.
    have hdecomp : ∑' i, g i = g i₀ + ∑' i, Function.update g i₀ 0 i := by
      rw [hg.tsum_eq_add_tsum_ite i₀]
      congr 1
      exact tsum_congr (fun i => (Function.update_apply g i₀ 0 i).symm)
    rw [hdecomp, norm_add_eq_max_of_norm_ne_norm (ne_of_gt htlt), max_eq_left htlt.le]

/-- **A dominant-term ultrametric sum is nonzero.** If `g` is summable, `g i₀ ≠ 0`, and `i₀`
strictly dominates every other term in norm, then `∑' i, g i ≠ 0`. -/
theorem tsum_ne_zero_of_dominant {g : ι → M} (hg : Summable g) {i₀ : ι} (hi₀ : g i₀ ≠ 0)
    (hdom : ∀ i, i ≠ i₀ → ‖g i‖ < ‖g i₀‖) : ∑' i, g i ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_tsum_eq_of_dominant hg hdom]
  exact norm_ne_zero_iff.mpr hi₀

end IsUltrametricDist
