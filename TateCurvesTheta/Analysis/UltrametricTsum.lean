/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# The ultrametric maximum-modulus principle for convergent sums

In a nonarchimedean (ultrametric) normed additive group, a convergent sum is measured by its
single strictly dominant term: if `f : ι → M` is summable and one index `i₀` strictly dominates
all the others in norm (`‖f i‖ < ‖f i₀‖` for `i ≠ i₀`), then

`‖∑' i, f i‖ = ‖f i₀‖`.

Mathlib provides the finite analogue (`IsUltrametricDist.norm_sum_eq_sup'_of_pairwise_ne`) and the
infinite-sum *inequality* `‖∑' i, f i‖ ≤ ⨆ i, ‖f i‖` (`IsUltrametricDist.norm_tsum_le`), but not the
equality under a unique strict maximum. That equality is the maximum-modulus kernel of the
nonarchimedean identity theorem for Laurent series (`LaurentCoeffUnique`, see
`TateCurvesTheta/Theta/Uniqueness.lean`): applied to the family `n ↦ cₙ · uⁿ` on `ℤ`, a Laurent
series whose leading term dominates at `u` has `‖∑' n, cₙ uⁿ‖ = ‖c_{n₀}‖ · ‖u‖ ^ n₀ ≠ 0`.

## Main result

* `TateCurvesTheta.norm_tsum_eq_of_dominant` : `‖∑' i, f i‖ = ‖f i₀‖` for a summable ultrametric
  family with a strictly dominant term at `i₀`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, §IV (the nonarchimedean
  maximum-modulus principle).
-/

open Filter Topology

namespace TateCurvesTheta

variable {ι M : Type*} [NormedAddCommGroup M] [IsUltrametricDist M]

/-- **Ultrametric maximum-modulus principle for convergent sums.** If `f : ι → M` is summable and
the index `i₀` strictly dominates every other index in norm, then the norm of the sum equals the
norm of that dominant term: `‖∑' i, f i‖ = ‖f i₀‖`.

The proof splits off the dominant term, `∑' i, f i = f i₀ + ∑' i, (if i = i₀ then 0 else f i)`, and
bounds the remainder strictly below `‖f i₀‖` (the summable family tends to `0` along `cofinite`, so
only finitely many terms come within `‖f i₀‖/2` of the dominant one, and those are all strictly
smaller). The isosceles law `norm_add_eq_max_of_norm_ne_norm` then pins the total norm to the
dominant term. -/
theorem norm_tsum_eq_of_dominant {f : ι → M} (hf : Summable f) {i₀ : ι}
    (hlt : ∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) :
    ‖∑' i, f i‖ = ‖f i₀‖ := by
  classical
  set r : ℝ := ‖f i₀‖ with hrdef
  rcases eq_or_lt_of_le (norm_nonneg (f i₀)) with hr | hr
  · -- Degenerate case `‖f i₀‖ = 0`: the strict domination forces every other term to vanish.
    have hsingle : ∑' i, f i = f i₀ := by
      refine tsum_eq_single i₀ fun b hb => ?_
      have hb0 : ‖f b‖ < 0 := by rw [hr]; exact hlt b hb
      exact absurd hb0 (not_lt.2 (norm_nonneg _))
    rw [hsingle]
  · -- Main case `0 < ‖f i₀‖`.
    -- The summable family tends to `0` along `cofinite`, so `{i | r/2 ≤ ‖f i‖}` is finite.
    have htend : Tendsto (fun i => ‖f i‖) cofinite (𝓝 0) := by
      simpa using hf.tendsto_cofinite_zero.norm
    have hmem : {i | ‖f i‖ < r / 2} ∈ (cofinite : Filter ι) :=
      htend (Iio_mem_nhds (half_pos hr))
    have hfin : {i : ι | r / 2 ≤ ‖f i‖}.Finite := by
      have hc := Filter.mem_cofinite.mp hmem
      apply hc.subset
      intro i hi
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
      exact hi
    set S := hfin.toFinset with hS
    have hi₀S : i₀ ∈ S := hfin.mem_toFinset.mpr (half_le_self hr.le)
    -- The remainder family, with the dominant term removed.
    set g : ι → M := fun i => if i = i₀ then 0 else f i with hg
    have hgi₀ : g i₀ = 0 := if_pos rfl
    have hgne : ∀ i, i ≠ i₀ → g i = f i := fun i h => if_neg h
    -- Every remainder term is strictly smaller than the dominant one.
    have hgr : ∀ i, ‖g i‖ < r := by
      intro i
      by_cases hie : i = i₀
      · rw [hie, hgi₀, norm_zero]; exact hr
      · rw [hgne i hie]; exact hlt i hie
    -- On the finite "near" set `S`, the remainder norm attains a maximum `< r`.
    obtain ⟨j, _, hjmax⟩ := S.exists_max_image (fun i => ‖g i‖) ⟨i₀, hi₀S⟩
    -- A single bound `C < r` dominating every remainder term.
    have hCr : max ‖g j‖ (r / 2) < r := max_lt (hgr j) (half_lt_self hr)
    have hC0 : 0 ≤ max ‖g j‖ (r / 2) := le_trans (norm_nonneg _) (le_max_left _ _)
    have hbound : ∀ i, ‖g i‖ ≤ max ‖g j‖ (r / 2) := by
      intro i
      by_cases hiS : i ∈ S
      · exact le_trans (hjmax i hiS) (le_max_left _ _)
      · have hine : i ≠ i₀ := fun h => hiS (h ▸ hi₀S)
        rw [hgne i hine]
        have hlt2 : ‖f i‖ < r / 2 :=
          not_le.mp fun hcon => hiS (hfin.mem_toFinset.mpr hcon)
        exact le_trans hlt2.le (le_max_right _ _)
    -- Split off the dominant term and apply the isosceles law.
    have hsplit : ∑' i, f i = f i₀ + ∑' i, g i := hf.tsum_eq_add_tsum_ite i₀
    have hrem : ‖∑' i, g i‖ ≤ max ‖g j‖ (r / 2) :=
      IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC0 hbound
    have hremlt : ‖∑' i, g i‖ < r := lt_of_le_of_lt hrem hCr
    rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hremlt.ne',
      max_eq_left hremlt.le]

end TateCurvesTheta
