/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Field.Basic

/-!
# The maximum term of a summable family is attained

Over a normed additive group, a summable family `g : ι → M` that is not identically zero attains
its supremum norm: there is an index `i₀` with `g i₀ ≠ 0` and `‖g i‖ ≤ ‖g i₀‖` for every `i`.
This is elementary — summability forces `‖g i‖ → 0` along the cofinite filter, so every
superlevel set `{i | ‖g i‖ ≥ ε}` is finite and a maximum can be selected over one of them — but it
is a foundational ingredient of the nonarchimedean theory of the *maximum term* of a convergent
(Laurent) series.

Together with the dominant-term principle
`IsUltrametricDist.norm_tsum_eq_of_dominant` (`Analysis/UltrametricSum.lean`), this is the second
step of the Newton-polygon programme for nonarchimedean Laurent coefficient uniqueness (the
`LaurentStrictDom`/`LaurentCoeffUnique` seam of `Theta/LaurentUnique.lean`): at a fixed radius
`ρ = ‖u‖` the terms `‖cₙ · uⁿ‖` of a convergent Laurent series attain a maximum at some index
`n₀`. The remaining, genuinely harder Newton-polygon step is to choose the radius `u : Kˣ` so that
this maximum is attained *uniquely* (strict domination); that residual seam is `LaurentStrictDom`.

## Main results

* `Summable.exists_max_norm` : a nonzero summable family attains its supremum norm at some index.
* `TateCurvesTheta.exists_max_norm_laurent` : the specialization to a convergent Laurent family
  `n : ℤ ↦ cₙ · uⁿ` at a fixed unit `u : Kˣ`: the maximum term is attained at some index `n₀` with
  `cₙ₀ ≠ 0`.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* A. Robert, *A Course in p-adic Analysis*, §6.1 (the maximum term of a nonarchimedean series).
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, §IV (Newton polygons).
-/

open Filter Topology

/-- **The maximum term of a nonzero summable family is attained.** If `g : ι → M` is summable and
`g i₁ ≠ 0` for some `i₁`, then there is an index `i₀` at which the norm is maximal: `g i₀ ≠ 0` and
`‖g i‖ ≤ ‖g i₀‖` for every `i`.

Summability makes the norms tend to `0` along the cofinite filter, so the superlevel set
`{i | ‖g i₁‖ ≤ ‖g i‖}` is finite and nonempty (it contains `i₁`); a maximum over it dominates
every term, since outside it `‖g i‖ < ‖g i₁‖ ≤ ‖g i₀‖`. -/
theorem Summable.exists_max_norm {ι M : Type*} [NormedAddCommGroup M] {g : ι → M}
    (hg : Summable g) {i₁ : ι} (hi₁ : g i₁ ≠ 0) :
    ∃ i₀, g i₀ ≠ 0 ∧ ∀ i, ‖g i‖ ≤ ‖g i₀‖ := by
  classical
  have hpos : 0 < ‖g i₁‖ := norm_pos_iff.mpr hi₁
  -- Summability makes the norms tend to `0` along the cofinite filter.
  have htend : Tendsto (fun i => ‖g i‖) cofinite (𝓝 0) := by
    simpa using hg.tendsto_cofinite_zero.norm
  have hev : ∀ᶠ i in cofinite, ‖g i‖ < ‖g i₁‖ := htend.eventually (Iio_mem_nhds hpos)
  -- Hence the superlevel set `{i | ‖g i₁‖ ≤ ‖g i‖}` is finite.
  have hfin : {i | ‖g i₁‖ ≤ ‖g i‖}.Finite := by
    refine (eventually_cofinite.mp hev).subset fun i hi => ?_
    simpa only [Set.mem_setOf_eq, not_lt] using hi
  have hmem₁ : i₁ ∈ {i | ‖g i₁‖ ≤ ‖g i‖} := le_refl ‖g i₁‖
  have hne : hfin.toFinset.Nonempty := ⟨i₁, hfin.mem_toFinset.mpr hmem₁⟩
  -- Take the argmax over the finite superlevel set.
  obtain ⟨i₀, hi₀mem, hi₀max⟩ := hfin.toFinset.exists_max_image (fun i => ‖g i‖) hne
  have hi₀S : ‖g i₁‖ ≤ ‖g i₀‖ := hfin.mem_toFinset.mp hi₀mem
  refine ⟨i₀, norm_pos_iff.mp (lt_of_lt_of_le hpos hi₀S), fun i => ?_⟩
  by_cases hi : i ∈ hfin.toFinset
  · exact hi₀max i hi
  · -- Outside the superlevel set the term is already dominated by `‖g i₁‖ ≤ ‖g i₀‖`.
    have hlt : ‖g i‖ < ‖g i₁‖ := by
      by_contra h
      exact hi (hfin.mem_toFinset.mpr (not_lt.mp h))
    exact le_trans hlt.le hi₀S

namespace TateCurvesTheta

/-- **The maximum term of a convergent Laurent series is attained.** At a fixed radius (a unit
`u : Kˣ`), if the two-sided family `n ↦ cₙ · uⁿ` is summable and some coefficient `cₘ ≠ 0`, then
the term of maximal norm is attained at an index `n₀` with `cₙ₀ ≠ 0`:
`‖cₙ · uⁿ‖ ≤ ‖cₙ₀ · uⁿ₀‖` for every `n`.

This is the fixed-radius maximum-term selection feeding the Newton-polygon vertex step of the
`LaurentStrictDom` seam in `Theta/LaurentUnique.lean`. -/
theorem exists_max_norm_laurent {K : Type*} [NormedField K] {c : ℤ → K} {u : Kˣ}
    (hsum : Summable fun n : ℤ => c n * (u : K) ^ n) {m : ℤ} (hm : c m ≠ 0) :
    ∃ n₀ : ℤ, c n₀ ≠ 0 ∧ ∀ n : ℤ, ‖c n * (u : K) ^ n‖ ≤ ‖c n₀ * (u : K) ^ n₀‖ := by
  have hu : (u : K) ≠ 0 := u.ne_zero
  have hm' : c m * (u : K) ^ m ≠ 0 := mul_ne_zero hm (zpow_ne_zero m hu)
  obtain ⟨n₀, hn₀, hmax⟩ := hsum.exists_max_norm hm'
  exact ⟨n₀, left_ne_zero_of_mul hn₀, hmax⟩

end TateCurvesTheta
