/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Field.Lemmas
import TateCurvesTheta.Theta.LaurentSphere

/-!
# Reducing finiteness of Laurent zeros on every sphere to the unit sphere

The Strassmann seam for nonarchimedean Laurent coefficient uniqueness is
`TateCurvesTheta.LaurentSphereZerosFinite K` (`Theta/LaurentSphere.lean`, #122): a nonzero
convergent two-sided Laurent series `u ↦ ∑' n, cₙ uⁿ` has only **finitely many** zeros on *each*
sphere `{u : Kˣ | ‖u‖ = ρ}`. The already-landed reduction
`laurentCoeffUnique_of_sphereZerosFinite` turns this into the full `LaurentCoeffUnique K`.

This file performs the elementary **radius normalization**: finiteness on every sphere follows
from finiteness on the *unit* sphere alone. Concretely, fixing a unit `u₀` with `‖u₀‖ = ρ` and
substituting `u = u₀ · v`, the family `cₙ uⁿ = (cₙ u₀ⁿ) · vⁿ =: dₙ vⁿ` is a nonzero
summable Laurent series whose zeros on the unit sphere `{‖v‖ = 1}` correspond, under the
bijection `v ↦ u₀ · v`, to the zeros of the original series on `{‖u‖ = ρ}`. (Empty spheres are
trivially handled.) The reduction is purely field-theoretic — it needs neither completeness nor
the ultrametric inequality — so it holds over any `NormedField K`.

This isolates the genuine analytic content into the single **unit-sphere** obligation
`LaurentUnitSphereZerosFinite K`, the honest residual: Strassmann's finiteness of zeros of a
convergent two-sided Laurent series on the unit sphere. A follow-up discharges it via the
ball-Strassmann theorem (`Analysis/Strassmann.lean`) — decomposing the unit sphere into the
finitely many residue disks that can carry a zero (the roots of the reduced maximal-term
polynomial) and, in each, recentring the two-sided series into a one-sided power series to which
ball-Strassmann applies.

## Main definitions

* `TateCurvesTheta.LaurentUnitSphereZerosFinite` : the unit-sphere finiteness-of-zeros seam.

## Main results

* `TateCurvesTheta.laurentSphereZerosFinite_of_unitSphere` :
  `LaurentUnitSphereZerosFinite K → LaurentSphereZerosFinite K`.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* A. Robert, *A Course in p-adic Analysis*, §6.2 (finiteness of zeros of a Laurent series on a
  sphere / annulus).
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
-/

namespace TateCurvesTheta

variable {K : Type*} [NormedField K]

/-- **Finiteness of zeros on the unit sphere** — the radius-normalized Strassmann seam. For every
coefficient family `c : ℤ → K` giving a summable Laurent series on all of `Kˣ` and not identically
zero, the set of units `u` with `‖u‖ = 1` at which the series vanishes is finite.

By `laurentSphereZerosFinite_of_unitSphere` this single case implies the all-radii
`LaurentSphereZerosFinite K`. -/
def LaurentUnitSphereZerosFinite (K : Type*) [NormedField K] : Prop :=
  ∀ c : ℤ → K, c ≠ 0 →
    (∀ u : Kˣ, Summable fun n : ℤ => c n * (u : K) ^ n) →
    {u : Kˣ | ‖(u : K)‖ = 1 ∧ (∑' n : ℤ, c n * (u : K) ^ n) = 0}.Finite

/-- **Radius normalization.** Finiteness of the Laurent zeros on every sphere reduces to the unit
sphere: fixing `u₀` with `‖u₀‖ = ρ` and rescaling `u = u₀ · v` sends the sphere `{‖u‖ = ρ}`
bijectively to the unit sphere `{‖v‖ = 1}` and the series `∑' cₙ uⁿ` to the series
`∑' (cₙ u₀ⁿ) vⁿ` of the nonzero, everywhere-summable family `dₙ = cₙ u₀ⁿ`. Empty spheres are
trivially finite. -/
theorem laurentSphereZerosFinite_of_unitSphere (h : LaurentUnitSphereZerosFinite K) :
    LaurentSphereZerosFinite K := by
  intro c hc hsum ρ
  by_cases hρ : ∃ u₀ : Kˣ, ‖(u₀ : K)‖ = ρ
  · obtain ⟨u₀, hu₀⟩ := hρ
    have hρpos : 0 < ρ := hu₀ ▸ norm_pos_iff.mpr (Units.ne_zero u₀)
    -- The rescaled coefficient family `dₙ = cₙ · u₀ⁿ`.
    set d : ℤ → K := fun n => c n * (u₀ : K) ^ n with hd
    -- Termwise identity: `dₙ · (v)ⁿ = cₙ · (u₀ · v)ⁿ`.
    have hterm : ∀ (v : Kˣ) (n : ℤ),
        c n * ((u₀ * v : Kˣ) : K) ^ n = d n * (v : K) ^ n := by
      intro v n
      rw [Units.val_mul, mul_zpow, hd]; ring
    -- `d` is nonzero (some `cₘ ≠ 0`, and `u₀ᵐ ≠ 0`).
    have hdne : d ≠ 0 := by
      obtain ⟨m, hm⟩ := Function.ne_iff.mp hc
      exact Function.ne_iff.mpr ⟨m, mul_ne_zero hm (zpow_ne_zero m (Units.ne_zero u₀))⟩
    -- `d` is summable on all of `Kˣ`.
    have hdsum : ∀ v : Kˣ, Summable fun n : ℤ => d n * (v : K) ^ n := by
      intro v
      exact (hsum (u₀ * v)).congr (hterm v)
    -- Finiteness of the zeros of `d` on the unit sphere.
    have hfin := h d hdne hdsum
    -- The `ρ`-sphere zeros of `c` embed into the image of the unit-sphere zeros of `d`.
    refine Set.Finite.subset (hfin.image fun v : Kˣ => u₀ * v) ?_
    rintro u ⟨hnorm, hzero⟩
    refine ⟨u₀⁻¹ * u, ⟨?_, ?_⟩, ?_⟩
    · -- `‖(u₀⁻¹ · u : K)‖ = 1`, from `‖u₀‖ · ‖u₀⁻¹ u‖ = ‖u‖ = ρ = ‖u₀‖`.
      have hval : (u₀ : K) * ((u₀⁻¹ * u : Kˣ) : K) = (u : K) := by
        rw [← Units.val_mul, mul_inv_cancel_left]
      have hnorms : ‖(u₀ : K)‖ * ‖((u₀⁻¹ * u : Kˣ) : K)‖ = ‖(u : K)‖ := by
        rw [← norm_mul, hval]
      rw [hu₀, hnorm] at hnorms
      exact mul_left_cancel₀ (ne_of_gt hρpos) (hnorms.trans (mul_one ρ).symm)
    · -- The rescaled series vanishes at `v = u₀⁻¹ u`, since it equals the original at `u`.
      have hval : (u₀ * (u₀⁻¹ * u) : Kˣ) = u := by rw [mul_inv_cancel_left]
      calc (∑' n : ℤ, d n * ((u₀⁻¹ * u : Kˣ) : K) ^ n)
          = ∑' n : ℤ, c n * ((u₀ * (u₀⁻¹ * u) : Kˣ) : K) ^ n :=
            (tsum_congr fun n => (hterm (u₀⁻¹ * u) n).symm)
        _ = ∑' n : ℤ, c n * (u : K) ^ n := by rw [hval]
        _ = 0 := hzero
    · -- `u₀ · (u₀⁻¹ · u) = u`.
      exact mul_inv_cancel_left u₀ u
  · -- No unit has norm `ρ`: the sphere is empty.
    convert Set.finite_empty
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun hnorm _ => hρ ⟨u, hnorm⟩

end TateCurvesTheta
