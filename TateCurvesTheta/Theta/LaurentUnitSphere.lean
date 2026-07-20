/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.Analysis.StrassmannSphere
import TateCurvesTheta.Theta.LaurentSphereReduce
import TateCurvesTheta.Theta.LaurentSphere

/-!
# Discharging the unit-sphere Strassmann seam and unconditional Laurent coefficient uniqueness

This file closes the last residual analytic seam behind the nonarchimedean `q`-difference engine.
The two-sided Strassmann theorem `StrassmannSphere.finite_zeros` (`Analysis/StrassmannSphere.lean`)
discharges `LaurentUnitSphereZerosFinite K` (`Theta/LaurentSphereReduce.lean`, #136): a nonzero
convergent Laurent series has finitely many zeros on the unit sphere. Combined with the radius
normalization `laurentSphereZerosFinite_of_unitSphere` (#27) and the elementary reduction
`laurentCoeffUnique_of_sphereZerosFinite` (#23), this makes `LaurentCoeffUnique K` — and the whole
engine `const_of_qinvariant_laurent` — **unconditional** for the project's abstract `K` (complete,
ultrametric), including the discretely-valued case `ℚₚ` that `LaurentStrictDom` cannot reach.

## Main results

* `TateCurvesTheta.laurentUnitSphereZerosFinite` : `LaurentUnitSphereZerosFinite K` (the #136 seam).
* `TateCurvesTheta.laurentSphereZerosFinite` : `LaurentSphereZerosFinite K`, unconditionally.
* `TateCurvesTheta.TateParameter.laurentCoeffUnique` : `LaurentCoeffUnique K`, unconditionally.
* `TateCurvesTheta.TateParameter.const_of_qinvariant_laurent'` : the #119 engine with **no**
  side hypothesis — a `q`-invariant convergent Laurent series equals its constant term.

## References

* A. Robert, *A Course in p-adic Analysis*, §6.2 (finiteness of zeros of a Laurent series).
* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
-/

namespace TateCurvesTheta

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- **The unit-sphere Strassmann seam is discharged.** A nonzero coefficient family whose Laurent
series is summable on all of `Kˣ` has finitely many zeros on the unit sphere. This is the #136
obligation, proved from the two-sided Strassmann theorem `StrassmannSphere.finite_zeros`. -/
theorem laurentUnitSphereZerosFinite : LaurentUnitSphereZerosFinite K := by
  intro c hc0 hsum
  -- Summability on `Kˣ` at `u = 1` gives summability of the raw coefficient family.
  have hc : Summable c := by
    have h := hsum 1
    simpa using h
  have hfin := StrassmannSphere.finite_zeros hc hc0
  -- Transfer the finite `K`-side zero set back to the units via the injection `u ↦ (u : K)`.
  refine Set.Finite.of_finite_image ?_ (fun a _ b _ h => Units.ext h)
  refine hfin.subset ?_
  rintro v ⟨u, ⟨hu1, huz⟩, rfl⟩
  exact ⟨hu1, huz⟩

/-- **Finiteness of Laurent zeros on every sphere**, unconditionally (via radius normalization). -/
theorem laurentSphereZerosFinite : LaurentSphereZerosFinite K :=
  laurentSphereZerosFinite_of_unitSphere laurentUnitSphereZerosFinite

namespace TateParameter

/-- **Nonarchimedean Laurent coefficient uniqueness, unconditionally.** A convergent two-sided
Laurent series over the complete ultrametric field `K` is determined by its values on `Kˣ`. This
discharges the standing `LaurentCoeffUnique K` hypothesis of the `q`-difference engine for the
project's abstract `K`. -/
theorem laurentCoeffUnique (t : TateParameter K) : LaurentCoeffUnique K :=
  laurentCoeffUnique_of_sphereZerosFinite t laurentSphereZerosFinite

/-- **The `q`-difference engine, unconditionally.** A `q`-invariant convergent Laurent series
equals its constant term `a 0` at every `u : Kˣ` — with no analytic side hypothesis, since
`LaurentCoeffUnique K` is now a theorem. -/
theorem const_of_qinvariant_laurent' (t : TateParameter K) (a : ℤ → K)
    (hsum : ∀ u : Kˣ, Summable fun n : ℤ => a n * (u : K) ^ n)
    (hqinv : ∀ u : Kˣ,
      (∑' n : ℤ, a n * ((t.q : K) * (u : K)) ^ n) = ∑' n : ℤ, a n * (u : K) ^ n) :
    ∀ u : Kˣ, (∑' n : ℤ, a n * (u : K) ^ n) = a 0 :=
  t.const_of_qinvariant_laurent (laurentCoeffUnique t) a hsum hqinv

end TateParameter

end TateCurvesTheta
