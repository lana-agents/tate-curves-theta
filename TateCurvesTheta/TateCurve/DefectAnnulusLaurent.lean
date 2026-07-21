/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.TateCurve.CoordinateAnnulusLaurent
import TateCurvesTheta.TateCurve.CoordinateAnnulusLaurentY
import TateCurvesTheta.TateCurve.WeierstrassIdentity
import TateCurvesTheta.Theta.ThetaProdGlobalLaurent

/-!
# The Weierstrass defect as a two-sided Laurent series on the fundamental annulus

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the coordinates
`X`, `Y` develop as explicit two-sided Laurent series on the fundamental annulus
`1 < ‖u‖ < ‖q‖⁻¹` (`TateCurve/CoordinateAnnulusLaurent.lean` (`X`) and
`TateCurve/CoordinateAnnulusLaurentY.lean` (`Y`), steps 2–3 of #146). This file is **step 4**: it
Cauchy-products those developments into a two-sided Laurent development of the **Weierstrass
defect** `tateDefect u = Y(u)² + X(u)·Y(u) − (X(u)³ + a₄·X(u) + a₆)` on the same annulus.

## The mechanism

The reusable nonarchimedean Cauchy product `TateParameter.hasSum_laurentConvolution`
(`Theta/ThetaProdGlobalLaurent.lean`, #148/PR #37) turns two convergent two-sided Laurent series
`∑ αₙ uⁿ = A`, `∑ βₘ uᵐ = B` at a fixed `u` into the convolution series `∑ₗ (∑ₘ α(ℓ−m)·βₘ) uˡ = A·B`
— *no norm estimate on the resulting coefficients is required*, only that both factors converge at
`u`. On the fundamental annulus both `X(u)` and `Y(u)` converge, so applying the engine gives the
annulus developments of `Y²`, `X·Y`, `X²` (and, chaining once more, `X³ = X²·X`) with **explicit,
`u`-independent** convolution coefficients built from `XLaurentCoeff`/`YLaurentCoeff`. Adding the
linear term `a₄·X` and the constant `a₆` assembles `tateDefect` as the two-sided Laurent series
```
tateDefect u = ∑' ℓ : ℤ, defectAnnulusCoeff ℓ · uˡ      (1 < ‖u‖ < ‖q‖⁻¹).
```

## What remains (the residual analytic crux of #146)

This is a development **valid only on the fundamental annulus**. The genuine remaining content of
`DefectLaurentRepr` (`TateCurve/TatePointMem.lean`) is the **pole cancellation**: while the
individual coordinate coefficients grow (linearly in `|m|`, so `X`, `Y` carry real `qᶻ`-poles and
converge only on the annulus), the specific algebraic combination `Y²+XY−X³−a₄X−a₆` has its
`qᶻ`-poles cancel, so `defectAnnulusCoeff` in fact decays super-geometrically in **both** directions
and the series above converges on **all** of `Kˣ` (global summability), agrees with the defect at
every off-orbit point, and is `q`-invariant. That coefficient-level cancellation — which
`hasSum_laurentConvolution` does *not* see, exactly as diagnosed for the individual coordinates — is
the analytic seam still to be discharged to close `DefectLaurentRepr` and unblock the Tate
parametrization subtree (#116/#117/#118).

## Main definitions

* `TateCurvesTheta.TateParameter.defectAnnulusCoeff`: the explicit convolution coefficients of the
  annulus Laurent development of the Weierstrass defect.

## Main results

* `TateParameter.tateDefect_hasSum_laurent`: on the fundamental annulus,
  `tateDefect u = ∑' ℓ, defectAnnulusCoeff ℓ · uˡ`, a convergent two-sided Laurent series.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* A. Robert, *A Course in p-adic Analysis*, §6 (convergent Laurent series on annuli).
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K) (u : Kˣ)

/-- **Coefficients of the annulus Laurent development of the Weierstrass defect.** The `ℓ`-th
coefficient is the algebraic combination `Y²+XY−X³−a₄X−a₆` at the coefficient level: the
nonarchimedean convolutions of `YLaurentCoeff`/`XLaurentCoeff` for the quadratic/cubic terms, the
scaled `a₄·XLaurentCoeff` for the linear term, and `a₆` in degree `0`. All coefficients are
`u`-independent. -/
def defectAnnulusCoeff (ℓ : ℤ) : K :=
  (∑' m : ℤ, t.YLaurentCoeff (ℓ - m) * t.YLaurentCoeff m)
    + (∑' m : ℤ, t.XLaurentCoeff (ℓ - m) * t.YLaurentCoeff m)
    - (∑' m : ℤ, (∑' k : ℤ, t.XLaurentCoeff (ℓ - m - k) * t.XLaurentCoeff k) * t.XLaurentCoeff m)
    - t.a₄ * t.XLaurentCoeff ℓ
    - (if ℓ = 0 then t.a₆ else 0)

/-- **The Weierstrass defect as a two-sided Laurent series on the fundamental annulus.** For
`1 < ‖u‖` and `‖q‖·‖u‖ < 1` (equivalently `1 < ‖u‖ < ‖q‖⁻¹`),
`tateDefect u = ∑' ℓ : ℤ, defectAnnulusCoeff ℓ · uˡ`, obtained by nonarchimedean Cauchy products of
the coordinate developments `X_hasSum_laurent`/`Y_hasSum_laurent`. This is step 4 of the
pole-cancellation Laurent development of the defect (#146); the resulting series converges globally
only after the `qᶻ`-pole cancellation, which is the residual analytic seam. -/
theorem tateDefect_hasSum_laurent (h1 : 1 < ‖(u : K)‖) (h2 : ‖(t.q : K)‖ * ‖(u : K)‖ < 1) :
    HasSum (fun ℓ : ℤ => t.defectAnnulusCoeff ℓ * (u : K) ^ ℓ) (t.tateDefect u) := by
  have hX := t.X_hasSum_laurent u h1 h2
  have hY := t.Y_hasSum_laurent u h1 h2
  -- Quadratic terms via the nonarchimedean Cauchy product engine.
  have hYY := hasSum_laurentConvolution u hY hY
  have hXY := hasSum_laurentConvolution u hX hY
  -- `X²`, packaged with an explicit coefficient family so the next convolution unifies cleanly.
  have hXX : HasSum
      (fun ℓ : ℤ => (∑' m : ℤ, t.XLaurentCoeff (ℓ - m) * t.XLaurentCoeff m) * (u : K) ^ ℓ)
      (t.X u * t.X u) := hasSum_laurentConvolution u hX hX
  -- `X³ = X²·X`.
  have hXXX := hasSum_laurentConvolution u hXX hX
  -- The linear term `a₄·X`.
  have ha4X : HasSum (fun ℓ : ℤ => (t.a₄ * t.XLaurentCoeff ℓ) * (u : K) ^ ℓ) (t.a₄ * t.X u) := by
    have hfun : (fun ℓ : ℤ => t.a₄ * (t.XLaurentCoeff ℓ * (u : K) ^ ℓ))
        = fun ℓ : ℤ => (t.a₄ * t.XLaurentCoeff ℓ) * (u : K) ^ ℓ := by
      funext ℓ; ring
    exact hfun ▸ hX.mul_left t.a₄
  -- The constant term `a₆`, in degree `0`.
  have ha6 : HasSum (fun ℓ : ℤ => (if ℓ = 0 then t.a₆ else 0) * (u : K) ^ ℓ) t.a₆ := by
    have hfun : (fun ℓ : ℤ => if ℓ = 0 then t.a₆ else (0 : K))
        = fun ℓ : ℤ => (if ℓ = 0 then t.a₆ else 0) * (u : K) ^ ℓ := by
      funext ℓ
      by_cases hℓ : ℓ = 0
      · subst hℓ; simp
      · simp [hℓ]
    exact hfun ▸ hasSum_ite_eq (0 : ℤ) t.a₆
  -- Assemble `Y² + XY − X³ − a₄X − a₆`.
  have hcomb := (((hYY.add hXY).sub hXXX).sub ha4X).sub ha6
  -- The value is the Weierstrass defect.
  have hval : t.Y u * t.Y u + t.X u * t.Y u - t.X u * t.X u * t.X u - t.a₄ * t.X u - t.a₆
      = t.tateDefect u := by
    rw [tateDefect_apply]; ring
  -- The summed coefficient function is `defectAnnulusCoeff`, after factoring out `uˡ`.
  have hfun : (fun ℓ : ℤ =>
        (∑' m : ℤ, t.YLaurentCoeff (ℓ - m) * t.YLaurentCoeff m) * (u : K) ^ ℓ
          + (∑' m : ℤ, t.XLaurentCoeff (ℓ - m) * t.YLaurentCoeff m) * (u : K) ^ ℓ
          - (∑' m : ℤ, (∑' k : ℤ, t.XLaurentCoeff (ℓ - m - k) * t.XLaurentCoeff k)
              * t.XLaurentCoeff m) * (u : K) ^ ℓ
          - (t.a₄ * t.XLaurentCoeff ℓ) * (u : K) ^ ℓ
          - (if ℓ = 0 then t.a₆ else 0) * (u : K) ^ ℓ)
      = fun ℓ : ℤ => t.defectAnnulusCoeff ℓ * (u : K) ^ ℓ := by
    funext ℓ
    simp only [defectAnnulusCoeff]
    ring
  rw [← hval, ← hfun]
  exact hcomb

end TateParameter

end TateCurvesTheta
