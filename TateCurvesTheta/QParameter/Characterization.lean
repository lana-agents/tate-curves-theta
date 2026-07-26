/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.QParameter.JParametrization
import TateCurvesTheta.TateCurve.SplitReduction

/-!
# Characterization of the Tate `q`-parameter

The capstone of issue #37: over a complete nonarchimedean field `K` (residue
characteristic `≠ 2, 3`), the assignment `q ↦ E_q` is a bijection

    { Tate parameters q, 0 < ‖q‖ < 1 }  ≃  { j : K, ‖j‖ > 1 }

realized by the `j`-invariant, and every curve `E_q` so produced has **split
multiplicative reduction**: `‖j(E_q)‖ = ‖q‖⁻¹ > 1` (`JInvariant.lean`), `q` is uniquely
determined by `j(E_q)` via the ultrametric isometry `‖j₁ - j₂‖ = ‖q₁ - q₂‖/(‖q₁‖‖q₂‖)`,
every non-integral `j` occurs (`JParametrization.lean`), and the special fibre of the
integral model is the split nodal cubic `y² + xy = x³` (`SplitReduction.lean`).

**Remaining seam (issue #36).** The classical statement "every elliptic curve over `K`
with split multiplicative reduction is isomorphic to `E_q` for this unique `q`"
additionally requires identifying an abstract curve with non-integral `j` with the
Weierstrass model `E_{q(j)}` up to `K`-isomorphism (triviality of the quadratic twist in
the split case, Silverman ATAEC V.5.3). That identification is part of the Tate
uniformization isomorphism tracked in issue #36, which this issue's statement defers to
("using the Tate-uniformization issue"); the `q`-parameter side — existence, uniqueness,
normalization and reduction behaviour of `q` itself — is complete here.

## Main results

* `TateCurvesTheta.TateParameter.existsUnique_splitMultiplicative_tateParameter`:
  for every `j` with `‖j‖ > 1` there is a unique Tate parameter with `j(E_q) = j`, and
  its Tate curve has split multiplicative reduction.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V,
  Theorems 3.1, 5.3.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* S. Mochizuki, *Inter-universal Teichmüller Theory I*, Definition 3.1(c).
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **Characterization of the Tate parameter** (issue #37): for every `j : K` with
`‖j‖ > 1` there is a *unique* Tate parameter `q` whose Tate curve has `j`-invariant `j` —
and the Tate curve of this parameter automatically has **split multiplicative
reduction**. -/
theorem existsUnique_splitMultiplicative_tateParameter (h12 : ‖(12 : K)‖ = 1) {j : K}
    (hj : 1 < ‖j‖) :
    ∃! t : TateParameter K, t.tateJ = j ∧
      ((t.tateCurveInt h12).map
        (Ideal.Quotient.mk (integerIdeal K))).IsSplitMultiplicative := by
  obtain ⟨t, ht, huniq⟩ := existsUnique_tateParameter_tateJ_eq h12 hj
  exact ⟨t, ⟨ht, t.isSplitMultiplicative_reduction h12⟩, fun t' h' => huniq t' h'.1⟩

end TateParameter

end TateCurvesTheta
