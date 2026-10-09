/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Eisenstein kernels and their pair identities

The classical elementary proof of the Tate Weierstrass identity (Silverman, *Advanced
Topics*, Ch. V, Thm 3.1; Weil, *Elliptic Functions According to Eisenstein and Kronecker*)
manipulates the rational **Eisenstein kernels**
```
p(x) = x/(1-x)²,   r(x) = x(1+x)/(1-x)³,   z(x) = (1+x)/(1-x),
φ(x) = x(1+4x+x²)/(1-x)⁴,   ψ(x) = x(1+11x+11x²+x³)/(1-x)⁵,   ψ₃(x) = x(2x+1)/(1-x)⁴,
```
the generating functions of the power weights `∑ₖ kʲ xᵏ` for `j = 1, 2, 3, 4` (`p`, `r`,
`φ`, `ψ`) together with the odd degree-one kernel `z`. This file records, as pure rational
identities over an arbitrary field, everything the analytic development consumes:

* the **inversion parities** under `x ↦ x⁻¹` (`p`, `φ` even; `r`, `z`, `ψ` odd; `ψ₃`
  averages to `φ`);
* the **nodal-cubic relation** `r² = 4p³ + p²` — the single-term Weierstrass equation;
* the three **pair identities** decomposing the products `p(tv)·p(v)`, `r(tv)·r(v)` and
  `p(tv)²·p(v)` into linear combinations of kernels at `v` and at `w = tv` with
  coefficients that are kernels at the ratio `t` — the partial-fraction identities of
  Eisenstein's method. They are stated in denominator-free form (multiplied by `2`), so
  all coefficients are integral.

Everything here is field algebra: no topology, no norms, no convergence. The analytic
files sum these identities over the `qᶻ`-orbit of a point.

## Main results

* `TateCurvesTheta.eisP_inv`, `eisR_inv`, `eisZ_inv`, `eisPhi_inv`, `eisPsi_inv`,
  `eisPsi3_add_inv`: inversion parities.
* `TateCurvesTheta.eisR_sq`: the nodal relation `r² = 4p³ + p²`.
* `TateCurvesTheta.eisP_mul_eisP`, `eisR_mul_eisR`, `eisP_sq_mul_eisP`: the pair
  identities.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* A. Weil, *Elliptic Functions According to Eisenstein and Kronecker*.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

namespace TateCurvesTheta

variable {K : Type*} [Field K]

/-- The Eisenstein kernel `p(x) = x/(1-x)²`, generating function of `∑ₖ k xᵏ`: the
single-term Tate `X`-coordinate. -/
def eisP (x : K) : K := x / (1 - x) ^ 2

/-- The Eisenstein kernel `r(x) = x(1+x)/(1-x)³`, generating function of `∑ₖ k² xᵏ`: the
single-term `2Y + X` combination (the "`℘'`-like" odd kernel). -/
def eisR (x : K) : K := x * (1 + x) / (1 - x) ^ 3

/-- The odd degree-one Eisenstein kernel `z(x) = (1+x)/(1-x)`, whose shifted differences
telescope over the `qᶻ`-orbit. -/
def eisZ (x : K) : K := (1 + x) / (1 - x)

/-- The Eisenstein kernel `φ(x) = x(1+4x+x²)/(1-x)⁴`, generating function of `∑ₖ k³ xᵏ`. -/
def eisPhi (x : K) : K := x * (1 + 4 * x + x ^ 2) / (1 - x) ^ 4

/-- The Eisenstein kernel `ψ(x) = x(1+11x+11x²+x³)/(1-x)⁵`, generating function of
`∑ₖ k⁴ xᵏ`. -/
def eisPsi (x : K) : K := x * (1 + 11 * x + 11 * x ^ 2 + x ^ 3) / (1 - x) ^ 5

/-- The auxiliary Eisenstein kernel `ψ₃(x) = x(2x+1)/(1-x)⁴`; it has no parity, but
`ψ₃(x) + ψ₃(x⁻¹) = φ(x)` (`eisPsi3_add_inv`). -/
def eisPsi3 (x : K) : K := x * (2 * x + 1) / (1 - x) ^ 4

lemma eisP_def (x : K) : eisP x = x / (1 - x) ^ 2 := rfl
lemma eisR_def (x : K) : eisR x = x * (1 + x) / (1 - x) ^ 3 := rfl
lemma eisZ_def (x : K) : eisZ x = (1 + x) / (1 - x) := rfl

private lemma one_sub_ne_zero {x : K} (h : x ≠ 1) : (1 : K) - x ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm h)

private lemma one_sub_inv_ne_zero {x : K} (hx1 : x ≠ 1) : (1 : K) - x⁻¹ ≠ 0 :=
  sub_ne_zero.mpr fun h => hx1 (by rwa [eq_comm, inv_eq_one] at h)

section Parity

variable {x : K} (hx0 : x ≠ 0) (hx1 : x ≠ 1)
include hx0 hx1

/-- The kernel `p` is even under inversion: `p(x⁻¹) = p(x)`. -/
lemma eisP_inv : eisP x⁻¹ = eisP x := by
  have h1 : (1 : K) - x ≠ 0 := one_sub_ne_zero (K := K) hx1
  have hinv : (1 : K) - x⁻¹ = -((1 - x) / x) := by field_simp; ring
  rw [eisP, eisP, hinv]
  field_simp

/-- The kernel `r` is odd under inversion: `r(x⁻¹) = -r(x)`. -/
lemma eisR_inv : eisR x⁻¹ = -eisR x := by
  have h1 : (1 : K) - x ≠ 0 := one_sub_ne_zero (K := K) hx1
  have hinv : (1 : K) - x⁻¹ = -((1 - x) / x) := by field_simp; ring
  rw [eisR, eisR, hinv]
  field_simp
  ring

/-- The kernel `z` is odd under inversion: `z(x⁻¹) = -z(x)`. -/
lemma eisZ_inv : eisZ x⁻¹ = -eisZ x := by
  have h1 : (1 : K) - x ≠ 0 := one_sub_ne_zero (K := K) hx1
  have hinv : (1 : K) - x⁻¹ = -((1 - x) / x) := by field_simp; ring
  rw [eisZ, eisZ, hinv]
  field_simp
  ring

/-- The kernel `φ` is even under inversion: `φ(x⁻¹) = φ(x)`. -/
lemma eisPhi_inv : eisPhi x⁻¹ = eisPhi x := by
  have h1 : (1 : K) - x ≠ 0 := one_sub_ne_zero (K := K) hx1
  have hinv : (1 : K) - x⁻¹ = -((1 - x) / x) := by field_simp; ring
  rw [eisPhi, eisPhi, hinv]
  field_simp
  ring

/-- The kernel `ψ` is odd under inversion: `ψ(x⁻¹) = -ψ(x)`. -/
lemma eisPsi_inv : eisPsi x⁻¹ = -eisPsi x := by
  have h1 : (1 : K) - x ≠ 0 := one_sub_ne_zero (K := K) hx1
  have hinv : (1 : K) - x⁻¹ = -((1 - x) / x) := by field_simp; ring
  rw [eisPsi, eisPsi, hinv]
  field_simp
  ring

/-- The kernel `ψ₃` averages to `φ` under inversion: `ψ₃(x) + ψ₃(x⁻¹) = φ(x)`. -/
lemma eisPsi3_add_inv : eisPsi3 x + eisPsi3 x⁻¹ = eisPhi x := by
  have h1 : (1 : K) - x ≠ 0 := one_sub_ne_zero (K := K) hx1
  have hinv : (1 : K) - x⁻¹ = -((1 - x) / x) := by field_simp; ring
  rw [eisPsi3, eisPsi3, eisPhi, hinv]
  field_simp
  ring

end Parity

/-- **The nodal-cubic relation** `r(x)² = 4p(x)³ + p(x)²`: the single term of the Tate
parametrization lies on the nodal cubic `w² = 4x³ + x²`, the degenerate Weierstrass
equation. All the arithmetic content of the Tate curve lives in the cross terms. -/
lemma eisR_sq {x : K} (hx1 : x ≠ 1) : eisR x ^ 2 = 4 * eisP x ^ 3 + eisP x ^ 2 := by
  have h1 : (1 : K) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  rw [eisR, eisP]
  field_simp
  ring

section PairIdentities

variable {t v : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hv1 : v ≠ 1) (htv : t * v ≠ 1)

include ht1 hv1 htv

/-- **Eisenstein pair identity for `p·p`** (denominator-free form): for `w = tv`,
`2·p(w)p(v) = 2·p(t)(p(v) + p(w)) - r(t)(z(v) - z(w))`.

The product of two translated `X`-kernels is a linear combination of the kernels at the
two points, with coefficients the kernels at the ratio `t`. Summed over the `qᶻ`-orbit,
the `z`-difference telescopes; this is the analytic engine behind the `X²` expansion. -/
lemma eisP_mul_eisP :
    2 * (eisP (t * v) * eisP v)
      = 2 * eisP t * (eisP v + eisP (t * v)) - eisR t * (eisZ v - eisZ (t * v)) := by
  have h1 : (1 : K) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have h2 : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have h3 : (1 : K) - t * v ≠ 0 := sub_ne_zero.mpr (Ne.symm htv)
  rw [eisP, eisP, eisP, eisR, eisZ, eisZ]
  field_simp
  ring

/-- **Eisenstein pair identity for `r·r`** (denominator-free form): for `w = tv`,
`2·r(w)r(v) = 2·r(t)(r(v) - r(w)) - 4·φ(t)(p(v) + p(w)) + ψ(t)(z(v) - z(w))`. -/
lemma eisR_mul_eisR :
    2 * (eisR (t * v) * eisR v)
      = 2 * eisR t * (eisR v - eisR (t * v)) - 4 * eisPhi t * (eisP v + eisP (t * v))
          + eisPsi t * (eisZ v - eisZ (t * v)) := by
  have h1 : (1 : K) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have h2 : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have h3 : (1 : K) - t * v ≠ 0 := sub_ne_zero.mpr (Ne.symm htv)
  rw [eisR, eisR, eisR, eisPhi, eisPsi, eisP, eisP, eisZ, eisZ]
  field_simp
  ring

/-- **Eisenstein pair identity for `p²·p`** (denominator-free form): for `w = tv`,
```
2·p(w)²p(v) = 2·p(t)·p(w)² + r(t)·r(w) + (2ψ₃(t) - r(t))·p(w) + 2·p(t)r(t)·z(w)
                + 2·p(t)²·p(v) - 2·p(t)r(t)·z(v).
```
This is the four-term partial-fraction decomposition feeding the `X³` expansion. -/
lemma eisP_sq_mul_eisP :
    2 * (eisP (t * v) ^ 2 * eisP v)
      = 2 * eisP t * eisP (t * v) ^ 2 + eisR t * eisR (t * v)
          + (2 * eisPsi3 t - eisR t) * eisP (t * v) + 2 * (eisP t * eisR t) * eisZ (t * v)
          + 2 * eisP t ^ 2 * eisP v - 2 * (eisP t * eisR t) * eisZ v := by
  have h1 : (1 : K) - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1)
  have h2 : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have h3 : (1 : K) - t * v ≠ 0 := sub_ne_zero.mpr (Ne.symm htv)
  rw [eisP, eisP, eisP, eisR, eisR, eisPsi3, eisZ, eisZ]
  field_simp
  ring

end PairIdentities

end TateCurvesTheta
