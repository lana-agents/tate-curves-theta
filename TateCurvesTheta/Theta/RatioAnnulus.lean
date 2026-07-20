/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.Theta.FactorReciprocal
import TateCurvesTheta.Theta.Divisor

/-!
# The reciprocal series of `thetaProd` on the fundamental annulus

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the product
form of the `q`-theta function factors through the elementary theta factor
(`Theta/Product.lean`):
```
thetaProd u = thetaProdFactor (-q) · thetaProdFactor (q·u) · thetaProdFactor (u⁻¹).
```
The reciprocal power series `1 / thetaProdFactor c = ∑' k, F k · cᵏ` (with `F = recipCoeff`,
`Theta/FactorReciprocal.lean`) is valid for `‖c‖ < 1`. Applying it to the three arguments:

* `thetaProdFactor (-q)` is a nonzero constant (`thetaProdFactor_neg_q_ne_zero`), invertible
  outright;
* `1 / thetaProdFactor (q·u) = ∑' k, F k (q·u)ᵏ` needs `‖q·u‖ < 1`, i.e. `‖u‖ < ‖q‖⁻¹`;
* `1 / thetaProdFactor (u⁻¹) = ∑' k, F k (u⁻¹)ᵏ` needs `‖u⁻¹‖ < 1`, i.e. `1 < ‖u‖`.

Both restrictions hold simultaneously exactly on the **fundamental annulus**
`1 < ‖u‖ < ‖q‖⁻¹`, where `thetaProd u` is therefore a unit with an explicit reciprocal series.
This is the analytic *step 1* of discharging `RatioLaurentRepr` (`Theta/TripleProduct.lean`):
the reciprocal development of `1 / thetaProd`, from which the ratio `theta / thetaProd` is built.

The annulus is genuinely maximal for the product-of-reciprocals form: the poles of the two
reciprocal series are exactly the zeros `u ∈ -qᶻ` of `thetaProd` (`thetaProd_eq_zero_iff`), the
nearest being `‖u‖ = 1` (from `thetaProdFactor (u⁻¹)`) and `‖u‖ = ‖q‖⁻¹` (from
`thetaProdFactor (q·u)`). Extending the ratio to **all** of `Kˣ` requires the pole cancellation
coming from the vanishing of `theta` on `-qᶻ` — the residual global-assembly step of #142,
recorded precisely in the remark at the end of this file.

## Main definitions

* `TateCurvesTheta.TateParameter.thetaProdRecip` : the candidate reciprocal
  `thetaProdFactor (-q)⁻¹ · (∑' k, F k (q·u)ᵏ) · (∑' k, F k (u⁻¹)ᵏ)`.

## Main results

* `TateParameter.thetaProd_mul_thetaProdRecip` : on the annulus,
  `thetaProd u · thetaProdRecip u = 1`.
* `TateParameter.thetaProdRecip_mul_thetaProd` : the symmetric form.
* `TateParameter.thetaProd_ne_zero_of_annulus` : `thetaProd u ≠ 0` on the annulus (a unit).
* `TateParameter.inv_thetaProd_eq_thetaProdRecip` : `(thetaProd u)⁻¹ = thetaProdRecip u`.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.4 (Jacobi triple product).
* A. Robert, *A Course in p-adic Analysis*, §6 (convergent series; units `1 + x` with `‖x‖ < 1`).
-/

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-- The **candidate reciprocal series of `thetaProd`** on the fundamental annulus
`1 < ‖u‖ < ‖q‖⁻¹`: the product of the reciprocal of the constant factor `thetaProdFactor (-q)`
with the two reciprocal power series `∑' k, F k (q·u)ᵏ` and `∑' k, F k (u⁻¹)ᵏ` of the remaining
factors. On the annulus this is the genuine inverse `(thetaProd u)⁻¹`
(`inv_thetaProd_eq_thetaProdRecip`). -/
noncomputable def thetaProdRecip (u : Kˣ) : K :=
  (t.thetaProdFactor (-(t.q : K)))⁻¹
    * (∑' k : ℕ, t.recipCoeff k * ((t.q : K) * (u : K)) ^ k)
    * (∑' k : ℕ, t.recipCoeff k * ((u : K)⁻¹) ^ k)

/-- **The reciprocal identity for `thetaProd` on the fundamental annulus.** For `u : Kˣ` with
`‖q·u‖ < 1` and `‖u⁻¹‖ < 1` (equivalently `1 < ‖u‖ < ‖q‖⁻¹`),
```
thetaProd u · thetaProdRecip u = 1,
```
so `thetaProdRecip u` is the reciprocal `1 / thetaProd u`. The proof multiplies the three
`thetaProdFactor · (reciprocal series) = 1` identities (`thetaProdFactor_mul_tsum_recipCoeff`
for the two non-constant factors, `mul_inv_cancel₀` for the nonzero constant factor
`thetaProdFactor (-q)`) after regrouping the six factors. -/
theorem thetaProd_mul_thetaProdRecip (u : Kˣ)
    (hqu : ‖(t.q : K) * (u : K)‖ < 1) (huinv : ‖((u : K)⁻¹)‖ < 1) :
    t.thetaProd u * t.thetaProdRecip u = 1 := by
  have ha : t.thetaProdFactor (-(t.q : K)) * (t.thetaProdFactor (-(t.q : K)))⁻¹ = 1 :=
    mul_inv_cancel₀ t.thetaProdFactor_neg_q_ne_zero
  have hb : t.thetaProdFactor ((t.q : K) * (u : K))
      * (∑' k : ℕ, t.recipCoeff k * ((t.q : K) * (u : K)) ^ k) = 1 :=
    t.thetaProdFactor_mul_tsum_recipCoeff hqu
  have hc : t.thetaProdFactor ((u : K)⁻¹)
      * (∑' k : ℕ, t.recipCoeff k * ((u : K)⁻¹) ^ k) = 1 :=
    t.thetaProdFactor_mul_tsum_recipCoeff huinv
  rw [thetaProd_apply, thetaProdRecip]
  calc
    t.thetaProdFactor (-(t.q : K)) * t.thetaProdFactor ((t.q : K) * (u : K))
          * t.thetaProdFactor ((u : K)⁻¹)
        * ((t.thetaProdFactor (-(t.q : K)))⁻¹
            * (∑' k : ℕ, t.recipCoeff k * ((t.q : K) * (u : K)) ^ k)
            * (∑' k : ℕ, t.recipCoeff k * ((u : K)⁻¹) ^ k))
        = (t.thetaProdFactor (-(t.q : K)) * (t.thetaProdFactor (-(t.q : K)))⁻¹)
            * (t.thetaProdFactor ((t.q : K) * (u : K))
                * (∑' k : ℕ, t.recipCoeff k * ((t.q : K) * (u : K)) ^ k))
            * (t.thetaProdFactor ((u : K)⁻¹)
                * (∑' k : ℕ, t.recipCoeff k * ((u : K)⁻¹) ^ k)) := by ring
    _ = 1 * 1 * 1 := by rw [ha, hb, hc]
    _ = 1 := by ring

/-- The symmetric form of the reciprocal identity, `thetaProdRecip u · thetaProd u = 1`. -/
theorem thetaProdRecip_mul_thetaProd (u : Kˣ)
    (hqu : ‖(t.q : K) * (u : K)‖ < 1) (huinv : ‖((u : K)⁻¹)‖ < 1) :
    t.thetaProdRecip u * t.thetaProd u = 1 := by
  rw [mul_comm]; exact t.thetaProd_mul_thetaProdRecip u hqu huinv

/-- On the fundamental annulus `thetaProd u` is a unit, hence nonzero — a direct sanity check
against `thetaProd_eq_zero_iff` (its zeros `u ∈ -qᶻ` all lie off the open annulus). -/
theorem thetaProd_ne_zero_of_annulus (u : Kˣ)
    (hqu : ‖(t.q : K) * (u : K)‖ < 1) (huinv : ‖((u : K)⁻¹)‖ < 1) :
    t.thetaProd u ≠ 0 := by
  intro h
  have hone := t.thetaProd_mul_thetaProdRecip u hqu huinv
  rw [h, zero_mul] at hone
  exact one_ne_zero hone.symm

/-- On the fundamental annulus, `thetaProdRecip u` is literally the inverse `(thetaProd u)⁻¹`. -/
theorem inv_thetaProd_eq_thetaProdRecip (u : Kˣ)
    (hqu : ‖(t.q : K) * (u : K)‖ < 1) (huinv : ‖((u : K)⁻¹)‖ < 1) :
    (t.thetaProd u)⁻¹ = t.thetaProdRecip u :=
  inv_eq_of_mul_eq_one_right (t.thetaProd_mul_thetaProdRecip u hqu huinv)

/-- The annulus reciprocal, expressed through the norm bounds `1 < ‖u‖` and `‖q‖ · ‖u‖ < 1`
that describe the fundamental annulus `1 < ‖u‖ < ‖q‖⁻¹` more readably than the raw factor-norm
hypotheses of `thetaProd_mul_thetaProdRecip`. -/
theorem thetaProd_mul_thetaProdRecip_of_annulus (u : Kˣ)
    (hlo : 1 < ‖(u : K)‖) (hhi : ‖(t.q : K)‖ * ‖(u : K)‖ < 1) :
    t.thetaProd u * t.thetaProdRecip u = 1 := by
  refine t.thetaProd_mul_thetaProdRecip u ?_ ?_
  · rw [norm_mul]; exact hhi
  · rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hlo

/-!
### Residual global-assembly step (issue #142)

`thetaProdRecip` gives `1 / thetaProd` only on the open annulus `1 < ‖u‖ < ‖q‖⁻¹`, because the
two reciprocal power series `∑' k, F k (q·u)ᵏ` and `∑' k, F k (u⁻¹)ᵏ` each diverge past a pole of
`thetaProd` (`thetaProd_eq_zero_iff`: zeros at `u ∈ -qᶻ`, nearest at `‖u‖ = 1` and
`‖u‖ = ‖q‖⁻¹`).

To reach `TateParameter.RatioLaurentRepr t` (`Theta/TripleProduct.lean`) — a single two-sided
Laurent family `c : ℤ → K` with `Summable (fun n => cₙ uⁿ)` and
`theta u = (∑' n, cₙ uⁿ) · thetaProd u` for **all** `u : Kˣ`, plus `q`-invariance of the sum — the
remaining work is:

1. Form the (three-fold, `ℤ × ℕ × ℕ → ℤ`) nonarchimedean Cauchy product of the `theta` family
   `n ↦ q^(e n) uⁿ` with `thetaProdFactor (-q)⁻¹`, `k ↦ F k qᵏ uᵏ`, and `k ↦ F k u⁻ᵏ`, giving the
   coefficients `cₙ = thetaProdFactor (-q)⁻¹ · ∑_{a + b - d = n} q^(e a) · F b qᵇ · F d`.
2. Prove `‖cₙ‖ → 0` faster than any geometric rate as `|n| → ∞` (the super-geometric decay of
   `q^(e a)` dominates the norm-≤-1 reciprocal coefficients), yielding `Summable (n ↦ cₙ uⁿ)` on
   **all** of `Kˣ`: the pole cancellation from `theta` vanishing on `-qᶻ` made rigorous.
3. Extend the factorization `theta u = (∑' n, cₙ uⁿ) · thetaProd u` and the `q`-invariance from
   the annulus (where they follow from `thetaProd_mul_thetaProdRecip` and `thetaDiv_q_smul`) to
   all of `Kˣ`, via shared `q`-quasiperiodicity (`theta_q_smul`, `thetaProd_q_smul`) covering
   `Kˣ ∖ (-qᶻ)` by `qᶻ`-translates of the annulus, then `-qᶻ` by both sides vanishing.

Steps 2–3 are the crux of #142 and are not attempted here; this file lands the annulus reciprocal
development (step 1) as reusable infrastructure. A worker closing #142 should build the
coefficient family on top of `thetaProdRecip` and `thetaProd_mul_thetaProdRecip`.
-/

end TateParameter

end TateCurvesTheta
