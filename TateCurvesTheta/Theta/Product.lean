/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TateCurvesTheta.Theta.Periodicity

/-!
# The product form of the `q`-theta function (Jacobi triple product)

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the naive
`q`-theta series `θ q u = ∑' n : ℤ, q ^ (e n) * u ^ n` (with `e n = n * (n + 1) / 2` the
triangular exponent, fixed in `TateCurvesTheta.Theta.Basic`) admits a *product form*. This is
the nonarchimedean **Jacobi triple product** identity; unlike the series, the product exhibits
each zero of `θ` as the vanishing of an explicit linear factor `1 + qⁿ · u`, which is the
handle needed to locate the divisor of `θ` (issue #88).

## The normalization

With the *unsigned* exponent `e n = n * (n + 1) / 2` fixed in `Theta/Basic.lean`, the classical
Jacobi triple product reads
```
∑' n : ℤ, q ^ (e n) * uⁿ  =  ∏' m ≥ 1, (1 - q ^ m) · (1 + q ^ m · u) · (1 + q ^ (m-1) · u⁻¹).
```
(One derives this from the symmetric form `∑ x ^ (n²) y ^ (2n) = ∏ (1-x^{2m})(1+x^{2m-1}y²)
(1+x^{2m-1}y^{-2})` by the substitution `x = q^{1/2}`, `y² = q^{1/2}·u`; all fractional powers
cancel, giving the integer-exponent product above.) Re-indexing all three products by `n : ℕ`
(`m = n + 1`) and factoring out the leading `qⁿ`, every factor has the uniform shape
`1 + qⁿ · c` for a constant `c`:

* `1 - q ^ (n+1)  = 1 + qⁿ · (-q)`;
* `1 + q ^ (n+1) · u = 1 + qⁿ · (q·u)`;
* `1 + q ^ n · u⁻¹`.

This motivates the single building block `thetaProdFactor c := ∏' n, (1 + qⁿ · c)` and the
definition
```
thetaProd q u = thetaProdFactor (-q) · thetaProdFactor (q · u) · thetaProdFactor u⁻¹.
```
This file **fixes this normalization** as the definitive product form for downstream work.

## Main definitions

* `TateCurvesTheta.TateParameter.thetaProdFactor` : the building block `∏' n : ℕ, (1 + qⁿ · c)`.
* `TateCurvesTheta.TateParameter.thetaProd` : the product form of the `q`-theta function.

## Main results

* `TateParameter.multipliable_thetaProdFactor` : each factor family `n ↦ 1 + qⁿ · c` is
  `Multipliable` over a complete field, because `‖qⁿ · c‖ = ‖q‖ⁿ · ‖c‖` is geometric hence
  summable. Packaged for the three factors of `thetaProd` as `multipliable_thetaProd_*`.
* `TateParameter.thetaProdFactor_eq` : the index-shift relation
  `thetaProdFactor c = (1 + c) · thetaProdFactor (q · c)`, the engine of quasi-periodicity.
* `TateParameter.thetaProd_q_smul` : the product form satisfies the **same** `q`-periodicity
  functional equation as the series, `thetaProd q (q · u) = (q · u)⁻¹ · thetaProd q u`
  (compare `theta_q_smul`).

## The identity `θ = thetaProd` (documented seam)

The full Jacobi triple product identity `theta q u = thetaProd q u` is **not** proved here.
Its standard proof observes that both sides satisfy the same `q`-difference equation
`f (q·u) = (q·u)⁻¹ · f u` (established here for `thetaProd` as `thetaProd_q_smul`, and for the
series as `theta_q_smul`), so their ratio is `qᶻ`-invariant, i.e. descends to a nowhere-zero
"holomorphic" function on the compact quotient `Kˣ/qᶻ` and is therefore constant; matching the
constant term closes the identity. The closing uniqueness step requires a nonarchimedean
Liouville/properness input for `Kˣ/qᶻ` that is not yet in this tree, so it is left as a
documented seam. Everything *claimed proved* below is `sorry`-free; the two sides are shown to
obey the identical functional equation, which is the substantive analytic agreement.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.4 (Jacobi triple product).
* S. Mochizuki, *The Étale Theta Function*, §1, Proposition 1.4.
-/

open Filter Topology

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- The **elementary factor family** of the `q`-theta product form: `n ↦ 1 + qⁿ · c`. Every
factor of `thetaProd` is `thetaProdFactor` at a suitable constant `c`. -/
noncomputable def thetaProdFactor (c : K) : K := ∏' n : ℕ, (1 + (t.q : K) ^ n * c)

/-- The defining unfolding of `thetaProdFactor`. -/
lemma thetaProdFactor_apply (c : K) :
    t.thetaProdFactor c = ∏' n : ℕ, (1 + (t.q : K) ^ n * c) := rfl

/-- The **product form** of the `q`-theta function,
`thetaProd q u = ∏' n, (1 - q ^ (n+1)) · ∏' n, (1 + q ^ (n+1) · u) · ∏' n, (1 + q ^ n · u⁻¹)`,
written through the uniform building block `thetaProdFactor`. See the module docstring for the
normalization pinning it to the unsigned series `theta`. -/
noncomputable def thetaProd (u : Kˣ) : K :=
  t.thetaProdFactor (-(t.q : K)) * t.thetaProdFactor ((t.q : K) * (u : K)) *
    t.thetaProdFactor ((u : K)⁻¹)

/-- The defining unfolding of `thetaProd`. -/
lemma thetaProd_apply (u : Kˣ) :
    t.thetaProd u = t.thetaProdFactor (-(t.q : K)) * t.thetaProdFactor ((t.q : K) * (u : K)) *
      t.thetaProdFactor ((u : K)⁻¹) := rfl

/-- **Multipliability of the elementary factor family.** Over a complete field the family
`n ↦ 1 + qⁿ · c` is `Multipliable`: its factors are `1 + (small)` with
`‖qⁿ · c‖ = ‖q‖ⁿ · ‖c‖` a geometric (hence summable) sequence, so the Banach-ring criterion
`multipliable_one_add_of_summable` applies. No ultrametric hypothesis is needed. -/
lemma multipliable_thetaProdFactor [CompleteSpace K] (c : K) :
    Multipliable (fun n : ℕ => 1 + (t.q : K) ^ n * c) := by
  apply multipliable_one_add_of_summable
  have hnorm : (fun n : ℕ => ‖(t.q : K) ^ n * c‖) = fun n : ℕ => ‖(t.q : K)‖ ^ n * ‖c‖ := by
    funext n; rw [norm_mul, norm_pow]
  rw [hnorm]
  exact (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one).mul_right ‖c‖

/-- The three factor families of `thetaProd` are each `Multipliable`. -/
lemma multipliable_thetaProd_qpow [CompleteSpace K] :
    Multipliable (fun n : ℕ => 1 + (t.q : K) ^ n * (-(t.q : K))) :=
  t.multipliable_thetaProdFactor _

lemma multipliable_thetaProd_u [CompleteSpace K] (u : Kˣ) :
    Multipliable (fun n : ℕ => 1 + (t.q : K) ^ n * ((t.q : K) * (u : K))) :=
  t.multipliable_thetaProdFactor _

lemma multipliable_thetaProd_uinv [CompleteSpace K] (u : Kˣ) :
    Multipliable (fun n : ℕ => 1 + (t.q : K) ^ n * (u : K)⁻¹) :=
  t.multipliable_thetaProdFactor _

/-- **The index-shift (quasi-periodicity) relation for the elementary factor.** Peeling off the
`n = 0` factor and re-absorbing the shift `q ^ (n+1) = qⁿ · q` gives
`thetaProdFactor c = (1 + c) · thetaProdFactor (q · c)`. This is the multiplicative engine
behind the `q`-periodicity of the product form. -/
lemma thetaProdFactor_eq [CompleteSpace K] (c : K) :
    t.thetaProdFactor c = (1 + c) * t.thetaProdFactor ((t.q : K) * c) := by
  -- Peel the `n = 0` factor.  `Multipliable.tprod_eq_zero_mul` lives in the topological-*group*
  -- section, which does not apply to the multiplicative monoid of the field `K`; the monoid-level
  -- `tprod_eq_zero_mul'` does, once we pin `f` explicitly to sidestep higher-order unification.
  have hshift : Multipliable (fun n : ℕ => 1 + (t.q : K) ^ (n + 1) * c) := by
    have h := t.multipliable_thetaProdFactor ((t.q : K) * c)
    have hfun : (fun n : ℕ => 1 + (t.q : K) ^ (n + 1) * c)
        = fun n : ℕ => 1 + (t.q : K) ^ n * ((t.q : K) * c) := by
      funext n; rw [pow_succ]; ring
    rw [hfun]; exact h
  have key : (∏' n : ℕ, (1 + (t.q : K) ^ n * c))
      = (1 + (t.q : K) ^ 0 * c) * ∏' n : ℕ, (1 + (t.q : K) ^ (n + 1) * c) :=
    tprod_eq_zero_mul' (f := fun n : ℕ => 1 + (t.q : K) ^ n * c) hshift
  rw [thetaProdFactor, key, pow_zero, one_mul]
  congr 1
  rw [thetaProdFactor]
  refine tprod_congr fun n => ?_
  rw [pow_succ]; ring

/-- **The `q`-periodicity functional equation of the product form.** Under the generating
translation `u ↦ q · u` the product form `thetaProd` transforms by exactly the automorphy factor
`(q · u)⁻¹` of the series (`theta_q_smul`):
`thetaProd q (q · u) = (q · u)⁻¹ · thetaProd q u`.

The proof applies the shift relation `thetaProdFactor_eq` to the two `u`-dependent factors,
`thetaProdFactor (q·u)` and `thetaProdFactor (q·u)⁻¹`, and collapses the resulting scalars using
`(1 + w⁻¹) = w⁻¹ · (1 + w)` for `w = q·u ≠ 0`. It holds unconditionally on `u : Kˣ` (no
avoidance of the divisor is needed). -/
theorem thetaProd_q_smul [CompleteSpace K] (u : Kˣ) :
    t.thetaProd (t.q * u) = ((t.q : K) * (u : K))⁻¹ * t.thetaProd u := by
  set w : K := (t.q : K) * (u : K) with hw
  have hwne : w ≠ 0 := mul_ne_zero t.q.ne_zero u.ne_zero
  -- Shift relation on the middle factor: `thetaProdFactor (q·u) = (1 + w) · thetaProdFactor (q·w)`.
  have hA : t.thetaProdFactor w = (1 + w) * t.thetaProdFactor ((t.q : K) * w) :=
    t.thetaProdFactor_eq w
  -- Shift relation on the inverse factor: `thetaProdFactor w⁻¹ = (1 + w⁻¹) · thetaProdFactor u⁻¹`,
  -- because `q · w⁻¹ = q · (q·u)⁻¹ = u⁻¹`.
  have hqw : (t.q : K) * w⁻¹ = (u : K)⁻¹ := by
    rw [hw, mul_inv_rev, ← mul_assoc, mul_comm (t.q : K), mul_assoc, mul_inv_cancel₀ t.q.ne_zero,
      mul_one]
  have hB : t.thetaProdFactor w⁻¹ = (1 + w⁻¹) * t.thetaProdFactor ((u : K)⁻¹) := by
    rw [t.thetaProdFactor_eq w⁻¹, hqw]
  -- Scalar collapse.
  have hscal : (1 + w⁻¹) = w⁻¹ * (1 + w) := by
    rw [mul_add, mul_one, inv_mul_cancel₀ hwne, add_comm]
  -- Assemble.  Note `↑(t.q * u) = w` and `(↑(t.q * u))⁻¹ = w⁻¹`.
  rw [thetaProd_apply, thetaProd_apply]
  simp only [Units.val_mul, ← hw]
  rw [hB, hA, hscal]
  ring

/-- Every factor of the constant term `thetaProdFactor (-q) = ∏' n, (1 - q ^ (n+1))` is nonzero:
`1 - q ^ (n+1) ≠ 0` because `q ^ (n+1) ≠ 1` (`q` is not a root of unity), rewritten in the
`thetaProdFactor` normalization `1 + qⁿ · (-q)`. -/
lemma thetaProdFactor_neg_q_factor_ne_zero (n : ℕ) :
    (1 : K) + (t.q : K) ^ n * (-(t.q : K)) ≠ 0 := by
  have h : (1 : K) + (t.q : K) ^ n * (-(t.q : K)) = 1 - (t.q : K) ^ (n + 1) := by
    rw [pow_succ]; ring
  rw [h, sub_ne_zero]
  exact (t.pow_ne_one n.succ_pos).symm

end TateParameter

end TateCurvesTheta
