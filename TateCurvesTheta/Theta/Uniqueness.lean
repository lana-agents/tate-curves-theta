/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import TateCurvesTheta.Theta.Product

/-!
# The nonarchimedean `q`-difference uniqueness engine

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), a
convergent two-sided Laurent series `f u = ∑' n : ℤ, aₙ · uⁿ` that is **`q`-invariant**
(`f (q · u) = f u` for all `u : Kˣ`) is necessarily **constant**. This is the analytic engine
behind three separate facts the project has repeatedly deferred as seams:

* the Jacobi triple product identity `theta = thetaProd` (`Theta/Product.lean`, #105): both
  sides obey `f (q·u) = (q·u)⁻¹ · f u`, so their ratio is `q`-invariant, hence constant;
* the *unconditional* zero divisor of the naive series `theta` (`Theta/Divisor.lean`, #88),
  currently stated conditionally on `theta = thetaProd`;
* membership `tatePoint_mem` (#116) and surjectivity of `Kˣ/qᶻ → E_q(K)` (#118): a
  `q`-invariant Laurent function with no poles is constant.

This file builds the shared engine **once**.

## The mathematical core (elementary, given coefficient uniqueness)

Write `f (q·u) = ∑' n, aₙ qⁿ uⁿ`. Comparing with `f u = ∑' n, aₙ uⁿ`, *uniqueness of Laurent
coefficients* forces `aₙ · qⁿ = aₙ`, i.e. `aₙ · (qⁿ − 1) = 0`, for every `n`. Since `q` is not
a root of unity (`qⁿ ≠ 1` for `n ≠ 0`, `TateParameter.zpow_ne_one`), `qⁿ − 1 ≠ 0` for `n ≠ 0`,
so `aₙ = 0` for `n ≠ 0` and `f` collapses to its constant term `a₀`.

The only nonelementary input is the **Laurent coefficient uniqueness principle**
`LaurentCoeffUnique`: over a complete nonarchimedean field, a convergent two-sided Laurent
series is determined by its values on `Kˣ`. This is the nonarchimedean analogue of the identity
theorem for Laurent expansions (its proof is a Newton-polygon / ultrametric maximum-modulus
argument that is not yet in this tree); the engine below is proved **conditionally** on it,
`sorry`-free, taking it as an explicit hypothesis. Everything else — the reduction of
`q`-invariance to the coefficient relation and the collapse to `a₀` — is elementary and proved
here in full, so the recurring project seam is reduced to this single named principle.

## Main definitions

* `TateCurvesTheta.LaurentCoeffUnique` : the coefficient-uniqueness principle for convergent
  two-sided Laurent series over `K`.

## Main results

* `TateCurvesTheta.TateParameter.zpow_ne_one` : `qⁿ ≠ 1` for `n ≠ 0` (integer exponents).
* `TateCurvesTheta.TateParameter.tsum_eq_coeff_zero_of_qinv` : a Laurent series whose
  coefficients satisfy `aₙ · qⁿ = aₙ` sums to its constant term `a₀` (the collapse step).
* `TateCurvesTheta.TateParameter.const_of_qinvariant_laurent` : **the engine** — given
  `LaurentCoeffUnique`, a `q`-invariant convergent Laurent series equals its constant term
  `a₀` at every `u`.
* `TateCurvesTheta.TateParameter.thetaDiv_q_smul` : the ratio `theta / thetaProd` is
  `q`-invariant (its automorphy factors `(q·u)⁻¹` cancel), the precise hypothesis to which the
  engine applies to close `theta = thetaProd`.

## Closing `theta = thetaProd` (the remaining seams)

With the engine in hand, `theta = thetaProd` follows once two further inputs are supplied:

1. `LaurentCoeffUnique K` — the coefficient-uniqueness principle above;
2. a **Laurent representation of the ratio** `theta u / thetaProd u = ∑' n, cₙ uⁿ` (division of
   two convergent products), the one genuinely analytic step flagged in `Theta/Product.lean`.

Given both, `thetaDiv_q_smul` makes the ratio `q`-invariant, `const_of_qinvariant_laurent`
makes it the constant `c₀`, and matching the leading term pins `c₀ = 1`. Steps 1–2 and the
`c₀ = 1` normalization are left as precisely-stated seams; the reusable engine and the ratio's
`q`-invariance are delivered here in full.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.4 (Jacobi triple product via the
  functional-equation uniqueness argument).
* S. Mochizuki, *The Étale Theta Function*, §1, Proposition 1.4.
-/

open Filter Topology

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- **A Tate parameter is not a root of unity (integer exponents).** For `n ≠ 0`, `qⁿ ≠ 1`.
This extends `TateParameter.pow_ne_one` (natural exponents) to all of `ℤ`, and is the
nonvanishing `qⁿ − 1 ≠ 0` that drives the `q`-difference engine. -/
lemma zpow_ne_one {n : ℤ} (hn : n ≠ 0) : (t.q : K) ^ n ≠ 1 := by
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · intro h
    have h' : (t.q : K) ^ (-n) = 1 := by
      rw [zpow_neg, h, inv_one]
    have hnat : (t.q : K) ^ (-n).toNat = 1 := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n)]; exact h'
    exact t.pow_ne_one (by omega : 0 < (-n).toNat) hnat
  · intro h
    have hnat : (t.q : K) ^ n.toNat = 1 := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hpos.le]; exact h
    exact t.pow_ne_one (by omega : 0 < n.toNat) hnat

/-- **Collapse of a `q`-invariant Laurent series to its constant term.** If the coefficients
satisfy the shift relation `aₙ · qⁿ = aₙ` for every `n`, then `aₙ = 0` for `n ≠ 0`
(`qⁿ − 1 ≠ 0` by `zpow_ne_one`) and the two-sided sum reduces to `a₀`. No convergence
hypothesis is needed: the family is supported at `0`. -/
theorem tsum_eq_coeff_zero_of_qinv (a : ℤ → K) (hcoeff : ∀ n : ℤ, a n * (t.q : K) ^ n = a n)
    (u : Kˣ) : (∑' n : ℤ, a n * (u : K) ^ n) = a 0 := by
  have haz : ∀ n : ℤ, n ≠ 0 → a n = 0 := by
    intro n hn
    have h1 : a n * ((t.q : K) ^ n - 1) = 0 := by
      rw [mul_sub, mul_one, hcoeff n, sub_self]
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) (t.zpow_ne_one hn)
  rw [tsum_eq_single (0 : ℤ) fun n hn => by rw [haz n hn, zero_mul], zpow_zero, mul_one]

/-- The **Laurent coefficient uniqueness principle** over `K`: a convergent two-sided Laurent
series is determined by its values on `Kˣ`. If two coefficient families `a, b : ℤ → K` give
summable Laurent series with `∑' n, aₙ uⁿ = ∑' n, bₙ uⁿ` for every `u : Kˣ`, then `a = b`.

This is the nonarchimedean identity theorem for Laurent expansions. Its proof (a Newton-polygon
/ ultrametric maximum-modulus argument) is not yet in this tree; it is the single analytic input
to the `q`-difference engine below and is carried as an explicit hypothesis rather than
`sorry`-ed. -/
def _root_.TateCurvesTheta.LaurentCoeffUnique (K : Type*) [NormedField K] : Prop :=
  ∀ a b : ℤ → K,
    (∀ u : Kˣ, Summable fun n : ℤ => a n * (u : K) ^ n) →
    (∀ u : Kˣ, Summable fun n : ℤ => b n * (u : K) ^ n) →
    (∀ u : Kˣ, (∑' n : ℤ, a n * (u : K) ^ n) = ∑' n : ℤ, b n * (u : K) ^ n) →
    a = b

/-- **The `q`-difference uniqueness engine.** Given the Laurent coefficient uniqueness principle
`LaurentCoeffUnique K`, a convergent two-sided Laurent series `f u = ∑' n, aₙ uⁿ` that is
`q`-invariant (`hqinv`: `∑' n, aₙ (q·u)ⁿ = ∑' n, aₙ uⁿ` for all `u`) equals its constant term
`a₀` at every `u : Kˣ`.

The proof reindexes `f (q·u) = ∑' n, (aₙ qⁿ) uⁿ`; uniqueness forces `aₙ qⁿ = aₙ`, and
`tsum_eq_coeff_zero_of_qinv` collapses the sum to `a₀`. -/
theorem const_of_qinvariant_laurent (huniq : LaurentCoeffUnique K) (a : ℤ → K)
    (hsum : ∀ u : Kˣ, Summable fun n : ℤ => a n * (u : K) ^ n)
    (hqinv : ∀ u : Kˣ,
      (∑' n : ℤ, a n * ((t.q : K) * (u : K)) ^ n) = ∑' n : ℤ, a n * (u : K) ^ n) :
    ∀ u : Kˣ, (∑' n : ℤ, a n * (u : K) ^ n) = a 0 := by
  -- Termwise reindexing `aₙ (q·v)ⁿ = (aₙ qⁿ) vⁿ`.
  have hpt : ∀ (v : Kˣ) (n : ℤ),
      a n * ((t.q : K) * (v : K)) ^ n = (a n * (t.q : K) ^ n) * (v : K) ^ n := by
    intro v n; rw [mul_zpow]; ring
  -- The shifted coefficient family `n ↦ aₙ qⁿ` is summable (it is `f` evaluated at `q·v`).
  have hbsum : ∀ v : Kˣ, Summable fun n : ℤ => (a n * (t.q : K) ^ n) * (v : K) ^ n := by
    intro v
    refine (hsum (t.q * v)).congr fun n => ?_
    rw [Units.val_mul, hpt v n]
  -- `q`-invariance in coefficient form: the shifted family has the same sums as `a`.
  have heq : ∀ v : Kˣ,
      (∑' n : ℤ, (a n * (t.q : K) ^ n) * (v : K) ^ n) = ∑' n : ℤ, a n * (v : K) ^ n := by
    intro v
    rw [tsum_congr fun n => (hpt v n).symm]
    exact hqinv v
  -- Coefficient uniqueness pins the shift relation `aₙ qⁿ = aₙ`.
  have hcoeff : (fun n : ℤ => a n * (t.q : K) ^ n) = a := huniq _ a hbsum hsum heq
  exact t.tsum_eq_coeff_zero_of_qinv a fun n => congrFun hcoeff n

/-- **The ratio `theta / thetaProd` is `q`-invariant.** Both `theta` and `thetaProd` transform
under `u ↦ q·u` by the *same* automorphy factor `(q·u)⁻¹` (`theta_q_smul`,
`thetaProd_q_smul`), so it cancels in the quotient:
`theta (q·u) · thetaProd (q·u)⁻¹ = theta u · thetaProd u⁻¹`.

This is the precise `q`-invariance hypothesis fed to `const_of_qinvariant_laurent` (once the
ratio is exhibited as a convergent Laurent series) to force `theta = thetaProd`. -/
theorem thetaDiv_q_smul [CompleteSpace K] (u : Kˣ) :
    t.theta (t.q * u) * (t.thetaProd (t.q * u))⁻¹ = t.theta u * (t.thetaProd u)⁻¹ := by
  have wne : (t.q : K) * (u : K) ≠ 0 := mul_ne_zero t.q.ne_zero u.ne_zero
  -- Inverting the `thetaProd` automorphy turns the factor `(q·u)⁻¹` into `(q·u)`.
  have h2 : (t.thetaProd (t.q * u))⁻¹ = ((t.q : K) * (u : K)) * (t.thetaProd u)⁻¹ := by
    rw [thetaProd_q_smul, mul_inv, inv_inv]
  rw [theta_q_smul, h2, mul_mul_mul_comm, inv_mul_cancel₀ wne, one_mul]

end TateParameter

end TateCurvesTheta
