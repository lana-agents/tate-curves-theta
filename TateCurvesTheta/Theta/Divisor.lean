/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TateCurvesTheta.Theta.Product

/-!
# The zero divisor of the `q`-theta function

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the product
form of the `q`-theta function (`TateCurvesTheta.Theta.Product`)
```
thetaProd q u = thetaProdFactor (-q) · thetaProdFactor (q · u) · thetaProdFactor u⁻¹,
        thetaProdFactor c = ∏' n : ℕ, (1 + qⁿ · c),
```
exhibits each zero of the theta function as the vanishing of an explicit linear factor
`1 + qⁿ · c`. This file reads off the **zero locus** of `thetaProd`: it is exactly the
`qᶻ`-orbit of `-1`,
```
thetaProd q u = 0  ↔  ∃ k : ℤ, (u : K) = -qᵏ,
```
the classical statement that the Tate theta function has its zeros along a single `qᶻ`-orbit,
so it descends to a **degree-one divisor** (a single point) on the Tate curve `E_q = Kˣ/qᶻ`.
This is the geometric input that makes `θ` the theta function of a principal polarization.

## Strategy

Over a complete normed field an infinite product `∏' (1 + f n)` is nonzero as soon as every
factor is nonzero and `‖f‖` is summable (`tprod_one_add_ne_zero_of_summable`); conversely a
single vanishing factor forces the whole product to vanish (peel it off with
`Multipliable.prod_mul_tprod_nat_mul'`). For `thetaProdFactor c = ∏' n, (1 + qⁿ c)` this gives
```
thetaProdFactor c = 0  ↔  ∃ n : ℕ, 1 + qⁿ · c = 0        (`thetaProdFactor_eq_zero_iff`).
```
The constant factor `thetaProdFactor (-q) = ∏' (1 - qⁿ⁺¹)` never vanishes (`q` is not a root of
unity), while the two `u`-dependent factors vanish precisely at `u = -q⁻⁽ⁿ⁺¹⁾` and `u = -qⁿ`;
folding the two sign-parametrized families of exponents into all of `ℤ` gives the orbit.

## Relation to the series `theta`

The naive series `theta` (`TateCurvesTheta.Theta.Basic`) and the product form `thetaProd`
satisfy the same `q`-periodicity functional equation (`theta_q_smul`, `thetaProd_q_smul`), but
the identity `theta = thetaProd` itself is a **documented seam** in
`TateCurvesTheta.Theta.Product` (it needs a nonarchimedean Liouville/properness input for
`Kˣ/qᶻ` not yet in this tree). Accordingly the divisor is computed here for `thetaProd`, and the
transfer to the series is packaged as `theta_eq_zero_iff_of_eq_thetaProd`, which yields the
divisor of `theta` verbatim the moment that seam is closed.

## Transport to `E_q(K)` = `Kˣ/qᶻ`

The `qᶻ`-orbit statement `thetaProd_zero_orbit` (any two zeros differ by an integer power of `q`)
is the elementary, `Kˣ`-level form of "the zeros form a single point of `Kˣ/qᶻ`". Packaging it
through the analytic-quotient group `AnalyticQuotient := Kˣ ⧸ qᶻ` (which is built on the separate
`TateDatum` structure) is left as a documented seam, matching the divisor-transport seam noted in
the issue.

## Main results

* `TateParameter.thetaProdFactor_eq_zero_iff`: `thetaProdFactor c = 0 ↔ ∃ n, 1 + qⁿ c = 0`.
* `TateParameter.thetaProdFactor_neg_q_ne_zero`: the constant factor `thetaProdFactor (-q)` is
  nonzero.
* `TateParameter.thetaProd_eq_zero_iff`: `thetaProd q u = 0 ↔ ∃ k : ℤ, (u : K) = -qᵏ`.
* `TateParameter.thetaProd_zero_orbit`: the zeros of `thetaProd` form a single `qᶻ`-orbit.
* `TateParameter.theta_eq_zero_iff_of_eq_thetaProd`: the divisor of the series `theta`, granted
  the `theta = thetaProd` seam.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V.
* S. Mochizuki, *The Étale Theta Function*, §1, Proposition 1.4.
-/

open Filter Topology

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- The norms `‖qⁿ · c‖ = ‖q‖ⁿ ‖c‖` form a summable (geometric) sequence, the analytic input to
both the nonvanishing and the factor-peeling arguments below. -/
private lemma summable_norm_qpow_mul (c : K) :
    Summable (fun n : ℕ => ‖(t.q : K) ^ n * c‖) := by
  have h : (fun n : ℕ => ‖(t.q : K) ^ n * c‖) = fun n : ℕ => ‖(t.q : K)‖ ^ n * ‖c‖ := by
    funext n; rw [norm_mul, norm_pow]
  rw [h]
  exact (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one).mul_right ‖c‖

/-- **Zero criterion for the elementary factor.** Over a complete field the product
`thetaProdFactor c = ∏' n, (1 + qⁿ c)` vanishes **iff** one of its factors vanishes. The forward
direction is the contrapositive of `tprod_one_add_ne_zero_of_summable` (all factors nonzero ⇒
nonzero product); the backward direction peels the vanishing factor off with
`Multipliable.prod_mul_tprod_nat_mul'`. -/
lemma thetaProdFactor_eq_zero_iff [CompleteSpace K] (c : K) :
    t.thetaProdFactor c = 0 ↔ ∃ n : ℕ, (1 : K) + (t.q : K) ^ n * c = 0 := by
  have hsum := t.summable_norm_qpow_mul c
  constructor
  · intro h
    by_contra hcon
    have hcon' : ∀ n : ℕ, (1 : K) + (t.q : K) ^ n * c ≠ 0 := fun n hn => hcon ⟨n, hn⟩
    have hne :=
      tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => (t.q : K) ^ n * c) hcon' hsum
    rw [thetaProdFactor] at h
    exact hne h
  · rintro ⟨m, hm⟩
    have hshift : Multipliable (fun n : ℕ => (1 : K) + (t.q : K) ^ (n + (m + 1)) * c) := by
      have h := t.multipliable_thetaProdFactor ((t.q : K) ^ (m + 1) * c)
      have hfun : (fun n : ℕ => (1 : K) + (t.q : K) ^ (n + (m + 1)) * c)
          = fun n : ℕ => (1 : K) + (t.q : K) ^ n * ((t.q : K) ^ (m + 1) * c) := by
        funext n; rw [pow_add]; ring
      rw [hfun]; exact h
    have hkey := Multipliable.prod_mul_tprod_nat_mul'
      (f := fun n : ℕ => (1 : K) + (t.q : K) ^ n * c) (k := m + 1) hshift
    rw [thetaProdFactor, ← hkey,
      Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_self m)) hm, zero_mul]

/-- The **constant factor never vanishes**: `thetaProdFactor (-q) = ∏' n, (1 - qⁿ⁺¹) ≠ 0`, since
`q` is not a root of unity (`thetaProdFactor_neg_q_factor_ne_zero`). -/
lemma thetaProdFactor_neg_q_ne_zero [CompleteSpace K] :
    t.thetaProdFactor (-(t.q : K)) ≠ 0 := by
  rw [ne_eq, t.thetaProdFactor_eq_zero_iff]
  rintro ⟨n, hn⟩
  exact t.thetaProdFactor_neg_q_factor_ne_zero n hn

/-- The middle factor `thetaProdFactor (q · u)` vanishes exactly along `u = -q⁻⁽ⁿ⁺¹⁾`. -/
private lemma factor2_pointwise (u : Kˣ) (n : ℕ) :
    (1 : K) + (t.q : K) ^ n * ((t.q : K) * (u : K)) = 0 ↔
      (u : K) = -(t.q : K) ^ (-((n : ℤ) + 1)) := by
  have hqn : (t.q : K) ^ (n + 1) ≠ 0 := pow_ne_zero _ t.q.ne_zero
  rw [show (-((n : ℤ) + 1)) = -(((n + 1 : ℕ)) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  constructor
  · intro h; field_simp; linear_combination h
  · intro h; rw [h]; field_simp; ring

/-- The trailing factor `thetaProdFactor u⁻¹` vanishes exactly along `u = -qⁿ`. -/
private lemma factor3_pointwise (u : Kˣ) (n : ℕ) :
    (1 : K) + (t.q : K) ^ n * (u : K)⁻¹ = 0 ↔ (u : K) = -(t.q : K) ^ (n : ℤ) := by
  have hu : (u : K) ≠ 0 := u.ne_zero
  rw [zpow_natCast]
  constructor
  · intro h; field_simp at h; linear_combination h
  · intro h; rw [h]; field_simp; ring

/-- **The zero divisor of the product form.** The `q`-theta product vanishes exactly on the
`qᶻ`-orbit of `-1`:
```
thetaProd q u = 0  ↔  ∃ k : ℤ, (u : K) = -qᵏ.
```
The constant factor `thetaProdFactor (-q)` is nonzero, so `thetaProd u = 0` iff one of the two
`u`-dependent factors vanishes; `factor2_pointwise`/`factor3_pointwise` locate their zeros at the
exponents `-(n+1)` and `n`, which together sweep out all of `ℤ`. -/
theorem thetaProd_eq_zero_iff [CompleteSpace K] (u : Kˣ) :
    t.thetaProd u = 0 ↔ ∃ k : ℤ, (u : K) = -(t.q : K) ^ k := by
  rw [thetaProd_apply, mul_eq_zero, mul_eq_zero, or_iff_right t.thetaProdFactor_neg_q_ne_zero,
    t.thetaProdFactor_eq_zero_iff, t.thetaProdFactor_eq_zero_iff]
  simp only [t.factor2_pointwise u, t.factor3_pointwise u]
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact ⟨-((n : ℤ) + 1), hn⟩
    · exact ⟨(n : ℤ), hn⟩
  · rintro ⟨k, hk⟩
    by_cases h0 : 0 ≤ k
    · right
      exact ⟨k.toNat, by rw [Int.toNat_of_nonneg h0]; exact hk⟩
    · left
      refine ⟨(-k - 1).toNat, ?_⟩
      rw [show (-(((-k - 1).toNat : ℤ) + 1)) = k by
        rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -k - 1)]; ring]
      exact hk

/-- **The zeros form a single `qᶻ`-orbit.** Any two zeros of `thetaProd` differ by an integer
power of `q`, so the zero locus descends to a single point of `Kˣ/qᶻ` — a degree-one divisor on
the Tate curve. -/
theorem thetaProd_zero_orbit [CompleteSpace K] {u v : Kˣ}
    (hu : t.thetaProd u = 0) (hv : t.thetaProd v = 0) :
    ∃ k : ℤ, (u : K) = (t.q : K) ^ k * (v : K) := by
  obtain ⟨a, ha⟩ := (t.thetaProd_eq_zero_iff u).mp hu
  obtain ⟨b, hb⟩ := (t.thetaProd_eq_zero_iff v).mp hv
  have hqb : (t.q : K) ^ b ≠ 0 := zpow_ne_zero b t.q.ne_zero
  refine ⟨a - b, ?_⟩
  rw [ha, hb, zpow_sub₀ t.q.ne_zero]
  field_simp

/-- **The zero divisor of the series `theta`, granted the `theta = thetaProd` identity.** Once the
Jacobi-triple-product identity `theta u = thetaProd u` (the documented seam in
`TateCurvesTheta.Theta.Product`) is available at `u`, the divisor of the naive theta series is the
same `qᶻ`-orbit of `-1` as for the product form. -/
theorem theta_eq_zero_iff_of_eq_thetaProd [CompleteSpace K] (u : Kˣ)
    (h : t.theta u = t.thetaProd u) :
    t.theta u = 0 ↔ ∃ k : ℤ, (u : K) = -(t.q : K) ^ k := by
  rw [h]; exact t.thetaProd_eq_zero_iff u

end TateParameter

end TateCurvesTheta
