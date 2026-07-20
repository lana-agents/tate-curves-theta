/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.Theta.Uniqueness
import TateCurvesTheta.Theta.Divisor

/-!
# `theta = thetaProd` from a global Laurent expansion of `thetaProd` (a cleaner reduction)

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the naive
`q`-theta series `theta` (`Theta/Basic.lean`) and the product form `thetaProd`
(`Theta/Product.lean`) both satisfy the *same* automorphy relation
`f (q·u) = (q·u)⁻¹ · f u` (`theta_q_smul`, `thetaProd_q_smul`). The **Jacobi triple product
identity** asserts they coincide: `theta t u = thetaProd t u`.

This file gives a reduction of that identity to a **single, clean analytic seam**: that
`thetaProd` is a *global* two-sided Laurent series,
```
TateParameter.ThetaProdLaurentRepr t :
  ∃ b : ℤ → K, (∀ u, Summable (n ↦ bₙ uⁿ)) ∧ (∀ u, thetaProd u = ∑' n, bₙ uⁿ).
```
It is deliberately a strict simplification of the earlier `RatioLaurentRepr` seam of
`Theta/TripleProduct.lean` (#124/#142):

* it is a statement about `thetaProd` **alone** — no division by `thetaProd`, no ratio;
* it carries **no** bundled `q`-invariance clause. Where `RatioLaurentRepr` had to *assume* the
  `q`-invariance of the ratio's coefficients (deriving it on all of `Kˣ` needs a
  density/continuity argument across the zero locus `-qᶻ`), here the corresponding recursion on
  the coefficients of `thetaProd` is **derived** below, purely from the automorphy relation
  `thetaProd_q_smul` and coefficient uniqueness.

## The mathematical core (elementary, given the seam and coefficient uniqueness)

Write `thetaProd u = ∑' n, bₙ uⁿ`. Feeding `u ↦ q·u` and comparing with the automorphy relation
`thetaProd (q·u) = (q·u)⁻¹ · thetaProd u`:
```
∑' n, (bₙ qⁿ) uⁿ  =  thetaProd (q·u)  =  (q·u)⁻¹ · thetaProd u  =  ∑' n, (bₙ₊₁ q⁻¹) uⁿ,
```
the right-hand reindexing being `∑' n, bₙ (q·u)⁻¹ uⁿ = ∑' n, bₙ q⁻¹ uⁿ⁻¹ = ∑' n, bₙ₊₁ q⁻¹ uⁿ`.
*Laurent coefficient uniqueness* (`LaurentCoeffUnique`) forces `bₙ qⁿ = bₙ₊₁ q⁻¹`, i.e. the
recursion `bₙ₊₁ = qⁿ⁺¹ bₙ`. Its unique solution is `bₙ = b₀ · q^(e n)` with `e n = n(n+1)/2`
the triangular exponent of `theta` (`thetaExp`), because `e (n+1) - e n = n+1`. Hence
```
thetaProd u = ∑' n, b₀ · q^(e n) · uⁿ = b₀ · theta u   for every u : Kˣ,
```
and a single normalization value `theta u₀ = thetaProd u₀ ≠ 0` pins `b₀ = 1`, giving
`theta = thetaProd`.

## Why the summability obligation is trivial here (and where the real difficulty now lives)

The `RatioLaurentRepr` route requires the ratio's Laurent coefficients to be summable on **all**
of `Kˣ` (clause (a) of `RatioLaurentRepr`). That clause is genuinely obstructed: the honest
`ratio = theta / thetaProd` coefficients obtained from the annulus reciprocal
(`Theta/RatioAnnulus.lean`) do *not* have norms tending to `0` as `n → -∞` (a nonarchimedean
sup-of-norms bound on the three-fold Cauchy product leaves a norm-`≤ 1` contribution from the
low-order term), so global summability of that family cannot come from norm estimates — its true
decay *is* the triple product identity. This reduction sidesteps that obstruction: the honest
coefficients of `thetaProd` are `bₙ = q^(e n)`, whose family is *already* known to be summable
(`thetaTerm_summable`). The **only** residual content of `ThetaProdLaurentRepr` is therefore the
*factorization* — that the infinite product `thetaProd` admits a global Laurent development at
all, i.e. is a rigid-analytic function on the annulus `Kˣ`. That is the correct, minimal target
for closing `theta = thetaProd` (its natural home is a nonarchimedean "analytic-on-an-annulus
functions have a global Laurent expansion" principle, not yet in this tree).

## Main definitions

* `TateCurvesTheta.TateParameter.ThetaProdLaurentRepr` : the clean seam — `thetaProd` is a global
  two-sided Laurent series.

## Main results

* `TateParameter.thetaExp_succ` : `e (n+1) = e n + (n+1)` for the triangular exponent.
* `TateParameter.thetaProd_eq_const_mul_theta` : given `LaurentCoeffUnique K` and
  `ThetaProdLaurentRepr t`, there is a constant `b₀` with `thetaProd u = b₀ · theta u` for all `u`.
* `TateParameter.theta_eq_thetaProd_of_thetaProdLaurent` : with, in addition, one normalization
  value, `theta = thetaProd`.
* `TateParameter.theta_eq_zero_iff_of_thetaProdLaurent` : the resulting unconditional-on-the-seam
  series-theta divisor.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.4 (Jacobi triple product via the
  functional-equation uniqueness argument).
* S. Mochizuki, *The Étale Theta Function*, §1, Proposition 1.4.
-/

namespace TateCurvesTheta

/-- The triangular exponent satisfies `e (n+1) = e n + (n+1)`; equivalently the coefficients of
`theta`, `q^(e n)`, obey the same `q`-difference recursion as any global Laurent expansion of a
function with `theta`'s automorphy factor. -/
lemma thetaExp_succ (n : ℤ) : thetaExp (n + 1) = thetaExp n + (n + 1) := by
  have h1 : 2 * thetaExp (n + 1) = 2 * thetaExp n + 2 * (n + 1) := by
    rw [two_mul_thetaExp, two_mul_thetaExp]; ring
  omega

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-- **The clean analytic seam for the triple product identity.** The product form `thetaProd`
is a convergent two-sided Laurent series: there is a coefficient family `b : ℤ → K`, summable on
all of `Kˣ`, with `thetaProd u = ∑' n, bₙ uⁿ` for every `u`.

Unlike `RatioLaurentRepr` (`Theta/TripleProduct.lean`) this is a statement about `thetaProd`
alone and carries no `q`-invariance clause: the required recursion on the `bₙ` is *derived* from
`thetaProd_q_smul` in `thetaProd_eq_const_mul_theta`. -/
def ThetaProdLaurentRepr : Prop :=
  ∃ b : ℤ → K,
    (∀ u : Kˣ, Summable fun n : ℤ => b n * (u : K) ^ n) ∧
    (∀ u : Kˣ, t.thetaProd u = ∑' n : ℤ, b n * (u : K) ^ n)

omit [IsUltrametricDist K] in
/-- **`thetaProd` is a constant multiple of `theta`.** Given the Laurent coefficient uniqueness
principle `LaurentCoeffUnique K` and a global Laurent expansion of `thetaProd`
(`ThetaProdLaurentRepr t`), the automorphy relation `thetaProd_q_smul` forces the recursion
`bₙ₊₁ = qⁿ⁺¹ bₙ` on the coefficients (via coefficient uniqueness), whose unique solution
`bₙ = b₀ · q^(e n)` matches the coefficients of `theta`. Hence `thetaProd u = b₀ · theta u` for
every `u : Kˣ`. -/
theorem thetaProd_eq_const_mul_theta (huniq : LaurentCoeffUnique K)
    (hrepr : t.ThetaProdLaurentRepr) :
    ∃ b₀ : K, ∀ u : Kˣ, t.thetaProd u = b₀ * t.theta u := by
  obtain ⟨b, hsum, hfact⟩ := hrepr
  have hqne : (t.q : K) ≠ 0 := t.q.ne_zero
  -- The two coefficient families whose Laurent series both compute `thetaProd (q·u)`:
  -- `A n = bₙ qⁿ` (from `∑ bₙ (q·u)ⁿ`) and `B n = bₙ₊₁ q⁻¹` (from `(q·u)⁻¹ ∑ bₙ uⁿ`).
  -- Summability of `A`.
  have hAsum : ∀ v : Kˣ, Summable fun n : ℤ => (b n * (t.q : K) ^ n) * (v : K) ^ n := by
    intro v
    refine (hsum (t.q * v)).congr fun n => ?_
    rw [Units.val_mul, mul_zpow]; ring
  -- Summability of `B`: reindex the summable family `n ↦ bₙ vⁿ` by the shift `n ↦ n + 1`.
  have hBsum : ∀ v : Kˣ, Summable fun n : ℤ => (b (n + 1) * (t.q : K)⁻¹) * (v : K) ^ n := by
    intro v
    have h1 : Summable fun n : ℤ => b (n + 1) * (v : K) ^ (n + 1) :=
      (hsum v).comp_injective (i := fun n : ℤ => n + 1) fun a c h => by simpa using h
    have h2 : Summable fun n : ℤ => b (n + 1) * (v : K) ^ n := by
      refine (h1.mul_right (v : K)⁻¹).congr fun n => ?_
      rw [mul_assoc, zpow_add_one₀ v.ne_zero, mul_assoc, mul_inv_cancel₀ v.ne_zero, mul_one]
    refine (h2.mul_left (t.q : K)⁻¹).congr fun n => ?_
    ring
  -- The `A`-series computes `thetaProd (q·v)`.
  have hAeq : ∀ v : Kˣ,
      (∑' n : ℤ, (b n * (t.q : K) ^ n) * (v : K) ^ n) = t.thetaProd (t.q * v) := by
    intro v
    rw [hfact (t.q * v)]
    refine tsum_congr fun n => ?_
    rw [Units.val_mul, mul_zpow]; ring
  -- Reindexing lemma: `∑' n, bₙ₊₁ vⁿ = v⁻¹ · thetaProd v`.
  have hshift : ∀ v : Kˣ,
      (∑' n : ℤ, b (n + 1) * (v : K) ^ n) = (v : K)⁻¹ * t.thetaProd v := by
    intro v
    have key : (∑' n : ℤ, b (n + 1) * (v : K) ^ n)
        = ∑' m : ℤ, b m * (v : K) ^ m * (v : K)⁻¹ := by
      rw [← Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) fun m => b m * (v : K) ^ m * (v : K)⁻¹]
      refine tsum_congr fun n => ?_
      simp only [Equiv.coe_addRight]
      rw [mul_assoc]
      congr 1
      rw [zpow_add_one₀ v.ne_zero, mul_assoc, mul_inv_cancel₀ v.ne_zero, mul_one]
    rw [key, tsum_mul_right, ← hfact v, mul_comm]
  -- The `B`-series also computes `thetaProd (q·v)`.
  have hBeq : ∀ v : Kˣ,
      (∑' n : ℤ, (b (n + 1) * (t.q : K)⁻¹) * (v : K) ^ n) = t.thetaProd (t.q * v) := by
    intro v
    have hpull : (∑' n : ℤ, (b (n + 1) * (t.q : K)⁻¹) * (v : K) ^ n)
        = (t.q : K)⁻¹ * ∑' n : ℤ, b (n + 1) * (v : K) ^ n := by
      rw [← tsum_mul_left]; exact tsum_congr fun n => by ring
    rw [hpull, hshift v, thetaProd_q_smul, mul_inv]; ring
  -- Coefficient uniqueness: `bₙ qⁿ = bₙ₊₁ q⁻¹`.
  have hAB : (fun n : ℤ => b n * (t.q : K) ^ n) = fun n : ℤ => b (n + 1) * (t.q : K)⁻¹ :=
    huniq _ _ hAsum hBsum fun v => by rw [hAeq v, hBeq v]
  -- Hence the recursion `bₙ₊₁ = qⁿ⁺¹ bₙ`.
  have hrec : ∀ n : ℤ, b (n + 1) = (t.q : K) ^ (n + 1) * b n := by
    intro n
    have hABn : b n * (t.q : K) ^ n = b (n + 1) * (t.q : K)⁻¹ := congrFun hAB n
    calc b (n + 1)
        = b (n + 1) * (t.q : K)⁻¹ * (t.q : K) := by
          rw [mul_assoc, inv_mul_cancel₀ hqne, mul_one]
      _ = b n * (t.q : K) ^ n * (t.q : K) := by rw [← hABn]
      _ = b n * ((t.q : K) ^ n * (t.q : K)) := by ring
      _ = b n * (t.q : K) ^ (n + 1) := by rw [← zpow_add_one₀ hqne]
      _ = (t.q : K) ^ (n + 1) * b n := by ring
  -- Solve the recursion: `bₙ = b₀ · q^(e n)` (matching `theta`'s coefficients).
  have hclosed : ∀ n : ℤ, b n = b 0 * (t.q : K) ^ thetaExp n := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [thetaExp]
    | succ i ih =>
        have hts : thetaExp ((i : ℤ) + 1) = thetaExp (i : ℤ) + ((i : ℤ) + 1) :=
          thetaExp_succ (i : ℤ)
        rw [hrec (i : ℤ), ih, hts, zpow_add₀ hqne (thetaExp (i : ℤ)) ((i : ℤ) + 1)]; ring
    | pred i ih =>
        -- From `hrec (-i-1)` : `b(-i) = q^(-i) · b(-i-1)`, solve for `b(-i-1)`.
        have hr : b (-(i : ℤ)) = (t.q : K) ^ (-(i : ℤ)) * b (-(i : ℤ) - 1) := by
          have h := hrec (-(i : ℤ) - 1); simpa using h
        have hstep : b (-(i : ℤ) - 1) = (t.q : K) ^ (i : ℤ) * b (-(i : ℤ)) := by
          rw [hr, ← mul_assoc, ← zpow_add₀ hqne]; simp
        have hts : thetaExp (-(i : ℤ) - 1) = thetaExp (-(i : ℤ)) + (i : ℤ) := by
          have h := thetaExp_succ (-(i : ℤ) - 1); simp only [sub_add_cancel] at h; omega
        rw [hstep, ih, hts, zpow_add₀ hqne (thetaExp (-(i : ℤ))) (i : ℤ)]; ring
  -- Conclude: `thetaProd u = ∑ b₀ q^(e n) uⁿ = b₀ · theta u`.
  refine ⟨b 0, fun u => ?_⟩
  rw [hfact u, theta_apply, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [hclosed n]; ring

omit [IsUltrametricDist K] in
/-- **The Jacobi triple product identity `theta = thetaProd`, from the clean seam.** Beyond the
coefficient-uniqueness principle and the global Laurent expansion of `thetaProd`, all that is
needed is one normalization value: a point `u₀` with `theta u₀ ≠ 0` and `theta u₀ = thetaProd u₀`.
This pins the constant `b₀` of `thetaProd_eq_const_mul_theta` to `1`. -/
theorem theta_eq_thetaProd_of_thetaProdLaurent (huniq : LaurentCoeffUnique K)
    (hrepr : t.ThetaProdLaurentRepr) {u₀ : Kˣ} (hu₀ : t.theta u₀ ≠ 0)
    (hnorm : t.theta u₀ = t.thetaProd u₀) (u : Kˣ) :
    t.theta u = t.thetaProd u := by
  obtain ⟨b₀, hb₀⟩ := t.thetaProd_eq_const_mul_theta huniq hrepr
  -- Normalize: `theta u₀ = thetaProd u₀ = b₀ · theta u₀`, so `theta u₀ ≠ 0` gives `b₀ = 1`.
  have hb1 : b₀ = 1 := by
    have h := hb₀ u₀
    rw [← hnorm] at h
    have h' : (b₀ - 1) * t.theta u₀ = 0 := by ring_nf; linear_combination -h
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact sub_eq_zero.mp h''
    · exact absurd h'' hu₀
  rw [hb₀ u, hb1, one_mul]

omit [IsUltrametricDist K] in
/-- **The zero divisor of the naive series `theta`, from the clean seam.** Given the
coefficient-uniqueness principle, the global Laurent expansion of `thetaProd`, and the single
normalization value, the series `theta` vanishes exactly on the `qᶻ`-orbit of `-1`. This
discharges the conditionality of `theta_eq_zero_iff_of_eq_thetaProd` (`Theta/Divisor.lean`, #88)
via the `ThetaProdLaurentRepr` seam. -/
theorem theta_eq_zero_iff_of_thetaProdLaurent (huniq : LaurentCoeffUnique K)
    (hrepr : t.ThetaProdLaurentRepr) {u₀ : Kˣ} (hu₀ : t.theta u₀ ≠ 0)
    (hnorm : t.theta u₀ = t.thetaProd u₀) (u : Kˣ) :
    t.theta u = 0 ↔ ∃ k : ℤ, (u : K) = -(t.q : K) ^ k :=
  t.theta_eq_zero_iff_of_eq_thetaProd u
    (t.theta_eq_thetaProd_of_thetaProdLaurent huniq hrepr hu₀ hnorm u)

end TateParameter

end TateCurvesTheta
