/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.Theta.Periodicity

/-!
# Series-side vanishing of the `q`-theta function on the orbit `-qᶻ`

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the naive
`q`-theta series `theta q u = ∑' n : ℤ, q ^ (e n) · uⁿ` (with `e n = n(n+1)/2`, `Theta/Basic.lean`)
vanishes on the whole `qᶻ`-orbit of `-1`. This is the elementary "`⇐`" direction of the theta
divisor, proved here **directly from the series** — without the Jacobi triple product identity
`theta = thetaProd` (`Theta/TripleProduct.lean`) and without the `RatioLaurentRepr` seam.

The base case `theta(-1) = 0` (in characteristic `≠ 2`) is a fixed-point-free pairing argument: the
involution `σ : n ↦ -(n+1)` of `ℤ` fixes the exponent (`e(-(n+1)) = e n`) while flipping the sign of
the monomial (`(-1)^{-(n+1)} = -(-1)ⁿ`), so it pairs each term of `theta(-1)` with its negative.
Reindexing the sum by `σ` therefore gives `theta(-1) = -theta(-1)`, whence `theta(-1) = 0` once
`2 ≠ 0`. The orbit form `theta(-qᵏ) = 0` then follows from the `qᶻ`-automorphy `theta_zpow_q_smul`
(`Theta/Periodicity.lean`), since `-qᵏ = qᵏ · (-1)` and the automorphy factor is a unit.

This is the vanishing that makes the pole cancellation of `theta / thetaProd` rigorous in the global
assembly of `RatioLaurentRepr` (issue #142), and it settles one direction of the series theta
divisor unconditionally.

## The characteristic `≠ 2` hypothesis

The hypothesis `(2 : K) ≠ 0` is genuine, not a convenience: in characteristic `2` the pairing
`n ↔ -(n+1)` is still fixed-point-free but the two paired terms **coincide** (`-x = x`) instead of
cancelling, so the argument gives `theta(-1) = theta(-1)` and no vanishing. It is stated as an
explicit hypothesis on the individual theorems rather than as a global assumption on `K`.

## Main results

* `TateParameter.theta_neg_one_eq_zero` : `theta(-1) = 0` for `(2 : K) ≠ 0`.
* `TateParameter.theta_eq_zero_of_neg_qzpow` : `theta u = 0` whenever `(u : K) = -qᵏ`.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (T : TateParameter K)

/-- The triangular exponent `e n = n(n+1)/2` is invariant under the involution `n ↦ -(n+1)`:
`e(-(n+1)) = e n`. Both sides double to `n(n+1)` (`two_mul_thetaExp`), so they are equal. -/
private lemma thetaExp_neg_add_one (n : ℤ) : thetaExp (-(n + 1)) = thetaExp n := by
  have hAB : 2 * thetaExp (-(n + 1)) = 2 * thetaExp n := by
    rw [two_mul_thetaExp, two_mul_thetaExp]; ring
  omega

/-- **The `q`-theta series vanishes at `-1`** (in characteristic `≠ 2`). The involution
`σ n = -(n+1)` of `ℤ` is fixed-point-free and sends the `n`-th term `q^(e n) · (-1)ⁿ` of `theta(-1)`
to its negative (`e` is `σ`-invariant while `(-1)^{-(n+1)} = -(-1)ⁿ`). Reindexing the defining sum
by `σ` thus yields `theta(-1) = -theta(-1)`, so `2 · theta(-1) = 0`; since `2 ≠ 0`,
`theta(-1) = 0`. -/
theorem theta_neg_one_eq_zero (h2 : (2 : K) ≠ 0) : T.theta (-1) = 0 := by
  -- The involution `σ n = -(n + 1)` as a permutation of `ℤ`.
  have hinv : Function.Involutive (fun n : ℤ => -(n + 1)) := by
    intro n; change -(-(n + 1) + 1) = n; ring
  set σ : Equiv.Perm ℤ := hinv.toPerm with hσ
  have hσ_apply : ∀ n : ℤ, σ n = -(n + 1) := fun n => rfl
  -- Each term is sent to its negative by `σ`.
  have hkey : ∀ n : ℤ, T.thetaTerm (-1) (σ n) = -T.thetaTerm (-1) n := by
    intro n
    simp only [thetaTerm, Units.coe_neg_one, hσ_apply, thetaExp_neg_add_one]
    have hpow : (-1 : K) ^ (-(n + 1)) = -((-1 : K) ^ n) := by
      rcases Int.even_or_odd n with he | ho
      · rw [((he.add_one).neg).neg_one_zpow, he.neg_one_zpow]
      · rw [((ho.add_one).neg).neg_one_zpow, ho.neg_one_zpow, neg_neg]
    rw [hpow]; ring
  -- Reindexing by `σ` gives `theta(-1) = -theta(-1)`.
  have hself : T.theta (-1) = -T.theta (-1) := by
    have e1 : (∑' n : ℤ, T.thetaTerm (-1) (σ n)) = T.theta (-1) :=
      Equiv.tsum_eq σ (T.thetaTerm (-1))
    calc
      T.theta (-1) = ∑' n : ℤ, T.thetaTerm (-1) (σ n) := e1.symm
      _ = ∑' n : ℤ, -T.thetaTerm (-1) n := tsum_congr hkey
      _ = -∑' n : ℤ, T.thetaTerm (-1) n := tsum_neg
      _ = -T.theta (-1) := rfl
  -- `2 · theta(-1) = 0`, and `2 ≠ 0`, so `theta(-1) = 0`.
  have h2S : (2 : K) * T.theta (-1) = 0 := by
    rw [two_mul]; nth_rewrite 2 [hself]; ring
  rcases mul_eq_zero.mp h2S with h | h
  · exact absurd h h2
  · exact h

/-- **The `q`-theta series vanishes on the orbit `-qᶻ`.** If `(u : K) = -qᵏ` for some `k : ℤ`, then
`theta u = 0` (in characteristic `≠ 2`). Writing `u = qᵏ · (-1)` and applying the `qᶻ`-automorphy
`theta_zpow_q_smul`, `theta u` is the unit automorphy factor times `theta(-1) = 0`. -/
theorem theta_eq_zero_of_neg_qzpow (h2 : (2 : K) ≠ 0) (k : ℤ) {u : Kˣ}
    (hu : (u : K) = -(T.q : K) ^ k) : T.theta u = 0 := by
  have huu : u = T.q ^ k * (-1 : Kˣ) := by
    apply Units.ext
    rw [hu, Units.val_mul, Units.coe_neg_one, Units.val_zpow_eq_zpow_val]
    ring
  rw [huu, T.theta_zpow_q_smul (-1) k, T.theta_neg_one_eq_zero h2, mul_zero]

end TateParameter

end TateCurvesTheta
