/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.LinearCombination

/-!
# q-Pochhammer symbols, Gaussian binomial coefficients, and the finite q-Vandermonde identity

Self-contained **finite** q-series infrastructure over a commutative ring, with a fixed base
`q : R`. Nothing here is analytic: no summability, no norms, no nonarchimedean hypotheses. Mathlib
has none of this (no `qPochhammer`, no Gaussian binomials, no q-Vandermonde), so it is built from
scratch. This is the finite engine of the **Durfee-square identity**
`∑ₖ q^{k²}/((q;q)ₖ)² = 1/(q;q)_∞` used to pin the Jacobi triple product normalization
`thetaProdNormConst = 1` (`Theta/Normalization.lean`); the analytic `n → ∞` limit lives in the
companion issue.

## Main definitions

* `TateCurvesTheta.qPoch q k = ∏ⱼ<ₖ (1 - q^{j+1})` : the finite q-Pochhammer symbol `(q;q)ₖ`.
* `TateCurvesTheta.gaussBinom q n k` : the Gaussian binomial coefficient `[n;k]_q`, defined by the
  q-Pascal recursion `[n+1;k+1] = [n;k+1] + q^{n-k}·[n;k]`, `[n;0] = 1`, `[0;k+1] = 0`.

## Main results

* `gaussBinom_mul_qPoch` : the closed form (division-free) `[n;k]·(q;q)ₖ·(q;q)_{n-k} = (q;q)ₙ`
  for `k ≤ n`.
* `gaussBinom_symm` : the symmetry `[n;k] = [n;n-k]` (`k ≤ n`), over a field where the `(q;q)`
  factors are units.
* `qbtPoly_coeff` : the finite q-binomial theorem (Rothe/Gauss)
  `[Xᵏ] ∏ᵢ<ₙ (C(c·qⁱ)·X + 1) = cᵏ·q^{k(k-1)/2}·[n;k]_q` for `k ≤ n`.
* `gaussBinom_two_mul_self` : the finite q-Vandermonde / Durfee-square identity
  `∑ₖ q^{k²}·([n;k]_q)² = [2n;n]_q` (over a field with `q ≠ 0` and the `(q;q)` factors units).

## References

* G. E. Andrews, *The Theory of Partitions*, §3.3 (Durfee squares, Gaussian binomials).
* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.2 (q-binomial theorem).
* V. Kac, P. Cheung, *Quantum Calculus*, §6 (Gaussian binomials, q-Vandermonde).
-/

open Finset Polynomial

namespace TateCurvesTheta

section CommRing

variable {R : Type*} [CommRing R] (q : R)

/-- The finite **q-Pochhammer symbol** `(q;q)ₖ = ∏_{j=1}^{k} (1 - qʲ)`. -/
def qPoch (q : R) : ℕ → R
  | 0 => 1
  | (k + 1) => qPoch q k * (1 - q ^ (k + 1))

@[simp] lemma qPoch_zero : qPoch q 0 = 1 := rfl

lemma qPoch_succ (k : ℕ) : qPoch q (k + 1) = qPoch q k * (1 - q ^ (k + 1)) := rfl

/-- The **Gaussian binomial coefficient** `[n;k]_q`, defined by the q-Pascal recursion
`[n;0] = 1`, `[0;k+1] = 0`, `[n+1;k+1] = [n;k+1] + q^{n-k}·[n;k]`. -/
def gaussBinom (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, (_ + 1) => 0
  | (n + 1), (k + 1) => gaussBinom q n (k + 1) + q ^ (n - k) * gaussBinom q n k

@[simp] lemma gaussBinom_zero_right (n : ℕ) : gaussBinom q n 0 = 1 := by
  cases n <;> rfl

@[simp] lemma gaussBinom_zero_succ (k : ℕ) : gaussBinom q 0 (k + 1) = 0 := rfl

/-- The defining q-Pascal recursion. -/
lemma gaussBinom_succ_succ (n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = gaussBinom q n (k + 1) + q ^ (n - k) * gaussBinom q n k := rfl

/-- Above the diagonal the Gaussian binomial vanishes: `[n;k] = 0` for `n < k`. -/
lemma gaussBinom_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → gaussBinom q n k = 0
  | 0, 0, h => absurd h (by omega)
  | 0, (_ + 1), _ => rfl
  | (_ + 1), 0, h => absurd h (by omega)
  | (n + 1), (k + 1), h => by
      rw [gaussBinom_succ_succ, gaussBinom_eq_zero_of_lt (by omega : n < k + 1),
        gaussBinom_eq_zero_of_lt (by omega : n < k)]
      ring

/-- On the diagonal the Gaussian binomial is `1`: `[n;n] = 1`. -/
@[simp] lemma gaussBinom_self : ∀ n : ℕ, gaussBinom q n n = 1
  | 0 => rfl
  | (n + 1) => by
      rw [gaussBinom_succ_succ, gaussBinom_eq_zero_of_lt q (by omega : n < n + 1),
        gaussBinom_self n]
      simp

/-- **Closed form of the Gaussian binomial (division-free).** For `k ≤ n`,
`[n;k]_q · (q;q)ₖ · (q;q)_{n-k} = (q;q)ₙ`. Proved by induction on `n` using the defining q-Pascal
recursion; the telescoping `(1 - q^{n-k}) + q^{n-k}(1 - q^{k+1}) = 1 - q^{n+1}` closes the step. -/
lemma gaussBinom_mul_qPoch {n k : ℕ} (hk : k ≤ n) :
    gaussBinom q n k * (qPoch q k * qPoch q (n - k)) = qPoch q n := by
  induction n generalizing k with
  | zero => obtain rfl : k = 0 := Nat.le_zero.mp hk; simp
  | succ n ih =>
    match k, hk with
    | 0, _ => simp
    | k + 1, hk =>
      rcases Nat.lt_or_ge k n with hkn | hkn
      · -- interior step `k + 1 ≤ n`: both inductive hypotheses are available
        have ihk := ih (show k ≤ n by omega)
        have ihk1 := ih (show k + 1 ≤ n by omega)
        have hsub : qPoch q (n - k) = qPoch q (n - (k + 1)) * (1 - q ^ (n - k)) := by
          have he : n - k = (n - (k + 1)) + 1 := by omega
          rw [he, qPoch_succ]
        have hn1 : q ^ (n + 1) = q ^ (n - k) * q ^ (k + 1) := by
          rw [← pow_add]; congr 1; omega
        rw [qPoch_succ q k] at ihk1
        rw [Nat.succ_sub_succ, gaussBinom_succ_succ, qPoch_succ q k, qPoch_succ q n, hn1]
        rw [hsub] at ihk ⊢
        linear_combination (1 - q ^ (n - k)) * ihk1 + q ^ (n - k) * (1 - q ^ (k + 1)) * ihk
      · -- diagonal `k = n`: `[n+1;n+1] = 1`
        obtain rfl : k = n := by omega
        simp

end CommRing

section Field

variable {K : Type*} [Field K] (q : K)

/-- The `(q;q)` factors are nonzero exactly when no `1 - q^{j+1}` vanishes. -/
lemma qPoch_ne_zero (hq : ∀ j : ℕ, (1 : K) - q ^ (j + 1) ≠ 0) : ∀ k : ℕ, qPoch q k ≠ 0
  | 0 => by simp
  | (k + 1) => by
      rw [qPoch_succ]
      exact mul_ne_zero (qPoch_ne_zero hq k) (hq k)

/-- **Symmetry of the Gaussian binomial:** `[n;k] = [n;n-k]` for `k ≤ n`. Both sides satisfy the
same closed form `(q;q)ₙ / ((q;q)ₖ·(q;q)_{n-k})`; cancelling the nonzero `(q;q)` factors gives the
identity. -/
lemma gaussBinom_symm (hq : ∀ j : ℕ, (1 : K) - q ^ (j + 1) ≠ 0) {n k : ℕ} (hk : k ≤ n) :
    gaussBinom q n k = gaussBinom q n (n - k) := by
  have h1 := gaussBinom_mul_qPoch q hk
  have h2 := gaussBinom_mul_qPoch q (Nat.sub_le n k)
  rw [show n - (n - k) = k by omega] at h2
  have hne : qPoch q k * qPoch q (n - k) ≠ 0 :=
    mul_ne_zero (qPoch_ne_zero q hq k) (qPoch_ne_zero q hq (n - k))
  apply mul_right_cancel₀ hne
  rw [h1, ← h2]; ring

end Field

section Polynomial

variable {R : Type*} [CommRing R] (q c : R)

/-- The **Rothe / Gauss finite q-binomial product** `∏_{i<N} (c·qⁱ·X + 1)`, whose `Xᵏ`-coefficient
is `cᵏ·q^{k(k-1)/2}·[N;k]_q`. -/
noncomputable def qbtPoly (q c : R) (N : ℕ) : R[X] := ∏ i ∈ Finset.range N, (C (c * q ^ i) * X + 1)

@[simp] lemma qbtPoly_zero : qbtPoly q c 0 = 1 := by
  rw [qbtPoly, Finset.prod_range_zero]

lemma qbtPoly_succ (N : ℕ) :
    qbtPoly q c (N + 1) = qbtPoly q c N * (C (c * q ^ N) * X + 1) := by
  rw [qbtPoly, Finset.prod_range_succ, ← qbtPoly]

private lemma choose_two_succ (m : ℕ) : (m + 1).choose 2 = m.choose 2 + m := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

/-- **Finite q-binomial theorem (Rothe/Gauss).** For every `k`,
`[Xᵏ] ∏_{i<N} (c·qⁱ·X + 1) = cᵏ·q^{k(k-1)/2}·[N;k]_q`. (For `k > N` both sides vanish.) -/
lemma qbtPoly_coeff (N k : ℕ) :
    (qbtPoly q c N).coeff k = c ^ k * q ^ (k.choose 2) * gaussBinom q N k := by
  induction N generalizing k with
  | zero =>
      cases k with
      | zero => simp
      | succ k => rw [qbtPoly_zero, Polynomial.coeff_one, gaussBinom_zero_succ]; simp
  | succ N ih =>
      rw [qbtPoly_succ]
      cases k with
      | zero =>
          rw [Polynomial.mul_coeff_zero, ih 0]
          simp
      | succ m =>
          have hcoeff : (qbtPoly q c N * (C (c * q ^ N) * X + 1)).coeff (m + 1)
              = (c * q ^ N) * (qbtPoly q c N).coeff m + (qbtPoly q c N).coeff (m + 1) := by
            have hcomm : qbtPoly q c N * (C (c * q ^ N) * X)
                = C (c * q ^ N) * (qbtPoly q c N * X) := by ring
            rw [mul_add, mul_one, Polynomial.coeff_add, hcomm,
              Polynomial.coeff_C_mul, Polynomial.coeff_mul_X]
          rw [hcoeff, ih m, ih (m + 1), gaussBinom_succ_succ]
          have key : q ^ N * q ^ (m.choose 2) * gaussBinom q N m
              = q ^ ((m + 1).choose 2) * q ^ (N - m) * gaussBinom q N m := by
            rcases Nat.lt_or_ge N m with hmN | hmN
            · rw [gaussBinom_eq_zero_of_lt q hmN, mul_zero, mul_zero]
            · rw [← pow_add, ← pow_add]
              congr 2
              rw [choose_two_succ]; omega
          linear_combination c ^ (m + 1) * key

/-- **Splitting the q-binomial product.** `∏_{i<n+m}(c·qⁱ·X+1) = (∏_{i<n}) · (∏_{i<m} shifted)`,
where the shifted factor has base `c·qⁿ`. -/
lemma qbtPoly_add (n m : ℕ) :
    qbtPoly q c (n + m) = qbtPoly q c n * qbtPoly q (c * q ^ n) m := by
  rw [qbtPoly, qbtPoly, Finset.prod_range_add]
  congr 1
  rw [qbtPoly]
  apply Finset.prod_congr rfl
  intro i _
  rw [show c * q ^ (n + i) = c * q ^ n * q ^ i by rw [pow_add]; ring]

private lemma choose_two_add (k a : ℕ) : (k + a).choose 2 = k.choose 2 + a.choose 2 + k * a := by
  induction a with
  | zero => simp
  | succ a ih =>
      have h1 : k + (a + 1) = (k + a) + 1 := by ring
      rw [h1, choose_two_succ, ih, choose_two_succ]; ring

end Polynomial

section Durfee

variable {K : Type*} [Field K] {q : K}

private lemma exp_durfee {n k : ℕ} (h : k ≤ n) :
    k.choose 2 + (n - k).choose 2 + n * (n - k) = (n - k) * (n - k) + n.choose 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, n = k + a := ⟨n - k, by omega⟩
  simp only [Nat.add_sub_cancel_left]
  rw [choose_two_add]
  ring

/-- **The finite q-Vandermonde / Durfee-square identity** `∑ₖ q^{k²}·([n;k]_q)² = [2n;n]_q`, the
q-analogue of `∑ₖ C(n,k)² = C(2n,n)` and the finite engine of the Durfee-square identity
`∑ₖ q^{k²}/((q;q)ₖ)² = 1/(q;q)_∞`. Proved by extracting the `Xⁿ`-coefficient of `∏_{i<2n}(qⁱ·X+1)`
two ways (directly, and after splitting the product in half), then cancelling the common factor
`q^{n(n-1)/2}` and applying the symmetry `[n;k] = [n;n-k]`. -/
theorem gaussBinom_two_mul_self (hq0 : q ≠ 0) (hq : ∀ j : ℕ, (1 : K) - q ^ (j + 1) ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), q ^ (k * k) * gaussBinom q n k ^ 2 = gaussBinom q (2 * n) n := by
  -- The `Xⁿ`-coefficient of `∏_{i<2n}(qⁱ·X+1)`, computed directly.
  have hdirect : (qbtPoly q 1 (n + n)).coeff n = q ^ (n.choose 2) * gaussBinom q (2 * n) n := by
    rw [qbtPoly_coeff, one_pow, one_mul, two_mul]
  -- The same coefficient, computed after splitting the product in half.
  have hsplit : (qbtPoly q 1 (n + n)).coeff n
      = ∑ k ∈ Finset.range (n + 1),
          q ^ (k.choose 2) * gaussBinom q n k
            * ((q ^ n) ^ (n - k) * q ^ ((n - k).choose 2) * gaussBinom q n (n - k)) := by
    rw [qbtPoly_add, one_mul, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro k _
    rw [qbtPoly_coeff, qbtPoly_coeff, one_pow, one_mul]
  -- Combine: both computations agree.
  rw [hdirect] at hsplit
  -- Rewrite each summand's `q`-power as `q^{n(n-1)/2} · q^{(n-k)²}`.
  have hstep : q ^ (n.choose 2) * gaussBinom q (2 * n) n
      = q ^ (n.choose 2)
        * ∑ k ∈ Finset.range (n + 1),
            q ^ ((n - k) * (n - k)) * (gaussBinom q n k * gaussBinom q n (n - k)) := by
    rw [hsplit, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    have hpow : q ^ (k.choose 2) * gaussBinom q n k
          * ((q ^ n) ^ (n - k) * q ^ ((n - k).choose 2) * gaussBinom q n (n - k))
        = q ^ (k.choose 2 + (n - k).choose 2 + n * (n - k))
          * (gaussBinom q n k * gaussBinom q n (n - k)) := by
      rw [← pow_mul, pow_add, pow_add]; ring
    rw [hpow, exp_durfee hk, pow_add]
    ring
  -- Cancel the common nonzero factor `q^{n(n-1)/2}`.
  have hcancel := mul_left_cancel₀ (pow_ne_zero (n.choose 2) hq0) hstep
  -- Reindex `k ↦ n - k` and apply symmetry `[n;n-k] = [n;k]` to reach the squared form.
  rw [hcancel, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  simp only [Nat.add_sub_cancel]
  rw [← gaussBinom_symm q hq hk]
  ring

end Durfee

end TateCurvesTheta
