/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TateCurvesTheta.TateCurve.EisensteinKernels
import TateCurvesTheta.TateCurve.Weierstrass

/-!
# `q`-expansions of the Eisenstein-kernel series of a Tate parameter

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the
elementary Eisenstein computation of the Tate Weierstrass identity (Silverman, *Advanced
Topics*, Ch. V, Thm 3.1; Weil) produces, after folding the `d`-weighted orbit sums by the
kernel parities, six constant `q`-series built from the Eisenstein kernels of
`TateCurve/EisensteinKernels.lean`:
```
𝔭 = ∑ₖ p(qᵏ),   𝔯 = ∑ₖ k·r(qᵏ),   𝛗 = ∑ₖ φ(qᵏ),   𝛙 = ∑ₖ k·ψ(qᵏ),
𝔭₂ = ∑ₖ p(qᵏ)²,   𝔭𝔯 = ∑ₖ k·p(qᵏ)r(qᵏ)          (k ≥ 1).
```
This file defines these series, proves their (geometric, ultrametric) convergence, and
computes their `q`-expansions with per-`N` **divisor-sum coefficients**, together with the
`q`-expansions of the classical series `sₖ(q)` (`TateParameter.eisenstein`) and the Cauchy
products `s₁²`, `s₁s₃`, `s₁·𝔯`, `s₁³` needed by the final bracket identities.

The analytic backbone is twofold:

* **power-weight generating functions** of the kernels on `‖x‖ < 1`:
  `p, r, φ, ψ` generate `∑ⱼ jᵐ xʲ` for `m = 1, 2, 3, 4`, while `p²` and `p·r` have
  binomial-coefficient expansions (`∑ⱼ C(j+1,3) xʲ` and `∑ⱼ (C(j+2,4)+C(j+1,4)) xʲ`);
  everything is assembled `ℤ`-linearly from `hasSum_choose_mul_geometric_of_norm_lt_one`
  via integer binomial identities such as `j³ = 6·C(j,3) + 6·C(j,2) + j`, so that no
  division by `2`, `6`, `12` or `24` ever occurs and all statements hold in every
  characteristic;
* the **divisor-fiber Fubini** `TateParameter.tsum_weighted_qpow_eq`: the double series
  `∑ₘ f(m) ∑ⱼ g(j) q^{mj}` regroups along the fibration `(m, j) ↦ m·j` of `ℕ+ × ℕ+` into
  `∑_N (∑_{de = N} f(d)g(e)) q^N`, proven ultrametrically (the analytic lemmas of
  `Mathlib.NumberTheory.TsumDivisorsAntidiagonal` require `NormSMulClass ℤ 𝕜`, which fails
  nonarchimedeanly; only the combinatorial equivalence `sigmaAntidiagonalEquivProd` is
  reused).

## Main definitions

* `TateParameter.pSum`, `rSum`, `phiSum`, `psiSum`, `pSqSum`, `prSum`: the six kernel
  series.

## Main results

* `TateCurvesTheta.hasSum_pow_mul_geometric_eisP` (and `_eisR`, `_eisPhi`, `_eisPsi`,
  `hasSum_choose_eisP_sq`, `hasSum_choose_eisP_mul_eisR`): the kernel generating functions.
* `TateParameter.summable_pSum_terms` … `summable_prSum_terms`: geometric convergence.
* `TateParameter.tsum_weighted_qpow_eq`: the divisor-fiber Fubini.
* `TateParameter.eisenstein_eq_qexp`, `pSum_eq_qexp`, `rSum_eq_qexp`, `phiSum_eq_qexp`,
  `psiSum_eq_qexp`, `pSqSum_mul_six_eq_qexp`, `prSum_mul_twelve_eq_qexp`: divisor-sum
  `q`-expansions.
* `TateParameter.eisenstein_one_sq_eq_qexp`, `eisenstein_one_mul_three_eq_qexp`,
  `eisenstein_one_mul_rSum_eq_qexp`, `eisenstein_one_cube_eq_qexp`: Cauchy products with
  `σ`-convolution coefficients.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* A. Weil, *Elliptic Functions According to Eisenstein and Kronecker*.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

noncomputable section

namespace TateCurvesTheta

/-! ### Integer binomial-coefficient identities

The power weights `j², j³, j⁴` decompose `ℤ`-linearly (in fact `ℕ`-linearly) in the
binomial coefficients `C(j, 2), C(j, 3), C(j, 4)`; these identities drive the generating
functions below without ever dividing by `2`, `6`, `12` or `24`. -/

section ChooseIdentities

private lemma sq_eq_choose (j : ℕ) : j ^ 2 = 2 * j.choose 2 + j := by
  induction j with
  | zero => rfl
  | succ n ih =>
    have hrec : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ' n 1
    have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
    rw [hrec, Nat.choose_one_right, hexp, ih]
    ring

private lemma cube_eq_choose (j : ℕ) : j ^ 3 = 6 * j.choose 3 + 6 * j.choose 2 + j := by
  induction j with
  | zero => rfl
  | succ n ih =>
    have hrec3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := Nat.choose_succ_succ' n 2
    have hrec2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ' n 1
    have hexp : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
    rw [hrec3, hrec2, Nat.choose_one_right, hexp, ih, sq_eq_choose n]
    ring

private lemma fourth_eq_choose (j : ℕ) :
    j ^ 4 = 24 * j.choose 4 + 36 * j.choose 3 + 14 * j.choose 2 + j := by
  induction j with
  | zero => rfl
  | succ n ih =>
    have hrec4 : (n + 1).choose 4 = n.choose 3 + n.choose 4 := Nat.choose_succ_succ' n 3
    have hrec3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := Nat.choose_succ_succ' n 2
    have hrec2 : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ' n 1
    have hexp : (n + 1) ^ 4 = n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1 := by ring
    rw [hrec4, hrec3, hrec2, Nat.choose_one_right, hexp, ih, cube_eq_choose n, sq_eq_choose n]
    ring

private lemma cube_eq_six_choose_succ (e : ℕ) : e ^ 3 = 6 * (e + 1).choose 3 + e := by
  rw [Nat.choose_succ_succ' e 2, cube_eq_choose e]
  ring

private lemma fourth_eq_twelve_choose_pair (e : ℕ) :
    e ^ 4 = 12 * ((e + 2).choose 4 + (e + 1).choose 4) + e ^ 2 := by
  have h1 : (e + 2).choose 4 = (e + 1).choose 3 + (e + 1).choose 4 :=
    Nat.choose_succ_succ' (e + 1) 3
  have h2 : (e + 1).choose 4 = e.choose 3 + e.choose 4 := Nat.choose_succ_succ' e 3
  have h3 : (e + 1).choose 3 = e.choose 2 + e.choose 3 := Nat.choose_succ_succ' e 2
  rw [h1, h3, h2, fourth_eq_choose e, sq_eq_choose e]
  ring

end ChooseIdentities

/-! ### Power-weight generating functions of the Eisenstein kernels

On the open unit ball `‖x‖ < 1` of a complete normed field, the kernels
`p, r, φ, ψ` are the generating functions of the power weights `∑ⱼ jᵐ xʲ`
(`m = 1, 2, 3, 4`), and `p²`, `p·r` have binomial-coefficient expansions. -/

section GeneratingFunctions

variable {K : Type*} [NormedField K] {x : K}

private lemma one_sub_ne_zero_of_norm_lt_one (hx : ‖x‖ < 1) : (1 : K) - x ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hx
  exact lt_irrefl _ hx

/-- Removing an initial segment of vanishing terms from a `HasSum`. -/
private lemma hasSum_of_shift {f : ℕ → K} {S : K} {m : ℕ}
    (h : HasSum (fun n : ℕ => f (n + m)) S) (h0 : ∀ i < m, f i = 0) : HasSum f S := by
  have hz : ∑ i ∈ Finset.range m, f i = 0 :=
    Finset.sum_eq_zero fun i hi => h0 i (Finset.mem_range.mp hi)
  have h' : HasSum (fun n : ℕ => f (n + m)) (S - ∑ i ∈ Finset.range m, f i) := by
    rwa [hz, sub_zero]
  exact (hasSum_nat_add_iff' m).mp h'

/-- Shifting a power series with vanishing constant term by one step. -/
private lemma hasSum_succ_of_hasSum {c : ℕ → K} {y S : K}
    (h : HasSum (fun j : ℕ => c j * y ^ j) S) (h0 : c 0 = 0) :
    HasSum (fun j : ℕ => c (j + 1) * y ^ (j + 1)) S := by
  have h' := (hasSum_nat_add_iff' (f := fun j : ℕ => c j * y ^ j) 1).mpr h
  simpa [h0] using h'

/-- The binomial series `∑ₙ C(n+k, k)·x^{n+m} = xᵐ/(1-x)^{k+1}` for `‖x‖ < 1`. -/
private lemma hasSum_choose_shift (k m : ℕ) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => ((n + k).choose k : K) * x ^ (n + m)) (x ^ m / (1 - x) ^ (k + 1)) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one k hx).mul_left (x ^ m)
  have hfun : (fun n : ℕ => x ^ m * (((n + k).choose k : K) * x ^ n))
      = fun n : ℕ => ((n + k).choose k : K) * x ^ (n + m) := by
    funext n
    rw [pow_add]
    ring
  rw [hfun] at h
  rwa [mul_one_div] at h

private lemma hasSum_choose_two (hx : ‖x‖ < 1) :
    HasSum (fun j : ℕ => (j.choose 2 : K) * x ^ j) (x ^ 2 / (1 - x) ^ 3) := by
  refine hasSum_of_shift (m := 2) (hasSum_choose_shift 2 2 hx) fun i hi => ?_
  rw [Nat.choose_eq_zero_of_lt hi, Nat.cast_zero, zero_mul]

private lemma hasSum_choose_three (hx : ‖x‖ < 1) :
    HasSum (fun j : ℕ => (j.choose 3 : K) * x ^ j) (x ^ 3 / (1 - x) ^ 4) := by
  refine hasSum_of_shift (m := 3) (hasSum_choose_shift 3 3 hx) fun i hi => ?_
  rw [Nat.choose_eq_zero_of_lt hi, Nat.cast_zero, zero_mul]

private lemma hasSum_choose_four (hx : ‖x‖ < 1) :
    HasSum (fun j : ℕ => (j.choose 4 : K) * x ^ j) (x ^ 4 / (1 - x) ^ 5) := by
  refine hasSum_of_shift (m := 4) (hasSum_choose_shift 4 4 hx) fun i hi => ?_
  rw [Nat.choose_eq_zero_of_lt hi, Nat.cast_zero, zero_mul]

/-- The shifted geometric series `∑ⱼ x^{j+1} = x/(1-x)` for `‖x‖ < 1`. -/
lemma hasSum_geometric_succ (hx : ‖x‖ < 1) :
    HasSum (fun j : ℕ => x ^ (j + 1)) (x / (1 - x)) := by
  have h := (hasSum_geometric_of_norm_lt_one hx).mul_left x
  rw [div_eq_mul_inv]
  simpa only [← pow_succ'] using h

/-- **`p` generates the weight-one powers**: `∑ⱼ j·xʲ = p(x)` for `‖x‖ < 1`. -/
lemma hasSum_pow_mul_geometric_eisP (hx : ‖x‖ < 1) :
    HasSum (fun j : ℕ => (j : K) * x ^ j) (eisP x) := by
  rw [eisP]
  exact hasSum_coe_mul_geometric_of_norm_lt_one hx

/-- **`r` generates the squares**: `∑ⱼ j²·xʲ = r(x)` for `‖x‖ < 1`. -/
lemma hasSum_sq_mul_geometric_eisR (hx : ‖x‖ < 1) :
    HasSum (fun j : ℕ => (j : K) ^ 2 * x ^ j) (eisR x) := by
  have hx1 : (1 : K) - x ≠ 0 := one_sub_ne_zero_of_norm_lt_one hx
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hx
  have h2 := hasSum_choose_two hx
  have h := (h2.mul_left 2).add h1
  have hfun : (fun j : ℕ => 2 * ((j.choose 2 : K) * x ^ j) + (j : K) * x ^ j)
      = fun j : ℕ => (j : K) ^ 2 * x ^ j := by
    funext j
    have hj : (j : K) ^ 2 = 2 * (j.choose 2 : K) + (j : K) := by
      exact_mod_cast congrArg (Nat.cast (R := K)) (sq_eq_choose j)
    rw [hj]
    ring
  rw [hfun] at h
  have hval : 2 * (x ^ 2 / (1 - x) ^ 3) + x / (1 - x) ^ 2 = eisR x := by
    rw [eisR]
    field_simp
    ring
  rwa [hval] at h

/-- **`φ` generates the cubes**: `∑ⱼ j³·xʲ = φ(x)` for `‖x‖ < 1`. -/
lemma hasSum_cube_mul_geometric_eisPhi (hx : ‖x‖ < 1) :
    HasSum (fun j : ℕ => (j : K) ^ 3 * x ^ j) (eisPhi x) := by
  have hx1 : (1 : K) - x ≠ 0 := one_sub_ne_zero_of_norm_lt_one hx
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hx
  have h2 := hasSum_choose_two hx
  have h3 := hasSum_choose_three hx
  have h := ((h3.mul_left 6).add (h2.mul_left 6)).add h1
  have hfun : (fun j : ℕ =>
        6 * ((j.choose 3 : K) * x ^ j) + 6 * ((j.choose 2 : K) * x ^ j) + (j : K) * x ^ j)
      = fun j : ℕ => (j : K) ^ 3 * x ^ j := by
    funext j
    have hj : (j : K) ^ 3 = 6 * (j.choose 3 : K) + 6 * (j.choose 2 : K) + (j : K) := by
      exact_mod_cast congrArg (Nat.cast (R := K)) (cube_eq_choose j)
    rw [hj]
    ring
  rw [hfun] at h
  have hval : 6 * (x ^ 3 / (1 - x) ^ 4) + 6 * (x ^ 2 / (1 - x) ^ 3) + x / (1 - x) ^ 2
      = eisPhi x := by
    rw [eisPhi]
    field_simp
    ring
  rwa [hval] at h

/-- **`ψ` generates the fourth powers**: `∑ⱼ j⁴·xʲ = ψ(x)` for `‖x‖ < 1`. -/
lemma hasSum_fourth_mul_geometric_eisPsi (hx : ‖x‖ < 1) :
    HasSum (fun j : ℕ => (j : K) ^ 4 * x ^ j) (eisPsi x) := by
  have hx1 : (1 : K) - x ≠ 0 := one_sub_ne_zero_of_norm_lt_one hx
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hx
  have h2 := hasSum_choose_two hx
  have h3 := hasSum_choose_three hx
  have h4 := hasSum_choose_four hx
  have h := (((h4.mul_left 24).add (h3.mul_left 36)).add (h2.mul_left 14)).add h1
  have hfun : (fun j : ℕ =>
        24 * ((j.choose 4 : K) * x ^ j) + 36 * ((j.choose 3 : K) * x ^ j)
          + 14 * ((j.choose 2 : K) * x ^ j) + (j : K) * x ^ j)
      = fun j : ℕ => (j : K) ^ 4 * x ^ j := by
    funext j
    have hj : (j : K) ^ 4
        = 24 * (j.choose 4 : K) + 36 * (j.choose 3 : K) + 14 * (j.choose 2 : K) + (j : K) := by
      exact_mod_cast congrArg (Nat.cast (R := K)) (fourth_eq_choose j)
    rw [hj]
    ring
  rw [hfun] at h
  have hval : 24 * (x ^ 4 / (1 - x) ^ 5) + 36 * (x ^ 3 / (1 - x) ^ 4)
      + 14 * (x ^ 2 / (1 - x) ^ 3) + x / (1 - x) ^ 2 = eisPsi x := by
    rw [eisPsi]
    field_simp
    ring
  rwa [hval] at h

/-- **Binomial expansion of `p²`**: `∑ⱼ C(j+1,3)·xʲ = p(x)²` for `‖x‖ < 1`. -/
lemma hasSum_choose_eisP_sq (hx : ‖x‖ < 1) :
    HasSum (fun j : ℕ => ((j + 1).choose 3 : K) * x ^ j) (eisP x ^ 2) := by
  have hval : eisP x ^ 2 = x ^ 2 / (1 - x) ^ 4 := by
    rw [eisP, div_pow, ← pow_mul]
  have h := hasSum_choose_shift 3 2 hx
  have hfun : (fun n : ℕ => ((n + 3).choose 3 : K) * x ^ (n + 2))
      = fun n : ℕ => ((n + 2 + 1).choose 3 : K) * x ^ (n + 2) := by
    funext n
    norm_num
  rw [hfun] at h
  rw [hval]
  refine hasSum_of_shift (m := 2) h fun i hi => ?_
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

/-- **Binomial expansion of `p·r`**: `∑ⱼ (C(j+2,4) + C(j+1,4))·xʲ = p(x)·r(x)` for
`‖x‖ < 1`. -/
lemma hasSum_choose_eisP_mul_eisR (hx : ‖x‖ < 1) :
    HasSum (fun j : ℕ => (((j + 2).choose 4 + (j + 1).choose 4 : ℕ) : K) * x ^ j)
      (eisP x * eisR x) := by
  have hx1 : (1 : K) - x ≠ 0 := one_sub_ne_zero_of_norm_lt_one hx
  have hA : HasSum (fun j : ℕ => ((j + 2).choose 4 : K) * x ^ j) (x ^ 2 / (1 - x) ^ 5) := by
    have h := hasSum_choose_shift 4 2 hx
    have hfun : (fun n : ℕ => ((n + 4).choose 4 : K) * x ^ (n + 2))
        = fun n : ℕ => ((n + 2 + 2).choose 4 : K) * x ^ (n + 2) := by
      funext n
      norm_num
    rw [hfun] at h
    refine hasSum_of_shift (m := 2) h fun i hi => ?_
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  have hB : HasSum (fun j : ℕ => ((j + 1).choose 4 : K) * x ^ j) (x ^ 3 / (1 - x) ^ 5) := by
    have h := hasSum_choose_shift 4 3 hx
    have hfun : (fun n : ℕ => ((n + 4).choose 4 : K) * x ^ (n + 3))
        = fun n : ℕ => ((n + 3 + 1).choose 4 : K) * x ^ (n + 3) := by
      funext n
      norm_num
    rw [hfun] at h
    refine hasSum_of_shift (m := 3) h fun i hi => ?_
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  have h := hA.add hB
  have hfun : (fun j : ℕ => ((j + 2).choose 4 : K) * x ^ j + ((j + 1).choose 4 : K) * x ^ j)
      = fun j : ℕ => (((j + 2).choose 4 + (j + 1).choose 4 : ℕ) : K) * x ^ j := by
    funext j
    push_cast
    ring
  rw [hfun] at h
  have hval : x ^ 2 / (1 - x) ^ 5 + x ^ 3 / (1 - x) ^ 5 = eisP x * eisR x := by
    rw [eisP, eisR]
    field_simp
  rwa [hval] at h

end GeneratingFunctions

/-! ### Ultrametric norm bounds for the kernels and divisor sums -/

section UltrametricBounds

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {x : K}

private lemma norm_one_sub_eq_one (hx : ‖x‖ < 1) : ‖(1 : K) - x‖ = 1 := by
  have hne : ‖(1 : K)‖ ≠ ‖-x‖ := by
    rw [norm_one, norm_neg]
    exact (ne_of_lt hx).symm
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_one,
    max_eq_left hx.le]

private lemma norm_one_add_le_one {y : K} (hy : ‖y‖ ≤ 1) : ‖(1 : K) + y‖ ≤ 1 :=
  le_trans (IsUltrametricDist.norm_add_le_max 1 y) (max_le norm_one.le hy)

private lemma norm_eisP_le (hx : ‖x‖ < 1) : ‖eisP x‖ ≤ ‖x‖ := by
  rw [eisP, norm_div, norm_pow, norm_one_sub_eq_one hx, one_pow, div_one]

private lemma norm_eisR_le (hx : ‖x‖ < 1) : ‖eisR x‖ ≤ ‖x‖ := by
  rw [eisR, norm_div, norm_pow, norm_one_sub_eq_one hx, one_pow, div_one, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_one_add_le_one hx.le)

private lemma norm_eisPhi_le (hx : ‖x‖ < 1) : ‖eisPhi x‖ ≤ ‖x‖ := by
  rw [eisPhi, norm_div, norm_pow, norm_one_sub_eq_one hx, one_pow, div_one, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  have h4x : ‖(4 : K) * x‖ ≤ 1 := by
    rw [norm_mul]
    have h4 : ‖(4 : K)‖ ≤ 1 := by
      simpa using IsUltrametricDist.norm_natCast_le_one K 4
    simpa using mul_le_mul h4 hx.le (norm_nonneg _) zero_le_one
  have hx2 : ‖x ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hx.le
  have s1 : ‖(1 : K) + 4 * x‖ ≤ 1 :=
    le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le norm_one.le h4x)
  exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le s1 hx2)

private lemma norm_eisPsi_le (hx : ‖x‖ < 1) : ‖eisPsi x‖ ≤ ‖x‖ := by
  rw [eisPsi, norm_div, norm_pow, norm_one_sub_eq_one hx, one_pow, div_one, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  have h11 : ‖(11 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 11
  have h1x : ‖(11 : K) * x‖ ≤ 1 := by
    rw [norm_mul]
    simpa using mul_le_mul h11 hx.le (norm_nonneg _) zero_le_one
  have hx2 : ‖x ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hx.le
  have h2x : ‖(11 : K) * x ^ 2‖ ≤ 1 := by
    rw [norm_mul]
    simpa using mul_le_mul h11 hx2 (norm_nonneg _) zero_le_one
  have hx3 : ‖x ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hx.le
  have s1 : ‖(1 : K) + 11 * x‖ ≤ 1 :=
    le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le norm_one.le h1x)
  have s2 : ‖(1 : K) + 11 * x + 11 * x ^ 2‖ ≤ 1 :=
    le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le s1 h2x)
  exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le s2 hx3)

private lemma norm_sigma1_le_one (M : ℕ) : ‖∑ d ∈ M.divisors, (d : K)‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun d _ =>
    IsUltrametricDist.norm_natCast_le_one K d

private lemma norm_sigma3_le_one (M : ℕ) : ‖∑ d ∈ M.divisors, (d : K) ^ 3‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun d _ => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K d)

private lemma norm_natCast_mul_sigma1_le_one (M : ℕ) :
    ‖(M : K) * ∑ d ∈ M.divisors, (d : K)‖ ≤ 1 := by
  rw [norm_mul]
  simpa using mul_le_mul (IsUltrametricDist.norm_natCast_le_one K M) (norm_sigma1_le_one M)
    (norm_nonneg _) zero_le_one

private lemma norm_sigma1_conv_le_one (m : ℕ) :
    ‖∑ r ∈ Finset.Ico 1 m, (∑ d ∈ r.divisors, (d : K)) * ∑ d ∈ (m - r).divisors, (d : K)‖
      ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun r _ => by
    rw [norm_mul]
    simpa using mul_le_mul (norm_sigma1_le_one r) (norm_sigma1_le_one (m - r)) (norm_nonneg _)
      zero_le_one

end UltrametricBounds

namespace TateParameter

/-! ### The six kernel series -/

section Defs

variable {K : Type*} [NormedField K] (t : TateParameter K)

/-- `𝔭 = ∑_{k ≥ 1} p(qᵏ)`: the constant series of `X`-kernels over the positive powers of
the Tate parameter. -/
def pSum : K := ∑' k : ℕ, eisP ((t.q : K) ^ (k + 1))

/-- `𝔯 = ∑_{k ≥ 1} k·r(qᵏ)`: the weight-one-weighted series of `r`-kernels. -/
def rSum : K := ∑' k : ℕ, ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1))

/-- `𝛗 = ∑_{k ≥ 1} φ(qᵏ)`: the constant series of `φ`-kernels. -/
def phiSum : K := ∑' k : ℕ, eisPhi ((t.q : K) ^ (k + 1))

/-- `𝛙 = ∑_{k ≥ 1} k·ψ(qᵏ)`: the weight-one-weighted series of `ψ`-kernels. -/
def psiSum : K := ∑' k : ℕ, ((k + 1 : ℕ) : K) * eisPsi ((t.q : K) ^ (k + 1))

/-- `𝔭₂ = ∑_{k ≥ 1} p(qᵏ)²`: the series of squared `X`-kernels. -/
def pSqSum : K := ∑' k : ℕ, eisP ((t.q : K) ^ (k + 1)) ^ 2

/-- `𝔭𝔯 = ∑_{k ≥ 1} k·p(qᵏ)r(qᵏ)`: the weight-one-weighted series of `p·r`-products. -/
def prSum : K :=
  ∑' k : ℕ, ((k + 1 : ℕ) : K) * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1)))

private lemma norm_qpow_lt_one (k : ℕ) : ‖(t.q : K) ^ (k + 1)‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) t.norm_lt_one k.succ_ne_zero

end Defs

section Series

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-! ### Summability of the defining families -/

omit [IsUltrametricDist K] in
/-- Domination by the geometric series `∑ ‖q‖^{k+1}` gives summability. -/
private lemma summable_of_norm_le_geometric {f : ℕ → K}
    (hf : ∀ k : ℕ, ‖f k‖ ≤ ‖(t.q : K)‖ ^ (k + 1)) : Summable f := by
  have hg : Summable fun k : ℕ => ‖(t.q : K)‖ ^ (k + 1) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one).mul_right ‖(t.q : K)‖
  exact hg.of_norm_bounded hf

/-- The family defining `pSum` is summable. -/
lemma summable_pSum_terms : Summable fun k : ℕ => eisP ((t.q : K) ^ (k + 1)) := by
  refine t.summable_of_norm_le_geometric fun k => ?_
  calc ‖eisP ((t.q : K) ^ (k + 1))‖
      ≤ ‖(t.q : K) ^ (k + 1)‖ := norm_eisP_le (t.norm_qpow_lt_one k)
    _ = ‖(t.q : K)‖ ^ (k + 1) := norm_pow _ _

/-- The family defining `rSum` is summable. -/
lemma summable_rSum_terms :
    Summable fun k : ℕ => ((k + 1 : ℕ) : K) * eisR ((t.q : K) ^ (k + 1)) := by
  refine t.summable_of_norm_le_geometric fun k => ?_
  rw [norm_mul]
  calc ‖((k + 1 : ℕ) : K)‖ * ‖eisR ((t.q : K) ^ (k + 1))‖
      ≤ 1 * ‖(t.q : K) ^ (k + 1)‖ := by
        gcongr
        · exact IsUltrametricDist.norm_natCast_le_one K _
        · exact norm_eisR_le (t.norm_qpow_lt_one k)
    _ = ‖(t.q : K)‖ ^ (k + 1) := by rw [one_mul, norm_pow]

/-- The family defining `phiSum` is summable. -/
lemma summable_phiSum_terms : Summable fun k : ℕ => eisPhi ((t.q : K) ^ (k + 1)) := by
  refine t.summable_of_norm_le_geometric fun k => ?_
  calc ‖eisPhi ((t.q : K) ^ (k + 1))‖
      ≤ ‖(t.q : K) ^ (k + 1)‖ := norm_eisPhi_le (t.norm_qpow_lt_one k)
    _ = ‖(t.q : K)‖ ^ (k + 1) := norm_pow _ _

/-- The family defining `psiSum` is summable. -/
lemma summable_psiSum_terms :
    Summable fun k : ℕ => ((k + 1 : ℕ) : K) * eisPsi ((t.q : K) ^ (k + 1)) := by
  refine t.summable_of_norm_le_geometric fun k => ?_
  rw [norm_mul]
  calc ‖((k + 1 : ℕ) : K)‖ * ‖eisPsi ((t.q : K) ^ (k + 1))‖
      ≤ 1 * ‖(t.q : K) ^ (k + 1)‖ := by
        gcongr
        · exact IsUltrametricDist.norm_natCast_le_one K _
        · exact norm_eisPsi_le (t.norm_qpow_lt_one k)
    _ = ‖(t.q : K)‖ ^ (k + 1) := by rw [one_mul, norm_pow]

/-- The family defining `pSqSum` is summable. -/
lemma summable_pSqSum_terms : Summable fun k : ℕ => eisP ((t.q : K) ^ (k + 1)) ^ 2 := by
  refine t.summable_of_norm_le_geometric fun k => ?_
  rw [norm_pow]
  calc ‖eisP ((t.q : K) ^ (k + 1))‖ ^ 2
      ≤ ‖(t.q : K) ^ (k + 1)‖ ^ 2 := by
        gcongr
        exact norm_eisP_le (t.norm_qpow_lt_one k)
    _ ≤ ‖(t.q : K)‖ ^ (k + 1) := by
        rw [norm_pow, ← pow_mul]
        exact pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le (by omega)

/-- The family defining `prSum` is summable. -/
lemma summable_prSum_terms :
    Summable fun k : ℕ =>
      ((k + 1 : ℕ) : K) * (eisP ((t.q : K) ^ (k + 1)) * eisR ((t.q : K) ^ (k + 1))) := by
  refine t.summable_of_norm_le_geometric fun k => ?_
  have hx := t.norm_qpow_lt_one k
  rw [norm_mul, norm_mul]
  calc ‖((k + 1 : ℕ) : K)‖ * (‖eisP ((t.q : K) ^ (k + 1))‖ * ‖eisR ((t.q : K) ^ (k + 1))‖)
      ≤ 1 * (‖(t.q : K) ^ (k + 1)‖ * ‖(t.q : K) ^ (k + 1)‖) := by
        gcongr
        · exact IsUltrametricDist.norm_natCast_le_one K _
        · exact norm_eisP_le hx
        · exact norm_eisR_le hx
    _ = (‖(t.q : K)‖ ^ (k + 1)) ^ 2 := by rw [one_mul, norm_pow, sq]
    _ ≤ ‖(t.q : K)‖ ^ (k + 1) := by
        rw [← pow_mul]
        exact pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le (by omega)

/-! ### The divisor-fiber Fubini -/

/-- The `ℕ+ × ℕ+`-indexed weighted family `(m, j) ↦ f(m)·g(j)·q^{mj}` underlying the
divisor-fiber regrouping. -/
private def qpowFamily (f g : ℕ → ℕ) : ℕ+ × ℕ+ → K := fun r =>
  (f (r.1 : ℕ) : K) * (g (r.2 : ℕ) : K) * (t.q : K) ^ ((r.1 : ℕ) * (r.2 : ℕ))

/-- **The divisor-fiber Fubini for weighted `q`-power double series.** For natural weights
`f`, `g`, the double series `∑ₖ f(k)·(∑ⱼ g(j)·(qᵏ)ʲ)` (all indices `≥ 1`) regroups along
the multiplication fibration `(k, j) ↦ k·j` into a `q`-expansion whose `N`-th coefficient
is the divisor convolution `∑_{d·e = N} f(d)·g(e)`. -/
lemma tsum_weighted_qpow_eq (f g : ℕ → ℕ) :
    (∑' k : ℕ, (f (k + 1) : K) * ∑' j : ℕ, (g (j + 1) : K) * ((t.q : K) ^ (k + 1)) ^ (j + 1))
      = ∑' N : ℕ, (∑ p ∈ (N + 1).divisorsAntidiagonal, ((f p.1 * g p.2 : ℕ) : K))
          * (t.q : K) ^ (N + 1) := by
  have hq0 : (0 : ℝ) ≤ ‖(t.q : K)‖ := norm_nonneg _
  have hgeom : Summable fun n : ℕ => ‖(t.q : K)‖ ^ n :=
    summable_geometric_of_lt_one hq0 t.norm_lt_one
  have hdom : Summable fun p : ℕ × ℕ => ‖(t.q : K)‖ ^ p.1 * ‖(t.q : K)‖ ^ p.2 :=
    hgeom.mul_of_nonneg hgeom (fun _ => by positivity) fun _ => by positivity
  -- summability of the joint family in shifted `ℕ × ℕ` coordinates
  have hG : Summable fun p : ℕ × ℕ =>
      (f (p.1 + 1) : K) * (g (p.2 + 1) : K) * (t.q : K) ^ ((p.1 + 1) * (p.2 + 1)) := by
    refine hdom.of_norm_bounded fun p => ?_
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖(f (p.1 + 1) : K)‖ * ‖(g (p.2 + 1) : K)‖ * ‖(t.q : K)‖ ^ ((p.1 + 1) * (p.2 + 1))
        ≤ 1 * 1 * ‖(t.q : K)‖ ^ ((p.1 + 1) * (p.2 + 1)) := by
          gcongr
          · exact IsUltrametricDist.norm_natCast_le_one K _
          · exact IsUltrametricDist.norm_natCast_le_one K _
      _ = ‖(t.q : K)‖ ^ ((p.1 + 1) * (p.2 + 1)) := by ring
      _ ≤ ‖(t.q : K)‖ ^ (p.1 + p.2) :=
          pow_le_pow_of_le_one hq0 t.norm_lt_one.le (by nlinarith)
      _ = ‖(t.q : K)‖ ^ p.1 * ‖(t.q : K)‖ ^ p.2 := pow_add _ _ _
  -- summability of the `ℕ+ × ℕ+` family
  have hFF : Summable (t.qpowFamily f g) := by
    rw [← (Equiv.prodCongr Equiv.pnatEquivNat.symm Equiv.pnatEquivNat.symm).summable_iff]
    exact hG.congr fun p => rfl
  -- collapse the inner geometric index: the double series is the joint `ℕ × ℕ` sum
  have hfibk : ∀ k : ℕ,
      HasSum (fun j : ℕ => (f (k + 1) : K) * (g (j + 1) : K)
          * (t.q : K) ^ ((k + 1) * (j + 1)))
        ((f (k + 1) : K) * ∑' j : ℕ, (g (j + 1) : K) * ((t.q : K) ^ (k + 1)) ^ (j + 1)) := by
    intro k
    have hj : Summable fun j : ℕ => (g (j + 1) : K) * ((t.q : K) ^ (k + 1)) ^ (j + 1) := by
      have hgeo2 : Summable fun j : ℕ => ‖(t.q : K) ^ (k + 1)‖ ^ (j + 1) := by
        simpa only [pow_succ] using
          (summable_geometric_of_lt_one (norm_nonneg _) (t.norm_qpow_lt_one k)).mul_right _
      refine hgeo2.of_norm_bounded fun j => ?_
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (by positivity) (IsUltrametricDist.norm_natCast_le_one K _)
    have h1 := hj.hasSum.mul_left (f (k + 1) : K)
    have hfun : (fun j : ℕ =>
          (f (k + 1) : K) * ((g (j + 1) : K) * ((t.q : K) ^ (k + 1)) ^ (j + 1)))
        = fun j : ℕ => (f (k + 1) : K) * (g (j + 1) : K) * (t.q : K) ^ ((k + 1) * (j + 1)) := by
      funext j
      rw [pow_mul]
      ring
    rwa [hfun] at h1
  have hL := hG.hasSum.prod_fiberwise hfibk
  -- regroup along the divisor fibration
  have hsig := sigmaAntidiagonalEquivProd.summable_iff.mpr hFF
  have hfibn : ∀ n : ℕ+,
      HasSum (fun x : ((n : ℕ)).divisorsAntidiagonal =>
          t.qpowFamily f g (sigmaAntidiagonalEquivProd ⟨n, x⟩))
        ((∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, ((f p.1 * g p.2 : ℕ) : K))
          * (t.q : K) ^ (n : ℕ)) := by
    intro n
    have hterm : ∀ x : ((n : ℕ)).divisorsAntidiagonal,
        t.qpowFamily f g (sigmaAntidiagonalEquivProd ⟨n, x⟩)
          = (f (x : ℕ × ℕ).1 : K) * (g (x : ℕ × ℕ).2 : K) * (t.q : K) ^ (n : ℕ) := by
      intro x
      obtain ⟨hprod, -⟩ := Nat.mem_divisorsAntidiagonal.mp x.2
      simp only [qpowFamily, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors,
        Equiv.coe_fn_mk, PNat.mk_coe]
      rw [hprod]
    have h0 := hasSum_fintype fun x : ((n : ℕ)).divisorsAntidiagonal =>
      t.qpowFamily f g (sigmaAntidiagonalEquivProd ⟨n, x⟩)
    convert h0 using 1
    calc (∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, ((f p.1 * g p.2 : ℕ) : K))
          * (t.q : K) ^ (n : ℕ)
        = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal,
            (f p.1 : K) * (g p.2 : K) * (t.q : K) ^ (n : ℕ) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          push_cast
          ring
      _ = ∑ x ∈ ((n : ℕ)).divisorsAntidiagonal.attach,
            (f (x : ℕ × ℕ).1 : K) * (g (x : ℕ × ℕ).2 : K) * (t.q : K) ^ (n : ℕ) :=
          (Finset.sum_attach _ _).symm
      _ = ∑ x : ((n : ℕ)).divisorsAntidiagonal,
            t.qpowFamily f g (sigmaAntidiagonalEquivProd ⟨n, x⟩) := by
          rw [Finset.univ_eq_attach]
          exact Finset.sum_congr rfl fun x _ => (hterm x).symm
  have hRsum := hsig.hasSum.sigma hfibn
  -- assemble
  calc (∑' k : ℕ, (f (k + 1) : K)
          * ∑' j : ℕ, (g (j + 1) : K) * ((t.q : K) ^ (k + 1)) ^ (j + 1))
      = ∑' p : ℕ × ℕ,
          (f (p.1 + 1) : K) * (g (p.2 + 1) : K) * (t.q : K) ^ ((p.1 + 1) * (p.2 + 1)) :=
        hL.tsum_eq
    _ = ∑' r : ℕ+ × ℕ+, t.qpowFamily f g r := by
        rw [← (Equiv.prodCongr Equiv.pnatEquivNat.symm Equiv.pnatEquivNat.symm).tsum_eq
          (t.qpowFamily f g)]
        exact tsum_congr fun p => rfl
    _ = ∑' n : ℕ+, (∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, ((f p.1 * g p.2 : ℕ) : K))
          * (t.q : K) ^ (n : ℕ) := by
        rw [← sigmaAntidiagonalEquivProd.tsum_eq (t.qpowFamily f g)]
        exact hRsum.tsum_eq.symm
    _ = ∑' N : ℕ, (∑ p ∈ (N + 1).divisorsAntidiagonal, ((f p.1 * g p.2 : ℕ) : K))
          * (t.q : K) ^ (N + 1) :=
        tsum_pnat_eq_tsum_succ (f := fun M : ℕ =>
          (∑ p ∈ M.divisorsAntidiagonal, ((f p.1 * g p.2 : ℕ) : K)) * (t.q : K) ^ M)

/-! ### `q`-expansions with divisor-sum coefficients -/

/-- **`q`-expansion of the Eisenstein series** `sₖ(q)`:
`sₖ(q) = ∑_{N ≥ 1} σₖ(N)·q^N` with `σₖ(N) = ∑_{d ∣ N} dᵏ`. -/
lemma eisenstein_eq_qexp (k : ℕ) :
    t.eisenstein k
      = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, (d : K) ^ k) * (t.q : K) ^ (N + 1) := by
  have h := t.tsum_weighted_qpow_eq (fun m => m ^ k) fun _ => 1
  calc t.eisenstein k
      = ∑' n : ℕ, (((n + 1) ^ k : ℕ) : K)
          * ∑' j : ℕ, ((1 : ℕ) : K) * ((t.q : K) ^ (n + 1)) ^ (j + 1) := by
        rw [eisenstein]
        refine tsum_congr fun n => ?_
        have hgeo := hasSum_geometric_succ (t.norm_qpow_lt_one n)
        have hinner : (∑' j : ℕ, ((1 : ℕ) : K) * ((t.q : K) ^ (n + 1)) ^ (j + 1))
            = (t.q : K) ^ (n + 1) / (1 - (t.q : K) ^ (n + 1)) := by
          rw [← hgeo.tsum_eq]
          refine tsum_congr fun j => ?_
          rw [Nat.cast_one, one_mul]
        rw [hinner, mul_div_assoc, Nat.cast_pow]
    _ = ∑' N : ℕ, (∑ p ∈ (N + 1).divisorsAntidiagonal, ((p.1 ^ k * 1 : ℕ) : K))
          * (t.q : K) ^ (N + 1) := h
    _ = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, (d : K) ^ k) * (t.q : K) ^ (N + 1) := by
        refine tsum_congr fun N => ?_
        congr 1
        calc ∑ p ∈ (N + 1).divisorsAntidiagonal, ((p.1 ^ k * 1 : ℕ) : K)
            = ∑ i ∈ (N + 1).divisors, ((i ^ k * 1 : ℕ) : K) :=
              Nat.sum_divisorsAntidiagonal (f := fun d _ => ((d ^ k * 1 : ℕ) : K))
          _ = ∑ d ∈ (N + 1).divisors, (d : K) ^ k := by
              refine Finset.sum_congr rfl fun i _ => ?_
              push_cast
              ring

/-- **`q`-expansion of `pSum`**: `𝔭 = ∑_{N ≥ 1} σ₁(N)·q^N`. -/
lemma pSum_eq_qexp :
    t.pSum = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, (d : K)) * (t.q : K) ^ (N + 1) := by
  have h := t.tsum_weighted_qpow_eq (fun _ => 1) fun m => m
  calc t.pSum
      = ∑' k : ℕ, ((1 : ℕ) : K)
          * ∑' j : ℕ, ((j + 1 : ℕ) : K) * ((t.q : K) ^ (k + 1)) ^ (j + 1) := by
        rw [pSum]
        refine tsum_congr fun k => ?_
        rw [Nat.cast_one, one_mul]
        exact (hasSum_succ_of_hasSum
          (hasSum_pow_mul_geometric_eisP (t.norm_qpow_lt_one k)) (by simp)).tsum_eq.symm
    _ = ∑' N : ℕ, (∑ p ∈ (N + 1).divisorsAntidiagonal, ((1 * p.2 : ℕ) : K))
          * (t.q : K) ^ (N + 1) := h
    _ = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, (d : K)) * (t.q : K) ^ (N + 1) := by
        refine tsum_congr fun N => ?_
        congr 1
        calc ∑ p ∈ (N + 1).divisorsAntidiagonal, ((1 * p.2 : ℕ) : K)
            = ∑ i ∈ (N + 1).divisors, ((1 * i : ℕ) : K) :=
              Nat.sum_divisorsAntidiagonal' (f := fun _ e => ((1 * e : ℕ) : K))
          _ = ∑ d ∈ (N + 1).divisors, (d : K) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [one_mul]

/-- **`q`-expansion of `rSum`**: `𝔯 = ∑_{N ≥ 1} N·σ₁(N)·q^N`. -/
lemma rSum_eq_qexp :
    t.rSum = ∑' N : ℕ, ((N + 1 : ℕ) : K) * (∑ d ∈ (N + 1).divisors, (d : K))
      * (t.q : K) ^ (N + 1) := by
  have h := t.tsum_weighted_qpow_eq (fun m => m) fun m => m ^ 2
  calc t.rSum
      = ∑' k : ℕ, ((k + 1 : ℕ) : K)
          * ∑' j : ℕ, (((j + 1) ^ 2 : ℕ) : K) * ((t.q : K) ^ (k + 1)) ^ (j + 1) := by
        rw [rSum]
        refine tsum_congr fun k => ?_
        congr 1
        refine ((hasSum_succ_of_hasSum
          (hasSum_sq_mul_geometric_eisR (t.norm_qpow_lt_one k))
            (by simp)).tsum_eq.symm).trans ?_
        refine tsum_congr fun j => ?_
        push_cast
        ring
    _ = ∑' N : ℕ, (∑ p ∈ (N + 1).divisorsAntidiagonal, ((p.1 * p.2 ^ 2 : ℕ) : K))
          * (t.q : K) ^ (N + 1) := h
    _ = ∑' N : ℕ, ((N + 1 : ℕ) : K) * (∑ d ∈ (N + 1).divisors, (d : K))
          * (t.q : K) ^ (N + 1) := by
        refine tsum_congr fun N => ?_
        congr 1
        calc ∑ p ∈ (N + 1).divisorsAntidiagonal, ((p.1 * p.2 ^ 2 : ℕ) : K)
            = ∑ i ∈ (N + 1).divisors, (((N + 1) / i * i ^ 2 : ℕ) : K) :=
              Nat.sum_divisorsAntidiagonal' (f := fun d e => ((d * e ^ 2 : ℕ) : K))
          _ = ((N + 1 : ℕ) : K) * ∑ d ∈ (N + 1).divisors, (d : K) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i hi => ?_
              have hdvd : i ∣ N + 1 := Nat.dvd_of_mem_divisors hi
              have hkey : (N + 1) / i * i ^ 2 = (N + 1) * i := by
                have h2 : i ^ 2 = i * i := by ring
                rw [h2, ← mul_assoc, Nat.div_mul_cancel hdvd]
              rw [hkey]
              push_cast
              ring

/-- **`q`-expansion of `phiSum`**: `𝛗 = ∑_{N ≥ 1} σ₃(N)·q^N`. -/
lemma phiSum_eq_qexp :
    t.phiSum = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, (d : K) ^ 3) * (t.q : K) ^ (N + 1) := by
  have h := t.tsum_weighted_qpow_eq (fun _ => 1) fun m => m ^ 3
  calc t.phiSum
      = ∑' k : ℕ, ((1 : ℕ) : K)
          * ∑' j : ℕ, (((j + 1) ^ 3 : ℕ) : K) * ((t.q : K) ^ (k + 1)) ^ (j + 1) := by
        rw [phiSum]
        refine tsum_congr fun k => ?_
        rw [Nat.cast_one, one_mul]
        refine ((hasSum_succ_of_hasSum
          (hasSum_cube_mul_geometric_eisPhi (t.norm_qpow_lt_one k))
            (by simp)).tsum_eq.symm).trans ?_
        refine tsum_congr fun j => ?_
        push_cast
        ring
    _ = ∑' N : ℕ, (∑ p ∈ (N + 1).divisorsAntidiagonal, ((1 * p.2 ^ 3 : ℕ) : K))
          * (t.q : K) ^ (N + 1) := h
    _ = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, (d : K) ^ 3) * (t.q : K) ^ (N + 1) := by
        refine tsum_congr fun N => ?_
        congr 1
        calc ∑ p ∈ (N + 1).divisorsAntidiagonal, ((1 * p.2 ^ 3 : ℕ) : K)
            = ∑ i ∈ (N + 1).divisors, ((1 * i ^ 3 : ℕ) : K) :=
              Nat.sum_divisorsAntidiagonal' (f := fun _ e => ((1 * e ^ 3 : ℕ) : K))
          _ = ∑ d ∈ (N + 1).divisors, (d : K) ^ 3 := by
              refine Finset.sum_congr rfl fun i _ => ?_
              push_cast
              ring

/-- **`q`-expansion of `psiSum`**: `𝛙 = ∑_{N ≥ 1} N·σ₃(N)·q^N`. -/
lemma psiSum_eq_qexp :
    t.psiSum = ∑' N : ℕ, ((N + 1 : ℕ) : K) * (∑ d ∈ (N + 1).divisors, (d : K) ^ 3)
      * (t.q : K) ^ (N + 1) := by
  have h := t.tsum_weighted_qpow_eq (fun m => m) fun m => m ^ 4
  calc t.psiSum
      = ∑' k : ℕ, ((k + 1 : ℕ) : K)
          * ∑' j : ℕ, (((j + 1) ^ 4 : ℕ) : K) * ((t.q : K) ^ (k + 1)) ^ (j + 1) := by
        rw [psiSum]
        refine tsum_congr fun k => ?_
        congr 1
        refine ((hasSum_succ_of_hasSum
          (hasSum_fourth_mul_geometric_eisPsi (t.norm_qpow_lt_one k))
            (by simp)).tsum_eq.symm).trans ?_
        refine tsum_congr fun j => ?_
        push_cast
        ring
    _ = ∑' N : ℕ, (∑ p ∈ (N + 1).divisorsAntidiagonal, ((p.1 * p.2 ^ 4 : ℕ) : K))
          * (t.q : K) ^ (N + 1) := h
    _ = ∑' N : ℕ, ((N + 1 : ℕ) : K) * (∑ d ∈ (N + 1).divisors, (d : K) ^ 3)
          * (t.q : K) ^ (N + 1) := by
        refine tsum_congr fun N => ?_
        congr 1
        calc ∑ p ∈ (N + 1).divisorsAntidiagonal, ((p.1 * p.2 ^ 4 : ℕ) : K)
            = ∑ i ∈ (N + 1).divisors, (((N + 1) / i * i ^ 4 : ℕ) : K) :=
              Nat.sum_divisorsAntidiagonal' (f := fun d e => ((d * e ^ 4 : ℕ) : K))
          _ = ((N + 1 : ℕ) : K) * ∑ d ∈ (N + 1).divisors, (d : K) ^ 3 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i hi => ?_
              have hdvd : i ∣ N + 1 := Nat.dvd_of_mem_divisors hi
              have hkey : (N + 1) / i * i ^ 4 = (N + 1) * i ^ 3 := by
                have h4 : i ^ 4 = i * i ^ 3 := by ring
                rw [h4, ← mul_assoc, Nat.div_mul_cancel hdvd]
              rw [hkey]
              push_cast
              ring

/-- **`q`-expansion of `6·pSqSum`**: `6·𝔭₂ = ∑_{N ≥ 1} (σ₃(N) - σ₁(N))·q^N`, stated with
the integral coefficient `∑_{d ∣ N} (d³ - d)` (no division by `6`). -/
lemma pSqSum_mul_six_eq_qexp :
    6 * t.pSqSum
      = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, ((d : K) ^ 3 - (d : K)))
          * (t.q : K) ^ (N + 1) := by
  have h := t.tsum_weighted_qpow_eq (fun _ => 1) fun m => (m + 1).choose 3
  have hbase : t.pSqSum = ∑' N : ℕ,
      (∑ p ∈ (N + 1).divisorsAntidiagonal, ((1 * (p.2 + 1).choose 3 : ℕ) : K))
        * (t.q : K) ^ (N + 1) := by
    calc t.pSqSum
        = ∑' k : ℕ, ((1 : ℕ) : K)
            * ∑' j : ℕ, (((j + 1 + 1).choose 3 : ℕ) : K) * ((t.q : K) ^ (k + 1)) ^ (j + 1) := by
          rw [pSqSum]
          refine tsum_congr fun k => ?_
          rw [Nat.cast_one, one_mul]
          exact (hasSum_succ_of_hasSum
            (hasSum_choose_eisP_sq (t.norm_qpow_lt_one k))
              (by simp [show Nat.choose 1 3 = 0 from rfl])).tsum_eq.symm
      _ = ∑' N : ℕ,
            (∑ p ∈ (N + 1).divisorsAntidiagonal, ((1 * (p.2 + 1).choose 3 : ℕ) : K))
              * (t.q : K) ^ (N + 1) := h
  rw [hbase, ← tsum_mul_left]
  refine tsum_congr fun N => ?_
  rw [← mul_assoc]
  congr 1
  calc 6 * ∑ p ∈ (N + 1).divisorsAntidiagonal, ((1 * (p.2 + 1).choose 3 : ℕ) : K)
      = ∑ p ∈ (N + 1).divisorsAntidiagonal, (6 : K) * ((1 * (p.2 + 1).choose 3 : ℕ) : K) := by
        rw [Finset.mul_sum]
    _ = ∑ i ∈ (N + 1).divisors, (6 : K) * ((1 * (i + 1).choose 3 : ℕ) : K) :=
        Nat.sum_divisorsAntidiagonal' (f := fun _ e => (6 : K) * ((1 * (e + 1).choose 3 : ℕ) : K))
    _ = ∑ d ∈ (N + 1).divisors, ((d : K) ^ 3 - (d : K)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hcast : (i : K) ^ 3 = 6 * (((i + 1).choose 3 : ℕ) : K) + (i : K) := by
          exact_mod_cast congrArg (Nat.cast (R := K)) (cube_eq_six_choose_succ i)
        rw [one_mul, hcast]
        ring

/-- **`q`-expansion of `12·prSum`**: `12·𝔭𝔯 = ∑_{N ≥ 1} N·(σ₃(N) - σ₁(N))·q^N`, stated
with the integral coefficient `N·∑_{d ∣ N} (d³ - d)` (no division by `12`). -/
lemma prSum_mul_twelve_eq_qexp :
    12 * t.prSum
      = ∑' N : ℕ, ((N + 1 : ℕ) : K) * (∑ d ∈ (N + 1).divisors, ((d : K) ^ 3 - (d : K)))
          * (t.q : K) ^ (N + 1) := by
  have h := t.tsum_weighted_qpow_eq (fun m => m) fun m => (m + 2).choose 4 + (m + 1).choose 4
  have hbase : t.prSum = ∑' N : ℕ,
      (∑ p ∈ (N + 1).divisorsAntidiagonal,
        ((p.1 * ((p.2 + 2).choose 4 + (p.2 + 1).choose 4) : ℕ) : K)) * (t.q : K) ^ (N + 1) := by
    calc t.prSum
        = ∑' k : ℕ, ((k + 1 : ℕ) : K)
            * ∑' j : ℕ, (((j + 1 + 2).choose 4 + (j + 1 + 1).choose 4 : ℕ) : K)
                * ((t.q : K) ^ (k + 1)) ^ (j + 1) := by
          rw [prSum]
          refine tsum_congr fun k => ?_
          congr 1
          exact (hasSum_succ_of_hasSum
            (hasSum_choose_eisP_mul_eisR (t.norm_qpow_lt_one k))
              (by simp [show Nat.choose 2 4 = 0 from rfl,
                show Nat.choose 1 4 = 0 from rfl])).tsum_eq.symm
      _ = ∑' N : ℕ,
            (∑ p ∈ (N + 1).divisorsAntidiagonal,
              ((p.1 * ((p.2 + 2).choose 4 + (p.2 + 1).choose 4) : ℕ) : K))
              * (t.q : K) ^ (N + 1) := h
  rw [hbase, ← tsum_mul_left]
  refine tsum_congr fun N => ?_
  rw [← mul_assoc]
  congr 1
  calc 12 * ∑ p ∈ (N + 1).divisorsAntidiagonal,
        ((p.1 * ((p.2 + 2).choose 4 + (p.2 + 1).choose 4) : ℕ) : K)
      = ∑ p ∈ (N + 1).divisorsAntidiagonal,
          (12 : K) * ((p.1 * ((p.2 + 2).choose 4 + (p.2 + 1).choose 4) : ℕ) : K) := by
        rw [Finset.mul_sum]
    _ = ∑ i ∈ (N + 1).divisors,
          (12 : K) * (((N + 1) / i * ((i + 2).choose 4 + (i + 1).choose 4) : ℕ) : K) :=
        Nat.sum_divisorsAntidiagonal'
          (f := fun d e => (12 : K) * ((d * ((e + 2).choose 4 + (e + 1).choose 4) : ℕ) : K))
    _ = ((N + 1 : ℕ) : K) * ∑ d ∈ (N + 1).divisors, ((d : K) ^ 3 - (d : K)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hdvd : i ∣ N + 1 := Nat.dvd_of_mem_divisors hi
        have hMi : (((N + 1) / i : ℕ) : K) * (i : K) = ((N + 1 : ℕ) : K) := by
          exact_mod_cast congrArg (Nat.cast (R := K)) (Nat.div_mul_cancel hdvd)
        have h4 : (i : K) ^ 4
            = 12 * ((((i + 2).choose 4 : ℕ) : K) + (((i + 1).choose 4 : ℕ) : K))
              + (i : K) ^ 2 := by
          exact_mod_cast congrArg (Nat.cast (R := K)) (fourth_eq_twelve_choose_pair i)
        push_cast at hMi h4 ⊢
        linear_combination (-(((N + 1) / i : ℕ) : K)) * h4 + ((i : K) ^ 3 - (i : K)) * hMi

/-! ### Cauchy products -/

/-- **The Cauchy product of two `q`-expansions with norm-`≤ 1` coefficients.** For
coefficient functions `c`, `d` with `‖c‖, ‖d‖ ≤ 1`,
`(∑_M c(M)·q^M)·(∑_M d(M)·q^M) = ∑_N (∑_{s=1}^{N} c(s)·d(N-s))·q^N` (indices `≥ 1`). -/
private lemma tsum_qexp_mul_tsum_qexp (c d : ℕ → K) (hc : ∀ M, ‖c M‖ ≤ 1)
    (hd : ∀ M, ‖d M‖ ≤ 1) :
    (∑' M : ℕ, c (M + 1) * (t.q : K) ^ (M + 1)) * (∑' M : ℕ, d (M + 1) * (t.q : K) ^ (M + 1))
      = ∑' N : ℕ, (∑ s ∈ Finset.Ico 1 (N + 1), c s * d (N + 1 - s))
          * (t.q : K) ^ (N + 1) := by
  have hgeom : Summable fun M : ℕ => ‖(t.q : K)‖ ^ (M + 1) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one).mul_right ‖(t.q : K)‖
  have hcn : Summable fun M : ℕ => ‖c (M + 1) * (t.q : K) ^ (M + 1)‖ := by
    refine Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_) hgeom
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hc (M + 1))
  have hdn : Summable fun M : ℕ => ‖d (M + 1) * (t.q : K) ^ (M + 1)‖ := by
    refine Summable.of_nonneg_of_le (fun M => norm_nonneg _) (fun M => ?_) hgeom
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hd (M + 1))
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hcn hdn]
  have hD : ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + 1),
        c (k + 1) * (t.q : K) ^ (k + 1) * (d (n - k + 1) * (t.q : K) ^ (n - k + 1)))
        = (∑ s ∈ Finset.Ico 1 (n + 1 + 1), c s * d (n + 1 + 1 - s))
            * (t.q : K) ^ (n + 1 + 1) := by
    intro n
    rw [Finset.sum_mul, Finset.sum_Ico_eq_sum_range]
    have hlen : n + 1 + 1 - 1 = n + 1 := by omega
    rw [hlen]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have h1 : n + 1 + 1 - (1 + k) = n - k + 1 := by omega
    have h3 : 1 + k = k + 1 := by omega
    have h2 : (t.q : K) ^ (k + 1) * (t.q : K) ^ (n - k + 1) = (t.q : K) ^ (n + 1 + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h1, h3, ← h2]
    ring
  have hsum : Summable fun n : ℕ =>
      ∑ k ∈ Finset.range (n + 1),
        c (k + 1) * (t.q : K) ^ (k + 1) * (d (n - k + 1) * (t.q : K) ^ (n - k + 1)) :=
    (summable_norm_sum_mul_range_of_summable_norm hcn hdn).of_norm
  have hhs := hsum.hasSum
  simp only [hD] at hhs ⊢
  have hCsum : HasSum
      (fun N : ℕ => (∑ s ∈ Finset.Ico 1 (N + 1), c s * d (N + 1 - s)) * (t.q : K) ^ (N + 1))
      (∑' n : ℕ, (∑ s ∈ Finset.Ico 1 (n + 1 + 1), c s * d (n + 1 + 1 - s))
        * (t.q : K) ^ (n + 1 + 1)) := by
    refine (hasSum_nat_add_iff' (f := fun N : ℕ =>
      (∑ s ∈ Finset.Ico 1 (N + 1), c s * d (N + 1 - s)) * (t.q : K) ^ (N + 1)) 1).mp ?_
    have hz : ∑ i ∈ Finset.range 1,
        (∑ s ∈ Finset.Ico 1 (i + 1), c s * d (i + 1 - s)) * (t.q : K) ^ (i + 1) = 0 := by
      simp
    rw [hz, sub_zero]
    exact hhs
  exact hCsum.tsum_eq.symm

/-- **`q`-expansion of `s₁²`**: the coefficient of `q^N` is the convolution
`∑_{s=1}^{N-1} σ₁(s)·σ₁(N-s)` (empty for `N = 1`). -/
lemma eisenstein_one_sq_eq_qexp :
    t.eisenstein 1 ^ 2
      = ∑' N : ℕ,
          (∑ s ∈ Finset.Ico 1 (N + 1),
            (∑ d ∈ s.divisors, (d : K)) * ∑ d ∈ (N + 1 - s).divisors, (d : K))
            * (t.q : K) ^ (N + 1) := by
  have he : t.eisenstein 1
      = ∑' M : ℕ, (∑ d ∈ (M + 1).divisors, (d : K)) * (t.q : K) ^ (M + 1) := by
    rw [t.eisenstein_eq_qexp 1]
    refine tsum_congr fun N => ?_
    simp only [pow_one]
  have h := t.tsum_qexp_mul_tsum_qexp (fun s => ∑ d ∈ s.divisors, (d : K))
    (fun s => ∑ d ∈ s.divisors, (d : K)) norm_sigma1_le_one norm_sigma1_le_one
  rw [sq, he]
  exact h

/-- **`q`-expansion of `s₁·s₃`**: the coefficient of `q^N` is the convolution
`∑_{s=1}^{N-1} σ₁(s)·σ₃(N-s)`. -/
lemma eisenstein_one_mul_three_eq_qexp :
    t.eisenstein 1 * t.eisenstein 3
      = ∑' N : ℕ,
          (∑ s ∈ Finset.Ico 1 (N + 1),
            (∑ d ∈ s.divisors, (d : K)) * ∑ d ∈ (N + 1 - s).divisors, (d : K) ^ 3)
            * (t.q : K) ^ (N + 1) := by
  have he : t.eisenstein 1
      = ∑' M : ℕ, (∑ d ∈ (M + 1).divisors, (d : K)) * (t.q : K) ^ (M + 1) := by
    rw [t.eisenstein_eq_qexp 1]
    refine tsum_congr fun N => ?_
    simp only [pow_one]
  have h := t.tsum_qexp_mul_tsum_qexp (fun s => ∑ d ∈ s.divisors, (d : K))
    (fun s => ∑ d ∈ s.divisors, (d : K) ^ 3) norm_sigma1_le_one norm_sigma3_le_one
  rw [he, t.eisenstein_eq_qexp 3]
  exact h

/-- **`q`-expansion of `s₁·rSum`**: the coefficient of `q^N` is
`∑_{s=1}^{N-1} σ₁(s)·(N-s)·σ₁(N-s)`. -/
lemma eisenstein_one_mul_rSum_eq_qexp :
    t.eisenstein 1 * t.rSum
      = ∑' N : ℕ,
          (∑ s ∈ Finset.Ico 1 (N + 1),
            (∑ d ∈ s.divisors, (d : K)) * ((N + 1 - s : ℕ) : K)
              * ∑ d ∈ (N + 1 - s).divisors, (d : K))
            * (t.q : K) ^ (N + 1) := by
  have he : t.eisenstein 1
      = ∑' M : ℕ, (∑ d ∈ (M + 1).divisors, (d : K)) * (t.q : K) ^ (M + 1) := by
    rw [t.eisenstein_eq_qexp 1]
    refine tsum_congr fun N => ?_
    simp only [pow_one]
  have h := t.tsum_qexp_mul_tsum_qexp (fun s => ∑ d ∈ s.divisors, (d : K))
    (fun s => (s : K) * ∑ d ∈ s.divisors, (d : K)) norm_sigma1_le_one
    norm_natCast_mul_sigma1_le_one
  rw [he, t.rSum_eq_qexp]
  refine h.trans ?_
  refine tsum_congr fun N => ?_
  congr 1
  exact Finset.sum_congr rfl fun s _ => (mul_assoc _ _ _).symm

/-- **`q`-expansion of `s₁³`**: the coefficient of `q^N` is the double convolution
`∑_{s=1}^{N-1} σ₁(s)·(∑_{r=1}^{N-s-1} σ₁(r)·σ₁(N-s-r))`, the inner sum being the
`s₁²`-coefficient of `eisenstein_one_sq_eq_qexp`. -/
lemma eisenstein_one_cube_eq_qexp :
    t.eisenstein 1 ^ 3
      = ∑' N : ℕ,
          (∑ s ∈ Finset.Ico 1 (N + 1), (∑ d ∈ s.divisors, (d : K))
            * ∑ r ∈ Finset.Ico 1 (N + 1 - s),
                (∑ d ∈ r.divisors, (d : K)) * ∑ d ∈ (N + 1 - s - r).divisors, (d : K))
            * (t.q : K) ^ (N + 1) := by
  have he : t.eisenstein 1
      = ∑' M : ℕ, (∑ d ∈ (M + 1).divisors, (d : K)) * (t.q : K) ^ (M + 1) := by
    rw [t.eisenstein_eq_qexp 1]
    refine tsum_congr fun N => ?_
    simp only [pow_one]
  have h := t.tsum_qexp_mul_tsum_qexp (fun s => ∑ d ∈ s.divisors, (d : K))
    (fun m => ∑ r ∈ Finset.Ico 1 m, (∑ d ∈ r.divisors, (d : K))
      * ∑ d ∈ (m - r).divisors, (d : K)) norm_sigma1_le_one norm_sigma1_conv_le_one
  have h3 : t.eisenstein 1 ^ 3 = t.eisenstein 1 * t.eisenstein 1 ^ 2 := by ring
  rw [h3, t.eisenstein_one_sq_eq_qexp, he]
  exact h

end Series

end TateParameter

end TateCurvesTheta
