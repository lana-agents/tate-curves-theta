/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Divisor-sum convolution identities: Besge and `σ₁ ∗ σ₃`

Self-contained **finite** arithmetic: the two classical divisor-sum convolution identities —
Besge's identity for `σ₁ ∗ σ₁` and the weight-6 evaluation of `σ₁ ∗ σ₃` — proved by the
"Euclidean descent" bijection on the solution set of `a·x + b·y = N` in positive integers.
Everything is a `Finset` sum over `ℕ` with values in `ℤ`: no analysis, no topology, no
modular forms.

The engine is the finite set `tateQuad N` of quadruples `((a, x), (b, y))` with
`a·x + b·y = N`, `a, x, b, y ≥ 1`.  Three families of manipulations suffice:

* the **descent bijection** `((a,x),(b,y)) ↦ ((a-b,x),(b,x+y))` from the region `b < a` to the
  region `x < y` (`sum_master`);
* the **swap involution** `((a,x),(b,y)) ↦ ((b,y),(a,x))` (`sum_swap_lt`, `sum_swap_xy`);
* explicit **diagonal evaluations** on `a = b` and `x = y` (`sum_diag_ab`, `sum_diag_xy`),
  reduced to divisor power sums via elementary power-sum formulas.

Combining these for quadratic (resp. quartic) monomial weights `xⁱyʲ` and factoring the full
sum as a convolution (`sum_tateQuad_mul`) yields the two target identities.

## Main results

* `TateCurvesTheta.besge_identity` : Besge's identity
  `12·∑_{0<s<N} σ₁(s)σ₁(N-s) = 5σ₃(N) + (1 - 6N)σ₁(N)`.
* `TateCurvesTheta.sigma_one_three_conv` : the weight-6 Liouville/Glaisher evaluation
  `240·∑_{0<s<N} σ₁(s)σ₃(N-s) = 21σ₅(N) + (10 - 30N)σ₃(N) - σ₁(N)`.

## References

* M. Besge, *Extrait d'une lettre de M. Besge à M. Liouville*,
  J. Math. Pures Appl. 7 (1862), 256.
* J. W. L. Glaisher, *On the square of the series in which the coefficients are the sums of the
  divisors of the exponents*, Messenger Math. 14 (1885), 156–163.
* J. G. Huard, Z. M. Ou, B. K. Spearman, K. S. Williams, *Elementary evaluation of certain
  convolution sums involving divisor functions*, Number Theory for the Millennium II (2002),
  229–274.
-/

open Finset

namespace TateCurvesTheta

/-! ### The divisor power sum `σₖ` with values in `ℤ` -/

/-- The divisor power sum `σₖ(N) = ∑_{d ∣ N} dᵏ`, as an integer. -/
def sigmaZ (k N : ℕ) : ℤ := ∑ d ∈ N.divisors, (d : ℤ) ^ k

/-- The divisor power sum computed over the second components of `divisorsAntidiagonal`. -/
lemma sigmaZ_eq_sum_divisorsAntidiagonal (k s : ℕ) :
    ∑ p ∈ s.divisorsAntidiagonal, (p.2 : ℤ) ^ k = sigmaZ k s :=
  Nat.sum_divisorsAntidiagonal' (f := fun _ d => (d : ℤ) ^ k)

/-! ### Solution quadruples of `a·x + b·y = N` -/

/-- The solution quadruples `((a, x), (b, y))` of `a*x + b*y = N` in positive integers. -/
def tateQuad (N : ℕ) : Finset ((ℕ × ℕ) × ℕ × ℕ) :=
  ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)) ×ˢ
      (Finset.range (N + 1) ×ˢ Finset.range (N + 1))).filter
    fun q => q.1.1 * q.1.2 + q.2.1 * q.2.2 = N ∧ 0 < q.1.1 ∧ 0 < q.1.2 ∧ 0 < q.2.1 ∧ 0 < q.2.2

/-- Membership in `tateQuad N` is exactly the equation `a*x + b*y = N` together with
positivity of all four entries; the auxiliary range bounds are automatic. -/
lemma mem_tateQuad {N : ℕ} {q : (ℕ × ℕ) × ℕ × ℕ} :
    q ∈ tateQuad N ↔
      q.1.1 * q.1.2 + q.2.1 * q.2.2 = N ∧ 0 < q.1.1 ∧ 0 < q.1.2 ∧ 0 < q.2.1 ∧ 0 < q.2.2 := by
  obtain ⟨⟨a, x⟩, b, y⟩ := q
  simp only [tateQuad, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨heq, ha, hx, hb, hy⟩ := h
  have h1 : a * 1 ≤ a * x := Nat.mul_le_mul (Nat.le_refl a) hx
  have h2 : 1 * x ≤ a * x := Nat.mul_le_mul ha (Nat.le_refl x)
  have h3 : b * 1 ≤ b * y := Nat.mul_le_mul (Nat.le_refl b) hy
  have h4 : 1 * y ≤ b * y := Nat.mul_le_mul hb (Nat.le_refl y)
  exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-! ### Power sums over `Finset.Ico 1 M`

The four basic power sums, in the divisibility-free form `(∑ …) * c = polynomial in M`,
valid for **all** `M : ℕ` (including `M = 0, 1`). -/

/-- `2·∑_{1 ≤ x < M} x = M² - M`. -/
lemma sum_Ico_pow_one (M : ℕ) : (∑ x ∈ Finset.Ico 1 M, (x : ℤ)) * 2 = (M : ℤ) ^ 2 - M := by
  induction M with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · rw [Finset.sum_Ico_succ_top hn]
      push_cast
      linear_combination ih

/-- `6·∑_{1 ≤ x < M} x² = 2M³ - 3M² + M`. -/
lemma sum_Ico_pow_two (M : ℕ) :
    (∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 2) * 6 = 2 * (M : ℤ) ^ 3 - 3 * (M : ℤ) ^ 2 + M := by
  induction M with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · rw [Finset.sum_Ico_succ_top hn]
      push_cast
      linear_combination ih

/-- `4·∑_{1 ≤ x < M} x³ = M⁴ - 2M³ + M²`. -/
lemma sum_Ico_pow_three (M : ℕ) :
    (∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 3) * 4 = (M : ℤ) ^ 4 - 2 * (M : ℤ) ^ 3 + (M : ℤ) ^ 2 := by
  induction M with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · rw [Finset.sum_Ico_succ_top hn]
      push_cast
      linear_combination ih

/-- `30·∑_{1 ≤ x < M} x⁴ = 6M⁵ - 15M⁴ + 10M³ - M`. -/
lemma sum_Ico_pow_four (M : ℕ) :
    (∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 4) * 30
      = 6 * (M : ℤ) ^ 5 - 15 * (M : ℤ) ^ 4 + 10 * (M : ℤ) ^ 3 - M := by
  induction M with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · rw [Finset.sum_Ico_succ_top hn]
      push_cast
      linear_combination ih

/-- Reflection `x ↦ M - x` is a bijection of `Ico 1 M`, so it preserves sums. -/
lemma sum_Ico_reflect (M : ℕ) (f : ℕ → ℤ) :
    ∑ x ∈ Finset.Ico 1 M, f (M - x) = ∑ x ∈ Finset.Ico 1 M, f x := by
  refine Finset.sum_nbij' (i := fun x => M - x) (j := fun x => M - x) ?_ ?_ ?_ ?_ ?_ <;>
    intro x hx <;> obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hx
  · exact Finset.mem_Ico.mpr (by omega)
  · exact Finset.mem_Ico.mpr (by omega)
  · omega
  · omega
  · rfl

/-- `6·∑_{1 ≤ x < M} x(M - x) = M³ - M`. -/
lemma sum_Ico_mul_sub (M : ℕ) :
    (∑ x ∈ Finset.Ico 1 M, (x : ℤ) * ((M - x : ℕ) : ℤ)) * 6 = (M : ℤ) ^ 3 - M := by
  have hcast : ∑ x ∈ Finset.Ico 1 M, (x : ℤ) * ((M - x : ℕ) : ℤ)
      = (M : ℤ) * (∑ x ∈ Finset.Ico 1 M, (x : ℤ)) - ∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Nat.cast_sub (Finset.mem_Ico.mp hx).2.le]
    ring
  linear_combination 6 * hcast + 3 * (M : ℤ) * sum_Ico_pow_one M - sum_Ico_pow_two M

/-- `60·∑_{1 ≤ x < M} x(M - x)³ = 3M⁵ - 5M³ + 2M`. -/
lemma sum_Ico_mul_sub_cube (M : ℕ) :
    (∑ x ∈ Finset.Ico 1 M, (x : ℤ) * ((M - x : ℕ) : ℤ) ^ 3) * 60
      = 3 * (M : ℤ) ^ 5 - 5 * (M : ℤ) ^ 3 + 2 * M := by
  have hcast : ∑ x ∈ Finset.Ico 1 M, (x : ℤ) * ((M - x : ℕ) : ℤ) ^ 3
      = (M : ℤ) ^ 3 * (∑ x ∈ Finset.Ico 1 M, (x : ℤ))
        - 3 * (M : ℤ) ^ 2 * (∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 2)
        + 3 * (M : ℤ) * (∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 3)
        - ∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 4 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Nat.cast_sub (Finset.mem_Ico.mp hx).2.le]
    ring
  linear_combination 60 * hcast + 30 * (M : ℤ) ^ 3 * sum_Ico_pow_one M
    - 30 * (M : ℤ) ^ 2 * sum_Ico_pow_two M + 45 * (M : ℤ) * sum_Ico_pow_three M
    - 2 * sum_Ico_pow_four M

/-- `30·∑_{1 ≤ x < M} x²(M - x)² = M⁵ - M`. -/
lemma sum_Ico_sq_mul_sub_sq (M : ℕ) :
    (∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 2 * ((M - x : ℕ) : ℤ) ^ 2) * 30 = (M : ℤ) ^ 5 - M := by
  have hcast : ∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 2 * ((M - x : ℕ) : ℤ) ^ 2
      = (M : ℤ) ^ 2 * (∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 2)
        - 2 * (M : ℤ) * (∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 3)
        + ∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 4 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Nat.cast_sub (Finset.mem_Ico.mp hx).2.le]
    ring
  linear_combination 30 * hcast + 5 * (M : ℤ) ^ 2 * sum_Ico_pow_two M
    - 15 * (M : ℤ) * sum_Ico_pow_three M + sum_Ico_pow_four M

/-- `6·∑_{1 ≤ x < M} (M - x)² = 2M³ - 3M² + M`. -/
lemma sum_Ico_sub_pow_two (M : ℕ) :
    (∑ x ∈ Finset.Ico 1 M, ((M - x : ℕ) : ℤ) ^ 2) * 6
      = 2 * (M : ℤ) ^ 3 - 3 * (M : ℤ) ^ 2 + M := by
  have h : ∑ x ∈ Finset.Ico 1 M, ((M - x : ℕ) : ℤ) ^ 2 = ∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 2 :=
    sum_Ico_reflect M fun n => (n : ℤ) ^ 2
  linear_combination 6 * h + sum_Ico_pow_two M

/-- `30·∑_{1 ≤ x < M} (M - x)⁴ = 6M⁵ - 15M⁴ + 10M³ - M`. -/
lemma sum_Ico_sub_pow_four (M : ℕ) :
    (∑ x ∈ Finset.Ico 1 M, ((M - x : ℕ) : ℤ) ^ 4) * 30
      = 6 * (M : ℤ) ^ 5 - 15 * (M : ℤ) ^ 4 + 10 * (M : ℤ) ^ 3 - M := by
  have h : ∑ x ∈ Finset.Ico 1 M, ((M - x : ℕ) : ℤ) ^ 4 = ∑ x ∈ Finset.Ico 1 M, (x : ℤ) ^ 4 :=
    sum_Ico_reflect M fun n => (n : ℤ) ^ 4
  linear_combination 30 * h + sum_Ico_pow_four M

/-! ### Divisor-sum plumbing -/

/-- Summing `(N/d)ᵏ` over the divisors of `N` gives `σₖ(N)`. -/
lemma sum_divisors_div_pow (N k : ℕ) :
    ∑ d ∈ N.divisors, ((N / d : ℕ) : ℤ) ^ k = sigmaZ k N :=
  Nat.sum_div_divisors N fun d => (d : ℤ) ^ k

/-- Summing `(N/d)·dᵏ` over the divisors of `N` gives `N·σ_{k-1}(N)`, for `1 ≤ k`. -/
lemma sum_divisors_div_mul_pow (N k : ℕ) (hk : 1 ≤ k) :
    ∑ d ∈ N.divisors, ((N / d : ℕ) : ℤ) * (d : ℤ) ^ k = (N : ℤ) * sigmaZ (k - 1) N := by
  have h : ∀ d ∈ N.divisors,
      ((N / d : ℕ) : ℤ) * (d : ℤ) ^ k = (N : ℤ) * (d : ℤ) ^ (k - 1) := by
    intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    have hpow : (d : ℤ) ^ k = (d : ℤ) * (d : ℤ) ^ (k - 1) := by
      conv_lhs => rw [show k = 1 + (k - 1) by omega]
      rw [pow_add, pow_one]
    have hdiv : ((N / d : ℕ) : ℤ) * (d : ℤ) = (N : ℤ) := by
      rw_mod_cast [Nat.div_mul_cancel hdvd]
    calc ((N / d : ℕ) : ℤ) * (d : ℤ) ^ k
        = ((N / d : ℕ) : ℤ) * (d : ℤ) * (d : ℤ) ^ (k - 1) := by rw [hpow]; ring
      _ = (N : ℤ) * (d : ℤ) ^ (k - 1) := by rw [hdiv]
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
  rfl

/-- The `x = y` diagonal value: `∑_{d ∣ N} (N/d - 1)·dʲ = N·σ_{j-1}(N) - σⱼ(N)` for `1 ≤ j`. -/
lemma diag_xy_value (N j : ℕ) (hj : 1 ≤ j) :
    ∑ x ∈ N.divisors, (((N / x : ℕ) : ℤ) - 1) * (x : ℤ) ^ j
      = (N : ℤ) * sigmaZ (j - 1) N - sigmaZ j N := by
  have h : ∀ x ∈ N.divisors,
      (((N / x : ℕ) : ℤ) - 1) * (x : ℤ) ^ j
        = ((N / x : ℕ) : ℤ) * (x : ℤ) ^ j - (x : ℤ) ^ j :=
    fun x _ => by ring
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, sum_divisors_div_mul_pow N j hj]
  rfl

/-! ### The descent bijection, the swap involution, and the region splits -/

/-- **Master bijection** (Euclidean descent): `((a,x),(b,y)) ↦ ((a-b,x),(b,x+y))` identifies
the region `b < a` of `tateQuad N` with the region `x < y`, shifting the weight's second
argument by the first. -/
lemma sum_master (N : ℕ) (f : ℕ → ℕ → ℤ) :
    ∑ q ∈ (tateQuad N).filter fun q => q.2.1 < q.1.1, f q.1.2 q.2.2
      = ∑ q ∈ (tateQuad N).filter fun q => q.1.2 < q.2.2, f q.1.2 (q.2.2 - q.1.2) := by
  refine Finset.sum_nbij'
    (i := fun q => ((q.1.1 - q.2.1, q.1.2), (q.2.1, q.1.2 + q.2.2)))
    (j := fun q => ((q.1.1 + q.2.1, q.1.2), (q.2.1, q.2.2 - q.1.2))) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq ⊢
    obtain ⟨⟨heq, ha, hx, hb, hy⟩, hba⟩ := hq
    have h1 : (a - b) * x = a * x - b * x := Nat.sub_mul a b x
    have h2 : b * (x + y) = b * x + b * y := Nat.mul_add b x y
    have h3 : b * x ≤ a * x := Nat.mul_le_mul (Nat.le_of_lt hba) (Nat.le_refl x)
    exact ⟨⟨by omega, by omega, hx, hb, by omega⟩, by omega⟩
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq ⊢
    obtain ⟨⟨heq, ha, hx, hb, hy⟩, hxy⟩ := hq
    have h1 : (a + b) * x = a * x + b * x := Nat.add_mul a b x
    have h2 : b * (y - x) = b * y - b * x := Nat.mul_sub b y x
    have h3 : b * x ≤ b * y := Nat.mul_le_mul (Nat.le_refl b) (Nat.le_of_lt hxy)
    exact ⟨⟨by omega, by omega, hx, hb, by omega⟩, by omega⟩
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq
    simp only [Prod.mk.injEq, and_true, true_and]
    omega
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    change f x y = f x (x + y - x)
    rw [Nat.add_sub_cancel_left]

/-- **Swap symmetry** for the `(a, b)` comparison: the involution
`((a,x),(b,y)) ↦ ((b,y),(a,x))` exchanges the regions `a < b` and `b < a`. -/
lemma sum_swap_lt (N : ℕ) (f : ℕ → ℕ → ℤ) :
    ∑ q ∈ (tateQuad N).filter fun q => q.1.1 < q.2.1, f q.1.2 q.2.2
      = ∑ q ∈ (tateQuad N).filter fun q => q.2.1 < q.1.1, f q.2.2 q.1.2 := by
  refine Finset.sum_nbij' (i := fun q => (q.2, q.1)) (j := fun q => (q.2, q.1)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq ⊢
    obtain ⟨⟨heq, ha, hx, hb, hy⟩, hab⟩ := hq
    exact ⟨⟨by omega, hb, hy, ha, hx⟩, hab⟩
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq ⊢
    obtain ⟨⟨heq, ha, hx, hb, hy⟩, hba⟩ := hq
    exact ⟨⟨by omega, hb, hy, ha, hx⟩, hba⟩
  · exact fun q _ => rfl
  · exact fun q _ => rfl
  · exact fun q _ => rfl

/-- **Swap symmetry** for the `(x, y)` comparison: the involution
`((a,x),(b,y)) ↦ ((b,y),(a,x))` exchanges the regions `y < x` and `x < y`. -/
lemma sum_swap_xy (N : ℕ) (f : ℕ → ℕ → ℤ) :
    ∑ q ∈ (tateQuad N).filter fun q => q.2.2 < q.1.2, f q.1.2 q.2.2
      = ∑ q ∈ (tateQuad N).filter fun q => q.1.2 < q.2.2, f q.2.2 q.1.2 := by
  refine Finset.sum_nbij' (i := fun q => (q.2, q.1)) (j := fun q => (q.2, q.1)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq ⊢
    obtain ⟨⟨heq, ha, hx, hb, hy⟩, hyx⟩ := hq
    exact ⟨⟨by omega, hb, hy, ha, hx⟩, hyx⟩
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq ⊢
    obtain ⟨⟨heq, ha, hx, hb, hy⟩, hxy⟩ := hq
    exact ⟨⟨by omega, hb, hy, ha, hx⟩, hxy⟩
  · exact fun q _ => rfl
  · exact fun q _ => rfl
  · exact fun q _ => rfl

/-- **Region split** by the trichotomy `b < a`, `a < b`, `a = b`. -/
lemma sum_split_ab (N : ℕ) (f : ℕ → ℕ → ℤ) :
    ∑ q ∈ tateQuad N, f q.1.2 q.2.2
      = (∑ q ∈ (tateQuad N).filter fun q => q.2.1 < q.1.1, f q.1.2 q.2.2)
        + (∑ q ∈ (tateQuad N).filter fun q => q.1.1 < q.2.1, f q.1.2 q.2.2)
        + ∑ q ∈ (tateQuad N).filter fun q => q.1.1 = q.2.1, f q.1.2 q.2.2 := by
  rw [← Finset.sum_filter_add_sum_filter_not (tateQuad N) (fun q => q.2.1 < q.1.1)
    (fun q => f q.1.2 q.2.2), add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not ((tateQuad N).filter fun q => ¬q.2.1 < q.1.1)
    (fun q => q.1.1 < q.2.1) (fun q => f q.1.2 q.2.2), Finset.filter_filter,
    Finset.filter_filter]
  congr 1
  · exact Finset.sum_congr (Finset.filter_congr fun q _ => by omega) fun _ _ => rfl
  · exact Finset.sum_congr (Finset.filter_congr fun q _ => by omega) fun _ _ => rfl

/-- **Region split** by the trichotomy `y < x`, `x < y`, `x = y`. -/
lemma sum_split_xy (N : ℕ) (f : ℕ → ℕ → ℤ) :
    ∑ q ∈ tateQuad N, f q.1.2 q.2.2
      = (∑ q ∈ (tateQuad N).filter fun q => q.2.2 < q.1.2, f q.1.2 q.2.2)
        + (∑ q ∈ (tateQuad N).filter fun q => q.1.2 < q.2.2, f q.1.2 q.2.2)
        + ∑ q ∈ (tateQuad N).filter fun q => q.1.2 = q.2.2, f q.1.2 q.2.2 := by
  rw [← Finset.sum_filter_add_sum_filter_not (tateQuad N) (fun q => q.2.2 < q.1.2)
    (fun q => f q.1.2 q.2.2), add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not ((tateQuad N).filter fun q => ¬q.2.2 < q.1.2)
    (fun q => q.1.2 < q.2.2) (fun q => f q.1.2 q.2.2), Finset.filter_filter,
    Finset.filter_filter]
  congr 1
  · exact Finset.sum_congr (Finset.filter_congr fun q _ => by omega) fun _ _ => rfl
  · exact Finset.sum_congr (Finset.filter_congr fun q _ => by omega) fun _ _ => rfl

/-! ### Diagonal evaluations and the convolution factorization -/

/-- **Diagonal `a = b`**: a solution with `a = b` is `d·(x + y) = N`, i.e. a divisor `d` of `N`
together with a split `x + (N/d - x)` of `N/d`. -/
lemma sum_diag_ab (N : ℕ) (hN : 0 < N) (f : ℕ → ℕ → ℤ) :
    ∑ q ∈ (tateQuad N).filter fun q => q.1.1 = q.2.1, f q.1.2 q.2.2
      = ∑ d ∈ N.divisors, ∑ x ∈ Finset.Ico 1 (N / d), f x (N / d - x) := by
  refine Eq.trans ?_ (Finset.sum_sigma' N.divisors (fun d => Finset.Ico 1 (N / d))
    fun d x => f x (N / d - x)).symm
  refine Finset.sum_nbij' (i := fun q => ⟨q.1.1, q.1.2⟩)
    (j := fun p => ((p.1, p.2), (p.1, N / p.1 - p.2))) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq
    obtain ⟨⟨heq, ha, hx, hb, hy⟩, hab⟩ := hq
    subst hab
    have hNa : a * (x + y) = N := by rw [← heq]; ring
    have hdiv : N / a = x + y := Nat.div_eq_of_eq_mul_right ha hNa.symm
    simp only [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_Ico]
    exact ⟨⟨⟨x + y, hNa.symm⟩, hN.ne'⟩, hx, by omega⟩
  · intro p hp
    obtain ⟨d, z⟩ := p
    simp only [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_Ico] at hp
    obtain ⟨⟨hdvd, -⟩, hz1, hz2⟩ := hp
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdvd hN
    have hdN : d * (N / d) = N := Nat.mul_div_cancel' hdvd
    have h1 : d * (N / d - z) = d * (N / d) - d * z := Nat.mul_sub d (N / d) z
    have h2 : d * z ≤ d * (N / d) := Nat.mul_le_mul (Nat.le_refl d) (Nat.le_of_lt hz2)
    simp only [Finset.mem_filter, mem_tateQuad, and_true]
    exact ⟨by omega, hd, by omega, hd, by omega⟩
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq
    obtain ⟨⟨heq, ha, hx, hb, hy⟩, hab⟩ := hq
    subst hab
    have hNa : a * (x + y) = N := by rw [← heq]; ring
    have hdiv : N / a = x + y := Nat.div_eq_of_eq_mul_right ha hNa.symm
    change ((a, x), (a, N / a - x)) = ((a, x), a, y)
    rw [show N / a - x = y by omega]
  · exact fun p _ => rfl
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq
    obtain ⟨⟨heq, ha, hx, hb, hy⟩, hab⟩ := hq
    subst hab
    have hNa : a * (x + y) = N := by rw [← heq]; ring
    have hdiv : N / a = x + y := Nat.div_eq_of_eq_mul_right ha hNa.symm
    change f x y = f x (N / a - x)
    rw [show N / a - x = y by omega]

/-- **Diagonal `x = y`**: a solution with `x = y` is `(a + b)·x = N`, i.e. a divisor `x` of `N`
together with a split `a + (N/x - a)` of `N/x`; the weight is constant on each fiber. -/
lemma sum_diag_xy (N : ℕ) (hN : 0 < N) (f : ℕ → ℕ → ℤ) :
    ∑ q ∈ (tateQuad N).filter fun q => q.1.2 = q.2.2, f q.1.2 q.2.2
      = ∑ x ∈ N.divisors, ∑ _a ∈ Finset.Ico 1 (N / x), f x x := by
  refine Eq.trans ?_ (Finset.sum_sigma' N.divisors (fun x => Finset.Ico 1 (N / x))
    fun x _ => f x x).symm
  refine Finset.sum_nbij' (i := fun q => ⟨q.1.2, q.1.1⟩)
    (j := fun p => ((p.2, p.1), (N / p.1 - p.2, p.1))) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq
    obtain ⟨⟨heq, ha, hx, hb, hy⟩, hxy⟩ := hq
    subst hxy
    have hNx : (a + b) * x = N := by rw [← heq]; ring
    have hdiv : N / x = a + b := Nat.div_eq_of_eq_mul_left hx hNx.symm
    simp only [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_Ico]
    exact ⟨⟨⟨a + b, by rw [← hNx]; ring⟩, hN.ne'⟩, ha, by omega⟩
  · intro p hp
    obtain ⟨t, z⟩ := p
    simp only [Finset.mem_sigma, Nat.mem_divisors, Finset.mem_Ico] at hp
    obtain ⟨⟨hdvd, -⟩, hz1, hz2⟩ := hp
    have ht : 0 < t := Nat.pos_of_dvd_of_pos hdvd hN
    have htN : N / t * t = N := Nat.div_mul_cancel hdvd
    have h1 : (N / t - z) * t = N / t * t - z * t := Nat.sub_mul (N / t) z t
    have h2 : z * t ≤ N / t * t := Nat.mul_le_mul (Nat.le_of_lt hz2) (Nat.le_refl t)
    simp only [Finset.mem_filter, mem_tateQuad, and_true]
    exact ⟨by omega, by omega, ht, by omega, ht⟩
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq
    obtain ⟨⟨heq, ha, hx, hb, hy⟩, hxy⟩ := hq
    subst hxy
    have hNx : (a + b) * x = N := by rw [← heq]; ring
    have hdiv : N / x = a + b := Nat.div_eq_of_eq_mul_left hx hNx.symm
    change ((a, x), (N / x - a, x)) = ((a, x), b, x)
    rw [show N / x - a = b by omega]
  · exact fun p _ => rfl
  · intro q hq
    obtain ⟨⟨a, x⟩, b, y⟩ := q
    simp only [Finset.mem_filter, mem_tateQuad] at hq
    obtain ⟨-, hxy⟩ := hq
    subst hxy
    rfl

/-- **Convolution factorization**: partitioning `tateQuad N` by `s = a·x` turns a product
weight `f(x)·g(y)` into the convolution of the divisor sums of `f` and `g`. -/
lemma sum_tateQuad_mul (N : ℕ) (_hN : 0 < N) (f g : ℕ → ℤ) :
    ∑ q ∈ tateQuad N, f q.1.2 * g q.2.2
      = ∑ s ∈ Finset.Ico 1 N,
          (∑ p ∈ s.divisorsAntidiagonal, f p.2) * ∑ p ∈ (N - s).divisorsAntidiagonal, g p.2 :=
  calc ∑ q ∈ tateQuad N, f q.1.2 * g q.2.2
      = ∑ p ∈ (Finset.Ico 1 N).sigma
          (fun s => s.divisorsAntidiagonal ×ˢ (N - s).divisorsAntidiagonal),
          f p.2.1.2 * g p.2.2.2 := by
        refine Finset.sum_nbij' (i := fun q => ⟨q.1.1 * q.1.2, q⟩) (j := fun p => p.2)
          ?_ ?_ ?_ ?_ ?_
        · intro q hq
          obtain ⟨⟨a, x⟩, b, y⟩ := q
          simp only [mem_tateQuad] at hq
          obtain ⟨heq, ha, hx, hb, hy⟩ := hq
          have hax : 0 < a * x := Nat.mul_pos ha hx
          have hby : 0 < b * y := Nat.mul_pos hb hy
          dsimp only
          simp only [Finset.mem_sigma, Finset.mem_Ico, Finset.mem_product,
            Nat.mem_divisorsAntidiagonal, true_and]
          omega
        · intro p hp
          obtain ⟨s, r⟩ := p
          simp only [Finset.mem_sigma, Finset.mem_Ico, Finset.mem_product,
            Nat.mem_divisorsAntidiagonal] at hp
          obtain ⟨⟨hs1, hs2⟩, ⟨hax, -⟩, hby, -⟩ := hp
          simp only [mem_tateQuad]
          have h1 : r.1.1 ≠ 0 ∧ r.1.2 ≠ 0 := by rw [← mul_ne_zero_iff]; omega
          have h2 : r.2.1 ≠ 0 ∧ r.2.2 ≠ 0 := by rw [← mul_ne_zero_iff]; omega
          exact ⟨by omega, by omega, by omega, by omega, by omega⟩
        · exact fun q _ => rfl
        · intro p hp
          obtain ⟨s, r⟩ := p
          simp only [Finset.mem_sigma, Finset.mem_product,
            Nat.mem_divisorsAntidiagonal] at hp
          obtain ⟨-, ⟨h1, -⟩, -⟩ := hp
          subst h1
          rfl
        · exact fun q _ => rfl
    _ = ∑ s ∈ Finset.Ico 1 N, ∑ p ∈ s.divisorsAntidiagonal ×ˢ (N - s).divisorsAntidiagonal,
          f p.1.2 * g p.2.2 :=
        (Finset.sum_sigma' (Finset.Ico 1 N)
          (fun s => s.divisorsAntidiagonal ×ˢ (N - s).divisorsAntidiagonal)
          fun _ p => f p.1.2 * g p.2.2).symm
    _ = ∑ s ∈ Finset.Ico 1 N,
          (∑ p ∈ s.divisorsAntidiagonal, f p.2) * ∑ p ∈ (N - s).divisorsAntidiagonal, g p.2 :=
        Finset.sum_congr rfl fun s _ =>
          (Finset.sum_product' s.divisorsAntidiagonal (N - s).divisorsAntidiagonal
            fun p r => f p.2 * g r.2).trans
            (Finset.sum_mul_sum s.divisorsAntidiagonal (N - s).divisorsAntidiagonal
              (fun p => f p.2) fun p => g p.2).symm

/-! ### Monomial-weight atoms

Private abbreviations for the sums of the monomial weight `xⁱ·yʲ` over the regions of
`tateQuad N`; the certificates below are linear algebra over these atoms. -/

/-- Full sum of the monomial weight `xⁱyʲ` over `tateQuad N`. -/
private def tSum (N i j : ℕ) : ℤ := ∑ q ∈ tateQuad N, (q.1.2 : ℤ) ^ i * (q.2.2 : ℤ) ^ j

/-- Monomial sum over the region `b < a`. -/
private def mA (N i j : ℕ) : ℤ :=
  ∑ q ∈ (tateQuad N).filter fun q => q.2.1 < q.1.1, (q.1.2 : ℤ) ^ i * (q.2.2 : ℤ) ^ j

/-- Monomial sum over the region `a < b`. -/
private def mB (N i j : ℕ) : ℤ :=
  ∑ q ∈ (tateQuad N).filter fun q => q.1.1 < q.2.1, (q.1.2 : ℤ) ^ i * (q.2.2 : ℤ) ^ j

/-- Monomial sum over the region `x < y`. -/
private def mX (N i j : ℕ) : ℤ :=
  ∑ q ∈ (tateQuad N).filter fun q => q.1.2 < q.2.2, (q.1.2 : ℤ) ^ i * (q.2.2 : ℤ) ^ j

/-- Monomial sum over the region `y < x`. -/
private def mY (N i j : ℕ) : ℤ :=
  ∑ q ∈ (tateQuad N).filter fun q => q.2.2 < q.1.2, (q.1.2 : ℤ) ^ i * (q.2.2 : ℤ) ^ j

/-- Monomial sum over the diagonal `a = b`. -/
private def dA (N i j : ℕ) : ℤ :=
  ∑ q ∈ (tateQuad N).filter fun q => q.1.1 = q.2.1, (q.1.2 : ℤ) ^ i * (q.2.2 : ℤ) ^ j

/-- Monomial sum over the diagonal `x = y`. -/
private def dX (N i j : ℕ) : ℤ :=
  ∑ q ∈ (tateQuad N).filter fun q => q.1.2 = q.2.2, (q.1.2 : ℤ) ^ i * (q.2.2 : ℤ) ^ j

/-- Swapping the pairs identifies the region `a < b` with `b < a`, transposing the weight. -/
private lemma mB_eq (N i j : ℕ) : mB N i j = mA N j i := by
  refine (sum_swap_lt N fun x y => (x : ℤ) ^ i * (y : ℤ) ^ j).trans ?_
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

/-- Swapping the pairs identifies the region `y < x` with `x < y`, transposing the weight. -/
private lemma mY_eq (N i j : ℕ) : mY N i j = mX N j i := by
  refine (sum_swap_xy N fun x y => (x : ℤ) ^ i * (y : ℤ) ^ j).trans ?_
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

/-- Splitting the full monomial sum along the `(a, b)` trichotomy. -/
private lemma tSum_split (N i j : ℕ) : tSum N i j = mA N i j + mA N j i + dA N i j := by
  have h : tSum N i j = mA N i j + mB N i j + dA N i j :=
    sum_split_ab N fun x y => (x : ℤ) ^ i * (y : ℤ) ^ j
  rw [h, mB_eq]

/-- Splitting the full monomial sum along the `(x, y)` trichotomy. -/
private lemma tSum_split_xy (N i j : ℕ) : tSum N i j = mX N j i + mX N i j + dX N i j := by
  have h : tSum N i j = mY N i j + mX N i j + dX N i j :=
    sum_split_xy N fun x y => (x : ℤ) ^ i * (y : ℤ) ^ j
  rw [h, mY_eq]

/-- Consistency: both trichotomies compute the same full sum. -/
private lemma consistency (N i j : ℕ) :
    mA N i j + mA N j i + dA N i j = mX N i j + mX N j i + dX N i j := by
  have h1 := tSum_split N i j
  have h2 := tSum_split_xy N i j
  linarith

/-- The master bijection with the shifted weight written as an integer binomial. -/
private lemma mA_shift (N i j : ℕ) :
    mA N i j = ∑ q ∈ (tateQuad N).filter fun q => q.1.2 < q.2.2,
      (q.1.2 : ℤ) ^ i * ((q.2.2 : ℤ) - (q.1.2 : ℤ)) ^ j := by
  refine (sum_master N fun x y => (x : ℤ) ^ i * (y : ℤ) ^ j).trans ?_
  refine Finset.sum_congr rfl fun q hq => ?_
  have hlt : q.1.2 < q.2.2 := (Finset.mem_filter.mp hq).2
  change (q.1.2 : ℤ) ^ i * ((q.2.2 - q.1.2 : ℕ) : ℤ) ^ j
    = (q.1.2 : ℤ) ^ i * ((q.2.2 : ℤ) - (q.1.2 : ℤ)) ^ j
  rw [Nat.cast_sub hlt.le]

/-! ### Shift expansions of the master bijection for the eight monomial weights -/

/-- Master instance for the weight `y²`. -/
private lemma mA02 (N : ℕ) : mA N 0 2 = mX N 0 2 - 2 * mX N 1 1 + mX N 2 0 := by
  rw [mA_shift]
  simp only [mX]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Master instance for the weight `x·y`. -/
private lemma mA11 (N : ℕ) : mA N 1 1 = mX N 1 1 - mX N 2 0 := by
  rw [mA_shift]
  simp only [mX]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Master instance for the weight `x²`. -/
private lemma mA20 (N : ℕ) : mA N 2 0 = mX N 2 0 := by
  rw [mA_shift]
  simp only [mX]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Master instance for the weight `y⁴`. -/
private lemma mA04 (N : ℕ) :
    mA N 0 4 = mX N 0 4 - 4 * mX N 1 3 + 6 * mX N 2 2 - 4 * mX N 3 1 + mX N 4 0 := by
  rw [mA_shift]
  simp only [mX]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Master instance for the weight `x·y³`. -/
private lemma mA13 (N : ℕ) :
    mA N 1 3 = mX N 1 3 - 3 * mX N 2 2 + 3 * mX N 3 1 - mX N 4 0 := by
  rw [mA_shift]
  simp only [mX]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Master instance for the weight `x²·y²`. -/
private lemma mA22 (N : ℕ) : mA N 2 2 = mX N 2 2 - 2 * mX N 3 1 + mX N 4 0 := by
  rw [mA_shift]
  simp only [mX]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Master instance for the weight `x³·y`. -/
private lemma mA31 (N : ℕ) : mA N 3 1 = mX N 3 1 - mX N 4 0 := by
  rw [mA_shift]
  simp only [mX]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Master instance for the weight `x⁴`. -/
private lemma mA40 (N : ℕ) : mA N 4 0 = mX N 4 0 := by
  rw [mA_shift]
  simp only [mX]
  exact Finset.sum_congr rfl fun q _ => by ring

/-! ### The two certificates -/

/-- Degree-2 certificate: `4·TA[xy] = -2·K[y²] + K[xy]` with `K[f] = Dxy[f] - Dab[f]`. -/
private lemma quad_e1 (N : ℕ) :
    4 * mA N 1 1 = -2 * (dX N 0 2 - dA N 0 2) + (dX N 1 1 - dA N 1 1) := by
  linear_combination 2 * mA02 N + 2 * mA11 N + 2 * mA20 N - 2 * consistency N 0 2
    + consistency N 1 1

/-- Degree-4 certificate: `8·(TA[xy³] + TA[x³y]) = -2·K[y⁴] + 4·K[xy³] - 3·K[x²y²]`. -/
private lemma quad_e2 (N : ℕ) :
    8 * (mA N 1 3 + mA N 3 1)
      = -2 * (dX N 0 4 - dA N 0 4) + 4 * (dX N 1 3 - dA N 1 3)
        - 3 * (dX N 2 2 - dA N 2 2) := by
  linear_combination 2 * mA04 N + 4 * mA13 N + 6 * mA22 N + 4 * mA31 N + 2 * mA40 N
    - 2 * consistency N 0 4 + 4 * consistency N 1 3 - 3 * consistency N 2 2

/-! ### Diagonal values -/

/-- The `x = y` diagonal of a degree-`(i+j)` monomial weight. -/
private lemma dX_val (N : ℕ) (hN : 0 < N) (i j : ℕ) (hij : 1 ≤ i + j) :
    dX N i j = (N : ℤ) * sigmaZ (i + j - 1) N - sigmaZ (i + j) N := by
  have h : dX N i j
      = ∑ x ∈ N.divisors, ∑ _a ∈ Finset.Ico 1 (N / x), (x : ℤ) ^ i * (x : ℤ) ^ j :=
    sum_diag_xy N hN fun x y => (x : ℤ) ^ i * (y : ℤ) ^ j
  rw [h]
  have h2 : ∀ x ∈ N.divisors,
      ∑ _a ∈ Finset.Ico 1 (N / x), (x : ℤ) ^ i * (x : ℤ) ^ j
        = (((N / x : ℕ) : ℤ) - 1) * (x : ℤ) ^ (i + j) := by
    intro x hx
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hx
    have h1 : 1 ≤ N / x :=
      (Nat.one_le_div_iff (Nat.pos_of_dvd_of_pos hdvd hN)).mpr (Nat.le_of_dvd hN hdvd)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub h1]
    push_cast
    ring
  rw [Finset.sum_congr rfl h2]
  exact diag_xy_value N (i + j) hij

/-- The `a = b` diagonal of the weight `x·y`. -/
private lemma dA11_val (N : ℕ) (hN : 0 < N) : 6 * dA N 1 1 = sigmaZ 3 N - sigmaZ 1 N := by
  have h : dA N 1 1
      = ∑ d ∈ N.divisors, ∑ x ∈ Finset.Ico 1 (N / d), (x : ℤ) * ((N / d - x : ℕ) : ℤ) := by
    refine (sum_diag_ab N hN fun x y => (x : ℤ) ^ 1 * (y : ℤ) ^ 1).trans ?_
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [h, Finset.mul_sum]
  have h2 : ∀ d ∈ N.divisors,
      6 * ∑ x ∈ Finset.Ico 1 (N / d), (x : ℤ) * ((N / d - x : ℕ) : ℤ)
        = ((N / d : ℕ) : ℤ) ^ 3 - ((N / d : ℕ) : ℤ) ^ 1 :=
    fun d _ => by linear_combination sum_Ico_mul_sub (N / d)
  rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, sum_divisors_div_pow N 3,
    sum_divisors_div_pow N 1]

/-- The `a = b` diagonal of the weight `y²`. -/
private lemma dA02_val (N : ℕ) (hN : 0 < N) :
    6 * dA N 0 2 = 2 * sigmaZ 3 N - 3 * sigmaZ 2 N + sigmaZ 1 N := by
  have h : dA N 0 2
      = ∑ d ∈ N.divisors, ∑ x ∈ Finset.Ico 1 (N / d), ((N / d - x : ℕ) : ℤ) ^ 2 := by
    refine (sum_diag_ab N hN fun x y => (x : ℤ) ^ 0 * (y : ℤ) ^ 2).trans ?_
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [h, Finset.mul_sum]
  have h2 : ∀ d ∈ N.divisors,
      6 * ∑ x ∈ Finset.Ico 1 (N / d), ((N / d - x : ℕ) : ℤ) ^ 2
        = 2 * ((N / d : ℕ) : ℤ) ^ 3 - 3 * ((N / d : ℕ) : ℤ) ^ 2 + ((N / d : ℕ) : ℤ) ^ 1 :=
    fun d _ => by linear_combination sum_Ico_sub_pow_two (N / d)
  rw [Finset.sum_congr rfl h2]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_divisors_div_pow N 3, sum_divisors_div_pow N 2, sum_divisors_div_pow N 1]

/-- The `a = b` diagonal of the weight `y⁴`. -/
private lemma dA04_val (N : ℕ) (hN : 0 < N) :
    30 * dA N 0 4 = 6 * sigmaZ 5 N - 15 * sigmaZ 4 N + 10 * sigmaZ 3 N - sigmaZ 1 N := by
  have h : dA N 0 4
      = ∑ d ∈ N.divisors, ∑ x ∈ Finset.Ico 1 (N / d), ((N / d - x : ℕ) : ℤ) ^ 4 := by
    refine (sum_diag_ab N hN fun x y => (x : ℤ) ^ 0 * (y : ℤ) ^ 4).trans ?_
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [h, Finset.mul_sum]
  have h2 : ∀ d ∈ N.divisors,
      30 * ∑ x ∈ Finset.Ico 1 (N / d), ((N / d - x : ℕ) : ℤ) ^ 4
        = 6 * ((N / d : ℕ) : ℤ) ^ 5 - 15 * ((N / d : ℕ) : ℤ) ^ 4
          + 10 * ((N / d : ℕ) : ℤ) ^ 3 - ((N / d : ℕ) : ℤ) ^ 1 :=
    fun d _ => by linear_combination sum_Ico_sub_pow_four (N / d)
  rw [Finset.sum_congr rfl h2]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_divisors_div_pow N 5, sum_divisors_div_pow N 4, sum_divisors_div_pow N 3,
    sum_divisors_div_pow N 1]

/-- The `a = b` diagonal of the weight `x·y³`. -/
private lemma dA13_val (N : ℕ) (hN : 0 < N) :
    60 * dA N 1 3 = 3 * sigmaZ 5 N - 5 * sigmaZ 3 N + 2 * sigmaZ 1 N := by
  have h : dA N 1 3
      = ∑ d ∈ N.divisors, ∑ x ∈ Finset.Ico 1 (N / d), (x : ℤ) * ((N / d - x : ℕ) : ℤ) ^ 3 := by
    refine (sum_diag_ab N hN fun x y => (x : ℤ) ^ 1 * (y : ℤ) ^ 3).trans ?_
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [h, Finset.mul_sum]
  have h2 : ∀ d ∈ N.divisors,
      60 * ∑ x ∈ Finset.Ico 1 (N / d), (x : ℤ) * ((N / d - x : ℕ) : ℤ) ^ 3
        = 3 * ((N / d : ℕ) : ℤ) ^ 5 - 5 * ((N / d : ℕ) : ℤ) ^ 3 + 2 * ((N / d : ℕ) : ℤ) ^ 1 :=
    fun d _ => by linear_combination sum_Ico_mul_sub_cube (N / d)
  rw [Finset.sum_congr rfl h2]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_divisors_div_pow N 5, sum_divisors_div_pow N 3, sum_divisors_div_pow N 1]

/-- The `a = b` diagonal of the weight `x²·y²`. -/
private lemma dA22_val (N : ℕ) (hN : 0 < N) : 30 * dA N 2 2 = sigmaZ 5 N - sigmaZ 1 N := by
  have h : dA N 2 2
      = ∑ d ∈ N.divisors, ∑ x ∈ Finset.Ico 1 (N / d), (x : ℤ) ^ 2 * ((N / d - x : ℕ) : ℤ) ^ 2 :=
    sum_diag_ab N hN fun x y => (x : ℤ) ^ 2 * (y : ℤ) ^ 2
  rw [h, Finset.mul_sum]
  have h2 : ∀ d ∈ N.divisors,
      30 * ∑ x ∈ Finset.Ico 1 (N / d), (x : ℤ) ^ 2 * ((N / d - x : ℕ) : ℤ) ^ 2
        = ((N / d : ℕ) : ℤ) ^ 5 - ((N / d : ℕ) : ℤ) ^ 1 :=
    fun d _ => by linear_combination sum_Ico_sq_mul_sub_sq (N / d)
  rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, sum_divisors_div_pow N 5,
    sum_divisors_div_pow N 1]

/-! ### The convolution values of the full sums -/

/-- The full `x·y`-weighted sum is the `σ₁ ∗ σ₁` convolution. -/
private lemma tSum_conv_one (N : ℕ) (hN : 0 < N) :
    tSum N 1 1 = ∑ s ∈ Finset.Ico 1 N, sigmaZ 1 s * sigmaZ 1 (N - s) := by
  refine (sum_tateQuad_mul N hN (fun n => (n : ℤ) ^ 1) fun n => (n : ℤ) ^ 1).trans ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sigmaZ_eq_sum_divisorsAntidiagonal, sigmaZ_eq_sum_divisorsAntidiagonal]

/-- The full `x·y³`-weighted sum is the `σ₁ ∗ σ₃` convolution. -/
private lemma tSum_conv_three (N : ℕ) (hN : 0 < N) :
    tSum N 1 3 = ∑ s ∈ Finset.Ico 1 N, sigmaZ 1 s * sigmaZ 3 (N - s) := by
  refine (sum_tateQuad_mul N hN (fun n => (n : ℤ) ^ 1) fun n => (n : ℤ) ^ 3).trans ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sigmaZ_eq_sum_divisorsAntidiagonal, sigmaZ_eq_sum_divisorsAntidiagonal]

/-! ### The two convolution identities -/

/-- **Besge's identity**: the classical `σ₁∗σ₁` convolution evaluation. -/
theorem besge_identity (N : ℕ) (hN : 0 < N) :
    12 * ∑ s ∈ Finset.Ico 1 N, sigmaZ 1 s * sigmaZ 1 (N - s)
      = 5 * sigmaZ 3 N + sigmaZ 1 N - 6 * (N : ℤ) * sigmaZ 1 N := by
  have hconv := tSum_conv_one N hN
  have hsplit := tSum_split N 1 1
  have he1 := quad_e1 N
  have hdX11 : dX N 1 1 = (N : ℤ) * sigmaZ 1 N - sigmaZ 2 N := by
    simpa using dX_val N hN 1 1 (by norm_num)
  have hdX02 : dX N 0 2 = (N : ℤ) * sigmaZ 1 N - sigmaZ 2 N := by
    simpa using dX_val N hN 0 2 (by norm_num)
  have hdA11 := dA11_val N hN
  have hdA02 := dA02_val N hN
  linear_combination (-12) * hconv + 12 * hsplit + 6 * he1 - 12 * hdX02 + 2 * hdA02
    + 6 * hdX11 + hdA11

/-- **The `σ₁∗σ₃` convolution evaluation** (weight-6 Liouville/Glaisher identity). -/
theorem sigma_one_three_conv (N : ℕ) (hN : 0 < N) :
    240 * ∑ s ∈ Finset.Ico 1 N, sigmaZ 1 s * sigmaZ 3 (N - s)
      = 21 * sigmaZ 5 N + 10 * sigmaZ 3 N - sigmaZ 1 N - 30 * (N : ℤ) * sigmaZ 3 N := by
  have hconv := tSum_conv_three N hN
  have hsplit := tSum_split N 1 3
  have he2 := quad_e2 N
  have hdX04 : dX N 0 4 = (N : ℤ) * sigmaZ 3 N - sigmaZ 4 N := by
    simpa using dX_val N hN 0 4 (by norm_num)
  have hdX13 : dX N 1 3 = (N : ℤ) * sigmaZ 3 N - sigmaZ 4 N := by
    simpa using dX_val N hN 1 3 (by norm_num)
  have hdX22 : dX N 2 2 = (N : ℤ) * sigmaZ 3 N - sigmaZ 4 N := by
    simpa using dX_val N hN 2 2 (by norm_num)
  have hdA04 := dA04_val N hN
  have hdA13 := dA13_val N hN
  have hdA22 := dA22_val N hN
  linear_combination (-240) * hconv + 240 * hsplit + 30 * he2 - 60 * hdX04 + 120 * hdX13
    - 90 * hdX22 + 2 * hdA04 + 2 * hdA13 + 3 * hdA22

end TateCurvesTheta
