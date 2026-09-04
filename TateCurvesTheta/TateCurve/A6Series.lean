/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import TateCurvesTheta.TateCurve.Weierstrass

/-!
# The integer-coefficient series of the Tate coefficient `a₆`

The Tate coefficient `a₆(q) = -(5 s₃(q) + 7 s₅(q))/12` carries a literal division by `12`. This
file removes the denominator once and for all: thanks to the term-wise divisibility
`12 ∣ 5 m³ + 7 m⁵` (checked in `ZMod 12`), one has

  `a₆(q) = -∑_{n ≥ 0} cₙ · qⁿ⁺¹/(1 - qⁿ⁺¹)`,  `cₙ = (5 (n+1)³ + 7 (n+1)⁵)/12 ∈ ℕ`,

valid whenever `(12 : K) ≠ 0` (`a₆_eq_neg_tsum`). All the norm estimates for `a₆` that were
previously derived under a norm-one hypothesis on `12` (residue characteristic `≠ 2, 3`) now
follow from the corresponding estimates for an arbitrary *integer-weighted* series
`∑ₙ (c n) · qⁿ⁺¹/(1 - qⁿ⁺¹)`, `c : ℕ → ℕ`, which hold in every residue characteristic because
`‖(c n : K)‖ ≤ 1` in a nonarchimedean field:

* `norm_weighted_le` : `‖∑ₙ cₙ Qₙ‖ ≤ ‖q‖`;
* `norm_weighted_sub_q_le` : `‖∑ₙ cₙ Qₙ - q‖ ≤ ‖q‖²` when `c 0 = 1`;
* `norm_weighted_sub_le` : `‖∑ₙ cₙ Qₙ(q₁) - ∑ₙ cₙ Qₙ(q₂)‖ ≤ ‖q₁ - q₂‖`;
* `norm_weighted_sub_q_sub_le` : the degree-`≥ 2` Lipschitz bound
  `‖(∑ₙ cₙ Qₙ(q₁) - q₁) - (∑ₙ cₙ Qₙ(q₂) - q₂)‖ ≤ max ‖q₁‖ ‖q₂‖ · ‖q₁ - q₂‖` when `c 0 = 1`.

Here `Qₙ(q) = qⁿ⁺¹/(1 - qⁿ⁺¹)` is `TateParameter.qFactor`. Specializing to `c = a₆Coeff` gives
`norm_a₆_add_q_le`, `norm_a₆_le`, `norm_a₆_sub_le`, `norm_a₆_add_q_sub_le`, each under the
single hypothesis `(12 : K) ≠ 0`. In particular the whole Tate uniformization becomes available
in residue characteristic `3`.

## The hypothesis split

The group law and the Tate uniformization additionally use `‖(2 : K)‖ = 1` (residue
characteristic `≠ 2`), for the square-avoidance argument of `GroupLaw.lean` and the Newton
iteration of `LargePointParametrization.lean`. The standing hypothesis of those files is
`TameResidueChar K := ‖(2 : K)‖ = 1 ∧ (12 : K) ≠ 0`, defined here; the discriminant, the
`j`-invariant and the `q ↔ j` bijection only need the second component `(12 : K) ≠ 0`.

## Main definitions and results

* `TateCurvesTheta.TameResidueChar` : `‖(2 : K)‖ = 1 ∧ (12 : K) ≠ 0`.
* `TateCurvesTheta.a₆Coeff`, `twelve_mul_a₆Coeff`, `a₆Coeff_zero` : the integer coefficients.
* `TateCurvesTheta.TateParameter.qFactor`, `norm_qFactor`, `norm_qFactor_sub_le` : the common
  analytic factor and its bounds.
* `TateCurvesTheta.TateParameter.a₆_eq_neg_tsum` : `a₆ = -∑ₙ cₙ Qₙ` (`(12 : K) ≠ 0`).
* `TateCurvesTheta.TateParameter.norm_a₆_add_q_le`, `norm_a₆_le`, `norm_a₆_sub_le`,
  `norm_a₆_add_q_sub_le` : the `a₆` bounds under `(12 : K) ≠ 0`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Lemma 5.1(b)
  (integrality of the Tate coefficients).
-/

open Filter Topology

noncomputable section

namespace TateCurvesTheta

/-- Residue characteristic `≠ 2` (`‖2‖ = 1`) together with `12 ≠ 0`: the standing hypothesis
of the group law and of the Tate uniformization. -/
abbrev TameResidueChar (K : Type*) [NormedField K] : Prop := ‖(2 : K)‖ = 1 ∧ (12 : K) ≠ 0

/-- The integer coefficient `cₘ = (5 m³ + 7 m⁵)/12` (with `m = n + 1`) of the `a₆` series. It is a
genuine integer thanks to `twelve_dvd_five_mul_cube_add_seven_mul_pow`. -/
def a₆Coeff (n : ℕ) : ℕ := (5 * (n + 1) ^ 3 + 7 * (n + 1) ^ 5) / 12

/-- The term-wise divisibility `12 ∣ 5 m³ + 7 m⁵` underlying the integrality of the Tate
coefficient `a₆`. Proved by checking all residues in `ZMod 12`. -/
lemma twelve_dvd_five_mul_cube_add_seven_mul_pow (n : ℕ) :
    12 ∣ 5 * (n + 1) ^ 3 + 7 * (n + 1) ^ 5 := by
  have h : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  refine (ZMod.natCast_eq_zero_iff _ 12).mp ?_
  push_cast
  exact h ((n : ZMod 12) + 1)

/-- Defining property of `a₆Coeff`: `12 · cₘ = 5 m³ + 7 m⁵`. -/
lemma twelve_mul_a₆Coeff (n : ℕ) :
    12 * a₆Coeff n = 5 * (n + 1) ^ 3 + 7 * (n + 1) ^ 5 :=
  Nat.mul_div_cancel' (twelve_dvd_five_mul_cube_add_seven_mul_pow n)

/-- The leading coefficient of the `a₆` series is `c₀ = (5 + 7)/12 = 1`. -/
@[simp] lemma a₆Coeff_zero : a₆Coeff 0 = 1 := by decide

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- The common analytic factor `qⁿ⁺¹ / (1 - qⁿ⁺¹)` shared by every Eisenstein term. -/
def qFactor (n : ℕ) : K := (t.q : K) ^ (n + 1) / (1 - (t.q : K) ^ (n + 1))

/-- The Eisenstein series written with the shared factor pulled out. -/
lemma eisenstein_eq_tsum_qFactor (k : ℕ) :
    t.eisenstein k = ∑' n : ℕ, ((n + 1 : ℕ) : K) ^ k * t.qFactor n := by
  simp only [eisenstein, qFactor, mul_div_assoc]

/-- The term-wise identity `5 (m³ Q) + 7 (m⁵ Q) = 12 (cₘ Q)`, where `Q = qᵐ/(1-qᵐ)` and
`cₘ = a₆Coeff`, packaging the divisibility `12 ∣ 5 m³ + 7 m⁵`. -/
lemma term_combo (n : ℕ) :
    5 * (((n + 1 : ℕ) : K) ^ 3 * t.qFactor n) + 7 * (((n + 1 : ℕ) : K) ^ 5 * t.qFactor n)
      = 12 * ((a₆Coeff n : K) * t.qFactor n) := by
  have hcast : 5 * ((n + 1 : ℕ) : K) ^ 3 + 7 * ((n + 1 : ℕ) : K) ^ 5 = 12 * (a₆Coeff n : K) := by
    have h : ((5 * (n + 1) ^ 3 + 7 * (n + 1) ^ 5 : ℕ) : K) = ((12 * a₆Coeff n : ℕ) : K) := by
      rw [twelve_mul_a₆Coeff]
    push_cast at h ⊢
    linear_combination h
  linear_combination t.qFactor n * hcast

section Nonarchimedean

variable [IsUltrametricDist K]

/-- **Ultrametric power-difference bound**: `‖x^(n+1) - y^(n+1)‖ ≤ max ‖x‖ ‖y‖ ^ n · ‖x - y‖`,
by induction from `x^(n+2) - y^(n+2) = x (x^(n+1) - y^(n+1)) + y^(n+1) (x - y)` and the
ultrametric inequality. -/
lemma norm_pow_sub_pow_le (x y : K) (n : ℕ) :
    ‖x ^ (n + 1) - y ^ (n + 1)‖ ≤ (max ‖x‖ ‖y‖) ^ n * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show x ^ (n + 2) - y ^ (n + 2)
        = x * (x ^ (n + 1) - y ^ (n + 1)) + y ^ (n + 1) * (x - y) from by ring]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖x‖ * ‖x ^ (n + 1) - y ^ (n + 1)‖
          ≤ max ‖x‖ ‖y‖ * ((max ‖x‖ ‖y‖) ^ n * ‖x - y‖) :=
            mul_le_mul (le_max_left _ _) ih (norm_nonneg _)
              (le_trans (norm_nonneg x) (le_max_left _ _))
        _ = (max ‖x‖ ‖y‖) ^ (n + 1) * ‖x - y‖ := by ring
    · rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _) (norm_nonneg _)

/-- The shared factor has norm `‖q‖ⁿ⁺¹`. -/
lemma norm_qFactor (n : ℕ) : ‖t.qFactor n‖ = ‖(t.q : K)‖ ^ (n + 1) := by
  rw [qFactor, norm_div, norm_pow, t.norm_one_sub_qpow n, div_one]

/-- The leading factor `Q₀ = q/(1 - q)` differs from `q` by `q²/(1 - q)`. -/
lemma qFactor_zero_sub_q : t.qFactor 0 - (t.q : K) = (t.q : K) ^ 2 / (1 - (t.q : K)) := by
  have hne : (1 : K) - (t.q : K) ≠ 0 := by simpa using t.one_sub_qpow_ne_zero 0
  simp only [qFactor, zero_add, pow_one]
  field_simp
  ring

/-- A natural-number weight is harmless in a nonarchimedean field: `‖(c n) Qₙ‖ ≤ ‖q‖ⁿ⁺¹`. -/
lemma norm_coeff_mul_qFactor_le (c : ℕ → ℕ) (n : ℕ) :
    ‖(c n : K) * t.qFactor n‖ ≤ ‖(t.q : K)‖ ^ (n + 1) := by
  rw [norm_mul, t.norm_qFactor n]
  calc ‖(c n : K)‖ * ‖(t.q : K)‖ ^ (n + 1)
      ≤ 1 * ‖(t.q : K)‖ ^ (n + 1) := by
        gcongr; exact IsUltrametricDist.norm_natCast_le_one K (c n)
    _ = ‖(t.q : K)‖ ^ (n + 1) := one_mul _

/-- Termwise Lipschitz estimate for the shared factor: `Qₙ` at two Tate parameters differs by at
most `max ‖q₁‖ ‖q₂‖ ^ n · ‖q₁ - q₂‖`. -/
lemma norm_qFactor_sub_le (t₁ t₂ : TateParameter K) (n : ℕ) :
    ‖t₁.qFactor n - t₂.qFactor n‖
      ≤ (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ n * ‖(t₁.q : K) - (t₂.q : K)‖ := by
  have h1 := t₁.one_sub_qpow_ne_zero n
  have h2 := t₂.one_sub_qpow_ne_zero n
  rw [qFactor, qFactor, div_sub_div _ _ h1 h2,
    show (t₁.q : K) ^ (n + 1) * (1 - (t₂.q : K) ^ (n + 1))
        - (1 - (t₁.q : K) ^ (n + 1)) * (t₂.q : K) ^ (n + 1)
      = (t₁.q : K) ^ (n + 1) - (t₂.q : K) ^ (n + 1) from by ring,
    norm_div, norm_mul, t₁.norm_one_sub_qpow n, t₂.norm_one_sub_qpow n, one_mul, div_one]
  exact norm_pow_sub_pow_le _ _ n

/-- The head-term estimate of the degree-`≥ 2` Lipschitz bound:
`‖q₁²/(1 - q₁) - q₂²/(1 - q₂)‖ ≤ max ‖q₁‖ ‖q₂‖ · ‖q₁ - q₂‖`, from the factorization
`q₁²/(1-q₁) - q₂²/(1-q₂) = (q₁ - q₂)(q₁ + q₂ - q₁q₂)/((1-q₁)(1-q₂))`. -/
lemma norm_q_sq_div_sub_le (t₁ t₂ : TateParameter K) :
    ‖(t₁.q : K) ^ 2 / (1 - (t₁.q : K)) - (t₂.q : K) ^ 2 / (1 - (t₂.q : K))‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
  have hM0 : (0 : ℝ) ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ :=
    le_trans (norm_nonneg _) (le_max_left _ _)
  have hne1 : (1 : K) - (t₁.q : K) ≠ 0 := by simpa using t₁.one_sub_qpow_ne_zero 0
  have hne2 : (1 : K) - (t₂.q : K) ≠ 0 := by simpa using t₂.one_sub_qpow_ne_zero 0
  rw [div_sub_div _ _ hne1 hne2,
    show (t₁.q : K) ^ 2 * (1 - (t₂.q : K)) - (1 - (t₁.q : K)) * (t₂.q : K) ^ 2
      = ((t₁.q : K) - (t₂.q : K)) * ((t₁.q : K) + (t₂.q : K) - (t₁.q : K) * (t₂.q : K))
        from by ring,
    norm_div, norm_mul, norm_mul,
    show (1 : K) - (t₁.q : K) = 1 - (t₁.q : K) ^ (0 + 1) from by rw [pow_one],
    t₁.norm_one_sub_qpow 0,
    show (1 : K) - (t₂.q : K) = 1 - (t₂.q : K) ^ (0 + 1) from by rw [pow_one],
    t₂.norm_one_sub_qpow 0, one_mul, div_one]
  have hfac : ‖(t₁.q : K) + (t₂.q : K) - (t₁.q : K) * (t₂.q : K)‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (le_max_left _ _) (le_max_right _ _))) ?_)
    rw [norm_neg, norm_mul]
    calc ‖(t₁.q : K)‖ * ‖(t₂.q : K)‖
        ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * 1 :=
          mul_le_mul (le_max_left _ _) t₂.norm_lt_one.le (norm_nonneg _) hM0
      _ = max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ := mul_one _
  calc ‖(t₁.q : K) - (t₂.q : K)‖ * ‖(t₁.q : K) + (t₂.q : K) - (t₁.q : K) * (t₂.q : K)‖
      ≤ ‖(t₁.q : K) - (t₂.q : K)‖ * max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ :=
        mul_le_mul_of_nonneg_left hfac (norm_nonneg _)
    _ = max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := mul_comm _ _

/-- An integer-weighted series is norm-bounded by `‖q‖`: `‖∑ₙ (c n) Qₙ‖ ≤ ‖q‖`. -/
lemma norm_weighted_le (c : ℕ → ℕ) :
    ‖∑' n : ℕ, (c n : K) * t.qFactor n‖ ≤ ‖(t.q : K)‖ := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n => ?_
  exact (t.norm_coeff_mul_qFactor_le c n).trans
    (pow_le_of_le_one (norm_nonneg _) t.norm_lt_one.le n.succ_ne_zero)

variable [CompleteSpace K]

/-- The Eisenstein summands, written with the shared factor, are summable. -/
lemma summable_qFactor_smul (k : ℕ) :
    Summable fun n : ℕ => ((n + 1 : ℕ) : K) ^ k * t.qFactor n := by
  simpa only [qFactor, mul_div_assoc] using t.eisenstein_summand_summable k

/-- An integer-weighted series `∑ₙ (c n) · qⁿ⁺¹/(1-qⁿ⁺¹)` is summable: each term has norm
`≤ ‖q‖ⁿ⁺¹`, dominated by the geometric series `∑ ‖q‖ⁿ⁺¹`. -/
lemma summable_coeff_mul_qFactor (c : ℕ → ℕ) :
    Summable fun n : ℕ => (c n : K) * t.qFactor n := by
  have hg : Summable fun n : ℕ => ‖(t.q : K)‖ ^ (n + 1) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one).mul_right ‖(t.q : K)‖
  exact hg.of_norm_bounded fun n => t.norm_coeff_mul_qFactor_le c n

/-- The `a₆`-coefficient series `∑ₘ cₘ · qᵐ/(1-qᵐ)` is summable. -/
lemma summable_a₆Coeff_qFactor :
    Summable fun n : ℕ => (a₆Coeff n : K) * t.qFactor n :=
  t.summable_coeff_mul_qFactor a₆Coeff

/-- The `5 s₃ + 7 s₅` combination collapses, term by term, into `12` times an *integer* series. -/
lemma eisenstein_combo :
    5 * t.eisenstein 3 + 7 * t.eisenstein 5
      = 12 * ∑' n : ℕ, (a₆Coeff n : K) * t.qFactor n := by
  rw [eisenstein_eq_tsum_qFactor, eisenstein_eq_tsum_qFactor, ← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add ((t.summable_qFactor_smul 3).mul_left 5)
      ((t.summable_qFactor_smul 5).mul_left 7), ← tsum_mul_left]
  exact tsum_congr fun n => t.term_combo n

/-- **The integral form of `a₆`.** For `(12 : K) ≠ 0`, the Tate coefficient is the negative of an
*integer-coefficient* series, `a₆(q) = -∑ₘ cₘ · qᵐ/(1-qᵐ)`, which makes its integrality
manifest. -/
lemma a₆_eq_neg_tsum (h12 : (12 : K) ≠ 0) :
    t.a₆ = -∑' n : ℕ, (a₆Coeff n : K) * t.qFactor n := by
  rw [a₆_def, t.eisenstein_combo]
  field_simp

/-! ### Norm bounds for integer-weighted series -/

/-- **Leading term of an integer-weighted series.** When `c 0 = 1`, `∑ₙ (c n) Qₙ = q + O(q²)`:
the `n = 0` term is `q/(1 - q) = q + q²/(1 - q)` and every later term has norm `≤ ‖q‖²`, so
`‖∑ₙ (c n) Qₙ - q‖ ≤ ‖q‖²`. -/
lemma norm_weighted_sub_q_le (c : ℕ → ℕ) (hc : c 0 = 1) :
    ‖(∑' n : ℕ, (c n : K) * t.qFactor n) - (t.q : K)‖ ≤ ‖(t.q : K)‖ ^ 2 := by
  rw [(t.summable_coeff_mul_qFactor c).tsum_eq_zero_add, add_sub_right_comm, hc, Nat.cast_one,
    one_mul, t.qFactor_zero_sub_q]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · -- `‖q²/(1-q)‖ = ‖q‖²`.
    rw [norm_div, norm_pow, show (1 : K) - (t.q : K) = 1 - (t.q : K) ^ (0 + 1) by rw [pow_one],
      t.norm_one_sub_qpow 0, div_one]
  · -- `‖∑ later terms‖ ≤ ‖q‖²`.
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n => ?_
    refine (t.norm_coeff_mul_qFactor_le c (n + 1)).trans ?_
    exact pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le (by omega)

/-- **Lipschitz estimate for integer-weighted series**:
`‖∑ₙ (c n) Qₙ(q₁) - ∑ₙ (c n) Qₙ(q₂)‖ ≤ ‖q₁ - q₂‖`. -/
lemma norm_weighted_sub_le (t₁ t₂ : TateParameter K) (c : ℕ → ℕ) :
    ‖(∑' n : ℕ, (c n : K) * t₁.qFactor n) - ∑' n : ℕ, (c n : K) * t₂.qFactor n‖
      ≤ ‖(t₁.q : K) - (t₂.q : K)‖ := by
  have hM0 : (0 : ℝ) ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ :=
    le_trans (norm_nonneg _) (le_max_left _ _)
  have hM1 : max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ ≤ 1 :=
    max_le t₁.norm_lt_one.le t₂.norm_lt_one.le
  rw [← (t₁.summable_coeff_mul_qFactor c).tsum_sub (t₂.summable_coeff_mul_qFactor c)]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n => ?_
  rw [← mul_sub, norm_mul]
  calc ‖(c n : K)‖ * ‖t₁.qFactor n - t₂.qFactor n‖
      ≤ 1 * ((max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ n * ‖(t₁.q : K) - (t₂.q : K)‖) :=
        mul_le_mul (IsUltrametricDist.norm_natCast_le_one K _) (t₁.norm_qFactor_sub_le t₂ n)
          (norm_nonneg _) zero_le_one
    _ ≤ 1 * (1 * ‖(t₁.q : K) - (t₂.q : K)‖) := by
        gcongr
        exact pow_le_one₀ hM0 hM1
    _ = ‖(t₁.q : K) - (t₂.q : K)‖ := by rw [one_mul, one_mul]

/-- **Degree-`≥ 2` Lipschitz estimate for integer-weighted series**: when `c 0 = 1`,
subtracting the common leading term `q` improves the Lipschitz constant to `max ‖q₁‖ ‖q₂‖`:
`‖(∑ₙ (c n) Qₙ(q₁) - q₁) - (∑ₙ (c n) Qₙ(q₂) - q₂)‖ ≤ max ‖q₁‖ ‖q₂‖ · ‖q₁ - q₂‖`. -/
lemma norm_weighted_sub_q_sub_le (t₁ t₂ : TateParameter K) (c : ℕ → ℕ) (hc : c 0 = 1) :
    ‖((∑' n : ℕ, (c n : K) * t₁.qFactor n) - (t₁.q : K))
        - ((∑' n : ℕ, (c n : K) * t₂.qFactor n) - (t₂.q : K))‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
  have hM0 : (0 : ℝ) ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ :=
    le_trans (norm_nonneg _) (le_max_left _ _)
  have hM1 : max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ ≤ 1 :=
    max_le t₁.norm_lt_one.le t₂.norm_lt_one.le
  have h1 := t₁.summable_coeff_mul_qFactor c
  have h2 := t₂.summable_coeff_mul_qFactor c
  have hg : Summable fun n : ℕ => (c n : K) * t₁.qFactor n - (c n : K) * t₂.qFactor n :=
    h1.sub h2
  -- split the difference of the two series into the `n = 0` head and the `n ≥ 1` tail
  have e : ((∑' n : ℕ, (c n : K) * t₁.qFactor n) - (t₁.q : K))
        - ((∑' n : ℕ, (c n : K) * t₂.qFactor n) - (t₂.q : K))
      = ((t₁.q : K) ^ 2 / (1 - (t₁.q : K)) - (t₂.q : K) ^ 2 / (1 - (t₂.q : K)))
        + ∑' n : ℕ, ((c (n + 1) : K) * t₁.qFactor (n + 1)
            - (c (n + 1) : K) * t₂.qFactor (n + 1)) := by
    rw [sub_sub_sub_comm, ← h1.tsum_sub h2, hg.tsum_eq_zero_add, ← t₁.qFactor_zero_sub_q,
      ← t₂.qFactor_zero_sub_q, hc, Nat.cast_one, one_mul]
    ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (t₁.norm_q_sq_div_sub_le t₂) ?_)
  -- tail: every summand with `n ≥ 1` is bounded by `max ‖q₁‖ ‖q₂‖ · ‖q₁ - q₂‖`
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg hM0 (norm_nonneg _)) fun n => ?_
  rw [← mul_sub, norm_mul]
  calc ‖(c (n + 1) : K)‖ * ‖t₁.qFactor (n + 1) - t₂.qFactor (n + 1)‖
      ≤ 1 * ((max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖) ^ (n + 1) * ‖(t₁.q : K) - (t₂.q : K)‖) :=
        mul_le_mul (IsUltrametricDist.norm_natCast_le_one K _)
          (t₁.norm_qFactor_sub_le t₂ (n + 1)) (norm_nonneg _) zero_le_one
    _ ≤ 1 * (max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖) := by
        gcongr
        exact pow_le_of_le_one hM0 hM1 n.succ_ne_zero
    _ = max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := one_mul _

/-! ### The bounds for `a₆` -/

/-- **Leading term of `a₆`.** `a₆(q) = -q + O(q²)`, i.e. `‖a₆(q) + q‖ ≤ ‖q‖²`. Requires only
`(12 : K) ≠ 0`. -/
lemma norm_a₆_add_q_le (h12 : (12 : K) ≠ 0) :
    ‖t.a₆ + (t.q : K)‖ ≤ ‖(t.q : K)‖ ^ 2 := by
  rw [t.a₆_eq_neg_tsum h12, neg_add_eq_sub, norm_sub_rev]
  exact t.norm_weighted_sub_q_le a₆Coeff a₆Coeff_zero

/-- The Tate coefficient `a₆(q)` is norm-bounded by `‖q‖` (`(12 : K) ≠ 0`). -/
lemma norm_a₆_le (h12 : (12 : K) ≠ 0) : ‖t.a₆‖ ≤ ‖(t.q : K)‖ := by
  rw [t.a₆_eq_neg_tsum h12, norm_neg]
  exact t.norm_weighted_le a₆Coeff

/-- **Lipschitz estimate for `a₆`**: `‖a₆(q₁) - a₆(q₂)‖ ≤ ‖q₁ - q₂‖` (`(12 : K) ≠ 0`). -/
lemma norm_a₆_sub_le (t₁ t₂ : TateParameter K) (h12 : (12 : K) ≠ 0) :
    ‖t₁.a₆ - t₂.a₆‖ ≤ ‖(t₁.q : K) - (t₂.q : K)‖ := by
  rw [t₁.a₆_eq_neg_tsum h12, t₂.a₆_eq_neg_tsum h12, neg_sub_neg, norm_sub_rev]
  exact t₁.norm_weighted_sub_le t₂ a₆Coeff

/-- **Degree-`≥ 2` Lipschitz estimate for `a₆ + q`**:
`‖(a₆(q₁) + q₁) - (a₆(q₂) + q₂)‖ ≤ max ‖q₁‖ ‖q₂‖ · ‖q₁ - q₂‖` (`(12 : K) ≠ 0`). -/
lemma norm_a₆_add_q_sub_le (t₁ t₂ : TateParameter K) (h12 : (12 : K) ≠ 0) :
    ‖(t₁.a₆ + (t₁.q : K)) - (t₂.a₆ + (t₂.q : K))‖
      ≤ max ‖(t₁.q : K)‖ ‖(t₂.q : K)‖ * ‖(t₁.q : K) - (t₂.q : K)‖ := by
  rw [t₁.a₆_eq_neg_tsum h12, t₂.a₆_eq_neg_tsum h12,
    show ∀ a b c d : K, -a + b - (-c + d) = -(a - b - (c - d)) from fun _ _ _ _ => by ring,
    norm_neg]
  exact t₁.norm_weighted_sub_q_sub_le t₂ a₆Coeff a₆Coeff_zero

end Nonarchimedean

end TateParameter

end TateCurvesTheta
