/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TateCurvesTheta.TateCurve.Parametrization
import TateCurvesTheta.Theta.Durfee
import TateCurvesTheta.Theta.ThetaProdGlobalLaurent

/-!
# Global Laurent coefficient families for `X·θ(-u)²` and `Y·θ(-u)³`

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), write
`Θ(u) := theta (-u)`, whose zeros are exactly the orbit `qᶻ` (`theta_eq_zero_iff`). The Tate
coordinates `X`, `Y` (`TateCurve/Parametrization.lean`) have double resp. triple poles along
`qᶻ`, so the products `X(u)·Θ(u)²` and `Y(u)·Θ(u)³` are pole-free. This file exhibits them as
**global two-sided Laurent series**: explicit coefficient families `XThetaSqCoeff`,
`YThetaCubeCoeff : ℤ → K` with

* `Summable (fun n : ℤ => XThetaSqCoeff n * uⁿ)` for **every** unit `u`, and
* `HasSum (fun n => XThetaSqCoeff n * uⁿ) (X u · Θ(u)²)` for every `u` off the orbit `qᶻ`
  (similarly for `Y` with cubes).

## The mechanism

By the (unconditional) Jacobi triple product `theta = thetaProd` (`Theta/Durfee.lean`),
`Θ(u) = F₋q · H(u) · G(u)` where `F₋q := thetaProdFactor (-q)` is a constant,
`H(u) := thetaProdFactor (-(q·u)) = ∏_{j≥0} (1 - q^{j+1}u)` and
`G(u) := thetaProdFactor (-u⁻¹) = ∏_{j≥0} (1 - qʲu⁻¹)`. The pole of the `n`-th term
`Xterm u n = qⁿu/(1-qⁿu)²` of `X` is killed by the matching linear factor of `Θ²` — with the
factor **removed**, the remaining *punctured* product is still an everywhere-convergent
one-sided power series. Concretely, `pFactorCoeff p` is the coefficient family of the
punctured Euler product `∏_{j≥0, j≠p} (1 + qʲc)`, defined by the recursion obtained from
peeling the `j = 0` factor; it satisfies the division-free identity
`(1 + q^p c) · ∑ₖ pFactorCoeff p k · cᵏ = thetaProdFactor c` and the uniform bound
`‖pFactorCoeff p k‖ ≤ ‖q‖^{k(k-1)/2}` (independent of the puncture `p`).

The per-`n` products `Xterm u n · Θ(u)²` are then global Laurent series obtained by the
nonarchimedean Cauchy product (`hasSum_laurentConvolution`) of everywhere-convergent power
series in `u` and in `u⁻¹`:

* for `n ≥ 1`:  `Xterm u n · Θ(u)² = qⁿ·u · (F₋q · A_{n-1}(u) · G(u))²` with
  `A_p(u) := ∑ₖ pFactorCoeff p k · (-q·u)ᵏ`;
* for `n ≤ 0`:  `Xterm u n · Θ(u)² = q⁻ⁿ·u⁻¹ · (F₋q · H(u) · B_{-n}(u))²` with
  `B_p(u) := ∑ₖ pFactorCoeff p k · (-u⁻¹)ᵏ`;
* for `Y`: `Yterm u n · Θ(u)³ = q²ⁿ·u² (F₋q A_{n-1} G)³` for `n ≥ 1` and
  `= -q⁻ⁿ·u⁻¹ (F₋q H B_{-n})³` for `n ≤ 0` (the cube keeps the sign).

The `n`-sum of these coefficient families converges coefficientwise, geometrically in `|n|`
with a uniform-in-`n` "entire" majorant obtained by convolving the triangular-exponent bound
`‖q‖^{k(k-1)/2}`; the resulting double families are summable over `ℤ × ℤ` for every `u`, and
the two fibrewise collapses (`HasSum.prod_fiberwise`) give both the coefficientwise summability
(all `u`) and the value (off-orbit `u`). The constant terms `-2·s₁·Θ²` and `+s₁·Θ³` come from
the self-convolution of the explicit theta coefficients `n ↦ (-1)ⁿ q^{e n}`.

## Main definitions

* `TateCurvesTheta.TateParameter.pFactorCoeff` : coefficients of the punctured Euler product
  `∏_{j≠p} (1 + qʲc)`.
* `TateCurvesTheta.lconv`, `TateCurvesTheta.rconv`, `TateCurvesTheta.EntireBound` : the
  two-sided convolution of coefficient families and the entire real bound families that
  dominate them.
* `TateCurvesTheta.TateParameter.XThetaSqCoeff`, `TateParameter.YThetaCubeCoeff` : the global
  Laurent coefficient families of `X·Θ²` and `Y·Θ³`.

## Main results

* `TateParameter.one_add_qpow_mul_pFactorSeries` : the defining identity
  `(1 + q^p c) · ∑ₖ pFactorCoeff p k · cᵏ = thetaProdFactor c`.
* `TateParameter.summable_XThetaSqCoeff_mul_zpow` and the `Y`-analogue
  `TateParameter.summable_YThetaCubeCoeff_mul_zpow` :
  the coefficient families converge at **every** unit `u`.
* `TateParameter.hasSum_XThetaSqCoeff`, `TateParameter.hasSum_YThetaCubeCoeff` : off the orbit
  `qᶻ` they sum to `X u · theta (-u)²` resp. `Y u · theta (-u)³`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, §3.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* D. Mumford, *Tata Lectures on Theta* I.
-/

open Filter Topology

noncomputable section

namespace TateCurvesTheta

/-! ### Two-sided convolutions and entire bound families -/

section Convolution

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The two-sided (Laurent) convolution of two `ℤ`-indexed coefficient families:
`lconv α β ℓ = ∑'ₘ α (ℓ - m) · β m`. This is the coefficient family of the product of the
Laurent series with coefficients `α` and `β` (`hasSum_laurentConvolution`). -/
def lconv (α β : ℤ → K) : ℤ → K := fun ℓ => ∑' m : ℤ, α (ℓ - m) * β m

/-- The real convolution of two nonnegative bound families, dominating `lconv` termwise. -/
def rconv (A B : ℤ → ℝ) : ℤ → ℝ := fun ℓ => ∑' m : ℤ, A (ℓ - m) * B m

/-- An **entire bound family**: a nonnegative real family `D : ℤ → ℝ` such that
`∑ₘ D m · rᵐ` converges for every radius `r > 0`. Such families dominate coefficient
families of global two-sided Laurent series and are closed under `rconv`, shifts and sums. -/
structure EntireBound (D : ℤ → ℝ) : Prop where
  nonneg : ∀ m, 0 ≤ D m
  summable : ∀ r : ℝ, 0 < r → Summable fun m : ℤ => D m * r ^ m

/-- An entire bound family is summable (radius `r = 1`). -/
lemma EntireBound.summable_one {A : ℤ → ℝ} (hA : EntireBound A) : Summable A := by
  have h := hA.summable 1 one_pos
  exact h.congr fun m => by simp

/-- Each convolution slice `m ↦ A (ℓ - m) · B m` of two entire bound families is summable. -/
lemma summable_rconv_slice {A B : ℤ → ℝ} (hA : EntireBound A) (hB : EntireBound B) (ℓ : ℤ) :
    Summable fun m : ℤ => A (ℓ - m) * B m := by
  have hprod : Summable fun p : ℤ × ℤ => A p.1 * B p.2 :=
    hA.summable_one.mul_of_nonneg hB.summable_one (fun n => hA.nonneg n) fun m => hB.nonneg m
  have hinj : Function.Injective (fun m : ℤ => ((ℓ - m, m) : ℤ × ℤ)) := fun a b hab => by
    simpa using congrArg Prod.snd hab
  have h := hprod.comp_injective hinj
  exact h.congr fun m => rfl

/-- The shear `(ℓ, m) ↦ (ℓ - m, m)` on `ℤ²`, used to Fubini convolutions. -/
private def shearZ : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 - p.2, p.2)
  invFun p := (p.1 + p.2, p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- Entire bound families are closed under real convolution. -/
lemma EntireBound.rconv {A B : ℤ → ℝ} (hA : EntireBound A) (hB : EntireBound B) :
    EntireBound (rconv A B) := by
  constructor
  · intro ℓ
    exact tsum_nonneg fun m => mul_nonneg (hA.nonneg _) (hB.nonneg _)
  · intro r hr
    have hprod := (hA.summable r hr).mul_of_nonneg (hB.summable r hr)
      (fun n => mul_nonneg (hA.nonneg n) (zpow_nonneg hr.le n))
      (fun m => mul_nonneg (hB.nonneg m) (zpow_nonneg hr.le m))
    have hshear : Summable fun p : ℤ × ℤ => A (p.1 - p.2) * B p.2 * r ^ p.1 := by
      have h := (shearZ.summable_iff
        (f := fun p : ℤ × ℤ => (A p.1 * r ^ p.1) * (B p.2 * r ^ p.2))).mpr hprod
      refine h.congr fun p => ?_
      change (A (p.1 - p.2) * r ^ (p.1 - p.2)) * (B p.2 * r ^ p.2)
          = A (p.1 - p.2) * B p.2 * r ^ p.1
      rw [mul_mul_mul_comm, ← zpow_add₀ (ne_of_gt hr), sub_add_cancel]
    have hfib : ∀ ℓ : ℤ, HasSum (fun m : ℤ => A (ℓ - m) * B m * r ^ ℓ)
        (TateCurvesTheta.rconv A B ℓ * r ^ ℓ) := fun ℓ =>
      ((summable_rconv_slice hA hB ℓ).hasSum.mul_right (r ^ ℓ))
    exact (hshear.hasSum.prod_fiberwise hfib).summable

/-- Entire bound families are closed under index shifts. -/
lemma EntireBound.shift {A : ℤ → ℝ} (hA : EntireBound A) (d : ℤ) :
    EntireBound fun m => A (m - d) := by
  constructor
  · intro m; exact hA.nonneg _
  · intro r hr
    refine ((Equiv.addRight d).summable_iff (f := fun m : ℤ => A (m - d) * r ^ m)).mp ?_
    have hfun : ((fun m : ℤ => A (m - d) * r ^ m) ∘ (Equiv.addRight d))
        = fun m : ℤ => A m * r ^ m * r ^ d := by
      funext m
      simp only [Function.comp_apply, Equiv.coe_addRight, add_sub_cancel_right]
      rw [zpow_add₀ (ne_of_gt hr), mul_assoc]
    rw [hfun]
    exact (hA.summable r hr).mul_right _

/-- Entire bound families are closed under pointwise sums. -/
lemma EntireBound.add {A B : ℤ → ℝ} (hA : EntireBound A) (hB : EntireBound B) :
    EntireBound fun m => A m + B m := by
  constructor
  · intro m; exact add_nonneg (hA.nonneg m) (hB.nonneg m)
  · intro r hr
    exact ((hA.summable r hr).add (hB.summable r hr)).congr fun m => (add_mul _ _ _).symm

omit [CompleteSpace K] in
/-- **Domination of the Laurent convolution.** If `α, β` are termwise dominated by entire
bound families `A, B`, then `lconv α β` is termwise dominated by `rconv A B`. This is the
ultrametric `‖tsum‖ ≤ ⨆ ‖·‖` bound followed by `A (ℓ-m) · B m ≤ rconv A B ℓ`. -/
lemma norm_lconv_le {α β : ℤ → K} {A B : ℤ → ℝ} (hA : EntireBound A) (hB : EntireBound B)
    (hα : ∀ k, ‖α k‖ ≤ A k) (hβ : ∀ m, ‖β m‖ ≤ B m) (ℓ : ℤ) :
    ‖lconv α β ℓ‖ ≤ rconv A B ℓ := by
  refine (IsUltrametricDist.norm_tsum_le _).trans (ciSup_le fun m => ?_)
  have h1 : ‖α (ℓ - m) * β m‖ ≤ A (ℓ - m) * B m := by
    rw [norm_mul]
    exact mul_le_mul (hα _) (hβ _) (norm_nonneg _) ((norm_nonneg _).trans (hα _))
  exact h1.trans ((summable_rconv_slice hA hB ℓ).le_tsum m
    fun j _ => mul_nonneg (hA.nonneg _) (hB.nonneg _))

/-- Geometric summability of `n ↦ c^|n|` over `ℤ` for `0 ≤ c < 1`. -/
private lemma summable_pow_natAbs {c : ℝ} (h0 : 0 ≤ c) (h1 : c < 1) :
    Summable fun n : ℤ => c ^ n.natAbs := by
  apply Summable.of_nat_of_neg_add_one
  · exact (summable_geometric_of_lt_one h0 h1).congr fun k => by
      simp [Int.natAbs_natCast]
  · refine ((summable_geometric_of_lt_one h0 h1).mul_right c).congr fun k => ?_
    have hk : ((-(↑k + 1) : ℤ)).natAbs = k + 1 := by omega
    rw [hk, pow_succ]

omit [CompleteSpace K] in
/-- Extend a `ℕ`-supported `HasSum` to `ℤ` (vanishing on negative indices). -/
private lemma hasSum_int_nonneg_support {f : ℤ → K} {S : K}
    (h0 : ∀ n : ℤ, n < 0 → f n = 0) (h : HasSum (fun k : ℕ => f (k : ℤ)) S) :
    HasSum f S := by
  have hneg : HasSum (fun k : ℕ => f (-((k : ℤ) + 1))) 0 := by
    have hz : (fun k : ℕ => f (-((k : ℤ) + 1))) = fun _ => (0 : K) :=
      funext fun k => h0 _ (by omega)
    rw [hz]
    exact hasSum_zero
  simpa using h.of_nat_of_neg_add_one hneg

omit [CompleteSpace K] in
/-- Extend a `(-ℕ)`-supported `HasSum` to `ℤ` (vanishing on positive indices). -/
private lemma hasSum_int_nonpos_support {f : ℤ → K} {S : K}
    (h0 : ∀ n : ℤ, 0 < n → f n = 0) (h : HasSum (fun k : ℕ => f (-(k : ℤ))) S) :
    HasSum f S := by
  have hflip : HasSum (fun n : ℤ => f (-n)) S :=
    hasSum_int_nonneg_support (fun n hn => h0 _ (by omega)) (by simpa using h)
  exact (Equiv.neg ℤ).hasSum_iff.mp hflip

/-- Shifting a global Laurent series: if `∑ₘ f m · uᵐ = S` then
`∑ₘ f (m - d) · uᵐ = S · u^d`. -/
private lemma hasSum_mul_zpow_shift {K : Type*} [NormedField K] (u : Kˣ) (d : ℤ)
    {f : ℤ → K} {S : K} (h : HasSum (fun m : ℤ => f m * (u : K) ^ m) S) :
    HasSum (fun m : ℤ => f (m - d) * (u : K) ^ m) (S * (u : K) ^ d) := by
  refine ((Equiv.addRight d).hasSum_iff).mp ?_
  have hfun : ((fun m : ℤ => f (m - d) * (u : K) ^ m) ∘ (Equiv.addRight d))
      = fun m : ℤ => f m * (u : K) ^ m * (u : K) ^ d := by
    funext m
    simp only [Function.comp_apply, Equiv.coe_addRight, add_sub_cancel_right]
    rw [zpow_add₀ u.ne_zero, mul_assoc]
  rw [hfun]
  exact h.mul_right _

end Convolution

/-! ### Triangular-exponent arithmetic -/

private lemma triangle_succ (k : ℕ) : (k + 1) * (k + 1 - 1) / 2 = k * (k - 1) / 2 + k := by
  rw [← Finset.sum_range_id k, ← Finset.sum_range_id (k + 1), Finset.sum_range_succ]

private lemma two_mul_triangle (k : ℕ) : 2 * (k * (k - 1) / 2) = k * (k - 1) := by
  cases k with
  | zero => rfl
  | succ j =>
    have h : (2 : ℕ) ∣ (j + 1) * (j + 1 - 1) := by
      simpa [mul_comm] using (Nat.even_mul_succ_self j).two_dvd
    exact Nat.mul_div_cancel' h

/-- The triangular number of `|m|` is at most the theta exponent `e m = m(m+1)/2`. -/
private lemma triangle_natAbs_le_thetaExp (m : ℤ) :
    ((m.natAbs * (m.natAbs - 1) / 2 : ℕ) : ℤ) ≤ thetaExp m := by
  have h2 : (2 : ℤ) * ((m.natAbs * (m.natAbs - 1) / 2 : ℕ) : ℤ)
      = (m.natAbs : ℤ) * (m.natAbs : ℤ) - (m.natAbs : ℤ) := by
    rcases Nat.eq_zero_or_pos m.natAbs with h | h
    · rw [h]; simp
    · have hcast : ((m.natAbs * (m.natAbs - 1) : ℕ) : ℤ)
          = (m.natAbs : ℤ) * (m.natAbs : ℤ) - (m.natAbs : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_sub h]
        ring
      calc (2 : ℤ) * ((m.natAbs * (m.natAbs - 1) / 2 : ℕ) : ℤ)
          = ((2 * (m.natAbs * (m.natAbs - 1) / 2) : ℕ) : ℤ) := by push_cast; ring
        _ = ((m.natAbs * (m.natAbs - 1) : ℕ) : ℤ) := by
            exact_mod_cast congrArg (Nat.cast (R := ℤ)) (two_mul_triangle m.natAbs)
        _ = _ := hcast
  have h3 : 2 * thetaExp m = m * (m + 1) := two_mul_thetaExp m
  have h4 : (m.natAbs : ℤ) * (m.natAbs : ℤ) = m * m := by
    rw [← Int.natCast_mul]
    exact Int.natAbs_mul_self
  have h5 : -(m.natAbs : ℤ) ≤ m := by omega
  nlinarith [h2, h3, h4, h5]

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-! ### The punctured Euler factor series -/

/-- The coefficients of the **punctured Euler product** `∏_{j ≥ 0, j ≠ p} (1 + qʲ · c)` as a
power series in `c`. The recursion peels the `j = 0` factor: the puncture `p = 0` leaves
`∏_{j≥1}(1+qʲc) = thetaProdFactor (q·c)`, with coefficients `E k · qᵏ`; for `p + 1` the
factor `(1 + c)` multiplies the `p`-punctured series evaluated at `q·c`, giving
`pFactorCoeff (p+1) (k+1) = q^{k+1}·pFactorCoeff p (k+1) + qᵏ·pFactorCoeff p k`. -/
noncomputable def pFactorCoeff : ℕ → ℕ → K
  | 0, k => factorCoeff t k * (t.q : K) ^ k
  | p + 1, 0 => pFactorCoeff p 0
  | p + 1, k + 1 =>
      (t.q : K) ^ (k + 1) * pFactorCoeff p (k + 1) + (t.q : K) ^ k * pFactorCoeff p k

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma pFactorCoeff_zero (k : ℕ) : t.pFactorCoeff 0 k = factorCoeff t k * (t.q : K) ^ k := by
  simp [pFactorCoeff]

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma pFactorCoeff_succ_zero (p : ℕ) : t.pFactorCoeff (p + 1) 0 = t.pFactorCoeff p 0 := by
  simp [pFactorCoeff]

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma pFactorCoeff_succ_succ (p k : ℕ) :
    t.pFactorCoeff (p + 1) (k + 1)
      = (t.q : K) ^ (k + 1) * t.pFactorCoeff p (k + 1) + (t.q : K) ^ k * t.pFactorCoeff p k := by
  simp [pFactorCoeff]

omit [CompleteSpace K] in
/-- **Uniform norm bound for the punctured coefficients**: `‖pFactorCoeff p k‖ ≤ ‖q‖^{k(k-1)/2}`,
independently of the puncture `p`. -/
lemma norm_pFactorCoeff_le (p k : ℕ) :
    ‖t.pFactorCoeff p k‖ ≤ ‖(t.q : K)‖ ^ (k * (k - 1) / 2) := by
  induction p generalizing k with
  | zero =>
    rw [pFactorCoeff_zero, norm_mul, norm_pow, t.norm_factorCoeff k]
    exact mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le)
  | succ p ih =>
    cases k with
    | zero => simpa [pFactorCoeff_succ_zero] using ih 0
    | succ k =>
      rw [pFactorCoeff_succ_succ]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul, norm_pow]
        exact mul_le_of_le_one_left (by positivity)
          (pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le) |>.trans'
          (mul_le_mul_of_nonneg_left (ih (k + 1)) (by positivity))
      · rw [norm_mul, norm_pow]
        calc ‖(t.q : K)‖ ^ k * ‖t.pFactorCoeff p k‖
            ≤ ‖(t.q : K)‖ ^ k * ‖(t.q : K)‖ ^ (k * (k - 1) / 2) :=
              mul_le_mul_of_nonneg_left (ih k) (by positivity)
          _ = ‖(t.q : K)‖ ^ ((k + 1) * (k + 1 - 1) / 2) := by
              rw [← pow_add, triangle_succ, Nat.add_comm]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The master real series: `∑ₖ ‖q‖^{k(k-1)/2} · rᵏ` converges for every `r ≥ 0`. -/
private lemma summable_norm_q_triangle_mul (r : ℝ) (hr : 0 ≤ r) :
    Summable fun k : ℕ => ‖(t.q : K)‖ ^ (k * (k - 1) / 2) * r ^ k := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  have htend : Tendsto (fun k : ℕ => ‖(t.q : K)‖ ^ k * r) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) t.norm_lt_one).mul_const r
  filter_upwards [htend.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num)] with k hk
  have key : ‖(t.q : K)‖ ^ ((k + 1) * (k + 1 - 1) / 2) * r ^ (k + 1)
      = (‖(t.q : K)‖ ^ k * r) * (‖(t.q : K)‖ ^ (k * (k - 1) / 2) * r ^ k) := by
    rw [triangle_succ, pow_add, pow_succ]
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (by positivity), key]
  exact mul_le_mul_of_nonneg_right hk (by positivity)

/-- The punctured factor series `∑ₖ pFactorCoeff p k · cᵏ` converges for every `c : K`. -/
lemma summable_pFactorCoeff_mul_pow (p : ℕ) (c : K) :
    Summable fun k : ℕ => t.pFactorCoeff p k * c ^ k := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hb : Tendsto (fun k : ℕ => ‖(t.q : K)‖ ^ (k * (k - 1) / 2) * ‖c‖ ^ k) atTop (𝓝 0) :=
    (t.summable_norm_q_triangle_mul ‖c‖ (norm_nonneg c)).tendsto_atTop_zero
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hb
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (t.norm_pFactorCoeff_le p k) (by positivity)

/-- The punctured factor series `S_p(c) = ∑ₖ pFactorCoeff p k · cᵏ`, the power-series form of
the punctured Euler product `∏_{j≠p}(1 + qʲc)`. -/
noncomputable def pFactorSeries (p : ℕ) (c : K) : K := ∑' k : ℕ, t.pFactorCoeff p k * c ^ k

/-- Peeling the `j = 0` factor of the punctured product:
`S_{p+1}(c) = (1 + c) · S_p(q·c)`. -/
lemma pFactorSeries_succ (p : ℕ) (c : K) :
    t.pFactorSeries (p + 1) c = (1 + c) * t.pFactorSeries p ((t.q : K) * c) := by
  have hg := t.summable_pFactorCoeff_mul_pow p ((t.q : K) * c)
  have hd : Summable (fun k : ℕ =>
      t.pFactorCoeff (p + 1) k * c ^ k - t.pFactorCoeff p k * ((t.q : K) * c) ^ k) :=
    (t.summable_pFactorCoeff_mul_pow (p + 1) c).sub hg
  have hsplit : ∀ k : ℕ, t.pFactorCoeff (p + 1) k * c ^ k
      = t.pFactorCoeff p k * ((t.q : K) * c) ^ k
        + (t.pFactorCoeff (p + 1) k * c ^ k - t.pFactorCoeff p k * ((t.q : K) * c) ^ k) :=
    fun k => by ring
  rw [pFactorSeries, pFactorSeries, tsum_congr hsplit, Summable.tsum_add hg hd, add_mul, one_mul]
  congr 1
  rw [hd.tsum_eq_zero_add]
  simp only [pow_zero, mul_one, pFactorCoeff_succ_zero, sub_self, zero_add]
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [pFactorCoeff_succ_succ, mul_pow, mul_pow]
  ring

/-- **The defining identity of the punctured factor series.** Restoring the removed factor
recovers the elementary theta factor: `(1 + q^p·c) · S_p(c) = thetaProdFactor c`. Division
never occurs: the identity is proved by induction on the puncture from the shift relation
`thetaProdFactor c = (1 + c)·thetaProdFactor (q·c)`. -/
lemma one_add_qpow_mul_pFactorSeries (p : ℕ) (c : K) :
    (1 + (t.q : K) ^ p * c) * t.pFactorSeries p c = t.thetaProdFactor c := by
  induction p generalizing c with
  | zero =>
    have h0 : t.pFactorSeries 0 c = ∑' k : ℕ, factorCoeff t k * ((t.q : K) * c) ^ k := by
      refine tsum_congr fun k => ?_
      rw [pFactorCoeff_zero, mul_pow]
      ring
    rw [pow_zero, one_mul, h0, ← thetaProdFactor_eq_tsum, ← thetaProdFactor_eq]
  | succ p ih =>
    rw [pFactorSeries_succ]
    have hswap : (1 + (t.q : K) ^ (p + 1) * c) * ((1 + c) * t.pFactorSeries p ((t.q : K) * c))
        = (1 + c)
          * ((1 + (t.q : K) ^ p * ((t.q : K) * c)) * t.pFactorSeries p ((t.q : K) * c)) := by
      ring
    rw [hswap, ih ((t.q : K) * c), ← thetaProdFactor_eq]

/-! ### Base coefficient families and their bounds -/

/-- The triangular bound family `m ↦ ‖q‖^{|m|(|m|-1)/2}`, the master entire majorant of all
coefficient families in this file. -/
private def triangleBound : ℤ → ℝ := fun m => ‖(t.q : K)‖ ^ (m.natAbs * (m.natAbs - 1) / 2)

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma entireBound_triangleBound : EntireBound t.triangleBound := by
  constructor
  · intro m
    exact pow_nonneg (norm_nonneg _) _
  · intro r hr
    apply Summable.of_nat_of_neg_add_one
    · exact (t.summable_norm_q_triangle_mul r hr.le).congr fun k => by
        simp [triangleBound, Int.natAbs_natCast, zpow_natCast]
    · have h := t.summable_norm_q_triangle_mul r⁻¹ (by positivity)
      have h1 : Summable (fun k : ℕ =>
          ‖(t.q : K)‖ ^ ((k + 1) * (k + 1 - 1) / 2) * r⁻¹ ^ (k + 1)) :=
        (summable_nat_add_iff 1).mpr h
      refine h1.congr fun k => ?_
      have hk : ((-(↑k + 1) : ℤ)).natAbs = k + 1 := by omega
      have hz : r ^ (-(↑k + 1) : ℤ) = r⁻¹ ^ (k + 1) := by
        rw [zpow_neg, ← inv_zpow, show ((↑k + 1 : ℤ)) = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
          zpow_natCast]
      rw [triangleBound, hk, hz]

/-- The coefficient family of `Θ(u) = theta (-u)`: `m ↦ (-1)ᵐ · q^{e m}`. -/
private def thetaNegCoeff : ℤ → K := fun m => (-1 : K) ^ m * (t.q : K) ^ thetaExp m

private lemma hasSum_thetaNegCoeff (u : Kˣ) :
    HasSum (fun m : ℤ => t.thetaNegCoeff m * (u : K) ^ m) (t.theta (-u)) := by
  have h : HasSum (fun n : ℤ => t.thetaTerm (-u) n) (t.theta (-u)) :=
    (t.thetaTerm_summable (-u)).hasSum
  have hfun : (fun n : ℤ => t.thetaTerm (-u) n)
      = fun m : ℤ => t.thetaNegCoeff m * (u : K) ^ m := by
    funext n
    rw [thetaTerm, thetaNegCoeff, Units.val_neg, show -(u : K) = (-1 : K) * (u : K) by ring,
      mul_zpow]
    ring
  rwa [hfun] at h

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma norm_thetaNegCoeff_le (m : ℤ) : ‖t.thetaNegCoeff m‖ ≤ t.triangleBound m := by
  rw [thetaNegCoeff, norm_mul, norm_zpow, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
  have he : (0 : ℤ) ≤ thetaExp m := thetaExp_nonneg m
  rw [show ‖(t.q : K)‖ ^ thetaExp m = ‖(t.q : K)‖ ^ (thetaExp m).toNat by
    rw [← zpow_natCast, Int.toNat_of_nonneg he]]
  refine pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le ?_
  have := triangle_natAbs_le_thetaExp m
  omega

/-- The coefficient family of `H(u) = thetaProdFactor (-(q·u)) = ∏(1 - q^{j+1}u)`,
supported on `k ≥ 0`. -/
private def hFam : ℤ → K := fun k =>
  if 0 ≤ k then factorCoeff t k.natAbs * (-(t.q : K)) ^ k.natAbs else 0

/-- The coefficient family of `G(u) = thetaProdFactor (-u⁻¹) = ∏(1 - qʲu⁻¹)`,
supported on `m ≤ 0`. -/
private def gFam : ℤ → K := fun m =>
  if m ≤ 0 then factorCoeff t m.natAbs * (-1 : K) ^ m.natAbs else 0

/-- The coefficient family of the punctured series `A_p(u) = S_p(-(q·u))`, supported on
`k ≥ 0`. -/
private def aFam (p : ℕ) : ℤ → K := fun k =>
  if 0 ≤ k then t.pFactorCoeff p k.natAbs * (-(t.q : K)) ^ k.natAbs else 0

/-- The coefficient family of the punctured series `B_p(u) = S_p(-u⁻¹)`, supported on
`m ≤ 0`. -/
private def bFam (p : ℕ) : ℤ → K := fun m =>
  if m ≤ 0 then t.pFactorCoeff p m.natAbs * (-1 : K) ^ m.natAbs else 0

private lemma hasSum_hFam (u : Kˣ) :
    HasSum (fun k : ℤ => t.hFam k * (u : K) ^ k)
      (t.thetaProdFactor (-((t.q : K) * (u : K)))) := by
  apply hasSum_int_nonneg_support (fun n hn => by simp [hFam, not_le.mpr hn])
  have hfun : ∀ k : ℕ, t.hFam (k : ℤ) * (u : K) ^ (k : ℤ)
      = factorCoeff t k * (-((t.q : K) * (u : K))) ^ k := by
    intro k
    simp only [hFam, Int.natAbs_natCast, if_pos (Int.natCast_nonneg k), zpow_natCast]
    rw [mul_assoc, ← mul_pow, neg_mul]
  rw [funext hfun, thetaProdFactor_eq_tsum]
  exact (t.factorCoeff_summable _).hasSum

private lemma hasSum_gFam (u : Kˣ) :
    HasSum (fun m : ℤ => t.gFam m * (u : K) ^ m) (t.thetaProdFactor (-((u : K))⁻¹)) := by
  apply hasSum_int_nonpos_support (fun n hn => by simp [gFam, not_le.mpr hn])
  have hfun : ∀ k : ℕ, t.gFam (-(k : ℤ)) * (u : K) ^ (-(k : ℤ))
      = factorCoeff t k * (-((u : K))⁻¹) ^ k := by
    intro k
    simp only [gFam, Int.natAbs_neg, Int.natAbs_natCast, if_pos (neg_nonpos.mpr
      (Int.natCast_nonneg k)), zpow_neg, zpow_natCast, ← inv_pow]
    rw [mul_assoc, ← mul_pow, neg_one_mul]
  rw [funext hfun, thetaProdFactor_eq_tsum]
  exact (t.factorCoeff_summable _).hasSum

private lemma hasSum_aFam (p : ℕ) (u : Kˣ) :
    HasSum (fun k : ℤ => t.aFam p k * (u : K) ^ k)
      (t.pFactorSeries p (-((t.q : K) * (u : K)))) := by
  apply hasSum_int_nonneg_support (fun n hn => by simp [aFam, not_le.mpr hn])
  have hfun : ∀ k : ℕ, t.aFam p (k : ℤ) * (u : K) ^ (k : ℤ)
      = t.pFactorCoeff p k * (-((t.q : K) * (u : K))) ^ k := by
    intro k
    simp only [aFam, Int.natAbs_natCast, if_pos (Int.natCast_nonneg k), zpow_natCast]
    rw [mul_assoc, ← mul_pow, neg_mul]
  rw [funext hfun]
  exact (t.summable_pFactorCoeff_mul_pow p _).hasSum

private lemma hasSum_bFam (p : ℕ) (u : Kˣ) :
    HasSum (fun m : ℤ => t.bFam p m * (u : K) ^ m)
      (t.pFactorSeries p (-((u : K))⁻¹)) := by
  apply hasSum_int_nonpos_support (fun n hn => by simp [bFam, not_le.mpr hn])
  have hfun : ∀ k : ℕ, t.bFam p (-(k : ℤ)) * (u : K) ^ (-(k : ℤ))
      = t.pFactorCoeff p k * (-((u : K))⁻¹) ^ k := by
    intro k
    simp only [bFam, Int.natAbs_neg, Int.natAbs_natCast, if_pos (neg_nonpos.mpr
      (Int.natCast_nonneg k)), zpow_neg, zpow_natCast, ← inv_pow]
    rw [mul_assoc, ← mul_pow, neg_one_mul]
  rw [funext hfun]
  exact (t.summable_pFactorCoeff_mul_pow p _).hasSum

omit [CompleteSpace K] in
private lemma norm_hFam_le (k : ℤ) : ‖t.hFam k‖ ≤ t.triangleBound k := by
  rw [hFam]
  split_ifs with hk
  · rw [norm_mul, norm_pow, norm_neg, t.norm_factorCoeff, triangleBound]
    exact mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le)
  · rw [norm_zero, triangleBound]
    positivity

omit [CompleteSpace K] in
private lemma norm_gFam_le (m : ℤ) : ‖t.gFam m‖ ≤ t.triangleBound m := by
  rw [gFam]
  split_ifs with hm
  · rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, t.norm_factorCoeff,
      triangleBound]
  · rw [norm_zero, triangleBound]
    positivity

omit [CompleteSpace K] in
private lemma norm_aFam_le (p : ℕ) (k : ℤ) : ‖t.aFam p k‖ ≤ t.triangleBound k := by
  rw [aFam]
  split_ifs with hk
  · rw [norm_mul, norm_pow, norm_neg, triangleBound]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le) |>.trans (t.norm_pFactorCoeff_le p _)
  · rw [norm_zero, triangleBound]
    positivity

omit [CompleteSpace K] in
private lemma norm_bFam_le (p : ℕ) (m : ℤ) : ‖t.bFam p m‖ ≤ t.triangleBound m := by
  rw [bFam]
  split_ifs with hm
  · rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one, triangleBound]
    exact t.norm_pFactorCoeff_le p _
  · rw [norm_zero, triangleBound]
    positivity

/-- `‖thetaProdFactor (-q)‖ ≤ 1`. -/
private lemma norm_constFactor_le_one : ‖t.thetaProdFactor (-(t.q : K))‖ ≤ 1 := by
  rw [thetaProdFactor_eq_tsum]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun k => ?_
  rw [norm_mul, norm_pow, norm_neg, t.norm_factorCoeff]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le) (by positivity)
    (pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le)

/-- `theta (-u)` in factorized form `F₋q · H(u) · G(u)`. -/
private lemma theta_neg_eq (u : Kˣ) :
    t.theta (-u) = t.thetaProdFactor (-(t.q : K))
      * t.thetaProdFactor (-((t.q : K) * (u : K))) * t.thetaProdFactor (-((u : K))⁻¹) := by
  rw [t.theta_eq_thetaProd (-u), thetaProd_apply]
  simp only [Units.val_neg, mul_neg, inv_neg]

/-! ### The per-`n` convolution families -/

/-- The 4-fold convolution `A_p ⋆ A_p ⋆ G ⋆ G` for the positive-`n` terms of `X·Θ²`. -/
private def convXPos (p : ℕ) : ℤ → K :=
  lconv (lconv (t.aFam p) (t.aFam p)) (lconv t.gFam t.gFam)

/-- The 4-fold convolution `H ⋆ H ⋆ B_p ⋆ B_p` for the nonpositive-`n` terms of `X·Θ²`. -/
private def convXNeg (p : ℕ) : ℤ → K :=
  lconv (lconv t.hFam t.hFam) (lconv (t.bFam p) (t.bFam p))

/-- The 6-fold convolution `A_p ⋆ A_p ⋆ A_p ⋆ G ⋆ G ⋆ G` for the positive-`n` terms of
`Y·Θ³`. -/
private def convYPos (p : ℕ) : ℤ → K :=
  lconv (lconv (lconv (t.aFam p) (t.aFam p)) (t.aFam p))
    (lconv (lconv t.gFam t.gFam) t.gFam)

/-- The 6-fold convolution `H ⋆ H ⋆ H ⋆ B_p ⋆ B_p ⋆ B_p` for the nonpositive-`n` terms of
`Y·Θ³`. -/
private def convYNeg (p : ℕ) : ℤ → K :=
  lconv (lconv (lconv t.hFam t.hFam) t.hFam)
    (lconv (lconv (t.bFam p) (t.bFam p)) (t.bFam p))

private lemma hasSum_convXPos (p : ℕ) (u : Kˣ) :
    HasSum (fun ℓ : ℤ => t.convXPos p ℓ * (u : K) ^ ℓ)
      ((t.pFactorSeries p (-((t.q : K) * (u : K)))
          * t.pFactorSeries p (-((t.q : K) * (u : K))))
        * (t.thetaProdFactor (-((u : K))⁻¹) * t.thetaProdFactor (-((u : K))⁻¹))) := by
  have hA := t.hasSum_aFam p u
  have hG := t.hasSum_gFam u
  exact hasSum_laurentConvolution u (hasSum_laurentConvolution u hA hA)
    (hasSum_laurentConvolution u hG hG)

private lemma hasSum_convXNeg (p : ℕ) (u : Kˣ) :
    HasSum (fun ℓ : ℤ => t.convXNeg p ℓ * (u : K) ^ ℓ)
      ((t.thetaProdFactor (-((t.q : K) * (u : K)))
          * t.thetaProdFactor (-((t.q : K) * (u : K))))
        * (t.pFactorSeries p (-((u : K))⁻¹) * t.pFactorSeries p (-((u : K))⁻¹))) := by
  have hH := t.hasSum_hFam u
  have hB := t.hasSum_bFam p u
  exact hasSum_laurentConvolution u (hasSum_laurentConvolution u hH hH)
    (hasSum_laurentConvolution u hB hB)

private lemma hasSum_convYPos (p : ℕ) (u : Kˣ) :
    HasSum (fun ℓ : ℤ => t.convYPos p ℓ * (u : K) ^ ℓ)
      (((t.pFactorSeries p (-((t.q : K) * (u : K)))
            * t.pFactorSeries p (-((t.q : K) * (u : K))))
          * t.pFactorSeries p (-((t.q : K) * (u : K))))
        * ((t.thetaProdFactor (-((u : K))⁻¹) * t.thetaProdFactor (-((u : K))⁻¹))
          * t.thetaProdFactor (-((u : K))⁻¹))) := by
  have hA := t.hasSum_aFam p u
  have hG := t.hasSum_gFam u
  exact hasSum_laurentConvolution u
    (hasSum_laurentConvolution u (hasSum_laurentConvolution u hA hA) hA)
    (hasSum_laurentConvolution u (hasSum_laurentConvolution u hG hG) hG)

private lemma hasSum_convYNeg (p : ℕ) (u : Kˣ) :
    HasSum (fun ℓ : ℤ => t.convYNeg p ℓ * (u : K) ^ ℓ)
      (((t.thetaProdFactor (-((t.q : K) * (u : K)))
            * t.thetaProdFactor (-((t.q : K) * (u : K))))
          * t.thetaProdFactor (-((t.q : K) * (u : K))))
        * ((t.pFactorSeries p (-((u : K))⁻¹) * t.pFactorSeries p (-((u : K))⁻¹))
          * t.pFactorSeries p (-((u : K))⁻¹))) := by
  have hH := t.hasSum_hFam u
  have hB := t.hasSum_bFam p u
  exact hasSum_laurentConvolution u
    (hasSum_laurentConvolution u (hasSum_laurentConvolution u hH hH) hH)
    (hasSum_laurentConvolution u (hasSum_laurentConvolution u hB hB) hB)

/-! ### Entire bounds for the convolution families -/

private def bound2 : ℤ → ℝ := rconv t.triangleBound t.triangleBound
private def bound4 : ℤ → ℝ := rconv t.bound2 t.bound2
private def bound3 : ℤ → ℝ := rconv t.bound2 t.triangleBound
private def bound6 : ℤ → ℝ := rconv t.bound3 t.bound3

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma entireBound_bound2 : EntireBound t.bound2 :=
  t.entireBound_triangleBound.rconv t.entireBound_triangleBound

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma entireBound_bound4 : EntireBound t.bound4 :=
  t.entireBound_bound2.rconv t.entireBound_bound2

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma entireBound_bound3 : EntireBound t.bound3 :=
  t.entireBound_bound2.rconv t.entireBound_triangleBound

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma entireBound_bound6 : EntireBound t.bound6 :=
  t.entireBound_bound3.rconv t.entireBound_bound3

omit [CompleteSpace K] in
private lemma norm_convXPos_le (p : ℕ) (ℓ : ℤ) : ‖t.convXPos p ℓ‖ ≤ t.bound4 ℓ :=
  norm_lconv_le t.entireBound_bound2 t.entireBound_bound2
    (norm_lconv_le t.entireBound_triangleBound t.entireBound_triangleBound
      (t.norm_aFam_le p) (t.norm_aFam_le p))
    (norm_lconv_le t.entireBound_triangleBound t.entireBound_triangleBound
      t.norm_gFam_le t.norm_gFam_le) ℓ

omit [CompleteSpace K] in
private lemma norm_convXNeg_le (p : ℕ) (ℓ : ℤ) : ‖t.convXNeg p ℓ‖ ≤ t.bound4 ℓ :=
  norm_lconv_le t.entireBound_bound2 t.entireBound_bound2
    (norm_lconv_le t.entireBound_triangleBound t.entireBound_triangleBound
      t.norm_hFam_le t.norm_hFam_le)
    (norm_lconv_le t.entireBound_triangleBound t.entireBound_triangleBound
      (t.norm_bFam_le p) (t.norm_bFam_le p)) ℓ

omit [CompleteSpace K] in
private lemma norm_convYPos_le (p : ℕ) (ℓ : ℤ) : ‖t.convYPos p ℓ‖ ≤ t.bound6 ℓ :=
  norm_lconv_le t.entireBound_bound3 t.entireBound_bound3
    (norm_lconv_le t.entireBound_bound2 t.entireBound_triangleBound
      (norm_lconv_le t.entireBound_triangleBound t.entireBound_triangleBound
        (t.norm_aFam_le p) (t.norm_aFam_le p))
      (t.norm_aFam_le p))
    (norm_lconv_le t.entireBound_bound2 t.entireBound_triangleBound
      (norm_lconv_le t.entireBound_triangleBound t.entireBound_triangleBound
        t.norm_gFam_le t.norm_gFam_le)
      t.norm_gFam_le) ℓ

omit [CompleteSpace K] in
private lemma norm_convYNeg_le (p : ℕ) (ℓ : ℤ) : ‖t.convYNeg p ℓ‖ ≤ t.bound6 ℓ :=
  norm_lconv_le t.entireBound_bound3 t.entireBound_bound3
    (norm_lconv_le t.entireBound_bound2 t.entireBound_triangleBound
      (norm_lconv_le t.entireBound_triangleBound t.entireBound_triangleBound
        t.norm_hFam_le t.norm_hFam_le)
      t.norm_hFam_le)
    (norm_lconv_le t.entireBound_bound2 t.entireBound_triangleBound
      (norm_lconv_le t.entireBound_triangleBound t.entireBound_triangleBound
        (t.norm_bFam_le p) (t.norm_bFam_le p))
      (t.norm_bFam_le p)) ℓ

/-! ### The per-`n` coefficient families -/

/-- The coefficient family of the `n`-th term `Xterm u n · Θ(u)²`. -/
private def xFam (n : ℤ) : ℤ → K := fun m =>
  if 1 ≤ n then
    (t.q : K) ^ n * t.thetaProdFactor (-(t.q : K)) ^ 2 * t.convXPos (n - 1).toNat (m - 1)
  else
    (t.q : K) ^ (-n) * t.thetaProdFactor (-(t.q : K)) ^ 2 * t.convXNeg (-n).toNat (m + 1)

/-- The coefficient family of the `n`-th term `Yterm u n · Θ(u)³`. -/
private def yFam (n : ℤ) : ℤ → K := fun m =>
  if 1 ≤ n then
    ((t.q : K) ^ n) ^ 2 * t.thetaProdFactor (-(t.q : K)) ^ 3 * t.convYPos (n - 1).toNat (m - 2)
  else
    -((t.q : K) ^ (-n) * t.thetaProdFactor (-(t.q : K)) ^ 3 * t.convYNeg (-n).toNat (m + 1))

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma norm_qzpow_natAbs {n : ℤ} (hn : 0 ≤ n) :
    ‖(t.q : K) ^ n‖ = ‖(t.q : K)‖ ^ n.natAbs := by
  rw [norm_zpow, ← zpow_natCast ‖(t.q : K)‖ n.natAbs, Int.natAbs_of_nonneg hn]

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma norm_qzpow_le_one {n : ℤ} (hn : 0 ≤ n) : ‖(t.q : K) ^ n‖ ≤ 1 := by
  rw [t.norm_qzpow_natAbs hn]
  exact pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le

private lemma norm_xFam_le (n m : ℤ) :
    ‖t.xFam n m‖ ≤ ‖(t.q : K)‖ ^ n.natAbs * (t.bound4 (m - 1) + t.bound4 (m + 1)) := by
  have hb4 := t.entireBound_bound4.nonneg
  have hFq : ‖t.thetaProdFactor (-(t.q : K)) ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) t.norm_constFactor_le_one
  rw [xFam]
  split_ifs with hn
  · rw [norm_mul, norm_mul]
    calc ‖(t.q : K) ^ n‖ * ‖t.thetaProdFactor (-(t.q : K)) ^ 2‖ * ‖t.convXPos (n - 1).toNat (m - 1)‖
        ≤ ‖(t.q : K)‖ ^ n.natAbs * 1 * t.bound4 (m - 1) := by
          refine mul_le_mul (mul_le_mul (le_of_eq (t.norm_qzpow_natAbs (by omega))) hFq
            (norm_nonneg _) (by positivity)) (t.norm_convXPos_le _ _) (norm_nonneg _)
            (by positivity)
      _ ≤ ‖(t.q : K)‖ ^ n.natAbs * (t.bound4 (m - 1) + t.bound4 (m + 1)) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hb4 _)) (by positivity)
  · rw [norm_mul, norm_mul]
    have habs : (-n).natAbs = n.natAbs := Int.natAbs_neg n
    calc ‖(t.q : K) ^ (-n)‖ * ‖t.thetaProdFactor (-(t.q : K)) ^ 2‖
          * ‖t.convXNeg (-n).toNat (m + 1)‖
        ≤ ‖(t.q : K)‖ ^ n.natAbs * 1 * t.bound4 (m + 1) := by
          refine mul_le_mul (mul_le_mul ?_ hFq (norm_nonneg _) (by positivity))
            (t.norm_convXNeg_le _ _) (norm_nonneg _) (by positivity)
          rw [t.norm_qzpow_natAbs (by omega), habs]
      _ ≤ ‖(t.q : K)‖ ^ n.natAbs * (t.bound4 (m - 1) + t.bound4 (m + 1)) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hb4 _)) (by positivity)

private lemma norm_yFam_le (n m : ℤ) :
    ‖t.yFam n m‖ ≤ ‖(t.q : K)‖ ^ n.natAbs * (t.bound6 (m - 2) + t.bound6 (m + 1)) := by
  have hb6 := t.entireBound_bound6.nonneg
  have hFq : ‖t.thetaProdFactor (-(t.q : K)) ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) t.norm_constFactor_le_one
  rw [yFam]
  split_ifs with hn
  · rw [norm_mul, norm_mul]
    have hq2 : ‖((t.q : K) ^ n) ^ 2‖ ≤ ‖(t.q : K)‖ ^ n.natAbs := by
      rw [norm_pow, sq]
      calc ‖(t.q : K) ^ n‖ * ‖(t.q : K) ^ n‖
          ≤ ‖(t.q : K) ^ n‖ * 1 :=
            mul_le_mul_of_nonneg_left (t.norm_qzpow_le_one (by omega)) (norm_nonneg _)
        _ = ‖(t.q : K)‖ ^ n.natAbs := by rw [mul_one, t.norm_qzpow_natAbs (by omega)]
    calc ‖((t.q : K) ^ n) ^ 2‖ * ‖t.thetaProdFactor (-(t.q : K)) ^ 3‖
          * ‖t.convYPos (n - 1).toNat (m - 2)‖
        ≤ ‖(t.q : K)‖ ^ n.natAbs * 1 * t.bound6 (m - 2) :=
          mul_le_mul (mul_le_mul hq2 hFq (norm_nonneg _) (by positivity))
            (t.norm_convYPos_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ ‖(t.q : K)‖ ^ n.natAbs * (t.bound6 (m - 2) + t.bound6 (m + 1)) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hb6 _)) (by positivity)
  · rw [norm_neg, norm_mul, norm_mul]
    have habs : (-n).natAbs = n.natAbs := Int.natAbs_neg n
    calc ‖(t.q : K) ^ (-n)‖ * ‖t.thetaProdFactor (-(t.q : K)) ^ 3‖
          * ‖t.convYNeg (-n).toNat (m + 1)‖
        ≤ ‖(t.q : K)‖ ^ n.natAbs * 1 * t.bound6 (m + 1) := by
          refine mul_le_mul (mul_le_mul ?_ hFq (norm_nonneg _) (by positivity))
            (t.norm_convYNeg_le _ _) (norm_nonneg _) (by positivity)
          rw [t.norm_qzpow_natAbs (by omega), habs]
      _ ≤ ‖(t.q : K)‖ ^ n.natAbs * (t.bound6 (m - 2) + t.bound6 (m + 1)) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hb6 _)) (by positivity)

/-! ### Per-`n` Laurent expansions -/

private lemma hasSum_xFam_pos (p : ℕ) (u : Kˣ) :
    HasSum (fun m : ℤ =>
        ((t.q : K) ^ (p + 1) * t.thetaProdFactor (-(t.q : K)) ^ 2
          * t.convXPos p (m - 1)) * (u : K) ^ m)
      ((t.q : K) ^ (p + 1) * (u : K)
        * (t.thetaProdFactor (-(t.q : K)) * t.pFactorSeries p (-((t.q : K) * (u : K)))
            * t.thetaProdFactor (-((u : K))⁻¹)) ^ 2) := by
  have h4 := t.hasSum_convXPos p u
  have h5 := hasSum_mul_zpow_shift u 1 h4
  have h6 := h5.mul_left ((t.q : K) ^ (p + 1) * t.thetaProdFactor (-(t.q : K)) ^ 2)
  have hfun : (fun m : ℤ => (t.q : K) ^ (p + 1) * t.thetaProdFactor (-(t.q : K)) ^ 2
      * (t.convXPos p (m - 1) * (u : K) ^ m))
      = fun m : ℤ => ((t.q : K) ^ (p + 1) * t.thetaProdFactor (-(t.q : K)) ^ 2
          * t.convXPos p (m - 1)) * (u : K) ^ m := by
    funext m
    ring
  rw [hfun] at h6
  have hval : (t.q : K) ^ (p + 1) * t.thetaProdFactor (-(t.q : K)) ^ 2
      * ((t.pFactorSeries p (-((t.q : K) * (u : K)))
            * t.pFactorSeries p (-((t.q : K) * (u : K))))
          * (t.thetaProdFactor (-((u : K))⁻¹) * t.thetaProdFactor (-((u : K))⁻¹))
        * (u : K) ^ (1 : ℤ))
      = (t.q : K) ^ (p + 1) * (u : K)
        * (t.thetaProdFactor (-(t.q : K)) * t.pFactorSeries p (-((t.q : K) * (u : K)))
            * t.thetaProdFactor (-((u : K))⁻¹)) ^ 2 := by
    rw [zpow_one]
    ring
  rwa [hval] at h6

private lemma hasSum_xFam_neg (p : ℕ) (u : Kˣ) :
    HasSum (fun m : ℤ =>
        ((t.q : K) ^ (p : ℕ) * t.thetaProdFactor (-(t.q : K)) ^ 2
          * t.convXNeg p (m + 1)) * (u : K) ^ m)
      ((t.q : K) ^ (p : ℕ) * ((u : K))⁻¹
        * (t.thetaProdFactor (-(t.q : K)) * t.thetaProdFactor (-((t.q : K) * (u : K)))
            * t.pFactorSeries p (-((u : K))⁻¹)) ^ 2) := by
  have h4 := t.hasSum_convXNeg p u
  have h5 := hasSum_mul_zpow_shift u (-1) h4
  have h6 := h5.mul_left ((t.q : K) ^ (p : ℕ) * t.thetaProdFactor (-(t.q : K)) ^ 2)
  have hfun : (fun m : ℤ => (t.q : K) ^ (p : ℕ) * t.thetaProdFactor (-(t.q : K)) ^ 2
      * (t.convXNeg p (m - (-1)) * (u : K) ^ m))
      = fun m : ℤ => ((t.q : K) ^ (p : ℕ) * t.thetaProdFactor (-(t.q : K)) ^ 2
          * t.convXNeg p (m + 1)) * (u : K) ^ m := by
    funext m
    rw [sub_neg_eq_add]
    ring
  rw [hfun] at h6
  have hval : (t.q : K) ^ (p : ℕ) * t.thetaProdFactor (-(t.q : K)) ^ 2
      * ((t.thetaProdFactor (-((t.q : K) * (u : K)))
            * t.thetaProdFactor (-((t.q : K) * (u : K))))
          * (t.pFactorSeries p (-((u : K))⁻¹) * t.pFactorSeries p (-((u : K))⁻¹))
        * (u : K) ^ (-1 : ℤ))
      = (t.q : K) ^ (p : ℕ) * ((u : K))⁻¹
        * (t.thetaProdFactor (-(t.q : K)) * t.thetaProdFactor (-((t.q : K) * (u : K)))
            * t.pFactorSeries p (-((u : K))⁻¹)) ^ 2 := by
    rw [zpow_neg_one]
    ring
  rwa [hval] at h6

private lemma hasSum_yFam_pos (p : ℕ) (u : Kˣ) :
    HasSum (fun m : ℤ =>
        (((t.q : K) ^ (p + 1)) ^ 2 * t.thetaProdFactor (-(t.q : K)) ^ 3
          * t.convYPos p (m - 2)) * (u : K) ^ m)
      (((t.q : K) ^ (p + 1)) ^ 2 * (u : K) ^ 2
        * (t.thetaProdFactor (-(t.q : K)) * t.pFactorSeries p (-((t.q : K) * (u : K)))
            * t.thetaProdFactor (-((u : K))⁻¹)) ^ 3) := by
  have h6 := t.hasSum_convYPos p u
  have h7 := hasSum_mul_zpow_shift u 2 h6
  have h8 := h7.mul_left (((t.q : K) ^ (p + 1)) ^ 2 * t.thetaProdFactor (-(t.q : K)) ^ 3)
  have hfun : (fun m : ℤ => ((t.q : K) ^ (p + 1)) ^ 2 * t.thetaProdFactor (-(t.q : K)) ^ 3
      * (t.convYPos p (m - 2) * (u : K) ^ m))
      = fun m : ℤ => (((t.q : K) ^ (p + 1)) ^ 2 * t.thetaProdFactor (-(t.q : K)) ^ 3
          * t.convYPos p (m - 2)) * (u : K) ^ m := by
    funext m
    ring
  rw [hfun] at h8
  have hz2 : ((u : K)) ^ (2 : ℤ) = (u : K) ^ 2 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
  have hval : ((t.q : K) ^ (p + 1)) ^ 2 * t.thetaProdFactor (-(t.q : K)) ^ 3
      * (((t.pFactorSeries p (-((t.q : K) * (u : K)))
              * t.pFactorSeries p (-((t.q : K) * (u : K))))
            * t.pFactorSeries p (-((t.q : K) * (u : K))))
          * ((t.thetaProdFactor (-((u : K))⁻¹) * t.thetaProdFactor (-((u : K))⁻¹))
            * t.thetaProdFactor (-((u : K))⁻¹))
        * (u : K) ^ (2 : ℤ))
      = ((t.q : K) ^ (p + 1)) ^ 2 * (u : K) ^ 2
        * (t.thetaProdFactor (-(t.q : K)) * t.pFactorSeries p (-((t.q : K) * (u : K)))
            * t.thetaProdFactor (-((u : K))⁻¹)) ^ 3 := by
    rw [hz2]
    ring
  rwa [hval] at h8

private lemma hasSum_yFam_neg (p : ℕ) (u : Kˣ) :
    HasSum (fun m : ℤ =>
        (-((t.q : K) ^ (p : ℕ) * t.thetaProdFactor (-(t.q : K)) ^ 3
          * t.convYNeg p (m + 1))) * (u : K) ^ m)
      (-((t.q : K) ^ (p : ℕ) * ((u : K))⁻¹
        * (t.thetaProdFactor (-(t.q : K)) * t.thetaProdFactor (-((t.q : K) * (u : K)))
            * t.pFactorSeries p (-((u : K))⁻¹)) ^ 3)) := by
  have h6 := t.hasSum_convYNeg p u
  have h7 := hasSum_mul_zpow_shift u (-1) h6
  have h8 := h7.mul_left (-((t.q : K) ^ (p : ℕ) * t.thetaProdFactor (-(t.q : K)) ^ 3))
  have hfun : (fun m : ℤ => -((t.q : K) ^ (p : ℕ) * t.thetaProdFactor (-(t.q : K)) ^ 3)
      * (t.convYNeg p (m - (-1)) * (u : K) ^ m))
      = fun m : ℤ => (-((t.q : K) ^ (p : ℕ) * t.thetaProdFactor (-(t.q : K)) ^ 3
          * t.convYNeg p (m + 1))) * (u : K) ^ m := by
    funext m
    rw [sub_neg_eq_add]
    ring
  rw [hfun] at h8
  have hval : -((t.q : K) ^ (p : ℕ) * t.thetaProdFactor (-(t.q : K)) ^ 3)
      * (((t.thetaProdFactor (-((t.q : K) * (u : K)))
              * t.thetaProdFactor (-((t.q : K) * (u : K))))
            * t.thetaProdFactor (-((t.q : K) * (u : K))))
          * ((t.pFactorSeries p (-((u : K))⁻¹) * t.pFactorSeries p (-((u : K))⁻¹))
            * t.pFactorSeries p (-((u : K))⁻¹))
        * (u : K) ^ (-1 : ℤ))
      = -((t.q : K) ^ (p : ℕ) * ((u : K))⁻¹
        * (t.thetaProdFactor (-(t.q : K)) * t.thetaProdFactor (-((t.q : K) * (u : K)))
            * t.pFactorSeries p (-((u : K))⁻¹)) ^ 3) := by
    rw [zpow_neg_one]
    ring
  rwa [hval] at h8

/-! ### The pointwise per-`n` identities off the orbit -/

private lemma Xterm_mul_theta_neg_sq_pos (u : Kˣ)
    (hu : ∀ j : ℤ, (t.q : K) ^ j * (u : K) ≠ 1) {n : ℤ} {p : ℕ} (hp : (p : ℤ) + 1 = n) :
    t.Xterm u n * t.theta (-u) ^ 2
      = (t.q : K) ^ (p + 1) * (u : K)
        * (t.thetaProdFactor (-(t.q : K)) * t.pFactorSeries p (-((t.q : K) * (u : K)))
            * t.thetaProdFactor (-((u : K))⁻¹)) ^ 2 := by
  have hθ := t.theta_neg_eq u
  have hH := t.one_add_qpow_mul_pFactorSeries p (-((t.q : K) * (u : K)))
  have hfac : (1 : K) + (t.q : K) ^ p * (-((t.q : K) * (u : K)))
      = 1 - (t.q : K) ^ (p + 1) * (u : K) := by
    rw [pow_succ]
    ring
  rw [hfac] at hH
  have hqn : (t.q : K) ^ n = (t.q : K) ^ (p + 1) := by
    rw [← hp, show ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hne : (1 : K) - (t.q : K) ^ (p + 1) * (u : K) ≠ 0 := by
    rw [← hqn]
    exact t.one_sub_qzpow_mul_ne_zero hu n
  rw [Xterm_apply, hθ, ← hH, hqn]
  field_simp

private lemma Xterm_mul_theta_neg_sq_neg (u : Kˣ)
    (hu : ∀ j : ℤ, (t.q : K) ^ j * (u : K) ≠ 1) {n : ℤ} {p : ℕ} (hp : (p : ℤ) = -n) :
    t.Xterm u n * t.theta (-u) ^ 2
      = (t.q : K) ^ (p : ℕ) * ((u : K))⁻¹
        * (t.thetaProdFactor (-(t.q : K)) * t.thetaProdFactor (-((t.q : K) * (u : K)))
            * t.pFactorSeries p (-((u : K))⁻¹)) ^ 2 := by
  have hθ := t.theta_neg_eq u
  have hG := t.one_add_qpow_mul_pFactorSeries p (-((u : K))⁻¹)
  have hfac : (1 : K) + (t.q : K) ^ p * (-((u : K))⁻¹)
      = 1 - (t.q : K) ^ p * ((u : K))⁻¹ := by
    ring
  rw [hfac] at hG
  have hqn : (t.q : K) ^ n = ((t.q : K) ^ (p : ℕ))⁻¹ := by
    have hn : n = -(p : ℤ) := by omega
    rw [hn, zpow_neg, zpow_natCast]
  have hne : (1 : K) - ((t.q : K) ^ (p : ℕ))⁻¹ * (u : K) ≠ 0 := by
    rw [← hqn]
    exact t.one_sub_qzpow_mul_ne_zero hu n
  have hq0 : (t.q : K) ^ (p : ℕ) ≠ 0 := pow_ne_zero _ t.q.ne_zero
  have hne' : (t.q : K) ^ (p : ℕ) - (u : K) ≠ 0 := by
    intro h0
    apply hne
    have hx : (t.q : K) ^ (p : ℕ) = (u : K) := sub_eq_zero.mp h0
    rw [← hx, inv_mul_cancel₀ hq0, sub_self]
  rw [Xterm_apply, hθ, ← hG, hqn]
  field_simp [hne']
  ring

private lemma Yterm_mul_theta_neg_cube_pos (u : Kˣ)
    (hu : ∀ j : ℤ, (t.q : K) ^ j * (u : K) ≠ 1) {n : ℤ} {p : ℕ} (hp : (p : ℤ) + 1 = n) :
    t.Yterm u n * t.theta (-u) ^ 3
      = ((t.q : K) ^ (p + 1)) ^ 2 * (u : K) ^ 2
        * (t.thetaProdFactor (-(t.q : K)) * t.pFactorSeries p (-((t.q : K) * (u : K)))
            * t.thetaProdFactor (-((u : K))⁻¹)) ^ 3 := by
  have hθ := t.theta_neg_eq u
  have hH := t.one_add_qpow_mul_pFactorSeries p (-((t.q : K) * (u : K)))
  have hfac : (1 : K) + (t.q : K) ^ p * (-((t.q : K) * (u : K)))
      = 1 - (t.q : K) ^ (p + 1) * (u : K) := by
    rw [pow_succ]
    ring
  rw [hfac] at hH
  have hqn : (t.q : K) ^ n = (t.q : K) ^ (p + 1) := by
    rw [← hp, show ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hne : (1 : K) - (t.q : K) ^ (p + 1) * (u : K) ≠ 0 := by
    rw [← hqn]
    exact t.one_sub_qzpow_mul_ne_zero hu n
  rw [Yterm_apply, hθ, ← hH, hqn]
  field_simp

private lemma Yterm_mul_theta_neg_cube_neg (u : Kˣ)
    (hu : ∀ j : ℤ, (t.q : K) ^ j * (u : K) ≠ 1) {n : ℤ} {p : ℕ} (hp : (p : ℤ) = -n) :
    t.Yterm u n * t.theta (-u) ^ 3
      = -((t.q : K) ^ (p : ℕ) * ((u : K))⁻¹
        * (t.thetaProdFactor (-(t.q : K)) * t.thetaProdFactor (-((t.q : K) * (u : K)))
            * t.pFactorSeries p (-((u : K))⁻¹)) ^ 3) := by
  have hθ := t.theta_neg_eq u
  have hG := t.one_add_qpow_mul_pFactorSeries p (-((u : K))⁻¹)
  have hfac : (1 : K) + (t.q : K) ^ p * (-((u : K))⁻¹)
      = 1 - (t.q : K) ^ p * ((u : K))⁻¹ := by
    ring
  rw [hfac] at hG
  have hqn : (t.q : K) ^ n = ((t.q : K) ^ (p : ℕ))⁻¹ := by
    have hn : n = -(p : ℤ) := by omega
    rw [hn, zpow_neg, zpow_natCast]
  have hne : (1 : K) - ((t.q : K) ^ (p : ℕ))⁻¹ * (u : K) ≠ 0 := by
    rw [← hqn]
    exact t.one_sub_qzpow_mul_ne_zero hu n
  have hq0 : (t.q : K) ^ (p : ℕ) ≠ 0 := pow_ne_zero _ t.q.ne_zero
  have hne' : (t.q : K) ^ (p : ℕ) - (u : K) ≠ 0 := by
    intro h0
    apply hne
    have hx : (t.q : K) ^ (p : ℕ) = (u : K) := sub_eq_zero.mp h0
    rw [← hx, inv_mul_cancel₀ hq0, sub_self]
  rw [Yterm_apply, hθ, ← hG, hqn]
  field_simp [hne']
  ring

/-! ### Per-`n` `HasSum` with the analytic values -/

private lemma hasSum_xFam (u : Kˣ) (hu : ∀ j : ℤ, (t.q : K) ^ j * (u : K) ≠ 1) (n : ℤ) :
    HasSum (fun m : ℤ => t.xFam n m * (u : K) ^ m) (t.Xterm u n * t.theta (-u) ^ 2) := by
  by_cases hn : 1 ≤ n
  · have hp : (((n - 1).toNat : ℤ)) + 1 = n := by omega
    have h := t.hasSum_xFam_pos (n - 1).toNat u
    have hqn : (t.q : K) ^ n = (t.q : K) ^ ((n - 1).toNat + 1) := by
      conv_lhs => rw [← hp]
      rw [show (((n - 1).toNat : ℤ) + 1) = (((n - 1).toNat + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast]
    have hfun : (fun m : ℤ => ((t.q : K) ^ ((n - 1).toNat + 1)
        * t.thetaProdFactor (-(t.q : K)) ^ 2 * t.convXPos (n - 1).toNat (m - 1)) * (u : K) ^ m)
        = fun m : ℤ => t.xFam n m * (u : K) ^ m := by
      funext m
      simp only [xFam, if_pos hn]
      rw [hqn]
    rw [hfun] at h
    rwa [← t.Xterm_mul_theta_neg_sq_pos u hu hp] at h
  · have hp : (((-n).toNat : ℤ)) = -n := by omega
    have h := t.hasSum_xFam_neg (-n).toNat u
    have hqn : (t.q : K) ^ (-n) = (t.q : K) ^ ((-n).toNat : ℕ) := by
      conv_lhs => rw [← hp]
      rw [zpow_natCast]
    have hfun : (fun m : ℤ => ((t.q : K) ^ ((-n).toNat : ℕ)
        * t.thetaProdFactor (-(t.q : K)) ^ 2 * t.convXNeg (-n).toNat (m + 1)) * (u : K) ^ m)
        = fun m : ℤ => t.xFam n m * (u : K) ^ m := by
      funext m
      simp only [xFam, if_neg hn]
      rw [hqn]
    rw [hfun] at h
    rwa [← t.Xterm_mul_theta_neg_sq_neg u hu hp] at h

private lemma hasSum_yFam (u : Kˣ) (hu : ∀ j : ℤ, (t.q : K) ^ j * (u : K) ≠ 1) (n : ℤ) :
    HasSum (fun m : ℤ => t.yFam n m * (u : K) ^ m) (t.Yterm u n * t.theta (-u) ^ 3) := by
  by_cases hn : 1 ≤ n
  · have hp : (((n - 1).toNat : ℤ)) + 1 = n := by omega
    have h := t.hasSum_yFam_pos (n - 1).toNat u
    have hqn : (t.q : K) ^ n = (t.q : K) ^ ((n - 1).toNat + 1) := by
      conv_lhs => rw [← hp]
      rw [show (((n - 1).toNat : ℤ) + 1) = (((n - 1).toNat + 1 : ℕ) : ℤ) by push_cast; ring,
        zpow_natCast]
    have hfun : (fun m : ℤ => (((t.q : K) ^ ((n - 1).toNat + 1)) ^ 2
        * t.thetaProdFactor (-(t.q : K)) ^ 3 * t.convYPos (n - 1).toNat (m - 2)) * (u : K) ^ m)
        = fun m : ℤ => t.yFam n m * (u : K) ^ m := by
      funext m
      simp only [yFam, if_pos hn]
      rw [hqn]
    rw [hfun] at h
    rwa [← t.Yterm_mul_theta_neg_cube_pos u hu hp] at h
  · have hp : (((-n).toNat : ℤ)) = -n := by omega
    have h := t.hasSum_yFam_neg (-n).toNat u
    have hqn : (t.q : K) ^ (-n) = (t.q : K) ^ ((-n).toNat : ℕ) := by
      conv_lhs => rw [← hp]
      rw [zpow_natCast]
    have hfun : (fun m : ℤ => (-((t.q : K) ^ ((-n).toNat : ℕ)
        * t.thetaProdFactor (-(t.q : K)) ^ 3 * t.convYNeg (-n).toNat (m + 1))) * (u : K) ^ m)
        = fun m : ℤ => t.yFam n m * (u : K) ^ m := by
      funext m
      simp only [yFam, if_neg hn]
      rw [hqn]
    rw [hfun] at h
    rwa [← t.Yterm_mul_theta_neg_cube_neg u hu hp] at h

/-! ### Double-family summability and marginal collapses -/

private lemma summable_xFam_double (u : Kˣ) :
    Summable fun p : ℤ × ℤ => t.xFam p.1 p.2 * (u : K) ^ p.2 := by
  have hub : (0 : ℝ) < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  have hDb : EntireBound fun m : ℤ => t.bound4 (m - 1) + t.bound4 (m + 1) := by
    have h1 := t.entireBound_bound4.shift 1
    have h2 := t.entireBound_bound4.shift (-1)
    have h2' : EntireBound fun m : ℤ => t.bound4 (m + 1) := by
      constructor
      · intro m; exact t.entireBound_bound4.nonneg _
      · intro r hr
        exact (h2.summable r hr).congr fun m => by rw [sub_neg_eq_add]
    exact h1.add h2'
  have hgeo : Summable (fun n : ℤ => ‖(t.q : K)‖ ^ n.natAbs) :=
    summable_pow_natAbs (norm_nonneg _) t.norm_lt_one
  have hcol : Summable (fun m : ℤ => (t.bound4 (m - 1) + t.bound4 (m + 1)) * ‖(u : K)‖ ^ m) :=
    hDb.summable _ hub
  have hprod := hgeo.mul_of_nonneg hcol (fun n => by positivity)
    (fun m => mul_nonneg (hDb.nonneg m) (zpow_nonneg (norm_nonneg _) m))
  refine hprod.of_norm_bounded fun p => ?_
  rw [norm_mul, norm_zpow]
  calc ‖t.xFam p.1 p.2‖ * ‖(u : K)‖ ^ p.2
      ≤ (‖(t.q : K)‖ ^ p.1.natAbs * (t.bound4 (p.2 - 1) + t.bound4 (p.2 + 1)))
        * ‖(u : K)‖ ^ p.2 :=
        mul_le_mul_of_nonneg_right (t.norm_xFam_le p.1 p.2)
          (zpow_nonneg (norm_nonneg _) _)
    _ = ‖(t.q : K)‖ ^ p.1.natAbs
        * ((t.bound4 (p.2 - 1) + t.bound4 (p.2 + 1)) * ‖(u : K)‖ ^ p.2) := by
        rw [mul_assoc]

private lemma summable_yFam_double (u : Kˣ) :
    Summable fun p : ℤ × ℤ => t.yFam p.1 p.2 * (u : K) ^ p.2 := by
  have hub : (0 : ℝ) < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  have hDb : EntireBound fun m : ℤ => t.bound6 (m - 2) + t.bound6 (m + 1) := by
    have h1 := t.entireBound_bound6.shift 2
    have h2 := t.entireBound_bound6.shift (-1)
    have h2' : EntireBound fun m : ℤ => t.bound6 (m + 1) := by
      constructor
      · intro m; exact t.entireBound_bound6.nonneg _
      · intro r hr
        exact (h2.summable r hr).congr fun m => by rw [sub_neg_eq_add]
    exact h1.add h2'
  have hgeo : Summable (fun n : ℤ => ‖(t.q : K)‖ ^ n.natAbs) :=
    summable_pow_natAbs (norm_nonneg _) t.norm_lt_one
  have hcol : Summable (fun m : ℤ => (t.bound6 (m - 2) + t.bound6 (m + 1)) * ‖(u : K)‖ ^ m) :=
    hDb.summable _ hub
  have hprod := hgeo.mul_of_nonneg hcol (fun n => by positivity)
    (fun m => mul_nonneg (hDb.nonneg m) (zpow_nonneg (norm_nonneg _) m))
  refine hprod.of_norm_bounded fun p => ?_
  rw [norm_mul, norm_zpow]
  calc ‖t.yFam p.1 p.2‖ * ‖(u : K)‖ ^ p.2
      ≤ (‖(t.q : K)‖ ^ p.1.natAbs * (t.bound6 (p.2 - 2) + t.bound6 (p.2 + 1)))
        * ‖(u : K)‖ ^ p.2 :=
        mul_le_mul_of_nonneg_right (t.norm_yFam_le p.1 p.2)
          (zpow_nonneg (norm_nonneg _) _)
    _ = ‖(t.q : K)‖ ^ p.1.natAbs
        * ((t.bound6 (p.2 - 2) + t.bound6 (p.2 + 1)) * ‖(u : K)‖ ^ p.2) := by
        rw [mul_assoc]

private lemma summable_xFam_slice (u : Kˣ) (m : ℤ) :
    Summable fun n : ℤ => t.xFam n m * (u : K) ^ m := by
  have hinj : Function.Injective (fun n : ℤ => ((n, m) : ℤ × ℤ)) := fun a b hab => by
    simpa using congrArg Prod.fst hab
  have h := (t.summable_xFam_double u).comp_injective hinj
  exact h.congr fun n => rfl

private lemma summable_yFam_slice (u : Kˣ) (m : ℤ) :
    Summable fun n : ℤ => t.yFam n m * (u : K) ^ m := by
  have hinj : Function.Injective (fun n : ℤ => ((n, m) : ℤ × ℤ)) := fun a b hab => by
    simpa using congrArg Prod.fst hab
  have h := (t.summable_yFam_double u).comp_injective hinj
  exact h.congr fun n => rfl

private lemma hasSum_xFam_marginal (u : Kˣ) :
    HasSum (fun m : ℤ => (∑' n : ℤ, t.xFam n m) * (u : K) ^ m)
      (∑' p : ℤ × ℤ, t.xFam p.1 p.2 * (u : K) ^ p.2) := by
  have hd := (t.summable_xFam_double u).hasSum
  have hswap : HasSum (fun p : ℤ × ℤ => t.xFam p.2 p.1 * (u : K) ^ p.1)
      (∑' p : ℤ × ℤ, t.xFam p.1 p.2 * (u : K) ^ p.2) :=
    ((Equiv.prodComm ℤ ℤ).hasSum_iff).mpr hd
  have hfib : ∀ m : ℤ, HasSum (fun n : ℤ => t.xFam n m * (u : K) ^ m)
      (∑' n : ℤ, t.xFam n m * (u : K) ^ m) := fun m => (t.summable_xFam_slice u m).hasSum
  have h := hswap.prod_fiberwise hfib
  have hfun : (fun m : ℤ => ∑' n : ℤ, t.xFam n m * (u : K) ^ m)
      = fun m : ℤ => (∑' n : ℤ, t.xFam n m) * (u : K) ^ m := by
    funext m
    exact tsum_mul_right
  rwa [hfun] at h

private lemma hasSum_yFam_marginal (u : Kˣ) :
    HasSum (fun m : ℤ => (∑' n : ℤ, t.yFam n m) * (u : K) ^ m)
      (∑' p : ℤ × ℤ, t.yFam p.1 p.2 * (u : K) ^ p.2) := by
  have hd := (t.summable_yFam_double u).hasSum
  have hswap : HasSum (fun p : ℤ × ℤ => t.yFam p.2 p.1 * (u : K) ^ p.1)
      (∑' p : ℤ × ℤ, t.yFam p.1 p.2 * (u : K) ^ p.2) :=
    ((Equiv.prodComm ℤ ℤ).hasSum_iff).mpr hd
  have hfib : ∀ m : ℤ, HasSum (fun n : ℤ => t.yFam n m * (u : K) ^ m)
      (∑' n : ℤ, t.yFam n m * (u : K) ^ m) := fun m => (t.summable_yFam_slice u m).hasSum
  have h := hswap.prod_fiberwise hfib
  have hfun : (fun m : ℤ => ∑' n : ℤ, t.yFam n m * (u : K) ^ m)
      = fun m : ℤ => (∑' n : ℤ, t.yFam n m) * (u : K) ^ m := by
    funext m
    exact tsum_mul_right
  rwa [hfun] at h

/-! ### The public interface -/

/-- **The global Laurent coefficient family of `X(u)·theta(-u)²`.** The `m`-th coefficient is
the (convergent) sum over `n : ℤ` of the per-`n` pole-free families, plus the Eisenstein
constant `-2·s₁` times the `m`-th coefficient of `theta(-u)²`. -/
noncomputable def XThetaSqCoeff : ℤ → K := fun m =>
  (∑' n : ℤ, t.xFam n m) - 2 * t.eisenstein 1 * lconv t.thetaNegCoeff t.thetaNegCoeff m

/-- **The global Laurent coefficient family of `Y(u)·theta(-u)³`.** The `m`-th coefficient is
the (convergent) sum over `n : ℤ` of the per-`n` pole-free families, plus the Eisenstein
constant `+s₁` times the `m`-th coefficient of `theta(-u)³`. -/
noncomputable def YThetaCubeCoeff : ℤ → K := fun m =>
  (∑' n : ℤ, t.yFam n m)
    + t.eisenstein 1 * lconv (lconv t.thetaNegCoeff t.thetaNegCoeff) t.thetaNegCoeff m

/-- The coefficient family of `theta(-u)²` as a global Laurent series. -/
private lemma hasSum_thetaNegSq (u : Kˣ) :
    HasSum (fun m : ℤ => lconv t.thetaNegCoeff t.thetaNegCoeff m * (u : K) ^ m)
      (t.theta (-u) * t.theta (-u)) :=
  hasSum_laurentConvolution u (t.hasSum_thetaNegCoeff u) (t.hasSum_thetaNegCoeff u)

/-- The coefficient family of `theta(-u)³` as a global Laurent series. -/
private lemma hasSum_thetaNegCube (u : Kˣ) :
    HasSum (fun m : ℤ =>
        lconv (lconv t.thetaNegCoeff t.thetaNegCoeff) t.thetaNegCoeff m * (u : K) ^ m)
      (t.theta (-u) * t.theta (-u) * t.theta (-u)) :=
  hasSum_laurentConvolution u (t.hasSum_thetaNegSq u) (t.hasSum_thetaNegCoeff u)

/-- **Global convergence of the `X·Θ²` coefficient family.** For *every* unit `u` (on or off
the orbit `qᶻ`), the family `n ↦ XThetaSqCoeff n · uⁿ` is summable. -/
lemma summable_XThetaSqCoeff_mul_zpow (u : Kˣ) :
    Summable fun n : ℤ => t.XThetaSqCoeff n * (u : K) ^ n := by
  have h1 := (t.hasSum_xFam_marginal u).summable
  have h2 := ((t.hasSum_thetaNegSq u).mul_left (2 * t.eisenstein 1)).summable
  refine (h1.sub h2).congr fun m => ?_
  rw [XThetaSqCoeff]
  ring

/-- **Global convergence of the `Y·Θ³` coefficient family.** For *every* unit `u` (on or off
the orbit `qᶻ`), the family `n ↦ YThetaCubeCoeff n · uⁿ` is summable. -/
lemma summable_YThetaCubeCoeff_mul_zpow (u : Kˣ) :
    Summable fun n : ℤ => t.YThetaCubeCoeff n * (u : K) ^ n := by
  have h1 := (t.hasSum_yFam_marginal u).summable
  have h2 := ((t.hasSum_thetaNegCube u).mul_left (t.eisenstein 1)).summable
  refine (h1.add h2).congr fun m => ?_
  rw [YThetaCubeCoeff]
  ring

/-- **`X(u)·theta(-u)²` as a global two-sided Laurent series.** Off the orbit `qᶻ` — i.e. when
`qⁿ·u ≠ 1` for all `n` — the coefficient family `XThetaSqCoeff` sums to `X u · theta (-u)²`. -/
theorem hasSum_XThetaSqCoeff {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    HasSum (fun n : ℤ => t.XThetaSqCoeff n * (u : K) ^ n)
      (t.X u * t.theta (-u) ^ 2) := by
  -- collapse the double family in the `n`-direction to identify the total.
  have hd := (t.summable_xFam_double u).hasSum
  have hcol : HasSum (fun n : ℤ => t.Xterm u n * t.theta (-u) ^ 2)
      (∑' p : ℤ × ℤ, t.xFam p.1 p.2 * (u : K) ^ p.2) :=
    hd.prod_fiberwise fun n => t.hasSum_xFam u hu n
  have hXsum : HasSum (fun n : ℤ => t.Xterm u n * t.theta (-u) ^ 2)
      ((∑' n : ℤ, t.Xterm u n) * t.theta (-u) ^ 2) :=
    (t.Xterm_summable u).hasSum.mul_right _
  have hT : (∑' p : ℤ × ℤ, t.xFam p.1 p.2 * (u : K) ^ p.2)
      = (∑' n : ℤ, t.Xterm u n) * t.theta (-u) ^ 2 := hcol.unique hXsum
  have h1 : HasSum (fun m : ℤ => (∑' n : ℤ, t.xFam n m) * (u : K) ^ m)
      ((∑' n : ℤ, t.Xterm u n) * t.theta (-u) ^ 2) := hT ▸ t.hasSum_xFam_marginal u
  have h2 := (t.hasSum_thetaNegSq u).mul_left (-(2 * t.eisenstein 1))
  have h := h1.add h2
  have hfun : (fun m : ℤ => (∑' n : ℤ, t.xFam n m) * (u : K) ^ m
      + -(2 * t.eisenstein 1) * (lconv t.thetaNegCoeff t.thetaNegCoeff m * (u : K) ^ m))
      = fun m : ℤ => t.XThetaSqCoeff m * (u : K) ^ m := by
    funext m
    rw [XThetaSqCoeff]
    ring
  have hval : (∑' n : ℤ, t.Xterm u n) * t.theta (-u) ^ 2
      + -(2 * t.eisenstein 1) * (t.theta (-u) * t.theta (-u))
      = t.X u * t.theta (-u) ^ 2 := by
    rw [X_apply]
    ring
  rwa [hfun, hval] at h

/-- **`Y(u)·theta(-u)³` as a global two-sided Laurent series.** Off the orbit `qᶻ` — i.e. when
`qⁿ·u ≠ 1` for all `n` — the coefficient family `YThetaCubeCoeff` sums to `Y u · theta (-u)³`. -/
theorem hasSum_YThetaCubeCoeff {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    HasSum (fun n : ℤ => t.YThetaCubeCoeff n * (u : K) ^ n)
      (t.Y u * t.theta (-u) ^ 3) := by
  have hd := (t.summable_yFam_double u).hasSum
  have hcol : HasSum (fun n : ℤ => t.Yterm u n * t.theta (-u) ^ 3)
      (∑' p : ℤ × ℤ, t.yFam p.1 p.2 * (u : K) ^ p.2) :=
    hd.prod_fiberwise fun n => t.hasSum_yFam u hu n
  have hYsum : HasSum (fun n : ℤ => t.Yterm u n * t.theta (-u) ^ 3)
      ((∑' n : ℤ, t.Yterm u n) * t.theta (-u) ^ 3) :=
    (t.Yterm_summable u).hasSum.mul_right _
  have hT : (∑' p : ℤ × ℤ, t.yFam p.1 p.2 * (u : K) ^ p.2)
      = (∑' n : ℤ, t.Yterm u n) * t.theta (-u) ^ 3 := hcol.unique hYsum
  have h1 : HasSum (fun m : ℤ => (∑' n : ℤ, t.yFam n m) * (u : K) ^ m)
      ((∑' n : ℤ, t.Yterm u n) * t.theta (-u) ^ 3) := hT ▸ t.hasSum_yFam_marginal u
  have h2 := (t.hasSum_thetaNegCube u).mul_left (t.eisenstein 1)
  have h := h1.add h2
  have hfun : (fun m : ℤ => (∑' n : ℤ, t.yFam n m) * (u : K) ^ m
      + t.eisenstein 1
        * (lconv (lconv t.thetaNegCoeff t.thetaNegCoeff) t.thetaNegCoeff m * (u : K) ^ m))
      = fun m : ℤ => t.YThetaCubeCoeff m * (u : K) ^ m := by
    funext m
    rw [YThetaCubeCoeff]
    ring
  have hval : (∑' n : ℤ, t.Yterm u n) * t.theta (-u) ^ 3
      + t.eisenstein 1 * (t.theta (-u) * t.theta (-u) * t.theta (-u))
      = t.Y u * t.theta (-u) ^ 3 := by
    rw [Y_apply]
    ring
  rwa [hfun, hval] at h

end TateParameter

end TateCurvesTheta
