/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.Theta.ThetaProdGlobalLaurent
import TateCurvesTheta.Theta.LaurentUnitSphere

/-!
# The `theta = thetaProd` normalization constant in closed form (reduction to a scalar identity)

With the rigid-analytic core of the Jacobi triple product discharged
(`Theta/ThetaProdGlobalLaurent.lean`, #148), the identity `theta = thetaProd` is reduced to a
single scalar normalization: the constant `b₀` with `thetaProd u = b₀ · theta u`
(`thetaProd_eq_const_mul_theta_of_laurentCoeffUnique`) must equal `1`.

This file identifies `b₀` **in closed form**, stripping away all Laurent-coefficient and
uniqueness plumbing. Comparing the `u⁰` Laurent coefficients of `thetaProd = b₀ · theta` via the
(unconditional) coefficient-uniqueness principle `laurentCoeffUnique` pins `b₀` to the constant
term `thetaProdLaurentCoeff 0`, and unfolding that constant term gives
```
b₀ = thetaProdLaurentCoeff 0 = thetaProdFactor(-q) · ∑' k, factorCoeff k ² · qᵏ.
```
Consequently the full identity `theta = thetaProd` follows from the single **scalar** `q`-series
identity `thetaProdFactor(-q) · ∑' k, factorCoeff k ² · qᵏ = 1` — carrying no analytic content.
In classical terms this is the **Durfee square identity**
`∑ₖ q^{k²}/((q;q)ₖ)² = 1/(q;q)_∞` (since `factorCoeff k = q^{k(k-1)/2}/(q;q)ₖ` and
`thetaProdFactor(-q) = (q;q)_∞`); see the follow-up issue #160.

## Main results

* `TateParameter.thetaProdLaurentCoeff_zero_eq` : the closed form
  `thetaProdLaurentCoeff 0 = thetaProdFactor(-q) · ∑' k, factorCoeff k ² · qᵏ`.
* `TateParameter.const_eq_thetaProdLaurentCoeff_zero` : any `b₀` with `thetaProd = b₀ · theta`
  equals `thetaProdLaurentCoeff 0` (coefficient uniqueness at `u⁰`).
* `TateParameter.thetaProdNormConst` : the normalization constant
  `thetaProdFactor(-q) · ∑' k, factorCoeff k ² · qᵏ` (the value of `b₀`).
* `TateParameter.theta_eq_thetaProd_of_durfee` : the Jacobi triple product identity
  `theta = thetaProd`, reduced to the scalar hypothesis `thetaProdNormConst = 1`.

## References

* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.2–10.4 (q-binomial, Durfee squares).
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

open scoped Topology

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **Closed form of the `u⁰` Laurent coefficient of `thetaProd`.** Unfolding
`thetaProdLaurentCoeff 0 = thetaProdFactor(-q) · ∑' m, aLaurentCoeff(-m)·bLaurentCoeff(m)` and
reindexing the convolution by `m = -k` (only `m ≤ 0` contributes), with
`aLaurentCoeff k · bLaurentCoeff (-k) = factorCoeff k · qᵏ · factorCoeff k = factorCoeff k ² · qᵏ`,
gives `thetaProdFactor(-q) · ∑' k, factorCoeff k ² · qᵏ`. -/
lemma thetaProdLaurentCoeff_zero_eq :
    t.thetaProdLaurentCoeff 0
      = t.thetaProdFactor (-(t.q : K)) * ∑' k : ℕ, factorCoeff t k ^ 2 * (t.q : K) ^ k := by
  rw [thetaProdLaurentCoeff]
  congr 1
  have hinj : Function.Injective (fun k : ℕ => -(k : ℤ)) := fun a b h => by simpa using h
  have hoff : ∀ m : ℤ, m ∉ Set.range (fun k : ℕ => -(k : ℤ)) →
      t.aLaurentCoeff (0 - m) * t.bLaurentCoeff m = 0 := by
    intro m hm
    rw [Set.mem_range] at hm
    have hpos : 0 < m := by
      by_contra h
      exact hm ⟨(-m).toNat, by simp [Int.toNat_of_nonneg (neg_nonneg.mpr (not_lt.mp h))]⟩
    simp [t.bLaurentCoeff_of_pos hpos]
  rw [← hinj.tsum_eq (f := fun m : ℤ => t.aLaurentCoeff (0 - m) * t.bLaurentCoeff m)
    (Function.support_subset_iff'.mpr hoff)]
  refine tsum_congr fun k => ?_
  simp only [zero_sub, neg_neg, aLaurentCoeff_natCast, bLaurentCoeff_negNatCast]
  ring

/-- **The normalization constant `b₀` is the `u⁰` Laurent coefficient.** For any `b₀` with
`thetaProd u = b₀ · theta u` on all of `Kˣ`, coefficient uniqueness (`laurentCoeffUnique`) applied
to the two Laurent developments of `thetaProd` — its own `thetaProdLaurentCoeff` and the scaled
`theta`-coefficients `n ↦ b₀ · q^(e n)` — forces `thetaProdLaurentCoeff = fun n => b₀ · q^(e n)`,
and evaluating at `n = 0` (where `q^(e 0) = q^0 = 1`) gives `b₀ = thetaProdLaurentCoeff 0`. -/
lemma const_eq_thetaProdLaurentCoeff_zero {b₀ : K}
    (hb₀ : ∀ u : Kˣ, t.thetaProd u = b₀ * t.theta u) :
    b₀ = t.thetaProdLaurentCoeff 0 := by
  have hAsum : ∀ u : Kˣ, Summable fun n : ℤ => t.thetaProdLaurentCoeff n * (u : K) ^ n :=
    fun u => (t.thetaProd_hasSum_laurent u).summable
  have hBsum : ∀ u : Kˣ,
      Summable fun n : ℤ => (b₀ * (t.q : K) ^ (thetaExp n)) * (u : K) ^ n := by
    intro u
    refine ((t.thetaTerm_summable u).mul_left b₀).congr fun n => ?_
    rw [thetaTerm]; ring
  have heq : ∀ u : Kˣ,
      (∑' n : ℤ, t.thetaProdLaurentCoeff n * (u : K) ^ n)
        = ∑' n : ℤ, (b₀ * (t.q : K) ^ (thetaExp n)) * (u : K) ^ n := by
    intro u
    rw [(t.thetaProd_hasSum_laurent u).tsum_eq, hb₀ u, theta_apply, ← tsum_mul_left]
    exact tsum_congr fun n => by ring
  have hcoeff := t.laurentCoeffUnique _ _ hAsum hBsum heq
  have h0 := congrFun hcoeff 0
  have hz : thetaExp 0 = 0 := by simp [thetaExp]
  rw [hz, zpow_zero, mul_one] at h0
  exact h0.symm

/-- **The `theta = thetaProd` normalization constant.** The value of the constant `b₀` with
`thetaProd = b₀ · theta`, in closed form: `thetaProdFactor(-q) · ∑' k, factorCoeff k ² · qᵏ`.
The Jacobi triple product identity is exactly the statement `thetaProdNormConst = 1`. -/
noncomputable def thetaProdNormConst : K :=
  t.thetaProdFactor (-(t.q : K)) * ∑' k : ℕ, factorCoeff t k ^ 2 * (t.q : K) ^ k

/-- The constant `b₀` of `thetaProd_eq_const_mul_theta` equals `thetaProdNormConst`. -/
lemma const_eq_thetaProdNormConst {b₀ : K} (hb₀ : ∀ u : Kˣ, t.thetaProd u = b₀ * t.theta u) :
    b₀ = t.thetaProdNormConst := by
  rw [t.const_eq_thetaProdLaurentCoeff_zero hb₀, t.thetaProdLaurentCoeff_zero_eq,
    thetaProdNormConst]

/-- **The Jacobi triple product identity `theta = thetaProd`, reduced to a scalar identity.** All
analytic content is discharged: given only the scalar normalization `thetaProdNormConst = 1`
(equivalently the Durfee square identity `thetaProdFactor(-q) · ∑' k, factorCoeff k ² · qᵏ = 1`),
the naive `q`-theta series equals its product form on all of `Kˣ`. The coefficient-uniqueness
principle is discharged unconditionally via `laurentCoeffUnique`. -/
theorem theta_eq_thetaProd_of_durfee (hnorm : t.thetaProdNormConst = 1) (u : Kˣ) :
    t.theta u = t.thetaProd u := by
  obtain ⟨b₀, hb₀⟩ :=
    t.thetaProd_eq_const_mul_theta_of_laurentCoeffUnique t.laurentCoeffUnique
  have hb1 : b₀ = 1 := by rw [t.const_eq_thetaProdNormConst hb₀, hnorm]
  rw [hb₀ u, hb1, one_mul]

end TateParameter

end TateCurvesTheta
