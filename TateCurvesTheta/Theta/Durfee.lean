/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.Theta.ThetaProdGlobalLaurent
import TateCurvesTheta.Theta.LaurentUnitSphere

/-!
# The `b₀ = 1` normalization of `theta = thetaProd` (the Durfee-square identity)

After `Theta/ThetaProdGlobalLaurent.lean` (#148) proved the global Laurent expansion
`thetaProdLaurentRepr` unconditionally, and `Theta/LaurentUnitSphere.lean` (#28) proved the
coefficient-uniqueness principle `laurentCoeffUnique` unconditionally, the Jacobi triple product
identity `theta = thetaProd` is pinned by a single scalar: the constant `b₀` with
`thetaProd u = b₀ · theta u` must equal `1`.

This file identifies `b₀` explicitly and reduces the full identity to that one scalar equation.

## Main results

* `TateParameter.thetaProdLaurentCoeff_zero` : the `0`-th global Laurent coefficient of `thetaProd`
  is
  ```
  thetaProdLaurentCoeff 0 = thetaProdFactor(-q) · ∑' k : ℕ, (factorCoeff k)² · qᵏ .
  ```
  Since `factorCoeff k = q^{k(k-1)/2}/(q;q)_k` and `thetaProdFactor(-q) = (q;q)_∞`, the right-hand
  side is `(q;q)_∞ · ∑_{k≥0} q^{k²}/(q;q)_k²`; the classical **Durfee-square identity**
  `∑_{k≥0} q^{k²}/(q;q)_k² = 1/(q;q)_∞` is exactly the statement that this equals `1`.

* `TateParameter.const_eq_thetaProdLaurentCoeff_zero` : the constant `b₀` of
  `thetaProd = b₀ · theta` is precisely this `0`-th coefficient — so pinning `b₀ = 1` is a pure,
  self-contained `q`-series identity with no remaining analytic content.

* `TateParameter.theta_eq_thetaProd_of_durfee` : **unconditional** `theta u = thetaProd u`, given
  the scalar Durfee identity `thetaProdFactor(-q) · durfeeSum = 1` as a hypothesis.

* `TateParameter.theta_eq_zero_iff_of_durfee` : the now-unconditional series-`theta` divisor
  `theta u = 0 ↔ ∃ k : ℤ, (u : K) = -qᵏ`, again given the Durfee identity.

The single remaining obligation to make `theta = thetaProd` fully unconditional is the scalar
Durfee-square identity `durfeeSum = 1`; it carries no analytic content (both sides are
everywhere-convergent series/products in `q`) and is scoped as a follow-up (issue #161).

## References

* G. E. Andrews, *The Theory of Partitions*, §3.3 (the Durfee square).
* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.2, §10.4.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
-/

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-- The **Durfee-square sum** `∑_{k≥0} (factorCoeff k)² · qᵏ = ∑_{k≥0} q^{k²}/(q;q)_k²`. -/
noncomputable def durfeeSum : K := ∑' k : ℕ, (factorCoeff t k) ^ 2 * (t.q : K) ^ k

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The `0`-th global Laurent coefficient of `thetaProd` is `thetaProdFactor(-q)` times the
Durfee-square sum. The two-sided convolution `∑' m, aLaurentCoeff(-m)·bLaurentCoeff m` collapses to
its diagonal `m = -k` (`k ≥ 0`), where `aLaurentCoeff k · bLaurentCoeff (-k) =
(factorCoeff k · qᵏ) · factorCoeff k = (factorCoeff k)² · qᵏ`. -/
lemma thetaProdLaurentCoeff_zero :
    t.thetaProdLaurentCoeff 0 = t.thetaProdFactor (-(t.q : K)) * t.durfeeSum := by
  rw [thetaProdLaurentCoeff, durfeeSum]
  congr 1
  -- Reindex the two-sided sum over `m` by `k ↦ -k`; off that range `bLaurentCoeff m = 0`.
  have hinj : Function.Injective (fun k : ℕ => -(k : ℤ)) := fun a b h => by simpa using h
  have hoff : ∀ m : ℤ, m ∉ Set.range (fun k : ℕ => -(k : ℤ)) →
      t.aLaurentCoeff (0 - m) * t.bLaurentCoeff m = 0 := by
    intro m hm
    have hpos : 0 < m := by
      by_contra h
      exact hm ⟨(-m).toNat, by simp [Int.toNat_of_nonneg (neg_nonneg.mpr (not_lt.mp h))]⟩
    simp [t.bLaurentCoeff_of_pos hpos]
  rw [← hinj.tsum_eq (Function.support_subset_iff'.mpr hoff)]
  refine tsum_congr fun k => ?_
  have h0k : (0 : ℤ) - -(k : ℤ) = (k : ℤ) := by ring
  rw [h0k, aLaurentCoeff_natCast, bLaurentCoeff_negNatCast]
  ring

/-- The constant `b₀` in `thetaProd = b₀ · theta` (from `thetaProd_eq_const_mul_theta`,
unconditional via the global Laurent expansion `thetaProdLaurentRepr` and `laurentCoeffUnique`)
equals the `0`-th Laurent coefficient of `thetaProd`. Consequently
`b₀ = thetaProdFactor(-q) · durfeeSum`, so the whole identity `theta = thetaProd` is pinned by the
scalar Durfee-square value alone. -/
lemma const_eq_thetaProdLaurentCoeff_zero {b₀ : K}
    (hb₀ : ∀ u : Kˣ, t.thetaProd u = b₀ * t.theta u) :
    b₀ = t.thetaProdLaurentCoeff 0 := by
  -- Compare the two Laurent coefficient families of `thetaProd`: its honest coefficients
  -- `thetaProdLaurentCoeff` and `n ↦ b₀ · q^(e n)` (from `b₀ · theta`), via `laurentCoeffUnique`.
  have hAsum : ∀ u : Kˣ, Summable fun n : ℤ => t.thetaProdLaurentCoeff n * (u : K) ^ n :=
    fun u => (t.thetaProd_hasSum_laurent u).summable
  have hBsum : ∀ u : Kˣ, Summable fun n : ℤ => (b₀ * (t.q : K) ^ (thetaExp n)) * (u : K) ^ n := by
    intro u
    refine ((t.thetaTerm_summable u).mul_left b₀).congr fun n => ?_
    simp only [thetaTerm]; ring
  have hEq : ∀ u : Kˣ, (∑' n : ℤ, t.thetaProdLaurentCoeff n * (u : K) ^ n)
      = ∑' n : ℤ, (b₀ * (t.q : K) ^ (thetaExp n)) * (u : K) ^ n := by
    intro u
    rw [(t.thetaProd_hasSum_laurent u).tsum_eq, hb₀ u, theta_apply]
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring
  have huniq := laurentCoeffUnique t t.thetaProdLaurentCoeff
    (fun n => b₀ * (t.q : K) ^ (thetaExp n)) hAsum hBsum hEq
  have h0 := congrFun huniq 0
  have hexp0 : thetaExp 0 = 0 := by simp [thetaExp]
  rw [hexp0, zpow_zero, mul_one] at h0
  exact h0.symm

/-- **The Jacobi triple product identity `theta = thetaProd`, unconditionally**, given the scalar
Durfee-square normalization `thetaProdFactor(-q) · durfeeSum = 1`. All analytic content
(the global Laurent expansion of `thetaProd`, and coefficient uniqueness) is already discharged on
`main`; the only hypothesis is the pure `q`-series identity pinning the constant. -/
theorem theta_eq_thetaProd_of_durfee (hdurfee : t.thetaProdFactor (-(t.q : K)) * t.durfeeSum = 1)
    (u : Kˣ) : t.theta u = t.thetaProd u := by
  obtain ⟨b₀, hb₀⟩ := t.thetaProd_eq_const_mul_theta t.laurentCoeffUnique t.thetaProdLaurentRepr
  have hb₀1 : b₀ = 1 := by
    rw [t.const_eq_thetaProdLaurentCoeff_zero hb₀, t.thetaProdLaurentCoeff_zero, hdurfee]
  rw [hb₀ u, hb₀1, one_mul]

/-- **The series-`theta` divisor, unconditionally** (given the Durfee normalization): `theta`
vanishes exactly on the orbit `-qᶻ`. This discharges the conditionality of
`theta_eq_zero_iff_of_eq_thetaProd` (`Theta/Divisor.lean`, #88). -/
theorem theta_eq_zero_iff_of_durfee
    (hdurfee : t.thetaProdFactor (-(t.q : K)) * t.durfeeSum = 1) (u : Kˣ) :
    t.theta u = 0 ↔ ∃ k : ℤ, (u : K) = -(t.q : K) ^ k :=
  t.theta_eq_zero_iff_of_eq_thetaProd u (t.theta_eq_thetaProd_of_durfee hdurfee u)

end TateParameter

end TateCurvesTheta
