/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.Theta.Durfee
import TateCurvesTheta.Theta.Periodicity

/-!
# Inversion and oddness of the `q`-theta function

The substitution `u ↦ u⁻¹` acts on the naive `q`-theta function
`θ(u) = ∑ q^{n(n+1)/2}·uⁿ` through the index flip `n ↦ -(n+1)`, which preserves the
exponent `n(n+1)/2`: this yields the **inversion functional equation**

* `theta_inv` : `θ(u⁻¹) = u·θ(u)`.

Renormalizing to the **odd theta function** `θ̈(u) = u·θ(-u²)` (the signed series
`∑ (-1)ⁿ q^{n(n+1)/2}·u^{2n+1}` of Mochizuki's *The Étale Theta Function*,
Proposition 1.4) turns inversion into genuine **oddness**, and the `qᶻ`-automorphy into
the classical quasi-periodicity:

* `thetaOdd_inv` : `θ̈(u⁻¹) = -θ̈(u)` — the oddness functional equation;
* `thetaOdd_q_smul` : `θ̈(q·u) = (q²·u⁴)⁻¹·θ̈(u)`;
* `thetaOdd_eq_zero_iff` : `θ̈(u) = 0 ↔ u² ∈ qᶻ` — the zero divisor of the odd theta,
  the theta divisor supported at the `2`-torsion classes of `Kˣ/qᶻ` lying over the
  identity component.

Together with the convergence (`Theta/Basic.lean`), `qᶻ`-automorphy
(`Theta/Periodicity.lean`), triple-product expansion and zero divisor
(`Theta/Durfee.lean`), this completes the classical functional-equation package of the
formal algebraic theta function.

## References

* S. Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations*,
  Proposition 1.4 (classical content only).
* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-- The index flip `n ↦ -(n+1)` of the theta series, as a permutation of `ℤ`. -/
private def negSuccEquiv : ℤ ≃ ℤ :=
  Function.Involutive.toPerm (fun n => -(n + 1)) fun n => by ring

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The theta exponent `n(n+1)/2` is invariant under the index flip `n ↦ -(n+1)`. -/
lemma thetaExp_neg_succ (n : ℤ) : thetaExp (-(n + 1)) = thetaExp n := by
  have h : -(n + 1) * (-(n + 1) + 1) = n * (n + 1) := by ring
  simp only [thetaExp, h]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Termwise inversion: `thetaTerm u⁻¹ (-(n+1)) = u · thetaTerm u n`. -/
lemma thetaTerm_inv_neg_succ (u : Kˣ) (n : ℤ) :
    t.thetaTerm u⁻¹ (-(n + 1)) = (u : K) * t.thetaTerm u n := by
  have hu : (u : K) ≠ 0 := Units.ne_zero u
  rw [thetaTerm, thetaTerm, thetaExp_neg_succ, Units.val_inv_eq_inv_val, inv_zpow,
    ← zpow_neg, neg_neg, zpow_add₀ hu, zpow_one]
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **The inversion functional equation of the `q`-theta function**:
`θ(u⁻¹) = u·θ(u)`, by the exponent-preserving index flip `n ↦ -(n+1)`. -/
theorem theta_inv (u : Kˣ) : t.theta u⁻¹ = (u : K) * t.theta u := by
  calc t.theta u⁻¹ = ∑' n : ℤ, t.thetaTerm u⁻¹ n := rfl
    _ = ∑' n : ℤ, t.thetaTerm u⁻¹ (-(n + 1)) :=
        (negSuccEquiv.tsum_eq (t.thetaTerm u⁻¹)).symm
    _ = ∑' n : ℤ, (u : K) * t.thetaTerm u n := tsum_congr (t.thetaTerm_inv_neg_succ u)
    _ = (u : K) * t.theta u := tsum_mul_left

/-! ### The odd normalization -/

/-- **The odd theta function** `θ̈(u) = u·θ(-u²)` — the signed odd-exponent series
`∑_{n : ℤ} (-1)ⁿ q^{n(n+1)/2}·u^{2n+1}` of Mochizuki's Proposition 1.4, expressed
through the naive theta function. -/
def thetaOdd (u : Kˣ) : K := (u : K) * t.theta (-(u ^ 2))

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma thetaOdd_apply (u : Kˣ) : t.thetaOdd u = (u : K) * t.theta (-(u ^ 2)) := rfl

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **Oddness of the odd theta function**: `θ̈(u⁻¹) = -θ̈(u)`. -/
theorem thetaOdd_inv (u : Kˣ) : t.thetaOdd u⁻¹ = -t.thetaOdd u := by
  have hu : (u : K) ≠ 0 := Units.ne_zero u
  have hUnit : -(u⁻¹ ^ 2) = (-(u ^ 2))⁻¹ := Units.ext (by
    push_cast [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp)
  rw [thetaOdd, thetaOdd, hUnit, t.theta_inv, Units.val_neg, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val]
  field_simp

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **Quasi-periodicity of the odd theta function**: `θ̈(q·u) = (q²·u⁴)⁻¹·θ̈(u)`. -/
theorem thetaOdd_q_smul (u : Kˣ) :
    t.thetaOdd (t.q * u) = ((t.q : K) ^ 2 * (u : K) ^ 4)⁻¹ * t.thetaOdd u := by
  have hq : (t.q : K) ≠ 0 := Units.ne_zero t.q
  have hu : (u : K) ≠ 0 := Units.ne_zero u
  have hUnit : -((t.q * u) ^ 2) = t.q ^ (2 : ℤ) * (-(u ^ 2)) := by
    rw [zpow_two]
    exact Units.ext (by
      push_cast [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mul]
      ring)
  have hexp2 : thetaExp 2 = 3 := by decide
  rw [thetaOdd, thetaOdd, hUnit, t.theta_zpow_q_smul (-(u ^ 2)) 2, hexp2,
    Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mul]
  field_simp

/-- **The zero divisor of the odd theta function**: `θ̈(u) = 0` exactly when `u² ∈ qᶻ` —
the theta divisor of the Tate curve, supported at the four `2`-torsion half-classes. -/
theorem thetaOdd_eq_zero_iff (u : Kˣ) :
    t.thetaOdd u = 0 ↔ ∃ k : ℤ, (u : K) ^ 2 = (t.q : K) ^ k := by
  have hu : (u : K) ≠ 0 := Units.ne_zero u
  rw [thetaOdd, mul_eq_zero]
  simp only [hu, false_or]
  rw [t.theta_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [Units.val_neg, Units.val_pow_eq_pow_val] at hk
    exact neg_injective hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [Units.val_neg, Units.val_pow_eq_pow_val, hk]

end TateParameter

end TateCurvesTheta
