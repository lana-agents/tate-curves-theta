/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.TateCurve.EisensteinKernels
import TateCurvesTheta.TateCurve.Parametrization

/-!
# Inversion symmetry of the Tate coordinates

The substitution `u ↦ u⁻¹` corresponds to negation on the Tate curve
`y² + xy = x³ + a₄x + a₆`: the `X`-coordinate is even, `X(u⁻¹) = X(u)`, and the
`Y`-coordinate transforms by the curve's negation `y ↦ -y - x`,
`Y(u⁻¹) = -Y(u) - X(u)`. Termwise this is the index flip `n ↦ -n` of the defining series
together with the inversion parities of the Eisenstein kernels
(`TateCurve/EisensteinKernels.lean`) and the integral identity
`y(x⁻¹) = -y(x) - p(x)` for the nodal kernels `p(x) = x/(1-x)²`, `y(x) = x²/(1-x)³`.
These identities make `u ↦ (X(u), Y(u))` compatible with the elliptic involution — the
negation step of the group isomorphism `Kˣ/qᶻ ≃ E_q(K)`.

## Main results

* `TateCurvesTheta.TateParameter.X_inv`: `X(u⁻¹) = X(u)`.
* `TateCurvesTheta.TateParameter.Y_inv`: `Y(u⁻¹) = -Y(u) - X(u)`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Off the orbit, `u⁻¹` is off the orbit as well. -/
lemma inv_off_orbit {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) (n : ℤ) :
    (t.q : K) ^ n * ((u⁻¹ : Kˣ) : K) ≠ 1 := by
  intro hcontra
  apply hu (-n)
  have hu0 : (u : K) ≠ 0 := Units.ne_zero u
  have hval : ((u⁻¹ : Kˣ) : K) = (u : K)⁻¹ := Units.val_inv_eq_inv_val u
  rw [hval] at hcontra
  have hq : (t.q : K) ^ n = (u : K) := by
    have h := congrArg (fun z => z * (u : K)) hcontra
    simpa [mul_assoc, inv_mul_cancel₀ hu0] using h
  rw [zpow_neg, hq]
  exact inv_mul_cancel₀ hu0

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma orbit_ne_zero (u : Kˣ) (n : ℤ) : (t.q : K) ^ n * (u : K) ≠ 0 :=
  mul_ne_zero (zpow_ne_zero n t.q.ne_zero) (Units.ne_zero u)

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma orbit_inv_eq (u : Kˣ) (n : ℤ) :
    ((t.q : K) ^ n * ((u⁻¹ : Kˣ) : K))⁻¹ = (t.q : K) ^ (-n) * (u : K) := by
  have hval : ((u⁻¹ : Kˣ) : K) = (u : K)⁻¹ := Units.val_inv_eq_inv_val u
  rw [hval, mul_inv, inv_inv, zpow_neg]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Termwise inversion of the `X`-series: `Xterm(u⁻¹, n) = Xterm(u, -n)` — the evenness
`p(x⁻¹) = p(x)` of the Eisenstein kernel at `x = qⁿu⁻¹`. -/
lemma Xterm_inv {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) (n : ℤ) :
    t.Xterm u⁻¹ n = t.Xterm u (-n) := by
  have hx0 : (t.q : K) ^ n * ((u⁻¹ : Kˣ) : K) ≠ 0 := orbit_ne_zero t u⁻¹ n
  have hx1 : (t.q : K) ^ n * ((u⁻¹ : Kˣ) : K) ≠ 1 := t.inv_off_orbit hu n
  have h := eisP_inv hx0 hx1
  rw [orbit_inv_eq] at h
  exact h.symm

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The nodal-kernel inversion identity `y(x⁻¹) = -y(x) - p(x)`, integral over `ℤ`. -/
private lemma ykernel_inv {x : K} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    (x⁻¹) ^ 2 / (1 - x⁻¹) ^ 3 = -(x ^ 2 / (1 - x) ^ 3) - x / (1 - x) ^ 2 := by
  have h1 : (1 : K) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hinv : (1 : K) - x⁻¹ = -((1 - x) / x) := by
    field_simp
    ring
  rw [hinv]
  field_simp
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Termwise inversion of the `Y`-series:
`Yterm(u⁻¹, n) = -Yterm(u, -n) - Xterm(u, -n)`. -/
lemma Yterm_inv {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) (n : ℤ) :
    t.Yterm u⁻¹ n = -t.Yterm u (-n) - t.Xterm u (-n) := by
  have hx0 : (t.q : K) ^ (-n) * (u : K) ≠ 0 := orbit_ne_zero t u (-n)
  have hx1 : (t.q : K) ^ (-n) * (u : K) ≠ 1 := fun h => hu (-n) h
  have h := ykernel_inv hx0 hx1
  have harg : ((t.q : K) ^ (-n) * (u : K))⁻¹ = (t.q : K) ^ n * ((u⁻¹ : Kˣ) : K) := by
    have hval : ((u⁻¹ : Kˣ) : K) = (u : K)⁻¹ := Units.val_inv_eq_inv_val u
    rw [hval, mul_inv, ← zpow_neg, neg_neg]
  rw [harg] at h
  rw [Yterm_apply, Yterm_apply, Xterm_apply]
  exact h

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **Evenness of the Tate `X`-coordinate**: `X(u⁻¹) = X(u)`. -/
theorem X_inv {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    t.X u⁻¹ = t.X u := by
  rw [X_apply, X_apply]
  congr 1
  calc (∑' n : ℤ, t.Xterm u⁻¹ n) = ∑' n : ℤ, t.Xterm u (-n) :=
        tsum_congr fun n => t.Xterm_inv hu n
    _ = ∑' n : ℤ, t.Xterm u n := by
        rw [← (Equiv.neg ℤ).tsum_eq (t.Xterm u)]
        exact tsum_congr fun n => rfl

/-- **Negation of the Tate `Y`-coordinate**: `Y(u⁻¹) = -Y(u) - X(u)` — the substitution
`u ↦ u⁻¹` realizes the elliptic involution `(x, y) ↦ (x, -y - x)` of the Tate curve. -/
theorem Y_inv {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    t.Y u⁻¹ = -t.Y u - t.X u := by
  have hX := t.Xterm_summable u
  have hY := t.Yterm_summable u
  have hXflip : Summable fun n : ℤ => t.Xterm u (-n) :=
    hX.comp_injective neg_injective
  have hYflip : Summable fun n : ℤ => t.Yterm u (-n) :=
    hY.comp_injective neg_injective
  have hsum : (∑' n : ℤ, t.Yterm u⁻¹ n)
      = -(∑' n : ℤ, t.Yterm u n) - ∑' n : ℤ, t.Xterm u n := by
    calc (∑' n : ℤ, t.Yterm u⁻¹ n)
        = ∑' n : ℤ, (-t.Yterm u (-n) - t.Xterm u (-n)) :=
          tsum_congr fun n => t.Yterm_inv hu n
      _ = -(∑' n : ℤ, t.Yterm u (-n)) - ∑' n : ℤ, t.Xterm u (-n) := by
          rw [Summable.tsum_sub hYflip.neg hXflip, tsum_neg]
      _ = -(∑' n : ℤ, t.Yterm u n) - ∑' n : ℤ, t.Xterm u n := by
          congr 1
          · congr 1
            rw [← (Equiv.neg ℤ).tsum_eq (t.Yterm u)]
            exact tsum_congr fun n => rfl
          · rw [← (Equiv.neg ℤ).tsum_eq (t.Xterm u)]
            exact tsum_congr fun n => rfl
  rw [Y_apply, Y_apply, X_apply, hsum]
  ring

end TateParameter

end TateCurvesTheta
