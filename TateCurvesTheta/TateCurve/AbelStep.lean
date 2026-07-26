/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.TateCurve.DefectCoeffBaseChange
import TateCurvesTheta.Theta.PuncturedProduct
import TateCurvesTheta.Theta.WeightSpace

/-!
# The nonarchimedean Abel step: third intersection and `X`-separation

For a Tate parameter `q` over a complete nonarchimedean field `K`, the coefficient families
`XThetaSqCoeff` and `YThetaCubeCoeff` of `X(u)·θ(-u)²` and `Y(u)·θ(-u)³`
(`Theta/PuncturedProduct.lean`) are **weight families** in the sense of
`Theta/WeightSpace.lean`: they satisfy the theta functional equation of weight `2` resp. `3`
with multiplier `Aθ² := ((q·(-1))⁻¹)²` resp. `Aθ³`. Consequently, for a line `y = λx + μ`,
the family of `(Y(u) - λ·X(u) - μ)·θ(-u)³` lies in the three-dimensional weight space
`W 3 (Aθ³)` — and vanishing at two points lets us **divide** by the corresponding theta
blocks (`exists_convBlock_eq'`), leaving a weight-one family, which is a single theta block
(`w1_eq_smul_thetaBlock`). Reading off the zero class of the remaining block is the
nonarchimedean **Abel theorem** for the Tate curve: if the line passes through the Tate
points of `u` and `v`, it passes through the Tate point of `(u·v)⁻¹`.

The same one-division argument applied to `X` alone shows that the `X`-coordinate separates
`qᶻ`-classes up to inversion, using a norm-blowup estimate `‖X(1 + q^{k+1})‖ = ‖q‖⁻²⁽ᵏ⁺¹⁾`
to rule out the degenerate constant case.

## Main results

* `TateParameter.isWeightFamily_XThetaSq`, `TateParameter.isWeightFamily_YThetaCube` :
  the coordinate-theta families are weight families.
* `TateParameter.tsum_lineFam` : the line family evaluates to `(Y u - λ·X u - μ)·θ(-u)³`.
* `TateParameter.line_third_intersection` : the **third-intersection theorem** (the Abel
  step): a line through the Tate points of `u` and `v` passes through the Tate point of
  `(u·v)⁻¹`.
* `TateParameter.class_eq_or_inv_of_X_eq` : the `X`-coordinate separates `qᶻ`-classes up
  to inversion.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* P. Roquette, *Analytic theory of elliptic functions over local fields*.
-/

open Filter Topology

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-! ### Weight membership of the coordinate families -/

/-- The coefficient family of `X(u)·θ(-u)²` is a weight-`2` family with multiplier
`Aθ² = ((q·(-1))⁻¹)²`. -/
theorem isWeightFamily_XThetaSq :
    t.IsWeightFamily 2 ((t.q * (-1))⁻¹ ^ 2) t.XThetaSqCoeff := by
  refine isWeightFamily_of_tsum_q_smul_off_orbit t.summable_XThetaSqCoeff_mul_zpow
    fun u hu => ?_
  have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hqu : ∀ n : ℤ, (t.q : K) ^ n * ((t.q * u : Kˣ) : K) ≠ 1 := by
    intro n hcon
    refine hu (n + 1) ?_
    rw [Units.val_mul] at hcon
    rw [zpow_add₀ hq0, zpow_one]
    linear_combination hcon
  have hL : (∑' n : ℤ, t.XThetaSqCoeff n * ((t.q : K) * (u : K)) ^ n)
      = t.X (t.q * u) * t.theta (-(t.q * u)) ^ 2 := by
    rw [← (t.hasSum_XThetaSqCoeff hqu).tsum_eq]
    exact tsum_congr fun n => by rw [Units.val_mul]
  rw [hL, (t.hasSum_XThetaSqCoeff hu).tsum_eq, X_q_smul]
  have hneg : -(t.q * u) = t.q * (-u) := by
    ext
    simp [mul_neg]
  rw [hneg, theta_q_smul, Units.val_neg]
  have hA : (((t.q * (-1))⁻¹ ^ 2 : Kˣ) : K) = ((t.q : K))⁻¹ ^ 2 := by
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mul, Units.val_neg,
      Units.val_one, mul_neg_one, inv_neg, neg_sq]
  have hu2 : (u : K) ^ (-((2 : ℕ) : ℤ)) = ((u : K) ^ 2)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hA, hu2]
  field_simp

/-- The coefficient family of `Y(u)·θ(-u)³` is a weight-`3` family with multiplier
`Aθ³ = ((q·(-1))⁻¹)³`. -/
theorem isWeightFamily_YThetaCube :
    t.IsWeightFamily 3 ((t.q * (-1))⁻¹ ^ 3) t.YThetaCubeCoeff := by
  refine isWeightFamily_of_tsum_q_smul_off_orbit t.summable_YThetaCubeCoeff_mul_zpow
    fun u hu => ?_
  have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hqu : ∀ n : ℤ, (t.q : K) ^ n * ((t.q * u : Kˣ) : K) ≠ 1 := by
    intro n hcon
    refine hu (n + 1) ?_
    rw [Units.val_mul] at hcon
    rw [zpow_add₀ hq0, zpow_one]
    linear_combination hcon
  have hL : (∑' n : ℤ, t.YThetaCubeCoeff n * ((t.q : K) * (u : K)) ^ n)
      = t.Y (t.q * u) * t.theta (-(t.q * u)) ^ 3 := by
    rw [← (t.hasSum_YThetaCubeCoeff hqu).tsum_eq]
    exact tsum_congr fun n => by rw [Units.val_mul]
  rw [hL, (t.hasSum_YThetaCubeCoeff hu).tsum_eq, Y_q_smul]
  have hneg : -(t.q * u) = t.q * (-u) := by
    ext
    simp [mul_neg]
  rw [hneg, theta_q_smul, Units.val_neg]
  have hA : (((t.q * (-1))⁻¹ ^ 3 : Kˣ) : K) = -((t.q : K))⁻¹ ^ 3 := by
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mul, Units.val_neg,
      Units.val_one, mul_neg_one, inv_neg]
    ring
  have hu3 : (u : K) ^ (-((3 : ℕ) : ℤ)) = ((u : K) ^ 3)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [hA, hu3]
  field_simp

/-! ### The line family and its values -/

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Weight families are closed under pointwise subtraction. -/
lemma IsWeightFamily.sub {t : TateParameter K} {k : ℕ} {A : Kˣ} {c d : ℤ → K}
    (hc : t.IsWeightFamily k A c) (hd : t.IsWeightFamily k A d) :
    t.IsWeightFamily k A (c - d) := by
  refine ⟨fun u => ?_, fun n => ?_⟩
  · refine ((hc.summable u).sub (hd.summable u)).congr fun n => ?_
    simp [sub_mul]
  · have h1 := hc.step n
    have h2 := hd.step n
    simp only [Pi.sub_apply]
    linear_combination h1 - h2

/-- The coefficient family of `X(u)·θ(-u)³` — the convolution of the theta block at `-1`
with the `X·θ²` family. -/
def xThetaCubeFam : ℤ → K := fun n => ∑' m : ℤ, t.thetaBlock (-1) (n - m) * t.XThetaSqCoeff m

/-- The coefficient family of `θ(-u)²` — the self-convolution of the theta block at `-1`. -/
def thetaSqFam : ℤ → K := fun n => ∑' m : ℤ, t.thetaBlock (-1) (n - m) * t.thetaBlock (-1) m

/-- The coefficient family of `θ(-u)³`. -/
def thetaCubeFam : ℤ → K := fun n => ∑' m : ℤ, t.thetaBlock (-1) (n - m) * t.thetaSqFam m

/-- The coefficient family of `(Y(u) - λ·X(u) - μ)·θ(-u)³` for the line `y = λx + μ`. -/
def lineFam (lam mu : K) : ℤ → K :=
  fun n => t.YThetaCubeCoeff n - lam * t.xThetaCubeFam n - mu * t.thetaCubeFam n

theorem isWeightFamily_xThetaCubeFam :
    t.IsWeightFamily 3 ((t.q * (-1))⁻¹ ^ 3) t.xThetaCubeFam := by
  have h := (isWeightFamily_thetaBlock (t := t) (-1)).conv t.isWeightFamily_XThetaSq
  rw [show (t.q * (-1))⁻¹ * (t.q * (-1))⁻¹ ^ 2 = (t.q * (-1))⁻¹ ^ 3 from
    (pow_succ' _ 2).symm] at h
  exact h

theorem isWeightFamily_thetaSqFam :
    t.IsWeightFamily 2 ((t.q * (-1))⁻¹ ^ 2) t.thetaSqFam := by
  have h := (isWeightFamily_thetaBlock (t := t) (-1)).conv
    (isWeightFamily_thetaBlock (t := t) (-1))
  rw [show (t.q * (-1))⁻¹ * (t.q * (-1))⁻¹ = (t.q * (-1))⁻¹ ^ 2 from (pow_two _).symm] at h
  exact h

theorem isWeightFamily_thetaCubeFam :
    t.IsWeightFamily 3 ((t.q * (-1))⁻¹ ^ 3) t.thetaCubeFam := by
  have h := (isWeightFamily_thetaBlock (t := t) (-1)).conv t.isWeightFamily_thetaSqFam
  rw [show (t.q * (-1))⁻¹ * (t.q * (-1))⁻¹ ^ 2 = (t.q * (-1))⁻¹ ^ 3 from
    (pow_succ' _ 2).symm] at h
  exact h

/-- The line family lies in the three-dimensional weight space `W 3 (Aθ³)`. -/
theorem isWeightFamily_lineFam (lam mu : K) :
    t.IsWeightFamily 3 ((t.q * (-1))⁻¹ ^ 3) (t.lineFam lam mu) := by
  have h := (t.isWeightFamily_YThetaCube.sub (t.isWeightFamily_xThetaCubeFam.smul lam)).sub
    (t.isWeightFamily_thetaCubeFam.smul mu)
  refine ⟨fun u => (h.summable u).congr fun n => ?_, fun n => ?_⟩
  · simp [lineFam]
  · have hstep := h.step n
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hstep
    simp only [lineFam]
    linear_combination hstep

/-- The series of `thetaSqFam` is `θ(-u)²`, at every unit. -/
lemma hasSum_thetaSqFam (u : Kˣ) :
    HasSum (fun n : ℤ => t.thetaSqFam n * (u : K) ^ n) (t.theta (-u) ^ 2) := by
  have h := (isWeightFamily_thetaBlock (t := t) (-1)).conv_hasSum
    (isWeightFamily_thetaBlock (t := t) (-1)) u
  rw [tsum_thetaBlock, neg_one_mul, ← pow_two] at h
  exact h

/-- The series of `thetaCubeFam` is `θ(-u)³`, at every unit. -/
lemma hasSum_thetaCubeFam (u : Kˣ) :
    HasSum (fun n : ℤ => t.thetaCubeFam n * (u : K) ^ n) (t.theta (-u) ^ 3) := by
  have h := (isWeightFamily_thetaBlock (t := t) (-1)).conv_hasSum
    t.isWeightFamily_thetaSqFam u
  rw [tsum_thetaBlock, neg_one_mul, (t.hasSum_thetaSqFam u).tsum_eq, ← pow_succ'] at h
  exact h

/-- The series of `xThetaCubeFam` is `θ(-u)·(X(u)·θ(-u)²)`, off the orbit. -/
lemma hasSum_xThetaCubeFam {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    HasSum (fun n : ℤ => t.xThetaCubeFam n * (u : K) ^ n)
      (t.theta (-u) * (t.X u * t.theta (-u) ^ 2)) := by
  have h := (isWeightFamily_thetaBlock (t := t) (-1)).conv_hasSum
    t.isWeightFamily_XThetaSq u
  rw [tsum_thetaBlock, neg_one_mul, (t.hasSum_XThetaSqCoeff hu).tsum_eq] at h
  exact h

/-- **The value of the line family**: off the orbit, its series is
`(Y(u) - λ·X(u) - μ)·θ(-u)³`. -/
theorem tsum_lineFam (lam mu : K) {u : Kˣ} (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    (∑' n : ℤ, t.lineFam lam mu n * (u : K) ^ n)
      = (t.Y u - lam * t.X u - mu) * t.theta (-u) ^ 3 := by
  have hY := t.hasSum_YThetaCubeCoeff hu
  have hx := t.hasSum_xThetaCubeFam hu
  have hc := t.hasSum_thetaCubeFam u
  have h := (hY.sub (hx.mul_left lam)).sub (hc.mul_left mu)
  have hfun : (fun n : ℤ => t.YThetaCubeCoeff n * (u : K) ^ n
        - lam * (t.xThetaCubeFam n * (u : K) ^ n)
        - mu * (t.thetaCubeFam n * (u : K) ^ n))
      = fun n : ℤ => t.lineFam lam mu n * (u : K) ^ n := by
    funext n
    simp only [lineFam]
    ring
  rw [hfun] at h
  rw [h.tsum_eq]
  ring

/-! ### Division helpers -/

/-- `θ(-1) = 0`: the point `-1` lies on the zero orbit of the theta function. -/
lemma theta_neg_one : t.theta (-1) = 0 := by
  rw [theta_eq_zero_iff]
  exact ⟨0, by simp⟩

/-- `θ(-x) ≠ 0` for `x` off the orbit `qᶻ`. -/
lemma theta_neg_ne_zero {x : Kˣ} (hx : ∀ n : ℤ, (t.q : K) ^ n * (x : K) ≠ 1) :
    t.theta (-x) ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp h0
  rw [Units.val_neg, neg_inj] at hk
  refine hx (-k) ?_
  rw [hk, ← zpow_add₀ t.q.ne_zero]
  simp

/-- The series of a double theta-block convolution is the product of the two thetas. -/
lemma hasSum_doubleBlock (e₁ e₂ x : Kˣ) :
    HasSum (fun n : ℤ =>
        (∑' m : ℤ, t.thetaBlock e₁ (n - m) * t.thetaBlock e₂ m) * (x : K) ^ n)
      (t.theta (e₁ * x) * t.theta (e₂ * x)) := by
  have h := (isWeightFamily_thetaBlock (t := t) e₁).conv_hasSum
    (isWeightFamily_thetaBlock (t := t) e₂) x
  rwa [tsum_thetaBlock, tsum_thetaBlock] at h

/-- The series of a triple theta-block convolution is the product of the three thetas. -/
lemma hasSum_tripleBlock (e₁ e₂ e₃ x : Kˣ) :
    HasSum (fun n : ℤ => (∑' m : ℤ, t.thetaBlock e₁ (n - m)
        * (∑' j : ℤ, t.thetaBlock e₂ (m - j) * t.thetaBlock e₃ j)) * (x : K) ^ n)
      (t.theta (e₁ * x) * (t.theta (e₂ * x) * t.theta (e₃ * x))) := by
  have h2 := t.hasSum_doubleBlock e₂ e₃ x
  have h := (isWeightFamily_thetaBlock (t := t) e₁).conv_hasSum
    ((isWeightFamily_thetaBlock (t := t) e₂).conv (isWeightFamily_thetaBlock (t := t) e₃)) x
  rwa [tsum_thetaBlock, h2.tsum_eq] at h

/-- If `F` is the convolution of the block at `e` with a weight family `c`, its series
factors as `θ(e·x)` times the series of `c` — the value form of a block division. -/
lemma tsum_eq_theta_mul_of_forall_conv_eq {k : ℕ} {A : Kˣ} {e : Kˣ} {F : ℤ → K}
    (c : t.weightSpace k A)
    (hc : ∀ n : ℤ, (∑' m : ℤ, t.thetaBlock e (n - m) * (c : ℤ → K) m) = F n) (x : Kˣ) :
    (∑' n : ℤ, F n * (x : K) ^ n)
      = t.theta (e * x) * ∑' n : ℤ, (c : ℤ → K) n * (x : K) ^ n := by
  have h := (isWeightFamily_thetaBlock (t := t) e).conv_hasSum c.2 x
  rw [tsum_thetaBlock] at h
  have hfun : (fun n : ℤ =>
      (∑' m : ℤ, t.thetaBlock e (n - m) * (c : ℤ → K) m) * (x : K) ^ n)
      = fun n : ℤ => F n * (x : K) ^ n := funext fun n => by rw [hc n]
  rw [hfun] at h
  exact h.tsum_eq

/-! ### The third-intersection theorem (the Abel step) -/

/-- **The nonarchimedean Abel step.** If the line `y = λx + μ` passes through the Tate
points of `u` and `v` — off-orbit, in distinct `qᶻ`-classes — and `w := (u·v)⁻¹` is
off-orbit, then it passes through the Tate point of `w`. -/
theorem line_third_intersection {u v : Kˣ}
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1)
    (hv : ∀ n : ℤ, (t.q : K) ^ n * (v : K) ≠ 1)
    (hw : ∀ n : ℤ, (t.q : K) ^ n * (((u * v)⁻¹ : Kˣ) : K) ≠ 1)
    (huv : ∀ n : ℤ, (v : K) ≠ (t.q : K) ^ n * (u : K)) {lam mu : K}
    (h1 : t.Y u = lam * t.X u + mu) (h2 : t.Y v = lam * t.X v + mu) :
    t.Y ((u * v)⁻¹) = lam * t.X ((u * v)⁻¹) + mu := by
  classical
  have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hv0 : (v : K) ≠ 0 := v.ne_zero
  set w : Kˣ := (u * v)⁻¹ with hwdef
  set A3 : Kˣ := (t.q * (-1))⁻¹ ^ 3 with hA3
  set A' : Kˣ := (t.q * (-u⁻¹)) * A3 with hA'
  set A'' : Kˣ := (t.q * (-v⁻¹)) * A' with hA''
  -- ### First division, at the block `-u⁻¹`, division point `u`
  have hM1 : (t.q * (-u⁻¹))⁻¹ * A' = A3 := by
    rw [hA', ← mul_assoc, inv_mul_cancel, one_mul]
  have hth1u : t.theta ((-u⁻¹ : Kˣ) * u) = 0 := by
    rw [neg_mul, inv_mul_cancel]
    exact t.theta_neg_one
  -- witness for the first division: a triple of theta blocks off the classes of `u`, `u⁻¹`
  obtain ⟨s, hs⟩ := t.exists_unit_avoiding {u, u⁻¹}
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hs_u : ∀ n : ℤ, (s : K) ≠ (t.q : K) ^ n * (u : K) := fun n => hs u (by simp) n
  have hs_uinv : ∀ n : ℤ, (s : K) ≠ (t.q : K) ^ n * ((u⁻¹ : Kˣ) : K) := fun n =>
    hs u⁻¹ (by simp) n
  have hmul3 : (t.q * (-s⁻¹))⁻¹ * ((t.q * (-s))⁻¹ * (t.q * (-1))⁻¹) = A3 := by
    rw [hA3]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one]
    field_simp
  have hg₁mem : t.IsWeightFamily 3 A3
      (fun n : ℤ => ∑' m : ℤ, t.thetaBlock (-s⁻¹) (n - m)
        * (∑' j : ℤ, t.thetaBlock (-s) (m - j) * t.thetaBlock (-1) j)) := by
    have h := (isWeightFamily_thetaBlock (t := t) (-s⁻¹)).conv
      ((isWeightFamily_thetaBlock (t := t) (-s)).conv (isWeightFamily_thetaBlock (t := t) (-1)))
    rw [hmul3] at h
    exact h
  have hg₁ne : evalAt u 3 A3 (⟨_, hg₁mem⟩ : t.weightSpace 3 A3) ≠ 0 := by
    have hval : evalAt u 3 A3 (⟨_, hg₁mem⟩ : t.weightSpace 3 A3)
        = t.theta (-s⁻¹ * u) * (t.theta (-s * u) * t.theta (-1 * u)) :=
      (t.hasSum_tripleBlock (-s⁻¹) (-s) (-1) u).tsum_eq
    rw [hval]
    refine mul_ne_zero ?_ (mul_ne_zero ?_ ?_)
    · intro h0
      obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp h0
      rw [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val, neg_mul, neg_inj] at hk
      refine hs_u (-k) ?_
      rw [zpow_neg, ← hk, mul_inv, inv_inv, inv_mul_cancel_right₀ hu0]
    · intro h0
      obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp h0
      rw [Units.val_mul, Units.val_neg, neg_mul, neg_inj] at hk
      refine hs_uinv k ?_
      rw [Units.val_inv_eq_inv_val, ← hk, mul_inv_cancel_right₀ hu0]
    · rw [neg_one_mul]
      exact t.theta_neg_ne_zero hu
  have hFu : evalAt u 3 A3
      (⟨t.lineFam lam mu, t.isWeightFamily_lineFam lam mu⟩ : t.weightSpace 3 A3) = 0 := by
    have h : (∑' n : ℤ, t.lineFam lam mu n * (u : K) ^ n) = 0 := by
      rw [t.tsum_lineFam lam mu hu,
        show t.Y u - lam * t.X u - mu = 0 by linear_combination h1, zero_mul]
    exact h
  obtain ⟨c₂, hc₂⟩ := exists_convBlock_eq' (t := t) (k := 2) (A := A')
    (by norm_num) (-u⁻¹) hM1 hth1u (⟨_, hg₁mem⟩ : t.weightSpace 3 A3) hg₁ne
    (⟨t.lineFam lam mu, t.isWeightFamily_lineFam lam mu⟩ : t.weightSpace 3 A3) hFu
  have hc₂' : ∀ n : ℤ, (∑' m : ℤ, t.thetaBlock (-u⁻¹) (n - m) * (c₂ : ℤ → K) m)
      = t.lineFam lam mu n := hc₂
  -- ### Second division, at the block `-v⁻¹`, division point `v`
  have hM2 : (t.q * (-v⁻¹))⁻¹ * A'' = A' := by
    rw [hA'', ← mul_assoc, inv_mul_cancel, one_mul]
  have hth1v : t.theta ((-v⁻¹ : Kˣ) * v) = 0 := by
    rw [neg_mul, inv_mul_cancel]
    exact t.theta_neg_one
  -- the value of `c₂` at `v` vanishes since the line vanishes there and `θ(-u⁻¹·v) ≠ 0`
  have hFv : evalAt v 2 A' c₂ = 0 := by
    have hfac := t.tsum_eq_theta_mul_of_forall_conv_eq c₂ hc₂' v
    have hlv : (∑' n : ℤ, t.lineFam lam mu n * (v : K) ^ n) = 0 := by
      rw [t.tsum_lineFam lam mu hv,
        show t.Y v - lam * t.X v - mu = 0 by linear_combination h2, zero_mul]
    rw [hlv] at hfac
    have hθ : t.theta (-u⁻¹ * v) ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp h0
      rw [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val, neg_mul, neg_inj] at hk
      refine huv k ?_
      rw [← hk, mul_comm ((u : K)⁻¹) ((v : K)), inv_mul_cancel_right₀ hu0]
    exact (mul_eq_zero.mp hfac.symm).resolve_left hθ
  -- witness for the second division: a pair of blocks, second block forced by the multiplier
  obtain ⟨s', hs'⟩ := t.exists_unit_avoiding {v, w}
  have hs'0 : (s' : K) ≠ 0 := s'.ne_zero
  have hs'_v : ∀ n : ℤ, (s' : K) ≠ (t.q : K) ^ n * (v : K) := fun n => hs' v (by simp) n
  have hs'_w : ∀ n : ℤ, (s' : K) ≠ (t.q : K) ^ n * (w : K) := fun n => hs' w (by simp) n
  set e' : Kˣ := (t.q * ((t.q * (-s'⁻¹)) * A'))⁻¹ with he'def
  have hmul2 : (t.q * (-s'⁻¹))⁻¹ * (t.q * e')⁻¹ = A' := by
    rw [he'def, hA', hA3]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one]
    field_simp
  have he'val : ((e' : Kˣ) : K) = -((s' : K) * (u : K)) := by
    rw [he'def, hA', hA3]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one]
    field_simp
  have hg₂mem : t.IsWeightFamily 2 A'
      (fun n : ℤ => ∑' m : ℤ, t.thetaBlock (-s'⁻¹) (n - m) * t.thetaBlock e' m) := by
    have h := (isWeightFamily_thetaBlock (t := t) (-s'⁻¹)).conv
      (isWeightFamily_thetaBlock (t := t) e')
    rw [hmul2] at h
    exact h
  have hwval : ((w : Kˣ) : K) = ((u : K) * (v : K))⁻¹ := by
    rw [hwdef, Units.val_inv_eq_inv_val, Units.val_mul]
  have hg₂ne : evalAt v 2 A' (⟨_, hg₂mem⟩ : t.weightSpace 2 A') ≠ 0 := by
    have hval : evalAt v 2 A' (⟨_, hg₂mem⟩ : t.weightSpace 2 A')
        = t.theta (-s'⁻¹ * v) * t.theta (e' * v) :=
      (t.hasSum_doubleBlock (-s'⁻¹) e' v).tsum_eq
    rw [hval]
    refine mul_ne_zero ?_ ?_
    · intro h0
      obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp h0
      rw [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val, neg_mul, neg_inj] at hk
      refine hs'_v (-k) ?_
      rw [zpow_neg, ← hk, mul_inv, inv_inv, inv_mul_cancel_right₀ hv0]
    · intro h0
      obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp h0
      rw [Units.val_mul, he'val, neg_mul, neg_inj] at hk
      refine hs'_w k ?_
      rw [hwval, ← hk, mul_assoc ((s' : K)) ((u : K)) ((v : K)),
        mul_inv_cancel_right₀ (mul_ne_zero hu0 hv0)]
  obtain ⟨H₁, hH₁⟩ := exists_convBlock_eq' (t := t) (k := 1) (A := A'')
    one_pos (-v⁻¹) hM2 hth1v (⟨_, hg₂mem⟩ : t.weightSpace 2 A') hg₂ne c₂ hFv
  -- ### Classification of the remaining weight-one family and evaluation at `w`
  have he₃w : ((t.q * A'')⁻¹ : Kˣ) * w = -1 := by
    rw [hA'', hA', hA3, hwdef]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one]
    field_simp
  have hH₁w : (∑' n : ℤ, (H₁ : ℤ → K) n * (w : K) ^ n) = 0 := by
    have hcl := w1_eq_smul_thetaBlock (t := t) H₁.2
    calc (∑' n : ℤ, (H₁ : ℤ → K) n * (w : K) ^ n)
        = ∑' n : ℤ, (H₁ : ℤ → K) 0 * (t.thetaBlock ((t.q * A'')⁻¹) n * (w : K) ^ n) := by
          refine tsum_congr fun n => ?_
          conv_lhs => rw [hcl]
          simp [mul_assoc]
      _ = (H₁ : ℤ → K) 0 * t.theta ((t.q * A'')⁻¹ * w) := by
          rw [tsum_mul_left, tsum_thetaBlock]
      _ = 0 := by rw [he₃w, t.theta_neg_one, mul_zero]
  have hc₂w : (∑' n : ℤ, (c₂ : ℤ → K) n * (w : K) ^ n) = 0 := by
    rw [t.tsum_eq_theta_mul_of_forall_conv_eq H₁ hH₁ w, hH₁w, mul_zero]
  have hlw : (∑' n : ℤ, t.lineFam lam mu n * (w : K) ^ n) = 0 := by
    rw [t.tsum_eq_theta_mul_of_forall_conv_eq c₂ hc₂' w, hc₂w, mul_zero]
  rw [t.tsum_lineFam lam mu hw] at hlw
  have hθw : t.theta (-w) ^ 3 ≠ 0 := pow_ne_zero _ (t.theta_neg_ne_zero hw)
  have hzero : t.Y w - lam * t.X w - mu = 0 :=
    (mul_eq_zero.mp hlw).resolve_right hθw
  linear_combination hzero

/-! ### Norm blow-up of `X` along the unit-sphere witnesses -/

omit [CompleteSpace K] in
/-- The norm-one witnesses `1 + qᵏ⁺¹` are off the orbit `qᶻ`. -/
lemma sphereWitness_off_orbit (j : ℕ) :
    ∀ n : ℤ, (t.q : K) ^ n * ((t.sphereWitness j : Kˣ) : K) ≠ 1 := by
  intro n hcontra
  have hnorm : ‖((t.sphereWitness j : Kˣ) : K)‖ = 1 := by
    rw [t.sphereWitness_val]
    exact t.norm_one_add_qpow j
  have h1 := congrArg norm hcontra
  rw [norm_mul, norm_zpow, hnorm, mul_one, norm_one] at h1
  have hq1 : ‖(t.q : K)‖ < 1 := t.norm_lt_one
  have hq0 : 0 < ‖(t.q : K)‖ := t.norm_q_pos
  have hn0 : n = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hmono := zpow_lt_zpow_right_of_lt_one₀ hq0 hq1 hlt
      rw [zpow_zero, h1] at hmono
      exact lt_irrefl _ hmono
    · have hmono := zpow_lt_zpow_right_of_lt_one₀ hq0 hq1 hgt
      rw [zpow_zero, h1] at hmono
      exact lt_irrefl _ hmono
  rw [hn0, zpow_zero, one_mul, t.sphereWitness_val] at hcontra
  have hz : (t.q : K) ^ (j + 1) = 0 := by linear_combination hcontra
  exact pow_ne_zero (j + 1) t.q.ne_zero hz

/-- **Norm blow-up of `X`**: `‖X(1 + qᵏ⁺¹)‖ = ‖q‖⁻²⁽ᵏ⁺¹⁾`. The `n = 0` term of the `X`-series
has this huge norm, and everything else (`n ≠ 0` terms, the Eisenstein constant) has norm at
most `1`. -/
lemma norm_X_sphereWitness (k : ℕ) :
    ‖t.X (t.sphereWitness k)‖ = ‖(t.q : K)‖⁻¹ ^ (2 * (k + 1)) := by
  classical
  set w : Kˣ := t.sphereWitness k with hwdef
  have hqn : 0 < ‖(t.q : K)‖ := t.norm_q_pos
  have hq1 : ‖(t.q : K)‖ < 1 := t.norm_lt_one
  have hwv : (w : K) = 1 + (t.q : K) ^ (k + 1) := t.sphereWitness_val k
  have hwn : ‖(w : K)‖ = 1 := by
    rw [hwv]
    exact t.norm_one_add_qpow k
  -- the `n = 0` term
  have hterm0 : ‖t.Xterm w 0‖ = ‖(t.q : K)‖⁻¹ ^ (2 * (k + 1)) := by
    have hden : ((1 : K) - (t.q : K) ^ (0 : ℤ) * (w : K)) = -((t.q : K) ^ (k + 1)) := by
      rw [zpow_zero, one_mul, hwv]
      ring
    rw [Xterm_apply, hden, norm_div, norm_mul, norm_zpow, zpow_zero, hwn, mul_one, norm_pow,
      norm_neg, norm_pow, ← pow_mul, one_div, ← inv_pow]
    ring
  -- the `n ≠ 0` terms have norm at most `1`
  have htail : ∀ n : ℤ, n ≠ 0 → ‖t.Xterm w n‖ ≤ 1 := by
    intro n hn
    have hxnorm : ‖(t.q : K) ^ n * (w : K)‖ = ‖(t.q : K)‖ ^ n := by
      rw [norm_mul, norm_zpow, hwn, mul_one]
    have hne1 : ‖(t.q : K) ^ n * (w : K)‖ ≠ 1 := by
      rw [hxnorm]
      intro hcon
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · have hmono := zpow_lt_zpow_right_of_lt_one₀ hqn hq1 hlt
        rw [zpow_zero, hcon] at hmono
        exact lt_irrefl _ hmono
      · have hmono := zpow_lt_zpow_right_of_lt_one₀ hqn hq1 hgt
        rw [zpow_zero, hcon] at hmono
        exact lt_irrefl _ hmono
    have hmax1 : (1 : ℝ) ≤ max 1 ‖(t.q : K) ^ n * (w : K)‖ := le_max_left _ _
    rw [Xterm_apply, norm_div, norm_pow, norm_one_sub_of_norm_ne_one hne1,
      div_le_one (pow_pos (lt_of_lt_of_le one_pos hmax1) 2)]
    calc ‖(t.q : K) ^ n * (w : K)‖
        ≤ max 1 ‖(t.q : K) ^ n * (w : K)‖ := le_max_right _ _
      _ = max 1 ‖(t.q : K) ^ n * (w : K)‖ * 1 := (mul_one _).symm
      _ ≤ max 1 ‖(t.q : K) ^ n * (w : K)‖ * max 1 ‖(t.q : K) ^ n * (w : K)‖ := by
          gcongr
      _ = (max 1 ‖(t.q : K) ^ n * (w : K)‖) ^ 2 := (pow_two _).symm
  -- split the series and bound the remainder
  have hsplit : (∑' n : ℤ, t.Xterm w n)
      = t.Xterm w 0 + ∑' n : ℤ, if n = 0 then 0 else t.Xterm w n :=
    (t.Xterm_summable w).tsum_eq_add_tsum_ite 0
  have hrest : ‖(∑' n : ℤ, if n = 0 then 0 else t.Xterm w n) - 2 * t.eisenstein 1‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun n => ?_
      by_cases hn : n = 0
      · simp [hn]
      · rw [if_neg hn]
        exact htail n hn
    · rw [norm_neg]
      have h2 : ‖(2 : K)‖ ≤ 1 := by
        have h := IsUltrametricDist.norm_natCast_le_one K 2
        rwa [Nat.cast_ofNat] at h
      calc ‖2 * t.eisenstein 1‖ = ‖(2 : K)‖ * ‖t.eisenstein 1‖ := norm_mul _ _
        _ ≤ 1 * 1 := mul_le_mul h2 (t.norm_eisenstein_le_one 1) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  -- assemble via the isosceles law
  have hX : t.X w = t.Xterm w 0
      + ((∑' n : ℤ, if n = 0 then 0 else t.Xterm w n) - 2 * t.eisenstein 1) := by
    rw [X_apply, hsplit]
    ring
  have hbig : (1 : ℝ) < ‖(t.q : K)‖⁻¹ ^ (2 * (k + 1)) :=
    one_lt_pow₀ ((one_lt_inv₀ hqn).mpr hq1) (by omega)
  have hne : ‖t.Xterm w 0‖
      ≠ ‖(∑' n : ℤ, if n = 0 then 0 else t.Xterm w n) - 2 * t.eisenstein 1‖ := by
    rw [hterm0]
    exact ne_of_gt (lt_of_le_of_lt hrest hbig)
  rw [hX, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hterm0,
    max_eq_left (hrest.trans hbig.le)]

/-! ### `X`-separation -/

/-- **The `X`-coordinate separates `qᶻ`-classes up to inversion.** If two off-orbit units
have the same `X`-value, they lie in the same `qᶻ`-class or in mutually inverse classes. -/
theorem class_eq_or_inv_of_X_eq {a b : Kˣ}
    (ha : ∀ n : ℤ, (t.q : K) ^ n * (a : K) ≠ 1)
    (hb : ∀ n : ℤ, (t.q : K) ^ n * (b : K) ≠ 1)
    (hX : t.X a = t.X b) :
    (∃ k : ℤ, (a : K) = (t.q : K) ^ k * (b : K))
      ∨ ∃ k : ℤ, (a : K) = (t.q : K) ^ k * ((b⁻¹ : Kˣ) : K) := by
  classical
  have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
  have hb0 : (b : K) ≠ 0 := b.ne_zero
  set A2 : Kˣ := (t.q * (-1))⁻¹ ^ 2 with hA2
  set A₁ : Kˣ := (t.q * (-b⁻¹)) * A2 with hA₁
  -- the difference family `G := XΘ² - X(b)·Θ²` lies in `W 2 (Aθ²)`
  have hGmem : t.IsWeightFamily 2 A2
      (fun n : ℤ => t.XThetaSqCoeff n - t.X b * t.thetaSqFam n) :=
    t.isWeightFamily_XThetaSq.sub (t.isWeightFamily_thetaSqFam.smul (t.X b))
  have hGval : ∀ x : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (x : K) ≠ 1) →
      (∑' n : ℤ, (t.XThetaSqCoeff n - t.X b * t.thetaSqFam n) * (x : K) ^ n)
        = (t.X x - t.X b) * t.theta (-x) ^ 2 := by
    intro x hx
    have h := (t.hasSum_XThetaSqCoeff hx).sub ((t.hasSum_thetaSqFam x).mul_left (t.X b))
    have hfun : (fun n : ℤ => t.XThetaSqCoeff n * (x : K) ^ n
        - t.X b * (t.thetaSqFam n * (x : K) ^ n))
        = fun n : ℤ => (t.XThetaSqCoeff n - t.X b * t.thetaSqFam n) * (x : K) ^ n := by
      funext n
      ring
    rw [hfun] at h
    rw [h.tsum_eq]
    ring
  -- one division at the block `-b⁻¹`, division point `b`
  have hM : (t.q * (-b⁻¹))⁻¹ * A₁ = A2 := by
    rw [hA₁, ← mul_assoc, inv_mul_cancel, one_mul]
  have hth1b : t.theta ((-b⁻¹ : Kˣ) * b) = 0 := by
    rw [neg_mul, inv_mul_cancel]
    exact t.theta_neg_one
  have hFb : evalAt b 2 A2 (⟨_, hGmem⟩ : t.weightSpace 2 A2) = 0 := by
    have h : (∑' n : ℤ, (t.XThetaSqCoeff n - t.X b * t.thetaSqFam n) * (b : K) ^ n) = 0 := by
      rw [hGval b hb, sub_self, zero_mul]
    exact h
  -- witness: a pair of blocks off the classes of `b`, `b⁻¹`
  obtain ⟨s, hs⟩ := t.exists_unit_avoiding {b, b⁻¹}
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hs_b : ∀ n : ℤ, (s : K) ≠ (t.q : K) ^ n * (b : K) := fun n => hs b (by simp) n
  have hs_binv : ∀ n : ℤ, (s : K) ≠ (t.q : K) ^ n * ((b⁻¹ : Kˣ) : K) := fun n =>
    hs b⁻¹ (by simp) n
  set e'' : Kˣ := (t.q * ((t.q * (-s⁻¹)) * A2))⁻¹ with he''def
  have hmul2 : (t.q * (-s⁻¹))⁻¹ * (t.q * e'')⁻¹ = A2 := by
    rw [he''def, hA2]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one]
    field_simp
  have he''val : ((e'' : Kˣ) : K) = -(s : K) := by
    rw [he''def, hA2]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one]
    field_simp
  have hgmem : t.IsWeightFamily 2 A2
      (fun n : ℤ => ∑' m : ℤ, t.thetaBlock (-s⁻¹) (n - m) * t.thetaBlock e'' m) := by
    have h := (isWeightFamily_thetaBlock (t := t) (-s⁻¹)).conv
      (isWeightFamily_thetaBlock (t := t) e'')
    rw [hmul2] at h
    exact h
  have hgne : evalAt b 2 A2 (⟨_, hgmem⟩ : t.weightSpace 2 A2) ≠ 0 := by
    have hval : evalAt b 2 A2 (⟨_, hgmem⟩ : t.weightSpace 2 A2)
        = t.theta (-s⁻¹ * b) * t.theta (e'' * b) :=
      (t.hasSum_doubleBlock (-s⁻¹) e'' b).tsum_eq
    rw [hval]
    refine mul_ne_zero ?_ ?_
    · intro h0
      obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp h0
      rw [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val, neg_mul, neg_inj] at hk
      refine hs_b (-k) ?_
      rw [zpow_neg, ← hk, mul_inv, inv_inv, inv_mul_cancel_right₀ hb0]
    · intro h0
      obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp h0
      rw [Units.val_mul, he''val, neg_mul, neg_inj] at hk
      refine hs_binv k ?_
      rw [Units.val_inv_eq_inv_val, ← hk, mul_inv_cancel_right₀ hb0]
  obtain ⟨H₁, hH₁⟩ := exists_convBlock_eq' (t := t) (k := 1) (A := A₁)
    one_pos (-b⁻¹) hM hth1b (⟨_, hgmem⟩ : t.weightSpace 2 A2) hgne
    (⟨_, hGmem⟩ : t.weightSpace 2 A2) hFb
  have hH₁' : ∀ n : ℤ, (∑' m : ℤ, t.thetaBlock (-b⁻¹) (n - m) * (H₁ : ℤ → K) m)
      = t.XThetaSqCoeff n - t.X b * t.thetaSqFam n := hH₁
  -- classify the weight-one quotient and compute its block point: `e₄ = -b`
  have hcl := w1_eq_smul_thetaBlock (t := t) H₁.2
  have he₄val : (((t.q * A₁)⁻¹ : Kˣ) : K) = -(b : K) := by
    rw [hA₁, hA2]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one]
    field_simp
  have hH₁ser : ∀ x : Kˣ, (∑' n : ℤ, (H₁ : ℤ → K) n * (x : K) ^ n)
      = (H₁ : ℤ → K) 0 * t.theta ((t.q * A₁)⁻¹ * x) := by
    intro x
    calc (∑' n : ℤ, (H₁ : ℤ → K) n * (x : K) ^ n)
        = ∑' n : ℤ, (H₁ : ℤ → K) 0 * (t.thetaBlock ((t.q * A₁)⁻¹) n * (x : K) ^ n) := by
          refine tsum_congr fun n => ?_
          conv_lhs => rw [hcl]
          simp [mul_assoc]
      _ = (H₁ : ℤ → K) 0 * t.theta ((t.q * A₁)⁻¹ * x) := by
          rw [tsum_mul_left, tsum_thetaBlock]
  have hGfac : ∀ x : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (x : K) ≠ 1) →
      (t.X x - t.X b) * t.theta (-x) ^ 2
        = t.theta (-b⁻¹ * x) * ((H₁ : ℤ → K) 0 * t.theta ((t.q * A₁)⁻¹ * x)) := by
    intro x hx
    rw [← hGval x hx, t.tsum_eq_theta_mul_of_forall_conv_eq H₁ hH₁' x, hH₁ser x]
  by_cases hH0 : (H₁ : ℤ → K) 0 = 0
  · -- degenerate case: `X` would be constant off the orbit — norm blow-up forbids it
    exfalso
    have hconst : ∀ x : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (x : K) ≠ 1) → t.X x = t.X b := by
      intro x hx
      have h := hGfac x hx
      rw [hH0, zero_mul, mul_zero] at h
      have hθ : t.theta (-x) ^ 2 ≠ 0 := pow_ne_zero _ (t.theta_neg_ne_zero hx)
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hθ)
    have h0 := hconst (t.sphereWitness 0) (t.sphereWitness_off_orbit 0)
    have h1 := hconst (t.sphereWitness 1) (t.sphereWitness_off_orbit 1)
    have hn0 := t.norm_X_sphereWitness 0
    have hn1 := t.norm_X_sphereWitness 1
    rw [h0] at hn0
    rw [h1] at hn1
    have hlt : ‖(t.q : K)‖⁻¹ ^ (2 * (0 + 1)) < ‖(t.q : K)‖⁻¹ ^ (2 * (1 + 1)) :=
      pow_lt_pow_right₀ ((one_lt_inv₀ t.norm_q_pos).mpr t.norm_lt_one) (by norm_num)
    rw [← hn0, ← hn1] at hlt
    exact lt_irrefl _ hlt
  · -- nondegenerate case: one of the two theta factors vanishes at `a`
    have h := hGfac a ha
    rw [hX, sub_self, zero_mul] at h
    rcases mul_eq_zero.mp h.symm with hz | hz
    · left
      obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp hz
      rw [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val, neg_mul, neg_inj] at hk
      refine ⟨k, ?_⟩
      rw [← hk, mul_comm ((b : K)⁻¹) ((a : K)), inv_mul_cancel_right₀ hb0]
    · rcases mul_eq_zero.mp hz with hz' | hz'
      · exact absurd hz' hH0
      · right
        obtain ⟨k, hk⟩ := (t.theta_eq_zero_iff _).mp hz'
        rw [Units.val_mul, he₄val, neg_mul, neg_inj] at hk
        refine ⟨k, ?_⟩
        rw [Units.val_inv_eq_inv_val, ← hk, mul_comm ((b : K)) ((a : K)),
          mul_inv_cancel_right₀ hb0]

end TateParameter

end TateCurvesTheta
