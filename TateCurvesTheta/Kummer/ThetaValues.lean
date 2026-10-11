/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.ZHat
import ContinuousKummerTheory.Kummer.Restriction
import TateCurvesTheta.Theta.Durfee
import TateCurvesTheta.Theta.Inversion
import TateCurvesTheta.QParameter.BaseChange

/-!
# Kummer classes of theta values

Let `q` be a Tate parameter over a complete non-archimedean field `K` and
`θ(u) = ∑ₙ q^{e(n)} uⁿ` (`e(n) = n(n+1)/2`) the theta function of `Theta/Basic.lean`. Off its
divisor `-qᶻ` (`theta_eq_zero_iff`) the value `θ(u)` is a unit of `K`
(`TateParameter.thetaUnit`), so it has Kummer classes

* `κ_n(θ(u)) = kummer n K Ω (thetaUnit u) ∈ H¹_cont(Gal(Ω/K), μ_n)`, and
* `κ_Ẑ(θ(u)) = kummerZHat K Ω (thetaUnit u) ∈ H¹_cont(G_K, Ẑ(1))`

(`continuous-kummer-theory`). This file records the relations between these classes coming
from the functional equations of `θ`. They are proved once in `Kˣ` and then transported along
an arbitrary homomorphism `φ : Kˣ →* G` into a commutative group (`map_thetaUnit_*`), which is
then specialised to `kummer n K Ω` and `kummerZHat K Ω`.

## Main results

* `thetaUnit_zpow_q_smul`, `kummer_thetaUnit_zpow_q_smul`: the `qᶻ`-translates,
  `κ(θ(qᵐu)) = κ(q)^{-e(m)} · κ(u)^{-m} · κ(θ(u))`.
* `thetaUnit_inv`, `kummer_thetaUnit_inv`: inversion, `κ(θ(u⁻¹)) = κ(u) · κ(θ(u))`.
* `theta_sqrt_ne_zero`, `theta_sqrt_zpow`, `kummer_thetaUnit_sqrt`,
  `kummerZHat_thetaUnit_sqrt`: for a square root `s` of `q` in `K` the points `s^{2j-1}` (the
  points `√q^{2j-1}`, i.e. `qʲ · q^{-1/2}`, of [EtTh, §1]) are never zeros of `θ`, and
  `θ(s^{2j-1}) = s^{-j²} · θ(s⁻¹)`, so
  `κ(θ(s^{2j-1})) = κ(s)^{-j²} · κ(θ(s⁻¹))`: up to the common class `κ(θ(s⁻¹))`, the Kummer
  classes of these theta values are those of `q^{-j²/2}`.
* `algebraMap_theta`, `restriction_kummer_thetaUnit`: `θ` commutes with base change along an
  extension of valued fields `L/K`, hence the restriction to `G_L` of `κ_K(θ(u))` is
  `κ_L(θ(u))`.

## References

* S. Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations*, §1.
-/

noncomputable section

open KummerTheory

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] (t : TateParameter K)

/-! ### Theta values as units -/

/-- The value `θ(u)` as a unit of `K`, for `u` off the divisor of `θ`. -/
def thetaUnit (u : Kˣ) (hu : t.theta u ≠ 0) : Kˣ := Units.mk0 (t.theta u) hu

@[simp]
lemma coe_thetaUnit (u : Kˣ) (hu : t.theta u ≠ 0) : (t.thetaUnit u hu : K) = t.theta u := rfl

/-- The automorphy factor `q^{e(m)} · uᵐ` of the `qᶻ`-translation, as a unit. -/
def thetaFactor (u : Kˣ) (m : ℤ) : Kˣ := t.q ^ thetaExp m * u ^ m

lemma coe_thetaFactor (u : Kˣ) (m : ℤ) :
    (t.thetaFactor u m : K) = (t.q : K) ^ thetaExp m * (u : K) ^ m := by
  simp [thetaFactor, Units.val_zpow_eq_zpow_val]

lemma theta_zpow_q_smul_ne_zero (u : Kˣ) (m : ℤ) (hu : t.theta u ≠ 0) :
    t.theta (t.q ^ m * u) ≠ 0 := by
  rw [theta_zpow_q_smul, ← coe_thetaFactor]
  exact mul_ne_zero (inv_ne_zero (t.thetaFactor u m).ne_zero) hu

/-- **`qᶻ`-translation of theta values**: `θ(qᵐu) = (q^{e(m)} uᵐ)⁻¹ · θ(u)` in `Kˣ`. -/
theorem thetaUnit_zpow_q_smul (u : Kˣ) (m : ℤ) (hu : t.theta u ≠ 0) :
    t.thetaUnit (t.q ^ m * u) (t.theta_zpow_q_smul_ne_zero u m hu) =
      (t.thetaFactor u m)⁻¹ * t.thetaUnit u hu := by
  ext
  simp [theta_zpow_q_smul, ← coe_thetaFactor]

lemma theta_inv_ne_zero (u : Kˣ) (hu : t.theta u ≠ 0) : t.theta u⁻¹ ≠ 0 := by
  rw [theta_inv]
  exact mul_ne_zero u.ne_zero hu

/-- **Inversion of theta values**: `θ(u⁻¹) = u · θ(u)` in `Kˣ`. -/
theorem thetaUnit_inv (u : Kˣ) (hu : t.theta u ≠ 0) :
    t.thetaUnit u⁻¹ (t.theta_inv_ne_zero u hu) = u * t.thetaUnit u hu := by
  ext
  simp [theta_inv]

/-! ### Theta values at the half-period points `√q^{2j-1}` -/

section Sqrt

variable {s : Kˣ}

/-- If `s² = q`, the points `s^{2j-1}` are never zeros of `θ` (they are not in `-qᶻ`). -/
theorem theta_sqrt_ne_zero [CompleteSpace K] [IsUltrametricDist K] (hs : s ^ 2 = t.q) (j : ℤ) :
    t.theta (s ^ (2 * j - 1)) ≠ 0 := by
  rw [Ne, theta_eq_zero_iff]
  rintro ⟨k, hk⟩
  have hsq : ((s : K) ^ 2) = t.q := by rw [← Units.val_pow_eq_pow_val, hs]
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
  have hk' : (s : K) ^ (2 * j - 1) = -(t.q : K) ^ k := by
    rw [← Units.val_zpow_eq_zpow_val, hk]
  have h3 : (t.q : K) ^ (2 * j - 1) = (t.q : K) ^ (2 * k) := by
    have e1 : ((s : K) ^ 2) ^ (2 * j - 1) = ((s : K) ^ (2 * j - 1)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have e2 : ((t.q : K) ^ k) ^ 2 = (t.q : K) ^ (2 * k) := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
      norm_cast
    rw [← hsq, e1, hk', neg_sq, hsq, e2]
  have h4 : (t.q : K) ^ (2 * j - 1 - 2 * k) = 1 := by
    rw [zpow_sub₀ hq0, h3, div_self (zpow_ne_zero _ hq0)]
  exact t.zpow_ne_one (by omega) h4

/-- The half-period points are `qᶻ`-translates of `s⁻¹`: `s^{2j-1} = qʲ · s⁻¹`. -/
lemma sqrt_zpow_eq (hs : s ^ 2 = t.q) (j : ℤ) : s ^ (2 * j - 1) = t.q ^ j * s⁻¹ := by
  rw [← hs, ← zpow_natCast, ← zpow_mul, ← zpow_neg_one, ← zpow_add]
  congr 1

/-- The automorphy factor at `s⁻¹` is `s^{j²}`: `q^{e(j)} · s^{-j} = s^{j(j+1)-j}`. -/
lemma thetaFactor_sqrt_inv (hs : s ^ 2 = t.q) (j : ℤ) : t.thetaFactor s⁻¹ j = s ^ (j ^ 2) := by
  rw [thetaFactor, ← hs, ← zpow_natCast, ← zpow_mul, ← zpow_neg_one, ← zpow_mul, ← zpow_add]
  congr 1
  have := two_mul_thetaExp j
  push_cast
  linear_combination this

/-- **Theta values at `√q^{2j-1}`**: `θ(s^{2j-1}) = s^{-j²} · θ(s⁻¹)`, the theta values are
`q^{-j²/2}` up to the common factor `θ(q^{-1/2})`. -/
theorem theta_sqrt_zpow (hs : s ^ 2 = t.q) (j : ℤ) :
    t.theta (s ^ (2 * j - 1)) = (s : K) ^ (-j ^ 2) * t.theta s⁻¹ := by
  rw [t.sqrt_zpow_eq hs j, theta_zpow_q_smul, ← coe_thetaFactor, t.thetaFactor_sqrt_inv hs j,
    Units.val_zpow_eq_zpow_val, ← zpow_neg]

/-- Unit form of `theta_sqrt_zpow`. -/
theorem thetaUnit_sqrt_zpow [CompleteSpace K] [IsUltrametricDist K] (hs : s ^ 2 = t.q) (j : ℤ) :
    t.thetaUnit (s ^ (2 * j - 1)) (t.theta_sqrt_ne_zero hs j) =
      s ^ (-j ^ 2) * t.thetaUnit s⁻¹ (by simpa using t.theta_sqrt_ne_zero hs 0) := by
  ext
  simp [t.theta_sqrt_zpow hs j, Units.val_zpow_eq_zpow_val]

end Sqrt

/-! ### Transport along homomorphisms (e.g. Kummer maps) -/

section Hom

variable {G : Type*} [CommGroup G] (φ : Kˣ →* G)

theorem map_thetaUnit_zpow_q_smul (u : Kˣ) (m : ℤ) (hu : t.theta u ≠ 0) :
    φ (t.thetaUnit (t.q ^ m * u) (t.theta_zpow_q_smul_ne_zero u m hu)) =
      φ t.q ^ (-thetaExp m) * φ u ^ (-m) * φ (t.thetaUnit u hu) := by
  rw [thetaUnit_zpow_q_smul, map_mul, map_inv, thetaFactor, map_mul, map_zpow, map_zpow,
    mul_inv, zpow_neg, zpow_neg]

theorem map_thetaUnit_inv (u : Kˣ) (hu : t.theta u ≠ 0) :
    φ (t.thetaUnit u⁻¹ (t.theta_inv_ne_zero u hu)) = φ u * φ (t.thetaUnit u hu) := by
  rw [thetaUnit_inv, map_mul]

theorem map_thetaUnit_sqrt_zpow [CompleteSpace K] [IsUltrametricDist K] {s : Kˣ}
    (hs : s ^ 2 = t.q) (j : ℤ) :
    φ (t.thetaUnit (s ^ (2 * j - 1)) (t.theta_sqrt_ne_zero hs j)) =
      φ s ^ (-j ^ 2) * φ (t.thetaUnit s⁻¹ (by simpa using t.theta_sqrt_ne_zero hs 0)) := by
  rw [t.thetaUnit_sqrt_zpow hs j, map_mul, map_zpow]

end Hom

/-! ### Kummer classes of theta values -/

section Kummer

variable (n : ℕ) (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra.IsIntegral K Ω]
  [HasKummerRoots n K Ω]

/-- **Kummer classes of `qᶻ`-translates of theta values**:
`κ(θ(qᵐu)) = κ(q)^{-e(m)} · κ(u)^{-m} · κ(θ(u))` in `H¹_cont(Gal(Ω/K), μ_n)`. -/
theorem kummer_thetaUnit_zpow_q_smul (u : Kˣ) (m : ℤ) (hu : t.theta u ≠ 0) :
    kummer n K Ω (t.thetaUnit (t.q ^ m * u) (t.theta_zpow_q_smul_ne_zero u m hu)) =
      kummer n K Ω t.q ^ (-thetaExp m) * kummer n K Ω u ^ (-m) *
        kummer n K Ω (t.thetaUnit u hu) :=
  t.map_thetaUnit_zpow_q_smul _ u m hu

/-- **Kummer class of the `q`-translate** (`m = 1`): `κ(θ(qu)) = κ(q)⁻¹ · κ(u)⁻¹ · κ(θ(u))`. -/
theorem kummer_thetaUnit_q_smul (u : Kˣ) (hu : t.theta u ≠ 0) :
    kummer n K Ω (t.thetaUnit (t.q ^ (1 : ℤ) * u) (t.theta_zpow_q_smul_ne_zero u 1 hu)) =
      (kummer n K Ω t.q)⁻¹ * (kummer n K Ω u)⁻¹ * kummer n K Ω (t.thetaUnit u hu) := by
  rw [kummer_thetaUnit_zpow_q_smul, thetaExp_one, zpow_neg_one, zpow_neg_one]

/-- **Kummer class under inversion**: `κ(θ(u⁻¹)) = κ(u) · κ(θ(u))`. -/
theorem kummer_thetaUnit_inv (u : Kˣ) (hu : t.theta u ≠ 0) :
    kummer n K Ω (t.thetaUnit u⁻¹ (t.theta_inv_ne_zero u hu)) =
      kummer n K Ω u * kummer n K Ω (t.thetaUnit u hu) :=
  t.map_thetaUnit_inv _ u hu

/-- **Kummer classes of the theta values at `√q^{2j-1}`**:
`κ(θ(s^{2j-1})) = κ(s)^{-j²} · κ(θ(s⁻¹))` for `s² = q`. -/
theorem kummer_thetaUnit_sqrt [CompleteSpace K] [IsUltrametricDist K] {s : Kˣ}
    (hs : s ^ 2 = t.q) (j : ℤ) :
    kummer n K Ω (t.thetaUnit (s ^ (2 * j - 1)) (t.theta_sqrt_ne_zero hs j)) =
      kummer n K Ω s ^ (-j ^ 2) *
        kummer n K Ω (t.thetaUnit s⁻¹ (by simpa using t.theta_sqrt_ne_zero hs 0)) :=
  t.map_thetaUnit_sqrt_zpow _ hs j

end Kummer

section KummerZHat

variable (Ω : Type*) [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]

/-- `Ẑ(1)`-form of `kummer_thetaUnit_zpow_q_smul`, in `H¹_cont(G_K, Ẑ(1))`. -/
theorem kummerZHat_thetaUnit_zpow_q_smul (u : Kˣ) (m : ℤ) (hu : t.theta u ≠ 0) :
    kummerZHat K Ω (t.thetaUnit (t.q ^ m * u) (t.theta_zpow_q_smul_ne_zero u m hu)) =
      kummerZHat K Ω t.q ^ (-thetaExp m) * kummerZHat K Ω u ^ (-m) *
        kummerZHat K Ω (t.thetaUnit u hu) :=
  t.map_thetaUnit_zpow_q_smul _ u m hu

/-- `Ẑ(1)`-form of `kummer_thetaUnit_inv`. -/
theorem kummerZHat_thetaUnit_inv (u : Kˣ) (hu : t.theta u ≠ 0) :
    kummerZHat K Ω (t.thetaUnit u⁻¹ (t.theta_inv_ne_zero u hu)) =
      kummerZHat K Ω u * kummerZHat K Ω (t.thetaUnit u hu) :=
  t.map_thetaUnit_inv _ u hu

/-- `Ẑ(1)`-form of `kummer_thetaUnit_sqrt`: in `H¹_cont(G_K, Ẑ(1))`,
`κ(θ(s^{2j-1})) = κ(s)^{-j²} · κ(θ(s⁻¹))`. -/
theorem kummerZHat_thetaUnit_sqrt [CompleteSpace K] [IsUltrametricDist K] {s : Kˣ}
    (hs : s ^ 2 = t.q) (j : ℤ) :
    kummerZHat K Ω (t.thetaUnit (s ^ (2 * j - 1)) (t.theta_sqrt_ne_zero hs j)) =
      kummerZHat K Ω s ^ (-j ^ 2) *
        kummerZHat K Ω (t.thetaUnit s⁻¹ (by simpa using t.theta_sqrt_ne_zero hs 0)) :=
  t.map_thetaUnit_sqrt_zpow _ hs j

/-- The components of `κ_Ẑ(θ(u))` are the classes `κ_n(θ(u))`. -/
theorem h1Proj_kummerZHat_thetaUnit (i : KummerIndex K) (u : Kˣ) (hu : t.theta u ≠ 0) :
    h1Proj K Ω i (kummerZHat K Ω (t.thetaUnit u hu)) = kummer i.n K Ω (t.thetaUnit u hu) :=
  h1Proj_kummerZHat K Ω i _

end KummerZHat

/-! ### Base change and restriction -/

section BaseChange

variable [CompleteSpace K] [IsUltrametricDist K] (L : Type*) [NormedField L] [NormedAlgebra K L]

/-- **`θ` commutes with base change** along an extension of valued fields `L/K`:
`θ_{q}(u)` maps to `θ_{q_L}(u_L)`. -/
theorem algebraMap_theta (u : Kˣ) :
    algebraMap K L (t.theta u) =
      (t.baseChange L).theta (Units.map (algebraMap K L : K →* L) u) := by
  have h := (t.thetaTerm_summable u).hasSum.map (algebraMap K L) (continuous_algebraMap K L)
  rw [theta]
  refine (HasSum.tsum_eq ?_).symm
  convert h using 1
  funext k
  simp [thetaTerm, Function.comp_apply, map_zpow₀]

lemma theta_baseChange_ne_zero (u : Kˣ) (hu : t.theta u ≠ 0) :
    (t.baseChange L).theta (Units.map (algebraMap K L : K →* L) u) ≠ 0 := by
  rw [← algebraMap_theta]
  exact (map_ne_zero _).2 hu

/-- Unit form of `algebraMap_theta`. -/
theorem map_thetaUnit (u : Kˣ) (hu : t.theta u ≠ 0) :
    Units.map (algebraMap K L : K →* L) (t.thetaUnit u hu) =
      (t.baseChange L).thetaUnit _ (t.theta_baseChange_ne_zero L u hu) := by
  ext
  simp [algebraMap_theta]

variable (n : ℕ) (ΩK ΩL : Type*) [Field ΩK] [Field ΩL] [Algebra K ΩK] [Algebra L ΩL]
  [Algebra K ΩL] [IsScalarTower K L ΩL] [Algebra ΩK ΩL] [IsScalarTower K ΩK ΩL] [Normal K ΩK]
  [Algebra.IsIntegral K ΩK] [Algebra.IsIntegral L ΩL] [HasKummerRoots n K ΩK]
  [HasKummerRoots n L ΩL]

/-- **Restriction of Kummer classes of theta values**: the restriction to `Gal(Ω_L/L)` of
`κ_K(θ(u))` is the Kummer class over `L` of the theta value of the base-changed Tate parameter
at the image of `u`. -/
theorem restriction_kummer_thetaUnit (u : Kˣ) (hu : t.theta u ≠ 0) :
    restriction K L ΩK ΩL n (kummer n K ΩK (t.thetaUnit u hu)) =
      kummer n L ΩL ((t.baseChange L).thetaUnit _ (t.theta_baseChange_ne_zero L u hu)) := by
  rw [restriction_kummer, map_thetaUnit]

end BaseChange

end TateParameter

end TateCurvesTheta
