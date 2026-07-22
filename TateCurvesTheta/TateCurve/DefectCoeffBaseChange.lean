/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.AdjoinRoot
import TateCurvesTheta.QParameter.BaseChange
import TateCurvesTheta.TateCurve.TatePointOnCurve

/-!
# The Eisenstein pole-cancellation identity, unconditionally (quadratic base change)

Over a complete nonarchimedean field `K`, the coefficient-level Eisenstein identity
`TateParameter.defectAnnulusCoeff_eq_zero` (`TateCurve/TatePointOnCurve.lean`, #169) was proved
under the hypothesis that the fundamental annulus `1 < ‖u‖ < ‖q‖⁻¹` of `K` is **nonempty** — a
genuine restriction: for `K = ℚₚ` with `q` a uniformizer the value group is `‖q‖^ℤ` and the
annulus is empty. This file removes that hypothesis.

## The mechanism

The coefficients `defectAnnulusCoeff` are `q`-power series identities, so they are insensitive
to isometric base change. We adjoin a square root `π` of `q`:

* if `q` is already a square in `K`, the annulus of `K` itself is nonempty (`‖s⁻¹‖ = ‖q‖^{-1/2}`
  lies in it) and the existing theorem applies directly;
* otherwise `X² − q` is irreducible (`X_pow_sub_C_irreducible_of_prime`), and
  `L := AdjoinRoot (X² − q)` is a quadratic field extension. The **spectral norm**
  (Bosch–Güntzer–Remmert, via `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`) makes `L` a
  complete ultrametric normed field with `‖algebraMap K L x‖ = ‖x‖`, so `q` is again a Tate
  parameter over `L` (`TateParameter.baseChange`) and `‖π‖² = ‖π²‖ = ‖q‖` puts `π⁻¹` inside the
  fundamental annulus of `L`.

The coefficient transfer `algebraMap K L (defectAnnulusCoeff ℓ) = defectAnnulusCoeff_L ℓ` is
proved for an **abstract** complete ultrametric normed-algebra extension `L / K`: the algebra
map is an isometry (`norm_algebraMap'`), hence maps each of the defining convergent series
(Eisenstein series, Laurent-coefficient convolutions) termwise onto its `L`-counterpart. The
required summability of the convolutions over `K` follows from the uniform geometric bounds
`‖XLaurentCoeff m‖, ‖YLaurentCoeff m‖ ≤ ‖q‖^{m⁺}` proved here. Vanishing over `L` then pulls
back along the injective algebra map.

## Main results

* `TateParameter.norm_XLaurentCoeff_le` / `TateParameter.norm_YLaurentCoeff_le`: uniform
  geometric bounds on the coordinate Laurent coefficients.
* `TateParameter.summable_laurentConvolution_of_norm_le`: convolutions of geometrically bounded
  coefficient families are unconditionally summable.
* `TateParameter.algebraMap_defectAnnulusCoeff`: the annulus defect coefficients commute with an
  isometric complete extension.
* `TateParameter.defectAnnulusCoeff_eq_zero'`: **the Eisenstein pole-cancellation identity**
  (#169), with no annulus-nonemptiness hypothesis.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §3.2 (the norm extension
  theorem used through `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`).
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-! ### Geometric bounds on the coordinate Laurent coefficients -/

omit [CompleteSpace K] in
/-- The Eisenstein series `sₖ(q)` has norm at most `1`: each summand has norm
`‖(m : K)‖ᵏ·‖q‖ᵐ ≤ 1` and the ultrametric `tsum` bound applies. -/
lemma norm_eisenstein_le_one (k : ℕ) : ‖t.eisenstein k‖ ≤ 1 := by
  rw [eisenstein]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun n => ?_
  rw [norm_div, norm_mul, norm_pow, norm_pow, t.norm_one_sub_qpow n, div_one]
  calc ‖((n + 1 : ℕ) : K)‖ ^ k * ‖(t.q : K)‖ ^ (n + 1)
      ≤ 1 ^ k * 1 ^ (n + 1) := by
        gcongr
        · exact IsUltrametricDist.norm_natCast_le_one K (n + 1)
        · exact t.norm_lt_one.le
    _ = 1 := by rw [one_pow, one_pow, one_mul]

omit [CompleteSpace K] in
/-- **Uniform geometric bound on the `X`-coefficients**: `‖XLaurentCoeff m‖ ≤ ‖q‖^{m⁺}` (with
`m⁺ = max m 0`); in particular all coefficients have norm at most `1`, and the positive-degree
coefficients decay geometrically. -/
lemma norm_XLaurentCoeff_le (m : ℤ) : ‖t.XLaurentCoeff m‖ ≤ ‖(t.q : K)‖ ^ m.toNat := by
  rcases lt_trichotomy 0 m with hm | hm | hm
  · rw [t.XLaurentCoeff_of_pos hm, norm_div, norm_mul, norm_pow]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, m.toNat = n + 1 := ⟨m.toNat - 1, by omega⟩
    rw [hn, t.norm_one_sub_qpow n, div_one]
    calc ‖((n + 1 : ℕ) : K)‖ * ‖(t.q : K)‖ ^ (n + 1)
        ≤ 1 * ‖(t.q : K)‖ ^ (n + 1) := by
          gcongr
          exact IsUltrametricDist.norm_natCast_le_one K (n + 1)
      _ = ‖(t.q : K)‖ ^ (n + 1) := one_mul _
  · rw [← hm, t.XLaurentCoeff_zero, Int.toNat_zero, pow_zero, norm_mul]
    have h2 : ‖(-2 : K)‖ ≤ 1 := by
      rw [norm_neg]
      simpa using IsUltrametricDist.norm_natCast_le_one K 2
    exact mul_le_one₀ h2 (norm_nonneg _) (t.norm_eisenstein_le_one 1)
  · rw [t.XLaurentCoeff_of_neg hm, norm_div]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (-m).toNat = n + 1 := ⟨(-m).toNat - 1, by omega⟩
    rw [hn, t.norm_one_sub_qpow n, div_one, (by omega : m.toNat = 0), pow_zero]
    exact IsUltrametricDist.norm_natCast_le_one K _

omit [CompleteSpace K] in
/-- All `X`-coefficients have norm at most `1`. -/
lemma norm_XLaurentCoeff_le_one (m : ℤ) : ‖t.XLaurentCoeff m‖ ≤ 1 :=
  (t.norm_XLaurentCoeff_le m).trans (pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le)

omit [CompleteSpace K] in
/-- **Uniform geometric bound on the `Y`-coefficients**: `‖YLaurentCoeff m‖ ≤ ‖q‖^{m⁺}`. -/
lemma norm_YLaurentCoeff_le (m : ℤ) : ‖t.YLaurentCoeff m‖ ≤ ‖(t.q : K)‖ ^ m.toNat := by
  rcases lt_trichotomy 0 m with hm | hm | hm
  · rw [t.YLaurentCoeff_of_pos hm, norm_div, norm_mul, norm_pow]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, m.toNat = n + 1 := ⟨m.toNat - 1, by omega⟩
    rw [hn, t.norm_one_sub_qpow n, div_one]
    calc ‖(((n + 1).choose 2 : ℕ) : K)‖ * ‖(t.q : K)‖ ^ (n + 1)
        ≤ 1 * ‖(t.q : K)‖ ^ (n + 1) := by
          gcongr
          exact IsUltrametricDist.norm_natCast_le_one K _
      _ = ‖(t.q : K)‖ ^ (n + 1) := one_mul _
  · rw [← hm, t.YLaurentCoeff_zero, Int.toNat_zero, pow_zero]
    exact t.norm_eisenstein_le_one 1
  · rw [t.YLaurentCoeff_of_neg hm, norm_div, norm_neg]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (-m).toNat = n + 1 := ⟨(-m).toNat - 1, by omega⟩
    rw [hn, t.norm_one_sub_qpow n, div_one, (by omega : m.toNat = 0), pow_zero]
    exact IsUltrametricDist.norm_natCast_le_one K _

omit [CompleteSpace K] in
/-- All `Y`-coefficients have norm at most `1`. -/
lemma norm_YLaurentCoeff_le_one (m : ℤ) : ‖t.YLaurentCoeff m‖ ≤ 1 :=
  (t.norm_YLaurentCoeff_le m).trans (pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le)

omit [CompleteSpace K] in
/-- The inner `X²`-convolution inherits the geometric bound `‖·‖ ≤ ‖q‖^{j⁺}`: each summand is
bounded by `‖q‖^{(j−k)⁺ + k⁺} ≤ ‖q‖^{j⁺}` and the ultrametric `tsum` bound applies. -/
lemma norm_tsum_XLaurentCoeff_mul_le (j : ℤ) :
    ‖∑' k : ℤ, t.XLaurentCoeff (j - k) * t.XLaurentCoeff k‖ ≤ ‖(t.q : K)‖ ^ j.toNat := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
  rw [norm_mul]
  calc ‖t.XLaurentCoeff (j - k)‖ * ‖t.XLaurentCoeff k‖
      ≤ ‖(t.q : K)‖ ^ (j - k).toNat * ‖(t.q : K)‖ ^ k.toNat := by
        gcongr
        · exact t.norm_XLaurentCoeff_le (j - k)
        · exact t.norm_XLaurentCoeff_le k
    _ = ‖(t.q : K)‖ ^ ((j - k).toNat + k.toNat) := (pow_add _ _ _).symm
    _ ≤ ‖(t.q : K)‖ ^ j.toNat :=
        pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le (by omega)

/-! ### Unconditional summability of the coefficient convolutions -/

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The shifted geometric majorant `n ↦ ‖q‖^{(c + n)⁺}` is summable over `ℕ`. -/
private lemma summable_qpow_shift (c : ℤ) :
    Summable fun n : ℕ => ‖(t.q : K)‖ ^ (c + (n : ℤ)).toNat := by
  refine (summable_nat_add_iff (-c).toNat).mp ?_
  have hfun : (fun n : ℕ => ‖(t.q : K)‖ ^ (c + ((n + (-c).toNat : ℕ) : ℤ)).toNat)
      = fun n : ℕ => ‖(t.q : K)‖ ^ (c + ((-c).toNat : ℤ)).toNat * ‖(t.q : K)‖ ^ n := by
    funext n
    rw [← pow_add]
    congr 1
    omega
  rw [hfun]
  exact (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one).mul_left _

/-- **Unconditional summability of coefficient convolutions.** If two coefficient families
satisfy the geometric bound `‖A m‖, ‖B m‖ ≤ ‖q‖^{m⁺}`, their convolution family
`m ↦ A (ℓ − m) · B m` is summable: it decays like `‖q‖^m` as `m → ∞` and like `‖q‖^{ℓ−m}` as
`m → −∞`. This is the coefficient-level input for transporting `defectAnnulusCoeff` along an
isometric base change. -/
lemma summable_laurentConvolution_of_norm_le {A B : ℤ → K} (ℓ : ℤ)
    (hA : ∀ m, ‖A m‖ ≤ ‖(t.q : K)‖ ^ m.toNat) (hB : ∀ m, ‖B m‖ ≤ ‖(t.q : K)‖ ^ m.toNat) :
    Summable fun m : ℤ => A (ℓ - m) * B m := by
  have hq1 : ∀ m : ℤ, ‖(t.q : K)‖ ^ m.toNat ≤ 1 := fun m =>
    pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le
  have h₁ : Summable fun n : ℕ => A (ℓ - (n : ℤ)) * B (n : ℤ) := by
    refine (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one).of_norm_bounded
      fun n => ?_
    rw [norm_mul]
    calc ‖A (ℓ - (n : ℤ))‖ * ‖B (n : ℤ)‖
        ≤ 1 * ‖(t.q : K)‖ ^ ((n : ℤ)).toNat :=
          mul_le_mul ((hA _).trans (hq1 _)) (hB _) (norm_nonneg _) zero_le_one
      _ = ‖(t.q : K)‖ ^ n := by rw [one_mul, Int.toNat_natCast]
  have h₂ : Summable fun n : ℕ => A (ℓ - -((n : ℤ) + 1)) * B (-((n : ℤ) + 1)) := by
    refine (t.summable_qpow_shift (ℓ + 1)).of_norm_bounded fun n => ?_
    rw [norm_mul]
    calc ‖A (ℓ - -((n : ℤ) + 1))‖ * ‖B (-((n : ℤ) + 1))‖
        ≤ ‖(t.q : K)‖ ^ (ℓ - -((n : ℤ) + 1)).toNat * 1 :=
          mul_le_mul (hA _) ((hB _).trans (hq1 _)) (norm_nonneg _) (by positivity)
      _ = ‖(t.q : K)‖ ^ (ℓ + 1 + (n : ℤ)).toNat := by
          rw [mul_one]
          congr 1
          omega
  exact Summable.of_nat_of_neg_add_one h₁ h₂

/-! ### Transfer of the coefficients along an isometric complete extension

Throughout this section `L / K` is an abstract complete ultrametric normed-algebra extension;
`NormedAlgebra K L` over the normed field `L` provides exactly the isometry
`‖algebraMap K L x‖ = ‖x‖` (`norm_algebraMap'`). -/

section Transfer

variable (L : Type*) [NormedField L] [NormedAlgebra K L]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The algebra map of an isometric extension maps convergent sums to convergent sums. -/
private lemma algebraMap_tsum {ι : Type*} {f : ι → K} (hf : Summable f) :
    algebraMap K L (∑' i : ι, f i) = ∑' i : ι, algebraMap K L (f i) :=
  ((hf.hasSum.map (algebraMap K L)
    (AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap' L)).continuous).tsum_eq).symm

/-- The Eisenstein series `sₖ(q)` commutes with an isometric complete extension. -/
lemma algebraMap_eisenstein (k : ℕ) :
    algebraMap K L (t.eisenstein k) = (t.baseChange L).eisenstein k := by
  simp only [eisenstein]
  rw [algebraMap_tsum L (t.eisenstein_summand_summable k)]
  refine tsum_congr fun n => ?_
  simp only [map_div₀, map_mul, map_pow, map_natCast, map_sub, map_one, baseChange_q_coe]

/-- The `X`-coordinate Laurent coefficients commute with an isometric complete extension. -/
lemma algebraMap_XLaurentCoeff (m : ℤ) :
    algebraMap K L (t.XLaurentCoeff m) = (t.baseChange L).XLaurentCoeff m := by
  rcases lt_trichotomy 0 m with hm | hm | hm
  · rw [t.XLaurentCoeff_of_pos hm, (t.baseChange L).XLaurentCoeff_of_pos hm, map_div₀, map_mul,
      map_natCast, map_pow, map_sub, map_one, map_pow, baseChange_q_coe]
  · rw [← hm, t.XLaurentCoeff_zero, (t.baseChange L).XLaurentCoeff_zero, map_mul, map_neg,
      map_ofNat, t.algebraMap_eisenstein L 1]
  · rw [t.XLaurentCoeff_of_neg hm, (t.baseChange L).XLaurentCoeff_of_neg hm, map_div₀,
      map_natCast, map_sub, map_one, map_pow, baseChange_q_coe]

/-- The `Y`-coordinate Laurent coefficients commute with an isometric complete extension. -/
lemma algebraMap_YLaurentCoeff (m : ℤ) :
    algebraMap K L (t.YLaurentCoeff m) = (t.baseChange L).YLaurentCoeff m := by
  rcases lt_trichotomy 0 m with hm | hm | hm
  · rw [t.YLaurentCoeff_of_pos hm, (t.baseChange L).YLaurentCoeff_of_pos hm, map_div₀, map_mul,
      map_natCast, map_pow, map_sub, map_one, map_pow, baseChange_q_coe]
  · rw [← hm, t.YLaurentCoeff_zero, (t.baseChange L).YLaurentCoeff_zero,
      t.algebraMap_eisenstein L 1]
  · rw [t.YLaurentCoeff_of_neg hm, (t.baseChange L).YLaurentCoeff_of_neg hm, map_div₀, map_neg,
      map_natCast, map_sub, map_one, map_pow, baseChange_q_coe]

/-- The Tate coefficient `a₄(q)` commutes with an isometric complete extension. -/
lemma algebraMap_a₄ : algebraMap K L t.a₄ = (t.baseChange L).a₄ := by
  simp only [a₄_def, map_mul, map_neg, map_ofNat, t.algebraMap_eisenstein L]

/-- The Tate coefficient `a₆(q)` commutes with an isometric complete extension. -/
lemma algebraMap_a₆ : algebraMap K L t.a₆ = (t.baseChange L).a₆ := by
  simp only [a₆_def, map_div₀, map_neg, map_add, map_mul, map_ofNat,
    t.algebraMap_eisenstein L]

/-- **Transfer of the annulus defect coefficients.** The coefficients of the annulus Laurent
development of the Weierstrass defect commute with an isometric complete extension `L / K`:
every defining convolution is unconditionally summable over `K` by the geometric coefficient
bounds, so the isometric algebra map carries it termwise onto the corresponding convolution
over `L`. -/
theorem algebraMap_defectAnnulusCoeff (ℓ : ℤ) :
    algebraMap K L (t.defectAnnulusCoeff ℓ) = (t.baseChange L).defectAnnulusCoeff ℓ := by
  have hYY : algebraMap K L (∑' m : ℤ, t.YLaurentCoeff (ℓ - m) * t.YLaurentCoeff m)
      = ∑' m : ℤ, (t.baseChange L).YLaurentCoeff (ℓ - m) * (t.baseChange L).YLaurentCoeff m := by
    rw [algebraMap_tsum L (t.summable_laurentConvolution_of_norm_le ℓ
      t.norm_YLaurentCoeff_le t.norm_YLaurentCoeff_le)]
    exact tsum_congr fun m => by
      rw [map_mul, t.algebraMap_YLaurentCoeff L, t.algebraMap_YLaurentCoeff L]
  have hXY : algebraMap K L (∑' m : ℤ, t.XLaurentCoeff (ℓ - m) * t.YLaurentCoeff m)
      = ∑' m : ℤ, (t.baseChange L).XLaurentCoeff (ℓ - m) * (t.baseChange L).YLaurentCoeff m := by
    rw [algebraMap_tsum L (t.summable_laurentConvolution_of_norm_le ℓ
      t.norm_XLaurentCoeff_le t.norm_YLaurentCoeff_le)]
    exact tsum_congr fun m => by
      rw [map_mul, t.algebraMap_XLaurentCoeff L, t.algebraMap_YLaurentCoeff L]
  have hXXX : algebraMap K L
      (∑' m : ℤ, (∑' k : ℤ, t.XLaurentCoeff (ℓ - m - k) * t.XLaurentCoeff k)
        * t.XLaurentCoeff m)
      = ∑' m : ℤ,
          (∑' k : ℤ, (t.baseChange L).XLaurentCoeff (ℓ - m - k)
            * (t.baseChange L).XLaurentCoeff k) * (t.baseChange L).XLaurentCoeff m := by
    rw [algebraMap_tsum L (t.summable_laurentConvolution_of_norm_le ℓ
      t.norm_tsum_XLaurentCoeff_mul_le t.norm_XLaurentCoeff_le)]
    refine tsum_congr fun m => ?_
    rw [map_mul, t.algebraMap_XLaurentCoeff L]
    congr 1
    rw [algebraMap_tsum L (t.summable_laurentConvolution_of_norm_le (ℓ - m)
      t.norm_XLaurentCoeff_le t.norm_XLaurentCoeff_le)]
    exact tsum_congr fun k => by
      rw [map_mul, t.algebraMap_XLaurentCoeff L, t.algebraMap_XLaurentCoeff L]
  simp only [defectAnnulusCoeff, map_sub, map_add, map_mul, apply_ite (algebraMap K L),
    map_zero, hYY, hXY, hXXX, t.algebraMap_a₄ L, t.algebraMap_a₆ L,
    t.algebraMap_XLaurentCoeff L]

end Transfer

/-! ### The unconditional pole-cancellation identity -/

/-- Elementary annulus bookkeeping: if `0 < a` and `a² = b < 1`, then `a⁻¹` lies in the
fundamental annulus data `1 < a⁻¹` and `b·a⁻¹ < 1`. -/
private lemma one_lt_inv_and_mul_inv_lt_one {a b : ℝ} (ha : 0 < a) (hab : a ^ 2 = b)
    (hb1 : b < 1) : 1 < a⁻¹ ∧ b * a⁻¹ < 1 := by
  have ha1 : a < 1 := by nlinarith
  refine ⟨one_lt_inv_iff₀.mpr ⟨ha, ha1⟩, ?_⟩
  have hba : b * a⁻¹ = a := by
    rw [← hab, pow_two, mul_assoc, mul_inv_cancel₀ ha.ne', mul_one]
  rw [hba]
  exact ha1

/-- If some complete ultrametric extension `L / K` contains a square root `π` of `q`, then the
annulus of `L` is nonempty (`π⁻¹` lies in it, since `‖π‖² = ‖q‖`), so the conditional identity
applies over `L` and pulls back along the injective isometric algebra map. -/
private lemma defectAnnulusCoeff_eq_zero_of_sq_root {L : Type*} [NormedField L]
    [CompleteSpace L] [IsUltrametricDist L] [NormedAlgebra K L] (h12 : (12 : K) ≠ 0)
    {π : L} (hπ : π ^ 2 = algebraMap K L (t.q : K)) (ℓ : ℤ) :
    t.defectAnnulusCoeff ℓ = 0 := by
  have hq0 : (t.q : K) ≠ 0 := Units.ne_zero t.q
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hπ
    exact hq0 ((algebraMap K L).injective (by rw [map_zero]; exact hπ.symm))
  have hnormsq : ‖π‖ ^ 2 = ‖(t.q : K)‖ := by rw [← norm_pow, hπ, norm_algebraMap']
  obtain ⟨h1, h2⟩ :=
    one_lt_inv_and_mul_inv_lt_one (norm_pos_iff.mpr hπ0) hnormsq t.norm_lt_one
  have h12L : (12 : L) ≠ 0 := by
    intro h
    apply h12
    apply (algebraMap K L).injective
    rw [map_ofNat, map_zero, h]
  have hz := (t.baseChange L).defectAnnulusCoeff_eq_zero h12L
    (u := (Units.mk0 π hπ0)⁻¹) (by simpa using h1) (by simpa using h2) ℓ
  have htrans := t.algebraMap_defectAnnulusCoeff L ℓ
  rw [hz] at htrans
  exact (map_eq_zero_iff _ (algebraMap K L).injective).mp htrans

/-- **The Eisenstein pole-cancellation identity** (#169), unconditionally: every coefficient of
the annulus Laurent development of the Weierstrass defect vanishes. This removes the
annulus-nonemptiness hypothesis of `defectAnnulusCoeff_eq_zero`: if `q` is a square in `K` the
annulus of `K` is already nonempty, and otherwise the coefficients are transported along the
quadratic extension `AdjoinRoot (X² − q)`, made a complete ultrametric normed field by the
spectral norm (Bosch–Güntzer–Remmert), whose annulus contains `(√q)⁻¹`. -/
theorem defectAnnulusCoeff_eq_zero' (h12 : (12 : K) ≠ 0) (ℓ : ℤ) :
    t.defectAnnulusCoeff ℓ = 0 := by
  by_cases hs : ∃ s : K, s ^ 2 = (t.q : K)
  · -- `q` is a square in `K`: the annulus of `K` itself is nonempty.
    obtain ⟨s, hsq⟩ := hs
    exact t.defectAnnulusCoeff_eq_zero_of_sq_root (L := K) h12 (π := s)
      (by simpa using hsq) ℓ
  · -- `X² − q` is irreducible: base-change to `AdjoinRoot (X² − q)` with the spectral norm.
    push Not at hs
    have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (t.q : K)) :=
      X_pow_sub_C_irreducible_of_prime Nat.prime_two hs
    haveI : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (t.q : K))) := ⟨hirr⟩
    haveI : Module.Finite K (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (t.q : K))) :=
      (AdjoinRoot.powerBasis hirr.ne_zero).finite
    haveI : Algebra.IsAlgebraic K (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (t.q : K))) :=
      Algebra.IsAlgebraic.of_finite K _
    -- The norm of `K` is nontrivial (witnessed by `q⁻¹`), definitionally the ambient one.
    letI : NontriviallyNormedField K :=
      { ‹NormedField K› with
        non_trivial := ⟨((t.q⁻¹ : Kˣ) : K), by
          rw [Units.val_inv_eq_inv_val, norm_inv]
          exact one_lt_inv_iff₀.mpr ⟨t.norm_q_pos, t.norm_lt_one⟩⟩ }
    -- The spectral norm makes the quadratic extension a complete ultrametric normed field
    -- extending the norm of `K` isometrically.
    letI : NormedField (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (t.q : K))) :=
      spectralNorm.normedField K _
    haveI : IsUltrametricDist (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (t.q : K))) :=
      IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
    haveI : CompleteSpace (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (t.q : K))) :=
      spectralNorm.completeSpace K _
    letI : NormedAlgebra K (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (t.q : K))) :=
      spectralNorm.normedAlgebra K _
    -- The adjoined root is a square root of `q`.
    have hπ : AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C (t.q : K)) ^ 2
        = algebraMap K (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (t.q : K))) (t.q : K) := by
      have h := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 - Polynomial.C (t.q : K))
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        sub_eq_zero] at h
      rw [AdjoinRoot.algebraMap_eq]
      exact h
    exact t.defectAnnulusCoeff_eq_zero_of_sq_root h12 hπ ℓ

end TateParameter

end TateCurvesTheta
