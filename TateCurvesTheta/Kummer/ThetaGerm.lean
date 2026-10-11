/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.Decomposition
import Mathlib.RingTheory.Valuation.LocalSubring
import TateCurvesTheta.Kummer.ThetaValues

/-!
# The Kummer class of the theta function and the Kummer classes of its values

We compare the Kummer class of `θ` *as a function* with the Kummer class of its value `θ(u)`.
Mathlib has no étale (or tempered) fundamental group of a curve over a non-closed field, so the
function side is taken in the **completed local ring at the point**: the germ of `θ` at
`u ∈ Kˣ`, written in the multiplicative local coordinate `u(1 + X)`,
```
Θ_u = ∑ₙ q^{e(n)} uⁿ (1 + X)ⁿ ∈ K⟦X⟧,   coeff_k Θ_u = ∑ₙ q^{e(n)} uⁿ binom(n, k)
```
(`TateParameter.thetaGerm`, with the integer binomial coefficients `binomCoeff n k` of
`(1 + X)ⁿ`, `n ∈ ℤ`). It is the germ of `θ` at `u`: for `‖w‖ < 1` the series converges to
`θ(u(1 + w))` (`TateParameter.hasSum_thetaGerm`, a Fubini argument for the absolutely
convergent double series, using `hasSum_binom : ∑ₖ binom(n, k) wᵏ = (1 + w)ⁿ`). Its constant
term is `θ(u)` (`constantCoeff_thetaGerm`), so off the divisor `-qᶻ` it is a unit of `K⟦X⟧`
(`thetaGermUnit`).

Let `F` be a field with a map `K⟦X⟧ → F` compatible with the constants (`hCF`; e.g. `K((X))`,
the fraction field of the completed local ring, `laurentSeries_algebraMap_C`), `Ω/F` algebraic,
and `A ⊆ Ω` a valuation subring dominating `K⟦X⟧` (it contains the image of `K⟦X⟧` and `X` lies
in its maximal ideal; such `A` exist, `exists_valuationSubring_dominating`,
`exists_valuationSubring_dominating_laurentSeries`). Its decomposition group `D_A ⊆ Gal(Ω/F)`
maps to `Gal(κ(A)/K)` (`continuous-kummer-theory`, `Decomposition.decompositionMap`), and
`decomposition_kummer_thetaGerm` states:

> the restriction of the Kummer class `κ_F(Θ_u)` to `D_A` (coefficients reduced mod `𝔪_A`) is the
> inflation of the Kummer class `κ_K(θ(u))` of the theta value.

This is `Decomposition.decomposition_kummerValue` for the point `X ↦ 0` (`pointEval`).

## References

* S. Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations*, §1.
-/

noncomputable section

open PowerSeries Filter Topology KummerTheory IsLocalRing

namespace TateCurvesTheta

/-! ### The binomial series `(1 + X)ⁿ`, `n ∈ ℤ` -/

/-- `1 + X` as a unit of `ℤ⟦X⟧`. -/
def onePlusX : (ℤ⟦X⟧)ˣ :=
  (isUnit_iff_constantCoeff (φ := (1 + X : ℤ⟦X⟧))).2 (by simp) |>.unit

@[simp]
lemma coe_onePlusX : (onePlusX : ℤ⟦X⟧) = 1 + X := IsUnit.unit_spec _

/-- The integer binomial coefficients `binom(n, k)`, `n ∈ ℤ`: the coefficients of `(1 + X)ⁿ`. -/
def binomCoeff (n : ℤ) (k : ℕ) : ℤ := coeff k ((onePlusX ^ n : (ℤ⟦X⟧)ˣ) : ℤ⟦X⟧)

lemma binomCoeff_zero_right (n : ℤ) : binomCoeff n 0 = 1 := by
  have h1 : Units.map (constantCoeff : ℤ⟦X⟧ →+* ℤ).toMonoidHom onePlusX = 1 :=
    Units.ext (by simp)
  have h : Units.map (constantCoeff : ℤ⟦X⟧ →+* ℤ).toMonoidHom (onePlusX ^ n) = 1 := by
    rw [map_zpow, h1, one_zpow]
  rw [binomCoeff, coeff_zero_eq_constantCoeff_apply]
  exact (Units.coe_map _ _).symm.trans (congrArg Units.val h)

lemma binomCoeff_zero_left (k : ℕ) : binomCoeff 0 k = if k = 0 then 1 else 0 := by
  simp [binomCoeff, coeff_one]

lemma binomCoeff_add_one_succ (n : ℤ) (k : ℕ) :
    binomCoeff (n + 1) (k + 1) = binomCoeff n (k + 1) + binomCoeff n k := by
  simp only [binomCoeff, zpow_add_one, Units.val_mul, coe_onePlusX, mul_add, mul_one, map_add,
    mul_comm _ (X : ℤ⟦X⟧), coeff_succ_X_mul]

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

omit [CompleteSpace K] in
lemma norm_binomCoeff_le_one (n : ℤ) (k : ℕ) : ‖(binomCoeff n k : K)‖ ≤ 1 :=
  IsUltrametricDist.norm_intCast_le_one K _

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma one_add_ne_zero_of_norm_lt_one {w : K} (hw : ‖w‖ < 1) : 1 + w ≠ 0 := by
  intro h
  have : ‖w‖ = 1 := by rw [show w = -1 by linear_combination h]; simp
  linarith

variable {w : K}

lemma summable_binom (n : ℤ) (hw : ‖w‖ < 1) :
    Summable fun k : ℕ => (binomCoeff n k : K) * w ^ k := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  refine squeeze_zero_norm (fun k => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg w) hw)
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) (norm_binomCoeff_le_one _ _)

lemma tsum_binom_add_one (n : ℤ) (hw : ‖w‖ < 1) :
    ∑' k : ℕ, (binomCoeff (n + 1) k : K) * w ^ k =
      (1 + w) * ∑' k : ℕ, (binomCoeff n k : K) * w ^ k := by
  set a : ℕ → K := fun k => (binomCoeff n k : K) * w ^ k with ha_def
  set S := ∑' k, a k
  have ha : HasSum a S := (summable_binom n hw).hasSum
  have h1 : HasSum (fun k : ℕ => (binomCoeff (n + 1) (k + 1) : K) * w ^ (k + 1))
      (S - a 0 + w * S) := by
    have e : (fun k : ℕ => (binomCoeff (n + 1) (k + 1) : K) * w ^ (k + 1)) =
        fun k => a (k + 1) + w * a k := by
      funext k
      simp only [ha_def, binomCoeff_add_one_succ, Int.cast_add, pow_succ]
      ring
    rw [e]
    refine HasSum.add ?_ (ha.mul_left w)
    simpa using (hasSum_nat_add_iff' 1).2 ha
  have h2 : HasSum (fun k : ℕ => (binomCoeff (n + 1) k : K) * w ^ k) (S + w * S) := by
    rw [← hasSum_nat_add_iff' 1]
    have hval : S + w * S - ∑ i ∈ Finset.range 1, (binomCoeff (n + 1) i : K) * w ^ i =
        S - a 0 + w * S := by
      simp [ha_def, binomCoeff_zero_right]
      ring
    rw [hval]
    exact h1
  rw [h2.tsum_eq]
  ring

/-- **The binomial series**: `∑ₖ binom(n, k) wᵏ = (1 + w)ⁿ` for `n ∈ ℤ`, `‖w‖ < 1`. -/
theorem hasSum_binom (n : ℤ) (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ => (binomCoeff n k : K) * w ^ k) ((1 + w) ^ n) := by
  have h1w := one_add_ne_zero_of_norm_lt_one hw
  refine (summable_binom n hw).hasSum_iff.2 ?_
  induction n using Int.induction_on with
  | zero =>
    simp_rw [binomCoeff_zero_left, zpow_zero]
    simp
  | succ m ih => rw [tsum_binom_add_one _ hw, ih, zpow_add_one₀ h1w]; ring
  | pred m ih =>
    have h := tsum_binom_add_one (-(m : ℤ) - 1) hw
    rw [show -(m : ℤ) - 1 + 1 = -m by ring, ih] at h
    rw [zpow_sub_one₀ h1w, h]
    field_simp

namespace TateParameter

variable (t : TateParameter K)

/-! ### The germ of `θ` at a point -/

/-- The **germ of `θ` at `u`** in the multiplicative local coordinate `u(1 + X)`:
`Θ_u = ∑ₙ q^{e(n)} uⁿ (1 + X)ⁿ ∈ K⟦X⟧`, coefficientwise `∑ₙ q^{e(n)} uⁿ binom(n, k)`. -/
def thetaGerm (u : Kˣ) : K⟦X⟧ :=
  PowerSeries.mk fun k => ∑' n : ℤ, t.thetaTerm u n * (binomCoeff n k : K)

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma coeff_thetaGerm (u : Kˣ) (k : ℕ) :
    coeff k (t.thetaGerm u) = ∑' n : ℤ, t.thetaTerm u n * (binomCoeff n k : K) :=
  coeff_mk _ _

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The constant term of the germ is the value: `Θ_u(0) = θ(u)`. -/
@[simp]
theorem constantCoeff_thetaGerm (u : Kˣ) : constantCoeff (t.thetaGerm u) = t.theta u := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_thetaGerm]
  simp [binomCoeff_zero_right, theta]

lemma summable_thetaGerm_family (u : Kˣ) (hw : ‖w‖ < 1) :
    Summable (Function.uncurry fun (n : ℤ) (k : ℕ) =>
      t.thetaTerm u n * (binomCoeff n k : K) * w ^ k) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  have hθ : Tendsto (fun n => ‖t.thetaTerm u n‖) cofinite (𝓝 0) := by
    simpa using (t.thetaTerm_summable u).tendsto_cofinite_zero.norm
  have hw' : Tendsto (fun k : ℕ => ‖w‖ ^ k) cofinite (𝓝 0) := by
    rw [Nat.cofinite_eq_atTop]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hw
  have hbd : ∀ p : ℤ × ℕ, ‖Function.uncurry (fun (n : ℤ) (k : ℕ) =>
      t.thetaTerm u n * (binomCoeff n k : K) * w ^ k) p‖ ≤ ‖t.thetaTerm u p.1‖ * ‖w‖ ^ p.2 := by
    rintro ⟨n, k⟩
    simp only [Function.uncurry_apply_pair, norm_mul, norm_pow]
    have := norm_binomCoeff_le_one (K := K) n k
    calc ‖t.thetaTerm u n‖ * ‖(binomCoeff n k : K)‖ * ‖w‖ ^ k
        ≤ ‖t.thetaTerm u n‖ * 1 * ‖w‖ ^ k := by gcongr
      _ = ‖t.thetaTerm u n‖ * ‖w‖ ^ k := by ring
  refine squeeze_zero_norm hbd ?_
  rw [← Filter.coprod_cofinite, Filter.coprod, Filter.tendsto_sup]
  constructor
  · refine Filter.Tendsto.zero_mul_isBoundedUnder_le (hθ.comp tendsto_comap) ?_
    refine Filter.isBoundedUnder_of ⟨1, fun p => ?_⟩
    simp only [Function.comp_apply, norm_pow, norm_norm]
    exact pow_le_one₀ (norm_nonneg _) hw.le
  · obtain ⟨C, hC⟩ := hθ.bddAbove_range_of_cofinite
    refine Filter.isBoundedUnder_le_mul_tendsto_zero ?_ (hw'.comp tendsto_comap)
    refine Filter.isBoundedUnder_of ⟨C, fun p => ?_⟩
    simp only [Function.comp_apply, norm_norm]
    exact hC ⟨p.1, rfl⟩

/-- **`Θ_u` is the germ of `θ` at `u`**: for `‖w‖ < 1`, `∑ₖ coeff_k(Θ_u) wᵏ = θ(u(1 + w))`. -/
theorem hasSum_thetaGerm (u : Kˣ) (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ => coeff k (t.thetaGerm u) * w ^ k)
      (t.theta (u * Units.mk0 (1 + w) (one_add_ne_zero_of_norm_lt_one hw))) := by
  set F : ℤ → ℕ → K := fun n k => t.thetaTerm u n * (binomCoeff n k : K) * w ^ k with hF
  have hS := t.summable_thetaGerm_family u hw
  have h₁ : ∀ n, Summable (F n) := fun n => hS.prod_factor n
  have h₂ : ∀ k, Summable fun n => F n k := fun k => hS.prod_symm.prod_factor k
  have hcol : ∀ n, ∑' k, F n k =
      t.thetaTerm (u * Units.mk0 (1 + w) (one_add_ne_zero_of_norm_lt_one hw)) n := by
    intro n
    have e : F n = fun k => t.thetaTerm u n * ((binomCoeff n k : K) * w ^ k) := by
      funext k; simp only [hF]; ring
    rw [e, tsum_mul_left, (hasSum_binom n hw).tsum_eq]
    simp [thetaTerm, mul_zpow, mul_assoc]
  have hrow : ∀ k, ∑' n, F n k = coeff k (t.thetaGerm u) * w ^ k := by
    intro k
    rw [coeff_thetaGerm, ← tsum_mul_right]
  have hsum : Summable fun k => ∑' n, F n k := hS.prod_symm.prod
  rw [theta, ← tsum_congr hcol, ← hS.tsum_comm' h₁ h₂]
  simp_rw [← hrow]
  exact hsum.hasSum

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma isUnit_thetaGerm (u : Kˣ) (hu : t.theta u ≠ 0) : IsUnit (t.thetaGerm u) :=
  isUnit_iff_constantCoeff.2 (by rw [constantCoeff_thetaGerm]; exact hu.isUnit)

/-- The germ `Θ_u` as a unit of `K⟦X⟧`, for `u` off the divisor of `θ`. -/
def thetaGermUnit (u : Kˣ) (hu : t.theta u ≠ 0) : (K⟦X⟧)ˣ := (t.isUnit_thetaGerm u hu).unit

omit [CompleteSpace K] [IsUltrametricDist K] in
@[simp]
lemma coe_thetaGermUnit (u : Kˣ) (hu : t.theta u ≠ 0) :
    (t.thetaGermUnit u hu : K⟦X⟧) = t.thetaGerm u :=
  IsUnit.unit_spec _

end TateParameter

/-- The point `X ↦ 0` of `K⟦X⟧` (i.e. the point `u` in the coordinate `u(1 + X)`), as a
`K`-algebra map. -/
def pointEval : K⟦X⟧ →ₐ[K] K :=
  { (constantCoeff : K⟦X⟧ →+* K) with
    commutes' := fun c => by simp }

omit [CompleteSpace K] [IsUltrametricDist K] in
@[simp]
lemma pointEval_apply (r : K⟦X⟧) : pointEval r = constantCoeff r := rfl

namespace TateParameter

variable (t : TateParameter K)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The Kummer class of the value of the germ `Θ_u` at the point is `κ(θ(u))`. -/
theorem kummerValue_thetaGermUnit (n : ℕ) (Ω : Type*) [Field Ω] [Algebra K Ω]
    [Algebra.IsIntegral K Ω] [HasKummerRoots n K Ω] (u : Kˣ) (hu : t.theta u ≠ 0) :
    kummerValue n K Ω pointEval (t.thetaGermUnit u hu) = kummer n K Ω (t.thetaUnit u hu) := by
  rw [kummerValue_apply]
  congr 1
  ext
  simp

/-! ### Function vs. value on the decomposition group -/

section Decomposition

variable (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra K F] [Algebra F Ω] [Algebra K Ω]
  [IsScalarTower K F Ω] [Algebra K⟦X⟧ F]

omit [CompleteSpace K] [IsUltrametricDist K] [Algebra K F] [Algebra K Ω] [IsScalarTower K F Ω] in
/-- Valuation subrings dominating `K⟦X⟧` exist in any field `Ω ⊇ F ⊇ K⟦X⟧`: they contain the image
of `K⟦X⟧`, and `X` reduces to `0`. -/
theorem exists_valuationSubring_dominating (hinj : Function.Injective (algebraMap K⟦X⟧ F)) :
    ∃ (A : ValuationSubring Ω) (hA : ∀ r : K⟦X⟧, algebraMap F Ω (algebraMap K⟦X⟧ F r) ∈ A),
      residue A ⟨_, hA X⟩ = 0 := by
  set g : K⟦X⟧ →+* Ω := (algebraMap F Ω).comp (algebraMap K⟦X⟧ F) with hg_def
  have hg : Function.Injective g := (algebraMap F Ω).injective.comp hinj
  obtain ⟨A, hsub, hloc⟩ := (LocalSubring.range g).exists_le_valuationSubring
  have hmem : ∀ r, g r ∈ (LocalSubring.range g).toSubring := fun r => ⟨r, rfl⟩
  have hA : ∀ r : K⟦X⟧, algebraMap F Ω (algebraMap K⟦X⟧ F r) ∈ A := fun r => hsub (hmem r)
  refine ⟨A, hA, ?_⟩
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  have hX : IsUnit (⟨g X, hmem X⟩ : (LocalSubring.range g).toSubring) :=
    hloc.map_nonunit _ hunit
  obtain ⟨v, hv⟩ := hX.exists_right_inv
  have hv' : (v : Ω) ∈ Set.range g := v.2
  obtain ⟨s, hs⟩ := hv'
  have h1 : g (X * s) = g 1 := by
    rw [map_mul, map_one, hs]
    exact congrArg Subtype.val hv
  have h2 := congrArg constantCoeff (hg h1)
  simp at h2

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- In `F = K((X))` the constants of `K⟦X⟧` are the constants of `K`: the compatibility
hypothesis `hCF` below holds for Laurent series. -/
theorem laurentSeries_algebraMap_C (c : K) :
    algebraMap K⟦X⟧ (LaurentSeries K) (C c) = algebraMap K (LaurentSeries K) c := by
  rw [LaurentSeries.coe_algebraMap, HahnSeries.algebraMap_apply' (Γ := ℤ) (S := K),
    PowerSeries.algebraMap_apply]
  rfl

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Valuation subrings of `Ω ⊇ K((X))` dominating `K⟦X⟧` exist. -/
theorem exists_valuationSubring_dominating_laurentSeries (Ω : Type*) [Field Ω]
    [Algebra (LaurentSeries K) Ω] :
    ∃ (A : ValuationSubring Ω)
      (hA : ∀ r : K⟦X⟧, algebraMap (LaurentSeries K) Ω (algebraMap K⟦X⟧ (LaurentSeries K) r) ∈ A),
      residue A ⟨_, hA X⟩ = 0 :=
  exists_valuationSubring_dominating (LaurentSeries K) (FaithfulSMul.algebraMap_injective _ _)

variable (hCF : ∀ c : K, algebraMap K⟦X⟧ F (C c) = algebraMap K F c)
variable (A : ValuationSubring Ω) (hk : ∀ c : K, algebraMap K Ω c ∈ A)
  [Algebra K (ResidueField A)]
  (hkres : ∀ c : K, residue A ⟨algebraMap K Ω c, hk c⟩ = algebraMap K (ResidueField A) c)
  (hA : ∀ r : K⟦X⟧, algebraMap F Ω (algebraMap K⟦X⟧ F r) ∈ A) (hX : residue A ⟨_, hA X⟩ = 0)

omit [CompleteSpace K] [IsUltrametricDist K] in
include hCF hkres hX in
/-- Reduction modulo a valuation subring dominating `K⟦X⟧` is evaluation at the point `X ↦ 0`. -/
theorem residue_eq_pointEval (r : K⟦X⟧) :
    residue A ⟨_, hA r⟩ = algebraMap K (ResidueField A) (pointEval r) := by
  have hC : ∀ c : K, algebraMap F Ω (algebraMap K⟦X⟧ F (C c)) = algebraMap K Ω c := by
    intro c
    rw [IsScalarTower.algebraMap_apply K F Ω, hCF]
  set r' := PowerSeries.mk fun p => coeff (p + 1) r
  have e : (⟨_, hA r⟩ : A) = ⟨_, hA X⟩ * ⟨_, hA r'⟩ + ⟨_, hk (constantCoeff r)⟩ := by
    apply Subtype.ext
    conv_lhs => rw [eq_X_mul_shift_add_const r]
    simp only [map_add, map_mul, hC]
    rfl
  rw [e, map_add, map_mul, hX, zero_mul, zero_add, hkres, pointEval_apply]

variable (n : ℕ) (hn : n ≠ 0) [Algebra.IsIntegral F Ω] [Algebra.IsIntegral K (ResidueField A)]
  [HasKummerRoots n F Ω] [HasKummerRoots n K (ResidueField A)]

omit [CompleteSpace K] [IsUltrametricDist K] in
include hCF hX in
/-- **The Kummer class of the theta function restricts to the Kummer class of its value.**
Let `A ⊆ Ω` be a valuation subring dominating the completed local ring `K⟦X⟧` of the point `u`
(coordinate `u(1 + X)`), with decomposition group `D_A ⊆ Gal(Ω/F)`. For `u` off the divisor of
`θ`, the restriction to `D_A` of the Kummer class `κ_F(Θ_u)` of the germ of `θ` (coefficients
reduced modulo `𝔪_A`) is the inflation along `D_A → Gal(κ(A)/K)` of the Kummer class
`κ_K(θ(u))` of the theta value. -/
theorem decomposition_kummer_thetaGerm (u : Kˣ) (hu : t.theta u ≠ 0) :
    letI := Decomposition.muAction F A hk hkres n
    ContH1.map (A.decompositionSubgroup F).subtype continuous_subtype_val
        (Decomposition.reduceMu A n hn) continuous_of_discreteTopology
        (Decomposition.reduceMu_smul F A hk hkres n hn)
        (kummer n F Ω (Units.map (algebraMap K⟦X⟧ F : K⟦X⟧ →* F) (t.thetaGermUnit u hu))) =
      ContH1.map (Decomposition.decompositionMap F A hk hkres)
        (Decomposition.continuous_decompositionMap F A hk hkres) (MonoidHom.id _) continuous_id
        (fun _ _ => rfl) (kummer n K (ResidueField A) (t.thetaUnit u hu)) := by
  have h := Decomposition.decomposition_kummerValue F A hk hkres n hn pointEval hA
    (residue_eq_pointEval F hCF A hk hkres hA hX) (t.thetaGermUnit u hu)
  rwa [kummerValue_thetaGermUnit] at h

end Decomposition

end TateParameter

end TateCurvesTheta
