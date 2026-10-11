/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.LaurentSeries
import TateCurvesTheta.Kummer.ThetaGerm

/-!
# The theta germ on decomposition groups over an algebraically closed field

`TateParameter.decomposition_kummer_thetaGerm` keeps `Algebra.IsIntegral K κ(A)`,
`HasKummerRoots n F Ω` and `HasKummerRoots n K κ(A)` as instance hypotheses. Here we discharge
them when `Ω` is algebraically closed and algebraic over `F = Frac K⟦X⟧` (e.g. `K((X))`):

* `isAlgClosed_residueField`: the residue field of a valuation subring of an algebraically closed
  field is algebraically closed (lift a monic polynomial, take a root in `Ω`, which is integral
  over `A`, hence in `A` since valuation rings are integrally closed);
* `hasKummerRoots_of_isAlgClosed`: an algebraically closed field has Kummer roots for `n ≠ 0`
  (in every characteristic);
* `isIntegral_residueField`: if `A ⊆ Ω` dominates `K⟦X⟧` and `Ω` is algebraic over
  `F = Frac K⟦X⟧`, then `κ(A)` is algebraic over `K`. Proof: an algebraic `b ∈ A` satisfies a
  nonzero polynomial over `K⟦X⟧` (clear denominators); divide by the largest common power `Xᵏ` of
  the coefficients, so that one coefficient has nonzero constant term; reduce modulo `𝔪_A`, which
  on `K⟦X⟧` is evaluation at `X = 0` (`residue_eq_pointEval`).
  So `κ(A)` is an algebraic closure of `K` (`isAlgClosure_residueField`).

The hypothesis `F = Frac K⟦X⟧` cannot be dropped: for `F = K((X))(Y)` there are valuation subrings
`A ⊆ \bar F` dominating `K⟦X⟧` with `Y ∈ A` and residue of `Y` transcendental over `K`, and then
`κ(A)/K` is not algebraic (the profinite group `Gal(κ(A)/K)` with its Krull topology, and hence
the Kummer class `κ_K(θ(u))` used here, is set up for algebraic extensions only).

Main results: `TateParameter.decomposition_kummer_thetaGerm_of_isAlgClosed` (any `F` with
`IsFractionRing K⟦X⟧ F`) and `TateParameter.decomposition_kummer_thetaGerm_laurentSeries`
(`F = K((X))`, `Ω` any algebraically closed algebraic extension, e.g. `AlgebraicClosure K((X))`):
the only remaining hypotheses are `n ≠ 0`, the valuation subring `A`, that it dominates `K⟦X⟧`,
and `θ(u) ≠ 0`.
-/

noncomputable section

open PowerSeries IsLocalRing KummerTheory

namespace TateCurvesTheta

/-! ### Residue fields of valuation subrings of algebraically closed fields -/

/-- **The residue field of a valuation subring of an algebraically closed field is algebraically
closed.** -/
theorem isAlgClosed_residueField {Ω : Type*} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) :
    IsAlgClosed (ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  have hlift : p ∈ Polynomial.lifts (residue A) :=
    Polynomial.map_surjective _ residue_surjective p
  obtain ⟨P, hPmap, hPdeg, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon
  have hdeg : P.degree ≠ 0 := by
    rw [hPdeg]
    exact fun h => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero Ω P hdeg
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 ⟨P, hPmon, hα⟩
  refine ⟨residue A y, ?_⟩
  have hy : Polynomial.aeval y P = 0 := by
    apply FaithfulSMul.algebraMap_injective A Ω
    rw [← Polynomial.aeval_algebraMap_apply, hα, map_zero]
  rw [← hPmap, Polynomial.eval_map]
  simpa [Polynomial.aeval_def, Polynomial.hom_eval₂] using congrArg (residue A) hy

/-- An algebraically closed field has `n`-th roots of all elements (of `K`), for `n ≠ 0`, in every
characteristic. -/
theorem hasKummerRoots_of_isAlgClosed {n : ℕ} (hn : n ≠ 0) (K L : Type*) [Field K] [Field L]
    [Algebra K L] [IsAlgClosed L] : HasKummerRoots n K L where
  exists_pow_eq a := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K L a) (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn, eq_comm, map_eq_zero_iff _ (algebraMap K L).injective] at hz
      exact a.ne_zero hz
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩

/-! ### The residue field is algebraic over the constants -/

section General

variable {K : Type*} [NormedField K] (F : Type*) {Ω : Type*} [Field F] [Field Ω] [Algebra K F]
  [Algebra F Ω] [Algebra K Ω] [IsScalarTower K F Ω] [Algebra K⟦X⟧ F]

/-- The constants lie in a valuation subring containing the image of `K⟦X⟧`. -/
theorem algebraMap_mem_of_dominating
    (hCF : ∀ c : K, algebraMap K⟦X⟧ F (C c) = algebraMap K F c) (A : ValuationSubring Ω)
    (hA : ∀ r : K⟦X⟧, algebraMap F Ω (algebraMap K⟦X⟧ F r) ∈ A) (c : K) :
    algebraMap K Ω c ∈ A := by
  rw [IsScalarTower.algebraMap_apply K F Ω, ← hCF]
  exact hA (C c)

section Residue

variable [IsFractionRing K⟦X⟧ F]
  (hCF : ∀ c : K, algebraMap K⟦X⟧ F (C c) = algebraMap K F c)
  (A : ValuationSubring Ω) (hk : ∀ c : K, algebraMap K Ω c ∈ A) [Algebra K (ResidueField A)]
  (hkres : ∀ c : K, residue A ⟨algebraMap K Ω c, hk c⟩ = algebraMap K (ResidueField A) c)
  (hA : ∀ r : K⟦X⟧, algebraMap F Ω (algebraMap K⟦X⟧ F r) ∈ A) (hX : residue A ⟨_, hA X⟩ = 0)

include hCF hkres hX in
/-- If `A ⊆ Ω` dominates `K⟦X⟧` and `b ∈ A` is algebraic over `F = Frac K⟦X⟧`, then its residue
is algebraic over `K`. -/
theorem isIntegral_residue (b : A) (hb : IsAlgebraic F (b : Ω)) :
    IsIntegral K (residue A b) := by
  set φ : K⟦X⟧ →+* Ω := (algebraMap F Ω).comp (algebraMap K⟦X⟧ F) with hφ
  have hφinj : Function.Injective φ :=
    (algebraMap F Ω).injective.comp (IsFractionRing.injective K⟦X⟧ F)
  set ψ : K⟦X⟧ →+* A := φ.codRestrict A.toSubring hA with hψ
  have hψφ : A.subtype.comp ψ = φ := rfl
  -- a nonzero polynomial over `K⟦X⟧` killing `b`
  obtain ⟨p, hp0, hpb⟩ := hb
  set q := IsLocalization.integerNormalization (nonZeroDivisors K⟦X⟧) p
  have hq0 : q ≠ 0 := by
    rwa [Ne, IsFractionRing.integerNormalization_eq_zero_iff]
  have hqb : Polynomial.eval₂ φ (b : Ω) q = 0 :=
    IsLocalization.integerNormalization_eval₂_eq_zero _ _ _ (by rwa [← Polynomial.aeval_def])
  -- divide by the largest power of `X` dividing all coefficients
  obtain ⟨i₀, hi₀, hmin⟩ := q.support.exists_min_image (fun i => (q.coeff i).order)
    (Polynomial.support_nonempty.2 hq0)
  have hi₀' : q.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.1 hi₀
  set k := (q.coeff i₀).order.toNat
  have hk_ord : ((k : ℕ) : ℕ∞) = (q.coeff i₀).order :=
    ENat.coe_toNat (order_eq_top.not.2 hi₀')
  have hdvd : Polynomial.C (X ^ k : K⟦X⟧) ∣ q := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    by_cases hi : q.coeff i = 0
    · rw [hi]; exact dvd_zero _
    rw [X_pow_dvd_iff]
    intro m hm
    apply coeff_of_lt_order
    calc (m : ℕ∞) < k := by exact_mod_cast hm
      _ = (q.coeff i₀).order := hk_ord
      _ ≤ (q.coeff i).order := hmin i (Polynomial.mem_support_iff.2 hi)
  obtain ⟨q', hq'⟩ := hdvd
  have hXk : φ (X ^ k) ≠ 0 := by
    rw [Ne, ← map_zero φ, hφinj.eq_iff]
    exact pow_ne_zero _ X_ne_zero
  have hq'b : Polynomial.eval₂ φ (b : Ω) q' = 0 := by
    rw [hq', Polynomial.eval₂_mul, Polynomial.eval₂_C] at hqb
    exact (mul_eq_zero.1 hqb).resolve_left hXk
  have hc : constantCoeff (q'.coeff i₀) ≠ 0 := by
    have h : coeff k (q.coeff i₀) ≠ 0 := coeff_order hi₀'
    rw [hq', Polynomial.coeff_C_mul, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply] at h
    exact h
  -- reduce modulo `𝔪_A`
  have hψb : Polynomial.eval₂ ψ b q' = 0 := by
    apply Subtype.ext
    change A.subtype (Polynomial.eval₂ ψ b q') = 0
    rw [Polynomial.hom_eval₂, hψφ]
    exact hq'b
  have hred : (algebraMap K (ResidueField A)).comp (pointEval : K⟦X⟧ →ₐ[K] K).toRingHom =
      (residue A).comp ψ := by
    ext r
    exact (TateParameter.residue_eq_pointEval F hCF A hk hkres hA hX r).symm
  refine (IsAlgebraic.isIntegral ⟨q'.map (pointEval : K⟦X⟧ →ₐ[K] K).toRingHom, ?_, ?_⟩)
  · intro h
    apply hc
    have := congrArg (Polynomial.coeff · i₀) h
    simpa using this
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map, hred, ← Polynomial.hom_eval₂, hψb, map_zero]

include hCF hkres hX in
/-- **The residue field of `A` is algebraic over `K`** when `Ω` is algebraic over
`F = Frac K⟦X⟧` and `A` dominates `K⟦X⟧`. -/
theorem isIntegral_residueField [Algebra.IsAlgebraic F Ω] :
    Algebra.IsIntegral K (ResidueField A) where
  isIntegral x := by
    obtain ⟨b, rfl⟩ := residue_surjective x
    exact isIntegral_residue F hCF A hk hkres hA hX b (Algebra.IsAlgebraic.isAlgebraic _)

include hCF hkres hX in
/-- For `Ω` algebraically closed and algebraic over `F = Frac K⟦X⟧`, the residue field of a
valuation subring dominating `K⟦X⟧` is an algebraic closure of `K`. -/
theorem isAlgClosure_residueField [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] :
    IsAlgClosure K (ResidueField A) :=
  haveI := isIntegral_residueField F hCF A hk hkres hA hX
  ⟨isAlgClosed_residueField A, inferInstance⟩

end Residue

/-! ### The corollary -/

variable [IsFractionRing K⟦X⟧ F] (hCF : ∀ c : K, algebraMap K⟦X⟧ F (C c) = algebraMap K F c)
  (A : ValuationSubring Ω) (hA : ∀ r : K⟦X⟧, algebraMap F Ω (algebraMap K⟦X⟧ F r) ∈ A)
  (hX : residue A ⟨_, hA X⟩ = 0)
  [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω] (n : ℕ) (hn : n ≠ 0)

namespace TateParameter

variable (t : TateParameter K)

include hCF hX in
/-- **`decomposition_kummer_thetaGerm` over an algebraically closed field.** For `Ω`
algebraically closed and algebraic over `F = Frac K⟦X⟧`, and `A ⊆ Ω` a valuation subring
dominating `K⟦X⟧`, the residue field `κ(A)` (with its canonical `K`-algebra structure) is an
algebraic closure of `K`, and the restriction of `κ_F(Θ_u)` to `D_A` is the inflation of
`κ_K(θ(u))`. -/
theorem decomposition_kummer_thetaGerm_of_isAlgClosed (u : Kˣ) (hu : t.theta u ≠ 0) :
    letI := Decomposition.residueAlgebra A (algebraMap_mem_of_dominating F hCF A hA)
    haveI := isIntegral_residueField F hCF A (algebraMap_mem_of_dominating F hCF A hA)
      (fun _ => rfl) hA hX
    haveI := hasKummerRoots_of_isAlgClosed hn F Ω
    haveI := isAlgClosed_residueField A
    haveI := hasKummerRoots_of_isAlgClosed hn K (ResidueField A)
    letI := Decomposition.muAction F A (algebraMap_mem_of_dominating F hCF A hA)
      (fun _ => rfl) n
    ContH1.map (A.decompositionSubgroup F).subtype continuous_subtype_val
        (Decomposition.reduceMu A n hn) continuous_of_discreteTopology
        (Decomposition.reduceMu_smul F A _ (fun _ => rfl) n hn)
        (kummer n F Ω (Units.map (algebraMap K⟦X⟧ F : K⟦X⟧ →* F) (t.thetaGermUnit u hu))) =
      ContH1.map (Decomposition.decompositionMap F A _ (fun _ => rfl))
        (Decomposition.continuous_decompositionMap F A _ (fun _ => rfl)) (MonoidHom.id _)
        continuous_id (fun _ _ => rfl) (kummer n K (ResidueField A) (t.thetaUnit u hu)) :=
  letI := Decomposition.residueAlgebra A (algebraMap_mem_of_dominating F hCF A hA)
  haveI := isIntegral_residueField F hCF A (algebraMap_mem_of_dominating F hCF A hA)
    (fun _ => rfl) hA hX
  haveI := hasKummerRoots_of_isAlgClosed hn F Ω
  haveI := isAlgClosed_residueField A
  haveI := hasKummerRoots_of_isAlgClosed hn K (ResidueField A)
  t.decomposition_kummer_thetaGerm F hCF A _ (fun _ => rfl) hA hX n hn u hu

end TateParameter

end General

section LaurentSeries

-- The scalar tower is stated with the `SMul` instances coming from the algebra structures: the
-- default `SMul K (LaurentSeries K)` (the `HahnSeries` one) is not reducibly `Algebra.toSMul`.
variable {K : Type*} [NormedField K] {Ω : Type*} [Field Ω] [Algebra (LaurentSeries K) Ω]
  [Algebra K Ω] [@IsScalarTower K (LaurentSeries K) Ω Algebra.toSMul Algebra.toSMul Algebra.toSMul]
  [IsAlgClosed Ω]
  [Algebra.IsAlgebraic (LaurentSeries K) Ω] (A : ValuationSubring Ω)
  (hA : ∀ r : K⟦X⟧, algebraMap (LaurentSeries K) Ω (algebraMap K⟦X⟧ (LaurentSeries K) r) ∈ A)
  (hX : residue A ⟨_, hA X⟩ = 0) (n : ℕ) (hn : n ≠ 0)

include hX in
/-- For `Ω` an algebraically closed algebraic extension of `K((X))` (e.g. its algebraic
closure) and `A ⊆ Ω` dominating `K⟦X⟧`, the residue field `κ(A)` is an algebraic closure of
`K`. -/
theorem isAlgClosure_residueField_laurentSeries :
    letI := Decomposition.residueAlgebra A
      (algebraMap_mem_of_dominating (LaurentSeries K) TateParameter.laurentSeries_algebraMap_C A hA)
    IsAlgClosure K (ResidueField A) :=
  letI := Decomposition.residueAlgebra A
    (algebraMap_mem_of_dominating (LaurentSeries K) TateParameter.laurentSeries_algebraMap_C A hA)
  isAlgClosure_residueField (LaurentSeries K) TateParameter.laurentSeries_algebraMap_C A _
    (fun _ => rfl) hA hX

variable (t : TateParameter K)

include hX in
/-- **`decomposition_kummer_thetaGerm` for `F = K((X))` and `Ω` algebraically closed** (e.g.
`Ω = AlgebraicClosure K((X))`), with the canonical `K`-algebra structure on `κ(A)`: the only
hypotheses left are that `A` dominates `K⟦X⟧`, `n ≠ 0` and `θ(u) ≠ 0`. -/
theorem TateParameter.decomposition_kummer_thetaGerm_laurentSeries (u : Kˣ)
    (hu : t.theta u ≠ 0) :
    letI := Decomposition.residueAlgebra A
      (algebraMap_mem_of_dominating (LaurentSeries K) TateParameter.laurentSeries_algebraMap_C A hA)
    haveI := isIntegral_residueField (LaurentSeries K) TateParameter.laurentSeries_algebraMap_C A
      (algebraMap_mem_of_dominating (LaurentSeries K) TateParameter.laurentSeries_algebraMap_C A hA)
      (fun _ => rfl) hA hX
    haveI := hasKummerRoots_of_isAlgClosed hn (LaurentSeries K) Ω
    haveI := isAlgClosed_residueField A
    haveI := hasKummerRoots_of_isAlgClosed hn K (ResidueField A)
    letI := Decomposition.muAction (LaurentSeries K) A
      (algebraMap_mem_of_dominating (LaurentSeries K) TateParameter.laurentSeries_algebraMap_C A hA)
      (fun _ => rfl) n
    ContH1.map (A.decompositionSubgroup (LaurentSeries K)).subtype continuous_subtype_val
        (Decomposition.reduceMu A n hn) continuous_of_discreteTopology
        (Decomposition.reduceMu_smul (LaurentSeries K) A _ (fun _ => rfl) n hn)
        (kummer n (LaurentSeries K) Ω
          (Units.map (algebraMap K⟦X⟧ (LaurentSeries K) : K⟦X⟧ →* LaurentSeries K)
            (t.thetaGermUnit u hu))) =
      ContH1.map (Decomposition.decompositionMap (LaurentSeries K) A _ (fun _ => rfl))
        (Decomposition.continuous_decompositionMap (LaurentSeries K) A _ (fun _ => rfl))
        (MonoidHom.id _) continuous_id (fun _ _ => rfl)
        (kummer n K (ResidueField A) (t.thetaUnit u hu)) :=
  t.decomposition_kummer_thetaGerm_of_isAlgClosed (LaurentSeries K)
    TateParameter.laurentSeries_algebraMap_C A hA hX n hn u hu

/-- The hypotheses are satisfiable: `AlgebraicClosure K((X))` has valuation subrings dominating
`K⟦X⟧`. -/
example : ∃ (A : ValuationSubring (AlgebraicClosure (LaurentSeries K)))
    (hA : ∀ r : K⟦X⟧, algebraMap (LaurentSeries K) (AlgebraicClosure (LaurentSeries K))
      (algebraMap K⟦X⟧ (LaurentSeries K) r) ∈ A), residue A ⟨_, hA X⟩ = 0 :=
  TateParameter.exists_valuationSubring_dominating_laurentSeries _

/-- The corollary applies to `Ω = AlgebraicClosure K((X))` (all instance hypotheses are found). -/
example (A : ValuationSubring (AlgebraicClosure (LaurentSeries K)))
    (hA : ∀ r : K⟦X⟧, algebraMap (LaurentSeries K) (AlgebraicClosure (LaurentSeries K))
      (algebraMap K⟦X⟧ (LaurentSeries K) r) ∈ A) (hX : residue A ⟨_, hA X⟩ = 0)
    (n : ℕ) (hn : n ≠ 0) (t : TateParameter K) (u : Kˣ) (hu : t.theta u ≠ 0) :=
  t.decomposition_kummer_thetaGerm_laurentSeries A hA hX n hn u hu

end LaurentSeries

end TateCurvesTheta
