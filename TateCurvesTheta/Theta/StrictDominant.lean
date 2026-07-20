/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.Theta.LaurentUnique

/-!
# Discharging `LaurentStrictDom` for densely-normed fields

`Theta/LaurentUnique.lean` (#121) reduced the nonarchimedean Laurent identity theorem
`LaurentCoeffUnique K` to the single sharp, purely existential seam `LaurentStrictDom K`:
every summable-on-`Kˣ`, not-identically-zero coefficient family `c : ℤ → K` has a radius
`u : Kˣ` and an index `n₀` at which the term `cₙ₀ · uⁿ₀` **strictly dominates** every other term
`cₙ · uⁿ` in norm. This is the Newton-polygon *vertex-selection* step.

This file discharges that seam for **densely-normed** complete ultrametric fields
(`[DenselyNormedField K]` — the value group `‖Kˣ‖` is dense in `ℝ₊`, e.g. `ℂₚ` or any
algebraically closed complete nonarchimedean field, the primary setting of the Tate theory).

## The argument (a *finite* Newton-polygon selection)

Fix two radii `a < b` realised by units `Ua, Ub` (density supplies them). At a radius `ρ ∈ [a, b]`
the term norms are `‖cₙ‖ · ρⁿ`. Summability at `a` and `b` forces `‖cₙ‖aⁿ → 0` and `‖cₙ‖bⁿ → 0`
cofinitely, and on `[a, b]` one has `ρⁿ ≤ aⁿ + bⁿ`; hence only the **finite** index set
`F = {n | M₀ ≤ ‖cₙ‖aⁿ + ‖cₙ‖bⁿ}` (with `M₀ := ‖c_m‖ · min (aᵐ) (bᵐ) > 0` a fixed lower bound for
the maximum term coming from a nonzero coefficient `c_m`) can ever attain the maximum term on
`[a, b]`: every index outside `F` stays strictly below `M₀ ≤ T(ρ)`.

Within the finite `F`, two indices `n₁ ≠ n₂` (both with nonzero coefficient) tie at **at most one**
radius (`ρ^{n₁-n₂} = ‖c_{n₂}‖/‖c_{n₁}‖` has a unique positive solution, `zpow_left_inj₀`). So only
finitely many radii in `(a, b)` carry a tie among `F`. Density provides a unit whose radius `ρ`
avoids all of them; there the finite maximiser over `F` is **unique** and, being `≥ M₀`, strictly
dominates every index outside `F` too. That is exactly `LaurentStrictDom`.

## Main results

* `TateCurvesTheta.laurentStrictDom_of_denselyNormed` : `LaurentStrictDom K` for a densely-normed
  complete ultrametric field.
* `TateCurvesTheta.laurentCoeffUnique_of_denselyNormed` : the identity theorem
  `LaurentCoeffUnique K`, now unconditional for such `K`.
* `TateCurvesTheta.TateParameter.const_of_qinvariant_laurent_of_denselyNormed` : the #119
  `q`-difference engine with **no** residual analytic hypothesis, for densely-normed `K`.

## The residual case

The discrete-value-group / finite-residue-field case (e.g. `ℚₚ`), where `LaurentStrictDom` can
genuinely fail radius-by-radius, still needs the Strassmann / finiteness-of-zeros input flagged in
#122 and is *not* covered here. Densely-normed fields are the primary setting for Tate curves, so
this discharges the seam where it matters most.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* A. Robert, *A Course in p-adic Analysis*, §6.1 (the maximum term of a nonarchimedean series).
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, §IV (Newton polygons).
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
-/

open Filter Topology

namespace TateCurvesTheta

/-- A finite subset `B` of `ℝ` cannot cover an open interval: given `a < b` there is a nonempty
open subinterval `(a', b') ⊆ [a, b]` disjoint from `B`. Used to dodge the finitely many
Newton-polygon tie radii before invoking density. -/
theorem exists_Ioo_subset_compl_of_finite {B : Set ℝ} (hB : B.Finite) {a b : ℝ} (hab : a < b) :
    ∃ a' b' : ℝ, a ≤ a' ∧ a' < b' ∧ b' ≤ b ∧ ∀ x, a' < x → x < b' → x ∉ B := by
  classical
  set S : Finset ℝ := hB.toFinset.filter (fun x => a < x ∧ x < b) with hS
  by_cases hSne : S.Nonempty
  · set p : ℝ := S.min' hSne with hp
    have hpS : p ∈ S := S.min'_mem hSne
    rw [hS, Finset.mem_filter] at hpS
    obtain ⟨-, hpa, hpb⟩ := hpS
    refine ⟨a, p, le_refl a, hpa, le_of_lt hpb, ?_⟩
    intro x hx1 hx2 hxB
    have hxS : x ∈ S := by
      rw [hS, Finset.mem_filter, hB.mem_toFinset]
      exact ⟨hxB, hx1, lt_of_lt_of_le hx2 (le_of_lt hpb)⟩
    have hpx : p ≤ x := S.min'_le x hxS
    linarith
  · refine ⟨a, b, le_refl a, hab, le_refl b, ?_⟩
    intro x hx1 hx2 hxB
    exact hSne ⟨x, by rw [hS, Finset.mem_filter, hB.mem_toFinset]; exact ⟨hxB, hx1, hx2⟩⟩

variable {K : Type*} [DenselyNormedField K]

/-- On `[a, b]` (with `0 < a`), every monomial is bounded by the sum of the endpoint monomials:
`ρⁿ ≤ aⁿ + bⁿ`. Increasing exponents are controlled at `b`, decreasing ones at `a`. -/
theorem zpow_le_add_zpow {a b ρ : ℝ} (ha : 0 < a) (haρ : a ≤ ρ) (hρb : ρ ≤ b) (n : ℤ) :
    ρ ^ n ≤ a ^ n + b ^ n := by
  have hρ0 : 0 ≤ ρ := le_trans ha.le haρ
  have hb0 : 0 < b := lt_of_lt_of_le ha (le_trans haρ hρb)
  obtain hn | hn : 0 ≤ n ∨ n < 0 := by omega
  · have h1 : ρ ^ n ≤ b ^ n := zpow_le_zpow_left₀ hn hρ0 hρb
    have h2 : (0 : ℝ) ≤ a ^ n := zpow_nonneg ha.le n
    linarith
  · have h1 : a ^ (-n) ≤ ρ ^ (-n) := zpow_le_zpow_left₀ (by omega) ha.le haρ
    have en : ρ ^ n = (ρ ^ (-n))⁻¹ := by rw [← zpow_neg, neg_neg]
    have ea : a ^ n = (a ^ (-n))⁻¹ := by rw [← zpow_neg, neg_neg]
    have han : (0 : ℝ) < a ^ (-n) := zpow_pos ha _
    have h2 : ρ ^ n ≤ a ^ n := by rw [en, ea]; gcongr
    have h3 : (0 : ℝ) ≤ b ^ n := zpow_nonneg hb0.le n
    linarith

/-- On `[a, b]` (with `0 < a`), every monomial dominates the smaller endpoint monomial:
`min (aⁿ) (bⁿ) ≤ ρⁿ`. This gives a positive lower bound for the maximum term. -/
theorem min_zpow_le_zpow {a b ρ : ℝ} (ha : 0 < a) (haρ : a ≤ ρ) (hρb : ρ ≤ b) (n : ℤ) :
    min (a ^ n) (b ^ n) ≤ ρ ^ n := by
  have hρ0 : 0 ≤ ρ := le_trans ha.le haρ
  have hb0 : 0 < b := lt_of_lt_of_le ha (le_trans haρ hρb)
  obtain hn | hn : 0 ≤ n ∨ n < 0 := by omega
  · have h1 : a ^ n ≤ ρ ^ n := zpow_le_zpow_left₀ hn ha.le haρ
    exact le_trans (min_le_left _ _) h1
  · have h1 : ρ ^ (-n) ≤ b ^ (-n) := zpow_le_zpow_left₀ (by omega) hρ0 hρb
    have en : ρ ^ n = (ρ ^ (-n))⁻¹ := by rw [← zpow_neg, neg_neg]
    have eb : b ^ n = (b ^ (-n))⁻¹ := by rw [← zpow_neg, neg_neg]
    have hρn : (0 : ℝ) < ρ ^ (-n) := zpow_pos (lt_of_lt_of_le ha haρ) _
    have h2 : b ^ n ≤ ρ ^ n := by rw [en, eb]; gcongr
    exact le_trans (min_le_right _ _) h2

/-- **`LaurentStrictDom` for densely-normed complete ultrametric fields.** A nonzero coefficient
family whose Laurent series is summable on all of `Kˣ` has a radius `u : Kˣ` and index `n₀` at
which `cₙ₀ · uⁿ₀` strictly dominates every other term in norm.

The proof is a finite Newton-polygon selection: only finitely many indices can attain the maximum
term on a fixed radius interval `[a, b]`, they pairwise tie at only finitely many radii, and
density supplies a unit whose radius avoids all those ties. -/
theorem laurentStrictDom_of_denselyNormed : LaurentStrictDom K := by
  classical
  rintro c hsum ⟨m, hm⟩
  -- Two radii `a < b`, realised by units `Ua, Ub`, obtained from density of the value group.
  obtain ⟨xa, hxa1, hxa2⟩ :=
    NormedField.exists_lt_norm_lt (α := K) (r₁ := (1 : ℝ)) (r₂ := 2) (by norm_num) (by norm_num)
  obtain ⟨xb, hxb1, hxb2⟩ :=
    NormedField.exists_lt_norm_lt (α := K) (r₁ := (2 : ℝ)) (r₂ := 3) (by norm_num) (by norm_num)
  have hxa0 : xa ≠ 0 := by rintro rfl; rw [norm_zero] at hxa1; linarith
  have hxb0 : xb ≠ 0 := by rintro rfl; rw [norm_zero] at hxb1; linarith
  set Ua : Kˣ := Units.mk0 xa hxa0 with hUa
  set Ub : Kˣ := Units.mk0 xb hxb0 with hUb
  set a : ℝ := ‖xa‖ with ha_def
  set b : ℝ := ‖xb‖ with hb_def
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hab : a < b := by linarith
  have hUav : (Ua : K) = xa := by rw [hUa]; exact Units.val_mk0 hxa0
  have hUbv : (Ub : K) = xb := by rw [hUb]; exact Units.val_mk0 hxb0
  -- Norm of a term at a unit `v` splits as `‖cₙ‖ · ‖v‖ⁿ`.
  have norm_term : ∀ (v : Kˣ) (k : ℤ), ‖c k * (v : K) ^ k‖ = ‖c k‖ * ‖(v : K)‖ ^ k := by
    intro v k; rw [norm_mul, norm_zpow]
  -- Term norms tend to `0` cofinitely at both radii.
  have hta : Tendsto (fun n : ℤ => ‖c n‖ * a ^ n) cofinite (𝓝 0) := by
    have := (hsum Ua).tendsto_cofinite_zero.norm
    simp only [norm_zero] at this
    refine this.congr ?_
    intro n; rw [norm_term Ua n, hUav, ← ha_def]
  have htb : Tendsto (fun n : ℤ => ‖c n‖ * b ^ n) cofinite (𝓝 0) := by
    have := (hsum Ub).tendsto_cofinite_zero.norm
    simp only [norm_zero] at this
    refine this.congr ?_
    intro n; rw [norm_term Ub n, hUbv, ← hb_def]
  set h : ℤ → ℝ := fun n => ‖c n‖ * a ^ n + ‖c n‖ * b ^ n with hh
  have hth : Tendsto h cofinite (𝓝 0) := by simpa [hh] using hta.add htb
  -- A positive lower bound `M₀` for the maximum term on `[a, b]`, from the nonzero coefficient `m`.
  set M₀ : ℝ := ‖c m‖ * min (a ^ m) (b ^ m) with hM₀
  have hcm : 0 < ‖c m‖ := norm_pos_iff.mpr hm
  have hM₀pos : 0 < M₀ := by
    rw [hM₀]; exact mul_pos hcm (lt_min (zpow_pos ha0 m) (zpow_pos hb0 m))
  -- The finite set of indices that can attain the maximum term on `[a, b]`.
  have hFfin : {n : ℤ | M₀ ≤ h n}.Finite := by
    have hev : ∀ᶠ n in cofinite, h n < M₀ := hth.eventually (Iio_mem_nhds hM₀pos)
    refine (eventually_cofinite.mp hev).subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq, not_lt]
    simpa only [Set.mem_setOf_eq] using hn
  set F : Finset ℤ := hFfin.toFinset with hF
  -- `m ∈ F`, so `F` is nonempty.
  have hmF : m ∈ F := by
    rw [hF, hFfin.mem_toFinset]
    change M₀ ≤ h m
    have h1 : min (a ^ m) (b ^ m) ≤ a ^ m := min_le_left _ _
    have h2 : (0 : ℝ) ≤ ‖c m‖ * b ^ m := mul_nonneg (norm_nonneg _) (zpow_nonneg hb0.le m)
    have h3 : ‖c m‖ * min (a ^ m) (b ^ m) ≤ ‖c m‖ * a ^ m :=
      mul_le_mul_of_nonneg_left h1 (norm_nonneg (c m))
    simp only [hM₀, hh]
    linarith
  have hFne : F.Nonempty := ⟨m, hmF⟩
  -- Every index in `F` has a nonzero coefficient.
  have hFcne : ∀ n ∈ F, c n ≠ 0 := by
    intro n hnF hcn
    rw [hF, hFfin.mem_toFinset] at hnF
    have hn' : M₀ ≤ h n := hnF
    simp only [hh, hcn, norm_zero, zero_mul, add_zero] at hn'
    linarith
  -- The finite set of radii carrying a tie among indices of `F`.
  set Bad : Set ℝ :=
    {ρ : ℝ | 0 < ρ ∧ ∃ n₁ ∈ F, ∃ n₂ ∈ F, n₁ ≠ n₂ ∧ ‖c n₁‖ * ρ ^ n₁ = ‖c n₂‖ * ρ ^ n₂} with hBad
  have hBadfin : Bad.Finite := by
    have hfin : (↑F.offDiag : Set (ℤ × ℤ)).Finite := F.offDiag.finite_toSet
    have hbi : (⋃ p ∈ (↑F.offDiag : Set (ℤ × ℤ)),
        {ρ : ℝ | 0 < ρ ∧ ‖c p.1‖ * ρ ^ p.1 = ‖c p.2‖ * ρ ^ p.2}).Finite := by
      refine hfin.biUnion ?_
      intro p hp
      rw [Finset.mem_coe, Finset.mem_offDiag] at hp
      obtain ⟨hp1, _, hpne⟩ := hp
      have hc1 : (0 : ℝ) < ‖c p.1‖ := norm_pos_iff.mpr (hFcne p.1 hp1)
      have hd : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hpne
      apply Set.Subsingleton.finite
      intro ρ hρ ρ' hρ'
      obtain ⟨hρ0, heqρ⟩ := hρ
      obtain ⟨hρ'0, heqρ'⟩ := hρ'
      -- Each tie forces `‖c p.1‖ · ρ^{p.1-p.2} = ‖c p.2‖`.
      have key : ∀ σ : ℝ, 0 < σ → ‖c p.1‖ * σ ^ p.1 = ‖c p.2‖ * σ ^ p.2 →
          ‖c p.1‖ * σ ^ (p.1 - p.2) = ‖c p.2‖ := by
        intro σ hσ0 heq
        have hσne : σ ≠ 0 := ne_of_gt hσ0
        have expand : σ ^ p.1 = σ ^ (p.1 - p.2) * σ ^ p.2 := by
          rw [← zpow_add₀ hσne]; congr 1; ring
        have e2 : (‖c p.1‖ * σ ^ (p.1 - p.2)) * σ ^ p.2 = ‖c p.2‖ * σ ^ p.2 := by
          rw [mul_assoc, ← expand]; exact heq
        exact mul_right_cancel₀ (zpow_ne_zero _ hσne) e2
      have hkρ := key ρ hρ0 heqρ
      have hkρ' := key ρ' hρ'0 heqρ'
      have hpow : ρ ^ (p.1 - p.2) = ρ' ^ (p.1 - p.2) :=
        mul_left_cancel₀ (ne_of_gt hc1) (hkρ.trans hkρ'.symm)
      exact (zpow_left_inj₀ hρ0.le hρ'0.le hd).mp hpow
    refine hbi.subset ?_
    intro ρ hρ
    rw [hBad] at hρ
    obtain ⟨hρ0, n₁, hn₁, n₂, hn₂, hne, heq⟩ := hρ
    rw [Set.mem_iUnion₂]
    exact ⟨(n₁, n₂), Finset.mem_offDiag.mpr ⟨hn₁, hn₂, hne⟩, hρ0, heq⟩
  -- Dodge the finitely many tie radii, then use density to realise a good radius.
  obtain ⟨a', b', haa', ha'b', hb'b, hcompl⟩ := exists_Ioo_subset_compl_of_finite hBadfin hab
  have ha'0 : 0 < a' := lt_of_lt_of_le ha0 haa'
  obtain ⟨x, hx1, hx2⟩ :=
    NormedField.exists_lt_norm_lt (α := K) (r₁ := a') (r₂ := b') ha'0.le ha'b'
  have hx0 : x ≠ 0 := by rintro rfl; rw [norm_zero] at hx1; linarith
  set U : Kˣ := Units.mk0 x hx0 with hU
  set ρ : ℝ := ‖x‖ with hρ
  have hUv : (U : K) = x := rfl
  have hρa : a ≤ ρ := le_trans haa' (le_of_lt hx1)
  have hρb : ρ ≤ b := le_trans (le_of_lt hx2) hb'b
  have hρ0 : 0 < ρ := lt_of_lt_of_le ha0 hρa
  have hρBad : ρ ∉ Bad := hcompl ρ hx1 hx2
  -- The maximiser over the finite `F` at radius `ρ`.
  obtain ⟨n₀, hn₀F, hn₀max⟩ := F.exists_max_image (fun n => ‖c n‖ * ρ ^ n) hFne
  refine ⟨U, n₀, fun n hn => ?_⟩
  rw [norm_term U n, norm_term U n₀, hUv, ← hρ]
  by_cases hnF : n ∈ F
  · -- Inside `F`: `n₀` dominates weakly, and a tie is excluded because `ρ ∉ Bad`.
    rcases lt_or_eq_of_le (hn₀max n hnF) with hlt | heq
    · exact hlt
    · exfalso
      exact hρBad (by rw [hBad]; exact ⟨hρ0, n, hnF, n₀, hn₀F, hn, heq⟩)
  · -- Outside `F`: below `M₀ ≤ ‖c_m‖ρ^m ≤ ‖c_{n₀}‖ρ^{n₀}`.
    have hchain1 : ‖c n‖ * ρ ^ n ≤ h n := by
      have hb := zpow_le_add_zpow ha0 hρa hρb n
      have h' := mul_le_mul_of_nonneg_left hb (norm_nonneg (c n))
      rw [mul_add] at h'
      exact h'
    have hchain2 : h n < M₀ := by
      by_contra hcon
      exact hnF (by rw [hF, hFfin.mem_toFinset]; exact not_lt.mp hcon)
    have hchain3 : M₀ ≤ ‖c m‖ * ρ ^ m := by
      rw [hM₀]
      exact mul_le_mul_of_nonneg_left (min_zpow_le_zpow ha0 hρa hρb m) (norm_nonneg _)
    have hchain4 : ‖c m‖ * ρ ^ m ≤ ‖c n₀‖ * ρ ^ n₀ := hn₀max m hmF
    linarith

variable [CompleteSpace K] [IsUltrametricDist K]

/-- **The nonarchimedean Laurent identity theorem holds for densely-normed fields.** A convergent
two-sided Laurent series over a complete densely-normed ultrametric field is determined by its
values on `Kˣ`. -/
theorem laurentCoeffUnique_of_denselyNormed : LaurentCoeffUnique K :=
  laurentCoeffUnique_of_strictDom laurentStrictDom_of_denselyNormed

namespace TateParameter

variable (t : TateParameter K)

/-- **The `q`-difference engine, unconditional for densely-normed fields.** A `q`-invariant
convergent Laurent series equals its constant term `a₀` everywhere — no residual analytic
hypothesis remains for a complete densely-normed ultrametric `K`. -/
theorem const_of_qinvariant_laurent_of_denselyNormed (a : ℤ → K)
    (hsum : ∀ u : Kˣ, Summable fun n : ℤ => a n * (u : K) ^ n)
    (hqinv : ∀ u : Kˣ,
      (∑' n : ℤ, a n * ((t.q : K) * (u : K)) ^ n) = ∑' n : ℤ, a n * (u : K) ^ n) :
    ∀ u : Kˣ, (∑' n : ℤ, a n * (u : K) ^ n) = a 0 :=
  t.const_of_qinvariant_laurent laurentCoeffUnique_of_denselyNormed a hsum hqinv

end TateParameter

end TateCurvesTheta
