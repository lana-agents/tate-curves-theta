/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TateCurvesTheta.TateCurve.CoordinateExpansion

/-!
# The Tate coordinate `Y` as a two-sided Laurent series on the fundamental annulus

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the Tate
coordinate `Y(u) = ∑' n : ℤ, (qⁿu)²/(1 - qⁿu)³ + s₁(q)` (`TateCurve/Parametrization.lean`) develops
as an explicit **two-sided Laurent series in `u`** on the fundamental annulus
`1 < ‖u‖ < ‖q‖⁻¹` (equivalently `1 < ‖u‖` and `‖q‖·‖u‖ < 1`). This is the `Y`-coordinate companion
of `TateCurve/CoordinateAnnulusLaurent.lean` (which handles `X`); both are steps of the
pole-cancellation Laurent development of the Weierstrass defect (issue #146). The per-term geometric
expansions (step 1) live in `TateCurve/CoordinateExpansion.lean`.

## The mechanism

On the annulus the `ℤ`-index of `Y = ∑ₙ Yterm` splits by the size of `‖qⁿu‖ = ‖q‖ⁿ‖u‖`:

* `n ≥ 1` (inner side `‖qⁿu‖ ≤ ‖q‖‖u‖ < 1`): the `Yterm` develops as `∑ₘ C(m+2,2)·(qⁿu)^{m+2}`
  (`Yterm_hasSum_of_norm_lt_one`);
* `n ≤ 0` (outer side `‖qⁿu‖ ≥ ‖u‖ > 1`): the `Yterm` develops as `∑ₘ -C(m+2,2)·((qⁿu)⁻¹)^{m+1}`
  (`Yterm_hasSum_of_one_lt_norm`).

Each half is a joint sum over `ℕ × ℕ` (the `ℤ`-index and the geometric index), unconditionally
summable in the ultrametric setting by a product-geometric norm bound; collapsing the two
coordinates in turn (`HasSum.prod_fiberwise`) — once to recover the analytic terms `Yterm`, once to
sum the geometric series in the `ℤ`-index — yields the closed-form binomial coefficients:
```
Y u = ∑_{m ≥ 2} [C(m,2)·qᵐ/(1-qᵐ)]·uᵐ  −  ∑_{m ≥ 1} [C(m+1,2)/(1-qᵐ)]·u⁻ᵐ  +  s₁(q),
```
a genuine two-sided Laurent series in `u` (the `u¹`-coefficient vanishes since `C(1,2) = 0`),
packaged by `TateParameter.YLaurentCoeff`.

## Main definitions

* `TateCurvesTheta.TateParameter.YLaurentCoeff`: the closed-form coefficients of the annulus
  Laurent development of `Y`.

## Main results

* `TateParameter.Y_inner_collapse` / `TateParameter.Y_outer_collapse`: each half of the `ℤ`-index
  collapses to a one-sided closed-form power series in `u` resp. `u⁻¹`.
* `TateParameter.Y_hasSum_laurent`: on the annulus, `Y(u) = ∑' m : ℤ, YLaurentCoeff m · uᵐ`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* A. Robert, *A Course in p-adic Analysis*, §6 (convergent Laurent series on annuli).
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K) (u : Kˣ)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The shifted geometric series: for `‖x‖ < 1`, `∑ⱼ x^{j+1} = x/(1-x)`. -/
private lemma hasSum_geom_succ' {x : K} (hx : ‖x‖ < 1) :
    HasSum (fun j : ℕ => x ^ (j + 1)) (x * (1 - x)⁻¹) := by
  have h := (hasSum_geometric_of_norm_lt_one hx).mul_left x
  simpa only [← pow_succ'] using h

/-- **Coefficients of the annulus Laurent development of `Y`.** For `m > 0` the coefficient of `uᵐ`
is `C(m,2)·qᵐ/(1-qᵐ)` (which vanishes for `m = 1` as `C(1,2) = 0`); for `m < 0` the coefficient of
`uᵐ` is `-C(-m+1,2)/(1-q^{-m})`; the constant term is `s₁(q)`. All binomial-Eisenstein-type and
independent of `u`. -/
def YLaurentCoeff : ℤ → K := fun m =>
  if 0 < m then (m.toNat.choose 2 : K) * (t.q : K) ^ m.toNat / (1 - (t.q : K) ^ m.toNat)
  else if m < 0 then -(((-m).toNat + 1).choose 2 : K) / (1 - (t.q : K) ^ (-m).toNat)
  else t.eisenstein 1

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma YLaurentCoeff_of_pos {m : ℤ} (hm : 0 < m) :
    t.YLaurentCoeff m
      = (m.toNat.choose 2 : K) * (t.q : K) ^ m.toNat / (1 - (t.q : K) ^ m.toNat) := by
  simp only [YLaurentCoeff, if_pos hm]

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma YLaurentCoeff_of_neg {m : ℤ} (hm : m < 0) :
    t.YLaurentCoeff m = -(((-m).toNat + 1).choose 2 : K) / (1 - (t.q : K) ^ (-m).toNat) := by
  simp only [YLaurentCoeff, if_neg (not_lt.mpr hm.le), if_pos hm]

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma YLaurentCoeff_zero : t.YLaurentCoeff 0 = t.eisenstein 1 := by
  simp only [YLaurentCoeff, lt_self_iff_false, if_false]

/-- The inner joint family over `ℕ × ℕ`: the `(m)`-th geometric coefficient of the `Y`-term
`Yterm u (j+1)` on the inner side `‖q^{j+1}u‖ < 1`. -/
private def YinnerFamily (p : ℕ × ℕ) : K :=
  ((p.2 + 2).choose 2 : K) * ((t.q : K) ^ ((p.1 : ℤ) + 1) * (u : K)) ^ (p.2 + 2)

/-- The outer joint family over `ℕ × ℕ`: the `(m)`-th geometric coefficient of the `Y`-term
`Yterm u (-j)` on the outer side `1 < ‖q^{-j}u‖`. -/
private def YouterFamily (p : ℕ × ℕ) : K :=
  -(((p.2 + 2).choose 2 : K) * (((t.q : K) ^ (-(p.1 : ℤ)) * (u : K))⁻¹) ^ (p.2 + 1))

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma YinnerFamily_eq (j m : ℕ) :
    t.YinnerFamily u (j, m)
      = ((m + 2).choose 2 : K) * (u : K) ^ (m + 2) * ((t.q : K) ^ (m + 2)) ^ (j + 1) := by
  have hz : (t.q : K) ^ ((j : ℤ) + 1) = (t.q : K) ^ (j + 1) := by
    rw [(by push_cast; ring : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ)), zpow_natCast]
  simp only [YinnerFamily, hz, mul_pow]
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma YouterFamily_eq (j m : ℕ) :
    t.YouterFamily u (j, m)
      = -(((m + 2).choose 2 : K) * ((u : K)⁻¹) ^ (m + 1) * ((t.q : K) ^ (m + 1)) ^ j) := by
  have hz : ((t.q : K) ^ (-(j : ℤ)) * (u : K))⁻¹ = (t.q : K) ^ j * (u : K)⁻¹ := by
    rw [mul_inv, zpow_neg, inv_inv, zpow_natCast]
  simp only [YouterFamily, hz, mul_pow]
  ring

/-- **Inner half-collapse of `Y`.** On the inner side `‖q‖·‖u‖ < 1`, the `ℤ`-index sum
`∑_{n ≥ 1} Yterm u n` equals the closed-form one-sided power series
`∑_{m ≥ 0} [C(m+2,2)·q^{m+2}/(1-q^{m+2})]·u^{m+2}` (both summing to the same value `S`). -/
lemma Y_inner_collapse (h2 : ‖(t.q : K)‖ * ‖(u : K)‖ < 1) :
    ∃ S : K, HasSum (fun j : ℕ => t.Yterm u ((j : ℤ) + 1)) S ∧
      HasSum (fun m : ℕ =>
        ((m + 2).choose 2 : K) * (u : K) ^ (m + 2) * (t.q : K) ^ (m + 2)
          * (1 - (t.q : K) ^ (m + 2))⁻¹) S := by
  have hdom : Summable (fun p : ℕ × ℕ =>
      ‖(t.q : K)‖ ^ p.1 * (‖(t.q : K)‖ * ‖(u : K)‖) ^ p.2) :=
    Summable.mul_of_nonneg
      (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one)
      (summable_geometric_of_lt_one (by positivity) h2)
      (fun _ => by positivity) (fun _ => by positivity)
  have hsum : Summable (t.YinnerFamily u) := by
    refine hdom.of_norm_bounded ?_
    intro p
    obtain ⟨j, m⟩ := p
    have hz : (t.q : K) ^ ((j : ℤ) + 1) = (t.q : K) ^ (j + 1) := by
      rw [(by push_cast; ring : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ)), zpow_natCast]
    have hb : ‖(t.q : K)‖ ^ (j + 1) * ‖(u : K)‖
        = ‖(t.q : K)‖ ^ j * (‖(t.q : K)‖ * ‖(u : K)‖) := by rw [pow_succ]; ring
    rw [YinnerFamily, hz, norm_mul, norm_pow, norm_mul, norm_pow]
    calc ‖((m + 2).choose 2 : K)‖ * (‖(t.q : K)‖ ^ (j + 1) * ‖(u : K)‖) ^ (m + 2)
        ≤ 1 * (‖(t.q : K)‖ ^ (j + 1) * ‖(u : K)‖) ^ (m + 2) := by
          apply mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one K _)
          positivity
      _ = ‖(t.q : K)‖ ^ (j * (m + 2)) * (‖(t.q : K)‖ * ‖(u : K)‖) ^ (m + 2) := by
          rw [one_mul, hb, mul_pow, ← pow_mul]
      _ ≤ ‖(t.q : K)‖ ^ j * (‖(t.q : K)‖ * ‖(u : K)‖) ^ (m + 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le
            (Nat.le_mul_of_pos_right j (by omega))
      _ ≤ ‖(t.q : K)‖ ^ j * (‖(t.q : K)‖ * ‖(u : K)‖) ^ m := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_of_le_one (by positivity) h2.le (by omega)
  have hfibj : ∀ j : ℕ,
      HasSum (fun m : ℕ => t.YinnerFamily u (j, m)) (t.Yterm u ((j : ℤ) + 1)) := by
    intro j
    have hnorm : ‖(t.q : K) ^ ((j : ℤ) + 1) * (u : K)‖ < 1 := by
      rw [(by push_cast; ring : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ)), zpow_natCast, norm_mul,
        norm_pow]
      calc ‖(t.q : K)‖ ^ (j + 1) * ‖(u : K)‖
          ≤ ‖(t.q : K)‖ * ‖(u : K)‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            calc ‖(t.q : K)‖ ^ (j + 1) ≤ ‖(t.q : K)‖ ^ 1 :=
                  pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le (by omega)
              _ = ‖(t.q : K)‖ := pow_one _
        _ < 1 := h2
    simpa only [YinnerFamily] using t.Yterm_hasSum_of_norm_lt_one u ((j : ℤ) + 1) hnorm
  have hfibm : ∀ m : ℕ, HasSum (fun j : ℕ => t.YinnerFamily u (j, m))
      (((m + 2).choose 2 : K) * (u : K) ^ (m + 2) * (t.q : K) ^ (m + 2)
        * (1 - (t.q : K) ^ (m + 2))⁻¹) := by
    intro m
    simp only [t.YinnerFamily_eq u]
    have hx : ‖(t.q : K) ^ (m + 2)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) t.norm_lt_one (by omega)
    have hgeom := (hasSum_geom_succ' hx).mul_left (((m + 2).choose 2 : K) * (u : K) ^ (m + 2))
    have hval : ((m + 2).choose 2 : K) * (u : K) ^ (m + 2) * (t.q : K) ^ (m + 2)
        * (1 - (t.q : K) ^ (m + 2))⁻¹
        = ((m + 2).choose 2 : K) * (u : K) ^ (m + 2)
            * ((t.q : K) ^ (m + 2) * (1 - (t.q : K) ^ (m + 2))⁻¹) := by ring
    rw [hval]
    exact hgeom
  refine ⟨∑' p : ℕ × ℕ, t.YinnerFamily u p, hsum.hasSum.prod_fiberwise hfibj, ?_⟩
  exact ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum).prod_fiberwise hfibm

/-- **Outer half-collapse of `Y`.** On the outer side `1 < ‖u‖`, the `ℤ`-index sum
`∑_{n ≤ 0} Yterm u n` equals the closed-form one-sided power series in `u⁻¹`,
`∑_{m ≥ 0} -[C(m+2,2)/(1-q^{m+1})]·(u⁻¹)^{m+1}` (both summing to the same value `S`). -/
lemma Y_outer_collapse (h1 : 1 < ‖(u : K)‖) :
    ∃ S : K, HasSum (fun j : ℕ => t.Yterm u (-(j : ℤ))) S ∧
      HasSum (fun m : ℕ =>
        -(((m + 2).choose 2 : K) * ((u : K)⁻¹) ^ (m + 1) * (1 - (t.q : K) ^ (m + 1))⁻¹)) S := by
  have hdom : Summable (fun p : ℕ × ℕ =>
      ‖(t.q : K)‖ ^ p.1 * (‖(u : K)‖⁻¹) ^ p.2) :=
    Summable.mul_of_nonneg
      (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one)
      (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ h1))
      (fun _ => by positivity) (fun _ => by positivity)
  have hinvlt : ‖(u : K)‖⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ h1).le
  have hsum : Summable (t.YouterFamily u) := by
    refine hdom.of_norm_bounded ?_
    intro p
    obtain ⟨j, m⟩ := p
    have hz : ((t.q : K) ^ (-(j : ℤ)) * (u : K))⁻¹ = (t.q : K) ^ j * (u : K)⁻¹ := by
      rw [mul_inv, zpow_neg, inv_inv, zpow_natCast]
    rw [YouterFamily, norm_neg, hz, norm_mul, norm_pow, norm_mul, norm_pow, norm_inv]
    calc ‖((m + 2).choose 2 : K)‖ * (‖(t.q : K)‖ ^ j * ‖(u : K)‖⁻¹) ^ (m + 1)
        ≤ 1 * (‖(t.q : K)‖ ^ j * ‖(u : K)‖⁻¹) ^ (m + 1) := by
          apply mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one K _)
          positivity
      _ = ‖(t.q : K)‖ ^ (j * (m + 1)) * (‖(u : K)‖⁻¹) ^ (m + 1) := by
          rw [one_mul, mul_pow, ← pow_mul]
      _ ≤ ‖(t.q : K)‖ ^ j * (‖(u : K)‖⁻¹) ^ (m + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le
            (Nat.le_mul_of_pos_right j (by omega))
      _ ≤ ‖(t.q : K)‖ ^ j * (‖(u : K)‖⁻¹) ^ m := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_of_le_one (by positivity) hinvlt (by omega)
  have hfibj : ∀ j : ℕ,
      HasSum (fun m : ℕ => t.YouterFamily u (j, m)) (t.Yterm u (-(j : ℤ))) := by
    intro j
    have hnorm : 1 < ‖(t.q : K) ^ (-(j : ℤ)) * (u : K)‖ := by
      rw [norm_mul, norm_zpow, zpow_neg, zpow_natCast]
      have hp : (0 : ℝ) < ‖(t.q : K)‖ ^ j := pow_pos t.norm_q_pos j
      have hle : ‖(t.q : K)‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le
      calc (1 : ℝ) < ‖(u : K)‖ := h1
        _ ≤ (‖(t.q : K)‖ ^ j)⁻¹ * ‖(u : K)‖ :=
            le_mul_of_one_le_left (norm_nonneg _) (one_le_inv_iff₀.mpr ⟨hp, hle⟩)
    simpa only [YouterFamily] using t.Yterm_hasSum_of_one_lt_norm u (-(j : ℤ)) hnorm
  have hfibm : ∀ m : ℕ, HasSum (fun j : ℕ => t.YouterFamily u (j, m))
      (-(((m + 2).choose 2 : K) * ((u : K)⁻¹) ^ (m + 1) * (1 - (t.q : K) ^ (m + 1))⁻¹)) := by
    intro m
    simp only [t.YouterFamily_eq u]
    have hx : ‖(t.q : K) ^ (m + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) t.norm_lt_one (by omega)
    exact ((hasSum_geometric_of_norm_lt_one hx).mul_left
      (((m + 2).choose 2 : K) * ((u : K)⁻¹) ^ (m + 1))).neg
  refine ⟨∑' p : ℕ × ℕ, t.YouterFamily u p, hsum.hasSum.prod_fiberwise hfibj, ?_⟩
  exact ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum).prod_fiberwise hfibm

/-- **The Tate coordinate `Y` as a two-sided Laurent series on the fundamental annulus.** For
`1 < ‖u‖` and `‖q‖·‖u‖ < 1` (equivalently `1 < ‖u‖ < ‖q‖⁻¹`),
`Y(u) = ∑' m : ℤ, YLaurentCoeff m · uᵐ`, a convergent two-sided Laurent series with
binomial-Eisenstein-type coefficients. This is the `Y`-coordinate companion of `X_hasSum_laurent`,
feeding the pole-cancellation Laurent development of the Weierstrass defect (#146). -/
theorem Y_hasSum_laurent (h1 : 1 < ‖(u : K)‖) (h2 : ‖(t.q : K)‖ * ‖(u : K)‖ < 1) :
    HasSum (fun m : ℤ => t.YLaurentCoeff m * (u : K) ^ m) (t.Y u) := by
  obtain ⟨Sin, hYin, hGin⟩ := t.Y_inner_collapse u h2
  obtain ⟨Sout, hYout, hGout⟩ := t.Y_outer_collapse u h1
  -- Split the `ℤ`-index sum of `Yterm` into `n ≥ 1` and `n ≤ 0`, identifying `∑' n, Yterm` with
  -- `Sin + Sout`.
  have hYpos : HasSum (fun n : ℤ => if 0 < n then t.Yterm u n else 0) Sin := by
    have hinj : Function.Injective (fun k : ℕ => (k : ℤ) + 1) := by
      intro a b h; simpa using h
    apply (hinj.hasSum_iff ?_).mp
    · have hcomp : (fun n : ℤ => if 0 < n then t.Yterm u n else 0) ∘ (fun k : ℕ => (k : ℤ) + 1)
          = fun k : ℕ => t.Yterm u ((k : ℤ) + 1) := by
        funext k
        simp only [Function.comp_apply]
        rw [if_pos (by positivity)]
      rw [hcomp]; exact hYin
    · intro n hn
      rw [Set.mem_range] at hn
      have hn0 : ¬ (0 < n) := fun hpos => hn ⟨(n - 1).toNat, by omega⟩
      rw [if_neg hn0]
  have hYnp : HasSum (fun n : ℤ => if n ≤ 0 then t.Yterm u n else 0) Sout := by
    have hinj : Function.Injective (fun k : ℕ => -(k : ℤ)) := by
      intro a b h; simpa using h
    apply (hinj.hasSum_iff ?_).mp
    · have hcomp : (fun n : ℤ => if n ≤ 0 then t.Yterm u n else 0) ∘ (fun k : ℕ => -(k : ℤ))
          = fun k : ℕ => t.Yterm u (-(k : ℤ)) := by
        funext k
        simp only [Function.comp_apply]
        rw [if_pos (by omega)]
      rw [hcomp]; exact hYout
    · intro n hn
      rw [Set.mem_range] at hn
      have hn0 : ¬ (n ≤ 0) := fun hnp => hn ⟨(-n).toNat, by omega⟩
      rw [if_neg hn0]
  have hYsum : HasSum
      (fun n : ℤ => (if 0 < n then t.Yterm u n else 0) + (if n ≤ 0 then t.Yterm u n else 0))
      (Sin + Sout) := hYpos.add hYnp
  have hpart : (fun n : ℤ =>
      (if 0 < n then t.Yterm u n else 0) + (if n ≤ 0 then t.Yterm u n else 0)) = t.Yterm u := by
    funext n
    by_cases h : 0 < n
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  rw [hpart] at hYsum
  have htsum : ∑' n : ℤ, t.Yterm u n = Sin + Sout := hYsum.tsum_eq
  -- Assemble the Laurent series from the positive (`m ≥ 2`), negative (`m ≤ -1`), and constant
  -- pieces. The `m = 1` coefficient vanishes since `C(1,2) = 0`.
  have hGpos : HasSum (fun m : ℤ => if 0 < m then t.YLaurentCoeff m * (u : K) ^ m else 0) Sin := by
    have hinj : Function.Injective (fun k : ℕ => (k : ℤ) + 2) := by
      intro a b h; simpa using h
    apply (hinj.hasSum_iff ?_).mp
    · have hcomp :
          (fun m : ℤ => if 0 < m then t.YLaurentCoeff m * (u : K) ^ m else 0)
            ∘ (fun k : ℕ => (k : ℤ) + 2)
          = fun k : ℕ => ((k + 2).choose 2 : K) * (u : K) ^ (k + 2) * (t.q : K) ^ (k + 2)
              * (1 - (t.q : K) ^ (k + 2))⁻¹ := by
        funext k
        simp only [Function.comp_apply]
        rw [if_pos (by positivity : (0 : ℤ) < (k : ℤ) + 2),
          t.YLaurentCoeff_of_pos (by positivity : (0 : ℤ) < (k : ℤ) + 2)]
        rw [(by omega : ((k : ℤ) + 2).toNat = k + 2),
          (by push_cast; ring : ((k : ℤ) + 2) = ((k + 2 : ℕ) : ℤ)), zpow_natCast, div_eq_mul_inv]
        ring
      rw [hcomp]; exact hGin
    · intro m hm
      rw [Set.mem_range] at hm
      have hm1 : m ≤ 1 := by by_contra hlt; exact hm ⟨(m - 2).toNat, by omega⟩
      by_cases h0 : 0 < m
      · have hme : m = 1 := by omega
        subst hme
        have hc : (1 : ℤ).toNat.choose 2 = 0 := by decide
        rw [if_pos h0, t.YLaurentCoeff_of_pos h0, hc]
        simp
      · rw [if_neg h0]
  have hGneg : HasSum (fun m : ℤ => if m < 0 then t.YLaurentCoeff m * (u : K) ^ m else 0) Sout := by
    have hinj : Function.Injective (fun k : ℕ => -((k : ℤ) + 1)) := by
      intro a b h; simpa using h
    apply (hinj.hasSum_iff ?_).mp
    · have hcomp :
          (fun m : ℤ => if m < 0 then t.YLaurentCoeff m * (u : K) ^ m else 0)
            ∘ (fun k : ℕ => -((k : ℤ) + 1))
          = fun k : ℕ =>
              -(((k + 2).choose 2 : K) * ((u : K)⁻¹) ^ (k + 1) * (1 - (t.q : K) ^ (k + 1))⁻¹) := by
        funext k
        simp only [Function.comp_apply]
        rw [if_pos (by omega : -((k : ℤ) + 1) < 0),
          t.YLaurentCoeff_of_neg (by omega : -((k : ℤ) + 1) < 0)]
        rw [(by omega : (-(-((k : ℤ) + 1))).toNat + 1 = k + 2),
          (by omega : (-(-((k : ℤ) + 1))).toNat = k + 1),
          (by push_cast; ring : -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ)), zpow_neg, zpow_natCast,
          ← inv_pow, div_eq_mul_inv]
        ring
      rw [hcomp]; exact hGout
    · intro m hm
      rw [Set.mem_range] at hm
      have hm0 : ¬ (m < 0) := fun hneg => hm ⟨(-m - 1).toNat, by omega⟩
      rw [if_neg hm0]
  have hGzero : HasSum (fun m : ℤ => if m = 0 then t.YLaurentCoeff m * (u : K) ^ m else 0)
      (t.eisenstein 1) := by
    have hfun : (fun m : ℤ => if m = 0 then t.YLaurentCoeff (0 : ℤ) * (u : K) ^ (0 : ℤ) else 0)
        = fun m : ℤ => if m = 0 then t.YLaurentCoeff m * (u : K) ^ m else 0 := by
      funext m
      by_cases hm : m = 0
      · subst hm; rfl
      · rw [if_neg hm, if_neg hm]
    have h0 : t.YLaurentCoeff (0 : ℤ) * (u : K) ^ (0 : ℤ) = t.eisenstein 1 := by
      rw [t.YLaurentCoeff_zero, zpow_zero, mul_one]
    have hbase := hasSum_ite_eq (0 : ℤ) (t.YLaurentCoeff (0 : ℤ) * (u : K) ^ (0 : ℤ))
    rw [hfun, h0] at hbase
    exact hbase
  have hG := (hGpos.add hGneg).add hGzero
  have hGfun : (fun m : ℤ =>
        ((if 0 < m then t.YLaurentCoeff m * (u : K) ^ m else 0)
          + (if m < 0 then t.YLaurentCoeff m * (u : K) ^ m else 0))
          + (if m = 0 then t.YLaurentCoeff m * (u : K) ^ m else 0))
      = fun m : ℤ => t.YLaurentCoeff m * (u : K) ^ m := by
    funext m
    rcases lt_trichotomy m 0 with h | h | h
    · rw [if_neg (by omega), if_pos h, if_neg (by omega)]; ring
    · subst h; simp
    · rw [if_pos h, if_neg (by omega), if_neg (by omega)]; ring
  rw [hGfun] at hG
  have hval : Sin + Sout + t.eisenstein 1 = t.Y u := by
    rw [Y_apply, htsum]
  rwa [hval] at hG

end TateParameter

end TateCurvesTheta
