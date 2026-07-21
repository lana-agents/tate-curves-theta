/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import TateCurvesTheta.TateCurve.CoordinateExpansion

/-!
# The Tate coordinate `X` as a two-sided Laurent series on the fundamental annulus

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the Tate
coordinate `X(u) = ∑' n : ℤ, qⁿu/(1 - qⁿu)² - 2 s₁(q)` (`TateCurve/Parametrization.lean`) develops
as an explicit **two-sided Laurent series in `u`** on the fundamental annulus
`1 < ‖u‖ < ‖q‖⁻¹` (equivalently `1 < ‖u‖` and `‖q‖·‖u‖ < 1`). This is step 2 of the
pole-cancellation Laurent development of the Weierstrass defect (issue #146); the per-term
geometric expansions (step 1) live in `TateCurve/CoordinateExpansion.lean`.

## The mechanism

On the annulus the `ℤ`-index of `X = ∑ₙ Xterm` splits by the size of `‖qⁿu‖ = ‖q‖ⁿ‖u‖`:

* `n ≥ 1` (inner side `‖qⁿu‖ ≤ ‖q‖‖u‖ < 1`): the `Xterm` develops as `∑ₘ m·(qⁿu)ᵐ`
  (`Xterm_hasSum_of_norm_lt_one`);
* `n ≤ 0` (outer side `‖qⁿu‖ ≥ ‖u‖ > 1`): the `Xterm` develops as `∑ₘ m·((qⁿu)⁻¹)ᵐ`
  (`Xterm_hasSum_of_one_lt_norm`).

Each half is a joint sum over `ℕ × ℕ` (the `ℤ`-index and the geometric index), unconditionally
summable in the ultrametric setting by a product-geometric norm bound; collapsing the two
coordinates in turn (`HasSum.prod_fiberwise`) — once to recover the analytic terms `Xterm`, once to
sum the geometric series in the `ℤ`-index — yields the closed-form Eisenstein-type coefficients:
```
X u = ∑_{m ≥ 1} [m·qᵐ/(1-qᵐ)]·uᵐ  +  ∑_{m ≥ 1} [m/(1-qᵐ)]·u⁻ᵐ  −  2 s₁(q),
```
a genuine two-sided Laurent series in `u`, packaged by `TateParameter.XLaurentCoeff`.

## Main definitions

* `TateCurvesTheta.TateParameter.XLaurentCoeff`: the closed-form coefficients of the annulus
  Laurent development of `X`.

## Main results

* `TateParameter.X_inner_collapse` / `TateParameter.X_outer_collapse`: each half of the `ℤ`-index
  collapses to a one-sided closed-form power series in `u` resp. `u⁻¹`.
* `TateParameter.X_hasSum_laurent`: on the annulus, `X(u) = ∑' m : ℤ, XLaurentCoeff m · uᵐ`.

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
private lemma hasSum_geom_succ {x : K} (hx : ‖x‖ < 1) :
    HasSum (fun j : ℕ => x ^ (j + 1)) (x * (1 - x)⁻¹) := by
  have h := (hasSum_geometric_of_norm_lt_one hx).mul_left x
  simpa only [← pow_succ'] using h

/-- **Coefficients of the annulus Laurent development of `X`.** For `m > 0` the coefficient of `uᵐ`
is `m·qᵐ/(1-qᵐ)`; for `m < 0` the coefficient of `uᵐ` is `(-m)/(1-q^{-m})`; the constant term is
`-2 s₁(q)`. All Eisenstein-type and independent of `u`. -/
def XLaurentCoeff : ℤ → K := fun m =>
  if 0 < m then (m.toNat : K) * (t.q : K) ^ m.toNat / (1 - (t.q : K) ^ m.toNat)
  else if m < 0 then ((-m).toNat : K) / (1 - (t.q : K) ^ (-m).toNat)
  else -2 * t.eisenstein 1

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma XLaurentCoeff_of_pos {m : ℤ} (hm : 0 < m) :
    t.XLaurentCoeff m = (m.toNat : K) * (t.q : K) ^ m.toNat / (1 - (t.q : K) ^ m.toNat) := by
  simp only [XLaurentCoeff, if_pos hm]

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma XLaurentCoeff_of_neg {m : ℤ} (hm : m < 0) :
    t.XLaurentCoeff m = ((-m).toNat : K) / (1 - (t.q : K) ^ (-m).toNat) := by
  simp only [XLaurentCoeff, if_neg (not_lt.mpr hm.le), if_pos hm]

omit [CompleteSpace K] [IsUltrametricDist K] in
lemma XLaurentCoeff_zero : t.XLaurentCoeff 0 = -2 * t.eisenstein 1 := by
  simp only [XLaurentCoeff, lt_self_iff_false, if_false]

/-- The inner joint family over `ℕ × ℕ`: the `(m)`-th geometric coefficient of the `X`-term
`Xterm u (j+1)` on the inner side `‖q^{j+1}u‖ < 1`. -/
private def XinnerFamily (p : ℕ × ℕ) : K :=
  (p.2 : K) * ((t.q : K) ^ ((p.1 : ℤ) + 1) * (u : K)) ^ p.2

/-- The outer joint family over `ℕ × ℕ`: the `(m)`-th geometric coefficient of the `X`-term
`Xterm u (-j)` on the outer side `1 < ‖q^{-j}u‖`. -/
private def XouterFamily (p : ℕ × ℕ) : K :=
  (p.2 : K) * (((t.q : K) ^ (-(p.1 : ℤ)) * (u : K))⁻¹) ^ p.2

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma XinnerFamily_eq (j m : ℕ) :
    t.XinnerFamily u (j, m) = (m : K) * (u : K) ^ m * ((t.q : K) ^ m) ^ (j + 1) := by
  have hz : (t.q : K) ^ ((j : ℤ) + 1) = (t.q : K) ^ (j + 1) := by
    rw [(by push_cast; ring : ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ)), zpow_natCast]
  simp only [XinnerFamily, hz, mul_pow]
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma XouterFamily_eq (j m : ℕ) :
    t.XouterFamily u (j, m) = (m : K) * ((u : K)⁻¹) ^ m * ((t.q : K) ^ m) ^ j := by
  have hz : ((t.q : K) ^ (-(j : ℤ)) * (u : K))⁻¹ = (t.q : K) ^ j * (u : K)⁻¹ := by
    rw [mul_inv, zpow_neg, inv_inv, zpow_natCast]
  simp only [XouterFamily, hz, mul_pow]
  ring

/-- **Inner half-collapse of `X`.** On the inner side `‖q‖·‖u‖ < 1`, the `ℤ`-index sum
`∑_{n ≥ 1} Xterm u n` equals the closed-form one-sided power series
`∑_{m ≥ 1} [m·qᵐ/(1-qᵐ)]·uᵐ` (both summing to the same value `S`). -/
lemma X_inner_collapse (h2 : ‖(t.q : K)‖ * ‖(u : K)‖ < 1) :
    ∃ S : K, HasSum (fun j : ℕ => t.Xterm u ((j : ℤ) + 1)) S ∧
      HasSum (fun m : ℕ =>
        (m : K) * (u : K) ^ m * (t.q : K) ^ m * (1 - (t.q : K) ^ m)⁻¹) S := by
  have hdom : Summable (fun p : ℕ × ℕ =>
      ‖(t.q : K)‖ ^ p.1 * (‖(t.q : K)‖ * ‖(u : K)‖) ^ p.2) :=
    Summable.mul_of_nonneg
      (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one)
      (summable_geometric_of_lt_one (by positivity) h2)
      (fun _ => by positivity) (fun _ => by positivity)
  have hsum : Summable (t.XinnerFamily u) := by
    refine hdom.of_norm_bounded ?_
    intro p
    obtain ⟨j, m⟩ := p
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [t.XinnerFamily_eq u, Nat.cast_zero, zero_mul, norm_zero]
      positivity
    · have hexp : j + m ≤ m * (j + 1) := by
        have h : j ≤ m * j := Nat.le_mul_of_pos_left j hm
        calc j + m ≤ m * j + m := by omega
          _ = m * (j + 1) := by ring
      rw [t.XinnerFamily_eq u, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
      calc ‖(m : K)‖ * ‖(u : K)‖ ^ m * (‖(t.q : K)‖ ^ m) ^ (j + 1)
          ≤ 1 * ‖(u : K)‖ ^ m * (‖(t.q : K)‖ ^ m) ^ (j + 1) := by
            gcongr
            exact IsUltrametricDist.norm_natCast_le_one K m
        _ = ‖(u : K)‖ ^ m * ‖(t.q : K)‖ ^ (m * (j + 1)) := by rw [one_mul, ← pow_mul]
        _ ≤ ‖(u : K)‖ ^ m * ‖(t.q : K)‖ ^ (j + m) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le hexp
        _ = ‖(t.q : K)‖ ^ j * (‖(t.q : K)‖ * ‖(u : K)‖) ^ m := by rw [mul_pow, pow_add]; ring
  have hfibj : ∀ j : ℕ,
      HasSum (fun m : ℕ => t.XinnerFamily u (j, m)) (t.Xterm u ((j : ℤ) + 1)) := by
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
    simpa only [XinnerFamily] using t.Xterm_hasSum_of_norm_lt_one u ((j : ℤ) + 1) hnorm
  have hfibm : ∀ m : ℕ, HasSum (fun j : ℕ => t.XinnerFamily u (j, m))
      ((m : K) * (u : K) ^ m * (t.q : K) ^ m * (1 - (t.q : K) ^ m)⁻¹) := by
    intro m
    simp only [t.XinnerFamily_eq u]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have hx : ‖(t.q : K) ^ m‖ < 1 := by
        rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) t.norm_lt_one hm.ne'
      have hgeom := (hasSum_geom_succ hx).mul_left ((m : K) * (u : K) ^ m)
      have hval : (m : K) * (u : K) ^ m * (t.q : K) ^ m * (1 - (t.q : K) ^ m)⁻¹
          = (m : K) * (u : K) ^ m * ((t.q : K) ^ m * (1 - (t.q : K) ^ m)⁻¹) := by ring
      rw [hval]
      exact hgeom
  refine ⟨∑' p : ℕ × ℕ, t.XinnerFamily u p, hsum.hasSum.prod_fiberwise hfibj, ?_⟩
  exact ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum).prod_fiberwise hfibm

/-- **Outer half-collapse of `X`.** On the outer side `1 < ‖u‖`, the `ℤ`-index sum
`∑_{n ≤ 0} Xterm u n` equals the closed-form one-sided power series in `u⁻¹`,
`∑_{m ≥ 1} [m/(1-qᵐ)]·u⁻ᵐ` (both summing to the same value `S`). -/
lemma X_outer_collapse (h1 : 1 < ‖(u : K)‖) :
    ∃ S : K, HasSum (fun j : ℕ => t.Xterm u (-(j : ℤ))) S ∧
      HasSum (fun m : ℕ =>
        (m : K) * ((u : K)⁻¹) ^ m * (1 - (t.q : K) ^ m)⁻¹) S := by
  have hdom : Summable (fun p : ℕ × ℕ =>
      ‖(t.q : K)‖ ^ p.1 * (‖(u : K)‖⁻¹) ^ p.2) :=
    Summable.mul_of_nonneg
      (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one)
      (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ h1))
      (fun _ => by positivity) (fun _ => by positivity)
  have hsum : Summable (t.XouterFamily u) := by
    refine hdom.of_norm_bounded ?_
    intro p
    obtain ⟨j, m⟩ := p
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [t.XouterFamily_eq u, Nat.cast_zero, zero_mul, norm_zero]
      positivity
    · have hexp : j ≤ m * j := Nat.le_mul_of_pos_left j hm
      rw [t.XouterFamily_eq u, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_inv]
      calc ‖(m : K)‖ * (‖(u : K)‖⁻¹) ^ m * (‖(t.q : K)‖ ^ m) ^ j
          ≤ 1 * (‖(u : K)‖⁻¹) ^ m * (‖(t.q : K)‖ ^ m) ^ j := by
            gcongr
            exact IsUltrametricDist.norm_natCast_le_one K m
        _ = (‖(u : K)‖⁻¹) ^ m * ‖(t.q : K)‖ ^ (m * j) := by rw [one_mul, ← pow_mul]
        _ ≤ (‖(u : K)‖⁻¹) ^ m * ‖(t.q : K)‖ ^ j := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le hexp
        _ = ‖(t.q : K)‖ ^ j * (‖(u : K)‖⁻¹) ^ m := by ring
  have hfibj : ∀ j : ℕ,
      HasSum (fun m : ℕ => t.XouterFamily u (j, m)) (t.Xterm u (-(j : ℤ))) := by
    intro j
    have hnorm : 1 < ‖(t.q : K) ^ (-(j : ℤ)) * (u : K)‖ := by
      rw [norm_mul, norm_zpow, zpow_neg, zpow_natCast]
      have hp : (0 : ℝ) < ‖(t.q : K)‖ ^ j := pow_pos t.norm_q_pos j
      have hle : ‖(t.q : K)‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le
      calc (1 : ℝ) < ‖(u : K)‖ := h1
        _ ≤ (‖(t.q : K)‖ ^ j)⁻¹ * ‖(u : K)‖ :=
            le_mul_of_one_le_left (norm_nonneg _) (one_le_inv_iff₀.mpr ⟨hp, hle⟩)
    simpa only [XouterFamily] using t.Xterm_hasSum_of_one_lt_norm u (-(j : ℤ)) hnorm
  have hfibm : ∀ m : ℕ, HasSum (fun j : ℕ => t.XouterFamily u (j, m))
      ((m : K) * ((u : K)⁻¹) ^ m * (1 - (t.q : K) ^ m)⁻¹) := by
    intro m
    simp only [t.XouterFamily_eq u]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have hx : ‖(t.q : K) ^ m‖ < 1 := by
        rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) t.norm_lt_one hm.ne'
      exact (hasSum_geometric_of_norm_lt_one hx).mul_left ((m : K) * (u : K)⁻¹ ^ m)
  refine ⟨∑' p : ℕ × ℕ, t.XouterFamily u p, hsum.hasSum.prod_fiberwise hfibj, ?_⟩
  exact ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum).prod_fiberwise hfibm

/-- **The Tate coordinate `X` as a two-sided Laurent series on the fundamental annulus.** For
`1 < ‖u‖` and `‖q‖·‖u‖ < 1` (equivalently `1 < ‖u‖ < ‖q‖⁻¹`),
`X(u) = ∑' m : ℤ, XLaurentCoeff m · uᵐ`, a convergent two-sided Laurent series with Eisenstein-type
coefficients. This is step 2 of the pole-cancellation Laurent development of the Weierstrass
defect (#146). -/
theorem X_hasSum_laurent (h1 : 1 < ‖(u : K)‖) (h2 : ‖(t.q : K)‖ * ‖(u : K)‖ < 1) :
    HasSum (fun m : ℤ => t.XLaurentCoeff m * (u : K) ^ m) (t.X u) := by
  obtain ⟨Sin, hXin, hGin⟩ := t.X_inner_collapse u h2
  obtain ⟨Sout, hXout, hGout⟩ := t.X_outer_collapse u h1
  -- Split the `ℤ`-index sum of `Xterm` into `n ≥ 1` and `n ≤ 0`, identifying `∑' n, Xterm` with
  -- `Sin + Sout`.
  have hXpos : HasSum (fun n : ℤ => if 0 < n then t.Xterm u n else 0) Sin := by
    have hinj : Function.Injective (fun k : ℕ => (k : ℤ) + 1) := by
      intro a b h; simpa using h
    apply (hinj.hasSum_iff ?_).mp
    · have hcomp : (fun n : ℤ => if 0 < n then t.Xterm u n else 0) ∘ (fun k : ℕ => (k : ℤ) + 1)
          = fun k : ℕ => t.Xterm u ((k : ℤ) + 1) := by
        funext k
        simp only [Function.comp_apply]
        rw [if_pos (by positivity)]
      rw [hcomp]; exact hXin
    · intro n hn
      rw [Set.mem_range] at hn
      have hn0 : ¬ (0 < n) := fun hpos => hn ⟨(n - 1).toNat, by omega⟩
      rw [if_neg hn0]
  have hXnp : HasSum (fun n : ℤ => if n ≤ 0 then t.Xterm u n else 0) Sout := by
    have hinj : Function.Injective (fun k : ℕ => -(k : ℤ)) := by
      intro a b h; simpa using h
    apply (hinj.hasSum_iff ?_).mp
    · have hcomp : (fun n : ℤ => if n ≤ 0 then t.Xterm u n else 0) ∘ (fun k : ℕ => -(k : ℤ))
          = fun k : ℕ => t.Xterm u (-(k : ℤ)) := by
        funext k
        simp only [Function.comp_apply]
        rw [if_pos (by omega)]
      rw [hcomp]; exact hXout
    · intro n hn
      rw [Set.mem_range] at hn
      have hn0 : ¬ (n ≤ 0) := fun hnp => hn ⟨(-n).toNat, by omega⟩
      rw [if_neg hn0]
  have hXsum : HasSum
      (fun n : ℤ => (if 0 < n then t.Xterm u n else 0) + (if n ≤ 0 then t.Xterm u n else 0))
      (Sin + Sout) := hXpos.add hXnp
  have hpart : (fun n : ℤ =>
      (if 0 < n then t.Xterm u n else 0) + (if n ≤ 0 then t.Xterm u n else 0)) = t.Xterm u := by
    funext n
    by_cases h : 0 < n
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  rw [hpart] at hXsum
  have htsum : ∑' n : ℤ, t.Xterm u n = Sin + Sout := hXsum.tsum_eq
  -- Assemble the Laurent series from the positive, negative, and constant pieces.
  have hGpos : HasSum (fun m : ℤ => if 0 < m then t.XLaurentCoeff m * (u : K) ^ m else 0) Sin := by
    apply ((Nat.cast_injective (R := ℤ)).hasSum_iff ?_).mp
    · have hcomp :
          (fun m : ℤ => if 0 < m then t.XLaurentCoeff m * (u : K) ^ m else 0) ∘ (Nat.cast : ℕ → ℤ)
          = fun k : ℕ => (k : K) * (u : K) ^ k * (t.q : K) ^ k * (1 - (t.q : K) ^ k)⁻¹ := by
        funext k
        simp only [Function.comp_apply]
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp
        · rw [if_pos (by exact_mod_cast hk : (0 : ℤ) < (k : ℤ)),
            t.XLaurentCoeff_of_pos (by exact_mod_cast hk : (0 : ℤ) < (k : ℤ)),
            Int.toNat_natCast, zpow_natCast, div_eq_mul_inv]
          ring
      rw [hcomp]; exact hGin
    · intro m hm
      rw [Set.mem_range] at hm
      have hm0 : ¬ (0 < m) := fun hpos => hm ⟨m.toNat, by omega⟩
      rw [if_neg hm0]
  have hGout' : HasSum
      (fun k : ℕ => ((k + 1 : ℕ) : K) * ((u : K)⁻¹) ^ (k + 1) * (1 - (t.q : K) ^ (k + 1))⁻¹)
      Sout := by
    have h := (hasSum_nat_add_iff'
      (f := fun m : ℕ => (m : K) * ((u : K)⁻¹) ^ m * (1 - (t.q : K) ^ m)⁻¹) 1).mpr hGout
    simpa using h
  have hGneg : HasSum (fun m : ℤ => if m < 0 then t.XLaurentCoeff m * (u : K) ^ m else 0) Sout := by
    have hinj : Function.Injective (fun k : ℕ => -((k : ℤ) + 1)) := by
      intro a b h; simpa using h
    apply (hinj.hasSum_iff ?_).mp
    · have hcomp :
          (fun m : ℤ => if m < 0 then t.XLaurentCoeff m * (u : K) ^ m else 0)
            ∘ (fun k : ℕ => -((k : ℤ) + 1))
          = fun k : ℕ => ((k + 1 : ℕ) : K) * ((u : K)⁻¹) ^ (k + 1)
              * (1 - (t.q : K) ^ (k + 1))⁻¹ := by
        funext k
        simp only [Function.comp_apply]
        rw [if_pos (by omega : -((k : ℤ) + 1) < 0),
          t.XLaurentCoeff_of_neg (by omega : -((k : ℤ) + 1) < 0)]
        rw [(by omega : (-(-((k : ℤ) + 1))).toNat = k + 1),
          (by push_cast; ring : -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ)), zpow_neg, zpow_natCast,
          ← inv_pow, div_eq_mul_inv]
        ring
      rw [hcomp]; exact hGout'
    · intro m hm
      rw [Set.mem_range] at hm
      have hm0 : ¬ (m < 0) := fun hneg => hm ⟨(-m - 1).toNat, by omega⟩
      rw [if_neg hm0]
  have hGzero : HasSum (fun m : ℤ => if m = 0 then t.XLaurentCoeff m * (u : K) ^ m else 0)
      (-2 * t.eisenstein 1) := by
    have hfun : (fun m : ℤ => if m = 0 then t.XLaurentCoeff (0 : ℤ) * (u : K) ^ (0 : ℤ) else 0)
        = fun m : ℤ => if m = 0 then t.XLaurentCoeff m * (u : K) ^ m else 0 := by
      funext m
      by_cases hm : m = 0
      · subst hm; rfl
      · rw [if_neg hm, if_neg hm]
    have h0 : t.XLaurentCoeff (0 : ℤ) * (u : K) ^ (0 : ℤ) = -2 * t.eisenstein 1 := by
      rw [t.XLaurentCoeff_zero, zpow_zero, mul_one]
    have hbase := hasSum_ite_eq (0 : ℤ) (t.XLaurentCoeff (0 : ℤ) * (u : K) ^ (0 : ℤ))
    rw [hfun, h0] at hbase
    exact hbase
  have hG := (hGpos.add hGneg).add hGzero
  have hGfun : (fun m : ℤ =>
        ((if 0 < m then t.XLaurentCoeff m * (u : K) ^ m else 0)
          + (if m < 0 then t.XLaurentCoeff m * (u : K) ^ m else 0))
          + (if m = 0 then t.XLaurentCoeff m * (u : K) ^ m else 0))
      = fun m : ℤ => t.XLaurentCoeff m * (u : K) ^ m := by
    funext m
    rcases lt_trichotomy m 0 with h | h | h
    · rw [if_neg (by omega), if_pos h, if_neg (by omega)]; ring
    · subst h; simp
    · rw [if_pos h, if_neg (by omega), if_neg (by omega)]; ring
  rw [hGfun] at hG
  have hval : Sin + Sout + (-2 * t.eisenstein 1) = t.X u := by
    rw [X_apply, htsum]; ring
  rwa [hval] at hG

end TateParameter

end TateCurvesTheta
