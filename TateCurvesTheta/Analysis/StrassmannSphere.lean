/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import TateCurvesTheta.Analysis.MaxTerm
import TateCurvesTheta.Analysis.UltrametricSum
import TateCurvesTheta.Analysis.Strassmann

/-!
# Strassmann's theorem on the unit sphere (two-sided Laurent series)

Over a complete nonarchimedean field `K`, a nonzero convergent **two-sided** Laurent series
`v ↦ ∑' n : ℤ, cₙ vⁿ` — meaning the coefficient family `c : ℤ → K` is summable (equivalently
`‖cₙ‖ → 0` as `|n| → ∞`), so the series converges for every `v` on the unit sphere `‖v‖ = 1` —
which is not identically zero has only **finitely many zeros** on the unit sphere. This is the
two-sided (annulus) analogue of ball-Strassmann (`Analysis/Strassmann.lean`), and it is the
genuine analytic core discharging `LaurentUnitSphereZerosFinite` (`Theta/LaurentSphereReduce.lean`,
#136), hence — via the radius normalization (#27) and `laurentCoeffUnique_of_sphereZerosFinite`
(#23) — the unconditional nonarchimedean Laurent coefficient-uniqueness principle.

## Proof outline

The argument is a **two-sided Weierstrass-division induction on the width** of the maximal-term
index set. Let `M = maxₙ ‖cₙ‖`, attained on the finite nonempty set `S = {n | ‖cₙ‖ = M}` (since
`‖cₙ‖ → 0` both ways), and let `lo = min S`, `hi = max S`, `W = hi − lo` the width.

* **Base `W = 0`** (a single maximal index `lo`): on the sphere `‖cₙ vⁿ‖ = ‖cₙ‖`, so `lo`
  strictly dominates and the ultrametric dominant-term principle
  `IsUltrametricDist.norm_tsum_eq_of_dominant` gives `‖∑ cₙ vⁿ‖ = M ≠ 0`: no zeros.

* **Step `W = k + 1`**: if there is no zero the set is empty; otherwise pick a zero `α`
  (`‖α‖ = 1`, `∑ cₙ αⁿ = 0`) and perform Weierstrass division `∑ cₙ vⁿ = (v − α) · ∑ gₙ vⁿ`,
  where `gₙ = ∑' j, c_{n+1+j} αʲ` is the (forward) Weierstrass quotient. Unlike the one-sided
  case, controlling `g` at `−∞` requires the **root** relation: the forward quotient equals the
  backward quotient (both equal `α^{−(n+1)}` times a one-sided tail of `∑ cₘ αᵐ = 0`), which
  gives `‖gₙ‖ ≤ sup_{m ≤ n} ‖cₘ‖`. Combined with the elementary forward bound
  `‖gₙ‖ ≤ sup_{m > n} ‖cₘ‖`, this shows `g` is summable and that its maximal-term index set is
  `[lo, hi − 1]`, i.e. width `k`. The induction hypothesis bounds `g`'s zeros, and the division
  identity gives `zeros(c) ⊆ {α} ∪ zeros(g)`.

## Main results

* `TateCurvesTheta.StrassmannSphere.finite_zeros` : a nonzero summable coefficient family `c`
  has finitely many zeros of `v ↦ ∑' n, cₙ vⁿ` on the unit sphere `{v : K | ‖v‖ = 1}`.

## References

* A. Robert, *A Course in p-adic Analysis*, §6.1–6.2 (the maximum term; Strassmann's theorem;
  finiteness of zeros on a sphere / annulus).
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, §IV (Newton polygons).
* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
-/

open Filter Topology

namespace TateCurvesTheta.StrassmannSphere

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### Convergence on the unit sphere -/

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The `atTop` (`n → +∞`) part of coefficient decay coming from summability. -/
theorem tendsto_atTop_norm {c : ℤ → K} (hc : Summable c) :
    Tendsto (fun n => ‖c n‖) atTop (𝓝 0) := by
  have h : Tendsto (fun n => ‖c n‖) cofinite (𝓝 0) := by
    simpa using hc.tendsto_cofinite_zero.norm
  exact h.mono_left (by rw [Int.cofinite_eq]; exact le_sup_right)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The `atBot` (`n → -∞`) part of coefficient decay coming from summability. -/
theorem tendsto_atBot_norm {c : ℤ → K} (hc : Summable c) :
    Tendsto (fun n => ‖c n‖) atBot (𝓝 0) := by
  have h : Tendsto (fun n => ‖c n‖) cofinite (𝓝 0) := by
    simpa using hc.tendsto_cofinite_zero.norm
  exact h.mono_left (by rw [Int.cofinite_eq]; exact le_sup_left)

/-- On the unit sphere `‖v‖ = 1` the Laurent series `∑' n, cₙ vⁿ` converges. -/
theorem summable_mul_zpow {c : ℤ → K} (hc : Summable c) {v : K} (hv : ‖v‖ = 1) :
    Summable fun n : ℤ => c n * v ^ n := by
  refine Strassmann.summable_of_norm_le hc fun n => ?_
  rw [norm_mul, norm_zpow, hv, one_zpow, mul_one]

/-! ### The Weierstrass quotient -/

/-- Coefficients of the (forward) Weierstrass quotient `∑ cₙ vⁿ / (v − α)`:
`g n = ∑' j, c (n + 1 + j) · αʲ`. -/
noncomputable def wCoeff (c : ℤ → K) (α : K) (n : ℤ) : K :=
  ∑' j : ℕ, c (n + 1 + j) * α ^ j

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem wCoeff_apply (c : ℤ → K) (α : K) (n : ℤ) :
    wCoeff c α n = ∑' j : ℕ, c (n + 1 + j) * α ^ j := rfl

omit [IsUltrametricDist K] in
/-- The shifted coefficient family `j ↦ c (n + 1 + j)` is summable. -/
theorem summable_shift {c : ℤ → K} (hc : Summable c) (n : ℤ) :
    Summable fun j : ℕ => c (n + 1 + j) :=
  hc.comp_injective fun j₁ j₂ h => by exact_mod_cast add_left_cancel h

/-- Each defining series of `wCoeff` converges (for `‖α‖ ≤ 1`). -/
theorem wCoeff_summable_family {c : ℤ → K} (hc : Summable c) {α : K} (hα : ‖α‖ ≤ 1) (n : ℤ) :
    Summable fun j : ℕ => c (n + 1 + j) * α ^ j := by
  refine Strassmann.summable_of_norm_le (summable_shift hc n) fun j => ?_
  rw [norm_mul, norm_pow]
  calc ‖c (n + 1 + j)‖ * ‖α‖ ^ j ≤ ‖c (n + 1 + j)‖ * 1 ^ j := by gcongr
    _ = ‖c (n + 1 + j)‖ := by rw [one_pow, mul_one]

/-- The synthetic-division recursion `c (n+1) = g n − α · g (n+1)`. -/
theorem wCoeff_rec {c : ℤ → K} (hc : Summable c) {α : K} (hα : ‖α‖ ≤ 1) (n : ℤ) :
    c (n + 1) = wCoeff c α n - α * wCoeff c α (n + 1) := by
  have h1 : wCoeff c α n = c (n + 1) + α * wCoeff c α (n + 1) := by
    rw [wCoeff_apply, (wCoeff_summable_family hc hα n).tsum_eq_zero_add, wCoeff_apply,
      ← tsum_mul_left]
    congr 1
    · simp
    · refine tsum_congr fun j => ?_
      have hidx : n + 1 + ((j : ℤ) + 1) = n + 1 + 1 + (j : ℤ) := by ring
      push_cast
      rw [hidx, pow_succ]; ring
  rw [h1]; ring

/-- The recursion in the form `c n + α · g n = g (n − 1)`. -/
theorem wCoeff_rec' {c : ℤ → K} (hc : Summable c) {α : K} (hα : ‖α‖ ≤ 1) (n : ℤ) :
    c n + α * wCoeff c α n = wCoeff c α (n - 1) := by
  have h := wCoeff_rec hc hα (n - 1)
  have hn : n - 1 + 1 = n := by ring
  rw [hn] at h
  rw [h]; ring

/-! #### Forward and backward norm bounds -/

omit [CompleteSpace K] in
/-- **Forward bound.** `‖g n‖` is controlled by the coefficients strictly beyond `n`. -/
theorem wCoeff_norm_le_above {c : ℤ → K} {α : K} (hα : ‖α‖ ≤ 1) (n : ℤ)
    {b : ℝ} (hb : 0 ≤ b) (hbd : ∀ m, n < m → ‖c m‖ ≤ b) : ‖wCoeff c α n‖ ≤ b := by
  rw [wCoeff_apply]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hb fun j => ?_
  rw [norm_mul, norm_pow]
  calc ‖c (n + 1 + j)‖ * ‖α‖ ^ j ≤ ‖c (n + 1 + j)‖ * 1 ^ j := by gcongr
    _ = ‖c (n + 1 + j)‖ := by rw [one_pow, mul_one]
    _ ≤ b := hbd _ (by have := Int.natCast_nonneg j; omega)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- `α^{n+1} · g n` is the upper tail `∑_{m > n} cₘ αᵐ` of the series (as a `ℤ`-indexed sum of the
`Ioi n`-indicator). -/
private theorem alpha_wCoeff_eq_upper {c : ℤ → K} {α : K} (hα0 : α ≠ 0) (n : ℤ) :
    α ^ (n + 1) * wCoeff c α n
      = ∑' m : ℤ, (Set.Ioi n).indicator (fun m => c m * α ^ m) m := by
  rw [wCoeff_apply, ← tsum_mul_left]
  have hinj : Function.Injective (fun j : ℕ => n + 1 + (j : ℤ)) :=
    fun a b h => by exact_mod_cast add_left_cancel h
  have hf : Function.support (fun m => (Set.Ioi n).indicator (fun m => c m * α ^ m) m)
      ⊆ Set.range (fun j : ℕ => n + 1 + (j : ℤ)) := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hxr
    have hxni : x ∉ Set.Ioi n := by
      intro hmem
      simp only [Set.mem_Ioi] at hmem
      exact hxr ⟨(x - n - 1).toNat, by change n + 1 + ((x - n - 1).toNat : ℤ) = x; omega⟩
    exact hx (Set.indicator_of_notMem hxni _)
  rw [← hinj.tsum_eq hf]
  refine tsum_congr fun j => ?_
  rw [Set.indicator_of_mem (by simp only [Set.mem_Ioi]; omega), ← zpow_natCast α j]
  simp only [zpow_add₀ hα0, zpow_one]
  ring

/-- **Backward bound (uses the root relation).** At a root `α` of the series, `‖g n‖` is
controlled by the coefficients up to and including `n`. -/
theorem wCoeff_norm_le_below {c : ℤ → K} (hc : Summable c) {α : K} (hα1 : ‖α‖ = 1)
    (hroot : (∑' n : ℤ, c n * α ^ n) = 0) (n : ℤ)
    {b : ℝ} (hb : 0 ≤ b) (hbd : ∀ m, m ≤ n → ‖c m‖ ≤ b) : ‖wCoeff c α n‖ ≤ b := by
  have hα0 : α ≠ 0 := by rw [← norm_pos_iff, hα1]; norm_num
  have hF : Summable fun m : ℤ => c m * α ^ m := summable_mul_zpow hc hα1
  have hUp : Summable fun m : ℤ => (Set.Ioi n).indicator (fun m => c m * α ^ m) m :=
    Strassmann.summable_of_norm_le hF fun m => by
      rw [Set.indicator_apply]; split_ifs
      · exact le_refl _
      · rw [norm_zero]; exact norm_nonneg _
  have hLo : Summable fun m : ℤ => (Set.Iic n).indicator (fun m => c m * α ^ m) m :=
    Strassmann.summable_of_norm_le hF fun m => by
      rw [Set.indicator_apply]; split_ifs
      · exact le_refl _
      · rw [norm_zero]; exact norm_nonneg _
  have hsplit : (fun m : ℤ => c m * α ^ m)
      = (fun m => (Set.Ioi n).indicator (fun m => c m * α ^ m) m
          + (Set.Iic n).indicator (fun m => c m * α ^ m) m) := by
    funext m
    by_cases hm : n < m
    · rw [Set.indicator_of_mem (by simpa using hm),
        Set.indicator_of_notMem (by simp only [Set.mem_Iic, not_le]; exact hm), add_zero]
    · rw [Set.indicator_of_notMem (by simpa using hm),
        Set.indicator_of_mem (by simp only [Set.mem_Iic]; omega), zero_add]
  have hsum0 : (∑' m : ℤ, (Set.Ioi n).indicator (fun m => c m * α ^ m) m)
      + (∑' m : ℤ, (Set.Iic n).indicator (fun m => c m * α ^ m) m) = 0 := by
    rw [← hUp.tsum_add hLo, ← hsplit]; exact hroot
  have hUeq : α ^ (n + 1) * wCoeff c α n
      = -(∑' m : ℤ, (Set.Iic n).indicator (fun m => c m * α ^ m) m) := by
    rw [alpha_wCoeff_eq_upper hα0]; exact eq_neg_of_add_eq_zero_left hsum0
  have hα1' : ‖α ^ (n + 1)‖ = 1 := by rw [norm_zpow, hα1, one_zpow]
  have hnorm : ‖wCoeff c α n‖
      = ‖∑' m : ℤ, (Set.Iic n).indicator (fun m => c m * α ^ m) m‖ := by
    calc ‖wCoeff c α n‖ = ‖α ^ (n + 1) * wCoeff c α n‖ := by rw [norm_mul, hα1', one_mul]
      _ = ‖∑' m : ℤ, (Set.Iic n).indicator (fun m => c m * α ^ m) m‖ := by rw [hUeq, norm_neg]
  rw [hnorm]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hb fun m => ?_
  by_cases hm : m ≤ n
  · rw [Set.indicator_of_mem (by simpa using hm), norm_mul, norm_zpow, hα1, one_zpow, mul_one]
    exact hbd m hm
  · rw [Set.indicator_of_notMem (by simp only [Set.mem_Iic]; omega), norm_zero]; exact hb

/-- **Summability of the Weierstrass quotient** at a root `α`. -/
theorem wCoeff_summable {c : ℤ → K} (hc : Summable c) {α : K} (hα1 : ‖α‖ = 1)
    (hroot : (∑' n : ℤ, c n * α ^ n) = 0) : Summable (wCoeff c α) := by
  have hα : ‖α‖ ≤ 1 := le_of_eq hα1
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Int.cofinite_eq, tendsto_sup]
  refine ⟨?_, ?_⟩
  · -- `n → -∞`
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨P, hP⟩ := eventually_atBot.mp ((tendsto_atBot_norm hc).eventually
      (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))
    filter_upwards [eventually_le_atBot P] with n hn
    calc ‖wCoeff c α n‖
        ≤ ε / 2 := wCoeff_norm_le_below hc hα1 hroot n (by positivity)
          fun m hm => (Set.mem_Iio.mp (hP m (by omega))).le
      _ < ε := by linarith
  · -- `n → +∞`
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨P, hP⟩ := eventually_atTop.mp ((tendsto_atTop_norm hc).eventually
      (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))
    filter_upwards [eventually_ge_atTop P] with n hn
    calc ‖wCoeff c α n‖
        ≤ ε / 2 := wCoeff_norm_le_above hα n (by positivity)
          fun m hm => (Set.mem_Iio.mp (hP m (by omega))).le
      _ < ε := by linarith

/-! ### The division identity -/

/-- **The Weierstrass division identity on the sphere.** If `α` is a root (`‖α‖ = 1`,
`∑ cₙ αⁿ = 0`), then `∑ cₙ vⁿ = (v − α) · ∑ gₙ vⁿ` on the unit sphere `‖v‖ = 1`. -/
theorem tsum_wCoeff_div {c : ℤ → K} (hc : Summable c) {α : K} (hα1 : ‖α‖ = 1)
    (hroot : (∑' n : ℤ, c n * α ^ n) = 0) {v : K} (hv : ‖v‖ = 1) :
    (∑' n : ℤ, c n * v ^ n) = (v - α) * ∑' n : ℤ, wCoeff c α n * v ^ n := by
  have hα : ‖α‖ ≤ 1 := le_of_eq hα1
  have hv0 : v ≠ 0 := by rw [← norm_pos_iff, hv]; norm_num
  have hg := wCoeff_summable hc hα1 hroot
  have hFsum := summable_mul_zpow hc hv
  have hGsum := summable_mul_zpow hg hv
  have e1 : (∑' n : ℤ, (c n + α * wCoeff c α n) * v ^ n)
      = (∑' n : ℤ, c n * v ^ n) + α * ∑' n : ℤ, wCoeff c α n * v ^ n := by
    rw [← tsum_mul_left, ← hFsum.tsum_add (hGsum.mul_left α)]
    exact tsum_congr fun n => by ring
  have e2 : (∑' n : ℤ, (c n + α * wCoeff c α n) * v ^ n)
      = ∑' n : ℤ, wCoeff c α (n - 1) * v ^ n :=
    tsum_congr fun n => by rw [wCoeff_rec' hc hα n]
  have e3 : (∑' n : ℤ, wCoeff c α (n - 1) * v ^ n)
      = v * ∑' n : ℤ, wCoeff c α n * v ^ n := by
    rw [← tsum_mul_left, ← (Equiv.addRight (1 : ℤ)).tsum_eq (fun n => wCoeff c α (n - 1) * v ^ n)]
    refine tsum_congr fun n => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [zpow_add₀ hv0, zpow_one]; ring
  have key : (∑' n : ℤ, c n * v ^ n) + α * ∑' n : ℤ, wCoeff c α n * v ^ n
      = v * ∑' n : ℤ, wCoeff c α n * v ^ n := by rw [← e1, e2, e3]
  rw [sub_mul, eq_sub_iff_add_eq]; exact key

/-! ### Finiteness of the zero set -/

/-- **Uniform strict bound off the maximal-index window.** If `lo`, `hi` bound the maximal-term
window and the coefficients are strictly smaller than `M = ‖c lo‖` outside `[lo, hi]`, there is a
single `C < M` bounding all of them there. -/
theorem exists_bound_window {c : ℤ → K} (hc : Summable c) {lo hi : ℤ} (hlo : c lo ≠ 0)
    (hbelow : ∀ n, n < lo → ‖c n‖ < ‖c lo‖) (habove : ∀ n, hi < n → ‖c n‖ < ‖c lo‖) :
    ∃ C, 0 ≤ C ∧ C < ‖c lo‖ ∧ (∀ m, m < lo → ‖c m‖ ≤ C) ∧ (∀ m, hi < m → ‖c m‖ ≤ C) := by
  classical
  have hMpos : 0 < ‖c lo‖ := norm_pos_iff.mpr hlo
  set d : ℤ → K := fun m => if m < lo ∨ hi < m then c m else 0 with hd
  have hdsum : Summable d :=
    Strassmann.summable_of_norm_le hc fun m => by
      rw [hd]; dsimp only; split_ifs <;> simp [norm_nonneg]
  have hdle : ∀ m, m < lo ∨ hi < m → ‖c m‖ < ‖c lo‖ := by
    rintro m (h | h)
    · exact hbelow m h
    · exact habove m h
  by_cases hz : ∀ m, d m = 0
  · refine ⟨0, le_refl 0, hMpos, ?_, ?_⟩
    · intro m hm
      have := hz m; rw [hd] at this; simp only [if_pos (Or.inl hm)] at this
      rw [this, norm_zero]
    · intro m hm
      have := hz m; rw [hd] at this; simp only [if_pos (Or.inr hm)] at this
      rw [this, norm_zero]
  · rw [not_forall] at hz
    obtain ⟨m₁, hm₁⟩ := hz
    obtain ⟨m₀, hm₀, hm₀max⟩ := hdsum.exists_max_norm hm₁
    have hm₀region : m₀ < lo ∨ hi < m₀ := by
      by_contra h
      rw [hd] at hm₀; simp only [if_neg h] at hm₀; exact hm₀ rfl
    have hcm₀ : d m₀ = c m₀ := by rw [hd]; simp only [if_pos hm₀region]
    have hClt : ‖c m₀‖ < ‖c lo‖ := hdle m₀ hm₀region
    refine ⟨‖d m₀‖, norm_nonneg _, by rw [hcm₀]; exact hClt, ?_, ?_⟩
    · intro m hm
      have hdm : d m = c m := by rw [hd]; simp only [if_pos (Or.inl hm)]
      rw [← hdm]; exact hm₀max m
    · intro m hm
      have hdm : d m = c m := by rw [hd]; simp only [if_pos (Or.inr hm)]
      rw [← hdm]; exact hm₀max m

/-- **Two-sided Strassmann, width-indexed form.** With `lo`, `hi` the smallest and largest indices
attaining the maximal coefficient norm `‖c lo‖`, and `hi = lo + W`, the series `∑ cₙ vⁿ` has
finitely many zeros on the unit sphere. Proved by strong induction on `W`. -/
theorem finite_zeros_isWidth (W : ℕ) : ∀ (c : ℤ → K), Summable c → ∀ (lo hi : ℤ),
    c lo ≠ 0 → (∀ n, ‖c n‖ ≤ ‖c lo‖) → ‖c hi‖ = ‖c lo‖ →
    (∀ n, n < lo → ‖c n‖ < ‖c lo‖) → (∀ n, hi < n → ‖c n‖ < ‖c lo‖) →
    hi = lo + W →
    {v : K | ‖v‖ = 1 ∧ (∑' n : ℤ, c n * v ^ n) = 0}.Finite := by
  induction W using Nat.strong_induction_on with
  | _ W ih =>
    intro c hc lo hi hlo hmax hhiM hbelow habove hW
    have hnv : ∀ w : K, ‖w‖ = 1 → ∀ n : ℤ, ‖c n * w ^ n‖ = ‖c n‖ :=
      fun w hw n => by rw [norm_mul, norm_zpow, hw, one_zpow, mul_one]
    by_cases hroot : ∃ α, ‖α‖ = 1 ∧ (∑' n : ℤ, c n * α ^ n) = 0
    · obtain ⟨α, hα1, hαroot⟩ := hroot
      have hα : ‖α‖ ≤ 1 := le_of_eq hα1
      obtain _ | k := W
      · -- `W = 0`: `hi = lo`, so `lo` is the unique maximal index; strict domination ⇒ no zero.
        refine (Set.finite_empty).subset ?_
        rintro v ⟨hv, hzero⟩
        have hv0 : v ≠ 0 := by rw [← norm_pos_iff, hv]; norm_num
        refine absurd hzero (IsUltrametricDist.tsum_ne_zero_of_dominant (summable_mul_zpow hc hv)
          (i₀ := lo) (mul_ne_zero hlo (zpow_ne_zero lo hv0)) (fun n hn => ?_))
        rw [hnv v hv n, hnv v hv lo]
        rcases lt_or_gt_of_ne hn with h | h
        · exact hbelow n h
        · exact habove n (by omega)
      · -- `W = k + 1`: divide out a root and recurse on `g = wCoeff c α` (width `k`).
        obtain ⟨C, hC0, hCM, hCbelow, hCabove⟩ := exists_bound_window hc hlo hbelow habove
        have hgsum : Summable (wCoeff c α) := wCoeff_summable hc hα1 hαroot
        have hgleM : ∀ n, ‖wCoeff c α n‖ ≤ ‖c lo‖ :=
          fun n => wCoeff_norm_le_above hα n (norm_nonneg _) fun m _ => hmax m
        have hgabove : ∀ n, hi ≤ n → ‖wCoeff c α n‖ ≤ C :=
          fun n hn => wCoeff_norm_le_above hα n hC0 fun m hm => hCabove m (by omega)
        have hgbelow : ∀ n, n < lo → ‖wCoeff c α n‖ ≤ C :=
          fun n hn => wCoeff_norm_le_below hc hα1 hαroot n hC0 fun m hm => hCbelow m (by omega)
        -- `‖g (hi-1)‖ = M`, from the recursion at `hi`.
        have hghiM : ‖wCoeff c α (hi - 1)‖ = ‖c lo‖ := by
          have hgS : wCoeff c α (hi - 1) = c hi + α * wCoeff c α hi := (wCoeff_rec' hc hα hi).symm
          have hαgt : ‖α * wCoeff c α hi‖ < ‖c hi‖ := by
            rw [norm_mul, hα1, one_mul, hhiM]
            exact lt_of_le_of_lt (hgabove hi (le_refl _)) hCM
          rw [hgS, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hαgt.ne',
            max_eq_left hαgt.le, hhiM]
        -- `‖g lo‖ = M`, from the recursion at `lo`.
        have hgloM : ‖wCoeff c α lo‖ = ‖c lo‖ := by
          have hrec := wCoeff_rec' hc hα lo
          have hαgt : ‖wCoeff c α (lo - 1)‖ < ‖c lo‖ :=
            lt_of_le_of_lt (hgbelow (lo - 1) (by omega)) hCM
          have hval : α * wCoeff c α lo = wCoeff c α (lo - 1) + (- c lo) := by
            rw [← hrec]; ring
          have : ‖α * wCoeff c α lo‖ = ‖c lo‖ := by
            rw [hval, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
              (by rw [norm_neg]; exact ne_of_lt hαgt), norm_neg, max_eq_right hαgt.le]
          rwa [norm_mul, hα1, one_mul] at this
        have hglo_ne : wCoeff c α lo ≠ 0 := by
          rw [← norm_pos_iff, hgloM]; exact norm_pos_iff.mpr hlo
        have hgmax : ∀ n, ‖wCoeff c α n‖ ≤ ‖wCoeff c α lo‖ := by rw [hgloM]; exact hgleM
        have hgbelow' : ∀ n, n < lo → ‖wCoeff c α n‖ < ‖wCoeff c α lo‖ := by
          intro n hn; rw [hgloM]; exact lt_of_le_of_lt (hgbelow n hn) hCM
        have hgabove' : ∀ n, hi - 1 < n → ‖wCoeff c α n‖ < ‖wCoeff c α lo‖ := by
          intro n hn; rw [hgloM]; exact lt_of_le_of_lt (hgabove n (by omega)) hCM
        have hgW : hi - 1 = lo + k := by omega
        have hgfin := ih k (by omega) (wCoeff c α) hgsum lo (hi - 1) hglo_ne hgmax
          (by rw [hgloM]; exact hghiM) hgbelow' hgabove' hgW
        refine (hgfin.insert α).subset ?_
        rintro v ⟨hv, hzero⟩
        rw [tsum_wCoeff_div hc hα1 hαroot hv] at hzero
        rcases mul_eq_zero.mp hzero with h | h
        · rw [sub_eq_zero] at h
          exact Set.mem_insert_iff.mpr (Or.inl h)
        · exact Set.mem_insert_iff.mpr (Or.inr ⟨hv, h⟩)
    · -- no root on the sphere: the zero set is empty.
      refine (Set.finite_empty).subset ?_
      rintro v ⟨hv, hzero⟩
      exact absurd ⟨v, hv, hzero⟩ hroot

/-- **Strassmann's theorem on the unit sphere.** A nonzero summable coefficient family
`c : ℤ → K` over a complete nonarchimedean field has only finitely many zeros of
`v ↦ ∑' n, cₙ vⁿ` on the unit sphere `{v : K | ‖v‖ = 1}`. -/
theorem finite_zeros {c : ℤ → K} (hc : Summable c) (hc0 : c ≠ 0) :
    {v : K | ‖v‖ = 1 ∧ (∑' n : ℤ, c n * v ^ n) = 0}.Finite := by
  classical
  obtain ⟨i₁, hi₁⟩ : ∃ i, c i ≠ 0 := Function.ne_iff.mp hc0
  obtain ⟨i₀, hi₀, hi₀max⟩ := hc.exists_max_norm hi₁
  have hpos : 0 < ‖c i₀‖ := norm_pos_iff.mpr hi₀
  have htend : Tendsto (fun n => ‖c n‖) cofinite (𝓝 0) := by
    simpa using hc.tendsto_cofinite_zero.norm
  have hfin : {n : ℤ | ‖c i₀‖ ≤ ‖c n‖}.Finite := by
    have hev := Filter.eventually_cofinite.mp (htend.eventually (Iio_mem_nhds hpos))
    exact hev.subset fun n hn => not_lt.mpr (by simpa using hn)
  have hne : hfin.toFinset.Nonempty :=
    ⟨i₀, by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]⟩
  set lo := hfin.toFinset.min' hne with hlodef
  set hi := hfin.toFinset.max' hne with hhidef
  have hloS : ‖c i₀‖ ≤ ‖c lo‖ :=
    (Set.Finite.mem_toFinset hfin).mp (hfin.toFinset.min'_mem hne)
  have hhiS : ‖c i₀‖ ≤ ‖c hi‖ :=
    (Set.Finite.mem_toFinset hfin).mp (hfin.toFinset.max'_mem hne)
  have hloM : ‖c lo‖ = ‖c i₀‖ := le_antisymm (hi₀max lo) hloS
  have hhiM : ‖c hi‖ = ‖c lo‖ := by rw [hloM]; exact le_antisymm (hi₀max hi) hhiS
  have hlo_ne : c lo ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hpos hloS)
  have hmax : ∀ n, ‖c n‖ ≤ ‖c lo‖ := fun n => by rw [hloM]; exact hi₀max n
  have hbelow : ∀ n, n < lo → ‖c n‖ < ‖c lo‖ := by
    intro n hn
    rw [hloM]
    by_contra hcon
    rw [not_lt] at hcon
    have hmem : n ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).mpr hcon
    have : lo ≤ n := hfin.toFinset.min'_le n hmem
    omega
  have habove : ∀ n, hi < n → ‖c n‖ < ‖c lo‖ := by
    intro n hn
    rw [hloM]
    by_contra hcon
    rw [not_lt] at hcon
    have hmem : n ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).mpr hcon
    have : n ≤ hi := hfin.toFinset.le_max' n hmem
    omega
  have hlohi : lo ≤ hi := hfin.toFinset.min'_le hi (hfin.toFinset.max'_mem hne)
  have hW : hi = lo + (hi - lo).toNat := by omega
  exact finite_zeros_isWidth (hi - lo).toNat c hc lo hi hlo_ne hmax hhiM hbelow habove hW

end TateCurvesTheta.StrassmannSphere
