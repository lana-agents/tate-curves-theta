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

/-!
# Strassmann's theorem on the closed unit ball

Over a complete nonarchimedean field `K`, a one-sided power series `f v = ∑' n, fₙ vⁿ` whose
coefficients tend to zero (so the series converges on the closed unit ball `𝒪 = {v | ‖v‖ ≤ 1}`)
and which is not identically zero has only **finitely many zeros** in `𝒪`. This is *Strassmann's
theorem*, the nonarchimedean finiteness-of-zeros fact, and the analytic heart of the
Newton-polygon programme for Laurent coefficient uniqueness (`LaurentSphereZerosFinite`, the
residual seam of `Theta/LaurentSphere.lean`).

Unlike the archimedean identity theorem, which relies on preconnectedness, the nonarchimedean
argument is a genuine Weierstrass-division induction: writing `N` for the largest index attaining
`maxₙ ‖fₙ‖`, one shows by induction on `N` that `f` has at most `N` zeros in `𝒪`. The base case
`N = 0` is the ultrametric maximum-modulus principle (the constant term strictly dominates, so
`f` never vanishes); the inductive step divides out a root `α` (`f v = (v - α) · g v`) and checks
that `g` has largest max-index `N - 1`.

## Main results

* `TateCurvesTheta.Strassmann.finite_zeros` : a nonzero convergent one-sided power series over a
  complete nonarchimedean field has finitely many zeros on the closed unit ball.

## References

* A. Robert, *A Course in p-adic Analysis*, §6.1–6.2 (the maximum term; Strassmann's theorem;
  finiteness of zeros).
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, §IV (Newton polygons).
* J. W. S. Cassels, *Local Fields*, §4 (Weierstrass preparation / Strassmann).
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
-/

open Filter Topology

namespace TateCurvesTheta.Strassmann

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Comparison test for summability over a complete nonarchimedean field: a family dominated
termwise in norm by a summable one is itself summable. -/
theorem summable_of_norm_le {ι : Type*} {f g : ι → K} (hf : Summable f)
    (h : ∀ i, ‖g i‖ ≤ ‖f i‖) : Summable g := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero] at hf ⊢
  refine squeeze_zero_norm (a := fun i => ‖f i‖) (fun i => h i) ?_
  simpa using hf.norm

/-- If the coefficients are summable, the one-sided power series `∑' n, fₙ vⁿ` converges for every
`v` in the closed unit ball `‖v‖ ≤ 1`. -/
theorem summable_mul_pow {f : ℕ → K} (hf : Summable f) {v : K} (hv : ‖v‖ ≤ 1) :
    Summable fun n : ℕ => f n * v ^ n := by
  refine summable_of_norm_le hf fun n => ?_
  rw [norm_mul, norm_pow]
  calc ‖f n‖ * ‖v‖ ^ n ≤ ‖f n‖ * 1 ^ n :=
        by gcongr
    _ = ‖f n‖ := by rw [one_pow, mul_one]

omit [CompleteSpace K] in
/-- **Uniform strict bound on the tail.** If `N` is (an index attaining) the maximum term and the
coefficients strictly beyond `N` are all strictly smaller than `‖f N‖`, then there is a single
constant `C < ‖f N‖` bounding *all* of them. This packages the finiteness of the superlevel set
into a usable strict bound. -/
theorem exists_bound_lt {f : ℕ → K} (hf : Summable f) {N : ℕ} (hfN : f N ≠ 0)
    (hlast : ∀ n, N < n → ‖f n‖ < ‖f N‖) :
    ∃ C, 0 ≤ C ∧ C < ‖f N‖ ∧ ∀ m, N < m → ‖f m‖ ≤ C := by
  have hMpos : 0 < ‖f N‖ := norm_pos_iff.mpr hfN
  have hsfs : Summable fun j : ℕ => f (N + 1 + j) :=
    ((summable_nat_add_iff (N + 1)).mpr hf).congr fun j => by rw [Nat.add_comm]
  -- turn `m > N` into the shifted index `j = m - (N+1)`
  have key : ∀ (C : ℝ), (∀ j : ℕ, ‖f (N + 1 + j)‖ ≤ C) → ∀ m, N < m → ‖f m‖ ≤ C := by
    intro C hC m hm
    have hm' : N + 1 + (m - (N + 1)) = m := by omega
    have := hC (m - (N + 1))
    rwa [hm'] at this
  by_cases hz : ∀ j : ℕ, f (N + 1 + j) = 0
  · exact ⟨0, le_refl 0, hMpos, key 0 fun j => by rw [hz j, norm_zero]⟩
  · rw [not_forall] at hz
    obtain ⟨j₁, hj₁⟩ := hz
    obtain ⟨j₀, _, hj₀⟩ := hsfs.exists_max_norm hj₁
    refine ⟨‖f (N + 1 + j₀)‖, norm_nonneg _, ?_, key _ hj₀⟩
    exact hlast _ (by omega)

/-- **Maximum-modulus principle (Strassmann base case).** If the constant term `f 0` strictly
dominates every higher coefficient in norm, then `f` vanishes nowhere on the closed unit ball:
the sum is congruent to `f 0` modulo strictly smaller terms, so its norm equals `‖f 0‖ > 0`. -/
theorem tsum_mul_pow_ne_zero {f : ℕ → K} (hf : Summable f) (hf0 : f 0 ≠ 0)
    (hlast : ∀ n, 0 < n → ‖f n‖ < ‖f 0‖) {v : K} (hv : ‖v‖ ≤ 1) :
    (∑' n : ℕ, f n * v ^ n) ≠ 0 := by
  obtain ⟨C, hC0, hCM, hCbd⟩ := exists_bound_lt hf hf0 hlast
  have hsum := summable_mul_pow hf hv
  intro hzero
  rw [hsum.tsum_eq_zero_add] at hzero
  simp only [pow_zero, mul_one] at hzero
  set tail := ∑' n : ℕ, f (n + 1) * v ^ (n + 1) with htail
  have htailbd : ‖tail‖ ≤ C := by
    rw [htail]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC0 fun n => ?_
    rw [norm_mul, norm_pow]
    calc ‖f (n + 1)‖ * ‖v‖ ^ (n + 1) ≤ ‖f (n + 1)‖ * 1 ^ (n + 1) := by gcongr
      _ = ‖f (n + 1)‖ := by rw [one_pow, mul_one]
      _ ≤ C := hCbd (n + 1) (by omega)
  have hne : ‖f 0‖ ≠ ‖tail‖ := (ne_of_lt (lt_of_le_of_lt htailbd hCM)).symm
  have heq : ‖f 0 + tail‖ = ‖f 0‖ := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne,
        max_eq_left (le_of_lt (lt_of_le_of_lt htailbd hCM))]
  rw [hzero, norm_zero] at heq
  exact hf0 (norm_eq_zero.mp heq.symm)

/-! ### Weierstrass division by `v - α` -/

/-- The coefficients of the Weierstrass quotient `f v / (v - α)`, namely
`g n = ∑' j, f (n + 1 + j) · αʲ`. When `α` is a root of `f` on the ball, `f v = (v - α) · g v`. -/
noncomputable def wCoeff (f : ℕ → K) (α : K) (n : ℕ) : K := ∑' j : ℕ, f (n + 1 + j) * α ^ j

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Unfolding lemma for `wCoeff`. -/
theorem wCoeff_apply (f : ℕ → K) (α : K) (n : ℕ) :
    wCoeff f α n = ∑' j : ℕ, f (n + 1 + j) * α ^ j := rfl

/-- Each defining series of `wCoeff` converges (for `‖α‖ ≤ 1`). -/
theorem wCoeff_summable_family {f : ℕ → K} (hf : Summable f) {α : K} (hα : ‖α‖ ≤ 1) (n : ℕ) :
    Summable fun j : ℕ => f (n + 1 + j) * α ^ j := by
  have hshift : Summable fun j : ℕ => f (n + 1 + j) :=
    ((summable_nat_add_iff (n + 1)).mpr hf).congr fun j => by rw [Nat.add_comm]
  refine summable_of_norm_le hshift fun j => ?_
  rw [norm_mul, norm_pow]
  calc ‖f (n + 1 + j)‖ * ‖α‖ ^ j ≤ ‖f (n + 1 + j)‖ * 1 ^ j := by gcongr
    _ = ‖f (n + 1 + j)‖ := by rw [one_pow, mul_one]

/-- The synthetic-division recursion `f (n+1) = g n - α · g (n+1)`. -/
theorem wCoeff_rec {f : ℕ → K} (hf : Summable f) {α : K} (hα : ‖α‖ ≤ 1) (n : ℕ) :
    f (n + 1) = wCoeff f α n - α * wCoeff f α (n + 1) := by
  have h1 : wCoeff f α n = f (n + 1) + α * wCoeff f α (n + 1) := by
    rw [wCoeff_apply, (wCoeff_summable_family hf hα n).tsum_eq_zero_add, wCoeff_apply,
      ← tsum_mul_left]
    congr 1
    · rw [Nat.add_zero, pow_zero, mul_one]
    · refine tsum_congr fun j => ?_
      rw [pow_succ]
      have hidx : n + 1 + (j + 1) = n + 1 + 1 + j := by omega
      rw [hidx]; ring
  rw [h1]; ring

/-- The Weierstrass quotient coefficients are again summable. -/
theorem wCoeff_summable {f : ℕ → K} (hf : Summable f) {α : K} (hα : ‖α‖ ≤ 1) :
    Summable (wCoeff f α) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop,
    NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hf0t : Tendsto f atTop (𝓝 0) := by
    simpa [Nat.cofinite_eq_atTop] using hf.tendsto_cofinite_zero
  obtain ⟨P, hP⟩ := Metric.tendsto_atTop.mp hf0t (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop P] with n hn
  rw [wCoeff_apply]
  have hbd : ‖∑' j : ℕ, f (n + 1 + j) * α ^ j‖ ≤ ε / 2 := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by linarith) fun j => ?_
    rw [norm_mul, norm_pow]
    calc ‖f (n + 1 + j)‖ * ‖α‖ ^ j ≤ ‖f (n + 1 + j)‖ * 1 ^ j := by gcongr
      _ = ‖f (n + 1 + j)‖ := by rw [one_pow, mul_one]
      _ ≤ ε / 2 := by
          have := hP (n + 1 + j) (by omega)
          rw [dist_eq_norm, sub_zero] at this
          exact this.le
  linarith

/-- **The division identity.** If `α` is a root of the convergent series on the ball, then on the
whole closed ball `f v = (v - α) · g v` where `g = wCoeff f α`. This is a pure rearrangement of
convergent sums via the coefficient recursion; no Cauchy-product machinery is needed because
`v - α` is a two-term polynomial. -/
theorem tsum_wCoeff_div {f : ℕ → K} (hf : Summable f) {α : K} (hα : ‖α‖ ≤ 1)
    (hroot : (∑' n : ℕ, f n * α ^ n) = 0) {v : K} (hv : ‖v‖ ≤ 1) :
    (∑' n : ℕ, f n * v ^ n) = (v - α) * ∑' n : ℕ, wCoeff f α n * v ^ n := by
  have hg := wCoeff_summable hf hα
  have hFsum := summable_mul_pow hf hv
  have hGsum := summable_mul_pow hg hv
  -- the root relation at the constant term
  have hg0 : f 0 + α * wCoeff f α 0 = 0 := by
    have h := (summable_mul_pow hf hα).tsum_eq_zero_add
    rw [hroot, pow_zero, mul_one] at h
    have h2 : (∑' n : ℕ, f (n + 1) * α ^ (n + 1)) = α * wCoeff f α 0 := by
      rw [wCoeff_apply, ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      rw [pow_succ]
      have hidx : 0 + 1 + n = n + 1 := by omega
      rw [hidx]; ring
    rw [h2] at h; exact h.symm
  -- ∑ f·vⁿ + α·∑ g·vⁿ = ∑ (f n + α g n)·vⁿ
  have hHsum : Summable fun n : ℕ => (f n + α * wCoeff f α n) * v ^ n := by
    have hrw : (fun n : ℕ => (f n + α * wCoeff f α n) * v ^ n)
        = fun n => f n * v ^ n + α * (wCoeff f α n * v ^ n) := by funext n; ring
    rw [hrw]; exact hFsum.add (hGsum.mul_left α)
  have hHsplit : (∑' n : ℕ, (f n + α * wCoeff f α n) * v ^ n)
      = (∑' n : ℕ, f n * v ^ n) + α * ∑' n : ℕ, wCoeff f α n * v ^ n := by
    rw [← tsum_mul_left, ← hFsum.tsum_add (hGsum.mul_left α)]
    exact tsum_congr fun n => by ring
  -- and it also equals ∑ g·v^(n+1) using the recursion + root
  have hHzero : (∑' n : ℕ, (f n + α * wCoeff f α n) * v ^ n)
      = ∑' n : ℕ, wCoeff f α n * v ^ (n + 1) := by
    rw [hHsum.tsum_eq_zero_add, pow_zero, mul_one, hg0, zero_add]
    refine tsum_congr fun n => ?_
    congr 1
    have hr := wCoeff_rec hf hα n
    rw [hr]; ring
  have hshift : (∑' n : ℕ, wCoeff f α n * v ^ (n + 1))
      = v * ∑' n : ℕ, wCoeff f α n * v ^ n := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by rw [pow_succ]; ring
  have key : (∑' n : ℕ, f n * v ^ n) + α * ∑' n : ℕ, wCoeff f α n * v ^ n
      = v * ∑' n : ℕ, wCoeff f α n * v ^ n := by rw [← hHsplit, hHzero, hshift]
  rw [sub_mul, eq_sub_iff_add_eq]
  exact key

/-! ### Finiteness of the zero set -/

/-- **Strassmann's theorem, indexed form.** If `N` is the largest index attaining the maximum
coefficient norm (`f N` dominates weakly, and dominates *strictly* beyond `N`), then `f` has at
most `N` zeros on the closed unit ball — in particular, finitely many. Proved by strong induction
on `N`: with no root the zero set is empty; the base `N = 0` is the maximum-modulus principle; the
step divides out a root and recurses on the quotient, whose largest max-index is `N - 1`. -/
theorem finite_zeros_isTop (N : ℕ) : ∀ f : ℕ → K, Summable f → f N ≠ 0 →
    (∀ n, ‖f n‖ ≤ ‖f N‖) → (∀ n, N < n → ‖f n‖ < ‖f N‖) →
    {v : K | ‖v‖ ≤ 1 ∧ (∑' n : ℕ, f n * v ^ n) = 0}.Finite := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro f hf hfN hmax hlast
    by_cases hroot : ∃ α, ‖α‖ ≤ 1 ∧ (∑' n : ℕ, f n * α ^ n) = 0
    · obtain ⟨α, hα, hαroot⟩ := hroot
      obtain _ | k := N
      · exact absurd hαroot (tsum_mul_pow_ne_zero hf hfN hlast hα)
      · -- `N = k + 1`: divide by `v - α` and recurse on `g = wCoeff f α`.
        obtain ⟨C, hC0, hCM, hCbd⟩ := exists_bound_lt hf hfN hlast
        have hgsum : Summable (wCoeff f α) := wCoeff_summable hf hα
        have hterm : ∀ n j : ℕ, ‖f (n + 1 + j) * α ^ j‖ ≤ ‖f (n + 1 + j)‖ := by
          intro n j
          rw [norm_mul, norm_pow]
          calc ‖f (n + 1 + j)‖ * ‖α‖ ^ j ≤ ‖f (n + 1 + j)‖ * 1 ^ j := by gcongr
            _ = ‖f (n + 1 + j)‖ := by rw [one_pow, mul_one]
        have hgle : ∀ n, ‖wCoeff f α n‖ ≤ ‖f (k + 1)‖ := by
          intro n
          rw [wCoeff_apply]
          exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _)
            fun j => (hterm n j).trans (hmax _)
        have hgC : ∀ n, k + 1 ≤ n → ‖wCoeff f α n‖ ≤ C := by
          intro n hn
          rw [wCoeff_apply]
          exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC0
            fun j => (hterm n j).trans (hCbd _ (by omega))
        have hαgC : ‖α * wCoeff f α (k + 1)‖ ≤ C := by
          rw [norm_mul]
          calc ‖α‖ * ‖wCoeff f α (k + 1)‖ ≤ 1 * ‖wCoeff f α (k + 1)‖ := by gcongr
            _ = ‖wCoeff f α (k + 1)‖ := one_mul _
            _ ≤ C := hgC _ (le_refl _)
        have hαglt : ‖α * wCoeff f α (k + 1)‖ < ‖f (k + 1)‖ := lt_of_le_of_lt hαgC hCM
        have hgkval : wCoeff f α k = f (k + 1) + α * wCoeff f α (k + 1) := by
          have hr := wCoeff_rec hf hα k; rw [hr]; ring
        have hgkM : ‖wCoeff f α k‖ = ‖f (k + 1)‖ := by
          rw [hgkval, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hαglt.ne',
            max_eq_left hαglt.le]
        have hgk_ne : wCoeff f α k ≠ 0 := by
          rw [← norm_pos_iff, hgkM]; exact norm_pos_iff.mpr hfN
        have hgmax : ∀ n, ‖wCoeff f α n‖ ≤ ‖wCoeff f α k‖ := by rw [hgkM]; exact hgle
        have hglast : ∀ n, k < n → ‖wCoeff f α n‖ < ‖wCoeff f α k‖ := by
          intro n hn; rw [hgkM]; exact lt_of_le_of_lt (hgC n (by omega)) hCM
        have hgfin := ih k (by omega) (wCoeff f α) hgsum hgk_ne hgmax hglast
        refine (hgfin.insert α).subset ?_
        rintro v ⟨hv, hzero⟩
        rw [tsum_wCoeff_div hf hα hαroot hv] at hzero
        rcases mul_eq_zero.mp hzero with h | h
        · rw [sub_eq_zero] at h
          exact Set.mem_insert_iff.mpr (Or.inl h)
        · exact Set.mem_insert_iff.mpr (Or.inr ⟨hv, h⟩)
    · -- no root on the ball: the zero set is empty.
      convert Set.finite_empty
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hv hzero => hroot ⟨v, hv, hzero⟩

/-- **Strassmann's theorem on the closed unit ball.** A convergent one-sided power series
`v ↦ ∑' n, fₙ vⁿ` over a complete nonarchimedean field, with summable coefficients and not
identically zero, has only finitely many zeros on the closed unit ball `{v | ‖v‖ ≤ 1}`. -/
theorem finite_zeros {f : ℕ → K} (hf : Summable f) (hf0 : f ≠ 0) :
    {v : K | ‖v‖ ≤ 1 ∧ (∑' n : ℕ, f n * v ^ n) = 0}.Finite := by
  -- pick an index where the coefficient norm is maximal, then the *largest* such index `N`.
  obtain ⟨i₁, hi₁⟩ : ∃ i, f i ≠ 0 := Function.ne_iff.mp hf0
  obtain ⟨i₀, hi₀, hi₀max⟩ := hf.exists_max_norm hi₁
  have hpos : 0 < ‖f i₀‖ := norm_pos_iff.mpr hi₀
  have htend : Tendsto (fun n => ‖f n‖) cofinite (𝓝 0) := by
    simpa using hf.tendsto_cofinite_zero.norm
  -- the superlevel set `{n | ‖f i₀‖ ≤ ‖f n‖}` is finite and nonempty.
  have hfin : {n : ℕ | ‖f i₀‖ ≤ ‖f n‖}.Finite := by
    have hev := Filter.eventually_cofinite.mp (htend.eventually (Iio_mem_nhds hpos))
    exact hev.subset fun n hn => not_lt.mpr (by simpa using hn)
  have hne : hfin.toFinset.Nonempty := by
    refine ⟨i₀, ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  set N := hfin.toFinset.max' hne with hNdef
  have hNle : ‖f i₀‖ ≤ ‖f N‖ :=
    (Set.Finite.mem_toFinset hfin).mp (hfin.toFinset.max'_mem hne)
  have hfN : f N ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hpos hNle)
  have hmax : ∀ n, ‖f n‖ ≤ ‖f N‖ := fun n => (hi₀max n).trans hNle
  have hlast : ∀ n, N < n → ‖f n‖ < ‖f N‖ := by
    intro n hn
    refine lt_of_lt_of_le ?_ hNle
    by_contra hcon
    rw [not_lt] at hcon
    have hmem : n ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).mpr hcon
    have : n ≤ N := hfin.toFinset.le_max' n hmem
    omega
  exact finite_zeros_isTop N f hf hfN hmax hlast

end TateCurvesTheta.Strassmann
