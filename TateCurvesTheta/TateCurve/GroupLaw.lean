/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.TateCurve.AbelStep
import TateCurvesTheta.TateCurve.AdditionLaw
import TateCurvesTheta.TateCurve.LargePointParametrization

/-!
# The group law of the Tate parametrization: the embedding `Kˣ/qᶻ ↪ E_q(K)`

This file assembles the analytic ingredients — the nonarchimedean Abel step
(`TateCurve/AbelStep.lean`), the secant addition law (`TateCurve/AdditionLaw.lean`) and the
large-point parametrization (`TateCurve/LargePointParametrization.lean`) — into the group
law of the Tate parametrization: the point map `u ↦ (X(u), Y(u))` is a **group
homomorphism** `Kˣ → E_q(K)` which descends to an **injective** homomorphism
`Kˣ/qᶻ ↪ E_q(K)` on the analytic quotient.

The additivity `tatePoint (u·v) = tatePoint u + tatePoint v` is proved in three layers:

* **good pairs** (`tatePoint_add_of_good`): when `u`, `v`, `u·v`, `u·v⁻¹`, `u²·v`, `u·v²`
  all avoid `qᶻ`, the secant line through `P(u)` and `P(v)` meets the curve again at the
  class of `(u·v)⁻¹` (`line_third_intersection`), the three abscissae are distinct by the
  `X`-separation theorem (`class_eq_or_inv_of_X_eq`), and the secant step
  `tatePoint_add_of_line` concludes;
* **degenerate orbit cases**: `u`, `v` or `u·v` in `qᶻ`, by `qᶻ`-invariance and negation;
* **the general case**, by the translation trick `P(u·v) = P(u·s) + P(s⁻¹·v)` with an
  auxiliary unit `s` avoiding finitely many `qᶻ`-classes and square-classes
  (`exists_unit_avoiding_sq`, using `‖2‖ = 1`, which follows from `‖12‖ = 1`).

**Surjectivity seam.** Injectivity is complete; surjectivity is delivered for all affine
points with `‖x‖ > 1` (`exists_tatePoint_eq_some`, from the fixed-point construction in
`LargePointParametrization.lean`). Points with `‖x‖ ≤ 1` require reduction theory or a
Newton-polygon zero-existence theorem for the theta function and are left as a documented
seam (issue #118): the concrete deliverable is the injective embedding `Kˣ/qᶻ ↪ E_q(K)`
together with large-point surjectivity.

## Main results

* `TateCurvesTheta.TateParameter.tatePoint_mul`: full additivity of the point map.
* `TateCurvesTheta.TateParameter.tatePointHom`: the point map as a homomorphism
  `Kˣ →* Multiplicative E_q(K)`, with kernel exactly `qᶻ` (`tatePointHom_ker`).
* `TateCurvesTheta.TateParameter.mapTatePointHom`: the descended homomorphism
  `Kˣ/qᶻ →* Multiplicative E_q(K)`.
* `TateCurvesTheta.TateParameter.mapTatePointHom_injective`: injectivity — the Tate
  uniformization embedding.
* `TateCurvesTheta.TateParameter.exists_tatePoint_eq_some`: large-point surjectivity.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* P. Roquette, *Analytic theory of elliptic functions over local fields*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-! ### Norm preliminaries -/

omit [CompleteSpace K] in
/-- In an ultrametric field, `‖12‖ = 1` forces `‖2‖ = 1` (residue characteristic is
neither `2` nor `3`). -/
lemma norm_two_eq_one_of_norm_twelve (h12 : ‖(12 : K)‖ = 1) : ‖(2 : K)‖ = 1 := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 2
  have h3 : ‖(3 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 3
  have h223 : (2 : K) * 2 * 3 = 12 := by norm_num
  have hprod : ‖(2 : K)‖ * ‖(2 : K)‖ * ‖(3 : K)‖ = 1 := by
    rw [← norm_mul, ← norm_mul, h223, h12]
  refine le_antisymm h2 ?_
  by_contra hlt
  rw [not_le] at hlt
  have hsm : ‖(2 : K)‖ * ‖(2 : K)‖ * ‖(3 : K)‖ < 1 := by
    nlinarith [norm_nonneg (2 : K), norm_nonneg (3 : K)]
  linarith [hprod ▸ hsm]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- `‖12‖ = 1` gives `12 ≠ 0`. -/
lemma twelve_ne_zero_of_norm (h12 : ‖(12 : K)‖ = 1) : (12 : K) ≠ 0 := by
  intro h
  rw [h, norm_zero] at h12
  exact zero_ne_one h12

/-! ### Membership plumbing for the orbit subgroup `qᶻ` -/

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Membership in `qᶻ` in terms of the value of the unit: `w ∈ qᶻ ↔ w = qⁿ` in `K`. -/
lemma mem_qpowers_iff_val_eq {w : Kˣ} :
    w ∈ t.qpowers ↔ ∃ n : ℤ, (w : K) = (t.q : K) ^ n := by
  rw [mem_qpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨-n, by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_right hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨-n, by
      rw [hn, zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (Units.ne_zero t.q))]⟩

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- A unit whose value is a power of `q` lies in `qᶻ`. -/
lemma mem_qpowers_of_val_eq {w : Kˣ} {k : ℤ} (h : (w : K) = (t.q : K) ^ k) :
    w ∈ t.qpowers :=
  t.mem_qpowers_iff_val_eq.mpr ⟨k, h⟩

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The off-orbit hypothesis `∀ n, qⁿ·u ≠ 1` says exactly `u ∉ qᶻ`. -/
lemma notMem_qpowers_of_off_orbit {u : Kˣ}
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) : u ∉ t.qpowers := fun h => by
  obtain ⟨n, hn⟩ := (t.mem_qpowers_iff u).mp h
  exact hu n hn

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- If `y·s ∈ qᶻ`, then `s` lies in the `qᶻ`-class of `y⁻¹` — the bridge from subgroup
membership to the avoidance conditions of `exists_unit_avoiding_sq`. -/
lemma exists_val_eq_of_mul_mem {y s : Kˣ} (h : y * s ∈ t.qpowers) :
    ∃ n : ℤ, (s : K) = (t.q : K) ^ n * ((y⁻¹ : Kˣ) : K) := by
  obtain ⟨n, hn⟩ := t.mem_qpowers_iff_val_eq.mp h
  rw [Units.val_mul] at hn
  have hy : (y : K) ≠ 0 := Units.ne_zero y
  refine ⟨n, ?_⟩
  rw [Units.val_inv_eq_inv_val]
  field_simp
  linear_combination hn

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Square-class version of the bridge: if `y·s² ∈ qᶻ`, then `s²` lies in the `qᶻ`-class
of `y⁻¹`. -/
lemma exists_sq_val_eq_of_mul_sq_mem {y s : Kˣ} (h : y * s ^ 2 ∈ t.qpowers) :
    ∃ n : ℤ, ((s : K)) ^ 2 = (t.q : K) ^ n * ((y⁻¹ : Kˣ) : K) := by
  obtain ⟨n, hn⟩ := t.mem_qpowers_iff_val_eq.mp h
  rw [Units.val_mul, Units.val_pow_eq_pow_val] at hn
  have hy : (y : K) ≠ 0 := Units.ne_zero y
  refine ⟨n, ?_⟩
  rw [Units.val_inv_eq_inv_val]
  field_simp
  linear_combination hn

/-! ### Good-pair additivity -/

variable (hmem : ∀ u : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) →
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u)) (h12 : ‖(12 : K)‖ = 1)

section Secant

variable [DecidableEq K]

/-! ### Degenerate orbit cases -/

/-- Additivity when the left factor lies on the orbit: `qᶻ`-invariance. -/
lemma tatePoint_mul_of_mem_left {u : Kˣ} (hu : u ∈ t.qpowers) (v : Kˣ) :
    t.tatePoint hmem h12 (u * v) = t.tatePoint hmem h12 u + t.tatePoint hmem h12 v := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (by rwa [show t.qpowers = Subgroup.zpowers t.q from rfl] at hu)
  rw [t.tatePoint_of_mem hmem h12 hu, zero_add, ← hk]
  exact t.tatePoint_zpow_q_mul hmem h12 k v

/-- Additivity when the right factor lies on the orbit. -/
lemma tatePoint_mul_of_mem_right (u : Kˣ) {v : Kˣ} (hv : v ∈ t.qpowers) :
    t.tatePoint hmem h12 (u * v) = t.tatePoint hmem h12 u + t.tatePoint hmem h12 v := by
  rw [mul_comm u v, t.tatePoint_mul_of_mem_left hmem h12 hv u, add_comm]

/-- Additivity when the product lies on the orbit: inverse classes map to opposite
points, by negation (`tatePoint_inv`). -/
lemma tatePoint_mul_of_mul_mem {u v : Kˣ} (huv : u * v ∈ t.qpowers) :
    t.tatePoint hmem h12 (u * v) = t.tatePoint hmem h12 u + t.tatePoint hmem h12 v := by
  rw [t.tatePoint_of_mem hmem h12 huv]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (by rwa [show t.qpowers = Subgroup.zpowers t.q from rfl] at huv)
  have hv' : v = t.q ^ k * u⁻¹ := by
    rw [hk, mul_comm u v, mul_inv_cancel_right]
  have hPv : t.tatePoint hmem h12 v = -t.tatePoint hmem h12 u := by
    rw [hv', t.tatePoint_zpow_q_mul hmem h12 k u⁻¹, t.tatePoint_inv hmem h12 u]
  rw [hPv, add_neg_cancel]

/-- **Good-pair additivity.** When `u`, `v`, `u·v`, `u·v⁻¹`, `u²·v` and `u·v²` all avoid
the orbit subgroup `qᶻ`, the secant construction applies verbatim:
`tatePoint u + tatePoint v = tatePoint (u·v)`. -/
theorem tatePoint_add_of_good {u v : Kˣ} (hu : u ∉ t.qpowers) (hv : v ∉ t.qpowers)
    (huv : u * v ∉ t.qpowers) (hratio : u * v⁻¹ ∉ t.qpowers)
    (hu2v : u ^ 2 * v ∉ t.qpowers) (huv2 : u * v ^ 2 ∉ t.qpowers) :
    t.tatePoint hmem h12 u + t.tatePoint hmem h12 v = t.tatePoint hmem h12 (u * v) := by
  have hu0 : (u : K) ≠ 0 := Units.ne_zero u
  have hv0 : (v : K) ≠ 0 := Units.ne_zero v
  have hu' := t.qzpow_mul_ne_one_of_notMem hu
  have hv' := t.qzpow_mul_ne_one_of_notMem hv
  have hw : (u * v)⁻¹ ∉ t.qpowers := fun h => huv ((t.inv_mem_qpowers_iff (u * v)).mp h)
  have hw' := t.qzpow_mul_ne_one_of_notMem hw
  -- the three abscissae are pairwise distinct, by X-separation
  have hx12 : t.X u ≠ t.X v := by
    intro hX
    rcases t.class_eq_or_inv_of_X_eq hu' hv' hX with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine hratio (t.mem_qpowers_of_val_eq (w := u * v⁻¹) (k := k) ?_)
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hk, mul_assoc,
        mul_inv_cancel₀ hv0, mul_one]
    · refine huv (t.mem_qpowers_of_val_eq (w := u * v) (k := k) ?_)
      rw [Units.val_mul, hk, Units.val_inv_eq_inv_val, mul_assoc,
        inv_mul_cancel₀ hv0, mul_one]
  have hx13 : t.X u ≠ t.X ((u * v)⁻¹) := by
    intro hX
    rcases t.class_eq_or_inv_of_X_eq hu' hw' hX with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine hu2v (t.mem_qpowers_of_val_eq (w := u ^ 2 * v) (k := k) ?_)
      rw [Units.val_inv_eq_inv_val, Units.val_mul] at hk
      rw [Units.val_mul, Units.val_pow_eq_pow_val]
      field_simp at hk
      linear_combination hk
    · rw [inv_inv] at hk
      refine hv (t.mem_qpowers_of_val_eq (w := v) (k := -k) ?_)
      rw [Units.val_mul] at hk
      have hcancel : (u : K) * 1 = (u : K) * ((t.q : K) ^ k * (v : K)) := by
        linear_combination hk
      have h1 : (1 : K) = (t.q : K) ^ k * (v : K) := mul_left_cancel₀ hu0 hcancel
      rw [zpow_neg]
      exact eq_inv_of_mul_eq_one_right (by linear_combination -h1)
  have hx23 : t.X v ≠ t.X ((u * v)⁻¹) := by
    intro hX
    rcases t.class_eq_or_inv_of_X_eq hv' hw' hX with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine huv2 (t.mem_qpowers_of_val_eq (w := u * v ^ 2) (k := k) ?_)
      rw [Units.val_inv_eq_inv_val, Units.val_mul] at hk
      rw [Units.val_mul, Units.val_pow_eq_pow_val]
      field_simp at hk
      linear_combination hk
    · rw [inv_inv] at hk
      refine hu (t.mem_qpowers_of_val_eq (w := u) (k := -k) ?_)
      rw [Units.val_mul] at hk
      have hcancel : (v : K) * 1 = (v : K) * ((t.q : K) ^ k * (u : K)) := by
        linear_combination hk
      have h1 : (1 : K) = (t.q : K) ^ k * (u : K) := mul_left_cancel₀ hv0 hcancel
      rw [zpow_neg]
      exact eq_inv_of_mul_eq_one_right (by linear_combination -h1)
  -- the secant line through the two points
  have hsub : t.X u - t.X v ≠ 0 := sub_ne_zero.mpr hx12
  set lam : K := (t.Y u - t.Y v) / (t.X u - t.X v) with hlam
  set mu : K := t.Y u - lam * t.X u with hmu
  have h1 : t.Y u = lam * t.X u + mu := by rw [hmu]; ring
  have h2 : t.Y v = lam * t.X v + mu := by
    rw [hmu, hlam]
    field_simp
    ring
  -- separation of the two classes, for the third-intersection theorem
  have huv_sep : ∀ n : ℤ, (v : K) ≠ (t.q : K) ^ n * (u : K) := by
    intro n hn
    refine hratio (t.mem_qpowers_of_val_eq (w := u * v⁻¹) (k := -n) ?_)
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hn, zpow_neg, mul_inv, ← mul_assoc,
      mul_comm (u : K) ((t.q : K) ^ n)⁻¹, mul_assoc, mul_inv_cancel₀ hu0, mul_one]
  have h3 := t.line_third_intersection hu' hv' hw' huv_sep h1 h2
  exact t.tatePoint_add_of_line hmem h12 hu hv hw h1 h2 h3 hx12 hx13 hx23

/-- **Full additivity of the Tate point map**: `tatePoint (u·v) = tatePoint u +
tatePoint v` for all units, by the translation trick `P(u·v) = P(u·s) + P(s⁻¹·v)` with an
auxiliary unit `s` avoiding finitely many `qᶻ`-classes and square-classes. -/
theorem tatePoint_mul (u v : Kˣ) :
    t.tatePoint hmem h12 (u * v) = t.tatePoint hmem h12 u + t.tatePoint hmem h12 v := by
  classical
  by_cases hu : u ∈ t.qpowers
  · exact t.tatePoint_mul_of_mem_left hmem h12 hu v
  by_cases hv : v ∈ t.qpowers
  · exact t.tatePoint_mul_of_mem_right hmem h12 u hv
  by_cases huv : u * v ∈ t.qpowers
  · exact t.tatePoint_mul_of_mul_mem hmem h12 huv
  -- generic case: translate by an avoiding unit `s`
  obtain ⟨s, hS, hT⟩ := t.exists_unit_avoiding_sq (norm_two_eq_one_of_norm_twelve h12)
    {1, u, u⁻¹, (u ^ 2)⁻¹, v, v⁻¹, v ^ 2, (u ^ 2 * v)⁻¹, u * v ^ 2}
    {u⁻¹, v, (u * v⁻¹)⁻¹}
  -- the twelve non-membership conditions for the three good pairs
  have hs : s ∉ t.qpowers := by
    intro h
    obtain ⟨n, hn⟩ := t.exists_val_eq_of_mul_mem (y := 1) (by rwa [one_mul])
    exact hS 1 (by simp) n (by simpa using hn)
  have hs_inv : s⁻¹ ∉ t.qpowers := fun h => hs ((t.inv_mem_qpowers_iff s).mp h)
  have h_us : u * s ∉ t.qpowers := by
    intro h
    obtain ⟨n, hn⟩ := t.exists_val_eq_of_mul_mem h
    exact hS u⁻¹ (by simp) n hn
  have h_usi : u * s⁻¹ ∉ t.qpowers := by
    intro h
    have h' : u⁻¹ * s ∈ t.qpowers := by
      have h2' := inv_mem h
      rwa [mul_inv_rev, inv_inv, mul_comm] at h2'
    obtain ⟨n, hn⟩ := t.exists_val_eq_of_mul_mem h'
    exact hS u (by simp) n (by simpa using hn)
  have h_u2s : u ^ 2 * s ∉ t.qpowers := by
    intro h
    obtain ⟨n, hn⟩ := t.exists_val_eq_of_mul_mem h
    exact hS ((u ^ 2)⁻¹) (by simp) n hn
  have h_us2 : u * s ^ 2 ∉ t.qpowers := by
    intro h
    obtain ⟨n, hn⟩ := t.exists_sq_val_eq_of_mul_sq_mem h
    exact hT u⁻¹ (by simp) n hn
  have h_siv : s⁻¹ * v ∉ t.qpowers := by
    intro h
    have h' : v⁻¹ * s ∈ t.qpowers := by
      have h2' := inv_mem h
      rwa [mul_inv_rev, inv_inv] at h2'
    obtain ⟨n, hn⟩ := t.exists_val_eq_of_mul_mem h'
    exact hS v (by simp) n (by simpa using hn)
  have h_sivi : s⁻¹ * v⁻¹ ∉ t.qpowers := by
    intro h
    have h' : v * s ∈ t.qpowers := by
      have h2' := inv_mem h
      rwa [mul_inv_rev, inv_inv, inv_inv] at h2'
    obtain ⟨n, hn⟩ := t.exists_val_eq_of_mul_mem h'
    exact hS v⁻¹ (by simp) n hn
  have h_si2v : s⁻¹ ^ 2 * v ∉ t.qpowers := by
    intro h
    have h' : v⁻¹ * s ^ 2 ∈ t.qpowers := by
      have h2' := inv_mem h
      rwa [mul_inv_rev, inv_pow, inv_inv] at h2'
    obtain ⟨n, hn⟩ := t.exists_sq_val_eq_of_mul_sq_mem h'
    exact hT v (by simp) n (by simpa using hn)
  have h_siv2 : s⁻¹ * v ^ 2 ∉ t.qpowers := by
    intro h
    have h' : (v ^ 2)⁻¹ * s ∈ t.qpowers := by
      have h2' := inv_mem h
      rwa [mul_inv_rev, inv_inv] at h2'
    obtain ⟨n, hn⟩ := t.exists_val_eq_of_mul_mem h'
    exact hS (v ^ 2) (by simp) n (by simpa using hn)
  -- pair-3 words, rewritten to `word · s`-form via `Units.ext`
  have hprod3 : (u * s) * (s⁻¹ * v) = u * v := by
    rw [mul_assoc, ← mul_assoc s s⁻¹ v, mul_inv_cancel, one_mul]
  have h_p3prod : (u * s) * (s⁻¹ * v) ∉ t.qpowers := fun h => huv (hprod3 ▸ h)
  have hs0 : (s : K) ≠ 0 := Units.ne_zero s
  have hu0 : (u : K) ≠ 0 := Units.ne_zero u
  have hv0 : (v : K) ≠ 0 := Units.ne_zero v
  have h_r3 : (u * s) * (s⁻¹ * v)⁻¹ ∉ t.qpowers := by
    intro h
    have heq : (u * s) * (s⁻¹ * v)⁻¹ = (u * v⁻¹) * s ^ 2 := Units.ext (by
      push_cast [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      field_simp)
    rw [heq] at h
    obtain ⟨n, hn⟩ := t.exists_sq_val_eq_of_mul_sq_mem h
    exact hT ((u * v⁻¹)⁻¹) (by simp) n hn
  have h_p3b : (u * s) ^ 2 * (s⁻¹ * v) ∉ t.qpowers := by
    intro h
    have heq : (u * s) ^ 2 * (s⁻¹ * v) = (u ^ 2 * v) * s := Units.ext (by
      push_cast [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      field_simp)
    rw [heq] at h
    obtain ⟨n, hn⟩ := t.exists_val_eq_of_mul_mem h
    exact hS ((u ^ 2 * v)⁻¹) (by simp) n hn
  have h_p3c : (u * s) * (s⁻¹ * v) ^ 2 ∉ t.qpowers := by
    intro h
    have heq : (u * s) * (s⁻¹ * v) ^ 2 = (u * v ^ 2) * s⁻¹ := Units.ext (by
      push_cast [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
      field_simp)
    rw [heq] at h
    have h' : (u * v ^ 2)⁻¹ * s ∈ t.qpowers := by
      have h2' := inv_mem h
      rwa [mul_inv_rev, inv_inv, mul_comm] at h2'
    obtain ⟨n, hn⟩ := t.exists_val_eq_of_mul_mem h'
    exact hS (u * v ^ 2) (by simp) n (by simpa using hn)
  -- the three good pairs
  have g1 := t.tatePoint_add_of_good hmem h12 hu hs h_us h_usi h_u2s h_us2
  have g2 := t.tatePoint_add_of_good hmem h12 hs_inv hv h_siv h_sivi h_si2v h_siv2
  have g3 := t.tatePoint_add_of_good hmem h12 h_us h_siv h_p3prod h_r3 h_p3b h_p3c
  have hPinv : t.tatePoint hmem h12 s⁻¹ = -t.tatePoint hmem h12 s :=
    t.tatePoint_inv hmem h12 s
  calc t.tatePoint hmem h12 (u * v)
      = t.tatePoint hmem h12 ((u * s) * (s⁻¹ * v)) := by rw [hprod3]
    _ = t.tatePoint hmem h12 (u * s) + t.tatePoint hmem h12 (s⁻¹ * v) := g3.symm
    _ = (t.tatePoint hmem h12 u + t.tatePoint hmem h12 s)
        + (t.tatePoint hmem h12 s⁻¹ + t.tatePoint hmem h12 v) := by rw [g1, g2]
    _ = t.tatePoint hmem h12 u + t.tatePoint hmem h12 v := by rw [hPinv]; abel

/-! ### The homomorphism `Kˣ →* E_q(K)` and its descent to `Kˣ/qᶻ` -/

/-- **The Tate point map as a group homomorphism** `Kˣ →* E_q(K)` (the Mordell–Weil group
written multiplicatively via `Multiplicative`). This closes the additivity seam of
issue #117. -/
def tatePointHom : Kˣ →* Multiplicative t.tateCurve.toAffine.Point where
  toFun u := Multiplicative.ofAdd (t.tatePoint hmem h12 u)
  map_one' := by rw [t.tatePoint_one hmem h12]; rfl
  map_mul' u v := by rw [t.tatePoint_mul hmem h12 u v]; rfl

@[simp] lemma tatePointHom_apply (u : Kˣ) :
    t.tatePointHom hmem h12 u = Multiplicative.ofAdd (t.tatePoint hmem h12 u) := rfl

omit [DecidableEq K] in
/-- The point map kills exactly the orbit subgroup `qᶻ`. -/
theorem tatePoint_eq_zero_iff {u : Kˣ} :
    t.tatePoint hmem h12 u = 0 ↔ u ∈ t.qpowers := by
  refine ⟨fun h => ?_, t.tatePoint_of_mem hmem h12⟩
  by_contra hu
  rw [t.tatePoint_of_notMem hmem h12 hu] at h
  exact WeierstrassCurve.Affine.Point.some_ne_zero _ h

/-- The kernel of the Tate point homomorphism is exactly `qᶻ`. -/
theorem tatePointHom_ker : (t.tatePointHom hmem h12).ker = t.qpowers := by
  ext u
  rw [MonoidHom.mem_ker, tatePointHom_apply, ofAdd_eq_one,
    t.tatePoint_eq_zero_iff hmem h12]

/-- **The Tate uniformization homomorphism** `Kˣ/qᶻ →* E_q(K)`: the descent of the point
map to the analytic quotient, as a group homomorphism. -/
def mapTatePointHom : t.AnalyticQuotient →* Multiplicative t.tateCurve.toAffine.Point :=
  QuotientGroup.lift t.qpowers (t.tatePointHom hmem h12)
    (le_of_eq (t.tatePointHom_ker hmem h12).symm)

@[simp] lemma mapTatePointHom_mk (u : Kˣ) :
    t.mapTatePointHom hmem h12 (t.toAnalyticQuotient u) =
      Multiplicative.ofAdd (t.tatePoint hmem h12 u) := rfl

/-- The homomorphism refines the bare descended map `mapTatePoint` of `PointMap.lean`. -/
lemma toAdd_mapTatePointHom (x : t.AnalyticQuotient) :
    Multiplicative.toAdd (t.mapTatePointHom hmem h12 x) = t.mapTatePoint hmem h12 x := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

/-- **Injectivity of the Tate uniformization**: the homomorphism `Kˣ/qᶻ →* E_q(K)` is
injective — the analytic quotient embeds into the Mordell–Weil group. This is the core of
issue #118. -/
theorem mapTatePointHom_injective :
    Function.Injective (t.mapTatePointHom hmem h12) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  rw [QuotientGroup.eq_one_iff, ← t.tatePoint_eq_zero_iff hmem h12, ← ofAdd_eq_one]
  exact hx

omit [DecidableEq K] in
/-- Injectivity of the bare descended point map. -/
theorem mapTatePoint_injective : Function.Injective (t.mapTatePoint hmem h12) := by
  classical
  intro x y hxy
  refine t.mapTatePointHom_injective hmem h12 (Multiplicative.toAdd.injective ?_)
  rw [t.toAdd_mapTatePointHom hmem h12 x, t.toAdd_mapTatePointHom hmem h12 y, hxy]

/-! ### Large-point surjectivity

Full surjectivity of `mapTatePointHom` — hitting also the affine points with `‖x‖ ≤ 1` —
requires reduction theory or a Newton-polygon zero-existence theorem for the theta
function; it is left as a documented seam (issue #118). The delivered result covers all
points outside the closed unit polydisc. -/

omit [DecidableEq K] in
/-- **Large-point surjectivity**: every affine point of the Tate curve whose
`x`-coordinate has norm `> 1` is a Tate point. -/
theorem exists_tatePoint_eq_some {x y : K} (hns : t.tateCurve.toAffine.Nonsingular x y)
    (hx : 1 < ‖x‖) :
    ∃ u : Kˣ, t.tatePoint hmem h12 u = .some x y hns := by
  have hxy : y ^ 2 + x * y = x ^ 3 + t.a₄ * x + t.a₆ :=
    (t.tateCurve_equation_iff x y).mp hns.1
  obtain ⟨u, hoff, hX, hY⟩ := t.exists_tate_coord_of_one_lt_norm
    (norm_two_eq_one_of_norm_twelve h12) (twelve_ne_zero_of_norm h12) hxy hx
  have hu : u ∉ t.qpowers := t.notMem_qpowers_of_off_orbit hoff
  refine ⟨u, ?_⟩
  rw [t.tatePoint_of_notMem hmem h12 hu]
  exact point_some_congr hX hY

end Secant

end TateParameter

end TateCurvesTheta
