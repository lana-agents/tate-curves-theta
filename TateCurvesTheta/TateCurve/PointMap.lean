/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import TateCurvesTheta.TateCurve.Discriminant
import TateCurvesTheta.TateCurve.WeierstrassIdentity
import TateCurvesTheta.TateCurve.Quotient

/-!
# The Tate parametrization point map `tatePoint` and its descent to `Kˣ/qᶻ`

For a Tate parameter `q` over a complete nonarchimedean field `K`, the Tate coordinate series
`X(u)`, `Y(u)` (`TateCurve/Parametrization.lean`) send a unit `u : Kˣ` off the `q`-orbit `qᶻ` to a
point `(X(u), Y(u))` on the Tate curve `E_q` (`tatePoint_mem`, #116), and the point at infinity
`O` for `u ∈ qᶻ`. This file packages that data as a total **point map**
```
tatePoint : Kˣ → E_q(K)   (into the Mordell–Weil group `t.tateCurve.toAffine.Point`)
```
and, using the `q`-periodicity `X_q_smul`, `Y_q_smul` (#111), descends it to the analytic quotient
`Kˣ ⧸ qᶻ` as a **function** `mapTatePoint : Kˣ/qᶻ → E_q(K)`.

## The two seams carried as hypotheses

`tatePoint_mem` produces only a `WeierstrassCurve.Affine.Equation`, and only *conditionally* on the
analytic Laurent-development seam `DefectLaurentRepr` (issue #146) plus `LaurentCoeffUnique` and a
normalization point. Rather than thread those unproved inputs through every definition, this file
abstracts the analytic content into a single hypothesis
```
hmem : ∀ u, (∀ n : ℤ, qⁿ·u ≠ 1) → t.tateCurve.toAffine.Equation (t.X u) (t.Y u)
```
which is *exactly* the conclusion of `tatePoint_mem` (dischargeable once #146 and the normalization
land). Building an honest `Point` also needs to upgrade `Equation` to `Nonsingular`; this uses
`equation_iff_nonsingular`, hence the residue-characteristic hypothesis `h12 : TameResidueChar K`
(`‖2‖ = 1 ∧ 12 ≠ 0`; only the component `12 ≠ 0` is used here, via `tateCurve_isElliptic`, #93,
while `‖2‖ = 1` is the standing hypothesis of the group law built on top of this map). Both
hypotheses are stated explicitly.

## What is delivered here, and what stays a seam

* **Delivered.** `tatePoint`, `tatePoint_one` (`1 ↦ O`), the `qᶻ`-invariance `tatePoint_zpow_q_mul`,
  and the descent `mapTatePoint : t.AnalyticQuotient → E_q(K)` factoring the point map through the
  quotient. The descent needs only `q`-periodicity, **not** the group law.
* **Seam (documented).** That `tatePoint` (and hence `mapTatePoint`) is a *group homomorphism*
  `tateParam (u·v) = tateParam u + tateParam v` — the classical elliptic-function addition theorem —
  is **not** proved here; it is the hard analytic content of the parametrization and remains open
  (issue #117 additivity clause / #118). Consequently `mapTatePoint` is delivered as a plain
  function, not an `AddMonoidHom`.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
-/

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] (t : TateParameter K)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Two affine points of a Weierstrass curve with equal coordinates are equal (the nonsingularity
witnesses live in `Prop`, so they are irrelevant). -/
lemma point_some_congr {W : WeierstrassCurve.Affine K} {x₁ y₁ x₂ y₂ : K}
    {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = .some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- Membership in the discrete `q`-orbit subgroup `qᶻ ≤ Kˣ` is the negation of the off-orbit
hypothesis `∀ n, qⁿ·u ≠ 1` used by `tatePoint_mem` and `one_sub_qzpow_mul_ne_zero`. -/
lemma mem_qpowers_iff (u : Kˣ) :
    u ∈ t.qpowers ↔ ∃ n : ℤ, (t.q : K) ^ n * (u : K) = 1 := by
  rw [show t.qpowers = Subgroup.zpowers t.q from rfl, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have hu : (u : K) = (t.q : K) ^ k := by rw [← hk, Units.val_zpow_eq_zpow_val]
    rw [hu, ← zpow_add₀ (by exact_mod_cast t.q.ne_zero), neg_add_cancel, zpow_zero]
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [zpow_neg]
    apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one]
    exact hn

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The off-orbit reformulation of `u ∉ qᶻ`: if `u` is not in the `q`-orbit subgroup, then
`qⁿ·u ≠ 1` for every `n`, the hypothesis form consumed by `tatePoint_mem`. -/
lemma qzpow_mul_ne_one_of_notMem {u : Kˣ} (hu : u ∉ t.qpowers) (n : ℤ) :
    (t.q : K) ^ n * (u : K) ≠ 1 :=
  not_exists.mp ((t.mem_qpowers_iff u).not.mp hu) n

open scoped Classical in
/-- **The Tate parametrization point map.** Sends `u ∈ qᶻ` to the point at infinity `O` and every
other `u` to the affine point `(X(u), Y(u))` on `E_q`, which lies on the curve by `hmem` (the
`tatePoint_mem` seam) and is nonsingular since `E_q` is elliptic (`h12`). -/
def tatePoint
    (hmem : ∀ u : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) →
      t.tateCurve.toAffine.Equation (t.X u) (t.Y u))
    (h12 : TameResidueChar K) (u : Kˣ) : t.tateCurve.toAffine.Point :=
  if h : u ∈ t.qpowers then 0
  else
    haveI : t.tateCurve.toAffine.IsElliptic := t.tateCurve_isElliptic h12.2
    .some (t.X u) (t.Y u)
      (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
        (hmem u (t.qzpow_mul_ne_one_of_notMem h)))

variable (hmem : ∀ u : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) →
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u)) (h12 : TameResidueChar K)

/-- On the orbit `u ∈ qᶻ`, the point map is the identity `O` of the Mordell–Weil group. -/
lemma tatePoint_of_mem {u : Kˣ} (hu : u ∈ t.qpowers) : t.tatePoint hmem h12 u = 0 := by
  classical
  simp only [tatePoint, dif_pos hu]

/-- Off the orbit, the point map is the affine point `(X(u), Y(u))`. -/
lemma tatePoint_of_notMem {u : Kˣ} (hu : u ∉ t.qpowers) :
    haveI : t.tateCurve.toAffine.IsElliptic := t.tateCurve_isElliptic h12.2
    t.tatePoint hmem h12 u =
      .some (t.X u) (t.Y u)
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (hmem u (t.qzpow_mul_ne_one_of_notMem hu))) := by
  classical
  simp only [tatePoint, dif_neg hu]

/-- The identity `1 ∈ Kˣ` maps to the point at infinity `O` (since `1 ∈ qᶻ`). -/
@[simp] lemma tatePoint_one : t.tatePoint hmem h12 1 = 0 :=
  t.tatePoint_of_mem hmem h12 (one_mem _)

/-- **`q`-invariance (single step).** The point map is unchanged under `u ↦ q·u`, since `X`, `Y`
are `q`-periodic (`X_q_smul`, `Y_q_smul`) and `qᶻ` absorbs the factor `q`. This is what lets the
map descend to `Kˣ/qᶻ`. -/
lemma tatePoint_q_mul (u : Kˣ) : t.tatePoint hmem h12 (t.q * u) = t.tatePoint hmem h12 u := by
  have hq : t.q ∈ t.qpowers := Subgroup.mem_zpowers t.q
  by_cases h : u ∈ t.qpowers
  · rw [t.tatePoint_of_mem hmem h12 ((Subgroup.mul_mem_cancel_left (h := hq)).mpr h),
      t.tatePoint_of_mem hmem h12 h]
  · have h' : t.q * u ∉ t.qpowers :=
      fun hc => h ((Subgroup.mul_mem_cancel_left (h := hq)).mp hc)
    rw [t.tatePoint_of_notMem hmem h12 h', t.tatePoint_of_notMem hmem h12 h]
    exact point_some_congr (t.X_q_smul u) (t.Y_q_smul u)

/-- **`qᶻ`-invariance.** The point map is constant along the whole `q`-orbit: `tatePoint (qⁿ·u) =
tatePoint u` for every `n : ℤ`. -/
lemma tatePoint_zpow_q_mul (n : ℤ) (u : Kˣ) :
    t.tatePoint hmem h12 (t.q ^ n * u) = t.tatePoint hmem h12 u := by
  induction n with
  | zero => simp
  | succ k ih =>
    have e : t.q ^ ((k : ℤ) + 1) * u = t.q * (t.q ^ (k : ℤ) * u) := by
      rw [zpow_add, zpow_one, mul_comm (t.q ^ (k : ℤ)) t.q, mul_assoc]
    rw [e, t.tatePoint_q_mul hmem h12, ih]
  | pred k ih =>
    have hq1 : t.q ^ (1 : ℤ) * t.q ^ (-(k : ℤ) - 1) = t.q ^ (-(k : ℤ)) := by
      rw [← zpow_add]; congr 1; ring
    have e : t.q * (t.q ^ (-(k : ℤ) - 1) * u) = t.q ^ (-(k : ℤ)) * u := by
      rw [← mul_assoc]; nth_rewrite 1 [← zpow_one t.q]; rw [hq1]
    rw [← t.tatePoint_q_mul hmem h12 (t.q ^ (-(k : ℤ) - 1) * u), e, ih]

/-- **Descent to the analytic quotient.** The point map, being `qᶻ`-invariant, descends to a total
function `Kˣ/qᶻ → E_q(K)` on the analytic quotient `AnalyticQuotient = Kˣ ⧸ qᶻ`.

This is the map underlying the Tate uniformization; promoting it to a *group* homomorphism (an
`AddMonoidHom`) is the additivity seam (the elliptic-function addition theorem), open in #117. -/
def mapTatePoint (x : t.AnalyticQuotient) : t.tateCurve.toAffine.Point :=
  Quotient.liftOn' x (t.tatePoint hmem h12) <| by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, show t.toTateDatum.qpowers = Subgroup.zpowers t.q from rfl,
      Subgroup.mem_zpowers_iff] at hab
    obtain ⟨n, hn⟩ := hab
    have hb : t.q ^ n * a = b := by rw [hn, mul_assoc, mul_comm b a, inv_mul_cancel_left]
    rw [← hb, t.tatePoint_zpow_q_mul hmem h12]

/-- The descent factors the point map: `mapTatePoint (toAnalyticQuotient u) = tatePoint u`. -/
@[simp] lemma mapTatePoint_toAnalyticQuotient (u : Kˣ) :
    t.mapTatePoint hmem h12 (t.toAnalyticQuotient u) = t.tatePoint hmem h12 u :=
  rfl

end TateParameter

end TateCurvesTheta
