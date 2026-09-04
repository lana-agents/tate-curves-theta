/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import TateCurvesTheta.TateCurve.A6Series
import TateCurvesTheta.TateCurve.Discriminant

/-!
# Integral model of the Tate curve and its split multiplicative special fiber

Over a complete nonarchimedean field `K` with valuation ring `𝒪 = {x : ‖x‖ ≤ 1}`, the Tate
Weierstrass coefficients `a₄(q) = -5 s₃(q)` and `a₆(q) = -(5 s₃(q) + 7 s₅(q))/12` are *integral*
and in fact lie in the maximal ideal `𝔪 = {x : ‖x‖ < 1}`: we prove `‖a₄(q)‖ ≤ ‖q‖ < 1` and
`‖a₆(q)‖ ≤ ‖q‖ < 1`. Consequently the reduction of `E_q` modulo `𝔪` has `a₄ ≡ a₆ ≡ 0`, i.e. the
special fiber is the nodal cubic `y² + x y = x³`, whose node at `(0,0)` has the two rational
tangent directions `y = 0` and `y = -x` — the hallmark of *split* multiplicative reduction.

## Integrality of `a₆` and the hypothesis `(12 : K) ≠ 0`

`‖a₄‖ ≤ ‖q‖` is immediate from `‖s₃‖ ≤ ‖q‖` (`Discriminant.norm_eisenstein_le`: every Eisenstein
term has norm `≤ ‖q‖`). The integrality of `a₆` is deeper: the denominator `12` is only harmless
because of the term-wise divisibility `12 ∣ 5 m³ + 7 m⁵` (proved in `A6Series.lean` by a residue
computation in `ZMod 12`), which lets us rewrite `5 s₃(q) + 7 s₅(q) = 12 · ∑ₘ cₘ · qᵐ/(1-qᵐ)` with
*integer* coefficients `cₘ = (5 m³ + 7 m⁵)/12`, so that `a₆(q) = -∑ₘ cₘ · qᵐ/(1-qᵐ)`
(`A6Series.a₆_eq_neg_tsum`) has norm `≤ ‖q‖` (`A6Series.norm_a₆_le`). This is exactly the
classical integrality of the Tate coefficients (Silverman ATAEC Ch. V), and it holds in *every*
residue characteristic. The only genuine hypothesis is `(12 : K) ≠ 0`, which is already required
for the `a₆` formula — with its literal `/12` — to be non-degenerate.

## The reduction of the actual invariants of `E_q`

Beyond the abstract nodal cubic we record that the *actual* Weierstrass invariants of `E_q` reduce
as expected: `c₄(E_q) = 1 - 48 a₄(q)` is a **unit** of `𝒪` (`‖c₄‖ = 1`, `norm_c₄_eq_one`,
unconditional), while `Δ(E_q)` lies in `𝔪` (`‖Δ‖ < 1`, `norm_Δ_lt_one`, needing only `(12:K) ≠ 0`).
Together (`tateCurve_multiplicative_reduction`) this is the classical invariant criterion for
**multiplicative reduction**: `Δ ≡ 0` makes the special fiber singular, while `c₄ ≢ 0` forces the
singularity to be a *node* (not a cusp / additive reduction).

## Scope / seam

The reduction `𝒪 → k` to the residue field and the scheme-theoretic special fiber (a nodal cubic
over `k`, split multiplicative) are stated here at the level of the Weierstrass data: the
integrality bounds `‖a₄‖, ‖a₆‖ < 1`, the invariant reductions `‖c₄‖ = 1`, `‖Δ‖ < 1`, and the
abstract nodal cubic `nodalCubic` with `Δ = 0` and its rational tangent-cone factorization.
Packaging the integral Weierstrass model over `𝒪` as a formal scheme and identifying its closed
fiber (reusing the `formal-schemes` dependency) is left as a documented seam.

## Main results

* `TateCurvesTheta.TateParameter.norm_a₄_lt_one` : `‖a₄(q)‖ < 1` (integrality of `a₄`).
* `TateCurvesTheta.TateParameter.norm_a₆_lt_one` : `‖a₆(q)‖ < 1` (integrality of `a₆`).
* `TateCurvesTheta.TateParameter.tateCurve_c₄`, `norm_c₄_eq_one` : `c₄ = 1 - 48 a₄`, a unit of `𝒪`.
* `TateCurvesTheta.TateParameter.norm_Δ_lt_one`,
  `TateCurvesTheta.TateParameter.tateCurve_multiplicative_reduction` : `Δ(E_q)` reduces to `0` and
  the reduction is multiplicative.
* `TateCurvesTheta.nodalCubic`, `nodalCubic_Δ`, `nodalCubic_tangentCone` : the split-multiplicative
  special fiber `y² + x y = x³` at the Weierstrass-data level.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter V (integral
  model, split multiplicative reduction, `y² + xy = x³` special fiber).
* D. Mumford, *An analytic construction of degenerating abelian varieties over complete rings*.
* S. Mochizuki, *Inter-universal Teichmüller Theory I* (split multiplicative reduction hypothesis).
-/

open Filter Topology

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K]
variable (t : TateParameter K)

/-- In a nonarchimedean normed field, every natural-number literal `≥ 2` has norm `≤ 1`. -/
private lemma norm_ofNat_le_one [IsUltrametricDist K] (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : K)‖ ≤ 1 := by
  rw [← Nat.cast_ofNat]
  exact IsUltrametricDist.norm_natCast_le_one K _

section Nonarchimedean

variable [IsUltrametricDist K]

variable [CompleteSpace K]

/-- **Integrality of `a₄`.** The Tate coefficient `a₄(q) = -5 s₃(q)` has norm `< 1`, so it reduces
to `0` in the residue field. -/
lemma norm_a₄_lt_one : ‖t.a₄‖ < 1 := by
  refine lt_of_le_of_lt ?_ t.norm_lt_one
  rw [a₄_def, neg_mul, norm_neg, norm_mul]
  calc ‖(5 : K)‖ * ‖t.eisenstein 3‖
      ≤ 1 * ‖t.eisenstein 3‖ := by
        gcongr
        calc ‖(5 : K)‖ = ‖((5 : ℕ) : K)‖ := by norm_cast
          _ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K 5
    _ = ‖t.eisenstein 3‖ := one_mul _
    _ ≤ ‖(t.q : K)‖ := t.norm_eisenstein_le 3

/-- **Integrality of `a₆`.** For `(12 : K) ≠ 0` the Tate coefficient
`a₆(q) = -(5 s₃(q) + 7 s₅(q))/12` has norm `< 1`, so it too reduces to `0` in the residue field.
This is the strict form of `A6Series.norm_a₆_le`. -/
lemma norm_a₆_lt_one (h12 : (12 : K) ≠ 0) : ‖t.a₆‖ < 1 :=
  lt_of_le_of_lt (t.norm_a₆_le h12) t.norm_lt_one

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The `c₄`-invariant of the Tate curve is `c₄ = 1 - 48 a₄(q)` (from `b₂ = 1`, `b₄ = 2 a₄`). -/
lemma tateCurve_c₄ : t.tateCurve.c₄ = 1 - 48 * t.a₄ := by
  simp only [WeierstrassCurve.c₄, t.tateCurve_b₂, t.tateCurve_b₄]; ring

/-- **`c₄` is a unit of `𝒪`.** `‖c₄(E_q)‖ = 1`: since `‖48 a₄‖ ≤ ‖a₄‖ < 1 = ‖1‖`, the ultrametric
isosceles law gives `‖1 - 48 a₄‖ = 1`. Thus `c₄` reduces to a *nonzero* element of the residue
field — the node of the special fiber is multiplicative (not a cusp). Unconditional. -/
lemma norm_c₄_eq_one : ‖t.tateCurve.c₄‖ = 1 := by
  have hlt : ‖(48 : K) * t.a₄‖ < 1 := by
    rw [norm_mul]
    calc ‖(48 : K)‖ * ‖t.a₄‖
        ≤ 1 * ‖t.a₄‖ := by gcongr; exact norm_ofNat_le_one (K := K) 48
      _ = ‖t.a₄‖ := one_mul _
      _ < 1 := t.norm_a₄_lt_one
  have hne : ‖(1 : K)‖ ≠ ‖-((48 : K) * t.a₄)‖ := by
    rw [norm_neg, norm_one]; exact (ne_of_lt hlt).symm
  rw [t.tateCurve_c₄, sub_eq_add_neg,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne,
    norm_neg, norm_one, max_eq_left hlt.le]

/-- **The discriminant reduces to `0`.** `‖Δ(E_q)‖ < 1`: expanding
`Δ = -a₆ + a₄² - 64 a₄³ - 432 a₆² + 72 a₄ a₆` (`Discriminant.tateCurve_Δ_eq`), each term has norm
`< 1` because `‖a₄‖, ‖a₆‖ < 1` and the integer coefficients have norm `≤ 1`; the ultrametric bound
then gives `‖Δ‖ < 1`. Needs only `(12:K) ≠ 0`. -/
lemma norm_Δ_lt_one (h12 : (12 : K) ≠ 0) : ‖t.tateCurve.Δ‖ < 1 := by
  have ha₄ := t.norm_a₄_lt_one
  have ha₆ := t.norm_a₆_lt_one h12
  have hrw : t.tateCurve.Δ
      = -t.a₆ + t.a₄ ^ 2 + (-64) * t.a₄ ^ 3 + (-432) * t.a₆ ^ 2 + 72 * t.a₄ * t.a₆ := by
    rw [t.tateCurve_Δ_eq]; ring
  rw [hrw]
  have b1 : ‖-t.a₆‖ < 1 := by rw [norm_neg]; exact ha₆
  have b2 : ‖t.a₄ ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) ha₄ two_ne_zero
  have b3 : ‖(-64 : K) * t.a₄ ^ 3‖ < 1 := by
    rw [norm_mul, norm_neg, norm_pow]
    calc ‖(64 : K)‖ * ‖t.a₄‖ ^ 3
        ≤ 1 * ‖t.a₄‖ ^ 3 := by gcongr; exact norm_ofNat_le_one (K := K) 64
      _ = ‖t.a₄‖ ^ 3 := one_mul _
      _ < 1 := pow_lt_one₀ (norm_nonneg _) ha₄ three_ne_zero
  have b4 : ‖(-432 : K) * t.a₆ ^ 2‖ < 1 := by
    rw [norm_mul, norm_neg, norm_pow]
    calc ‖(432 : K)‖ * ‖t.a₆‖ ^ 2
        ≤ 1 * ‖t.a₆‖ ^ 2 := by gcongr; exact norm_ofNat_le_one (K := K) 432
      _ = ‖t.a₆‖ ^ 2 := one_mul _
      _ < 1 := pow_lt_one₀ (norm_nonneg _) ha₆ two_ne_zero
  have b5 : ‖(72 : K) * t.a₄ * t.a₆‖ < 1 := by
    rw [norm_mul, norm_mul]
    calc ‖(72 : K)‖ * ‖t.a₄‖ * ‖t.a₆‖
        ≤ 1 * ‖t.a₄‖ * ‖t.a₆‖ := by gcongr; exact norm_ofNat_le_one (K := K) 72
      _ = ‖t.a₄‖ * ‖t.a₆‖ := by rw [one_mul]
      _ ≤ ‖t.a₄‖ * 1 := mul_le_mul_of_nonneg_left ha₆.le (norm_nonneg _)
      _ = ‖t.a₄‖ := mul_one _
      _ < 1 := ha₄
  refine ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt
    ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt
      ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt
        ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt b1 b2)) b3)) b4)) b5))

/-- **Multiplicative reduction of the Tate curve.** The invariant-level criterion: over the
valuation ring `𝒪` the discriminant reduces to `0` (`‖Δ‖ < 1`, singular special fiber) while `c₄`
reduces to a nonzero element (`‖c₄‖ = 1`). The singularity is therefore a *node* — the reduction is
multiplicative, not additive (`(12:K) ≠ 0`). -/
theorem tateCurve_multiplicative_reduction (h12 : (12 : K) ≠ 0) :
    ‖t.tateCurve.c₄‖ = 1 ∧ ‖t.tateCurve.Δ‖ < 1 :=
  ⟨t.norm_c₄_eq_one, t.norm_Δ_lt_one h12⟩

end Nonarchimedean

end TateParameter

/-- The **nodal cubic** `y² + x y = x³` — the special fiber of the Tate curve modulo the maximal
ideal. Since `‖a₄(q)‖, ‖a₆(q)‖ < 1`, the reduction of `E_q` has `a₄ ≡ a₆ ≡ 0` and is exactly this
curve. -/
def nodalCubic (R : Type*) [CommRing R] : WeierstrassCurve R where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 0

@[simp] lemma nodalCubic_a₁ (R : Type*) [CommRing R] : (nodalCubic R).a₁ = 1 := rfl
@[simp] lemma nodalCubic_a₂ (R : Type*) [CommRing R] : (nodalCubic R).a₂ = 0 := rfl
@[simp] lemma nodalCubic_a₃ (R : Type*) [CommRing R] : (nodalCubic R).a₃ = 0 := rfl
@[simp] lemma nodalCubic_a₄ (R : Type*) [CommRing R] : (nodalCubic R).a₄ = 0 := rfl
@[simp] lemma nodalCubic_a₆ (R : Type*) [CommRing R] : (nodalCubic R).a₆ = 0 := rfl

/-- The special fiber is **singular**: its discriminant vanishes, so `E_q` has (potentially)
multiplicative — not good — reduction. -/
lemma nodalCubic_Δ (R : Type*) [CommRing R] : (nodalCubic R).Δ = 0 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, nodalCubic_a₁, nodalCubic_a₂, nodalCubic_a₃, nodalCubic_a₄, nodalCubic_a₆]
  ring

/-- **Split multiplicative reduction.** The tangent cone of the node at `(0,0)` — the lowest-degree
part `y² + x y` of the affine equation `y² + x y - x³` — factors over the base ring into the two
distinct *rational* tangent lines `y = 0` and `y = -x`. Rationality of the two branches is exactly
the statement that the multiplicative reduction is **split**. -/
lemma nodalCubic_tangentCone (R : Type*) [CommRing R] (x y : R) :
    y ^ 2 + x * y = y * (y + x) := by ring

end TateCurvesTheta
