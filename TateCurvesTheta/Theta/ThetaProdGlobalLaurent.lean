/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import TateCurvesTheta.Theta.FactorSeries
import TateCurvesTheta.Theta.ThetaProdLaurent

/-!
# `thetaProd` is a global two-sided Laurent series (the rigid-analytic core of `theta = thetaProd`)

For a Tate parameter `q` over a complete nonarchimedean field `K` (`0 < ‖q‖ < 1`), the product form
`thetaProd` (`Theta/Product.lean`) factors through the elementary factor `thetaProdFactor`:
```
thetaProd u = thetaProdFactor(-q) · thetaProdFactor(q·u) · thetaProdFactor(u⁻¹).
```
The Euler `q`-binomial expansion (`Theta/FactorSeries.lean`) develops each `thetaProdFactor` as a
convergent power series `thetaProdFactor c = ∑' k, E k · cᵏ`, with **super-geometrically decaying**
coefficients `‖E k‖ = ‖q‖^{k(k-1)/2}`. Consequently:

* `A(u) := thetaProdFactor(q·u) = ∑' k, (E k qᵏ) uᵏ` is an everywhere-convergent power series
  in `u`;
* `B(u) := thetaProdFactor(u⁻¹) = ∑' k, E k u⁻ᵏ` is an everywhere-convergent power series in
  `u⁻¹`.

Their product is a *global* two-sided Laurent series: writing the coefficient families as
`ℤ`-indexed families supported on `ℕ` and `-ℕ` respectively, the nonarchimedean Cauchy product
(`HasSum.mul_of_nonarchimedean`, `Mathlib/Topology/Algebra/InfiniteSum/Nonarchimedean.lean`)
followed by a shear reindexing `(n, m) ↦ (n + m, m)` on `ℤ × ℤ` and a fibrewise sum
(`HasSum.prod_fiberwise`) yields coefficients
```
bₗ = thetaProdFactor(-q) · ∑' m, aLaurentCoeff(ℓ - m) · bLaurentCoeff(m)
```
with `∀ u, Summable (ℓ ↦ bₗ uˡ)` and `∀ u, thetaProd u = ∑' ℓ, bₗ uˡ`. This is exactly the seam
`TateParameter.ThetaProdLaurentRepr` (`Theta/ThetaProdLaurent.lean`).

The point is that *no norm estimate on the Laurent coefficients is needed*: global convergence is
inherited from the two everywhere-convergent one-sided series through the ultrametric Cauchy
product, sidestepping the obstruction diagnosed for the `RatioLaurentRepr` route (whose honest
coefficients do not decay as `n → -∞`). This discharges the rigid-analytic core of the Jacobi
triple product identity.

## Main results

* `TateParameter.hasSum_laurentConvolution` : the reusable nonarchimedean Cauchy product of a power
  series in `u` and a power series in `u⁻¹` as a global two-sided Laurent series (the same shape is
  what the Weierstrass-defect development of #146 reduces to).
* `TateParameter.thetaProdLaurentRepr` : `thetaProd` admits a global two-sided Laurent expansion,
  i.e. the seam `ThetaProdLaurentRepr t` holds unconditionally.
* `TateParameter.thetaProd_eq_const_mul_theta_of_laurentCoeffUnique` : consequently, given only the
  Laurent coefficient uniqueness principle `LaurentCoeffUnique K`, there is a constant `b₀` with
  `thetaProd u = b₀ · theta u` for every `u`.
* `TateParameter.theta_eq_thetaProd_of_laurentCoeffUnique` : with, in addition, one normalization
  value `theta u₀ = thetaProd u₀ ≠ 0`, the Jacobi triple product identity `theta = thetaProd`. All
  rigid-analytic content is now discharged; the sole remaining obligation is the scalar
  normalization `b₀ = 1`.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* G. E. Andrews, R. Askey, R. Roy, *Special Functions*, §10.4 (Jacobi triple product).
* A. Robert, *A Course in p-adic Analysis*, §6 (convergent Laurent series on annuli).
-/

open scoped Topology

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-- A ultrametric normed field is a nonarchimedean ring: the open balls at `0` are additive
subgroups, so every neighbourhood of `0` contains an open additive subgroup. This equips `K` with
the ultrametric Cauchy product `HasSum.mul_of_nonarchimedean`. -/
instance (priority := 100) instNonarchimedeanRingOfUltrametric : NonarchimedeanRing K where
  toIsTopologicalRing := inferInstance
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

/-- The `ℤ`-indexed coefficient family of `A(u) = thetaProdFactor(q·u)`, supported on `n ≥ 0`,
where the coefficient of `uⁿ` is the Euler `q`-binomial coefficient `E n` times `qⁿ`. -/
noncomputable def aLaurentCoeff (n : ℤ) : K :=
  if 0 ≤ n then factorCoeff t n.toNat * (t.q : K) ^ n.toNat else 0

/-- The `ℤ`-indexed coefficient family of `B(u) = thetaProdFactor(u⁻¹)`, supported on `m ≤ 0`,
where the coefficient of `uᵐ` is the Euler `q`-binomial coefficient `E (-m)`. -/
noncomputable def bLaurentCoeff (m : ℤ) : K :=
  if m ≤ 0 then factorCoeff t (-m).toNat else 0

omit [CompleteSpace K] [IsUltrametricDist K] in
@[simp] lemma aLaurentCoeff_natCast (k : ℕ) :
    t.aLaurentCoeff k = factorCoeff t k * (t.q : K) ^ k := by
  simp [aLaurentCoeff]

omit [CompleteSpace K] [IsUltrametricDist K] in
@[simp] lemma bLaurentCoeff_negNatCast (k : ℕ) :
    t.bLaurentCoeff (-(k : ℤ)) = factorCoeff t k := by
  simp [bLaurentCoeff]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- `aLaurentCoeff` vanishes on negative indices. -/
lemma aLaurentCoeff_of_neg {n : ℤ} (hn : n < 0) : t.aLaurentCoeff n = 0 := by
  simp [aLaurentCoeff, not_le.mpr hn]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- `bLaurentCoeff` vanishes on positive indices. -/
lemma bLaurentCoeff_of_pos {m : ℤ} (hm : 0 < m) : t.bLaurentCoeff m = 0 := by
  simp [bLaurentCoeff, not_le.mpr hm]

/-- The coefficient family of `A` is summable (the power series `A` converges everywhere). -/
lemma summable_aLaurentCoeff : Summable t.aLaurentCoeff := by
  rw [← (Nat.cast_injective (R := ℤ)).summable_iff (f := t.aLaurentCoeff) (fun n hn => ?_)]
  · exact (t.factorCoeff_summable (t.q : K)).congr fun k => by simp
  · rw [Set.mem_range] at hn
    have hneg : n < 0 := by
      by_contra h
      exact hn ⟨n.toNat, by simp [Int.toNat_of_nonneg (not_lt.mp h)]⟩
    exact t.aLaurentCoeff_of_neg hneg

/-- The coefficient family of `B` is summable (the power series `B` converges everywhere). -/
lemma summable_bLaurentCoeff : Summable t.bLaurentCoeff := by
  have hinj : Function.Injective (fun k : ℕ => -(k : ℤ)) := fun a b h => by simpa using h
  rw [← hinj.summable_iff (f := t.bLaurentCoeff) (fun m hm => ?_)]
  · exact (t.factorCoeff_summable (1 : K)).congr fun k => by simp
  · rw [Set.mem_range] at hm
    have hpos : 0 < m := by
      by_contra h
      exact hm ⟨(-m).toNat, by simp [Int.toNat_of_nonneg (neg_nonneg.mpr (not_lt.mp h))]⟩
    exact t.bLaurentCoeff_of_pos hpos

/-- `A(u) = thetaProdFactor(q·u)` as a two-sided Laurent series with coefficients
`aLaurentCoeff`. -/
lemma aLaurentCoeff_hasSum (u : Kˣ) :
    HasSum (fun n : ℤ => t.aLaurentCoeff n * (u : K) ^ n)
      (t.thetaProdFactor ((t.q : K) * (u : K))) := by
  have hnat : HasSum (fun k : ℕ => factorCoeff t k * ((t.q : K) * (u : K)) ^ k)
      (t.thetaProdFactor ((t.q : K) * (u : K))) := by
    rw [thetaProdFactor_eq_tsum]; exact (t.factorCoeff_summable _).hasSum
  have hoff : ∀ n : ℤ, n ∉ Set.range ((↑) : ℕ → ℤ) →
      t.aLaurentCoeff n * (u : K) ^ n = 0 := by
    intro n hn
    rw [Set.mem_range] at hn
    have hneg : n < 0 := by
      by_contra h
      exact hn ⟨n.toNat, by simp [Int.toNat_of_nonneg (not_lt.mp h)]⟩
    simp [t.aLaurentCoeff_of_neg hneg]
  have hcomp : ((fun n : ℤ => t.aLaurentCoeff n * (u : K) ^ n) ∘ ((↑) : ℕ → ℤ))
      = fun k : ℕ => factorCoeff t k * ((t.q : K) * (u : K)) ^ k := by
    funext k
    simp only [Function.comp_apply, aLaurentCoeff_natCast, zpow_natCast, mul_pow]
    ring
  rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff
      (f := fun n : ℤ => t.aLaurentCoeff n * (u : K) ^ n) hoff, hcomp]
  exact hnat

/-- `B(u) = thetaProdFactor(u⁻¹)` as a two-sided Laurent series with coefficients
`bLaurentCoeff`. -/
lemma bLaurentCoeff_hasSum (u : Kˣ) :
    HasSum (fun m : ℤ => t.bLaurentCoeff m * (u : K) ^ m)
      (t.thetaProdFactor ((u : K)⁻¹)) := by
  have hnat : HasSum (fun k : ℕ => factorCoeff t k * ((u : K)⁻¹) ^ k)
      (t.thetaProdFactor ((u : K)⁻¹)) := by
    rw [thetaProdFactor_eq_tsum]; exact (t.factorCoeff_summable _).hasSum
  have hinj : Function.Injective (fun k : ℕ => -(k : ℤ)) := fun a b h => by simpa using h
  have hoff : ∀ m : ℤ, m ∉ Set.range (fun k : ℕ => -(k : ℤ)) →
      t.bLaurentCoeff m * (u : K) ^ m = 0 := by
    intro m hm
    rw [Set.mem_range] at hm
    have hpos : 0 < m := by
      by_contra h
      exact hm ⟨(-m).toNat, by simp [Int.toNat_of_nonneg (neg_nonneg.mpr (not_lt.mp h))]⟩
    simp [t.bLaurentCoeff_of_pos hpos]
  have hcomp : ((fun m : ℤ => t.bLaurentCoeff m * (u : K) ^ m) ∘ (fun k : ℕ => -(k : ℤ)))
      = fun k : ℕ => factorCoeff t k * ((u : K)⁻¹) ^ k := by
    funext k
    simp only [Function.comp_apply, bLaurentCoeff_negNatCast, zpow_neg, zpow_natCast, inv_pow]
  rw [← hinj.hasSum_iff (f := fun m : ℤ => t.bLaurentCoeff m * (u : K) ^ m) hoff, hcomp]
  exact hnat

/-- The global two-sided Laurent coefficients of `thetaProd`: the constant `thetaProdFactor(-q)`
times the nonarchimedean convolution of the `A`- and `B`-coefficient families. -/
noncomputable def thetaProdLaurentCoeff (ℓ : ℤ) : K :=
  t.thetaProdFactor (-(t.q : K)) *
    ∑' m : ℤ, t.aLaurentCoeff (ℓ - m) * t.bLaurentCoeff m

/-- **Nonarchimedean Cauchy product of a power series and a reverse power series.** Over a complete
nonarchimedean field, if `∑' n, αₙ uⁿ = A` and `∑' m, βₘ uᵐ = B` are two convergent two-sided
series (typically `α` supported on `ℕ` and `β` on `-ℕ`, i.e. a power series in `u` and one in
`u⁻¹`), then their product is the convergent Laurent series with convolution coefficients
`ℓ ↦ ∑' m, α(ℓ - m)·βₘ`. The proof is the ultrametric Cauchy product `HasSum.mul_of_nonarchimedean`
reindexed by the shear `(n, m) ↦ (n + m, m)` on `ℤ × ℤ`, summed over the fibres `n + m = ℓ`;
no norm estimate on the resulting coefficients is required. -/
lemma hasSum_laurentConvolution {α β : ℤ → K} {A B : K} (u : Kˣ)
    (hA : HasSum (fun n : ℤ => α n * (u : K) ^ n) A)
    (hB : HasSum (fun m : ℤ => β m * (u : K) ^ m) B) :
    HasSum (fun ℓ : ℤ => (∑' m : ℤ, α (ℓ - m) * β m) * (u : K) ^ ℓ) (A * B) := by
  have hAB := hA.mul_of_nonarchimedean hB
  -- Shear `(ℓ, m) ↦ (ℓ - m, m)` on `ℤ × ℤ`, so the new first coordinate is `n + m`.
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1 - p.2, p.2)
      invFun := fun p => (p.1 + p.2, p.2)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have hshear : HasSum
      (fun p : ℤ × ℤ => (α (p.1 - p.2) * (u : K) ^ (p.1 - p.2)) * (β p.2 * (u : K) ^ p.2))
      (A * B) :=
    (e.hasSum_iff (f := fun p : ℤ × ℤ =>
      (α p.1 * (u : K) ^ p.1) * (β p.2 * (u : K) ^ p.2))).mpr hAB
  refine hshear.prod_fiberwise (fun ℓ => ?_)
  -- The `ℓ`-fibre, after collapsing `u^{ℓ-m}·u^m = u^ℓ`.
  have hfun : (fun m : ℤ => (α (ℓ - m) * (u : K) ^ (ℓ - m)) * (β m * (u : K) ^ m))
      = fun m : ℤ => (α (ℓ - m) * β m) * (u : K) ^ ℓ := by
    funext m
    have hexp : ℓ - m + m = ℓ := by ring
    rw [mul_mul_mul_comm, ← zpow_add₀ u.ne_zero, hexp]
  -- Fibrewise summability, obtained by slicing the (summable) sheared product family.
  have hslice : Summable (fun m : ℤ =>
      (α (ℓ - m) * (u : K) ^ (ℓ - m)) * (β m * (u : K) ^ m)) := by
    have hinj : Function.Injective (fun m : ℤ => ((ℓ, m) : ℤ × ℤ)) :=
      fun a b h => by simpa using congrArg Prod.snd h
    simpa only [Function.comp_def] using hshear.summable.comp_injective hinj
  have hconv : Summable (fun m : ℤ => α (ℓ - m) * β m) := by
    refine ((hfun ▸ hslice).mul_right ((u : K) ^ ℓ)⁻¹).congr fun m => ?_
    rw [mul_assoc, mul_inv_cancel₀ (zpow_ne_zero ℓ u.ne_zero), mul_one]
  have hfiber := hconv.hasSum.mul_right ((u : K) ^ ℓ)
  rwa [← hfun] at hfiber

/-- **`thetaProd` develops as a global two-sided Laurent series.** For every unit `u`,
`thetaProd u = ∑' ℓ, thetaProdLaurentCoeff ℓ · uˡ`, and the family is summable. This is the
nonarchimedean Cauchy product of the everywhere-convergent power series
`A(u) = thetaProdFactor(q·u)` and `B(u) = thetaProdFactor(u⁻¹)`, restored by the constant factor
`thetaProdFactor(-q)`. -/
lemma thetaProd_hasSum_laurent (u : Kˣ) :
    HasSum (fun ℓ : ℤ => t.thetaProdLaurentCoeff ℓ * (u : K) ^ ℓ) (t.thetaProd u) := by
  have h := hasSum_laurentConvolution u (t.aLaurentCoeff_hasSum u) (t.bLaurentCoeff_hasSum u)
  have hval : t.thetaProdFactor (-(t.q : K)) *
      (t.thetaProdFactor ((t.q : K) * (u : K)) * t.thetaProdFactor ((u : K)⁻¹))
      = t.thetaProd u := by
    rw [thetaProd_apply]; ring
  have hfinal := h.mul_left (t.thetaProdFactor (-(t.q : K)))
  rw [hval] at hfinal
  have hcoeffun : (fun ℓ : ℤ => t.thetaProdLaurentCoeff ℓ * (u : K) ^ ℓ)
      = fun ℓ : ℤ => t.thetaProdFactor (-(t.q : K)) *
          ((∑' m : ℤ, t.aLaurentCoeff (ℓ - m) * t.bLaurentCoeff m) * (u : K) ^ ℓ) := by
    funext ℓ; rw [thetaProdLaurentCoeff]; ring
  rw [hcoeffun]
  exact hfinal

/-- **The rigid-analytic core of `theta = thetaProd`.** The product form `thetaProd` admits a
global two-sided Laurent expansion; equivalently, the seam `ThetaProdLaurentRepr t`
(`Theta/ThetaProdLaurent.lean`) holds unconditionally over any complete nonarchimedean field. -/
theorem thetaProdLaurentRepr : t.ThetaProdLaurentRepr :=
  ⟨t.thetaProdLaurentCoeff,
    fun u => (t.thetaProd_hasSum_laurent u).summable,
    fun u => (t.thetaProd_hasSum_laurent u).tsum_eq.symm⟩

/-- **`thetaProd` is a constant multiple of `theta`, unconditionally in the Laurent expansion.**
Combining the global Laurent expansion `thetaProdLaurentRepr` with the Laurent coefficient
uniqueness principle `LaurentCoeffUnique K`, there is a constant `b₀` with
`thetaProd u = b₀ · theta u` for every `u`. The only remaining input for the full Jacobi triple
product `theta = thetaProd` is the scalar normalization `b₀ = 1` (equivalently, one `u₀` with
`theta u₀ = thetaProd u₀ ≠ 0`). -/
theorem thetaProd_eq_const_mul_theta_of_laurentCoeffUnique (huniq : LaurentCoeffUnique K) :
    ∃ b₀ : K, ∀ u : Kˣ, t.thetaProd u = b₀ * t.theta u :=
  t.thetaProd_eq_const_mul_theta huniq t.thetaProdLaurentRepr

/-- **The Jacobi triple product identity `theta = thetaProd`, given only `LaurentCoeffUnique` and
one normalization value.** With the global Laurent expansion of `thetaProd` now unconditional
(`thetaProdLaurentRepr`), all rigid-analytic content is discharged: the identity `theta = thetaProd`
follows from the Laurent coefficient uniqueness principle together with a single point `u₀` where
`theta u₀ = thetaProd u₀ ≠ 0` (which pins the constant `b₀` of
`thetaProd_eq_const_mul_theta_of_laurentCoeffUnique` to `1`). This is the wiring of
`theta_eq_thetaProd_of_thetaProdLaurent` through the unconditional seam. -/
theorem theta_eq_thetaProd_of_laurentCoeffUnique (huniq : LaurentCoeffUnique K) {u₀ : Kˣ}
    (hu₀ : t.theta u₀ ≠ 0) (hnorm : t.theta u₀ = t.thetaProd u₀) (u : Kˣ) :
    t.theta u = t.thetaProd u :=
  t.theta_eq_thetaProd_of_thetaProdLaurent huniq t.thetaProdLaurentRepr hu₀ hnorm u

end TateParameter

end TateCurvesTheta
