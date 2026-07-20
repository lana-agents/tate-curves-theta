/-
Copyright (c) 2026 The tate-curves-theta contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The tate-curves-theta contributors
-/
import Mathlib.Data.Nat.Prime.Basic
import TateCurvesTheta.QParameter.Basic

/-!
# Coprimality to the order of the Tate `q`-parameter

Initial Θ-data (Mochizuki, *Inter-universal Teichmüller Theory I*, Definition 3.1(c))
requires a prime `ℓ` that is *prime to the order of the `q`-parameter*: the multiplicative
order datum attached to the Tate curve must be coprime to `ℓ`. This file isolates that
purely arithmetic condition.

The **order** meant here is the *discrete normalized additive valuation* of `q`, a positive
natural number: over a complete nonarchimedean field it equals the number of irreducible
components of the special fibre of the Tate curve `E_q`. The real-valued order
`TateParameter.ord` of `TateCurvesTheta.QParameter.Basic` refines to this integer once a
normalized additive valuation is fixed; that normalization is supplied by the shared
valuation infrastructure and is not yet available in this repository. Until then the
discrete order is carried as data on `OrderedTateParameter`, which is the seam where the
canonical value will later be plugged in.

## Main definitions

* `TateCurvesTheta.PrimeToOrder ℓ n`: the coprimality predicate `Nat.Coprime ℓ n`, read as
  "`ℓ` is prime to the order `n`". This is the reusable arithmetic core.
* `TateCurvesTheta.OrderedTateParameter K`: a `TateParameter` together with its discrete
  normalized order `orderNat` (a positive natural number).
* `OrderedTateParameter.PrimeToOrder`: the Θ-data condition for a Tate parameter, `ℓ`
  prime to its order.

## Main results

* `PrimeToOrder.prime_iff_not_dvd`: for a prime `ℓ`, prime-to-order is exactly `¬ ℓ ∣ n`,
  the nondegeneracy form used in the Θ-data hypotheses.
* `PrimeToOrder.of_dvd`: prime-to-order descends to divisors of the order.
* `OrderedTateParameter.primeToOrder_iff_not_dvd`: the same, phrased for a Tate parameter.

Decidability instances are provided so the condition can be checked on explicit data.

## References

* S. Mochizuki, *Inter-universal Teichmüller Theory I*, Definition 3.1(c).
* S. Mochizuki, *The Étale Theta Function and its Frobenioid-theoretic Manifestations*, §1.
-/

namespace TateCurvesTheta

/-- The **coprimality-to-order** condition: a natural number `ℓ` is *prime to the order*
`n` when it is coprime to `n`. Read `n` as the discrete normalized order of a Tate
parameter; this is the arithmetic condition appearing in initial Θ-data (IUT I,
Definition 3.1(c)). -/
def PrimeToOrder (ℓ n : ℕ) : Prop := Nat.Coprime ℓ n

namespace PrimeToOrder

variable {ℓ n : ℕ}

instance decidable (ℓ n : ℕ) : Decidable (PrimeToOrder ℓ n) :=
  inferInstanceAs (Decidable (Nat.Coprime ℓ n))

/-- Unfold the predicate to `Nat.Coprime`. -/
@[simp] theorem iff_coprime : PrimeToOrder ℓ n ↔ Nat.Coprime ℓ n := Iff.rfl

/-- Everything is prime to the order `1` (the degenerate, good-reduction end of the
convention). -/
theorem order_one : PrimeToOrder ℓ 1 := Nat.coprime_one_right ℓ

/-- `1` is prime to every order. -/
theorem one : PrimeToOrder 1 n := Nat.coprime_one_left n

/-- The condition is symmetric in its two arguments, as `Nat.Coprime`. -/
theorem symm (h : PrimeToOrder ℓ n) : PrimeToOrder n ℓ := Nat.Coprime.symm h

/-- For a prime `ℓ`, being prime to the order is exactly *not dividing* it: this is the
nondegeneracy form in which the Θ-data condition is checked. -/
theorem prime_iff_not_dvd (hℓ : ℓ.Prime) : PrimeToOrder ℓ n ↔ ¬ ℓ ∣ n :=
  hℓ.coprime_iff_not_dvd

/-- If `ℓ` is prime to the order `n`, it is prime to every divisor of `n`. -/
theorem of_dvd (h : PrimeToOrder ℓ n) {d : ℕ} (hd : d ∣ n) : PrimeToOrder ℓ d :=
  Nat.Coprime.coprime_dvd_right hd h

end PrimeToOrder

variable (K : Type*) [NormedField K]

/-- A **Tate parameter together with its discrete normalized order** `orderNat`.

`orderNat` is the positive-integer normalized additive valuation of `q` — over a complete
nonarchimedean field, the number of irreducible components of the special fibre of the Tate
curve `E_q`. It refines the real order `TateParameter.ord`. The canonical value is produced
by the shared normalized-valuation infrastructure, which is not yet available here, so it is
carried as data: this structure is the seam where that value will later be supplied. -/
structure OrderedTateParameter extends TateParameter K where
  /-- The discrete normalized order of the Tate parameter. -/
  orderNat : ℕ
  /-- A Tate parameter has `0 < ‖q‖ < 1`, so its normalized order is strictly positive. -/
  orderNat_pos : 0 < orderNat

namespace OrderedTateParameter

variable {K}
variable (t : OrderedTateParameter K)

/-- The **Θ-data condition** for a Tate parameter: `ℓ` is prime to the order of `t`. -/
def PrimeToOrder (ℓ : ℕ) : Prop := TateCurvesTheta.PrimeToOrder ℓ t.orderNat

instance decidable (ℓ : ℕ) : Decidable (t.PrimeToOrder ℓ) :=
  inferInstanceAs (Decidable (Nat.Coprime ℓ t.orderNat))

/-- Unfold the Θ-data condition to `Nat.Coprime`. -/
theorem primeToOrder_iff (ℓ : ℕ) : t.PrimeToOrder ℓ ↔ Nat.Coprime ℓ t.orderNat := Iff.rfl

/-- For a prime `ℓ`, the Θ-data condition is exactly that `ℓ` does not divide the order. -/
theorem primeToOrder_iff_not_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) :
    t.PrimeToOrder ℓ ↔ ¬ ℓ ∣ t.orderNat :=
  hℓ.coprime_iff_not_dvd

end OrderedTateParameter

end TateCurvesTheta
