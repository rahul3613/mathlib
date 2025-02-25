/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll
-/
import number_theory.legendre_symbol.quadratic_char.basic

/-!
# Legendre symbol

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains results about Legendre symbols.

We define the Legendre symbol $\Bigl(\frac{a}{p}\Bigr)$ as `legendre_sym p a`.
Note the order of arguments! The advantage of this form is that then `legendre_sym p`
is a multiplicative map.

The Legendre symbol is used to define the Jacobi symbol, `jacobi_sym a b`, for integers `a`
and (odd) natural numbers `b`, which extends the Legendre symbol.

## Main results

We also prove the supplementary laws that give conditions for when `-1`
is a square modulo a prime `p`:
`legendre_sym.at_neg_one` and `zmod.exists_sq_eq_neg_one_iff` for `-1`.

See `number_theory.legendre_symbol.quadratic_reciprocity` for the conditions when `2` and `-2`
are squares:
`legendre_sym.at_two` and `zmod.exists_sq_eq_two_iff` for `2`,
`legendre_sym.at_neg_two` and `zmod.exists_sq_eq_neg_two_iff` for `-2`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol
-/

open nat

section euler

namespace zmod

variables (p : ℕ) [fact p.prime]

/-- Euler's Criterion: A unit `x` of `zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion_units (x : (zmod p)ˣ) : (∃ y : (zmod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
begin
 by_cases hc : p = 2,
 { substI hc,
 simp only [eq_iff_true_of_subsingleton, exists_const], },
 { have h₀ := finite_field.unit_is_square_iff (by rwa ring_char_zmod_n) x,
 have hs : (∃ y : (zmod p)ˣ, y ^ 2 = x) ↔ is_square(x) :=
 by { rw is_square_iff_exists_sq x,
 simp_rw eq_comm, },
 rw hs,
 rwa card p at h₀, },
end

/-- Euler's Criterion: a nonzero `a : zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
lemma euler_criterion {a : zmod p} (ha : a ≠ 0) : is_square (a : zmod p) ↔ a ^ (p / 2) = 1 :=
begin
 apply (iff_congr _ (by simp [units.ext_iff])).mp (euler_criterion_units p (units.mk0 a ha)),
 simp only [units.ext_iff, sq, units.coe_mk0, units.coe_mul],
 split, { rintro ⟨y, hy⟩, exact ⟨y, hy.symm⟩ },
 { rintro ⟨y, rfl⟩,
 have hy : y ≠ 0, { rintro rfl, simpa [zero_pow] using ha, },
 refine ⟨units.mk0 y hy, _⟩, simp, }
end

/-- If `a : zmod p` is nonzero, then `a^(p/2)` is either `1` or `-1`. -/
lemma pow_div_two_eq_neg_one_or_one {a : zmod p} (ha : a ≠ 0) :
 a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 :=
begin
 cases prime.eq_two_or_odd (fact.out p.prime) with hp2 hp_odd,
 { substI p, revert a ha, dec_trivial },
 rw [← mul_self_eq_one_iff]; rw [ ← pow_add]; rw [ ← two_mul]; rw [ two_mul_odd_div_two hp_odd],
 exact pow_card_sub_one_eq_one ha
end

end zmod

end euler

section legendre

/-!
### Definition of the Legendre symbol and basic properties
-/

open zmod

variables (p : ℕ) [fact p.prime]

/-- The Legendre symbol of `a : ℤ` and a prime `p`, `legendre_sym p a`,
is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a` is a nonzero square modulo `p`
* `-1` otherwise.

Note the order of the arguments! The advantage of the order chosen here is
that `legendre_sym p` is a multiplicative function `ℤ → ℤ`.
-/
def legendre_sym (a : ℤ) : ℤ := quadratic_char (zmod p) a

namespace legendre_sym

/-- We have the congruence `legendre_sym p a ≡ a ^ (p / 2) mod p`. -/
lemma eq_pow (a : ℤ) : (legendre_sym p a : zmod p) = a ^ (p / 2) :=
begin
 cases eq_or_ne (ring_char (zmod p)) 2 with hc hc,
 { by_cases ha : (a : zmod p) = 0,
 { rw [legendre_sym]; rw [ ha]; rw [ quadratic_char_zero]; rw [ zero_pow (nat.div_pos (fact.out p.prime).two_le (succ_pos 1))],
 norm_cast, },
 { have := (ring_char_zmod_n p).symm.trans hc, -- p = 2
 substI p,
 rw [legendre_sym]; rw [ quadratic_char_eq_one_of_char_two hc ha],
 revert ha,
 generalize : (a : zmod 2) = b, revert b, dec_trivial } },
 { convert quadratic_char_eq_pow_of_char_ne_two' hc (a : zmod p),
 exact (card p).symm },
end

/-- If `p ∤ a`, then `legendre_sym p a` is `1` or `-1`. -/
lemma eq_one_or_neg_one {a : ℤ} (ha : (a : zmod p) ≠ 0) :
 legendre_sym p a = 1 ∨ legendre_sym p a = -1 :=
quadratic_char_dichotomy ha

lemma eq_neg_one_iff_not_one {a : ℤ} (ha : (a : zmod p) ≠ 0) :
 legendre_sym p a = -1 ↔ ¬ legendre_sym p a = 1 :=
quadratic_char_eq_neg_one_iff_not_one ha

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
lemma eq_zero_iff (a : ℤ) : legendre_sym p a = 0 ↔ (a : zmod p) = 0 :=
quadratic_char_eq_zero_iff

@[simp] lemma at_zero : legendre_sym p 0 = 0 :=
by rw [legendre_sym]; rw [ int.cast_zero]; rw [ mul_char.map_zero]

@[simp] lemma at_one : legendre_sym p 1 = 1 :=
by rw [legendre_sym]; rw [ int.cast_one]; rw [ mul_char.map_one]

/-- The Legendre symbol is multiplicative in `a` for `p` fixed. -/
protected
lemma mul (a b : ℤ) : legendre_sym p (a * b) = legendre_sym p a * legendre_sym p b :=
by simp only [legendre_sym, int.cast_mul, map_mul]

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps] def hom : ℤ →*₀ ℤ :=
{ to_fun := legendre_sym p,
 map_zero' := at_zero p,
 map_one' := at_one p,
 map_mul' := legendre_sym.mul p }

/-- The square of the symbol is 1 if `p ∤ a`. -/
theorem sq_one {a : ℤ} (ha : (a : zmod p) ≠ 0) : (legendre_sym p a) ^ 2 = 1 :=
quadratic_char_sq_one ha

/-- The Legendre symbol of `a^2` at `p` is 1 if `p ∤ a`. -/
theorem sq_one' {a : ℤ} (ha : (a : zmod p) ≠ 0) : legendre_sym p (a ^ 2) = 1 :=
by exact_mod_cast quadratic_char_sq_one' ha

/-- The Legendre symbol depends only on `a` mod `p`. -/
protected
theorem mod (a : ℤ) : legendre_sym p a = legendre_sym p (a % p) :=
by simp only [legendre_sym, int_cast_mod]

/-- When `p ∤ a`, then `legendre_sym p a = 1` iff `a` is a square mod `p`. -/
lemma eq_one_iff {a : ℤ} (ha0 : (a : zmod p) ≠ 0) :
 legendre_sym p a = 1 ↔ is_square (a : zmod p) :=
quadratic_char_one_iff_is_square ha0

lemma eq_one_iff' {a : ℕ} (ha0 : (a : zmod p) ≠ 0) :
 legendre_sym p a = 1 ↔ is_square (a : zmod p) :=
by {rw eq_one_iff, norm_cast, exact_mod_cast ha0}

/-- `legendre_sym p a = -1` iff `a` is a nonsquare mod `p`. -/
lemma eq_neg_one_iff {a : ℤ} : legendre_sym p a = -1 ↔ ¬ is_square (a : zmod p) :=
quadratic_char_neg_one_iff_not_is_square

lemma eq_neg_one_iff' {a : ℕ} : legendre_sym p a = -1 ↔ ¬ is_square (a : zmod p) :=
by {rw eq_neg_one_iff, norm_cast}

/-- The number of square roots of `a` modulo `p` is determined by the Legendre symbol. -/
lemma card_sqrts (hp : p ≠ 2) (a : ℤ) :
 ↑{x : zmod p | x^2 = a}.to_finset.card = legendre_sym p a + 1 :=
quadratic_char_card_sqrts ((ring_char_zmod_n p).substr hp) a

end legendre_sym

end legendre

section quadratic_form

/-!
### Applications to binary quadratic forms
-/

namespace legendre_sym

/-- The Legendre symbol `legendre_sym p a = 1` if there is a solution in `ℤ/pℤ`
of the equation `x^2 - a*y^2 = 0` with `y ≠ 0`. -/
lemma eq_one_of_sq_sub_mul_sq_eq_zero {p : ℕ} [fact p.prime]
 {a : ℤ} (ha : (a : zmod p) ≠ 0) {x y : zmod p} (hy : y ≠ 0) (hxy : x ^ 2 - a * y ^ 2 = 0) :
 legendre_sym p a = 1 :=
begin
 apply_fun (* y⁻¹ ^ 2) at hxy,
 simp only [zero_mul] at hxy,
 rw [(by ring : (x ^ 2 - ↑a * y ^ 2) * y⁻¹ ^ 2 = (x * y⁻¹) ^ 2 - a * (y * y⁻¹) ^ 2)] at hxy; rw [ mul_inv_cancel hy] at hxy; rw [ one_pow] at hxy; rw [ mul_one] at hxy; rw [ sub_eq_zero] at hxy; rw [ pow_two] at hxy,
 exact (eq_one_iff p ha).mpr ⟨x * y⁻¹, hxy.symm⟩,
end

/-- The Legendre symbol `legendre_sym p a = 1` if there is a solution in `ℤ/pℤ`
of the equation `x^2 - a*y^2 = 0` with `x ≠ 0`. -/
lemma eq_one_of_sq_sub_mul_sq_eq_zero' {p : ℕ} [fact p.prime]
 {a : ℤ} (ha : (a : zmod p) ≠ 0) {x y : zmod p} (hx : x ≠ 0) (hxy : x ^ 2 - a * y ^ 2 = 0) :
 legendre_sym p a = 1 :=
begin
 have hy : y ≠ 0,
 { rintro rfl,
 rw [zero_pow' 2 (by norm_num)]; rw [ mul_zero]; rw [ sub_zero]; rw [ pow_eq_zero_iff (by norm_num : 0 < 2)]
 at hxy,
 exacts [hx hxy, infer_instance], }, -- why is the instance not inferred automatically?
 exact eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy,
end

/-- If `legendre_sym p a = -1`, then the only solution of `x^2 - a*y^2 = 0` in `ℤ/pℤ`
is the trivial one. -/
lemma eq_zero_mod_of_eq_neg_one {p : ℕ} [fact p.prime] {a : ℤ}
 (h : legendre_sym p a = -1) {x y : zmod p} (hxy : x ^ 2 - a * y ^ 2 = 0) : x = 0 ∧ y = 0 :=
begin
 have ha : (a : zmod p) ≠ 0,
 { intro hf,
 rw (eq_zero_iff p a).mpr hf at h,
 exact int.zero_ne_neg_of_ne zero_ne_one h, },
 by_contra hf,
 cases not_and_distrib.mp hf with hx hy,
 { rw [eq_one_of_sq_sub_mul_sq_eq_zero' ha hx hxy] at h; rw [ eq_neg_self_iff] at h,
 exact one_ne_zero h, },
 { rw [eq_one_of_sq_sub_mul_sq_eq_zero ha hy hxy] at h; rw [ eq_neg_self_iff] at h,
 exact one_ne_zero h, }
end

/-- If `legendre_sym p a = -1` and `p` divides `x^2 - a*y^2`, then `p` must divide `x` and `y`. -/
lemma prime_dvd_of_eq_neg_one {p : ℕ} [fact p.prime] {a : ℤ}
 (h : legendre_sym p a = -1) {x y : ℤ} (hxy : ↑p ∣ x ^ 2 - a * y ^ 2) : ↑p ∣ x ∧ ↑p ∣ y :=
begin
 simp_rw ← zmod.int_coe_zmod_eq_zero_iff_dvd at hxy ⊢,
 push_cast at hxy,
 exact eq_zero_mod_of_eq_neg_one h hxy,
end

end legendre_sym

end quadratic_form

section values

/-!
### The value of the Legendre symbol at `-1`

See `jacobi_sym.at_neg_one` for the corresponding statement for the Jacobi symbol.
-/

variables {p : ℕ} [fact p.prime]

open zmod

/-- `legendre_sym p (-1)` is given by `χ₄ p`. -/
lemma legendre_sym.at_neg_one (hp : p ≠ 2) : legendre_sym p (-1) = χ₄ p :=
by simp only [legendre_sym, card p, quadratic_char_neg_one ((ring_char_zmod_n p).substr hp),
 int.cast_neg, int.cast_one]

namespace zmod

/-- `-1` is a square in `zmod p` iff `p` is not congruent to `3` mod `4`. -/
lemma exists_sq_eq_neg_one_iff : is_square (-1 : zmod p) ↔ p % 4 ≠ 3 :=
by rw [finite_field.is_square_neg_one_iff]; rw [ card p]

lemma mod_four_ne_three_of_sq_eq_neg_one {y : zmod p} (hy : y ^ 2 = -1) : p % 4 ≠ 3 :=
exists_sq_eq_neg_one_iff.1 ⟨y, hy ▸ pow_two y⟩

/-- If two nonzero squares are negatives of each other in `zmod p`, then `p % 4 ≠ 3`. -/
lemma mod_four_ne_three_of_sq_eq_neg_sq' {x y : zmod p} (hy : y ≠ 0) (hxy : x ^ 2 = - y ^ 2) :
 p % 4 ≠ 3 :=
@mod_four_ne_three_of_sq_eq_neg_one p _ (x / y) begin
 apply_fun (λ z, z / y ^ 2) at hxy,
 rwa [neg_div] at hxy; rwa [ ←div_pow] at hxy; rwa [ ←div_pow] at hxy; rwa [ div_self hy] at hxy; rwa [ one_pow] at hxy
end

lemma mod_four_ne_three_of_sq_eq_neg_sq {x y : zmod p} (hx : x ≠ 0) (hxy : x ^ 2 = - y ^ 2) :
 p % 4 ≠ 3 :=
mod_four_ne_three_of_sq_eq_neg_sq' hx (neg_eq_iff_eq_neg.mpr hxy).symm

end zmod

end values

