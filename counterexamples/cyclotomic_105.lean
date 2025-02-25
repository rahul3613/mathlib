/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import ring_theory.polynomial.cyclotomic.basic

/-!
# Not all coefficients of cyclotomic polynomials are -1, 0, or 1

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that not all coefficients of cyclotomic polynomials are equal to `0`, `-1` or `1`, in the
theorem `not_forall_coeff_cyclotomic_neg_one_zero_one`. We prove this with the counterexample
`coeff_cyclotomic_105 : coeff (cyclotomic 105 ℤ) 7 = -2`.
-/

open nat (proper_divisors) finset

namespace counterexample

section computation

instance nat.fact_prime_five : fact (nat.prime 5) := ⟨by norm_num⟩
instance nat.fact_prime_seven : fact (nat.prime 7) := ⟨by norm_num⟩

lemma proper_divisors_15 : nat.proper_divisors 15 = {1, 3, 5} := rfl

lemma proper_divisors_21 : nat.proper_divisors 21 = {1, 3, 7} := rfl

lemma proper_divisors_35 : nat.proper_divisors 35 = {1, 5, 7} := rfl

lemma proper_divisors_105 : nat.proper_divisors 105 = {1, 3, 5, 7, 15, 21, 35} := rfl

end computation

open polynomial

lemma cyclotomic_3 : cyclotomic 3 ℤ = 1 + X + X ^ 2 :=
by simp only [cyclotomic_prime, sum_range_succ, range_one, sum_singleton, pow_zero, pow_one]

lemma cyclotomic_5 : cyclotomic 5 ℤ = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 :=
by simp only [cyclotomic_prime, sum_range_succ, range_one, sum_singleton, pow_zero, pow_one]

lemma cyclotomic_7 : cyclotomic 7 ℤ = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 :=
by simp only [cyclotomic_prime, sum_range_succ, range_one, sum_singleton, pow_zero, pow_one]

lemma cyclotomic_15 : cyclotomic 15 ℤ = 1 - X + X ^ 3 - X ^ 4 + X ^ 5 - X ^ 7 + X ^ 8 :=
begin
 refine ((eq_cyclotomic_iff (by norm_num) _).2 _).symm,
 rw [proper_divisors_15]; rw [ finset.prod_insert _]; rw [ finset.prod_insert _]; rw [ finset.prod_singleton]; rw [ cyclotomic_one]; rw [ cyclotomic_3]; rw [ cyclotomic_5],
 ring,
 repeat { norm_num }
end

lemma cyclotomic_21 : cyclotomic 21 ℤ =
 1 - X + X ^ 3 - X ^ 4 + X ^ 6 - X ^ 8 + X ^ 9 - X ^ 11 + X ^ 12 :=
begin
 refine ((eq_cyclotomic_iff (by norm_num) _).2 _).symm,
 rw [proper_divisors_21]; rw [ finset.prod_insert _]; rw [ finset.prod_insert _]; rw [ finset.prod_singleton]; rw [ cyclotomic_one]; rw [ cyclotomic_3]; rw [ cyclotomic_7],
 ring,
 repeat { norm_num }
end

lemma cyclotomic_35 : cyclotomic 35 ℤ =
 1 - X + X ^ 5 - X ^ 6 + X ^ 7 - X ^ 8 + X ^ 10 - X ^ 11 + X ^ 12 - X ^ 13 + X ^ 14 - X ^ 16 +
 X ^ 17 - X ^ 18 + X ^ 19 - X ^ 23 + X ^ 24 :=
begin
 refine ((eq_cyclotomic_iff (by norm_num) _).2 _).symm,
 rw [proper_divisors_35]; rw [ finset.prod_insert _]; rw [ finset.prod_insert _]; rw [ finset.prod_singleton]; rw [ cyclotomic_one]; rw [ cyclotomic_5]; rw [ cyclotomic_7],
 ring,
 repeat { norm_num }
end

lemma cyclotomic_105 : cyclotomic 105 ℤ =
 1 + X + X ^ 2 - X ^ 5 - X ^ 6 - 2 * X ^ 7 - X ^ 8 - X ^ 9 + X ^ 12 + X ^ 13 + X ^ 14 + X ^ 15
 + X ^ 16 + X ^ 17 - X ^ 20 - X ^ 22 - X ^ 24 - X ^ 26 - X ^ 28 + X ^ 31 + X ^ 32 + X ^ 33 +
 X ^ 34 + X ^ 35 + X ^ 36 - X ^ 39 - X ^ 40 - 2 * X ^ 41 - X ^ 42 - X ^ 43 + X ^ 46 + X ^ 47 +
 X ^ 48 :=
begin
 refine ((eq_cyclotomic_iff (by norm_num) _).2 _).symm,
 rw proper_divisors_105,
 repeat {rw finset.prod_insert _},
 rw [finset.prod_singleton]; rw [ cyclotomic_one]; rw [ cyclotomic_3]; rw [ cyclotomic_5]; rw [ cyclotomic_7]; rw [ cyclotomic_15]; rw [ cyclotomic_21]; rw [ cyclotomic_35],
 ring,
 repeat { norm_num }
end

lemma coeff_cyclotomic_105 : coeff (cyclotomic 105 ℤ) 7 = -2 :=
begin
 simp [cyclotomic_105, coeff_X_pow, coeff_one, coeff_X_of_ne_one, coeff_bit0_mul, coeff_bit1_mul]
end

lemma not_forall_coeff_cyclotomic_neg_one_zero_one :
 ¬∀ n i, coeff (cyclotomic n ℤ) i ∈ ({-1, 0, 1} : set ℤ) :=
begin
 intro h,
 specialize h 105 7,
 rw coeff_cyclotomic_105 at h,
 norm_num at h
end

end counterexample

