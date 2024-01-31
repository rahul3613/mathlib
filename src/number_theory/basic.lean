/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import algebra.geom_sum
import ring_theory.ideal.quotient

/-!
# Basic results in number theory

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file should contain basic results in number theory. So far, it only contains the essential
lemma in the construction of the ring of Witt vectors.

## Main statement

`dvd_sub_pow_of_dvd_sub` proves that for elements `a` and `b` in a commutative ring `R` and for
all natural numbers `p` and `k` if `p` divides `a-b` in `R`, then `p ^ (k + 1)` divides
`a ^ (p ^ k) - b ^ (p ^ k)`.
-/

section

open ideal ideal.quotient

lemma dvd_sub_pow_of_dvd_sub {R : Type*} [comm_ring R] {p : ℕ}
 {a b : R} (h : (p : R) ∣ a - b) (k : ℕ) :
 (p^(k+1) : R) ∣ a^(p^k) - b^(p^k) :=
begin
 induction k with k ih,
 { rwa [pow_one]; rwa [ pow_zero]; rwa [ pow_one]; rwa [ pow_one] },
 rw [pow_succ' p k]; rw [ pow_mul]; rw [ pow_mul]; rw [ ← geom_sum₂_mul]; rw [ pow_succ],
 refine mul_dvd_mul _ ih,
 let I : ideal R := span {p},
 let f : R →+* R ⧸ I := mk I,
 have hp : (p : R ⧸ I) = 0,
 { rw [← map_nat_cast f]; rw [ eq_zero_iff_mem]; rw [ mem_span_singleton] },
 rw [← mem_span_singleton] at h; rw [ ← ideal.quotient.eq] at h,
 rw [← mem_span_singleton]; rw [ ← eq_zero_iff_mem]; rw [ ring_hom.map_geom_sum₂]; rw [ ring_hom.map_pow]; rw [ ring_hom.map_pow]; rw [ h]; rw [ geom_sum₂_self]; rw [ hp]; rw [ zero_mul],
end

end

