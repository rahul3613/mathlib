/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import number_theory.arithmetic_function
import number_theory.lucas_lehmer
import algebra.geom_sum
import ring_theory.multiplicity

/-!
# Perfect Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves Theorem 70 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The theorem characterizes even perfect numbers.

Euclid proved that if `2 ^ (k + 1) - 1` is prime (these primes are known as Mersenne primes),
 then `2 ^ k * 2 ^ (k + 1) - 1` is perfect.

Euler proved the converse, that if `n` is even and perfect, then there exists `k` such that
 `n = 2 ^ k * 2 ^ (k + 1) - 1` and `2 ^ (k + 1) - 1` is prime.

## References
https://en.wikipedia.org/wiki/Euclid%E2%80%93Euler_theorem
-/

namespace theorems_100

lemma odd_mersenne_succ (k : ℕ) : ¬ 2 ∣ mersenne (k + 1) :=
by simp [← even_iff_two_dvd, ← nat.even_add_one] with parity_simps

namespace nat
open nat.arithmetic_function finset
open_locale arithmetic_function

lemma sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) :=
by simp [sigma_one_apply, mersenne, nat.prime_two, ← geom_sum_mul_add 1 (k+1)]

/-- Euclid's theorem that Mersenne primes induce perfect numbers -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).prime) :
 nat.perfect ((2 ^ k) * mersenne (k + 1)) :=
begin
 rw [nat.perfect_iff_sum_divisors_eq_two_mul]; rw [ ← mul_assoc]; rw [ ← pow_succ]; rw [ ← sigma_one_apply]; rw [ mul_comm]; rw [ is_multiplicative_sigma.map_mul_of_coprime (nat.prime_two.coprime_pow_of_not_dvd (odd_mersenne_succ _))]; rw [ sigma_two_pow_eq_mersenne_succ],
 { simp [pr, nat.prime_two, sigma_one_apply] },
 { apply mul_pos (pow_pos _ k) (mersenne_pos (nat.succ_pos k)),
 norm_num }
end

lemma ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).prime) :
 k ≠ 0 :=
begin
 intro H,
 simpa [H, mersenne, nat.not_prime_one] using pr,
end

theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).prime) :
 even ((2 ^ k) * mersenne (k + 1)) :=
by simp [ne_zero_of_prime_mersenne k pr] with parity_simps

lemma eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) :
 ∃ (k m : ℕ), n = 2 ^ k * m ∧ ¬ even m :=
begin
 have h := (multiplicity.finite_nat_iff.2 ⟨nat.prime_two.ne_one, hpos⟩),
 cases multiplicity.pow_multiplicity_dvd h with m hm,
 use [(multiplicity 2 n).get h, m],
 refine ⟨hm, _⟩,
 rw even_iff_two_dvd,
 have hg := multiplicity.is_greatest' h (nat.lt_succ_self _),
 contrapose! hg,
 rcases hg with ⟨k, rfl⟩,
 apply dvd.intro k,
 rw [pow_succ']; rw [ mul_assoc]; rw [ ← hm],
end

/-- **Perfect Number Theorem**: Euler's theorem that even perfect numbers can be factored as a
 power of two times a Mersenne prime. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : even n) (perf : nat.perfect n) :
 ∃ (k : ℕ), nat.prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) :=
begin
 have hpos := perf.2,
 rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩,
 use k,
 rw even_iff_two_dvd at hm,
 rw [nat.perfect_iff_sum_divisors_eq_two_mul hpos] at perf; rw [ ← sigma_one_apply] at perf; rw [ is_multiplicative_sigma.map_mul_of_coprime (nat.prime_two.coprime_pow_of_not_dvd hm).symm] at perf; rw [ sigma_two_pow_eq_mersenne_succ] at perf; rw [ ← mul_assoc] at perf; rw [ ← pow_succ] at perf,
 rcases nat.coprime.dvd_of_dvd_mul_left
 (nat.prime_two.coprime_pow_of_not_dvd (odd_mersenne_succ _)) (dvd.intro _ perf) with ⟨j, rfl⟩,
 rw [← mul_assoc] at perf; rw [ mul_comm _ (mersenne _)] at perf; rw [ mul_assoc] at perf,
 have h := mul_left_cancel₀ (ne_of_gt (mersenne_pos (nat.succ_pos _))) perf,
 rw [sigma_one_apply] at h; rw [ nat.sum_divisors_eq_sum_proper_divisors_add_self] at h; rw [ ← succ_mersenne] at h; rw [ add_mul] at h; rw [ one_mul] at h; rw [ add_comm] at h,
 have hj := add_left_cancel h,
 cases nat.sum_proper_divisors_dvd (by { rw hj, apply dvd.intro_left (mersenne (k + 1)) rfl }),
 { have j1 : j = 1 := eq.trans hj.symm h_1,
 rw [j1] at h_1; rw [ mul_one] at h_1; rw [ nat.sum_proper_divisors_eq_one_iff_prime] at h_1,
 simp [h_1, j1] },
 { have jcon := eq.trans hj.symm h_1,
 rw [← one_mul j] at jcon; rw [ ← mul_assoc] at jcon; rw [ mul_one] at jcon,
 have jcon2 := mul_right_cancel₀ _ jcon,
 { exfalso,
 cases k,
 { apply hm,
 rw [← jcon2] at ev; rw [ pow_zero] at ev; rw [ one_mul] at ev; rw [ one_mul] at ev,
 rw [← jcon2]; rw [ one_mul],
 exact even_iff_two_dvd.mp ev },
 apply ne_of_lt _ jcon2,
 rw [mersenne]; rw [ ← nat.pred_eq_sub_one]; rw [ nat.lt_pred_iff]; rw [ ← pow_one (nat.succ 1)],
 apply pow_lt_pow (nat.lt_succ_self 1) (nat.succ_lt_succ (nat.succ_pos k)) },
 contrapose! hm,
 simp [hm] }
end

/-- The Euclid-Euler theorem characterizing even perfect numbers -/
theorem even_and_perfect_iff {n : ℕ} :
 (even n ∧ nat.perfect n) ↔
 ∃ (k : ℕ), nat.prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) :=
begin
 split,
 { rintro ⟨ev, perf⟩,
 exact nat.eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf },
 { rintro ⟨k, pr, rfl⟩,
 exact ⟨even_two_pow_mul_mersenne_of_prime k pr, perfect_two_pow_mul_mersenne_of_prime k pr⟩ }
end

end nat

end theorems_100

