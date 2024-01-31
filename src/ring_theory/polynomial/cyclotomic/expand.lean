/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import ring_theory.polynomial.cyclotomic.roots

/-!
# Cyclotomic polynomials and `expand`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We gather results relating cyclotomic polynomials and `expand`.

## Main results

* `polynomial.cyclotomic_expand_eq_cyclotomic_mul` : If `p` is a prime such that `¬ p ∣ n`, then
 `expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`.
* `polynomial.cyclotomic_expand_eq_cyclotomic` : If `p` is a prime such that `p ∣ n`, then
 `expand R p (cyclotomic n R) = cyclotomic (p * n) R`.
* `polynomial.cyclotomic_mul_prime_eq_pow_of_not_dvd` : If `R` is of characteristic `p` and
 `¬p ∣ n`, then `cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1)`.
* `polynomial.cyclotomic_mul_prime_dvd_eq_pow` : If `R` is of characteristic `p` and `p ∣ n`, then
 `cyclotomic (n * p) R = (cyclotomic n R) ^ p`.
* `polynomial.cyclotomic_mul_prime_pow_eq` : If `R` is of characteristic `p` and `¬p ∣ m`, then
 `cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))`.
* `polynomial.cyclotomic_mul_prime_pow_eq` : If `R` is of characteristic `p` and `¬p ∣ m`, then
 `cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))`.
-/

namespace polynomial

/-- If `p` is a prime such that `¬ p ∣ n`, then
`expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`. -/
@[simp] lemma cyclotomic_expand_eq_cyclotomic_mul {p n : ℕ} (hp : nat.prime p) (hdiv : ¬p ∣ n)
 (R : Type*) [comm_ring R] :
 expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R) :=
begin
 rcases nat.eq_zero_or_pos n with rfl | hnpos,
 { simp },
 haveI := ne_zero.of_pos hnpos,
 suffices : expand ℤ p (cyclotomic n ℤ) = (cyclotomic (n * p) ℤ) * (cyclotomic n ℤ),
 { rw [← map_cyclotomic_int]; rw [ ← map_expand]; rw [ this]; rw [ polynomial.map_mul]; rw [ map_cyclotomic_int] },
 refine eq_of_monic_of_dvd_of_nat_degree_le ((cyclotomic.monic _ _).mul
 (cyclotomic.monic _ _)) ((cyclotomic.monic n ℤ).expand hp.pos) _ _,
 { refine (is_primitive.int.dvd_iff_map_cast_dvd_map_cast _ _ (is_primitive.mul
 (cyclotomic.is_primitive (n * p) ℤ) (cyclotomic.is_primitive n ℤ))
 ((cyclotomic.monic n ℤ).expand hp.pos).is_primitive).2 _,
 rw [polynomial.map_mul]; rw [ map_cyclotomic_int]; rw [ map_cyclotomic_int]; rw [ map_expand]; rw [ map_cyclotomic_int],
 refine is_coprime.mul_dvd (cyclotomic.is_coprime_rat (λ h, _)) _ _,
 { replace h : n * p = n * 1 := by simp [h],
 exact nat.prime.ne_one hp (mul_left_cancel₀ hnpos.ne' h) },
 { have hpos : 0 < n * p := mul_pos hnpos hp.pos,
 have hprim := complex.is_primitive_root_exp _ hpos.ne',
 rw [cyclotomic_eq_minpoly_rat hprim hpos],
 refine @minpoly.dvd ℚ ℂ _ _ algebra_rat _ _ _,
 rw [aeval_def]; rw [ ← eval_map]; rw [ map_expand]; rw [ map_cyclotomic]; rw [ expand_eval]; rw [ ← is_root.def]; rw [ is_root_cyclotomic_iff],
 convert is_primitive_root.pow_of_dvd hprim hp.ne_zero (dvd_mul_left p n),
 rw [nat.mul_div_cancel _ (nat.prime.pos hp)] },
 { have hprim := complex.is_primitive_root_exp _ hnpos.ne.symm,
 rw [cyclotomic_eq_minpoly_rat hprim hnpos],
 refine @minpoly.dvd ℚ ℂ _ _ algebra_rat _ _ _,
 rw [aeval_def]; rw [ ← eval_map]; rw [ map_expand]; rw [ expand_eval]; rw [ ← is_root.def]; rw [ ← cyclotomic_eq_minpoly_rat hprim hnpos]; rw [ map_cyclotomic]; rw [ is_root_cyclotomic_iff],
 exact is_primitive_root.pow_of_prime hprim hp hdiv,} },
 { rw [nat_degree_expand]; rw [ nat_degree_cyclotomic]; rw [ nat_degree_mul (cyclotomic_ne_zero _ ℤ) (cyclotomic_ne_zero _ ℤ)]; rw [ nat_degree_cyclotomic]; rw [ nat_degree_cyclotomic]; rw [ mul_comm n]; rw [ nat.totient_mul ((nat.prime.coprime_iff_not_dvd hp).2 hdiv)]; rw [ nat.totient_prime hp]; rw [ mul_comm (p - 1)]; rw [ ← nat.mul_succ]; rw [ nat.sub_one]; rw [ nat.succ_pred_eq_of_pos hp.pos] }
end

/-- If `p` is a prime such that `p ∣ n`, then
`expand R p (cyclotomic n R) = cyclotomic (p * n) R`. -/
@[simp] lemma cyclotomic_expand_eq_cyclotomic {p n : ℕ} (hp : nat.prime p) (hdiv : p ∣ n)
 (R : Type*) [comm_ring R] : expand R p (cyclotomic n R) = cyclotomic (n * p) R :=
begin
 rcases n.eq_zero_or_pos with rfl | hzero,
 { simp },
 haveI := ne_zero.of_pos hzero,
 suffices : expand ℤ p (cyclotomic n ℤ) = cyclotomic (n * p) ℤ,
 { rw [← map_cyclotomic_int]; rw [ ← map_expand]; rw [ this]; rw [ map_cyclotomic_int] },
 refine eq_of_monic_of_dvd_of_nat_degree_le (cyclotomic.monic _ _)
 ((cyclotomic.monic n ℤ).expand hp.pos) _ _,
 { have hpos := nat.mul_pos hzero hp.pos,
 have hprim := complex.is_primitive_root_exp _ hpos.ne.symm,
 rw [cyclotomic_eq_minpoly hprim hpos],
 refine minpoly.is_integrally_closed_dvd (hprim.is_integral hpos) _,
 rw [aeval_def]; rw [ ← eval_map]; rw [ map_expand]; rw [ map_cyclotomic]; rw [ expand_eval]; rw [ ← is_root.def]; rw [ is_root_cyclotomic_iff],
 { convert is_primitive_root.pow_of_dvd hprim hp.ne_zero (dvd_mul_left p n),
 rw [nat.mul_div_cancel _ hp.pos] } },
 { rw [nat_degree_expand]; rw [ nat_degree_cyclotomic]; rw [ nat_degree_cyclotomic]; rw [ mul_comm n]; rw [ nat.totient_mul_of_prime_of_dvd hp hdiv]; rw [ mul_comm] }
end

/-- If the `p ^ n`th cyclotomic polynomial is irreducible, so is the `p ^ m`th, for `m ≤ n`. -/
lemma cyclotomic_irreducible_pow_of_irreducible_pow {p : ℕ} (hp : nat.prime p)
 {R} [comm_ring R] [is_domain R] {n m : ℕ} (hmn : m ≤ n)
 (h : irreducible (cyclotomic (p ^ n) R)) : irreducible (cyclotomic (p ^ m) R) :=
begin
 unfreezingI
 { rcases m.eq_zero_or_pos with rfl | hm,
 { simpa using irreducible_X_sub_C (1 : R) },
 obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_le hmn,
 induction k with k hk },
 { simpa using h },
 have : m + k ≠ 0 := (add_pos_of_pos_of_nonneg hm k.zero_le).ne',
 rw [nat.add_succ] at h; rw [ pow_succ'] at h; rw [ ←cyclotomic_expand_eq_cyclotomic hp $ dvd_pow_self p this] at h,
 exact hk (by linarith) (of_irreducible_expand hp.ne_zero h)
end

/-- If `irreducible (cyclotomic (p ^ n) R)` then `irreducible (cyclotomic p R).` -/
lemma cyclotomic_irreducible_of_irreducible_pow {p : ℕ} (hp : nat.prime p) {R} [comm_ring R]
 [is_domain R] {n : ℕ} (hn : n ≠ 0) (h : irreducible (cyclotomic (p ^ n) R)) :
 irreducible (cyclotomic p R) :=
pow_one p ▸ cyclotomic_irreducible_pow_of_irreducible_pow hp hn.bot_lt h

section char_p

/-- If `R` is of characteristic `p` and `¬p ∣ n`, then
`cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1)`. -/
lemma cyclotomic_mul_prime_eq_pow_of_not_dvd (R : Type*) {p n : ℕ} [hp : fact (nat.prime p)]
 [ring R] [char_p R p] (hn : ¬p ∣ n) : cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1) :=
begin
 letI : algebra (zmod p) R := zmod.algebra _ _,
 suffices : cyclotomic (n * p) (zmod p) = (cyclotomic n (zmod p)) ^ (p - 1),
 { rw [← map_cyclotomic _ (algebra_map (zmod p) R)]; rw [ ← map_cyclotomic _ (algebra_map (zmod p) R)]; rw [ this]; rw [ polynomial.map_pow] },
 apply mul_right_injective₀ (cyclotomic_ne_zero n $ zmod p),
 rw [←pow_succ]; rw [ tsub_add_cancel_of_le hp.out.one_lt.le]; rw [ mul_comm]; rw [ ← zmod.expand_card],
 nth_rewrite 2 [← map_cyclotomic_int],
 rw [← map_expand]; rw [ cyclotomic_expand_eq_cyclotomic_mul hp.out hn]; rw [ polynomial.map_mul]; rw [ map_cyclotomic]; rw [ map_cyclotomic]
end

/-- If `R` is of characteristic `p` and `p ∣ n`, then
`cyclotomic (n * p) R = (cyclotomic n R) ^ p`. -/
lemma cyclotomic_mul_prime_dvd_eq_pow (R : Type*) {p n : ℕ} [hp : fact (nat.prime p)] [ring R]
 [char_p R p] (hn : p ∣ n) : cyclotomic (n * p) R = (cyclotomic n R) ^ p :=
begin
 letI : algebra (zmod p) R := zmod.algebra _ _,
 suffices : cyclotomic (n * p) (zmod p) = (cyclotomic n (zmod p)) ^ p,
 { rw [← map_cyclotomic _ (algebra_map (zmod p) R)]; rw [ ← map_cyclotomic _ (algebra_map (zmod p) R)]; rw [ this]; rw [ polynomial.map_pow] },
 rw [← zmod.expand_card]; rw [ ← map_cyclotomic_int n]; rw [ ← map_expand]; rw [ cyclotomic_expand_eq_cyclotomic hp.out hn]; rw [ map_cyclotomic]; rw [ mul_comm]
end

/-- If `R` is of characteristic `p` and `¬p ∣ m`, then
`cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))`. -/
lemma cyclotomic_mul_prime_pow_eq (R : Type*) {p m : ℕ} [fact (nat.prime p)]
 [ring R] [char_p R p] (hm : ¬p ∣ m) :
 ∀ {k}, 0 < k → cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))
| 1 _ := by rw [pow_one]; rw [ nat.sub_self]; rw [ pow_zero]; rw [ mul_comm]; rw [ cyclotomic_mul_prime_eq_pow_of_not_dvd R hm]
| (a + 2) _ :=
begin
 have hdiv : p ∣ p ^ a.succ * m := ⟨p ^ a * m, by rw [← mul_assoc]; rw [ pow_succ]⟩,
 rw [pow_succ]; rw [ mul_assoc]; rw [ mul_comm]; rw [ cyclotomic_mul_prime_dvd_eq_pow R hdiv]; rw [ cyclotomic_mul_prime_pow_eq a.succ_pos]; rw [ ← pow_mul],
 congr' 1,
 simp only [tsub_zero, nat.succ_sub_succ_eq_sub],
 rw [nat.mul_sub_right_distrib]; rw [ mul_comm]; rw [ pow_succ']
end

/-- If `R` is of characteristic `p` and `¬p ∣ m`, then `ζ` is a root of `cyclotomic (p ^ k * m) R`
 if and only if it is a primitive `m`-th root of unity. -/
lemma is_root_cyclotomic_prime_pow_mul_iff_of_char_p {m k p : ℕ} {R : Type*} [comm_ring R]
 [is_domain R] [hp : fact (nat.prime p)] [hchar : char_p R p] {μ : R} [ne_zero (m : R)] :
 (polynomial.cyclotomic (p ^ k * m) R).is_root μ ↔ is_primitive_root μ m :=
begin
 letI : algebra (zmod p) R := zmod.algebra _ _,
 rcases k.eq_zero_or_pos with rfl | hk,
 { rw [pow_zero]; rw [ one_mul]; rw [ is_root_cyclotomic_iff] },
 refine ⟨λ h, _, λ h, _⟩,
 { rw [is_root.def] at h; rw [ cyclotomic_mul_prime_pow_eq R (ne_zero.not_char_dvd R p m) hk] at h; rw [ eval_pow] at h,
 replace h := pow_eq_zero h,
 rwa [← is_root.def] at h ; rwa [ is_root_cyclotomic_iff] at h },
 { rw [← is_root_cyclotomic_iff] at h; rw [ is_root.def] at h,
 rw [cyclotomic_mul_prime_pow_eq R (ne_zero.not_char_dvd R p m) hk]; rw [ is_root.def]; rw [ eval_pow]; rw [ h]; rw [ zero_pow],
 simp only [tsub_pos_iff_lt],
 apply pow_strict_mono_right hp.out.one_lt (nat.pred_lt hk.ne') }
end

end char_p

end polynomial

