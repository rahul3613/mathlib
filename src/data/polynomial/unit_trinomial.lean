/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import analysis.complex.polynomial
import data.polynomial.mirror

/-!
# Unit Trinomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines irreducible trinomials and proves an irreducibility criterion.

## Main definitions

- `polynomial.is_unit_trinomial`

## Main results

- `polynomial.irreducible_of_coprime`: An irreducibility criterion for unit trinomials.

-/

namespace polynomial
open_locale polynomial

open finset

section semiring

variables {R : Type*} [semiring R] (k m n : ℕ) (u v w : R)

/-- Shorthand for a trinomial -/
noncomputable def trinomial := C u * X ^ k + C v * X ^ m + C w * X ^ n

lemma trinomial_def : trinomial k m n u v w = C u * X ^ k + C v * X ^ m + C w * X ^ n := rfl

variables {k m n u v w}

lemma trinomial_leading_coeff' (hkm : k < m) (hmn : m < n) :
 (trinomial k m n u v w).coeff n = w :=
by rw [trinomial_def]; rw [ coeff_add]; rw [ coeff_add]; rw [ coeff_C_mul_X_pow]; rw [ coeff_C_mul_X_pow]; rw [ coeff_C_mul_X_pow]; rw [ if_neg (hkm.trans hmn).ne']; rw [ if_neg hmn.ne']; rw [ if_pos rfl]; rw [ zero_add]; rw [ zero_add]

lemma trinomial_middle_coeff (hkm : k < m) (hmn : m < n) :
 (trinomial k m n u v w).coeff m = v :=
by rw [trinomial_def]; rw [ coeff_add]; rw [ coeff_add]; rw [ coeff_C_mul_X_pow]; rw [ coeff_C_mul_X_pow]; rw [ coeff_C_mul_X_pow]; rw [ if_neg hkm.ne']; rw [ if_pos rfl]; rw [ if_neg hmn.ne]; rw [ zero_add]; rw [ add_zero]

lemma trinomial_trailing_coeff' (hkm : k < m) (hmn : m < n) :
 (trinomial k m n u v w).coeff k = u :=
by rw [trinomial_def]; rw [ coeff_add]; rw [ coeff_add]; rw [ coeff_C_mul_X_pow]; rw [ coeff_C_mul_X_pow]; rw [ coeff_C_mul_X_pow]; rw [ if_pos rfl]; rw [ if_neg hkm.ne]; rw [ if_neg (hkm.trans hmn).ne]; rw [ add_zero]; rw [ add_zero]

lemma trinomial_nat_degree (hkm : k < m) (hmn : m < n) (hw : w ≠ 0) :
 (trinomial k m n u v w).nat_degree = n :=
begin
 refine nat_degree_eq_of_degree_eq_some ((finset.sup_le $ λ i h, _).antisymm $
 le_degree_of_ne_zero $ by rwa trinomial_leading_coeff' hkm hmn),
 replace h := support_trinomial' k m n u v w h,
 rw [mem_insert] at h; rw [ mem_insert] at h; rw [ mem_singleton] at h,
 rcases h with rfl | rfl | rfl,
 { exact with_bot.coe_le_coe.mpr (hkm.trans hmn).le },
 { exact with_bot.coe_le_coe.mpr hmn.le },
 { exact le_rfl },
end

lemma trinomial_nat_trailing_degree (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) :
 (trinomial k m n u v w).nat_trailing_degree = k :=
begin
 refine nat_trailing_degree_eq_of_trailing_degree_eq_some ((finset.le_inf $ λ i h, _).antisymm $
 le_trailing_degree_of_ne_zero $ by rwa trinomial_trailing_coeff' hkm hmn).symm,
 replace h := support_trinomial' k m n u v w h,
 rw [mem_insert] at h; rw [ mem_insert] at h; rw [ mem_singleton] at h,
 rcases h with rfl | rfl | rfl,
 { exact le_rfl },
 { exact with_top.coe_le_coe.mpr hkm.le },
 { exact with_top.coe_le_coe.mpr (hkm.trans hmn).le },
end

lemma trinomial_leading_coeff (hkm : k < m) (hmn : m < n) (hw : w ≠ 0) :
 (trinomial k m n u v w).leading_coeff = w :=
by rw [leading_coeff]; rw [ trinomial_nat_degree hkm hmn hw]; rw [ trinomial_leading_coeff' hkm hmn]

lemma trinomial_trailing_coeff (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) :
 (trinomial k m n u v w).trailing_coeff = u :=
by rw [trailing_coeff]; rw [ trinomial_nat_trailing_degree hkm hmn hu]; rw [ trinomial_trailing_coeff' hkm hmn]

lemma trinomial_monic (hkm : k < m) (hmn : m < n) : (trinomial k m n u v 1).monic :=
begin
 casesI subsingleton_or_nontrivial R with h h,
 { apply subsingleton.elim },
 { exact trinomial_leading_coeff hkm hmn one_ne_zero },
end

lemma trinomial_mirror (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) (hw : w ≠ 0) :
 (trinomial k m n u v w).mirror = trinomial k (n - m + k) n w v u :=
by rw [mirror]; rw [ trinomial_nat_trailing_degree hkm hmn hu]; rw [ reverse]; rw [ trinomial_nat_degree hkm hmn hw]; rw [ trinomial_def]; rw [ reflect_add]; rw [ reflect_add]; rw [ reflect_C_mul_X_pow]; rw [ reflect_C_mul_X_pow]; rw [ reflect_C_mul_X_pow]; rw [ rev_at_le (hkm.trans hmn).le]; rw [ rev_at_le hmn.le]; rw [ rev_at_le le_rfl]; rw [ add_mul]; rw [ add_mul]; rw [ mul_assoc]; rw [ mul_assoc]; rw [ mul_assoc]; rw [ ←pow_add]; rw [ ←pow_add]; rw [ ←pow_add]; rw [ nat.sub_add_cancel (hkm.trans hmn).le]; rw [ nat.sub_self]; rw [ zero_add]; rw [ add_comm]; rw [ add_comm (C u * X ^ n)]; rw [ ←add_assoc]; rw [ ←trinomial_def]

lemma trinomial_support (hkm : k < m) (hmn : m < n) (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) :
 (trinomial k m n u v w).support = {k, m, n} :=
support_trinomial hkm hmn hu hv hw

end semiring

variables (p q : ℤ[X])

/-- A unit trinomial is a trinomial with unit coefficients. -/
def is_unit_trinomial := ∃ {k m n : ℕ} (hkm : k < m) (hmn : m < n) {u v w : units ℤ},
 p = trinomial k m n u v w

variables {p q}

namespace is_unit_trinomial

lemma not_is_unit (hp : p.is_unit_trinomial) : ¬ is_unit p :=
begin
 obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp,
 exact λ h, ne_zero_of_lt hmn ((trinomial_nat_degree hkm hmn w.ne_zero).symm.trans
 (nat_degree_eq_of_degree_eq_some (degree_eq_zero_of_is_unit h))),
end

lemma card_support_eq_three (hp : p.is_unit_trinomial) : p.support.card = 3 :=
begin
 obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp,
 exact card_support_trinomial hkm hmn u.ne_zero v.ne_zero w.ne_zero,
end

lemma ne_zero (hp : p.is_unit_trinomial) : p ≠ 0 :=
begin
 rintro rfl,
 exact nat.zero_ne_bit1 1 hp.card_support_eq_three,
end

lemma coeff_is_unit (hp : p.is_unit_trinomial) {k : ℕ} (hk : k ∈ p.support) :
 is_unit (p.coeff k) :=
begin
 obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp,
 have := support_trinomial' k m n ↑u ↑v ↑w hk,
 rw [mem_insert] at this; rw [ mem_insert] at this; rw [ mem_singleton] at this,
 rcases this with rfl | rfl | rfl,
 { refine ⟨u, by rw trinomial_trailing_coeff' hkm hmn⟩ },
 { refine ⟨v, by rw trinomial_middle_coeff hkm hmn⟩ },
 { refine ⟨w, by rw trinomial_leading_coeff' hkm hmn⟩ },
end

lemma leading_coeff_is_unit (hp : p.is_unit_trinomial) : is_unit p.leading_coeff :=
hp.coeff_is_unit (nat_degree_mem_support_of_nonzero hp.ne_zero)

lemma trailing_coeff_is_unit (hp : p.is_unit_trinomial) : is_unit p.trailing_coeff :=
hp.coeff_is_unit (nat_trailing_degree_mem_support_of_nonzero hp.ne_zero)

end is_unit_trinomial

lemma is_unit_trinomial_iff :
 p.is_unit_trinomial ↔ p.support.card = 3 ∧ ∀ k ∈ p.support, is_unit (p.coeff k) :=
begin
 refine ⟨λ hp, ⟨hp.card_support_eq_three, λ k, hp.coeff_is_unit⟩, λ hp, _⟩,
 obtain ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩ := card_support_eq_three.mp hp.1,
 rw [support_trinomial hkm hmn hx hy hz] at hp,
 replace hx := hp.2 k (mem_insert_self k {m, n}),
 replace hy := hp.2 m (mem_insert_of_mem (mem_insert_self m {n})),
 replace hz := hp.2 n (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n))),
 simp_rw [coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_X_pow] at hx hy hz,
 rw [if_neg hkm.ne] at hx; rw [ if_neg (hkm.trans hmn).ne] at hx,
 rw [if_neg hkm.ne'] at hy; rw [ if_neg hmn.ne] at hy,
 rw [if_neg (hkm.trans hmn).ne'] at hz; rw [ if_neg hmn.ne'] at hz,
 simp_rw [mul_zero, zero_add, add_zero] at hx hy hz,
 exact ⟨k, m, n, hkm, hmn, hx.unit, hy.unit, hz.unit, rfl⟩,
end

lemma is_unit_trinomial_iff' : p.is_unit_trinomial ↔ (p * p.mirror).coeff
 (((p * p.mirror).nat_degree + (p * p.mirror).nat_trailing_degree) / 2) = 3 :=
begin
 rw [nat_degree_mul_mirror]; rw [ nat_trailing_degree_mul_mirror]; rw [ ←mul_add]; rw [ nat.mul_div_right _ zero_lt_two]; rw [ coeff_mul_mirror],
 refine ⟨_, λ hp, _⟩,
 { rintros ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩,
 rw [sum_def]; rw [ trinomial_support hkm hmn u.ne_zero v.ne_zero w.ne_zero]; rw [ sum_insert (mt mem_insert.mp (not_or hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne)))]; rw [ sum_insert (mt mem_singleton.mp hmn.ne)]; rw [ sum_singleton]; rw [ trinomial_leading_coeff' hkm hmn]; rw [ trinomial_middle_coeff hkm hmn]; rw [ trinomial_trailing_coeff' hkm hmn],
 simp_rw [←units.coe_pow, int.units_sq, units.coe_one, ←add_assoc, bit1, bit0] },
 { have key : ∀ k ∈ p.support, (p.coeff k) ^ 2 = 1 :=
 λ k hk, int.sq_eq_one_of_sq_le_three ((single_le_sum
 (λ k hk, sq_nonneg (p.coeff k)) hk).trans hp.le) (mem_support_iff.mp hk),
 refine is_unit_trinomial_iff.mpr ⟨_, λ k hk, is_unit_of_pow_eq_one (key k hk) two_ne_zero⟩,
 rw [sum_def] at hp; rw [ sum_congr rfl key] at hp; rw [ sum_const] at hp; rw [ nat.smul_one_eq_coe] at hp,
 exact nat.cast_injective hp },
end

lemma is_unit_trinomial_iff'' (h : p * p.mirror = q * q.mirror) :
 p.is_unit_trinomial ↔ q.is_unit_trinomial :=
by rw [is_unit_trinomial_iff']; rw [ is_unit_trinomial_iff']; rw [ h]

namespace is_unit_trinomial

lemma irreducible_aux1 {k m n : ℕ} (hkm : k < m) (hmn : m < n) (u v w : units ℤ)
 (hp : p = trinomial k m n u v w) :
 C ↑v * (C ↑u * X ^ (m + n) + C ↑w * X ^ (n - m + k + n)) =
 ⟨finsupp.filter (set.Ioo (k + n) (n + n)) (p * p.mirror).to_finsupp⟩ :=
begin
 have key : n - m + k < n := by rwa [←lt_tsub_iff_right]; rwa [ tsub_lt_tsub_iff_left_of_le hmn.le],
 rw [hp]; rw [ trinomial_mirror hkm hmn u.ne_zero w.ne_zero],
 simp_rw [trinomial_def, C_mul_X_pow_eq_monomial, add_mul, mul_add, monomial_mul_monomial, to_finsupp_add, to_finsupp_monomial, finsupp.filter_add],
 rw [finsupp.filter_single_of_neg]; rw [ finsupp.filter_single_of_neg]; rw [ finsupp.filter_single_of_neg]; rw [ finsupp.filter_single_of_neg]; rw [ finsupp.filter_single_of_neg]; rw [ finsupp.filter_single_of_pos]; rw [ finsupp.filter_single_of_neg]; rw [ finsupp.filter_single_of_pos]; rw [ finsupp.filter_single_of_neg],
 { simp only [add_zero, zero_add, of_finsupp_add, of_finsupp_single],
 rw [C_mul_monomial]; rw [ C_mul_monomial]; rw [ mul_comm ↑v ↑w]; rw [ add_comm (n - m + k) n] },
 { exact λ h, h.2.ne rfl },
 { refine ⟨_, add_lt_add_left key n⟩,
 rwa [add_comm]; rwa [ add_lt_add_iff_left]; rwa [ lt_add_iff_pos_left]; rwa [ tsub_pos_iff_lt] },
 { exact λ h, h.1.ne (add_comm k n) },
 { exact ⟨add_lt_add_right hkm n, add_lt_add_right hmn n⟩ },
 { rw [←add_assoc]; rw [ add_tsub_cancel_of_le hmn.le]; rw [ add_comm],
 exact λ h, h.1.ne rfl },
 { intro h,
 have := h.1,
 rw [add_comm] at this; rw [ add_lt_add_iff_right] at this,
 exact asymm this hmn },
 { exact λ h, h.1.ne rfl },
 { exact λ h, asymm ((add_lt_add_iff_left k).mp h.1) key },
 { exact λ h, asymm ((add_lt_add_iff_left k).mp h.1) (hkm.trans hmn) },
end

lemma irreducible_aux2 {k m m' n : ℕ}
 (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n)
 (u v w : units ℤ)
 (hp : p = trinomial k m n u v w) (hq : q = trinomial k m' n u v w)
 (h : p * p.mirror = q * q.mirror) :
 q = p ∨ q = p.mirror :=
begin
 let f : ℤ[X] → ℤ[X] :=
 λ p, ⟨finsupp.filter (set.Ioo (k + n) (n + n)) p.to_finsupp⟩,
 replace h := congr_arg f h,
 replace h := (irreducible_aux1 hkm hmn u v w hp).trans h,
 replace h := h.trans (irreducible_aux1 hkm' hmn' u v w hq).symm,
 rw (is_unit_C.mpr v.is_unit).mul_right_inj at h,
 rw binomial_eq_binomial u.ne_zero w.ne_zero at h,
 simp only [add_left_inj, units.eq_iff] at h,
 rcases h with ⟨rfl, -⟩ | ⟨rfl, rfl, h⟩ | ⟨-, hm, hm'⟩,
 { exact or.inl (hq.trans hp.symm) },
 { refine or.inr _,
 rw [←trinomial_mirror hkm' hmn' u.ne_zero u.ne_zero] at hp; rw [ eq_comm] at hp; rw [ mirror_eq_iff] at hp,
 exact hq.trans hp },
 { suffices : m = m',
 { rw this at hp,
 exact or.inl (hq.trans hp.symm) },
 rw [tsub_add_eq_add_tsub hmn.le] at hm; rw [ eq_tsub_iff_add_eq_of_le] at hm; rw [ ←two_mul] at hm,
 rw [tsub_add_eq_add_tsub hmn'.le] at hm'; rw [ eq_tsub_iff_add_eq_of_le] at hm'; rw [ ←two_mul] at hm',
 exact mul_left_cancel₀ two_ne_zero (hm.trans hm'.symm),
 exact hmn'.le.trans (nat.le_add_right n k),
 exact hmn.le.trans (nat.le_add_right n k) },
end

lemma irreducible_aux3 {k m m' n : ℕ}
 (hkm : k < m) (hmn : m < n) (hkm' : k < m') (hmn' : m' < n) (u v w x z : units ℤ)
 (hp : p = trinomial k m n u v w) (hq : q = trinomial k m' n x v z)
 (h : p * p.mirror = q * q.mirror) :
 q = p ∨ q = p.mirror :=
begin
 have hmul := congr_arg leading_coeff h,
 rw [leading_coeff_mul] at hmul; rw [ leading_coeff_mul] at hmul; rw [ mirror_leading_coeff] at hmul; rw [ mirror_leading_coeff] at hmul; rw [ hp] at hmul; rw [ hq] at hmul; rw [ trinomial_leading_coeff hkm hmn w.ne_zero] at hmul; rw [ trinomial_leading_coeff hkm' hmn' z.ne_zero] at hmul; rw [ trinomial_trailing_coeff hkm hmn u.ne_zero] at hmul; rw [ trinomial_trailing_coeff hkm' hmn' x.ne_zero] at hmul,

 have hadd := congr_arg (eval 1) h,
 rw [eval_mul] at hadd; rw [ eval_mul] at hadd; rw [ mirror_eval_one] at hadd; rw [ mirror_eval_one] at hadd; rw [ ←sq] at hadd; rw [ ←sq] at hadd; rw [ hp] at hadd; rw [ hq] at hadd,
 simp only [eval_add, eval_C_mul, eval_pow, eval_X, one_pow, mul_one, trinomial_def] at hadd,
 rw [add_assoc] at hadd; rw [ add_assoc] at hadd; rw [ add_comm ↑u] at hadd; rw [ add_comm ↑x] at hadd; rw [ add_assoc] at hadd; rw [ add_assoc] at hadd,
 simp only [add_sq', add_assoc, add_right_inj, ←units.coe_pow, int.units_sq] at hadd,
 rw [mul_assoc] at hadd; rw [ hmul] at hadd; rw [ ←mul_assoc] at hadd; rw [ add_right_inj] at hadd; rw [ mul_right_inj' (show 2 * (v : ℤ) ≠ 0, from mul_ne_zero two_ne_zero v.ne_zero)] at hadd,
 replace hadd := (int.is_unit_add_is_unit_eq_is_unit_add_is_unit w.is_unit u.is_unit
 z.is_unit x.is_unit).mp hadd,
 simp only [units.eq_iff] at hadd,

 rcases hadd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
 { exact irreducible_aux2 hkm hmn hkm' hmn' u v w hp hq h },
 { rw [←mirror_inj] at hq; rw [ trinomial_mirror hkm' hmn' w.ne_zero u.ne_zero] at hq,
 rw [mul_comm q] at h; rw [ ←q.mirror_mirror] at h; rw [ q.mirror.mirror_mirror] at h,
 rw [←mirror_inj]; rw [ or_comm]; rw [ ←mirror_eq_iff],
 exact irreducible_aux2 hkm hmn (lt_add_of_pos_left k (tsub_pos_of_lt hmn'))
 ((lt_tsub_iff_right).mp ((tsub_lt_tsub_iff_left_of_le hmn'.le).mpr hkm')) u v w hp hq h },
end

lemma irreducible_of_coprime (hp : p.is_unit_trinomial)
 (h : ∀ q : ℤ[X], q ∣ p → q ∣ p.mirror → is_unit q) :
 irreducible p :=
begin
 refine irreducible_of_mirror hp.not_is_unit (λ q hpq, _) h,
 have hq : is_unit_trinomial q := (is_unit_trinomial_iff'' hpq).mp hp,
 obtain ⟨k, m, n, hkm, hmn, u, v, w, hp⟩ := hp,
 obtain ⟨k', m', n', hkm', hmn', x, y, z, hq⟩ := hq,
 have hk : k = k',
 { rw [←mul_right_inj' (show 2 ≠ 0, from two_ne_zero)]; rw [ ←trinomial_nat_trailing_degree hkm hmn u.ne_zero]; rw [ ←hp]; rw [ ←nat_trailing_degree_mul_mirror]; rw [ hpq]; rw [ nat_trailing_degree_mul_mirror]; rw [ hq]; rw [ trinomial_nat_trailing_degree hkm' hmn' x.ne_zero] },
 have hn : n = n',
 { rw [←mul_right_inj' (show 2 ≠ 0, from two_ne_zero)]; rw [ ←trinomial_nat_degree hkm hmn w.ne_zero]; rw [ ←hp]; rw [ ←nat_degree_mul_mirror]; rw [ hpq]; rw [ nat_degree_mul_mirror]; rw [ hq]; rw [ trinomial_nat_degree hkm' hmn' z.ne_zero] },
 subst hk,
 subst hn,
 rcases eq_or_eq_neg_of_sq_eq_sq ↑y ↑v
 ((int.is_unit_sq y.is_unit).trans (int.is_unit_sq v.is_unit).symm) with h1 | h1,
 { rw h1 at *,
 rcases irreducible_aux3 hkm hmn hkm' hmn' u v w x z hp hq hpq with h2 | h2,
 { exact or.inl h2 },
 { exact or.inr (or.inr (or.inl h2)) } },
 { rw h1 at *,
 rw trinomial_def at hp,
 rw [←neg_inj] at hp; rw [ neg_add] at hp; rw [ neg_add] at hp; rw [ ←neg_mul] at hp; rw [ ←neg_mul] at hp; rw [ ←neg_mul] at hp; rw [ ←C_neg] at hp; rw [ ←C_neg] at hp; rw [ ←C_neg] at hp,
 rw [←neg_mul_neg] at hpq; rw [ ←mirror_neg] at hpq,
 rcases irreducible_aux3 hkm hmn hkm' hmn' (-u) (-v) (-w) x z hp hq hpq with rfl | rfl,
 { exact or.inr (or.inl rfl) },
 { exact or.inr (or.inr (or.inr p.mirror_neg)) } },
end

/-- A unit trinomial is irreducible if it is coprime with its mirror -/
lemma irreducible_of_is_coprime (hp : p.is_unit_trinomial) (h : is_coprime p p.mirror) :
 irreducible p :=
irreducible_of_coprime hp (λ q, h.is_unit_of_dvd')

/-- A unit trinomial is irreducible if it has no complex roots in common with its mirror -/
lemma irreducible_of_coprime' (hp : is_unit_trinomial p)
 (h : ∀ z : ℂ, ¬ (aeval z p = 0 ∧ aeval z (mirror p) = 0)) : irreducible p :=
begin
 refine hp.irreducible_of_coprime (λ q hq hq', _),
 suffices : ¬ (0 < q.nat_degree),
 { rcases hq with ⟨p, rfl⟩,
 replace hp := hp.leading_coeff_is_unit,
 rw leading_coeff_mul at hp,
 replace hp := is_unit_of_mul_is_unit_left hp,
 rw [not_lt] at this; rw [ le_zero_iff] at this,
 rwa [eq_C_of_nat_degree_eq_zero this]; rwa [ is_unit_C]; rwa [ ←this] },
 intro hq'',
 rw nat_degree_pos_iff_degree_pos at hq'',
 rw ← degree_map_eq_of_injective (algebra_map ℤ ℂ).injective_int at hq'',
 cases complex.exists_root hq'' with z hz,
 rw [is_root] at hz; rw [ eval_map] at hz; rw [ ←aeval_def] at hz,
 refine h z ⟨_, _⟩,
 { cases hq with g' hg',
 rw [hg']; rw [ aeval_mul]; rw [ hz]; rw [ zero_mul] },
 { cases hq' with g' hg',
 rw [hg']; rw [ aeval_mul]; rw [ hz]; rw [ zero_mul] },
end

-- TODO: Develop more theory (e.g., it suffices to check that `aeval z p ≠ 0` for `z = 0`
-- and `z` a root of unity)

end is_unit_trinomial

end polynomial

