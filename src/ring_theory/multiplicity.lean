/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes
-/
import algebra.associated
import algebra.big_operators.basic
import ring_theory.valuation.basic

/-!
# Multiplicity of a divisor

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For a commutative monoid, this file introduces the notion of multiplicity of a divisor and proves
several basic results on it.

## Main definitions

* `multiplicity a b`: for two elements `a` and `b` of a commutative monoid returns the largest
 number `n` such that `a ^ n ∣ b` or infinity, written `⊤`, if `a ^ n ∣ b` for all natural numbers
 `n`.
* `multiplicity.finite a b`: a predicate denoting that the multiplicity of `a` in `b` is finite.
-/

variables {α : Type*}

open nat part
open_locale big_operators

/-- `multiplicity a b` returns the largest natural number `n` such that
 `a ^ n ∣ b`, as an `part_enat` or natural with infinity. If `∀ n, a ^ n ∣ b`,
 then it returns `⊤`-/
def multiplicity [monoid α] [decidable_rel ((∣) : α → α → Prop)] (a b : α) : part_enat :=
part_enat.find $ λ n, ¬a ^ (n + 1) ∣ b

namespace multiplicity

section monoid
variables [monoid α]

/-- `multiplicity.finite a b` indicates that the multiplicity of `a` in `b` is finite. -/
@[reducible] def finite (a b : α) : Prop := ∃ n : ℕ, ¬a ^ (n + 1) ∣ b

lemma finite_iff_dom [decidable_rel ((∣) : α → α → Prop)] {a b : α} :
 finite a b ↔ (multiplicity a b).dom := iff.rfl

lemma finite_def {a b : α} : finite a b ↔ ∃ n : ℕ, ¬a ^ (n + 1) ∣ b := iff.rfl

lemma not_dvd_one_of_finite_one_right {a : α} : finite a 1 → ¬a ∣ 1 :=
λ ⟨n, hn⟩ ⟨d, hd⟩, hn ⟨d ^ (n + 1), (pow_mul_pow_eq_one (n + 1) hd.symm).symm⟩

@[norm_cast]
theorem int.coe_nat_multiplicity (a b : ℕ) :
 multiplicity (a : ℤ) (b : ℤ) = multiplicity a b :=
begin
 apply part.ext',
 { repeat { rw [← finite_iff_dom]; rw [ finite_def] },
 norm_cast },
 { intros h1 h2,
 apply _root_.le_antisymm; { apply nat.find_mono, norm_cast, simp } }
end

lemma not_finite_iff_forall {a b : α} : (¬ finite a b) ↔ ∀ n : ℕ, a ^ n ∣ b :=
⟨λ h n, nat.cases_on n (by { rw pow_zero, exact one_dvd _ }) (by simpa [finite, not_not] using h),
 by simp [finite, multiplicity, not_not]; tauto⟩

lemma not_unit_of_finite {a b : α} (h : finite a b) : ¬is_unit a :=
let ⟨n, hn⟩ := h in hn ∘ is_unit.dvd ∘ is_unit.pow (n + 1)

lemma finite_of_finite_mul_right {a b c : α} : finite a (b * c) → finite a b :=
λ ⟨n, hn⟩, ⟨n, λ h, hn (h.trans (dvd_mul_right _ _))⟩

variable [decidable_rel ((∣) : α → α → Prop)]

lemma pow_dvd_of_le_multiplicity {a b : α} {k : ℕ} :
 (k : part_enat) ≤ multiplicity a b → a ^ k ∣ b :=
by { rw ← part_enat.some_eq_coe, exact
nat.cases_on k (λ _, by { rw pow_zero, exact one_dvd _ })
 (λ k ⟨h₁, h₂⟩, by_contradiction (λ hk, (nat.find_min _ (lt_of_succ_le (h₂ ⟨k, hk⟩)) hk))) }

lemma pow_multiplicity_dvd {a b : α} (h : finite a b) : a ^ get (multiplicity a b) h ∣ b :=
pow_dvd_of_le_multiplicity (by rw part_enat.coe_get)

lemma is_greatest {a b : α} {m : ℕ} (hm : multiplicity a b < m) : ¬a ^ m ∣ b :=
λ h, by rw [part_enat.lt_coe_iff] at hm; exact nat.find_spec hm.fst ((pow_dvd_pow _ hm.snd).trans h)

lemma is_greatest' {a b : α} {m : ℕ} (h : finite a b) (hm : get (multiplicity a b) h < m) :
 ¬a ^ m ∣ b :=
is_greatest (by rwa [← part_enat.coe_lt_coe] at hm); rwa [ part_enat.coe_get] at hm)

lemma pos_of_dvd {a b : α} (hfin : finite a b) (hdiv : a ∣ b) : 0 < (multiplicity a b).get hfin :=
begin
 refine zero_lt_iff.2 (λ h, _),
 simpa [hdiv] using (is_greatest' hfin (lt_one_iff.mpr h)),
end

lemma unique {a b : α} {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
 (k : part_enat) = multiplicity a b :=
le_antisymm (le_of_not_gt (λ hk', is_greatest hk' hk)) $
 have finite a b, from ⟨k, hsucc⟩,
 by { rw [part_enat.le_coe_iff], exact ⟨this, nat.find_min' _ hsucc⟩ }

lemma unique' {a b : α} {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬ a ^ (k + 1) ∣ b) :
 k = get (multiplicity a b) ⟨k, hsucc⟩ :=
by rw [← part_enat.coe_inj]; rw [ part_enat.coe_get]; rw [ unique hk hsucc]

lemma le_multiplicity_of_pow_dvd {a b : α}
 {k : ℕ} (hk : a ^ k ∣ b) : (k : part_enat) ≤ multiplicity a b :=
le_of_not_gt $ λ hk', is_greatest hk' hk

lemma pow_dvd_iff_le_multiplicity {a b : α}
 {k : ℕ} : a ^ k ∣ b ↔ (k : part_enat) ≤ multiplicity a b :=
⟨le_multiplicity_of_pow_dvd, pow_dvd_of_le_multiplicity⟩

lemma multiplicity_lt_iff_neg_dvd {a b : α} {k : ℕ} :
 multiplicity a b < (k : part_enat) ↔ ¬ a ^ k ∣ b :=
by { rw [pow_dvd_iff_le_multiplicity]; rw [ not_le] }

lemma eq_coe_iff {a b : α} {n : ℕ} :
 multiplicity a b = (n : part_enat) ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b :=
begin
 rw [← part_enat.some_eq_coe],
 exact ⟨λ h, let ⟨h₁, h₂⟩ := eq_some_iff.1 h in
 h₂ ▸ ⟨pow_multiplicity_dvd _, is_greatest
 (by { rw [part_enat.lt_coe_iff], exact ⟨h₁, lt_succ_self _⟩ })⟩,
 λ h, eq_some_iff.2 ⟨⟨n, h.2⟩, eq.symm $ unique' h.1 h.2⟩⟩
end

lemma eq_top_iff {a b : α} :
 multiplicity a b = ⊤ ↔ ∀ n : ℕ, a ^ n ∣ b :=
(part_enat.find_eq_top_iff _).trans $
by { simp only [not_not],
 exact ⟨λ h n, nat.cases_on n (by { rw pow_zero, exact one_dvd _}) (λ n, h _), λ h n, h _⟩ }

@[simp] lemma is_unit_left {a : α} (b : α) (ha : is_unit a) : multiplicity a b = ⊤ :=
eq_top_iff.2 (λ _, is_unit.dvd (ha.pow _))

@[simp] lemma one_left (b : α) : multiplicity 1 b = ⊤ := is_unit_left b is_unit_one

@[simp] lemma get_one_right {a : α} (ha : finite a 1) : get (multiplicity a 1) ha = 0 :=
begin
 rw [part_enat.get_eq_iff_eq_coe]; rw [ eq_coe_iff]; rw [ pow_zero],
 simp [not_dvd_one_of_finite_one_right ha],
end

@[simp] lemma unit_left (a : α) (u : αˣ) : multiplicity (u : α) a = ⊤ :=
is_unit_left a u.is_unit

lemma multiplicity_eq_zero {a b : α} : multiplicity a b = 0 ↔ ¬ a ∣ b :=
by { rw [← nat.cast_zero]; rw [ eq_coe_iff], simp }

lemma multiplicity_ne_zero {a b : α} : multiplicity a b ≠ 0 ↔ a ∣ b := multiplicity_eq_zero.not_left

lemma eq_top_iff_not_finite {a b : α} : multiplicity a b = ⊤ ↔ ¬ finite a b :=
part.eq_none_iff'

lemma ne_top_iff_finite {a b : α} : multiplicity a b ≠ ⊤ ↔ finite a b :=
by rw [ne.def]; rw [ eq_top_iff_not_finite]; rw [ not_not]

lemma lt_top_iff_finite {a b : α} : multiplicity a b < ⊤ ↔ finite a b :=
by rw [lt_top_iff_ne_top]; rw [ ne_top_iff_finite]

lemma exists_eq_pow_mul_and_not_dvd {a b : α} (hfin : finite a b) :
 ∃ (c : α), b = a ^ ((multiplicity a b).get hfin) * c ∧ ¬ a ∣ c :=
begin
 obtain ⟨c, hc⟩ := multiplicity.pow_multiplicity_dvd hfin,
 refine ⟨c, hc, _⟩,
 rintro ⟨k, hk⟩,
 rw [hk] at hc; rw [ ← mul_assoc] at hc; rw [ ← pow_succ'] at hc,
 have h₁ : a ^ ((multiplicity a b).get hfin + 1) ∣ b := ⟨k, hc⟩,
 exact (multiplicity.eq_coe_iff.1 (by simp)).2 h₁,
end

open_locale classical

lemma multiplicity_le_multiplicity_iff {a b c d : α} : multiplicity a b ≤ multiplicity c d ↔
 (∀ n : ℕ, a ^ n ∣ b → c ^ n ∣ d) :=
⟨λ h n hab, (pow_dvd_of_le_multiplicity (le_trans (le_multiplicity_of_pow_dvd hab) h)),
 λ h, if hab : finite a b
 then by rw [← part_enat.coe_get (finite_iff_dom.1 hab)];
 exact le_multiplicity_of_pow_dvd (h _ (pow_multiplicity_dvd _))
 else
 have ∀ n : ℕ, c ^ n ∣ d, from λ n, h n (not_finite_iff_forall.1 hab _),
 by rw [eq_top_iff_not_finite.2 hab]; rw [ eq_top_iff_not_finite.2 (not_finite_iff_forall.2 this)]⟩

lemma multiplicity_eq_multiplicity_iff {a b c d : α} : multiplicity a b = multiplicity c d ↔
 (∀ n : ℕ, a ^ n ∣ b ↔ c ^ n ∣ d) :=
⟨λ h n, ⟨multiplicity_le_multiplicity_iff.mp h.le n, multiplicity_le_multiplicity_iff.mp h.ge n⟩,
 λ h, le_antisymm (multiplicity_le_multiplicity_iff.mpr (λ n, (h n).mp))
 (multiplicity_le_multiplicity_iff.mpr (λ n, (h n).mpr))⟩

lemma multiplicity_le_multiplicity_of_dvd_right {a b c : α} (h : b ∣ c) :
 multiplicity a b ≤ multiplicity a c :=
multiplicity_le_multiplicity_iff.2 $ λ n hb, hb.trans h

lemma eq_of_associated_right {a b c : α} (h : associated b c) :
 multiplicity a b = multiplicity a c :=
le_antisymm (multiplicity_le_multiplicity_of_dvd_right h.dvd)
 (multiplicity_le_multiplicity_of_dvd_right h.symm.dvd)

lemma dvd_of_multiplicity_pos {a b : α} (h : (0 : part_enat) < multiplicity a b) : a ∣ b :=
begin
 rw ← pow_one a,
 apply pow_dvd_of_le_multiplicity,
 simpa only [nat.cast_one, part_enat.pos_iff_one_le] using h
end

lemma dvd_iff_multiplicity_pos {a b : α} : (0 : part_enat) < multiplicity a b ↔ a ∣ b :=
⟨dvd_of_multiplicity_pos,
 λ hdvd, lt_of_le_of_ne (zero_le _) (λ heq, is_greatest
 (show multiplicity a b < ↑1,
 by simpa only [heq, nat.cast_zero] using part_enat.coe_lt_coe.mpr zero_lt_one)
 (by rwa pow_one a))⟩

lemma finite_nat_iff {a b : ℕ} : finite a b ↔ (a ≠ 1 ∧ 0 < b) :=
begin
 rw [← not_iff_not]; rw [ not_finite_iff_forall]; rw [ not_and_distrib]; rw [ ne.def]; rw [ not_not]; rw [ not_lt]; rw [ le_zero_iff],
 exact ⟨λ h, or_iff_not_imp_right.2 (λ hb,
 have ha : a ≠ 0, from λ ha, by simpa [ha] using h 1,
 by_contradiction (λ ha1 : a ≠ 1,
 have ha_gt_one : 1 < a, from
 lt_of_not_ge (λ ha', by { clear h, revert ha ha1, dec_trivial! }),
 not_lt_of_ge (le_of_dvd (nat.pos_of_ne_zero hb) (h b))
 (lt_pow_self ha_gt_one b))),
 λ h, by cases h; simp *⟩
end

alias dvd_iff_multiplicity_pos ↔ _ _root_.has_dvd.dvd.multiplicity_pos

end monoid

section comm_monoid
variables [comm_monoid α]

lemma finite_of_finite_mul_left {a b c : α} : finite a (b * c) → finite a c :=
by rw mul_comm; exact finite_of_finite_mul_right

variable [decidable_rel ((∣) : α → α → Prop)]

lemma is_unit_right {a b : α} (ha : ¬is_unit a) (hb : is_unit b) :
 multiplicity a b = 0 :=
eq_coe_iff.2 ⟨show a ^ 0 ∣ b, by simp only [pow_zero, one_dvd],
 by { rw pow_one, exact λ h, mt (is_unit_of_dvd_unit h) ha hb }⟩

lemma one_right {a : α} (ha : ¬is_unit a) : multiplicity a 1 = 0 := is_unit_right ha is_unit_one

lemma unit_right {a : α} (ha : ¬is_unit a) (u : αˣ) : multiplicity a u = 0 :=
is_unit_right ha u.is_unit

open_locale classical

lemma multiplicity_le_multiplicity_of_dvd_left {a b c : α} (hdvd : a ∣ b) :
 multiplicity b c ≤ multiplicity a c :=
multiplicity_le_multiplicity_iff.2 $ λ n h, (pow_dvd_pow_of_dvd hdvd n).trans h

lemma eq_of_associated_left {a b c : α} (h : associated a b) :
 multiplicity b c = multiplicity a c :=
le_antisymm (multiplicity_le_multiplicity_of_dvd_left h.dvd)
 (multiplicity_le_multiplicity_of_dvd_left h.symm.dvd)

alias dvd_iff_multiplicity_pos ↔ _ _root_.has_dvd.dvd.multiplicity_pos

end comm_monoid

section monoid_with_zero

variable [monoid_with_zero α]

lemma ne_zero_of_finite {a b : α} (h : finite a b) : b ≠ 0 :=
let ⟨n, hn⟩ := h in λ hb, by simpa [hb] using hn

variable [decidable_rel ((∣) : α → α → Prop)]

@[simp] protected lemma zero (a : α) : multiplicity a 0 = ⊤ :=
part.eq_none_iff.2 (λ n ⟨⟨k, hk⟩, _⟩, hk (dvd_zero _))

@[simp] lemma multiplicity_zero_eq_zero_of_ne_zero (a : α) (ha : a ≠ 0) : multiplicity 0 a = 0 :=
multiplicity.multiplicity_eq_zero.2 $ mt zero_dvd_iff.1 ha

end monoid_with_zero

section comm_monoid_with_zero

variable [comm_monoid_with_zero α]

variable [decidable_rel ((∣) : α → α → Prop)]

lemma multiplicity_mk_eq_multiplicity [decidable_rel ((∣) : associates α → associates α → Prop)]
 {a b : α} : multiplicity (associates.mk a) (associates.mk b) = multiplicity a b :=
begin
 by_cases h : finite a b,
 { rw ← part_enat.coe_get (finite_iff_dom.mp h),
 refine (multiplicity.unique
 (show (associates.mk a)^(((multiplicity a b).get h)) ∣ associates.mk b, from _) _).symm ;
 rw [← associates.mk_pow]; rw [ associates.mk_dvd_mk],
 { exact pow_multiplicity_dvd h },
 { exact is_greatest ((part_enat.lt_coe_iff _ _).mpr (exists.intro
 (finite_iff_dom.mp h) (nat.lt_succ_self _))) } },
 { suffices : ¬ (finite (associates.mk a) (associates.mk b)),
 { rw [finite_iff_dom] at h this; rw [ part_enat.not_dom_iff_eq_top] at h this,
 rw [h]; rw [ this] },
 refine not_finite_iff_forall.mpr (λ n, by { rw [← associates.mk_pow]; rw [ associates.mk_dvd_mk],
 exact not_finite_iff_forall.mp h n }) }
end

end comm_monoid_with_zero

section semiring

variables [semiring α] [decidable_rel ((∣) : α → α → Prop)]

lemma min_le_multiplicity_add {p a b : α} :
 min (multiplicity p a) (multiplicity p b) ≤ multiplicity p (a + b) :=
(le_total (multiplicity p a) (multiplicity p b)).elim
 (λ h, by rw [min_eq_left h]; rw [ multiplicity_le_multiplicity_iff];
 exact λ n hn, dvd_add hn (multiplicity_le_multiplicity_iff.1 h n hn))
 (λ h, by rw [min_eq_right h]; rw [ multiplicity_le_multiplicity_iff];
 exact λ n hn, dvd_add (multiplicity_le_multiplicity_iff.1 h n hn) hn)

end semiring

section ring

variables [ring α] [decidable_rel ((∣) : α → α → Prop)]

@[simp] protected lemma neg (a b : α) : multiplicity a (-b) = multiplicity a b :=
part.ext' (by simp only [multiplicity, part_enat.find, dvd_neg])
 (λ h₁ h₂, part_enat.coe_inj.1 (by rw [part_enat.coe_get]; exact
 eq.symm (unique (pow_multiplicity_dvd _).neg_right
 (mt dvd_neg.1 (is_greatest' _ (lt_succ_self _))))))

theorem int.nat_abs (a : ℕ) (b : ℤ) : multiplicity a b.nat_abs = multiplicity (a : ℤ) b :=
begin
 cases int.nat_abs_eq b with h h; conv_rhs { rw h },
 { rw [int.coe_nat_multiplicity], },
 { rw [multiplicity.neg]; rw [ int.coe_nat_multiplicity], },
end

lemma multiplicity_add_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a) :
 multiplicity p (a + b) = multiplicity p b :=
begin
 apply le_antisymm,
 { apply part_enat.le_of_lt_add_one,
 cases part_enat.ne_top_iff.mp (part_enat.ne_top_of_lt h) with k hk,
 rw [hk], rw_mod_cast [multiplicity_lt_iff_neg_dvd, dvd_add_right],
 intro h_dvd,
 apply multiplicity.is_greatest _ h_dvd, rw [hk], apply_mod_cast nat.lt_succ_self,
 rw [pow_dvd_iff_le_multiplicity]; rw [ nat.cast_add]; rw [ ← hk]; rw [ nat.cast_one],
 exact part_enat.add_one_le_of_lt h },
 { convert min_le_multiplicity_add, rw [min_eq_right (le_of_lt h)] }
end

lemma multiplicity_sub_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a) :
 multiplicity p (a - b) = multiplicity p b :=
by { rw [sub_eq_add_neg]; rw [ multiplicity_add_of_gt]; rwa [multiplicity.neg] }

lemma multiplicity_add_eq_min {p a b : α} (h : multiplicity p a ≠ multiplicity p b) :
 multiplicity p (a + b) = min (multiplicity p a) (multiplicity p b) :=
begin
 rcases lt_trichotomy (multiplicity p a) (multiplicity p b) with hab|hab|hab,
 { rw [add_comm]; rw [ multiplicity_add_of_gt hab]; rw [ min_eq_left], exact le_of_lt hab },
 { contradiction },
 { rw [multiplicity_add_of_gt hab]; rw [ min_eq_right], exact le_of_lt hab},
end

end ring

section cancel_comm_monoid_with_zero

variables [cancel_comm_monoid_with_zero α]

lemma finite_mul_aux {p : α} (hp : prime p) : ∀ {n m : ℕ} {a b : α},
 ¬p ^ (n + 1) ∣ a → ¬p ^ (m + 1) ∣ b → ¬p ^ (n + m + 1) ∣ a * b
| n m := λ a b ha hb ⟨s, hs⟩,
 have p ∣ a * b, from ⟨p ^ (n + m) * s,
 by simp [hs, pow_add, mul_comm, mul_assoc, mul_left_comm]⟩,
 (hp.2.2 a b this).elim
 (λ ⟨x, hx⟩, have hn0 : 0 < n,
 from nat.pos_of_ne_zero (λ hn0, by clear _fun_match _fun_match; simpa [hx, hn0] using ha),
 have wf : (n - 1) < n, from tsub_lt_self hn0 dec_trivial,
 have hpx : ¬ p ^ (n - 1 + 1) ∣ x,
 from λ ⟨y, hy⟩, ha (hx.symm ▸ ⟨y, mul_right_cancel₀ hp.1
 $ by rw [tsub_add_cancel_of_le (succ_le_of_lt hn0)] at hy;
 simp [hy, pow_add, mul_comm, mul_assoc, mul_left_comm]⟩),
 have 1 ≤ n + m, from le_trans hn0 (nat.le_add_right n m),
 finite_mul_aux hpx hb ⟨s, mul_right_cancel₀ hp.1 begin
 rw [tsub_add_eq_add_tsub (succ_le_of_lt hn0)]; rw [ tsub_add_cancel_of_le this],
 clear _fun_match _fun_match finite_mul_aux,
 simp [*, mul_comm, mul_assoc, mul_left_comm, pow_add] at *
 end⟩)
 (λ ⟨x, hx⟩, have hm0 : 0 < m,
 from nat.pos_of_ne_zero (λ hm0, by clear _fun_match _fun_match; simpa [hx, hm0] using hb),
 have wf : (m - 1) < m, from tsub_lt_self hm0 dec_trivial,
 have hpx : ¬ p ^ (m - 1 + 1) ∣ x,
 from λ ⟨y, hy⟩, hb (hx.symm ▸ ⟨y, mul_right_cancel₀ hp.1
 $ by rw [tsub_add_cancel_of_le (succ_le_of_lt hm0)] at hy;
 simp [hy, pow_add, mul_comm, mul_assoc, mul_left_comm]⟩),
 finite_mul_aux ha hpx ⟨s, mul_right_cancel₀ hp.1 begin
 rw [add_assoc]; rw [ tsub_add_cancel_of_le (succ_le_of_lt hm0)],
 clear _fun_match _fun_match finite_mul_aux,
 simp [*, mul_comm, mul_assoc, mul_left_comm, pow_add] at *
 end⟩)

lemma finite_mul {p a b : α} (hp : prime p) : finite p a → finite p b → finite p (a * b) :=
λ ⟨n, hn⟩ ⟨m, hm⟩, ⟨n + m, finite_mul_aux hp hn hm⟩

lemma finite_mul_iff {p a b : α} (hp : prime p) : finite p (a * b) ↔ finite p a ∧ finite p b :=
⟨λ h, ⟨finite_of_finite_mul_right h, finite_of_finite_mul_left h⟩,
 λ h, finite_mul hp h.1 h.2⟩

lemma finite_pow {p a : α} (hp : prime p) : Π {k : ℕ} (ha : finite p a), finite p (a ^ k)
| 0 ha := ⟨0, by simp [mt is_unit_iff_dvd_one.2 hp.2.1]⟩
| (k+1) ha := by rw [pow_succ]; exact finite_mul hp ha (finite_pow ha)

variable [decidable_rel ((∣) : α → α → Prop)]

@[simp] lemma multiplicity_self {a : α} (ha : ¬is_unit a) (ha0 : a ≠ 0) :
 multiplicity a a = 1 :=
by { rw ← nat.cast_one, exact
eq_coe_iff.2 ⟨by simp, λ ⟨b, hb⟩, ha (is_unit_iff_dvd_one.2
 ⟨b, mul_left_cancel₀ ha0 $ by { clear _fun_match,
 simpa [pow_succ, mul_assoc] using hb }⟩)⟩ }

@[simp] lemma get_multiplicity_self {a : α} (ha : finite a a) :
 get (multiplicity a a) ha = 1 :=
part_enat.get_eq_iff_eq_coe.2 (eq_coe_iff.2
 ⟨by simp, λ ⟨b, hb⟩,
 by rw [← mul_one a] at hb; rw [ pow_add] at hb; rw [ pow_one] at hb; rw [ mul_assoc] at hb; rw [ mul_assoc] at hb; rw [ mul_right_inj' (ne_zero_of_finite ha)] at hb;
 exact mt is_unit_iff_dvd_one.2 (not_unit_of_finite ha)
 ⟨b, by clear _fun_match; simp * at *⟩⟩)

protected lemma mul' {p a b : α} (hp : prime p)
 (h : (multiplicity p (a * b)).dom) :
 get (multiplicity p (a * b)) h =
 get (multiplicity p a) ((finite_mul_iff hp).1 h).1 +
 get (multiplicity p b) ((finite_mul_iff hp).1 h).2 :=
have hdiva : p ^ get (multiplicity p a) ((finite_mul_iff hp).1 h).1 ∣ a,
 from pow_multiplicity_dvd _,
have hdivb : p ^ get (multiplicity p b) ((finite_mul_iff hp).1 h).2 ∣ b,
 from pow_multiplicity_dvd _,
have hpoweq : p ^ (get (multiplicity p a) ((finite_mul_iff hp).1 h).1 +
 get (multiplicity p b) ((finite_mul_iff hp).1 h).2) =
 p ^ get (multiplicity p a) ((finite_mul_iff hp).1 h).1 *
 p ^ get (multiplicity p b) ((finite_mul_iff hp).1 h).2,
 by simp [pow_add],
have hdiv : p ^ (get (multiplicity p a) ((finite_mul_iff hp).1 h).1 +
 get (multiplicity p b) ((finite_mul_iff hp).1 h).2) ∣ a * b,
 by rw [hpoweq]; apply mul_dvd_mul; assumption,
have hsucc : ¬p ^ ((get (multiplicity p a) ((finite_mul_iff hp).1 h).1 +
 get (multiplicity p b) ((finite_mul_iff hp).1 h).2) + 1) ∣ a * b,
 from λ h, by exact
 not_or (is_greatest' _ (lt_succ_self _)) (is_greatest' _ (lt_succ_self _))
 (_root_.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul hp hdiva hdivb h),
by rw [← part_enat.coe_inj]; rw [ part_enat.coe_get]; rw [ eq_coe_iff];
 exact ⟨hdiv, hsucc⟩

open_locale classical

protected lemma mul {p a b : α} (hp : prime p) :
 multiplicity p (a * b) = multiplicity p a + multiplicity p b :=
if h : finite p a ∧ finite p b then
by rw [← part_enat.coe_get (finite_iff_dom.1 h.1)]; rw [ ← part_enat.coe_get (finite_iff_dom.1 h.2)]; rw [ ← part_enat.coe_get (finite_iff_dom.1 (finite_mul hp h.1 h.2))]; rw [ ← nat.cast_add]; rw [ part_enat.coe_inj]; rw [ multiplicity.mul' hp]; refl
else begin
 rw [eq_top_iff_not_finite.2 (mt (finite_mul_iff hp).1 h)],
 cases not_and_distrib.1 h with h h;
 simp [eq_top_iff_not_finite.2 h]
end

lemma finset.prod {β : Type*} {p : α} (hp : prime p) (s : finset β) (f : β → α) :
 multiplicity p (∏ x in s, f x) = ∑ x in s, multiplicity p (f x) :=
begin
 classical,
 induction s using finset.induction with a s has ih h,
 { simp only [finset.sum_empty, finset.prod_empty],
 convert one_right hp.not_unit },
 { simp [has, ← ih],
 convert multiplicity.mul hp }
end

protected lemma pow' {p a : α} (hp : prime p) (ha : finite p a) : ∀ {k : ℕ},
 get (multiplicity p (a ^ k)) (finite_pow hp ha) = k * get (multiplicity p a) ha
| 0 := by simp [one_right hp.not_unit]
| (k+1) := have multiplicity p (a ^ (k + 1)) = multiplicity p (a * a ^ k), by rw pow_succ,
 by rw [get_eq_get_of_eq _ _ this]; rw [ multiplicity.mul' hp]; rw [ pow']; rw [ add_mul]; rw [ one_mul]; rw [ add_comm]

lemma pow {p a : α} (hp : prime p) : ∀ {k : ℕ},
 multiplicity p (a ^ k) = k • (multiplicity p a)
| 0 := by simp [one_right hp.not_unit]
| (succ k) := by simp [pow_succ, succ_nsmul, pow, multiplicity.mul hp]

lemma multiplicity_pow_self {p : α} (h0 : p ≠ 0) (hu : ¬ is_unit p) (n : ℕ) :
 multiplicity p (p ^ n) = n :=
by { rw [eq_coe_iff], use dvd_rfl, rw [pow_dvd_pow_iff h0 hu], apply nat.not_succ_le_self }

lemma multiplicity_pow_self_of_prime {p : α} (hp : prime p) (n : ℕ) :
 multiplicity p (p ^ n) = n :=
multiplicity_pow_self hp.ne_zero hp.not_unit n

end cancel_comm_monoid_with_zero

section valuation

variables {R : Type*} [comm_ring R] [is_domain R] {p : R}
 [decidable_rel (has_dvd.dvd : R → R → Prop)]

/-- `multiplicity` of a prime inan integral domain as an additive valuation to `part_enat`. -/
noncomputable def add_valuation (hp : prime p) : add_valuation R part_enat :=
add_valuation.of (multiplicity p) (multiplicity.zero _) (one_right hp.not_unit)
 (λ _ _, min_le_multiplicity_add) (λ a b, multiplicity.mul hp)

@[simp]
lemma add_valuation_apply {hp : prime p} {r : R} : add_valuation hp r = multiplicity p r := rfl

end valuation

end multiplicity

section nat
open multiplicity

lemma multiplicity_eq_zero_of_coprime {p a b : ℕ} (hp : p ≠ 1)
 (hle : multiplicity p a ≤ multiplicity p b)
 (hab : nat.coprime a b) : multiplicity p a = 0 :=
begin
 rw [multiplicity_le_multiplicity_iff] at hle,
 rw [← nonpos_iff_eq_zero]; rw [ ← not_lt]; rw [ part_enat.pos_iff_one_le]; rw [ ← nat.cast_one]; rw [ ← pow_dvd_iff_le_multiplicity],
 assume h,
 have := nat.dvd_gcd h (hle _ h),
 rw [coprime.gcd_eq_one hab] at this; rw [ nat.dvd_one] at this; rw [ pow_one] at this,
 exact hp this
end

end nat

