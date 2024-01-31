/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.nat.modeq
import tactic.ring

/-!

# Congruences modulo an integer

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the equivalence relation `a ≡ b [ZMOD n]` on the integers, similarly to how
`data.nat.modeq` defines them for the natural numbers. The notation is short for `n.modeq a b`,
which is defined to be `a % n = b % n` for integers `a b n`.

## Tags

modeq, congruence, mod, MOD, modulo, integers

-/

namespace int

/-- `a ≡ b [ZMOD n]` when `a % n = b % n`. -/
@[derive decidable]
def modeq (n a b : ℤ) := a % n = b % n

notation a ` ≡ `:50 b ` [ZMOD `:50 n `]`:0 := modeq n a b

variables {m n a b c d : ℤ}

namespace modeq

@[refl] protected theorem refl (a : ℤ) : a ≡ a [ZMOD n] := @rfl _ _

protected theorem rfl : a ≡ a [ZMOD n] := modeq.refl _

instance : is_refl _ (modeq n) := ⟨modeq.refl⟩

@[symm] protected theorem symm : a ≡ b [ZMOD n] → b ≡ a [ZMOD n] := eq.symm

@[trans] protected theorem trans : a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n] := eq.trans

protected lemma eq : a ≡ b [ZMOD n] → a % n = b % n := id

end modeq

lemma modeq_comm : a ≡ b [ZMOD n] ↔ b ≡ a [ZMOD n] := ⟨modeq.symm, modeq.symm⟩

lemma coe_nat_modeq_iff {a b n : ℕ} : a ≡ b [ZMOD n] ↔ a ≡ b [MOD n] :=
by unfold modeq nat.modeq; rw ← int.coe_nat_eq_coe_nat_iff; simp [coe_nat_mod]

theorem modeq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a :=
by rw [modeq, zero_mod, dvd_iff_mod_eq_zero]

lemma _root_.has_dvd.dvd.modeq_zero_int (h : n ∣ a) : a ≡ 0 [ZMOD n] := modeq_zero_iff_dvd.2 h
lemma _root_.has_dvd.dvd.zero_modeq_int (h : n ∣ a) : 0 ≡ a [ZMOD n] := h.modeq_zero_int.symm

theorem modeq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a :=
by rw [modeq, eq_comm];
   simp [mod_eq_mod_iff_mod_sub_eq_zero, dvd_iff_mod_eq_zero]

theorem modeq_iff_add_fac {a b n : ℤ} : a ≡ b [ZMOD n] ↔ ∃ t, b = a + n * t :=
begin
  rw modeq_iff_dvd,
  exact exists_congr (λ t, sub_eq_iff_eq_add'),
end

alias modeq_iff_dvd ↔ modeq.dvd modeq_of_dvd

theorem mod_modeq (a n) : a % n ≡ a [ZMOD n] := mod_mod _ _

@[simp] lemma neg_modeq_neg : -a ≡ -b [ZMOD n] ↔ a ≡ b [ZMOD n] :=
by simp [modeq_iff_dvd, dvd_sub_comm]

@[simp] lemma modeq_neg : a ≡ b [ZMOD -n] ↔ a ≡ b [ZMOD n] := by simp [modeq_iff_dvd]

namespace modeq

protected lemma of_dvd (d : m ∣ n) (h : a ≡ b [ZMOD n]) : a ≡ b [ZMOD m] :=
modeq_of_dvd $ d.trans h.dvd

protected theorem mul_left' (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD (c * n)] :=
begin
  obtain hc | rfl | hc := lt_trichotomy c 0,
  { rw [←neg_modeq_neg, ←modeq_neg, ←neg_mul, ←neg_mul, ←neg_mul],
    simp only [modeq, mul_mod_mul_of_pos (neg_pos.2 hc), h.eq] },
  { simp },
  { simp only [modeq, mul_mod_mul_of_pos hc, h.eq] }
end

protected theorem mul_right' (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD (n * c)] :=
by rw [mul_comm a, mul_comm b, mul_comm n]; exact h.mul_left'

protected theorem add (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n] :=
modeq_iff_dvd.2 $ by { convert dvd_add h₁.dvd h₂.dvd, ring }

protected theorem add_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c + a ≡ c + b [ZMOD n] :=
modeq.rfl.add h

protected theorem add_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a + c ≡ b + c [ZMOD n] :=
h.add modeq.rfl

protected theorem add_left_cancel (h₁ : a ≡ b [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
  c ≡ d [ZMOD n] :=
have d - c = b + d - (a + c) - (b - a) := by ring,
modeq_iff_dvd.2 $ by { rw [this], exact dvd_sub h₂.dvd h₁.dvd }

protected theorem add_left_cancel' (c : ℤ) (h : c + a ≡ c + b [ZMOD n]) : a ≡ b [ZMOD n] :=
modeq.rfl.add_left_cancel h

protected theorem add_right_cancel (h₁ : c ≡ d [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
  a ≡ b [ZMOD n] :=
by { rw [add_comm a, add_comm b] at h₂, exact h₁.add_left_cancel h₂ }

protected theorem add_right_cancel' (c : ℤ) (h : a + c ≡ b + c [ZMOD n]) : a ≡ b [ZMOD n] :=
modeq.rfl.add_right_cancel h

protected theorem neg (h : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] :=
h.add_left_cancel (by simp_rw [←sub_eq_add_neg, sub_self])

protected theorem sub (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) :
  a - c ≡ b - d [ZMOD n] :=
by { rw [sub_eq_add_neg, sub_eq_add_neg], exact h₁.add h₂.neg }

protected theorem sub_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c - a ≡ c - b [ZMOD n] :=
modeq.rfl.sub h

protected theorem sub_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a - c ≡ b - c [ZMOD n] :=
h.sub modeq.rfl

protected theorem mul_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD n] :=
h.mul_left'.of_dvd $ dvd_mul_left _ _

protected theorem mul_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n] :=
h.mul_right'.of_dvd $ dvd_mul_right _ _

protected theorem mul (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a * c ≡ b * d [ZMOD n] :=
(h₂.mul_left _).trans (h₁.mul_right _)

protected theorem pow (m : ℕ) (h : a ≡ b [ZMOD n]) : a ^ m ≡ b ^ m [ZMOD n] :=
begin
  induction m with d hd, {refl},
  rw [pow_succ, pow_succ],
  exact h.mul hd,
end

theorem of_mul_left (m : ℤ) (h : a ≡ b [ZMOD m * n]) : a ≡ b [ZMOD n] :=
by rw [modeq_iff_dvd] at *; exact (dvd_mul_left n m).trans h

theorem of_mul_right (m : ℤ) : a ≡ b [ZMOD n * m] → a ≡ b [ZMOD n] :=
mul_comm m n ▸ of_mul_left _

/-- To cancel a common factor `c` from a `modeq` we must divide the modulus `m` by `gcd m c`. -/
lemma cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [ZMOD m]) : a ≡ b [ZMOD m / gcd m c] :=
begin
  let d := gcd m c,
  have hmd := gcd_dvd_left m c,
  have hcd := gcd_dvd_right m c,
  rw modeq_iff_dvd at ⊢ h,
  refine int.dvd_of_dvd_mul_right_of_gcd_one _ _,
  show m / d ∣ c / d * (b - a),
  { rw [mul_comm, ←int.mul_div_assoc (b - a) hcd, sub_mul],
    exact int.div_dvd_div hmd h },
  { rw [gcd_div hmd hcd, nat_abs_of_nat, nat.div_self (gcd_pos_of_ne_zero_left c hm.ne')] }
end

/-- To cancel a common factor `c` from a `modeq` we must divide the modulus `m` by `gcd m c`. -/
lemma cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [ZMOD m]) : a ≡ b [ZMOD m / gcd m c] :=
cancel_right_div_gcd hm $ by simpa [mul_comm] using h

lemma of_div (h : a / c ≡ b / c [ZMOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m) :
  a ≡ b [ZMOD m] :=
by convert h.mul_left'; rwa int.mul_div_cancel'

end modeq

theorem modeq_one : a ≡ b [ZMOD 1] := modeq_of_dvd (one_dvd _)

lemma modeq_sub (a b : ℤ) : a ≡ b [ZMOD a - b] :=
(modeq_of_dvd dvd_rfl).symm

@[simp] lemma modeq_zero_iff : a ≡ b [ZMOD 0] ↔ a = b := by rw [modeq, mod_zero, mod_zero]

@[simp] lemma add_modeq_left : n + a ≡ a [ZMOD n] := modeq.symm $ modeq_iff_dvd.2 $ by simp
@[simp] lemma add_modeq_right : a + n ≡ a [ZMOD n] := modeq.symm $ modeq_iff_dvd.2 $ by simp

lemma modeq_and_modeq_iff_modeq_mul {a b m n : ℤ} (hmn : m.nat_abs.coprime n.nat_abs) :
  a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ (a ≡ b [ZMOD m * n]) :=
⟨λ h, begin
    rw [modeq_iff_dvd, modeq_iff_dvd] at h,
    rw [modeq_iff_dvd, ← nat_abs_dvd, ← dvd_nat_abs,
      coe_nat_dvd, nat_abs_mul],
    refine hmn.mul_dvd_of_dvd_of_dvd _ _;
    rw [← coe_nat_dvd, nat_abs_dvd, dvd_nat_abs]; tauto
  end,
λ h, ⟨h.of_mul_right _, h.of_mul_left _⟩⟩

lemma gcd_a_modeq (a b : ℕ) : (a : ℤ) * nat.gcd_a a b ≡ nat.gcd a b [ZMOD b] :=
by { rw [← add_zero ((a : ℤ) * _), nat.gcd_eq_gcd_ab],
  exact (dvd_mul_right _ _).zero_modeq_int.add_left _ }

theorem modeq_add_fac {a b n : ℤ} (c : ℤ) (ha : a ≡ b [ZMOD n]) : a + n*c ≡ b [ZMOD n] :=
calc a + n*c ≡ b + n*c [ZMOD n] : ha.add_right _
         ... ≡ b + 0 [ZMOD n] : (dvd_mul_right _ _).modeq_zero_int.add_left _
         ... ≡ b [ZMOD n] : by rw add_zero

theorem modeq_add_fac_self {a t n : ℤ} : a + n * t ≡ a [ZMOD n] :=
modeq_add_fac _ modeq.rfl

lemma mod_coprime {a b : ℕ} (hab : nat.coprime a b) : ∃ y : ℤ, a * y ≡ 1 [ZMOD b] :=
⟨ nat.gcd_a a b,
  have hgcd : nat.gcd a b = 1, from nat.coprime.gcd_eq_one hab,
  calc
   ↑a * nat.gcd_a a b ≡ ↑a * nat.gcd_a a b + ↑b * nat.gcd_b a b [ZMOD ↑b] : modeq.symm $
                      modeq_add_fac _ $ modeq.refl _
              ... ≡ 1 [ZMOD ↑b] : by rw [← nat.gcd_eq_gcd_ab, hgcd]; reflexivity ⟩

lemma exists_unique_equiv (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ z : ℤ, 0 ≤ z ∧ z < b ∧ z ≡ a [ZMOD b] :=
⟨ a % b, mod_nonneg _ (ne_of_gt hb),
  have a % b < |b|, from mod_lt _ (ne_of_gt hb),
  by rwa abs_of_pos hb at this,
  by simp [modeq] ⟩

lemma exists_unique_equiv_nat (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ z : ℕ, ↑z < b ∧ ↑z ≡ a [ZMOD b] :=
let ⟨z, hz1, hz2, hz3⟩ := exists_unique_equiv a hb in
⟨z.nat_abs, by split; rw [←of_nat_eq_coe, of_nat_nat_abs_eq_of_nonneg hz1]; assumption⟩


@[simp] lemma mod_mul_right_mod (a b c : ℤ) : a % (b * c) % b = a % b :=
(mod_modeq _ _).of_mul_right _

@[simp] lemma mod_mul_left_mod (a b c : ℤ) : a % (b * c) % c = a % c :=
(mod_modeq _ _).of_mul_left _

end int
