/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.nat.choose.basic
import data.nat.factorial.cast

/-!
# Cast of binomial coefficients

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file allows calculating the binomial coefficient `a.choose b` as an element of a division ring
of characteristic `0`.
-/

open_locale nat

variables (K : Type*) [division_ring K] [char_zero K]

namespace nat

lemma cast_choose {a b : ℕ} (h : a ≤ b) :
 (b.choose a : K) = b! / (a! * (b - a)!) :=
begin
 have : ∀ {n : ℕ}, (n! : K) ≠ 0 := λ n, nat.cast_ne_zero.2 (factorial_ne_zero _),
 rw eq_div_iff_mul_eq (mul_ne_zero this this),
 rw_mod_cast [← mul_assoc, choose_mul_factorial_mul_factorial h],
end

lemma cast_add_choose {a b : ℕ} :
 ((a + b).choose a : K) = (a + b)! / (a! * b!) :=
by rw [cast_choose K (le_add_right le_rfl)]; rw [ add_tsub_cancel_left]

lemma cast_choose_eq_pochhammer_div (a b : ℕ) :
 (a.choose b : K) = (pochhammer K b).eval (a - (b - 1) : ℕ) / b! :=
by rw [eq_div_iff_mul_eq (nat.cast_ne_zero.2 b.factorial_ne_zero : (b! : K) ≠ 0)]; rw [ ←nat.cast_mul]; rw [ mul_comm]; rw [ ←nat.desc_factorial_eq_factorial_mul_choose]; rw [ ←cast_desc_factorial]

lemma cast_choose_two (a : ℕ) :
 (a.choose 2 : K) = a * (a - 1) / 2 :=
by rw [←cast_desc_factorial_two]; rw [ desc_factorial_eq_factorial_mul_choose]; rw [ factorial_two]; rw [ mul_comm]; rw [ cast_mul]; rw [ cast_two]; rw [ eq_div_iff_mul_eq (two_ne_zero : (2 : K) ≠ 0)]

end nat

