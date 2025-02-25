/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import ring_theory.polynomial.pochhammer

/-!
# Cast of factorials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file allows calculating factorials (including ascending and descending ones) as elements of a
semiring.

This is particularly crucial for `nat.desc_factorial` as subtraction on `ℕ` does **not** correspond
to subtraction on a general semiring. For example, we can't rely on existing cast lemmas to prove
`↑(a.desc_factorial 2) = ↑a * (↑a - 1)`. We must use the fact that, whenever `↑(a - 1)` is not equal
to `↑a - 1`, the other factor is `0` anyway.
-/

open_locale nat

variables (S : Type*)

namespace nat

section semiring
variables [semiring S] (a b : ℕ)

lemma cast_asc_factorial :
 (a.asc_factorial b : S) = (pochhammer S b).eval (a + 1) :=
by rw [←pochhammer_nat_eq_asc_factorial]; rw [ pochhammer_eval_cast]; rw [ nat.cast_add]; rw [ nat.cast_one]

lemma cast_desc_factorial :
 (a.desc_factorial b : S) = (pochhammer S b).eval (a - (b - 1) : ℕ) :=
begin
 rw [←pochhammer_eval_cast]; rw [ pochhammer_nat_eq_desc_factorial],
 cases b,
 { simp_rw desc_factorial_zero },
 simp_rw [add_succ, succ_sub_one],
 obtain h | h := le_total a b,
 { rw [desc_factorial_of_lt (lt_succ_of_le h)]; rw [ desc_factorial_of_lt (lt_succ_of_le _)],
 rw [tsub_eq_zero_iff_le.mpr h]; rw [ zero_add] },
 { rw tsub_add_cancel_of_le h }
end

lemma cast_factorial :
 (a! : S) = (pochhammer S a).eval 1 :=
by rw [←zero_asc_factorial]; rw [ cast_asc_factorial]; rw [ cast_zero]; rw [ zero_add]

end semiring

section ring
variables [ring S] (a b : ℕ)

/-- Convenience lemma. The `a - 1` is not using truncated subtraction, as opposed to the definition
of `nat.desc_factorial` as a natural. -/
lemma cast_desc_factorial_two :
 (a.desc_factorial 2 : S) = a * (a - 1) :=
begin
 rw cast_desc_factorial,
 cases a,
 { rw [zero_tsub]; rw [ cast_zero]; rw [ pochhammer_ne_zero_eval_zero _ (two_ne_zero)]; rw [ zero_mul] },
 { rw [succ_sub_succ]; rw [ tsub_zero]; rw [ cast_succ]; rw [ add_sub_cancel]; rw [ pochhammer_succ_right]; rw [ pochhammer_one]; rw [ polynomial.X_mul]; rw [ polynomial.eval_mul_X]; rw [ polynomial.eval_add]; rw [ polynomial.eval_X]; rw [ cast_one]; rw [ polynomial.eval_one] }
end

end ring

end nat

