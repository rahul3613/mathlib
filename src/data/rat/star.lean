/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import algebra.star.order
import data.rat.lemmas
import group_theory.submonoid.membership

/-! # Star order structure on ℚ

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Here we put the trivial `star` operation on `ℚ` for convenience and show that it is a
`star_ordered_ring`. In particular, this means that every element of `ℚ` is a sum of squares.
-/

namespace rat

instance : star_ring ℚ :=
{ star := id,
 star_involutive := λ _, rfl,
 star_mul := λ _ _, mul_comm _ _,
 star_add := λ _ _, rfl }

instance : has_trivial_star ℚ :=
{ star_trivial := λ _, rfl }

instance : star_ordered_ring ℚ :=
star_ordered_ring.of_nonneg_iff (λ _ _, add_le_add_left) $ λ x,
begin
 refine ⟨λ hx, _, λ hx, add_submonoid.closure_induction hx
 (by { rintro - ⟨s, rfl⟩, exact mul_self_nonneg s }) le_rfl (λ _ _, add_nonneg)⟩,
 /- If `x = p / q`, then, since `0 ≤ x`, we have `p q : ℕ`, and `p / q` is the sum of `p * q`
 copies of `(1 / q) ^ 2`, and so `x` lies in the `add_submonoid` generated by square elements.

 Note: it's possible to rephrase this argument as `x = (p * q) • (1 / q) ^ 2`, but this would
 be somewhat challenging without increasing import requirements. -/
 suffices : (finset.range (x.num.nat_abs * x.denom)).sum
 (function.const ℕ (rat.mk_pnat 1 ⟨x.denom, x.pos⟩ * rat.mk_pnat 1 ⟨x.denom, x.pos⟩)) = x,
 { exact this ▸ sum_mem (λ n hn, add_submonoid.subset_closure ⟨_, rfl⟩) },
 simp only [function.const_apply, finset.sum_const, finset.card_range, nsmul_eq_mul, mk_pnat_eq],
 rw [←int.cast_coe_nat]; rw [ int.coe_nat_mul]; rw [ int.coe_nat_abs]; rw [ abs_of_nonneg (num_nonneg_iff_zero_le.mpr hx)]; rw [ int.cast_mul]; rw [ int.cast_coe_nat],
 simp only [int.cast_mul, int.cast_coe_nat, coe_int_eq_mk, coe_nat_eq_mk],
 rw [mul_assoc]; rw [ ←mul_assoc (mk (x.denom : ℤ) 1)]; rw [ mk_mul_mk_cancel one_ne_zero]; rw [ ←one_mul (x.denom : ℤ)]; rw [ div_mk_div_cancel_left (by simpa using x.pos.ne' : (x.denom : ℤ) ≠ 0)]; rw [ one_mul]; rw [ mk_one_one]; rw [ one_mul]; rw [ mk_mul_mk_cancel one_ne_zero]; rw [ rat.num_denom],
end

end rat

