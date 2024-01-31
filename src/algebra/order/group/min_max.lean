/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.order.group.abs
import algebra.order.monoid.min_max

/-!
# `min` and `max` in linearly ordered groups.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

section
variables {α : Type*} [group α] [linear_order α] [covariant_class α α (*) (≤)]

@[simp, to_additive] lemma max_one_div_max_inv_one_eq_self (a : α) :
  max a 1 / max a⁻¹ 1 = a :=
by { rcases le_total a 1 with h|h; simp [h] }

alias max_zero_sub_max_neg_zero_eq_self ← max_zero_sub_eq_self

end

section linear_ordered_comm_group
variables {α : Type*} [linear_ordered_comm_group α] {a b c : α}

@[to_additive min_neg_neg]
lemma min_inv_inv' (a b : α) : min (a⁻¹) (b⁻¹) = (max a b)⁻¹ :=
eq.symm $ @monotone.map_max α αᵒᵈ _ _ has_inv.inv a b $ λ a b, inv_le_inv_iff.mpr

@[to_additive max_neg_neg]
lemma max_inv_inv' (a b : α) : max (a⁻¹) (b⁻¹) = (min a b)⁻¹ :=
eq.symm $ @monotone.map_min α αᵒᵈ _ _ has_inv.inv a b $ λ a b, inv_le_inv_iff.mpr

@[to_additive min_sub_sub_right]
lemma min_div_div_right' (a b c : α) : min (a / c) (b / c) = min a b / c :=
by simpa only [div_eq_mul_inv] using min_mul_mul_right a b (c⁻¹)

@[to_additive max_sub_sub_right]
lemma max_div_div_right' (a b c : α) : max (a / c) (b / c) = max a b / c :=
by simpa only [div_eq_mul_inv] using max_mul_mul_right a b (c⁻¹)

@[to_additive min_sub_sub_left]
lemma min_div_div_left' (a b c : α) : min (a / b) (a / c) = a / max b c :=
by simp only [div_eq_mul_inv, min_mul_mul_left, min_inv_inv']

@[to_additive max_sub_sub_left]
lemma max_div_div_left' (a b c : α) : max (a / b) (a / c) = a / min b c :=
by simp only [div_eq_mul_inv, max_mul_mul_left, max_inv_inv']

end linear_ordered_comm_group

section linear_ordered_add_comm_group
variables {α : Type*} [linear_ordered_add_comm_group α] {a b c : α}

lemma max_sub_max_le_max (a b c d : α) : max a b - max c d ≤ max (a - c) (b - d) :=
begin
  simp only [sub_le_iff_le_add, max_le_iff], split,
  calc a = a - c + c : (sub_add_cancel a c).symm
  ... ≤ max (a - c) (b - d) + max c d : add_le_add (le_max_left _ _) (le_max_left _ _),
  calc b = b - d + d : (sub_add_cancel b d).symm
  ... ≤ max (a - c) (b - d) + max c d : add_le_add (le_max_right _ _) (le_max_right _ _)
end

lemma abs_max_sub_max_le_max (a b c d : α) : |max a b - max c d| ≤ max (|a - c|) (|b - d|) :=
begin
  refine abs_sub_le_iff.2 ⟨_, _⟩,
  { exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _)) },
  { rw [abs_sub_comm a c, abs_sub_comm b d],
    exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _)) }
end

lemma abs_min_sub_min_le_max (a b c d : α) : |min a b - min c d| ≤ max (|a - c|) (|b - d|) :=
by simpa only [max_neg_neg, neg_sub_neg, abs_sub_comm]
  using abs_max_sub_max_le_max (-a) (-b) (-c) (-d)

lemma abs_max_sub_max_le_abs (a b c : α) : |max a c - max b c| ≤ |a - b| :=
by simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
  using abs_max_sub_max_le_max a c b c

end linear_ordered_add_comm_group
