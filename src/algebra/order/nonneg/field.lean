/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import algebra.order.field.basic
import algebra.order.field.canonical.defs
import algebra.order.field.inj_surj
import algebra.order.nonneg.ring

/-!
# Semifield structure on the type of nonnegative elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.

## Main declarations

* `{x : α // 0 ≤ x}` is a `canonically_linear_ordered_semifield` if `α` is a `linear_ordered_field`.
-/

open set

variables {α : Type*}

namespace nonneg

section linear_ordered_semifield
variables [linear_ordered_semifield α] {x y : α}

instance has_inv : has_inv {x : α // 0 ≤ x} := ⟨λ x, ⟨x⁻¹, inv_nonneg.2 x.2⟩⟩

@[simp, norm_cast]
protected lemma coe_inv (a : {x : α // 0 ≤ x}) : ((a⁻¹ : {x : α // 0 ≤ x}) : α) = a⁻¹ := rfl

@[simp] lemma inv_mk (hx : 0 ≤ x) : (⟨x, hx⟩ : {x : α // 0 ≤ x})⁻¹ = ⟨x⁻¹, inv_nonneg.2 hx⟩ := rfl

instance has_div : has_div {x : α // 0 ≤ x} := ⟨λ x y, ⟨x / y, div_nonneg x.2 y.2⟩⟩

@[simp, norm_cast] protected lemma coe_div (a b : {x : α // 0 ≤ x}) :
  ((a / b : {x : α // 0 ≤ x}) : α) = a / b := rfl

@[simp] lemma mk_div_mk (hx : 0 ≤ x) (hy : 0 ≤ y) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ := rfl

instance has_zpow : has_pow {x : α // 0 ≤ x} ℤ := ⟨λ a n, ⟨a ^ n, zpow_nonneg a.2 _⟩⟩

@[simp, norm_cast] protected lemma coe_zpow (a : {x : α // 0 ≤ x}) (n : ℤ) :
  ((a ^ n : {x : α // 0 ≤ x}) : α) = a ^ n := rfl

@[simp] lemma mk_zpow (hx : 0 ≤ x) (n : ℤ) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) ^ n = ⟨x ^ n, zpow_nonneg hx n⟩ := rfl

instance linear_ordered_semifield : linear_ordered_semifield {x : α // 0 ≤ x} :=
subtype.coe_injective.linear_ordered_semifield _ nonneg.coe_zero nonneg.coe_one nonneg.coe_add
    nonneg.coe_mul nonneg.coe_inv nonneg.coe_div (λ _ _, rfl) nonneg.coe_pow nonneg.coe_zpow
    nonneg.coe_nat_cast (λ _ _, rfl) (λ _ _, rfl)

end linear_ordered_semifield

instance canonically_linear_ordered_semifield [linear_ordered_field α] :
  canonically_linear_ordered_semifield {x : α // 0 ≤ x} :=
{ ..nonneg.linear_ordered_semifield, ..nonneg.canonically_ordered_comm_semiring }

instance linear_ordered_comm_group_with_zero [linear_ordered_field α] :
  linear_ordered_comm_group_with_zero {x : α // 0 ≤ x} :=
infer_instance

end nonneg
