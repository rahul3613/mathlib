/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import order.min_max
import algebra.order.monoid.lemmas

/-!
# Lemmas about `min` and `max` in an ordered monoid.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open function

variables {α β : Type*}

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/
@[to_additive]
lemma fn_min_mul_fn_max [linear_order α] [comm_semigroup β] (f : α → β) (n m : α) :
  f (min n m) * f (max n m) = f n * f m :=
by { cases le_total n m with h h; simp [h, mul_comm] }

@[to_additive]
lemma min_mul_max [linear_order α] [comm_semigroup α] (n m : α) :
  min n m * max n m = n * m :=
fn_min_mul_fn_max id n m

section covariant_class_mul_le
variables [linear_order α]

section has_mul
variable [has_mul α]

section left
variable [covariant_class α α (*) (≤)]

@[to_additive] lemma min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c :=
(monotone_id.const_mul' a).map_min.symm

@[to_additive]
lemma max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
(monotone_id.const_mul' a).map_max.symm

end left

section right
variable [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
(monotone_id.mul_const' c).map_min.symm

@[to_additive]
lemma max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
(monotone_id.mul_const' c).map_max.symm

end right

@[to_additive] lemma lt_or_lt_of_mul_lt_mul [covariant_class α α (*) (≤)]
  [covariant_class α α (swap (*)) (≤)] {a₁ a₂ b₁ b₂ : α} :
  a₁ * b₁ < a₂ * b₂ → a₁ < a₂ ∨ b₁ < b₂ :=
by { contrapose!, exact λ h, mul_le_mul' h.1 h.2 }

@[to_additive] lemma le_or_lt_of_mul_le_mul [covariant_class α α (*) (≤)]
  [covariant_class α α (swap (*)) (<)] {a₁ a₂ b₁ b₂ : α} :
  a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ < b₂ :=
by { contrapose!, exact λ h, mul_lt_mul_of_lt_of_le h.1 h.2 }

@[to_additive] lemma lt_or_le_of_mul_le_mul [covariant_class α α (*) (<)]
  [covariant_class α α (swap (*)) (≤)]  {a₁ a₂ b₁ b₂ : α} :
  a₁ * b₁ ≤ a₂ * b₂ → a₁ < a₂ ∨ b₁ ≤ b₂ :=
by { contrapose!, exact λ h, mul_lt_mul_of_le_of_lt h.1 h.2 }

@[to_additive] lemma le_or_le_of_mul_le_mul [covariant_class α α (*) (<)]
  [covariant_class α α (swap (*)) (<)] {a₁ a₂ b₁ b₂ : α} :
  a₁ * b₁ ≤ a₂ * b₂ → a₁ ≤ a₂ ∨ b₁ ≤ b₂ :=
by { contrapose!, exact λ h, mul_lt_mul_of_lt_of_lt h.1 h.2 }

@[to_additive] lemma mul_lt_mul_iff_of_le_of_le  [covariant_class α α (*) (≤)]
  [covariant_class α α (swap (*)) (≤)] [covariant_class α α (*) (<)]
  [covariant_class α α (swap (*)) (<)] {a₁ a₂ b₁ b₂ : α} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
  a₁ * b₁ < a₂ * b₂ ↔ a₁ < a₂ ∨ b₁ < b₂ :=
begin
  refine ⟨lt_or_lt_of_mul_lt_mul, _⟩,
  rintro (ha | hb),
  { exact mul_lt_mul_of_lt_of_le ha hb },
  { exact mul_lt_mul_of_le_of_lt ha hb }
end

end has_mul

variable [mul_one_class α]

@[to_additive]
lemma min_le_mul_of_one_le_right [covariant_class α α (*) (≤)] {a b : α} (hb : 1 ≤ b) :
  min a b ≤ a * b :=
min_le_iff.2 $ or.inl $ le_mul_of_one_le_right' hb

@[to_additive]
lemma min_le_mul_of_one_le_left [covariant_class α α (function.swap (*)) (≤)] {a b : α}
  (ha : 1 ≤ a) : min a b ≤ a * b :=
min_le_iff.2 $ or.inr $ le_mul_of_one_le_left' ha

@[to_additive]
lemma max_le_mul_of_one_le [covariant_class α α (*) (≤)]
  [covariant_class α α (function.swap (*)) (≤)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
  max a b ≤ a * b :=
max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

end covariant_class_mul_le
