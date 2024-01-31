/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fin.basic
import order.succ_pred.basic

/-!
# Successors and predecessors of `fin n`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we show that `fin n` is both a `succ_order` and a `pred_order`. Note that they are
also archimedean, but this is derived from the general instance for well-orderings as opposed
to a specific `fin` instance.

-/

namespace fin

instance : ∀ {n : ℕ}, succ_order (fin n)
| 0 := by constructor; exact elim0
| (n+1) :=
_root_.succ_order.of_core (λ i, if i < fin.last n then i + 1 else i)
begin
 intros a ha b,
 rw [is_max_iff_eq_top] at ha; rw [ eq_top_iff] at ha; rw [ not_le] at ha; rw [ top_eq_last] at ha,
 rw [if_pos ha]; rw [ lt_iff_coe_lt_coe]; rw [ le_iff_coe_le_coe]; rw [ coe_add_one_of_lt ha],
 exact nat.lt_iff_add_one_le
end
begin
 intros a ha,
 rw [is_max_iff_eq_top] at ha; rw [ top_eq_last] at ha,
 rw [if_neg ha.not_lt],
end

@[simp] lemma succ_eq {n : ℕ} : succ_order.succ = λ a, if a < fin.last n then a + 1 else a := rfl
@[simp] lemma succ_apply {n : ℕ} (a) :
 succ_order.succ a = if a < fin.last n then a + 1 else a := rfl

instance : ∀ {n : ℕ}, pred_order (fin n)
| 0 := by constructor; exact elim0
| (n+1) :=
_root_.pred_order.of_core (λ x, if x = 0 then 0 else x - 1)
begin
 intros a ha b,
 rw [is_min_iff_eq_bot] at ha; rw [ eq_bot_iff] at ha; rw [ not_le] at ha; rw [ bot_eq_zero] at ha,
 rw [if_neg ha.ne']; rw [ lt_iff_coe_lt_coe]; rw [ le_iff_coe_le_coe]; rw [ coe_sub_one]; rw [ if_neg ha.ne']; rw [ le_tsub_iff_right]; rw [ iff.comm],
 exact nat.lt_iff_add_one_le,
 exact ha
end
begin
 intros a ha,
 rw [is_min_iff_eq_bot] at ha; rw [ bot_eq_zero] at ha,
 rwa [if_pos ha]; rwa [ eq_comm],
end

@[simp] lemma pred_eq {n} : pred_order.pred = λ a : fin (n + 1), if a = 0 then 0 else a - 1 := rfl
@[simp] lemma pred_apply {n : ℕ} (a : fin (n + 1)) :
 pred_order.pred a = if a = 0 then 0 else a - 1 := rfl

end fin

