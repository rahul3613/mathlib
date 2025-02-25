/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import tactic.monotonicity
import tactic.norm_num
import algebra.order.ring.defs
import measure_theory.function.locally_integrable
import measure_theory.integral.bochner
import measure_theory.measure.lebesgue.basic
import data.list.defs

open list tactic tactic.interactive set

example
 (h : 3 + 6 ≤ 4 + 5)
: 1 + 3 + 2 + 6 ≤ 4 + 2 + 1 + 5 :=
begin
 ac_mono,
end

example
 (h : 3 ≤ (4 : ℤ))
 (h' : 5 ≤ (6 : ℤ))
: (1 + 3 + 2) - 6 ≤ (4 + 2 + 1 : ℤ) - 5 :=
begin
 ac_mono,
 mono,
end

example
 (h : 3 ≤ (4 : ℤ))
 (h' : 5 ≤ (6 : ℤ))
: (1 + 3 + 2) - 6 ≤ (4 + 2 + 1 : ℤ) - 5 :=
begin
 transitivity (1 + 3 + 2 - 5 : ℤ),
 { ac_mono },
 { ac_mono },
end

example (x y z k : ℕ)
 (h : 3 ≤ (4 : ℕ))
 (h' : z ≤ y)
: (k + 3 + x) - y ≤ (k + 4 + x) - z :=
begin
 mono, norm_num
end

example (x y z k : ℤ)
 (h : 3 ≤ (4 : ℤ))
 (h' : z ≤ y)
: (k + 3 + x) - y ≤ (k + 4 + x) - z :=
begin
 mono, norm_num
end

example (x y z a b : ℕ)
 (h : a ≤ (b : ℕ))
 (h' : z ≤ y)
: (1 + a + x) - y ≤ (1 + b + x) - z :=
begin
 transitivity (1 + a + x - z),
 { mono, },
 { mono, mono, mono },
end

example (x y z a b : ℤ)
 (h : a ≤ (b : ℤ))
 (h' : z ≤ y)
: (1 + a + x) - y ≤ (1 + b + x) - z :=
begin
 transitivity (1 + a + x - z),
 { mono, },
 { mono, mono, mono },
end

example (x y z : ℤ)
 (h' : z ≤ y)
: (1 + 3 + x) - y ≤ (1 + 4 + x) - z :=
begin
 transitivity (1 + 3 + x - z),
 { mono },
 { mono, mono, norm_num },
end

example (x y z : ℤ)
 (h : 3 ≤ (4 : ℤ))
 (h' : z ≤ y)
: (1 + 3 + x) - y ≤ (1 + 4 + x) - z :=
begin
 ac_mono, mono*
end

@[simp]
def list.le' {α : Type*} [has_le α] : list α → list α → Prop
 | (x::xs) (y::ys) := x ≤ y ∧ list.le' xs ys
 | [] [] := true
 | _ _ := false

@[simp]
instance list_has_le {α : Type*} [has_le α] : has_le (list α) :=
⟨ list.le' ⟩

lemma list.le_refl {α : Type*} [preorder α] {xs : list α}
: xs ≤ xs :=
begin
 induction xs with x xs,
 { trivial },
 { simp [has_le.le,list.le],
 split, exact le_rfl, apply xs_ih }
end

-- @[trans]
lemma list.le_trans {α : Type*} [preorder α]
 {xs zs : list α} (ys : list α)
 (h : xs ≤ ys)
 (h' : ys ≤ zs)
: xs ≤ zs :=
begin
 revert ys zs,
 induction xs with x xs
 ; intros ys zs h h'
 ; cases ys with y ys
 ; cases zs with z zs
 ; try { cases h ; cases h' ; done },
 { apply list.le_refl },
 { simp [has_le.le,list.le],
 split,
 apply le_trans h.left h'.left,
 apply xs_ih _ h.right h'.right, }
end

@[mono]
lemma list_le_mono_left {α : Type*} [preorder α] {xs ys zs : list α}
 (h : xs ≤ ys)
: xs ++ zs ≤ ys ++ zs :=
begin
 revert ys,
 induction xs with x xs ; intros ys h,
 { cases ys, apply list.le_refl, cases h },
 { cases ys with y ys, cases h, simp [has_le.le,list.le] at *,
 revert h, apply and.imp_right,
 apply xs_ih }
end

@[mono]
lemma list_le_mono_right {α : Type*} [preorder α] {xs ys zs : list α}
 (h : xs ≤ ys)
: zs ++ xs ≤ zs ++ ys :=
begin
 revert ys zs,
 induction xs with x xs ; intros ys zs h,
 { cases ys, { simp, apply list.le_refl }, cases h },
 { cases ys with y ys, cases h, simp [has_le.le,list.le] at *,
 suffices : list.le' ((zs ++ [x]) ++ xs) ((zs ++ [y]) ++ ys),
 { refine cast _ this, simp, },
 apply list.le_trans (zs ++ [y] ++ xs),
 { apply list_le_mono_left,
 induction zs with z zs,
 { simp [has_le.le,list.le], apply h.left },
 { simp [has_le.le,list.le], split, exact le_rfl,
 apply zs_ih, } },
 { apply xs_ih h.right, } }
end

lemma bar_bar'
 (h : [] ++ [3] ++ [2] ≤ [1] ++ [5] ++ [4])
: [] ++ [3] ++ [2] ++ [2] ≤ [1] ++ [5] ++ ([4] ++ [2]) :=
begin
 ac_mono,
end

lemma bar_bar''
 (h : [3] ++ [2] ++ [2] ≤ [5] ++ [4] ++ [])
: [1] ++ ([3] ++ [2]) ++ [2] ≤ [1] ++ [5] ++ ([4] ++ []) :=
begin
 ac_mono,
end

lemma bar_bar
 (h : [3] ++ [2] ≤ [5] ++ [4])
: [1] ++ [3] ++ [2] ++ [2] ≤ [1] ++ [5] ++ ([4] ++ [2]) :=
begin
 ac_mono,
end

def P (x : ℕ) := 7 ≤ x
def Q (x : ℕ) := x ≤ 7

@[mono]
lemma P_mono {x y : ℕ}
 (h : x ≤ y)
: P x → P y :=
by { intro h', apply le_trans h' h }

@[mono]
lemma Q_mono {x y : ℕ}
 (h : y ≤ x)
: Q x → Q y :=
by apply le_trans h

example (x y z : ℕ)
 (h : x ≤ y)
: P (x + z) → P (z + y) :=
begin
 ac_mono,
 ac_mono,
end

example (x y z : ℕ)
 (h : y ≤ x)
: Q (x + z) → Q (z + y) :=
begin
 ac_mono,
 ac_mono,
end

example (x y z k m n : ℤ)
 (h₀ : z ≤ 0)
 (h₁ : y ≤ x)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
 ac_mono,
 ac_mono,
 ac_mono,
end

example (x y z k m n : ℕ)
 (h₀ : z ≥ 0)
 (h₁ : x ≤ y)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
 ac_mono,
 ac_mono,
 ac_mono,
end

example (x y z k m n : ℕ)
 (h₀ : z ≥ 0)
 (h₁ : x ≤ y)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
 ac_mono,
 -- ⊢ (m + x + n) * z ≤ z * (y + n + m)
 ac_mono,
 -- ⊢ m + x + n ≤ y + n + m
 ac_mono,
end

example (x y z k m n : ℕ)
 (h₀ : z ≥ 0)
 (h₁ : x ≤ y)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by { ac_mono* := h₁ }

example (x y z k m n : ℕ)
 (h₀ : z ≥ 0)
 (h₁ : m + x + n ≤ y + n + m)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by { ac_mono* := h₁ }

example (x y z k m n : ℕ)
 (h₀ : z ≥ 0)
 (h₁ : n + x + m ≤ y + n + m)
: (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
 ac_mono* : m + x + n ≤ y + n + m,
 transitivity ; [ skip , apply h₁ ],
 apply le_of_eq,
 ac_refl,
end

example (x y z k m n : ℤ)
 (h₁ : x ≤ y)
: true :=
begin
 have : (m + x + n) * z + k ≤ z * (y + n + m) + k,
 { ac_mono,
 success_if_fail { ac_mono },
 admit },
 trivial
end

example (x y z k m n : ℕ)
 (h₁ : x ≤ y)
: true :=
begin
 have : (m + x + n) * z + k ≤ z * (y + n + m) + k,
 { ac_mono*,
 change 0 ≤ z, apply nat.zero_le, },
 trivial
end

example (x y z k m n : ℕ)
 (h₁ : x ≤ y)
: true :=
begin
 have : (m + x + n) * z + k ≤ z * (y + n + m) + k,
 { ac_mono,
 change (m + x + n) * z ≤ z * (y + n + m),
 admit },
 trivial,
end

example (x y z k m n i j : ℕ)
 (h₁ : x + i = y + j)
: (m + x + n + i) * z + k = z * (j + n + m + y) + k :=
begin
 ac_mono^3,
 cc
end

example (x y z k m n i j : ℕ)
 (h₁ : x + i = y + j)
: z * (x + i + n + m) + k = z * (y + j + n + m) + k :=
begin
 congr,
 simp [h₁],
end

example (x y z k m n i j : ℕ)
 (h₁ : x + i = y + j)
: (m + x + n + i) * z + k = z * (j + n + m + y) + k :=
begin
 ac_mono*,
 cc,
end

example (x y : ℕ)
 (h : x ≤ y)
: true :=
begin
 (do v ← mk_mvar,
 p ← to_expr ```(%%v + x ≤ y + %%v),
 assert `h' p),
 ac_mono := h,
 trivial,
 exact 1,
end

example {x y z : ℕ} : true :=
begin
 have : y + x ≤ y + z,
 { mono,
 guard_target' x ≤ z,
 admit },
 trivial
end

example {x y z : ℕ} : true :=
begin
 suffices : x + y ≤ z + y, trivial,
 mono,
 guard_target' x ≤ z,
 admit,
end

example {x y z w : ℕ} : true :=
begin
 have : x + y ≤ z + w,
 { mono,
 guard_target' x ≤ z, admit,
 guard_target' y ≤ w, admit },
 trivial
end

example {x y z w : ℕ} : true :=
begin
 have : x * y ≤ z * w,
 { mono with [0 ≤ z,0 ≤ y],
 { guard_target 0 ≤ z, admit },
 { guard_target 0 ≤ y, admit },
 guard_target' x ≤ z, admit,
 guard_target' y ≤ w, admit },
 trivial
end

example {x y z w : Prop} : true :=
begin
 have : x ∧ y → z ∧ w,
 { mono,
 guard_target' x → z, admit,
 guard_target' y → w, admit },
 trivial
end

example {x y z w : Prop} : true :=
begin
 have : x ∨ y → z ∨ w,
 { mono,
 guard_target' x → z, admit,
 guard_target' y → w, admit },
 trivial
end

example {x y z w : ℤ} : true :=
begin
 suffices : x + y < w + z, trivial,
 have : x < w, admit,
 have : y ≤ z, admit,
 mono right,
end

example {x y z w : ℤ} : true :=
begin
 suffices : x * y < w * z, trivial,
 have : x < w, admit,
 have : y ≤ z, admit,
 mono right,
 { guard_target' 0 < y, admit },
 { guard_target' 0 ≤ w, admit },
end

open tactic

example (x y : ℕ)
 (h : x ≤ y)
: true :=
begin
 (do v ← mk_mvar,
 p ← to_expr ```(%%v + x ≤ y + %%v),
 assert `h' p),
 ac_mono := h,
 trivial,
 exact 3
end

example {α} [linear_order α]
 (a b c d e : α) :
 max a b ≤ e → b ≤ e :=
by { mono, apply le_max_right }

example (a b c d e : Prop)
 (h : d → a) (h' : c → e) :
 (a ∧ b → c) ∨ d → (d ∧ b → e) ∨ a :=
begin
 mono,
 mono,
 mono,
end

example : ∫ x in Icc 0 1, real.exp x ≤ ∫ x in Icc 0 1, real.exp (x+1) :=
begin
 mono,
 { exact real.continuous_exp.locally_integrable.integrable_on_is_compact is_compact_Icc },
 { exact (real.continuous_exp.comp $ continuous_add_right 1)
 .locally_integrable.integrable_on_is_compact is_compact_Icc },
 intro x,
 dsimp only,
 mono,
 linarith
end

